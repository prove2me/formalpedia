-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.weakSourceConverse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:09:08.012149+00:00
-- url     : https://prove2.me/submissions/976f1d0b-59a2-4bfe-b3ee-73f02ae1887e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_mixedDistance
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_sourceCoding

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
open Filter

namespace X6WSC

variable {a d n : ℕ}

lemma law_sum (S : PureSource a d) : ∑ x, (S.law x).toReal = 1 := by
  have h := S.law.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top _ _), h]; simp

lemma weight_nonneg (S : PureSource a d) (w : Fin n → Fin a) : 0 ≤ S.weight w :=
  Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg

lemma weight_sum (S : PureSource a d) : ∑ w : Fin n → Fin a, S.weight w = 1 := by
  unfold PureSource.weight
  rw [← Fintype.prod_sum (fun (m : Fin n) (j : Fin a) => (S.law j).toReal)]; simp [law_sum]

lemma word_pure (S : PureSource a d) (w : Fin n → Fin a) : IsPure (S.word w) := by
  choose vx hvx1 hvx using S.pure
  have hv1 : ∀ x, ∑ j, ‖vx x j‖ ^ 2 = 1 := by
    intro x
    have h := hvx1 x
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
    exact h
  refine ⟨WithLp.toLp 2 (fun b => ∏ i, vx (w i) (b i)), ?_, ?_⟩
  · rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp only [PiLp.toLp_apply, norm_prod, ← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun i j => ‖vx (w i) j‖ ^ 2)]
    simp [hv1]
  · ext x y
    simp only [PureSource.word, wordTensor, hvx, pureDensity, Matrix.of_apply, map_prod,
      Finset.prod_mul_distrib]

lemma channel_density {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Φ : Superop ι κ) (hΦ : IsChannel Φ) (ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (Φ ρ) := by
  obtain ⟨m, E, hE, hEq⟩ := hΦ
  rw [hEq]; unfold krausApply
  refine ⟨Matrix.posSemidef_sum _ fun k _ => hρ.1.mul_mul_conjTranspose_same _, ?_⟩
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_mul_comm _ (E _)ᴴ, ← Matrix.mul_assoc]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  unfold IsKrausFamily at hE
  rw [hE, Matrix.one_mul]; exact hρ.2

lemma traceNorm_neg {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    traceNorm (-X) = traceNorm X := by
  simp [traceNorm, Matrix.conjTranspose_neg]

lemma td_symm {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) :
    traceDistance A B = traceDistance B A := by
  unfold traceDistance
  rw [← traceNorm_neg, neg_sub]

/-- Per-word bounds: `1 - F ≤ T` and `T² ≤ 1 - F`. -/
lemma word_bounds (S : PureSource a d) (c : SourceCode S n) (w : Fin n → Fin a) :
    1 - effectProb (c.decode (c.encode w)) (S.word w) ≤
        traceDistance (c.decode (c.encode w)) (S.word w) ∧
      (traceDistance (c.decode (c.encode w)) (S.word w)) ^ 2 ≤
        1 - effectProb (c.decode (c.encode w)) (S.word w) := by
  have hσ := channel_density c.decode c.decoder_channel _ (c.encoded_state w)
  have h := mixedDistance (S.word w) (c.decode (c.encode w)) (word_pure S w) hσ
  have he : effectProb (S.word w) (c.decode (c.encode w)) =
      effectProb (c.decode (c.encode w)) (S.word w) := by
    unfold effectProb; rw [Matrix.trace_mul_comm]
  rw [he, td_symm] at h
  exact ⟨h.1, h.2⟩

lemma one_sub_fid (S : PureSource a d) (c : SourceCode S n) :
    1 - c.fidelity = ∑ w, S.weight w * (1 - effectProb (c.decode (c.encode w)) (S.word w)) := by
  unfold SourceCode.fidelity
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, weight_sum]

lemma fid_of_dist (S : PureSource a d) (c : SourceCode S n) : 1 - c.fidelity ≤ c.distortion := by
  rw [one_sub_fid]; unfold SourceCode.distortion
  exact Finset.sum_le_sum fun w _ =>
    mul_le_mul_of_nonneg_left (word_bounds S c w).1 (weight_nonneg S w)

lemma dist_sq (S : PureSource a d) (c : SourceCode S n) : c.distortion ^ 2 ≤ 1 - c.fidelity := by
  rw [one_sub_fid]; unfold SourceCode.distortion
  set T := fun w => traceDistance (c.decode (c.encode w)) (S.word w)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun w => Real.sqrt (S.weight w))
    (fun w => Real.sqrt (S.weight w) * T w)
  have hw : ∀ w : Fin n → Fin a, Real.sqrt (S.weight w) ^ 2 = S.weight w := fun w =>
    Real.sq_sqrt (weight_nonneg S w)
  have hl : ∀ w : Fin n → Fin a, Real.sqrt (S.weight w) * (Real.sqrt (S.weight w) * T w) =
      S.weight w * T w := fun w => by rw [← mul_assoc, Real.mul_self_sqrt (weight_nonneg S w)]
  simp only [mul_pow, hw, hl] at hcs
  rw [weight_sum, one_mul] at hcs
  refine hcs.trans (Finset.sum_le_sum fun w _ =>
    mul_le_mul_of_nonneg_left (word_bounds S c w).2 (weight_nonneg S w))

lemma dist_le_sqrt (S : PureSource a d) (c : SourceCode S n) (l : ℝ) (h : 1 - c.fidelity ≤ l) :
    c.distortion ≤ Real.sqrt l :=
  Real.le_sqrt_of_sq_le ((dist_sq S c).trans h)

lemma f_le_g (S : PureSource a d) (l : ℝ) :
    sourceRate S .arbitraryFidelity l ≤ sourceRate S .arbitraryDistortion l := by
  unfold sourceRate
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
  unfold minimumSourceRate
  refine sInf_le_sInf ?_
  rintro r ⟨c, hc, rfl⟩
  exact ⟨c, (fid_of_dist S c).trans hc, rfl⟩

lemma g_sqrt_le_f (S : PureSource a d) (l : ℝ) :
    sourceRate S .arbitraryDistortion (Real.sqrt l) ≤ sourceRate S .arbitraryFidelity l := by
  unfold sourceRate
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
  unfold minimumSourceRate
  refine sInf_le_sInf ?_
  rintro r ⟨c, hc, rfl⟩
  exact ⟨c, dist_le_sqrt S c l hc, rfl⟩

end X6WSC

open X6WSC in
theorem solution {a d : ℕ} (S : PureSource a d) :
    Filter.liminf (sourceRate S .arbitraryFidelity) (nhdsWithin 0 (Set.Ioi 0)) =
      Filter.liminf (sourceRate S .arbitraryDistortion) (nhdsWithin 0 (Set.Ioi 0)) ∧
    ENNReal.ofReal (vnEntropy S.average) ≤
      Filter.liminf (sourceRate S .arbitraryDistortion) (nhdsWithin 0 (Set.Ioi 0)) := by
  set H := ENNReal.ofReal (vnEntropy S.average)
  set f := sourceRate S .arbitraryFidelity
  set g := sourceRate S .arbitraryDistortion
  have hev : ∀ᶠ l in nhdsWithin (0 : ℝ) (Set.Ioi 0), f l = H := by
    have h1 : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [h1] with l hl
    exact (sourceCoding S l hl.1 hl.2).2.2
  have hf : Filter.liminf f (nhdsWithin 0 (Set.Ioi 0)) = H := by
    rw [liminf_congr hev, liminf_const]
  have hlow : H ≤ Filter.liminf g (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [← hf]
    exact liminf_le_liminf (Eventually.of_forall fun l => f_le_g S l)
  have htend : Tendsto Real.sqrt (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (Real.continuous_sqrt.tendsto 0)
      rw [Real.sqrt_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with l hl
      exact Real.sqrt_pos.mpr hl
  have hup : Filter.liminf g (nhdsWithin 0 (Set.Ioi 0)) ≤ H := by
    calc Filter.liminf g (nhdsWithin 0 (Set.Ioi 0))
        ≤ Filter.liminf (g ∘ Real.sqrt) (nhdsWithin 0 (Set.Ioi 0)) := by
          rw [Filter.liminf_comp]
          exact liminf_le_liminf_of_le htend
      _ ≤ Filter.liminf f (nhdsWithin 0 (Set.Ioi 0)) :=
          liminf_le_liminf (Eventually.of_forall fun l => g_sqrt_le_f S l)
      _ = H := hf
  exact ⟨hf.trans (le_antisymm hlow hup), hlow⟩
