-- Prove2me | solution 1 for RovelliLQG.tetrahedron_volume_sq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:36:33.372995+00:00
-- url     : https://prove2.me/submissions/86e53790-0d85-4a24-82f6-ea1d4d59e183

import Mathlib
import Definitions.Def_RovelliLQG_Defs

open MeasureTheory

namespace LQSimplex

def T (n : ℕ) (s : ℝ) : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ s}

lemma T_closed (n : ℕ) (s : ℝ) : IsClosed (T n s) := by
  have : T n s = (⋂ i, {x : Fin n → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ s} := by
    ext x; simp [T]
  rw [this]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const

lemma T_empty (n : ℕ) (s : ℝ) (hs : s < 0) : T n s = ∅ := by
  ext x
  simp only [T, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
  intro h
  exact lt_of_lt_of_le hs (Finset.sum_nonneg fun i _ => h i)

lemma vol_T (n : ℕ) : ∀ s : ℝ, 0 ≤ s →
    volume (T n s) = ENNReal.ofReal (s ^ n / n.factorial) := by
  induction n with
  | zero =>
    intro s hs
    have : T 0 s = Set.univ := by ext x; simp [T, hs]
    rw [this, volume_pi, Measure.pi_univ]; simp
  | succ n ih =>
    intro s hs
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℝ)) 0
    let S' : Set (ℝ × (Fin n → ℝ)) := {p | 0 ≤ p.1 ∧ p.2 ∈ T n (s - p.1)}
    have hpre : T (n+1) s = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) ⁻¹' S' := by
      ext x
      simp only [T, S', Set.mem_preimage, Set.mem_ofPred_eq, Fin.sum_univ_succ, Fin.forall_fin_succ,
        MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.succAbove_zero,
        Equiv.coe_fn_symm_mk, Fin.removeNth_apply]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, by linarith⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, by linarith⟩
    have hS'm : MeasurableSet S' := by
      apply IsClosed.measurableSet
      have : S' = {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1} ∩ ((⋂ i, {p | 0 ≤ p.2 i}) ∩ {p | ∑ i, p.2 i + p.1 ≤ s}) := by
        ext p; simp [S', T, le_sub_iff_add_le]
      rw [this]
      refine IsClosed.inter (isClosed_le continuous_const continuous_fst) (IsClosed.inter ?_ ?_)
      · exact isClosed_iInter fun i => isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)
      · exact isClosed_le ((continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_snd).add
          continuous_fst) continuous_const
    rw [hpre, volume_pi, hmp.measure_preimage_equiv, Measure.prod_apply hS'm, ← volume_pi]
    have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' S') =
        (Set.Icc 0 s).indicator (fun t => ENNReal.ofReal ((s - t) ^ n / n.factorial)) t := by
      intro t
      by_cases ht : t ∈ Set.Icc 0 s
      · rw [Set.indicator_of_mem ht, ← ih (s - t) (by linarith [ht.2])]
        congr 1; ext y; simp [S', ht.1]
      · rw [Set.indicator_of_notMem ht]
        rcases not_and_or.mp ht with h | h
        · have : Prod.mk t ⁻¹' S' = ∅ := by ext y; simp [S']; intro h'; exact absurd h' h
          rw [this, measure_empty]
        · have : Prod.mk t ⁻¹' S' = ∅ := by
            ext y; simp only [S', Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
            rw [T_empty n (s - t) (by push Not at h; linarith)]; simp
          rw [this, measure_empty]
    simp_rw [hslice]
    rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
      simp only [div_eq_mul_inv]
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_sub_left
        (fun t => t ^ n), integral_pow]
      simp [Nat.factorial_succ]
      field_simp
    · exact (by fun_prop : Continuous fun t : ℝ => (s - t) ^ n / n.factorial).integrableOn_Icc
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have : 0 ≤ s - t := by linarith [ht.2]
      positivity

end LQSimplex

open MeasureTheory RovelliLQG
open scoped InnerProductSpace

namespace LQTet

noncomputable def fL (a b c : E3) : E3 →ₗ[ℝ] E3 where
  toFun x := x 0 • a + x 1 • b + x 2 • c
  map_add' x y := by simp [add_smul]; abel
  map_smul' r x := by simp [smul_add, mul_smul]

def X : Set E3 := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

lemma vol_X : volume X = ENNReal.ofReal (1/6) := by
  have h := PiLp.volume_preserving_ofLp (Fin 3)
  have : X = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹' LQSimplex.T 3 1 := by ext x; rfl
  rw [this, h.measure_preimage (LQSimplex.T_closed 3 1).measurableSet.nullMeasurableSet,
    LQSimplex.vol_T 3 1 zero_le_one]
  norm_num [Nat.factorial]

lemma convex_X : Convex ℝ X := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have := hx.1 i; have := hy.1 i; positivity
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    nlinarith [hx.2, hy.2]

lemma hull_eq (p0 p1 p2 p3 : E3) : convexHull ℝ {p0, p1, p2, p3} =
    (fun x => p0 + x) '' (fL (p1 - p0) (p2 - p0) (p3 - p0) '' X) := by
  apply subset_antisymm
  · apply convexHull_min
    · intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · refine ⟨0, ⟨0, ?_, by simp⟩, by simp⟩; simp [X]
      · refine ⟨_, ⟨EuclideanSpace.single 0 1, ?_, rfl⟩, ?_⟩
        · refine ⟨fun i => ?_, ?_⟩
          · fin_cases i <;> simp
          · simp [Fin.sum_univ_three]
        · simp [fL]
      · refine ⟨_, ⟨EuclideanSpace.single 1 1, ?_, rfl⟩, ?_⟩
        · refine ⟨fun i => ?_, ?_⟩
          · fin_cases i <;> simp
          · simp [Fin.sum_univ_three]
        · simp [fL]
      · refine ⟨_, ⟨EuclideanSpace.single 2 1, ?_, rfl⟩, ?_⟩
        · refine ⟨fun i => ?_, ?_⟩
          · fin_cases i <;> simp
          · simp [Fin.sum_univ_three]
        · simp [fL]
    · exact (convex_X.linear_image _).translate p0
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hconv := convex_convexHull ℝ ({p0, p1, p2, p3} : Set E3)
    have hs : x 0 + x 1 + x 2 ≤ 1 := by simpa [Fin.sum_univ_three] using hx.2
    have := hconv.sum_mem (t := Finset.univ) (w := ![1 - (x 0 + x 1 + x 2), x 0, x 1, x 2])
      (z := ![p0, p1, p2, p3])
      (fun i _ => by fin_cases i <;> simp [hx.1 0, hx.1 1, hx.1 2, hs])
      (by simp [Fin.sum_univ_four]; ring)
      (fun i _ => subset_convexHull ℝ _ (by fin_cases i <;> simp))
    convert this using 1
    simp [Fin.sum_univ_four, fL]
    module

lemma det_fL (a b c : E3) : LinearMap.det (fL a b c) =
    a 0 * b 1 * c 2 - a 0 * b 2 * c 1 - a 1 * b 0 * c 2 + a 1 * b 2 * c 0 + a 2 * b 0 * c 1
      - a 2 * b 1 * c 0 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  simp [LinearMap.toMatrix_apply, fL]
  ring

lemma key (D E : ℝ) (h : E = D ^ 2 / 8) : (|D| * (1 / 6)) ^ 2 = 2 / 9 * |E| := by
  rw [h, abs_of_nonneg (by positivity : (0:ℝ) ≤ D ^ 2 / 8), mul_pow, sq_abs]; ring

theorem main (p₀ p₁ p₂ p₃ : E3) :
    (MeasureTheory.volume (convexHull ℝ {p₀, p₁, p₂, p₃})).toReal ^ 2 =
      (2 / 9 : ℝ) * |⟪(1 / 2 : ℝ) • cross3 (p₁ - p₀) (p₂ - p₀),
        cross3 ((1 / 2 : ℝ) • cross3 (p₂ - p₀) (p₃ - p₀))
          ((1 / 2 : ℝ) • cross3 (p₃ - p₀) (p₁ - p₀))⟫_ℝ| := by
  rw [hull_eq, Set.image_add_left, measure_preimage_add, Measure.addHaar_image_linearMap, vol_X,
    det_fL]
  set a := p₁ - p₀
  set b := p₂ - p₀
  set c := p₃ - p₀
  simp only [cross3, PiLp.inner_apply, Fin.sum_univ_three, PiLp.smul_apply, WithLp.ofLp_smul,
    cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply,
    smul_eq_mul, RCLike.inner_apply, conj_trivial]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (by norm_num)]
  refine key _ _ ?_
  simp only [Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_succ, Matrix.cons_val_zero,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

end LQTet

open RovelliLQG in
theorem solution (p₀ p₁ p₂ p₃ : E3) :
    (MeasureTheory.volume (convexHull ℝ {p₀, p₁, p₂, p₃})).toReal ^ 2 =
      (2 / 9 : ℝ) * |⟪(1 / 2 : ℝ) • cross3 (p₁ - p₀) (p₂ - p₀),
        cross3 ((1 / 2 : ℝ) • cross3 (p₂ - p₀) (p₃ - p₀))
          ((1 / 2 : ℝ) • cross3 (p₃ - p₀) (p₁ - p₀))⟫_ℝ| :=
  LQTet.main p₀ p₁ p₂ p₃
