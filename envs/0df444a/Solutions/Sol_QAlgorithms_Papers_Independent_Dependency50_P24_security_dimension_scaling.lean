-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.security_dimension_scaling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T08:12:36.450039+00:00
-- url     : https://prove2.me/submissions/21981221-2a52-49db-b06d-c662017d7a3e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy average holevo)

section G55BD
open Polynomial
lemma g55b_cfc_diag {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  set A := Matrix.diagonal (fun i => (d i : ℂ)) with hA
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, hA, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  set S : Finset ℝ := Finset.univ.image d
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ i, p.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f) (i := d i)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    exact this
  have hspec : ∀ x ∈ spectrum ℝ A, ∃ i, d i = x := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, hA, spectrum_diagonal,
      Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by rw [Complex.coe_algebraMap] at hi; exact_mod_cast hi⟩
  have h1 : cfc f A = cfc p.eval A := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := hspec x hx
    exact (hp i).symm
  rw [h1, cfc_polynomial p A]
  rw [hA, show Matrix.diagonal (fun i => (d i : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) from rfl, Polynomial.aeval_algHom_apply]
  rw [show Matrix.diagonal (fun i => (f (d i) : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (f (d i) : ℂ)) from rfl]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply₂]
  rw [show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval, hp]
  rfl
end G55BD

lemma g55b_cnt (d : ℕ) (A B : ℝ) :
    ∑ k : Key d, (if k.1 = k.2 then A else B) = d * A + ((d : ℝ) ^ 2 - d) * B := by
  rw [Fintype.sum_prod_type]
  have : ∀ i : Fin d, ∑ j : Fin d, (if i = j then A else B) = B * d + (A - B) := by
    intro i
    rw [show (fun j : Fin d => if i = j then A else B) = fun j => B + (if i = j then A - B else 0) by
      funext j; split_ifs <;> ring]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp [mul_comm]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma g55b_pure_ket {ι : Type*} [Fintype ι] (x : ι) :
    pureDensity (ket x) = Matrix.diagonal (fun y => (((if y = x then 1 else 0 : ℝ)) : ℂ)) := by
  ext a b
  simp only [pureDensity, ket, Matrix.of_apply, Matrix.diagonal_apply, PiLp.single_apply]
  by_cases hab : a = b
  · subst hab; split_ifs <;> simp_all
  · rw [if_neg hab]; split_ifs <;> simp_all

lemma g55b_tn_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℝ) :
    traceNorm (Matrix.diagonal (fun i => (m i : ℂ))) = ∑ i, |m i| := by
  unfold traceNorm
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [show (fun i => star (fun i => (m i : ℂ)) i * (m i : ℂ)) = fun i => ((m i * m i : ℝ) : ℂ) by
    funext i; simp]
  rw [g55b_cfc_diag, Matrix.trace_diagonal, Complex.re_sum]
  simp [Real.sqrt_mul_self_eq_abs]

lemma g55b_ent_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℝ) :
    QAlgorithms.Papers.Independent.Information100.P56.entropy (Matrix.diagonal (fun i => (m i : ℂ))) =
      -∑ i, m i * Real.log (m i) := by
  unfold QAlgorithms.Papers.Independent.Information100.P56.entropy
  rw [g55b_cfc_diag, Matrix.trace_diagonal, Complex.re_sum]
  simp

theorem solution (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (a : ℝ) (ha : 0 ≤ a) (haone : a ≤ 1) :
    IsEnsemble (scalingWeights d a) (scalingEve d) ∧
    traceNorm (cqState (scalingWeights d a) (scalingEve d) -
      idealCCQ (d := d) (pureDensity (ket ((0,0) : Key d)))) = 2*a ∧
    ensembleHolevoBits (scalingWeights d a) (scalingEve d) = binEntropy2 a + a*logBits ((d:ℝ)^2-d) := by
  have hd2 : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0:ℝ) < d := by linarith
  set D : ℝ := (d:ℝ)^2 - d with hDdef
  have hD : 0 < D := by rw [hDdef]; nlinarith
  set w := scalingWeights d a with hwdef
  have hw : ∀ k : Key d, w k = if k.1 = k.2 then (1-a)/d else a/D := fun k => rfl
  set ek : Key d → Key d := fun k => if k.1 = k.2 then (0,0) else k with hek
  have heve : ∀ k, scalingEve d k = Matrix.diagonal (fun y => ((if y = ek k then 1 else 0 : ℝ) : ℂ)) :=
    fun k => by unfold scalingEve; convert g55b_pure_ket (ek k)
  have hens : IsEnsemble w (scalingEve d) := by
    refine ⟨fun k => ?_, ?_, fun k => ?_⟩
    · rw [hw]; split_ifs
      · exact div_nonneg (by linarith) hdpos.le
      · exact div_nonneg ha hD.le
    · simp only [hw]; rw [g55b_cnt]; field_simp; ring
    · rw [heve]
      refine ⟨?_, ?_⟩
      · rw [Matrix.posSemidef_diagonal_iff]; intro y; split_ifs <;> simp
      · rw [Matrix.trace_diagonal, Finset.sum_eq_single (ek k)]
        · simp
        · intro b _ hb; simp [hb]
        · simp
  refine ⟨hens, ?_, ?_⟩
  · set m : Key d × Key d → ℝ := fun x => (if x.2 = ek x.1 then w x.1 else 0) -
      (if x.1.1 = x.1.2 ∧ x.2 = (0,0) then 1 / (d:ℝ) else 0) with hm
    have hM : cqState w (scalingEve d) - idealCCQ (d := d) (pureDensity (ket ((0,0) : Key d))) =
        Matrix.diagonal (fun x => (m x : ℂ)) := by
      have h0 : pureDensity (ket ((0,0) : Key d)) =
          Matrix.diagonal (fun y => ((if y = ((0,0) : Key d) then 1 else 0 : ℝ) : ℂ)) := by
        convert g55b_pure_ket ((0,0) : Key d)
      rw [h0]
      ext ⟨k, e⟩ ⟨k', e'⟩
      simp only [cqState, idealCCQ, heve, Matrix.sub_apply, Matrix.diagonal_apply, hm]
      by_cases hk : k = k'
      · subst hk
        by_cases he : e = e'
        · subst he; simp only [if_true, true_and]; push_cast; split_ifs <;> simp_all
        · simp [he]
      · simp [hk]
    rw [hM, g55b_tn_diag, Fintype.sum_prod_type]
    have hrow : ∀ k : Key d, ∑ e : Key d, |m (k, e)| = if k.1 = k.2 then a / d else a / D := by
      intro k
      by_cases hk : k.1 = k.2
      · rw [if_pos hk, Finset.sum_eq_single ((0,0) : Key d)]
        · simp only [hm, hek, hw, if_pos hk, and_true, if_true]
          rw [show (1 - a) / (d:ℝ) - 1 / d = -(a / d) by ring, abs_neg, abs_of_nonneg (div_nonneg ha hdpos.le)]
        · intro e _ he
          simp [hm, hek, hk, he]
        · simp
      · rw [if_neg hk, Finset.sum_eq_single k]
        · simp only [hm, hek, hw, if_neg hk, if_true]
          simp [hk, abs_of_nonneg (div_nonneg ha hD.le)]
        · intro e _ he
          simp [hm, hek, hk, he]
        · simp
    simp only [hrow]
    rw [g55b_cnt]
    field_simp
    ring
  · have hpure : ∀ k, entropy (scalingEve d k) = 0 := by
      intro k
      rw [heve, g55b_ent_diag]
      simp
    set μ : Key d → ℝ := fun e => if e = (0,0) then 1 - a else if e.1 = e.2 then 0 else a / D with hμ
    have havg : average (scalingEve d) w = Matrix.diagonal (fun e => (μ e : ℂ)) := by
      have h1 : average (scalingEve d) w =
          Matrix.diagonal (fun e => ((∑ k, w k * (if e = ek k then 1 else 0) : ℝ) : ℂ)) := by
        ext e e'
        simp only [average, Matrix.sum_apply, Matrix.smul_apply, heve, Matrix.diagonal_apply, smul_eq_mul]
        by_cases he : e = e'
        · subst he; simp only [if_true]; push_cast
          refine Finset.sum_congr rfl (fun k _ => ?_)
          split_ifs <;> simp
        · simp [he]
      rw [h1]
      congr 1
      funext e
      congr 1
      have hsplit : ∀ k : Key d, w k * (if e = ek k then 1 else 0) =
          (if k.1 = k.2 then (if e = (0,0) then (1-a)/d else 0) else 0) +
          (if e = k then (if k.1 = k.2 then 0 else a / D) else 0) := by
        intro k
        rw [hw]
        by_cases hk : k.1 = k.2
        · simp only [hek, if_pos hk]
          by_cases he : e = k
          · subst he; split_ifs <;> simp
          · simp [he]
        · simp only [hek, if_neg hk]
          by_cases he : e = k
          · subst he; simp [hk]
          · simp [he]
      simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq]
      rw [g55b_cnt]
      simp only [hμ, Finset.mem_univ, if_true]
      by_cases h0 : e = (0,0)
      · subst h0; simp; field_simp
      · by_cases hd' : e.1 = e.2 <;> simp [h0, hd']
    have hsum : ∑ e, μ e * Real.log (μ e) = (1 - a) * Real.log (1 - a) + a * Real.log (a / D) := by
      have hpt : ∀ e : Key d, μ e * Real.log (μ e) =
          (if e = (0,0) then (1 - a) * Real.log (1 - a) else 0) +
          (if e.1 = e.2 then 0 else a / D * Real.log (a / D)) := by
        intro e
        simp only [hμ]
        by_cases h0 : e = (0,0)
        · subst h0; simp
        · by_cases hd' : e.1 = e.2 <;> simp [h0, hd']
      simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [g55b_cnt, ← hDdef]
      field_simp
      ring
    unfold ensembleHolevoBits holevo
    rw [havg]
    have target : (-∑ e, μ e * Real.log (μ e) - 0) / Real.log 2 = binEntropy2 a + a * logBits D := by
      rw [hsum, sub_zero]
      unfold binEntropy2 logBits Real.binEntropy
      rw [Real.log_inv, Real.log_inv]
      rcases ha.eq_or_lt with h | h
      · rw [← h]; simp
      · rw [Real.log_div h.ne' hD.ne']
        ring
    convert target using 3
    · convert g55b_ent_diag μ
    · refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [mul_eq_zero]; right; convert hpure k
end
