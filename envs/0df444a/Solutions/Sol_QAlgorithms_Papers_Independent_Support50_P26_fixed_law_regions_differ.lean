-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P26.fixed_law_regions_differ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:41:38.421897+00:00
-- url     : https://prove2.me/submissions/d308871f-841b-4da6-bfe1-3b9250f0d9d7

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P26
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P26

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op quantumMI)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks)
open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

section S168
open Polynomial
lemma S168_cfc_diag {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) (f : ℝ → ℝ) :
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
end S168

lemma S168_ent {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  unfold vnEntropy
  rw [S168_cfc_diag, Matrix.trace_diagonal, Complex.re_sum]
  simp

lemma S168_l4 : Real.logb 2 (1 / 4) = -2 := by
  rw [one_div, Real.logb_inv, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]; norm_num
lemma S168_l2 : Real.logb 2 (1 / 2) = -1 := by
  rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]

-- matrices
local notation "SC" => separatingChannel
local notation "SL" => separatingLaw

lemma S168_WB1 : superWB1 SC SL = Matrix.diagonal (fun _ => ((1 / 4 : ℝ) : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, e⟩
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp [superWB1, superWB2, separatingChannel, separatingLaw, cqBlocks, traceRight, traceLeft,
      Matrix.diagonal, Fintype.sum_prod_type] <;> simp [Finset.filter_eq', Finset.filter_eq] <;> norm_num

lemma S168_WB2 : superWB2 SC SL =
    Matrix.diagonal (fun z : Bool × Bool => ((if z.1 = z.2 then 1 / 2 else 0 : ℝ) : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, e⟩
  cases a <;> cases b <;> cases c <;> cases e <;>
    simp [superWB1, superWB2, separatingChannel, separatingLaw, cqBlocks, traceRight, traceLeft,
      Matrix.diagonal, Fintype.sum_prod_type] <;> simp [Finset.filter_eq', Finset.filter_eq] <;> norm_num

lemma S168_WB1R : traceRight (superWB1 SC SL) = Matrix.diagonal (fun _ => ((1 / 2 : ℝ) : ℂ)) := by
  ext a c
  cases a <;> cases c <;>
    simp [superWB1, superWB2, separatingChannel, separatingLaw, cqBlocks, traceRight, traceLeft,
      Matrix.diagonal, Fintype.sum_prod_type] <;> simp [Finset.filter_eq', Finset.filter_eq] <;> norm_num

lemma S168_WB1L : traceLeft (superWB1 SC SL) = Matrix.diagonal (fun _ => ((1 / 2 : ℝ) : ℂ)) := by
  ext a c
  cases a <;> cases c <;>
    simp [superWB1, superWB2, separatingChannel, separatingLaw, cqBlocks, traceRight, traceLeft,
      Matrix.diagonal, Fintype.sum_prod_type] <;> simp [Finset.filter_eq', Finset.filter_eq] <;> norm_num

lemma S168_WB2R : traceRight (superWB2 SC SL) = Matrix.diagonal (fun _ => ((1 / 2 : ℝ) : ℂ)) := by
  ext a c
  cases a <;> cases c <;>
    simp [superWB1, superWB2, separatingChannel, separatingLaw, cqBlocks, traceRight, traceLeft,
      Matrix.diagonal, Fintype.sum_prod_type] <;> simp [Finset.filter_eq', Finset.filter_eq] <;> norm_num

lemma S168_WB2L : traceLeft (superWB2 SC SL) = Matrix.diagonal (fun _ => ((1 / 2 : ℝ) : ℂ)) := by
  ext a c
  cases a <;> cases c <;>
    simp [superWB1, superWB2, separatingChannel, separatingLaw, cqBlocks, traceRight, traceLeft,
      Matrix.diagonal, Fintype.sum_prod_type] <;> simp [Finset.filter_eq', Finset.filter_eq] <;> norm_num

lemma S168_TR (x : Bool × Bool) : traceRight (separatingChannel.rho x) =
    Matrix.diagonal (fun b : Bool => ((if b = x.2 then 1 else 0 : ℝ) : ℂ)) := by
  obtain ⟨u, v⟩ := x
  ext a c
  cases u <;> cases v <;> cases a <;> cases c <;>
    simp [separatingChannel, traceRight, Matrix.diagonal] <;> simp [Finset.filter_eq', Finset.filter_eq]

lemma S168_TOT : (∑ w, ∑ x, (separatingLaw.prob (w, x) : ℂ) • traceRight (separatingChannel.rho x)) =
    Matrix.diagonal (fun _ : Bool => ((1 / 2 : ℝ) : ℂ)) := by
  ext a c
  cases a <;> cases c <;>
    simp [superWB1, superWB2, separatingChannel, separatingLaw, cqBlocks, traceRight, traceLeft,
      Matrix.diagonal, Fintype.sum_prod_type] <;> simp [Finset.filter_eq', Finset.filter_eq] <;> norm_num


lemma S168_E0 (x : Bool × Bool) : vnEntropy (traceRight (separatingChannel.rho x)) = 0 := by
  rw [S168_TR, S168_ent]
  simp [Fintype.sum_bool, apply_ite]

lemma S168_Ehalf : vnEntropy (Matrix.diagonal (fun _ : Bool => ((1 / 2 : ℝ) : ℂ))) = 1 := by
  rw [S168_ent]; simp only [Fintype.sum_bool, S168_l2]; norm_num

lemma S168_EWB1 : vnEntropy (superWB1 SC SL) = 2 := by
  rw [S168_WB1, S168_ent]; simp only [Fintype.sum_prod_type, Fintype.sum_bool, S168_l4]; norm_num

lemma S168_EWB2 : vnEntropy (superWB2 SC SL) = 1 := by
  rw [S168_WB2, S168_ent]; simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [S168_l2]; norm_num

lemma S168_H : shannon (fun w => ∑ x, separatingLaw.prob (w, x)) = 1 := by
  have : (fun w => ∑ x, separatingLaw.prob (w, x)) = fun _ => 1 / 2 := by
    funext w; cases w <;> simp [separatingLaw, Fintype.sum_prod_type] <;> norm_num
  rw [this]; simp only [shannon, Fintype.sum_bool, S168_l2]; norm_num

lemma S168_priv : superPrivate SC SL = 1 := by
  simp only [superPrivate, S168_EWB1, S168_H, S168_E0, mul_zero, Finset.sum_const_zero]; norm_num

lemma S168_mi2 : quantumMI (superWB2 SC SL) = 1 := by
  simp only [quantumMI, S168_WB2R, S168_WB2L, S168_Ehalf, S168_EWB2]; norm_num

lemma S168_mi1 : quantumMI (superWB1 SC SL) = 0 := by
  simp only [quantumMI, S168_WB1R, S168_WB1L, S168_Ehalf, S168_EWB1]; norm_num

lemma S168_tot : superTotal SC SL = 1 := by
  simp only [superTotal, S168_TOT, S168_Ehalf, S168_E0, mul_zero, Finset.sum_const_zero]; norm_num

end QAlgorithms.Papers.Independent.Support50.P26

open QAlgorithms.Papers.Independent.Support50.P26
open QAlgorithms.Papers.Independent.Information100.P22 (Op quantumMI)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution :
    let C := separatingChannel
    let p := separatingLaw
    superPrivate C p = 1 ∧ quantumMI (superWB2 C p) = 1 ∧ superTotal C p = 1 ∧
    quantumMI (superWB1 C p) = 0 ∧
    SuccessiveRegion C p ⊂ SuperRegion C p ∧
    ((1 / 2, 1 / 2) : ℝ × ℝ) ∈ SuperRegion C p ∧
    ((1 / 2, 1 / 2) : ℝ × ℝ) ∉ SuccessiveRegion C p ∧
    successiveCorner C p ∈ SuccessiveRegion C p ∩ SuperRegion C p := by
  dsimp only
  have h1 := S168_priv; have h2 := S168_mi2; have h3 := S168_tot; have h4 := S168_mi1
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, fun hsub => ?_⟩
    · simp only [SuccessiveRegion, SuperRegion, Set.mem_setOf_eq, h1, h2, h3, h4] at hr ⊢
      refine ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ?_⟩; linarith [hr.2.2.2.2]
    · have : ((1 / 2, 1 / 2) : ℝ × ℝ) ∈ SuperRegion separatingChannel separatingLaw := by
        simp only [SuperRegion, Set.mem_setOf_eq, h1, h2, h3]; norm_num
      have h := hsub this
      simp only [SuccessiveRegion, Set.mem_setOf_eq, h4] at h
      linarith [h.2.2.2.2]
  · simp only [SuperRegion, Set.mem_setOf_eq, h1, h2, h3]; norm_num
  · simp only [SuccessiveRegion, Set.mem_setOf_eq, h4]; norm_num
  · simp only [successiveCorner, SuccessiveRegion, SuperRegion, Set.mem_inter_iff, Set.mem_setOf_eq,
      h1, h2, h3, h4]; norm_num

end
