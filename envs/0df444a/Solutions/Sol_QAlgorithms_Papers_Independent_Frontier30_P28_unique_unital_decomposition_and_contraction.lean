-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P28.unique_unital_decomposition_and_contraction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:32:50.723632+00:00
-- url     : https://prove2.me/submissions/846ab35f-720d-49a9-b4e3-4e1e5b5017b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_unitality_contractivity_equivalences

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder
open QAlgorithms.Papers.Independent.Frontier30.P28
open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)
open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)
open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

theorem solution (n : ℕ) (hn : 0 < n) (T : Lin n n)
    (htrace : TracePreserving T) :
    let N := nonunitalOffset T
    let U := unitalPart T
    N.trace = 0 ∧ IsUnital U ∧ TracePreserving U ∧
    (∀ A : M n, T A = A.trace • N + U A) ∧
    (∀ (Nother : M n) (Uother : Lin n n),
      Nother.trace = 0 → IsUnital Uother → TracePreserving Uother →
      (∀ A : M n, T A = A.trace • Nother + Uother A) →
      Nother = N ∧ Uother = U) ∧
    (IsPositiveMap U → ∀ p : ℝ≥0∞, 1 ≤ p →
      restrictedPNorm p T (fun A => A.trace = 0) ≤ 1) := by
  dsimp only
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hId : (1 : M n).trace = (n : ℂ) := by simp
  have hN : (nonunitalOffset T).trace = 0 := by
    rw [nonunitalOffset, Matrix.trace_smul, Matrix.trace_sub, htrace, sub_self, smul_zero]
  have hU : IsUnital (unitalPart T) := by
    change T 1 - (1 : M n).trace • nonunitalOffset T = 1
    rw [hId, nonunitalOffset, smul_smul, mul_inv_cancel₀ hnC, one_smul]
    abel
  have hUT : TracePreserving (unitalPart T) := by
    intro A
    change (T A - A.trace • nonunitalOffset T).trace = A.trace
    rw [Matrix.trace_sub, Matrix.trace_smul, hN, smul_zero, sub_zero]
    exact htrace A
  have hdecomp : ∀ A : M n,
      T A = A.trace • nonunitalOffset T + unitalPart T A := by
    intro A
    change T A = A.trace • nonunitalOffset T + (T A - A.trace • nonunitalOffset T)
    abel
  refine ⟨hN, hU, hUT, hdecomp, ?_, ?_⟩
  · intro Nother Uother _ hUother _ hother
    have hI := hother (1 : M n)
    change Uother 1 = 1 at hUother
    rw [hUother, hId] at hI
    have hNother : Nother = nonunitalOffset T := by
      have heq : (n : ℂ) • Nother = T 1 - 1 := by rw [hI]; abel
      calc
        Nother = (n : ℂ)⁻¹ • ((n : ℂ) • Nother) := by
          rw [smul_smul, inv_mul_cancel₀ hnC, one_smul]
        _ = nonunitalOffset T := by rw [heq]; rfl
    refine ⟨hNother, ?_⟩
    apply LinearMap.ext
    intro A
    have hA := (hother A).symm.trans (hdecomp A)
    rw [hNother] at hA
    exact add_left_cancel hA
  · intro hpos p hp
    have hfull : inducedPNorm p (unitalPart T) ≤ 1 :=
      (unitality_contractivity_equivalences n hn (unitalPart T) hpos hUT).2.1.mp hU p hp
    unfold restrictedPNorm
    refine iSup_le fun A => ?_
    have hsame : unitalPart T A.val = T A.val := by
      change T A.val - A.val.trace • nonunitalOffset T = T A.val
      rw [A.property.1, zero_smul, sub_zero]
    rw [← hsame]
    exact le_trans (le_iSup_of_le ⟨A.val, trivial, A.property.2⟩ le_rfl) hfull
