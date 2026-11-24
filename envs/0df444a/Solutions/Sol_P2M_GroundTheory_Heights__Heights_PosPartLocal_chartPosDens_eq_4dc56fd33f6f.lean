-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PosPartLocal_chartPosDens_eq_4dc56fd33f6f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:18.375022+00:00
-- url     : https://prove2.me/submissions/0403a676-3473-4830-923d-d06b8faeb5c2

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_term_eq_ead537038306


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.PosPartLocal
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.PosPartLocal
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin d → ℂ)} {W E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hsd : DifferentiableOn ℂ s U)
    (hsec : ∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J)
    (hW : IsOpen W) (hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x')
    (hEW : E ⊆ W) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    chartPosDens J A (E.indicator f) φ y = (U ∩ s ⁻¹' E).indicator
      (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y := by
  classical
  unfold chartPosDens sheetSum
  by_cases hy : y ∈ U ∩ s ⁻¹' E
  · rw [Set.indicator_of_mem hy]
    have hfib : s y ∈ fibre J A y := ⟨(hsec y hy.1).2, (hsec y hy.1).1⟩
    have hsh : IsSheetAt J A (s y) s :=
      ⟨U, hU, by rw [(hsec y hy.1).1]; exact hy.1, hsd, by rw [(hsec y hy.1).1], hsec, W,
        hW.mem_nhds (hEW hy.2), fun x' hx' _ => (hWs x' hx').2.symm⟩
    rw [finsum_eq_single _ (s y) ?_, finsum_eq_if, if_pos hfib, dif_pos ⟨s, hsh⟩]
    · have h := SheetSumMeasurable.term_eq (fun a b => max (a * b) 0) (E.indicator f) φ hsh ⟨s, hsh⟩
      rw [(hsec y hy.1).1] at h
      dsimp only
      rw [h, Set.indicator_of_mem (show s y ∈ E from hy.2)]
    · intro x hne
      rw [finsum_eq_if]
      split_ifs with hx h
      · have hxE : x ∉ E := fun hxE => hne (by
          have h' := (hWs x ⟨hx.1, hEW hxE⟩).2
          rw [hx.2] at h'
          exact h'.symm)
        dsimp only
        rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
      · rfl
      · rfl
  · rw [Set.indicator_of_notMem hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    split_ifs with h
    · have hxE : x ∉ E := fun hxE => hy (by
        obtain ⟨h1, h2⟩ := hWs x ⟨hx.1, hEW hxE⟩
        rw [hx.2] at h1 h2
        exact ⟨h1, by rw [Set.mem_preimage, h2]; exact hxE⟩)
      dsimp only
      rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
    · rfl
end GroundTheory.Heights₂.Heights.PosPartLocal
