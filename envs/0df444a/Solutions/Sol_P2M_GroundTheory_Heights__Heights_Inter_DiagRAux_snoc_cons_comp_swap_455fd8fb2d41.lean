-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_snoc_cons_comp_swap_455fd8fb2d41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:56:51.516049+00:00
-- url     : https://prove2.me/submissions/785a95b4-820e-4960-8a6d-d2b9528d99bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {α : Type*}
namespace GroundTheory.Heights₂.Heights.Inter.DiagRAux
theorem _root_.solution {n : ℕ} (A B : α) (L : Fin n → α) :
    (Fin.snoc (Fin.cons A L : Fin (n + 1) → α) B : Fin (n + 2) → α) ∘ Equiv.swap 0 (Fin.last (n + 1)) =
      Fin.snoc (Fin.cons B L : Fin (n + 1) → α) A := by
  funext i
  simp only [Function.comp]
  by_cases h0 : i = 0
  · subst h0
    rw [Equiv.swap_apply_left, ← Fin.castSucc_zero, Fin.snoc_last, Fin.snoc_castSucc, Fin.cons_zero]
  by_cases hl : i = Fin.last (n + 1)
  · subst hl
    rw [Equiv.swap_apply_right, Fin.snoc_last, ← Fin.castSucc_zero, Fin.snoc_castSucc, Fin.cons_zero]
  rw [Equiv.swap_apply_of_ne_of_ne h0 hl]
  obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 hl
  have hi' : i' ≠ 0 := fun h => h0 (by rw [h, Fin.castSucc_zero])
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi'
  rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.cons_succ, Fin.cons_succ]
end GroundTheory.Heights₂.Heights.Inter.DiagRAux
