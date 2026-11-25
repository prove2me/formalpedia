-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_append_pair_eq_8bf807583c1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:57:46.548118+00:00
-- url     : https://prove2.me/submissions/637269d6-2226-4315-b41e-6310c3da8f0e

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
theorem _root_.solution {n : ℕ} (L : Fin n → α) (A B : α) :
    (Fin.append L ![A, B] : Fin (n + 2) → α) = Fin.snoc (Fin.snoc L A : Fin (n + 1) → α) B := by
  have e : (![A, B] : Fin 2 → α) = Fin.snoc (![A] : Fin 1 → α) B := by
    funext i
    fin_cases i <;> rfl
  rw [e, Fin.append_snoc, Fin.append_right_eq_snoc]
  rfl
end GroundTheory.Heights₂.Heights.Inter.DiagRAux
