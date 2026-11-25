-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_cxHessian_pot_snoc_1ce7e36a8e4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:29.395116+00:00
-- url     : https://prove2.me/submissions/f9094045-fc1f-40da-90cd-4f26ab6e52fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMixSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRSlotAdd

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {n : ℕ} (L : Fin n → HermLine ι) (A X : HermLine ι)
    (γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ) (y : Fin (n + 1) → ℂ) :
    (fun k => cxHessian (fun y' => pot (Fin.snoc L X) k (γ y')) y) =
      Function.update (fun k => cxHessian (fun y' => pot (Fin.snoc L A) k (γ y')) y) (Fin.last n)
        (cxHessian (fun y' => Real.log (X.h (γ y'))) y) := by
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
  · rw [Function.update_of_ne (Fin.castSucc_ne_last j)]
    simp only [pot, Fin.snoc_castSucc]
  · rw [Function.update_self]
    simp only [pot, Fin.snoc_last]
end GroundTheory.Heights₂.Heights.Inter
