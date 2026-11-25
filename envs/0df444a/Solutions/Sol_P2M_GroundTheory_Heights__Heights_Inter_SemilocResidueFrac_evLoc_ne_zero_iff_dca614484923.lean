-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evLoc_ne_zero_iff_dca614484923
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:15:53.337794+00:00
-- url     : https://prove2.me/submissions/5d060eef-0fdd-4c22-af4e-4c76426928c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueFrac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evLoc_spec_e16d5efc3bff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_isUnit_of_rep_302d1e1b094c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_exists_rep_569c3fcb9a3c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
theorem _root_.solution (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (x : (Σ k, ι k) → Ω)
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) {z : locRing P W} :
    evLoc P W hPW x hx z ≠ 0 ↔ IsUnit z := by
  refine ⟨fun hz => ?_, fun hz => (hz.map (evLoc P W hPW x hx)).ne_zero⟩
  obtain ⟨u, w, a, hu, hw, hwW, e⟩ := regularityLocalResidue_holds.exists_rep ‹W.IsPrime› z.2
  have h := evLoc_spec P W hPW x hx e
  refine isUnit_of_rep P W hPW hu hw (fun huW => hz ?_) e
  rw [(aeval_eq_zero_iff W x hx).2 huW] at h
  exact (mul_eq_zero.1 h).resolve_right (mt (aeval_eq_zero_iff W x hx).1 hwW)
end GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
