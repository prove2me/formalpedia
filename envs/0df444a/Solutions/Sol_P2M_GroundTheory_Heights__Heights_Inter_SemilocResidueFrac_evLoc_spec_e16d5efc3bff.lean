-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evLoc_spec_e16d5efc3bff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:55:50.493913+00:00
-- url     : https://prove2.me/submissions/d5f09902-a5e2-4bab-8f74-b0cba55bda0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueFrac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_evAt_algebraMap_c81db62de5d4

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
    (hx : RingHom.ker (aeval x : MRing ι →ₐ[ℤ] Ω) = W) {z : locRing P W} {u w : MRing ι}
    (e : (z : FractionRing (MRing ι ⧸ P)) * regularityLocalResidue_holds.frHom P w = regularityLocalResidue_holds.frHom P u) :
    evLoc P W hPW x hx z * aeval x w = aeval x u := by
  have e' : (⟨z, locRing_le P W hPW z.2⟩ : locAt P W hPW) * algebraMap _ _ (Ideal.Quotient.mk P w) =
      algebraMap _ _ (Ideal.Quotient.mk P u) := Subtype.ext e
  have h := congrArg (evAt P W hPW x hx) e'
  rw [map_mul, evAt_algebraMap, evAt_algebraMap] at h
  exact (congrArg (· * aeval x w) (rfl : evLoc P W hPW x hx z = evAt P W hPW x hx ⟨z, locRing_le P W hPW z.2⟩)).trans h
end GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
