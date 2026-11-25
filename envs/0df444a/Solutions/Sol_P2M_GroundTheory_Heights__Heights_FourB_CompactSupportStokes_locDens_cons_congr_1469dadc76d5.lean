-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_locDens_cons_congr_1469dadc76d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:30.689878+00:00
-- url     : https://prove2.me/submissions/5d1ad80b-9fe3-40aa-8871-c3ef2126685f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_CompactSupportStokes
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_cons


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff Manifold
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
theorem _root_.solution (A : FinHolAtlas (e + 1) X) {P Q : LocPot X} (Φ : Fin e → LocPot X)
    (h : P.φ = Q.φ) (k : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons P Φ) k y = locDens A (Fin.cons Q Φ) k y := by
  rw [locDens_cons, locDens_cons, h]
end GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
