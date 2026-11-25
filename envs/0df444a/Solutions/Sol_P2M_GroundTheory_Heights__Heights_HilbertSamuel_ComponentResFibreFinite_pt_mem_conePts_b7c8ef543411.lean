-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_pt_mem_conePts_b7c8ef543411
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:21:48.581431+00:00
-- url     : https://prove2.me/submissions/1ebda116-a9f4-45a5-bde9-82624eb3f0e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResFibreFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComponentResFibreFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
theorem _root_.solution (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e) (x : R.R.M) :
    R.pt x ∈ ReciprocityTheory.AnForm.R.conePts W :=
  R.R.lift_mem (R.idx x) x (R.mem_src_idx x)
end GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
