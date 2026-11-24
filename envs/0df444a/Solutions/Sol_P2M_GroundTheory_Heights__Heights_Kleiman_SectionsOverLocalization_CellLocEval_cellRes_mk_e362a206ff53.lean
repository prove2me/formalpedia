-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_cellRes_mk_e362a206ff53
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:40.4404+00:00
-- url     : https://prove2.me/submissions/136a1647-b0d8-416d-91b2-65ca0414597c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsHomogOfMemQuotPartAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc mIdealOver mConeMapOver
  quotPart)
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
theorem _root_.solution {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] {J I : ∀ k, Finset (ι k)}
    (h : cellMon S J ≤ cellMon S I) (m : M) (t : cellMon S J) :
    cellRes S M J I (LocalizedModule.mk m t) = LocalizedModule.mk m ⟨t.1, h t.2⟩ := by
  unfold cellRes
  rw [dif_pos h, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
