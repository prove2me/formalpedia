-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_evMap_mk__1e00d859a561
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:11.55942+00:00
-- url     : https://prove2.me/submissions/46e46e3c-b8c3-4e9e-bdf9-288f195125d6

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
variable {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
variable {y}
variable (y)
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
theorem _root_.solution {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) (m : MRingOver S ι ⧸ mIdealOver S y)
    (t : cellMon S I) :
    evMap y I (LocalizedModule.mk m t) = ev0 y m / aeval y (t : MRingOver S ι) := by
  unfold evMap
  rw [dif_pos hI]
  exact ev_mk y I hI _ t
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
