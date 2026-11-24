-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_smul_8e170cd1372f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:12.249853+00:00
-- url     : https://prove2.me/submissions/16f5428a-6d15-4bf0-bcfc-a2e11983ceb2

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
theorem _root_.solution {p : MRingOver S ι} {a : K → ℕ} (s : S) (hp : IsMultiHomog p a) :
    IsMultiHomog (s • p) a :=
  fun m hm k => hp m (support_smul hm) k
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
