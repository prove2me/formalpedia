-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_zero_subsingleton_fd8caf63e24d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:54:45.884709+00:00
-- url     : https://prove2.me/submissions/b9542355-ac05-44e7-bc2c-0407c1390c6c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]
omit [LinearOrder K] [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution : Subsingleton (KH.Cell K ι 0) :=
  ⟨fun I J => Subtype.ext (funext fun k => (I.2.1 k).eq_univ.trans (J.2.1 k).eq_univ.symm)⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel
