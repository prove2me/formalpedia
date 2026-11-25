-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_RgTransfer_k__cont_339454cbab40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:57.141842+00:00
-- url     : https://prove2.me/submissions/fc4d1b2b-6e0d-4529-b9af-904c2bc4f386

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgTransfer
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']
variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution (hL : IsLevi Γ K Q Γ' K' π ι c₀) : Continuous (kι hL) :=
  Continuous.subtype_mk (continuous_subtype_val.comp (hL.contι.comp continuous_subtype_val)) _
end GlobalTheory.CompanionTheory.RgTransfer
