-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_RgTransfer_c__inv_a6ca6509e8fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:50:55.4451+00:00
-- url     : https://prove2.me/submissions/bfcf27a9-34b8-43c2-befb-8264f5e290dc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_isCh_one

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
theorem _root_.solution (hL : IsLevi Γ K Q Γ' K' π ι c₀) (a : Q) : c₀ ((a⁻¹ : Q) : G) = (c₀ a)⁻¹ := by
  have h := c₀_mul hL a⁻¹ a
  rw [inv_mul_cancel] at h
  have h1 : c₀ ((1 : Q) : G) = 1 := isCh_one hL.par.ch
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_left h.symm
end GlobalTheory.CompanionTheory.RgTransfer
