-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_L4_proj_comm_abs__dd44a5ea645a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:35.402514+00:00
-- url     : https://prove2.me/submissions/62f606bc-c665-45ab-af11-0fb08c620197

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (PE A : V →ₗ[k] V) (R W L : Submodule k V) (h1 : PE ∘ₗ PE = PE)
    (h2 : LinearMap.range PE = R ⊓ W) (h3 : LinearMap.ker PE ⊓ W = L ⊓ W)
    (hR : ∀ x ∈ R, A x ∈ R) (hW : ∀ x ∈ W, A x ∈ W) (hL : ∀ x ∈ L, A x ∈ L) :
    ∀ x ∈ W, PE (A x) = A (PE x) := by
  intro x hx
  have hfix : ∀ y ∈ LinearMap.range PE, PE y = y := by
    rintro y ⟨z, rfl⟩
    rw [← LinearMap.comp_apply, h1]
  have hPx : PE x ∈ R ⊓ W := by
    rw [← h2]
    exact LinearMap.mem_range_self PE x
  have hA1 : A (PE x) ∈ R ⊓ W := ⟨hR _ hPx.1, hW _ hPx.2⟩
  have hA1' : PE (A (PE x)) = A (PE x) := hfix _ (by rw [h2]; exact hA1)
  have hker : x - PE x ∈ LinearMap.ker PE ⊓ W := by
    refine ⟨LinearMap.mem_ker.mpr ?_, W.sub_mem hx hPx.2⟩
    rw [map_sub, ← LinearMap.comp_apply, h1, sub_self]
  rw [h3] at hker
  have hA2 : A (x - PE x) ∈ LinearMap.ker PE ⊓ W := by
    rw [h3]
    exact ⟨hL _ hker.1, hW _ hker.2⟩
  have h0 : PE (A (x - PE x)) = 0 := hA2.1
  rw [map_sub, map_sub, hA1', sub_eq_zero] at h0
  exact h0
end Formalism.InvariantFactorPaths.L4
