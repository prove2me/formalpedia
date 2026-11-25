-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_quotient_span_sub_b356f7ceefe4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:10.38406+00:00
-- url     : https://prove2.me/submissions/64215f5a-2fe4-4f69-a856-3ac90a425f89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSublattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E]
    [Module (𝓞 K) E] (F : Submodule (𝓞 K) E) {ι : Type*} (s : ι → F) :
    Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : E))) =
      Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) * Nat.card (E ⧸ F) := by
  set S := Submodule.span (𝓞 K) (Set.range s)
  set T := Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : E))
  have hspan : T = S.map F.subtype := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have hTF : T ≤ F := by
    rw [hspan]; exact Submodule.map_subtype_le F S
  rw [← Submodule.card_quotient_mul_card_quotient F T hTF]
  congr 1
  have hk : LinearMap.ker (T.mkQ ∘ₗ F.subtype) = S := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, hspan,
      Submodule.comap_map_eq_of_injective F.injective_subtype]
  have hr : LinearMap.range (T.mkQ ∘ₗ F.subtype) = F.map T.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hk, ← hr]
  exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm
end GroundTheory.Heights₂.Heights.LatticeLemmas
