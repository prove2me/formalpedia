-- Prove2me | solution 1 for UpperTheory.Reformulated.B.DYhc7.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:55:08.65252+00:00
-- url     : https://prove2.me/submissions/fe2e32ab-ffd2-4c31-b5d7-8907ba4dc5e8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_Iwa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.DYhc7
theorem _root_.solution :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] {K P : Subgroup G},
      IsCompact (↑K : Set G) →
        IsClosed (↑P : Set G) →
          UpperTheory.Reformulated.B.DYhc7.Iwa P K → Topology.IsQuotientMap fun (x : ↥P × ↥K) ↦ (↑x.1 : G) * (↑x.2 : G) := by
  intro G _ _ _ K P hK hP hI
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let h : G × K ≃ₜ G × K :=
    { toFun := fun y => (y.1 * (y.2 : G), y.2)
      invFun := fun y => (y.1 * (y.2 : G)⁻¹, y.2)
      left_inv := fun y => by simp
      right_inv := fun y => by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hι : Topology.IsClosedEmbedding (Prod.map (Subtype.val : P → G) (id : K → K)) :=
    hP.isClosedEmbedding_subtypeVal.prodMap Topology.IsClosedEmbedding.id
  have hcl : IsClosedMap (fun x : ↥P × ↥K ↦ (x.1 : G) * (x.2 : G)) := by
    have h1 : IsClosedMap (Prod.fst : G × K → G) := isClosedMap_fst_of_compactSpace
    exact h1.comp (h.isClosedMap.comp hι.isClosedMap)
  refine hcl.isQuotientMap (by fun_prop) ?_
  intro g
  obtain ⟨p, hp, k, hk, rfl⟩ := hI g
  exact ⟨(⟨p, hp⟩, ⟨k, hk⟩), rfl⟩
end UpperTheory.Reformulated.B.DYhc7
