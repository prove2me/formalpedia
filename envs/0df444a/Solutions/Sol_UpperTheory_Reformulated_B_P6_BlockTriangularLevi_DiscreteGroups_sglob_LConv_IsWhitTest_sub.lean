-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.BlockTriangularLevi.DiscreteGroups.sglob.LConv.IsWhitTest.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:25:18.302581+00:00
-- url     : https://prove2.me/submissions/ceef72a7-8c84-4994-961b-923ffc95eb77

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_BlockTriangularLevi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.BlockTriangularLevi
open scoped Sigma DFunLike EquivLike Equiv Matrix CommSemiring CommRing Membership Set Preorder PartialOrder SemilatticeInf Lattice DistribLattice MulZeroClass Units Semiring HMul MulOne MulOneClass Monoid DivInvMonoid Group OfNat One Inv InvOneClass DivInvOneMonoid DivisionMonoid Subgroup Submonoid Subsemigroup Subtype SetLike MulZeroOneClass MonoidHom OneHom Pi PUnit Fin Finset HAdd AddMonoidWithOne AddGroupWithOne Ring DivisionRing Field CommGroup Circle DivisionSemiring Semifield Complex SeminormedRing SeminormedCommRing NormedCommRing NormedField AddChar Zero HSub
namespace UpperTheory.Reformulated.B.P6.BlockTriangularLevi
namespace DiscreteGroups.sglob.LConv.IsWhitTest
theorem _root_.solution :
    ∀ {k : Type} [inst_h0 : Field k] [inst_h1 : TopologicalSpace k] {m : ℕ} {ψ : AddChar k Circle} {f f' : GL (Fin m) k → ℂ}, DiscreteGroups.sglob.LConv.IsWhitTest ψ f → DiscreteGroups.sglob.LConv.IsWhitTest ψ f' → DiscreteGroups.sglob.LConv.IsWhitTest (m := m) ψ fun (g : GL (Fin m) k) ↦ f g - f' g := by
  intro k _ _ m ψ f f' hf hf'
  unfold DiscreteGroups.sglob.LConv.IsWhitTest at hf hf' ⊢
  obtain ⟨h1, h2, C, hC, h3⟩ := hf
  obtain ⟨h1', h2', C', hC', h3'⟩ := hf'
  refine ⟨?_, h2.sub h2', C ∪ C', hC.union hC', ?_⟩
  · intro u hu g
    beta_reduce
    rw [h1 u hu g, h1' u hu g, mul_sub]
  · intro g hg
    beta_reduce at hg
    by_cases hfg : f g = 0
    · have hfg' : f' g ≠ 0 := by
        intro h
        apply hg
        rw [hfg, h, sub_zero]
      obtain ⟨u, hu, c, hc, rfl⟩ := h3' g hfg'
      exact ⟨u, hu, c, Set.mem_union_right _ hc, rfl⟩
    · obtain ⟨u, hu, c, hc, rfl⟩ := h3 g hfg
      exact ⟨u, hu, c, Set.mem_union_left _ hc, rfl⟩
end DiscreteGroups.sglob.LConv.IsWhitTest
end UpperTheory.Reformulated.B.P6.BlockTriangularLevi
