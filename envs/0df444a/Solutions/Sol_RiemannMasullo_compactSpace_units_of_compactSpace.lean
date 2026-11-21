-- Prove2me | solution 1 for RiemannMasullo.compactSpace_units_of_compactSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:16:07.968256+00:00
-- url     : https://prove2.me/submissions/4966c6e3-a23c-4fd0-822a-6e3e344675bc

module
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Compactness.Compact
public import Definitions.Def_RiemannMasullo_ForMathlib_Topology_Algebra_Group_Units

set_option autoImplicit false
@[expose] public section
public section
open RiemannMasullo
open Topology
namespace RiemannMasullo
theorem _root_.solution (M : Type*) [Monoid M]
    [TopologicalSpace M] [T2Space M] [ContinuousMul M] [CompactSpace M] :
    CompactSpace Mˣ := by
  refine IsClosedEmbedding.compactSpace ⟨Units.isEmbedding_embedProduct, ?_⟩
  have hrange : Set.range (Units.embedProduct M) =
      {p | p.1 * MulOpposite.unop p.2 = 1} ∩ {p | MulOpposite.unop p.2 * p.1 = 1} := by
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val_inv, u.inv_val⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨p.1, MulOpposite.unop p.2, h, h'⟩, by cases p; rfl⟩
  rw [hrange]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
    continuous_const).inter (isClosed_eq
      ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)
end RiemannMasullo
