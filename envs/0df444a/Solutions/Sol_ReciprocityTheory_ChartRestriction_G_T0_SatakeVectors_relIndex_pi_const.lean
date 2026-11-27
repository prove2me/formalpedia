-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.relIndex_pi_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:48:59.720067+00:00
-- url     : https://prove2.me/submissions/899a54da-ca23-429e-99d4-a838a2b6e19a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {M : Type*} [AddCommGroup M] (H L : AddSubgroup M) (k : ℕ) :
    (AddSubgroup.pi Set.univ fun _ : Fin k => H).relIndex (AddSubgroup.pi Set.univ fun _ : Fin k => L)
      = H.relIndex L ^ k := by
  let f : (Fin k → L) →+ (AddSubgroup.pi Set.univ fun _ : Fin k => L) :=
    { toFun := fun g => ⟨fun i => (g i : M), fun i _ => (g i).2⟩
      map_zero' := Subtype.ext (funext fun _ => rfl)
      map_add' := fun _ _ => Subtype.ext (funext fun _ => rfl) }
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨fun i => ⟨(x : Fin k → M) i, ?_⟩, Subtype.ext rfl⟩
    first
    | exact x.2 i (Set.mem_univ i)
    | exact AddSubgroup.mem_pi.mp x.2 i (Set.mem_univ i)
  have hcomap : AddSubgroup.comap f ((AddSubgroup.pi Set.univ fun _ : Fin k => H).addSubgroupOf
      (AddSubgroup.pi Set.univ fun _ : Fin k => L)) =
      AddSubgroup.pi Set.univ fun _ : Fin k => H.addSubgroupOf L := by
    ext g
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    all_goals rfl
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_comap_of_surjective ((AddSubgroup.pi Set.univ fun _ : Fin k => H).addSubgroupOf
      (AddSubgroup.pi Set.univ fun _ : Fin k => L)) hsurj, hcomap, AddSubgroup.index_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
