-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.split_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:56:06.177295+00:00
-- url     : https://prove2.me/submissions/cf6fe11d-caae-42af-a594-dfb6f8d33e7c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LocAt_unitAt_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LocAt_unitAt_zpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LocAt_unitAt_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_gen_not_mem
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
set_option linter.style.haveILetI false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite)
    {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    ∃ V : KTf K d.D d.N, LocAt.UnitAt p V ∧
      (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p * V := by
  haveI := hp.1
  have hfin : ((d.HtOne \ {p}) ∩ Function.mulSupport
      (fun q => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q)).Finite := by
    refine hE.subset ?_
    rintro q ⟨⟨hq, _⟩, hq1⟩
    refine ⟨hq, fun h0 => (Function.mem_mulSupport.mp hq1) ?_⟩
    simp [h0]
  refine ⟨∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne \ {p}), algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q, ?_, ?_⟩
  · rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod _ hfin]
    apply LocAt.unitAt_prod
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨⟨hq1, hq2⟩, _⟩ := hq
    exact LocAt.unitAt_zpow
      (LocAt.unitAt_alg (d.gen_not_mem hp hq1 (fun h => hq2 (Set.mem_singleton_iff.mpr h)))) _
  · have hins : d.HtOne = insert p (d.HtOne \ {p}) := by
      ext x
      by_cases hx : x = p
      · subst hx
        simp [hp]
      · simp [hx]
    conv_lhs => rw [hins]
    rw [finprod_mem_insert' _ (fun h => h.2 (Set.mem_singleton p)) hfin]
end ReciprocityTheory.ChartRestriction.G.T0.Data
