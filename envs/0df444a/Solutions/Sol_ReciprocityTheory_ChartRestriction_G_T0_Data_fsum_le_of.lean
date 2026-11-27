-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.fsum_le_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:58:06.99368+00:00
-- url     : https://prove2.me/submissions/3867b1ac-2171-45c6-94f6-b0f00a46590f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumLeOf
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
theorem _root_.solution {α : Type*} (s : Set α) (f g : α → ℤ) (hf : {x | x ∈ s ∧ f x ≠ 0}.Finite)
    (hg : {x | x ∈ s ∧ g x ≠ 0}.Finite) (r : ℝ) (hle : ∀ x ∈ s, (f x : ℝ) ≤ r * g x) :
    ((∑ᶠ x ∈ s, f x : ℤ) : ℝ) ≤ r * ((∑ᶠ x ∈ s, g x : ℤ) : ℝ) := by
  classical
  set u : Finset α := (hf.union hg).toFinset with hu
  have hus : ∀ x ∈ u, x ∈ s := by
    intro x hx
    simp only [hu, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq] at hx
    rcases hx with h | h
    · exact h.1
    · exact h.1
  have ef : ∑ᶠ x ∈ s, f x = ∑ x ∈ u, f x := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [hu, Set.Finite.coe_toFinset, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      Function.mem_support]
    tauto
  have eg : ∑ᶠ x ∈ s, g x = ∑ x ∈ u, g x := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext x
    simp only [hu, Set.Finite.coe_toFinset, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq,
      Function.mem_support]
    tauto
  rw [ef, eg, Int.cast_sum, Int.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx => hle x (hus x hx)
end ReciprocityTheory.ChartRestriction.G.T0.Data
