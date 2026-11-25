-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.substRowZero_fix_of_degree_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:30:44.045342+00:00
-- url     : https://prove2.me/submissions/703b25dd-b1aa-471d-88f1-db907ec8de82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstRowZeroFixOfDegreeZero
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
theorem _root_.solution (x : Fin (d.N + 1) → K) (q : KTp K d.D d.N)
    (hq : ∀ s ∈ q.support, ∑ j, s (0, j) = 0) : d.sub0 x q = q := by
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  conv_rhs => rw [q.as_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h0 : ∀ j, s (0, j) = 0 := fun j =>
    (Finset.sum_eq_zero_iff.mp (hq s hs)) j (Finset.mem_univ _)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun v hv => ?_
  have hv0 : v.1 ≠ 0 := by
    intro h1
    apply Finsupp.mem_support_iff.mp hv
    have e : ((0 : Fin (d.D + 1)), v.2) = v := Prod.ext h1.symm rfl
    rw [← e]
    exact h0 v.2
  simp [hv0]
end ReciprocityTheory.ChartRestriction.G.T0.Data
