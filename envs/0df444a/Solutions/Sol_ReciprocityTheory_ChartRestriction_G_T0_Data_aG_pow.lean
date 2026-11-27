-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.aG_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:03:14.148804+00:00
-- url     : https://prove2.me/submissions/e5ab216a-6b56-4a3d-8bbc-7d0944c4d400

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumLeOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_pow_mem_ne
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_nP_mul
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


section
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
private lemma finsum_mem_const_mul {α : Type*} (s : Set α) (f : α → ℤ) (k : ℤ) (hk : k ≠ 0) :
    ∑ᶠ x ∈ s, k * f x = k * ∑ᶠ x ∈ s, f x := by
  classical
  have hs : s ∩ Function.support (fun x => k * f x) = s ∩ Function.support f := by
    ext x
    simp [hk]
  by_cases hf : (s ∩ Function.support f).Finite
  · rw [finsum_mem_eq_sum_of_inter_support_eq (fun x => k * f x) (t := hf.toFinset) (by
        ext x
        simp [hk]
        try tauto),
      finsum_mem_eq_sum_of_inter_support_eq f (t := hf.toFinset) (by
        ext x
        simp
        try tauto),
      Finset.mul_sum]
  · rw [finsum_mem_eq_zero_of_infinite hf, finsum_mem_eq_zero_of_infinite (by rwa [hs]), mul_zero]
private lemma nP_pow_succ_eq_succ_mul (hd : d.AxH 𝒜) (h : d.S1) {G : WT} {ta : ∀ c, A c}
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (n : ℕ) : d.nP h c ((n + 1) • G) ((ta ^ (n + 1)) c) p = ((n : ℤ) + 1) * d.nP h c G (ta c) p := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (ta ^ (n + 1 + 1)) c = (ta ^ (n + 1)) c * ta c := by rw [pow_succ, Pi.mul_apply]
    rw [e, succ_nsmul G (n + 1), d.nP_mul hd h c (d.pow_mem_ne hd hta n c).1 (hta c).1
      (d.pow_mem_ne hd hta n c).2 (hta c).2 hp, ih]
    push_cast
    ring
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) {G : WT} {ta : ∀ c, A c}
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (n : ℕ) :
    d.aG h ((n + 1) • G) (ta ^ (n + 1)) = (n + 1) * d.aG h G ta := by
  unfold aG
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← finsum_mem_const_mul _ (fun p => d.nP h c G (ta c) p * (d.dg (d.gen p) : ℤ)) ((n : ℤ) + 1) (by positivity)]
  refine finsum_mem_congr rfl fun p hp => ?_
  rw [nP_pow_succ_eq_succ_mul d hd h hta c hp n, mul_assoc]
end ReciprocityTheory.ChartRestriction.G.T0.Data
