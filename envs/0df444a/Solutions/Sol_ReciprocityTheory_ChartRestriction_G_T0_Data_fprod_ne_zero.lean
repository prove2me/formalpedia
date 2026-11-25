-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.fprod_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:33:17.858807+00:00
-- url     : https://prove2.me/submissions/64023022-5764-4d0f-bf2e-7b6c83271be4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DePres
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AGFrameNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Hartogs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FprodNeZero
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


section
set_option linter.style.haveILetI false
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
private theorem gen_ne_zero_of_mem_htOne_heightData {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  obtain ⟨hpr, hht⟩ := hp
  have hne : p ≠ ⊥ := by
    rintro rfl
    first
      | (simp at hht; done)
      | (rw [Ideal.height_bot] at hht; exact zero_ne_one hht)
  obtain ⟨q, hqp, hq⟩ := hpr.exists_mem_prime_of_ne_bot hne
  have hqi : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  have hle : Ideal.span {q} ≤ p := (Ideal.span_singleton_le_iff_mem p).mpr hqp
  have hbot : (⊥ : Ideal (KTp K d.D d.N)) < Ideal.span {q} :=
    bot_lt_iff_ne_bot.mpr (by simpa using hq.ne_zero)
  haveI := hpr
  haveI := hqi
  have hspan : Ideal.span {q} = p := by
    by_contra hne'
    have hlt : Ideal.span {q} < p := lt_of_le_of_ne hle hne'
    have h3 : (Ideal.span {q}).height < 1 := by
      have hp1 : p.height ≤ (1 : ℕ) := by rw [hht]; rfl
      exact (Ideal.height_le_iff.mp hp1) _ hqi hlt
    have h0 : (Ideal.span {q}).height ≤ (0 : ℕ) := by
      rw [ENat.lt_one_iff_eq_zero] at h3
      rw [h3]; rfl
    have h2 := (Ideal.height_le_iff.mp h0) ⊥ Ideal.bot_prime hbot
    first
      | (simp at h2; done)
      | exact absurd h2 (not_lt_of_ge bot_le)
      | exact ENat.not_lt_zero _ h2
  have hprin : p.IsPrincipal := ⟨⟨q, hspan.symm⟩⟩
  haveI := hprin
  simp only [Data.gen, dif_pos hprin]
  intro h0
  exact hne ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

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
theorem _root_.solution (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite) :
    (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) ≠ 0 := by
  refine finprod_mem_induction (fun x => x ≠ 0) one_ne_zero (fun x y hx hy => mul_ne_zero hx hy) ?_
  intro q hq
  apply zpow_ne_zero
  have hg := gen_ne_zero_of_mem_htOne_heightData d hq
  first
    | exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hg
    | exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hg
    | exact (map_ne_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective _ _)).mpr hg
    | (simpa using hg)
end ReciprocityTheory.ChartRestriction.G.T0.Data
