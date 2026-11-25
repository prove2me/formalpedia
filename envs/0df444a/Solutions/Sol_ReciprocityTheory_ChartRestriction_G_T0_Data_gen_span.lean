-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.gen_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:05:30.617688+00:00
-- url     : https://prove2.me/submissions/c3bfcedd-9151-46c4-a2ad-59808d79377b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : p = Ideal.span {d.gen p} := by
  obtain ⟨hprime, hh⟩ := hp
  haveI := hprime
  have hne : p ≠ ⊥ := by
    rintro rfl
    rw [Ideal.height_bot] at hh
    exact zero_ne_one hh
  obtain ⟨q, hqp, hq⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hprime hne
  have hsq : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  have hle : Ideal.span {q} ≤ p := (Ideal.span_singleton_le_iff_mem _).mpr hqp
  have heq : Ideal.span {q} = p := by
    by_contra hne2
    haveI := hsq
    have hqb : (⊥ : Ideal (KTp K d.D d.N)) < Ideal.span {q} := by
      rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact hq.ne_zero
    have h1 : (Ideal.span {q}).height < ((1 : ℕ) : ℕ∞) :=
      (Ideal.height_le_iff (n := 1)).mp (by rw [hh]; norm_num) _ hsq (lt_of_le_of_ne hle hne2)
    have h2 : ¬ (Ideal.span {q}).height ≤ ((0 : ℕ) : ℕ∞) := by
      rw [Ideal.height_le_iff]
      push_neg
      exact ⟨⊥, Ideal.bot_prime, hqb, by simp⟩
    apply h2
    have h1' : (Ideal.span {q}).height < 1 := by simpa using h1
    simpa using ENat.lt_one_iff_eq_zero.mp h1'
  have hpr : p.IsPrincipal := ⟨⟨q, heq.symm⟩⟩
  unfold Data.gen
  rw [dif_pos hpr]
  exact (Ideal.span_singleton_generator p).symm
end ReciprocityTheory.ChartRestriction.G.T0.Data
