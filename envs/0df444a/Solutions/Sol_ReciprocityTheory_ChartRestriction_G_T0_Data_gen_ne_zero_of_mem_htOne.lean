-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.gen_ne_zero_of_mem_htOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:14:48.469615+00:00
-- url     : https://prove2.me/submissions/89e89853-58ef-4cde-bc8e-ef74f6a78093

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SphereMeanSubArchimedean
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteHeightFractionRepr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_heightOne_principal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  obtain ⟨hpr, hh⟩ := hp
  haveI := hpr
  obtain ⟨g, hg, hpg⟩ := ValUFD.heightOne_principal p hh
  have hPr : p.IsPrincipal := ⟨⟨g, hpg⟩⟩
  unfold gen
  rw [dif_pos hPr]
  intro h0
  have hbot : p = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).2 h0
  rw [hbot] at hpg
  exact hg.ne_zero (Ideal.span_singleton_eq_bot.1 hpg.symm)
end ReciprocityTheory.ChartRestriction.G.T0.Data
