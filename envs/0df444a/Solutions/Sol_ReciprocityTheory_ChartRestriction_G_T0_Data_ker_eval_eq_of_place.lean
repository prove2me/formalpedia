-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.ker_eval_eq_of_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:57:15.703862+00:00
-- url     : https://prove2.me/submissions/a63dc4c7-82d0-4cdf-bb22-3f8ab56db799

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ker_eval_isPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ker_eval_ne_bot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_ker_eval_le_of_place

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.OverP c p)
    (htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) (hy : 0 < w (d.rationalBaseRow c)) :
    kerP (K := K) (D := d.D) (d.jc c) (d.x c) = p := by
  have hle := d.ker_eval_le_of_place hd c hw htriv hy
  have hprime := ker_eval_isPrime (K := K) (D := d.D) (d.jc c) (d.x c)
  have hne := ker_eval_ne_bot (K := K) (hd.trdeg c) (d.jc c) (d.x c)
  obtain ⟨hpp, hph⟩ := hp
  by_contra hneq
  have hlt := lt_of_le_of_ne hle hneq
  have h1 : p.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hph]; simp
  have h2 := (Ideal.height_le_iff.mp h1) _ hprime hlt
  have h3 : ¬ (kerP (K := K) (D := d.D) (d.jc c) (d.x c)).height ≤ ((0 : ℕ) : ℕ∞) := by
    intro h0
    have h4 := (Ideal.height_le_iff.mp h0) ⊥ Ideal.bot_prime (bot_lt_iff_ne_bot.mpr hne)
    simp at h4
  apply h3
  have h5 : (kerP (K := K) (D := d.D) (d.jc c) (d.x c)).height = 0 :=
    ENat.lt_one_iff_eq_zero.mp (by simpa using h2)
  rw [h5]
  simp
end ReciprocityTheory.ChartRestriction.G.T0.Data
