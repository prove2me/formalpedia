-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.lineSection_pow_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:45:56.777291+00:00
-- url     : https://prove2.me/submissions/a66b5c1c-3918-4a86-966f-507d1fc5337f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorHeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_lineSection_pow_mem

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
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (k : ℕ) : d.w (d.jc c) c ^ k ≠ 0 := by
  induction k with
  | zero =>
    haveI : Nontrivial (A c) := nontrivial_of_ne _ _ (hd.w_base c)
    rw [pow_zero]
    exact one_ne_zero
  | succ k ih =>
    rw [pow_succ]
    exact hd.mul_ne_zero c (lineSection_pow_mem d hd c k) (hd.w_mem _ _) ih (hd.w_base c)
end ReciprocityTheory.ChartRestriction.G.T0.Data
