-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.x4v4_ordMM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:57:47.800266+00:00
-- url     : https://prove2.me/submissions/ff17560b-e948-4620-b5b5-43a0b9ed4a9b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_X4v4RatioSpec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_x4v4_eq_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_x4v4_ratio_ne
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_adm
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) {f : A c}
    (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c (d.Wres c w) f = WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c))) +
      d.ordMM c (d.Wres c w) (d.w (d.jc c) c) := by
  have hA := d.good_adm hd h c hp hw
  have e : ((d.ord c (d.Wres c w) d.wL f : ℤ) : WithTop ℤ) =
      d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) +
        (d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) : WithTop ℤ) := by
    conv_lhs => rw [d.x4v4_eq_smul hd c hf]
    exact hd.ord_smul c _ hA _ (hd.w_mem _ _) (hd.w_base c) (d.x4v4_ratio_ne hd c hf hf0)
  have hfin : d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) =
      ((d.ord c (d.Wres c w) d.wL f - d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) : ℤ) : WithTop ℤ) := by
    revert e
    generalize d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) = t
    intro e
    induction t using WithTop.recTopCoe with
    | top => simp at e
    | coe t =>
      have e' : d.ord c (d.Wres c w) d.wL f = t + d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) := by
        exact_mod_cast e
      rw [e']
      congr 1
      ring
  unfold ordMM
  rw [hfin, WithTop.untopD_coe]
  ring
end ReciprocityTheory.ChartRestriction.G.T0.Data
