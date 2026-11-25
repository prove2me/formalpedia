-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.hx4v2_ratio_wx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:54.451295+00:00
-- url     : https://prove2.me/submissions/b8a60118-7fb9-43e3-899e-ab8c46ca4e9d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormGenericRatioSpec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hx4v2_ratio_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hx4v2_eq_ratio_smul

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
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (x : Fin (d.N + 1) → K) :
    ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) =
      ∑ j, algebraMap K (Ω c) (x j) * ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) := by
  have := hd.tower c
  have hg := hd.w_base c
  have hrep : ∀ j, d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
    fun j => hx4v2_eq_ratio_smul _ (hd.finrank_one c d.wL) (hd.w_mem j c) (hd.w_mem (d.jc c) c) hg
  have hsum : d.wx x c = (∑ j, algebraMap K (Ω c) (x j) *
      ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) • d.w (d.jc c) c := by
    simp only [Data.wx, Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [hrep j]
    rw [mul_smul, algebraMap_smul]
  rw [hsum, hx4v2_ratio_smul hg]
end ReciprocityTheory.ChartRestriction.G.T0.Data
