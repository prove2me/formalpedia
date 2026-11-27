-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.ratio_linearCombination_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:43:59.294056+00:00
-- url     : https://prove2.me/submissions/7a95fdec-ca19-4309-ab1e-681595ec1ede

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationGenericRatioEqRestriction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightProdPowMultiHomogeneous
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero


section
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField ReciprocityTheory.MultiplicativeHeights
namespace Data
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
variable (d : Data K ι Ω WT A)
private lemma ratio_eq_of_eq_smul' {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V} {a : Ω'}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  have hex : ∃ b : Ω', f = b • g := ⟨a, h⟩
  unfold ratio
  rw [dif_pos hex]
  have hc := hex.choose_spec
  exact smul_left_injective Ω' hg (hc.symm.trans h)
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) :
    ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) =
      ∑ j, algebraMap K (Ω c) (x j) * ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) := by
  haveI := hd.tower c
  have hg : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have hspan : ∀ f ∈ 𝒜 c d.wL, ∃ a : Ω c, f = a • d.w (d.jc c) c := by
    intro f hf
    have hne : (⟨d.w (d.jc c) c, hd.w_mem _ c⟩ : 𝒜 c d.wL) ≠ 0 := by
      intro h0
      exact hg (congrArg Subtype.val h0)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp (hd.finrank_one c d.wL) ⟨f, hf⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  choose r hr using fun j => hspan (d.w j c) (hd.w_mem j c)
  have hrat : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = r j := fun j => ratio_eq_of_eq_smul' hg (hr j)
  simp only [hrat]
  apply ratio_eq_of_eq_smul' hg
  rw [Finset.sum_smul]
  unfold Data.wx
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.smul_apply, mul_smul, algebraMap_smul]
  conv_lhs => rw [hr j]
end ReciprocityTheory.ChartRestriction.G.T0.Data
