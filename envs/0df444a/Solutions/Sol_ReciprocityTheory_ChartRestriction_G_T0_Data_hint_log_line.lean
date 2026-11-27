-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.hint_log_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:37:44.175169+00:00
-- url     : https://prove2.me/submissions/6060a0ae-45de-4767-8dc7-da4d5c64d6fc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintLogFinprod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintISBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_hint_ratio_ne
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
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
private theorem eq_ratio_smul_of_mem_graded {d' : Data K ι Ω WT A} (hd : d'.AxH 𝒜) {c : ι} {G : WT} {f e : A c}
    (he : e ∈ 𝒜 c G) (he0 : e ≠ 0) (hf : f ∈ 𝒜 c G) : f = ratio (Ω := Ω c) f e • e := by
  have hnz : (⟨e, he⟩ : 𝒜 c G) ≠ 0 := fun h0 => he0 (by simpa using congrArg Subtype.val h0)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, he⟩ : 𝒜 c G) hnz).mp (hd.finrank_one c G) ⟨f, hf⟩
  have hex : ∃ a : Ω c, f = a • e := ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  rw [ratio, dif_pos hex]
  exact hex.choose_spec
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) {c : ι} {G : WT} {f e : A c} (he : e ∈ 𝒜 c G) (he0 : e ≠ 0)
    (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0) (P : Ω c →+* ℂ) :
    Real.log (d.nrm c G f P) = Real.log ‖P (ratio (Ω := Ω c) f e)‖ + Real.log (d.nrm c G e P) := by
  have hfe := eq_ratio_smul_of_mem_graded hd he he0 hf
  have hr := hint_ratio_ne hd he he0 hf hf0
  calc Real.log (d.nrm c G f P)
      = Real.log (d.nrm c G (ratio (Ω := Ω c) f e • e) P) := by rw [← hfe]
    _ = _ := by
      rw [hd.nrm_smul c P _ he he0 hr,
        Real.log_mul (norm_ne_zero_iff.mpr ((map_ne_zero P).mpr hr)) (hd.nrm_pos c P he he0).ne']
end ReciprocityTheory.ChartRestriction.G.T0.Data
