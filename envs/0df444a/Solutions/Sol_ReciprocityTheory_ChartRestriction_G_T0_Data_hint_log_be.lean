-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.hint_log_be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:15:33.321817+00:00
-- url     : https://prove2.me/submissions/3d41f86d-1fec-4a0a-ae25-7782a7e336c1

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
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) :
    Real.log (d.be c P) =
      Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) + Real.log ‖d.hintU c P‖ := by
  have he := hd.w_mem (d.jc c) c
  have he0 := hd.w_base c
  have key : ∀ j, d.nrm c d.wL (d.w j c) P =
      ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ * d.nrm c d.wL (d.w (d.jc c) c) P := by
    intro j
    by_cases hj : d.w j c = 0
    · have hr : ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = 0 := by
        have h1 := eq_ratio_smul_of_mem_graded hd he he0 (hd.w_mem j c)
        have h2 : ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c = 0 := by
          rw [← h1]; exact hj
        exact (smul_eq_zero.mp h2).resolve_right he0
      rw [hr, hj, hd.nrm_zero, map_zero, norm_zero, zero_mul]
    · rw [← hd.nrm_smul c P _ he he0 (hint_ratio_ne hd he he0 (hd.w_mem j c) hj),
        ← eq_ratio_smul_of_mem_graded hd he he0 (hd.w_mem j c)]
  have hsum : ∑ j, d.nrm c d.wL (d.w j c) P ^ 2 = d.nrm c d.wL (d.w (d.jc c) c) P ^ 2 *
      ∑ j, ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [key j]; ring
  have hU : ‖d.hintU c P‖ = Real.sqrt (∑ j, ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ ^ 2) := by
    simp [hintU, EuclideanSpace.norm_eq]
  have hUne : ‖d.hintU c P‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h0
    have h1 := congrArg (fun x => x (d.jc c)) h0
    exact hint_ratio_ne hd he he0 he he0 (by simpa [hintU] using h1)
  have hpos := hd.nrm_pos c P he he0
  rw [be, hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le, ← hU, Real.log_mul hpos.ne' hUne]
end ReciprocityTheory.ChartRestriction.G.T0.Data
