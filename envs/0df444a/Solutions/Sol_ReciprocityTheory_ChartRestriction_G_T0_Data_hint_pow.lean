-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.hint_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:21:04.854722+00:00
-- url     : https://prove2.me/submissions/4720d65f-42d4-4a8f-99b5-68057701c560

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintLogFinprod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintISBounds
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
theorem _root_.solution (hd : d.AxH 𝒜) {c : ι} {G : WT} {f : A c} (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0) :
    ∀ k : ℕ, 0 < k → f ^ k ∈ 𝒜 c (k • G) ∧ f ^ k ≠ 0 ∧
      ∀ P, Real.log (d.nrm c (k • G) (f ^ k) P) = k * Real.log (d.nrm c G f P) := by
  intro k hk
  haveI := hd.graded c
  induction k with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨by simpa using hf, by simpa using hf0, fun P => by simp⟩
    · obtain ⟨h1, h2, h3⟩ := ih hn
      have hmem : f ^ (n + 1) ∈ 𝒜 c ((n + 1) • G) := by
        rw [pow_succ, succ_nsmul]; exact SetLike.mul_mem_graded h1 hf
      have hne : f ^ (n + 1) ≠ 0 := by
        rw [pow_succ]; exact hd.mul_ne_zero c h1 hf h2 hf0
      refine ⟨hmem, hne, fun P => ?_⟩
      rw [pow_succ, succ_nsmul, hd.nrm_mul c P h1 hf h2 hf0,
        Real.log_mul (hd.nrm_pos c P h1 h2).ne' (hd.nrm_pos c P hf hf0).ne', h3 P]
      push_cast
      ring
end ReciprocityTheory.ChartRestriction.G.T0.Data
