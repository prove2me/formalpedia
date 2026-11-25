-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.tendsto_zetaReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:49:41.441068+00:00
-- url     : https://prove2.me/submissions/64aab6a3-31c1-4ba2-bde7-6d126630d07d

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_DedekindZetaReal_dedekindZeta_eq_zetaReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable (K : Type*) [Field K] [NumberField K]
open ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
namespace ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
theorem _root_.solution : Tendsto (zetaReal K) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun s : ℝ ↦ (s - 1) * zetaReal K s) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue K)) := by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
    refine (h.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    simp only [Function.comp_apply, dedekindZeta_eq_zetaReal K hs]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h2 : Tendsto (fun s : ℝ ↦ (s - 1)⁻¹) (𝓝[>] 1) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ ↦ s - 1) (𝓝 1) (𝓝 (1 - 1)) := tendsto_id.sub tendsto_const_nhds
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      exact sub_pos.mpr hs
  refine (h1.pos_mul_atTop (dedekindZeta_residue_pos K) h2).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs.ne'
  field_simp
end ReciprocityTheory.Neutral.Bridge.DedekindZetaReal
