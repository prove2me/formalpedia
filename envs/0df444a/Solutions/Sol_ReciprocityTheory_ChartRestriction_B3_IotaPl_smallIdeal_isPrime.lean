-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.B3.IotaPl.smallIdeal_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:24:27.767451+00:00
-- url     : https://prove2.me/submissions/21e1ad26-7f41-4d75-b3fc-5e94a6c9cf2e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlaceB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_B3_IotaPl_mem_smallIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.B3 ReciprocityTheory.ChartRestriction.B3.IotaPl
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.ChartRestriction.B3.IotaPl
theorem _root_.solution (ι : K →+* ℂ_[p]) : (smallIdeal ι).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : 𝓞 K) ∈ smallIdeal ι := (Ideal.eq_top_iff_one _).mp h
    rw [mem_smallIdeal] at h1
    simp at h1
  · intro a b hab
    simp only [mem_smallIdeal] at hab ⊢
    have e : ι ((a * b : 𝓞 K) : K) = ι (a : K) * ι (b : K) := by simp
    rw [e, norm_mul] at hab
    by_contra hc
    push_neg at hc
    obtain ⟨ha, hb⟩ := hc
    nlinarith [norm_int_le ι a, norm_int_le ι b]
end ReciprocityTheory.ChartRestriction.B3.IotaPl
