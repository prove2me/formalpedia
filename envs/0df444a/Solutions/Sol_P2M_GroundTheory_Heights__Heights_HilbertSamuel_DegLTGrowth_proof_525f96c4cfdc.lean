-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegLTGrowth_proof_525f96c4cfdc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:11.110249+00:00
-- url     : https://prove2.me/submissions/e81c7381-b66e-4702-b88f-6e2a2a3fd4b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_of_fin_zero_39ff712c69c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_degLT_succ_growth_natPow_86a645ae5dec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.NumbersDVR
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace DegLTGrowth
theorem _root_.solution : DegLTGrowth.Statement := by
  intro K _ _ n g hg
  cases n with
  | zero =>
    have hev : ∀ᶠ m in Filter.atTop, g m = 0 := by
      simpa [mixedDiff_of_fin_zero] using hg Fin.elim0
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hev
    refine ⟨∑ k, (m₀ k).toNat, 0, fun a ha => ?_⟩
    have hge : m₀ ≤ fun k => (a k : ℤ) := by
      intro k
      calc m₀ k ≤ ((m₀ k).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ ((∑ k, (m₀ k).toNat : ℕ) : ℤ) := by
          exact_mod_cast Finset.single_le_sum (f := fun k => (m₀ k).toNat)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        _ ≤ (a k : ℤ) := by exact_mod_cast ha k
    rw [hm₀ _ hge]
    simp
  | succ n =>
    obtain ⟨A, C, _, hb⟩ := degLT_succ_growth_natPow n g hg
    refine ⟨A, C, fun a ha => ?_⟩
    have h := hb a ha
    have he : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
    rw [he, Real.rpow_natCast]
    push_cast at h
    exact h
end DegLTGrowth
end GroundTheory.Heights₂.Heights.HilbertSamuel
