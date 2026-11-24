-- Prove2me | solution 1 for P2M_Formalism_PairingDivisionLocalBalance_weight_sum__2a3905c4f836
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:39.332695+00:00
-- url     : https://prove2.me/submissions/cb482ad3-b7da-4b6d-a2cd-b0b2ce03fcd1

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_natCast_nonneg
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_sum_valuation_nat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
open Formalism Formalism.PairingDivisionLocalBalance
namespace Formalism.PairingDivisionLocalBalance
theorem _root_.solution : WtSum := by
  intro K _ _ _ _ S c
  have hs : ∀ l ∈ S, (Function.support fun w : Pl K => c l * (lw w * (vw w (l : K) : ℝ))).Finite := by
    intro l _
    refine (sum_valuation_nat K l).1.subset ?_
    intro w hw
    simp only [Function.mem_support] at hw ⊢
    exact right_ne_zero_of_mul hw
  have he : (fun w : Pl K => lw w * wt S c w) =
      fun w => ∑ l ∈ S, c l * (lw w * (vw w (l : K) : ℝ)) := by
    funext w; unfold wt; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    refine (Set.Finite.biUnion S.finite_toSet hs).subset ?_
    intro w hw
    simp only [Function.mem_support] at hw
    obtain ⟨l, hl, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    simp only [Set.mem_iUnion]
    exact ⟨l, hl, hne⟩
  · rw [he, finsum_sum_comm _ _ hs]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_finsum, (sum_valuation_nat K l).2]
  · intro hc w
    exact Finset.sum_nonneg fun l hl => mul_nonneg (hc l hl) (by exact_mod_cast vw_natCast_nonneg w l)
end Formalism.PairingDivisionLocalBalance
