-- Prove2me | solution 1 for PI.SqfDivDeg.W.card_monic_two_roots_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:40.302278+00:00
-- url     : https://prove2.me/submissions/cba938e8-9c29-4dc6-8984-ce63ab64fd55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe
import Theorems.Thm_PI_SqfDivDeg_W_decomp2
import Theorems.Thm_PI_SqfDivDeg_W_card_Mon
import Theorems.Thm_PI_SqfDivDeg_W_mem_Mon


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
open Classical
namespace PI.SqfDivDeg.W
theorem _root_.solution {g : ℕ} [Fact g.Prime] (n : ℕ) (c d : ZMod g) (hcd : c ≠ d) :
    ((Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d)).card ≤ g ^ n := by
  rw [← card_Mon g n]
  apply Finset.card_le_card_of_injOn (fun f => (f /ₘ (X - C c)) /ₘ (X - C d))
  · intro f hf
    have hf' : f ∈ (Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d) := by simpa using hf
    rw [Finset.mem_filter, mem_Mon] at hf'
    obtain ⟨⟨hm, hn⟩, hc, hd⟩ := hf'
    have e := decomp2 hcd hc hd
    set q := (f /ₘ (X - C c)) /ₘ (X - C d)
    have hm1 : ((X - C d) * q).Monic :=
      (monic_X_sub_C c).of_mul_monic_left (by rw [e]; exact hm)
    have hm2 : q.Monic := (monic_X_sub_C d).of_mul_monic_left hm1
    have hq : q ∈ Mon g n := by
      rw [mem_Mon]
      refine ⟨hm2, ?_⟩
      have := congrArg natDegree e
      rw [(monic_X_sub_C c).natDegree_mul hm1, (monic_X_sub_C d).natDegree_mul hm2,
        natDegree_X_sub_C, natDegree_X_sub_C, hn] at this
      omega
    simpa using hq
  · intro f1 hf1 f2 hf2 e
    have hf1' : f1 ∈ (Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d) := by simpa using hf1
    have hf2' : f2 ∈ (Mon g (n + 2)).filter (fun f => f.IsRoot c ∧ f.IsRoot d) := by simpa using hf2
    rw [Finset.mem_filter] at hf1' hf2'
    have e1 := decomp2 hcd hf1'.2.1 hf1'.2.2
    have e2 := decomp2 hcd hf2'.2.1 hf2'.2.2
    simp only at e
    rw [← e1, ← e2, e]
end PI.SqfDivDeg.W
