-- Prove2me | solution 1 for PositivityTheory.PrwZar.Qi.killedCore
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:20:46.706853+00:00
-- url     : https://prove2.me/submissions/06f559a3-bd01-48ba-9ef4-3c48862f8227

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_CompLmulMapId
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiIdem
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiStab
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCharP
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCartier
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCore
import Theorems.Thm_PositivityTheory_PrwZar_Qi_aug_le_sq
import Theorems.Thm_PositivityTheory_PrwZar_Qi_exists_stable_pow
import Theorems.Thm_PositivityTheory_PrwZar_Qi_idem_eq_zero
import Theorems.Thm_PositivityTheory_PrwZar_Qi_pw_charP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open PositivityTheory PositivityTheory.PrwZar PositivityTheory.PrwZar.Qi
namespace PositivityTheory.PrwZar.Qi
theorem _root_.solution : KilledCore := by
  intro K H _ _ _ _ _ Δ ε hL hR hmul hpts
  obtain ⟨m, hm, hpt⟩ := hpts
  set I : Ideal H := RingHom.ker ε with hI
  obtain ⟨k, e, he, hIk, hstab⟩ := exists_stable_pow (K := K) I

  have hk1 : I ^ (k + 1) = Ideal.span {e} := by rw [hstab (k + 1) (Nat.le_succ k), hIk]
  have heI : e ∈ I := by
    have : e ∈ I ^ (k + 1) := by rw [hk1]; exact Ideal.subset_span rfl
    exact Ideal.pow_le_self (Nat.succ_ne_zero k) this

  have hs : ∃ s : ℕ, 0 < s ∧ ∀ x ∈ I, pw Δ ε s x ∈ I ^ k := by
    obtain ⟨p, hp⟩ := CharP.exists K
    rcases CharP.char_is_prime_or_zero K p with hpp | hp0
    · have : Fact p.Prime := ⟨hpp⟩
      refine ⟨p ^ k, pow_pos hpp.pos k, fun x hx => ?_⟩
      exact Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le (pw_charP p Δ ε hL hR hmul k hx)
    · subst hp0
      have : CharZero K := CharP.charP_to_charZero K
      have h1 : pw Δ ε 1 = AlgHom.id K H := hL
      have hle : ∀ j : ℕ, I ≤ I ^ (j + 1) := by
        intro j
        induction j with
        | zero => rw [zero_add, pow_one]
        | succ j ih =>
          calc I ≤ I ^ 2 := aug_le_sq Δ ε hL hR
            _ = I * I := pow_two I
            _ ≤ I * I ^ (j + 1) := Ideal.mul_mono_right ih
            _ = I ^ (j + 1 + 1) := (pow_succ' I (j + 1)).symm
      refine ⟨1, one_pos, fun x hx => ?_⟩
      rw [h1]
      exact Ideal.pow_le_pow_right (Nat.le_succ k) (hle k hx)
  obtain ⟨s, hs0, hsI⟩ := hs

  have hme : pw Δ ε m e = 0 := by
    refine idem_eq_zero (K := K) (he.map (pw Δ ε m)) fun x => ?_
    have := congrArg (fun f : H →ₐ[K] K => f e) (hpt x)
    simp only [AlgHom.comp_apply] at this
    rw [this]
    exact heI
  refine ⟨m * s, Nat.mul_pos hm hs0, AlgHom.ext fun x => ?_⟩
  have hy : x - algebraMap K H (ε x) ∈ I := by
    change ε (x - algebraMap K H (ε x)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hIk ▸ hsI _ hy)
  have key : pw Δ ε (m * s) (x - algebraMap K H (ε x)) = 0 := by
    rw [hmul, AlgHom.comp_apply, ← ha, map_mul, hme, mul_zero]
  have h0 : pw Δ ε 0 (x - algebraMap K H (ε x)) = 0 := by
    change algebraMap K H (ε (x - algebraMap K H (ε x))) = 0
    rw [show ε (x - algebraMap K H (ε x)) = 0 from hy, map_zero]
  have e1 := congrArg (· + algebraMap K H (ε x)) key
  have e2 := congrArg (· + algebraMap K H (ε x)) h0
  simp only [map_sub, AlgHom.commutes, sub_add_cancel, zero_add] at e1 e2
  rw [e1, e2]
end PositivityTheory.PrwZar.Qi
