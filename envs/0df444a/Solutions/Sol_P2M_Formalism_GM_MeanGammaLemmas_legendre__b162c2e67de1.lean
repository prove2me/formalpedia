-- Prove2me | solution 1 for P2M_Formalism_GM_MeanGammaLemmas_legendre__b162c2e67de1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:52.870975+00:00
-- url     : https://prove2.me/submissions/de40221c-e907-4506-b2f3-e30f1df5ce91

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Finset
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (n : ℝ) / ((p : ℝ) - 1) - (padicValNat p n.factorial : ℝ) ≤ (Nat.log p n : ℝ) + 1 := by
  have hp1 := hp.out.one_lt
  have h := sub_one_mul_padicValNat_factorial (p := p) n
  have hds := Nat.digit_sum_le p n
  have hsum : (p.digits n).sum ≤ (p.digits n).length * (p - 1) := by
    have := List.sum_le_card_nsmul (p.digits n) (p - 1)
      (fun d hd => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp1 hd))
    simpa using this
  have hp1r : (1 : ℝ) < p := by exact_mod_cast hp1
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hlen := Nat.digits_len p n hp1 hn.ne'
    have key : ((p : ℝ) - 1) * (padicValNat p n.factorial) = n - (p.digits n).sum := by
      have := congrArg (fun x : ℕ => (x : ℝ)) h
      rw [Nat.cast_mul, Nat.cast_sub hp1.le, Nat.cast_sub hds, Nat.cast_one] at this
      exact this
    have hsumR : ((p.digits n).sum : ℝ) ≤ ((Nat.log p n : ℝ) + 1) * ((p : ℝ) - 1) := by
      rw [hlen] at hsum
      have := (Nat.cast_le (α := ℝ)).mpr hsum
      rw [Nat.cast_mul, Nat.cast_sub hp1.le, Nat.cast_add, Nat.cast_one] at this
      exact this
    have hv : (padicValNat p n.factorial : ℝ) = (n - (p.digits n).sum) / ((p : ℝ) - 1) := by
      rw [eq_div_iff hpm.ne', ← key]
      ring
    rw [hv, ← sub_div, sub_sub_cancel, div_le_iff₀ hpm]
    exact hsumR
end Formalism.GM.MeanGammaLemmas
