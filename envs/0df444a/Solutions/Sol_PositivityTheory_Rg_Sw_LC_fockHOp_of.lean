-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.fockHOp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:16:25.823261+00:00
-- url     : https://prove2.me/submissions/263ecdb8-fd53-464e-9931-7bd0e59414b0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_hop_pderiv_comm__fcbfde84e7a3
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_sgn_mul_same
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_sgn_mul_diff
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_fL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_hop_deriv_fock
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_hop_tr_false
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_hop_tr_true

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
variable (hB : FockBasic)
include hB
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution : FockHOp := by
  intro m n ε c hc a b p
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set Y := fock c p with hY
  have d1 : ∀ i, pderiv (a, i, false) Y = C (2 * c : ℂ) * fock c (pderiv (a, i, true) p) := fun i => hop_deriv_fock hB hc (a, i, true) p
  have d2 : ∀ i, pderiv (b, i, true) Y = C (2 * c : ℂ) * fock c (pderiv (b, i, false) p) := fun i => hop_deriv_fock hB hc (b, i, false) p
  unfold hOp Dop
  rw [← fL_apply hB hc]
  by_cases h : ε a = ε b
  · rw [if_pos h, map_sum, sgn_mul_same ε h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub, fL_apply, fL_apply, d1, d2]
    have e1 := hop_tr_false hB hc b i (pderiv (a, i, true) p)
    have e2 := hop_tr_true hB hc a i (pderiv (b, i, false) p)
    rw [hop_pderiv_comm' (b, i, false) (a, i, true)] at e1
    simp only [sub_self, mul_zero, map_zero, zero_mul, sub_zero, map_one, one_mul]
    linear_combination e1 - e2
  · rw [if_neg h, map_sum, sgn_mul_diff ε h]
    have hab : a ≠ b := fun e => h (e ▸ rfl)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub, map_smul, map_smul, fL_apply, fL_apply, d1, d2, smul_eq_C_mul, smul_eq_C_mul]
    have t2 := hop_tr_true hB hc a i (pderiv (b, i, false) p)
    have t3 := hop_tr_true hB hc a i p
    have t4 := hop_tr_false hB hc b i (X (a, i, false) * p)
    have e5 : pderiv (b, i, false) (X (a, i, false) * p) = X (a, i, false) * pderiv (b, i, false) p := by
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
      have : ((b, i, false) : Fin m × Fin n × Bool) ≠ (a, i, false) := by simp [Ne.symm hab]
      simp [Pi.single_apply, this]
    rw [e5] at t4
    rw [hop_pderiv_comm' (a, i, true) (b, i, false)] at t2
    have e6 : fock c (X (b, i, true) * (X (a, i, false) * p)) = fock c (X (a, i, false) * X (b, i, true) * p) := by
      congr 1; ring
    have hK : (C (1 / (2 * c) : ℂ) : PX m n) * C (2 * c : ℂ) = 1 := by
      rw [← map_mul, show (1 / (2 * c) : ℂ) * (2 * c) = 1 by field_simp, map_one]
    have e7 : (c : ℂ) * (1 - -1) = 2 * c := by ring
    simp only [e7, map_neg, map_one, neg_one_mul, neg_neg]
    linear_combination t2 - X (b, i, false) * t3 - C (1 / (2 * c) : ℂ) * t4 - C (1 / (2 * c) : ℂ) * e6 +
      (X (b, i, false) * fock c (X (a, i, false) * p) - fock c (X (a, i, false) * pderiv (b, i, false) p)) * hK
end PositivityTheory.Rg.Sw.LC
