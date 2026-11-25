-- Prove2me | solution 1 for PI.SqfRootShift.W.ptp_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:26:48.416635+00:00
-- url     : https://prove2.me/submissions/c6e69255-1198-47c0-aec6-35db0ada74db

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
namespace PI.SqfRootShift.W
theorem _root_.solution {M : Type*} [Monoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x : M) (hx : 0 < orderOf x) :
    x ^ (ℓ ^ (orderOf x).factorization ℓ) =
      (primeToPart ℓ x) ^ (ℓ ^ (orderOf x).factorization ℓ) := by
  set n := orderOf x with hn
  set L := ℓ ^ n.factorization ℓ with hL
  set m := n / L with hm
  have hcop : Nat.Coprime L m := by
    have := Nat.coprime_ordCompl hℓ hx.ne'
    exact Nat.Coprime.pow_left _ this
  have hnm : L * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have : NeZero m := ⟨by intro h0; rw [h0, mul_zero] at hnm; omega⟩
  set u := (((L : ℕ) : ZMod m)⁻¹).val with hu
  have hmod : L * u ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hu, ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one L hcop
  have hptp : primeToPart ℓ x = x ^ (L * u) := rfl
  rw [hptp, ← pow_mul, ← pow_mod_orderOf x L, ← pow_mod_orderOf x (L * u * L)]
  congr 1
  show L ≡ L * u * L [MOD orderOf x]
  rw [← hn, ← hnm]
  have := Nat.ModEq.mul_left' L hmod
  rw [mul_one] at this
  rw [mul_comm (L * u) L]
  exact this.symm
end PI.SqfRootShift.W
