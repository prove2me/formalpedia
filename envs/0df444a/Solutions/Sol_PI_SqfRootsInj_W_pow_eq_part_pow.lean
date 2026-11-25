-- Prove2me | solution 1 for PI.SqfRootsInj.W.pow_eq_part_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:26.488082+00:00
-- url     : https://prove2.me/submissions/09009b99-f959-4b42-af57-b5e5464aa081

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase

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
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution {M : Type*} [Monoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x : M)
    (hx : 0 < orderOf x) :
    x ^ (ℓ ^ (orderOf x).factorization ℓ) =
      (primeToPart ℓ x) ^ (ℓ ^ (orderOf x).factorization ℓ) := by
  have hdvd : ℓ ^ (orderOf x).factorization ℓ ∣ orderOf x := Nat.ordProj_dvd _ ℓ
  have hmpos : 0 < orderOf x / ℓ ^ (orderOf x).factorization ℓ :=
    Nat.div_pos (Nat.le_of_dvd hx hdvd) (pow_pos hℓ.pos _)
  have hcop : Nat.Coprime (ℓ ^ (orderOf x).factorization ℓ)
      (orderOf x / ℓ ^ (orderOf x).factorization ℓ) :=
    (Nat.coprime_ordCompl hℓ hx.ne').pow_left _
  haveI : NeZero (orderOf x / ℓ ^ (orderOf x).factorization ℓ) := ⟨hmpos.ne'⟩
  have hu : ((ℓ ^ (orderOf x).factorization ℓ *
      (((ℓ ^ (orderOf x).factorization ℓ : ℕ) :
        ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ))⁻¹).val : ℕ) :
        ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ)) = ((1 : ℕ) : ZMod _) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ hcop
  rw [ZMod.natCast_eq_natCast_iff] at hu
  have hmod := Nat.ModEq.mul_left' (ℓ ^ (orderOf x).factorization ℓ) hu
  rw [Nat.mul_div_cancel' hdvd, mul_one] at hmod
  unfold primeToPart
  rw [← pow_mul, ← pow_mod_orderOf, mul_comm _ (ℓ ^ (orderOf x).factorization ℓ), ← hmod,
    pow_mod_orderOf]
end PI.SqfRootsInj.W
