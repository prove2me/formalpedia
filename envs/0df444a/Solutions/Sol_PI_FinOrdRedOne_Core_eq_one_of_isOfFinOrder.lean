-- Prove2me | solution 1 for PI.FinOrdRedOne.Core.eq_one_of_isOfFinOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:10:50.498364+00:00
-- url     : https://prove2.me/submissions/bbfd6ab5-73c7-425e-9bfc-02106a01165d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
import Theorems.Thm_PI_FinOrdRedOne_Core_eq_one_of_pow_prime
import Theorems.Thm_PI_FinOrdRedOne_Core_isUnit_natCast_of_ne
import Theorems.Thm_PI_FinOrdRedOne_Core_pdvd_of_map_residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Core
open Matrix Finset
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace PI.FinOrdRedOne.Core
theorem _root_.solution [IsDomain R] [IsLocalRing R] (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp0 : (p : R) ≠ 0) (hM : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)})
    (hsep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (β : GL n R) (hfin : IsOfFinOrder β)
    (hred : (β : Matrix n n R).map (IsLocalRing.residue R) = 1) : β = 1 := by
  have hpM : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [hM]; exact Ideal.mem_span_singleton_self _
  have hunit := isUnit_natCast_of_ne (R := R) p hp hpM
  by_contra hne
  set N := orderOf β with hN
  have hNpos : 0 < N := hfin.orderOf_pos
  have hN1 : N ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  obtain ⟨l, hl, hld⟩ := Nat.exists_prime_and_dvd hN1
  set γ := β ^ (N / l) with hγ
  have hγl : γ ^ l = 1 := by
    rw [hγ, ← pow_mul, Nat.div_mul_cancel hld, hN, pow_orderOf_eq_one]
  have hγred : (γ : Matrix n n R).map (IsLocalRing.residue R) = 1 := by
    rw [hγ, Units.val_pow_eq_pow_val, ← RingHom.mapMatrix_apply, map_pow,
      RingHom.mapMatrix_apply, hred, one_pow]
  have hγ1 : (γ : Matrix n n R) = 1 := by
    refine eq_one_of_pow_prime p hp hp3 hp0 hunit hsep _ (pdvd_of_map_residue p hM _ hγred) l hl ?_
    rw [← Units.val_pow_eq_pow_val, hγl, Units.val_one]
  have hγ1' : γ = 1 := Units.ext hγ1
  have hdvd : N ∣ N / l := orderOf_dvd_of_pow_eq_one hγ1'
  have hpos : 0 < N / l := Nat.div_pos (Nat.le_of_dvd hNpos hld) hl.pos
  have hlt : N / l < N := Nat.div_lt_self hNpos hl.one_lt
  exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
end PI.FinOrdRedOne.Core
