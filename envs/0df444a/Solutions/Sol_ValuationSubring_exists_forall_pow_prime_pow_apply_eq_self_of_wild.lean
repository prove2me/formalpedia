-- Prove2me | solution 1 for ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9140cf86-0541-5a5a-a3ef-52a15777e971

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
set_option autoImplicit false

theorem wild_pow {L : Type} [Field L] [Algebra ℚ L] (A : ValuationSubring L) {σ : L ≃ₐ[ℚ] L}
    (hwild : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits) (n : ℕ) :
    ∀ z : L, z ≠ 0 → (σ ^ n) z * z⁻¹ - 1 ∈ A.nonunits := by

  have hw : ∀ z : L, z ≠ 0 → A.valuation (σ z - z) < A.valuation z := by
    intro z hz
    have h := hwild z hz
    rw [ValuationSubring.mem_nonunits_iff] at h
    have : σ z - z = (σ z * z⁻¹ - 1) * z := by field_simp
    rw [this, map_mul]
    calc A.valuation (σ z * z⁻¹ - 1) * A.valuation z < 1 * A.valuation z :=
          mul_lt_mul_of_pos_right h (zero_lt_iff.mpr ((map_ne_zero _).mpr hz))
      _ = A.valuation z := one_mul _
  have hval : ∀ w : L, A.valuation (σ w) = A.valuation w := by
    intro w
    by_cases hw0 : w = 0
    · subst hw0; simp
    have h := Valuation.map_add_eq_of_lt_right A.valuation (hw w hw0)
    rwa [sub_add_cancel] at h
  have hpow : ∀ n : ℕ, ∀ z : L, z ≠ 0 → A.valuation ((σ ^ n) z - z) < A.valuation z := by
    intro n
    induction n with
    | zero => intro z hz; simp [(map_ne_zero A.valuation).mpr hz, zero_lt_iff]
    | succ n ih =>
      intro z hz
      have hsplit : (σ ^ (n + 1)) z - z = σ ((σ ^ n) z - z) + (σ z - z) := by
        rw [pow_succ', AlgEquiv.mul_apply, map_sub]; ring
      rw [hsplit]
      refine Valuation.map_add_lt _ ?_ (hw z hz)
      rw [hval]
      exact ih z hz
  intro z hz
  rw [ValuationSubring.mem_nonunits_iff]
  have : (σ ^ n) z * z⁻¹ - 1 = ((σ ^ n) z - z) / z := by field_simp
  rw [this, map_div₀, div_lt_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hz))]
  exact hpow n z hz

theorem solution {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F] :
    ∃ a : ℕ, ∀ x ∈ F, (σ ^ (q ^ a)) x = x := by
  let τ : F ≃ₐ[ℚ] F := AlgEquiv.restrictNormalHom F σ
  have ho : 0 < orderOf τ := orderOf_pos τ
  obtain ⟨a, m, hqm, ho'⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho.ne' q hq.one_lt.ne'
  have hcop : Nat.Coprime m q := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqm)
  refine ⟨a, fun x hx => ?_⟩
  have hfix : ∀ z : F, (σ ^ (q ^ a * m)) (z : AlgebraicClosure ℚ) = z := by
    intro z
    have h1 : AlgEquiv.restrictNormalHom F (σ ^ (q ^ a * m)) = 1 := by
      rw [map_pow, ← ho']; exact pow_orderOf_eq_one τ
    have h2 := AlgEquiv.restrictNormal_commutes (σ ^ (q ^ a * m)) F z
    change algebraMap F (AlgebraicClosure ℚ) ((AlgEquiv.restrictNormalHom F (σ ^ (q ^ a * m))) z) = _ at h2
    rw [h1, AlgEquiv.one_apply] at h2
    exact h2.symm
  refine ValuationSubring.apply_eq_self_of_pow_apply_eq_self_of_wild P hP (wild_pow P hwild (q ^ a)) hcop ?_
  rw [← pow_mul]
  exact hfix ⟨x, hx⟩

end S_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
end P2MW
export P2MW.S_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild (solution)
