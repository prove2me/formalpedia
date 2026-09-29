-- Prove2me | solution 1 for WeierstrassCurve.exists_minimalLevel_of_steps_of_level_of_not_sq_dvd_of_not_cube_dvd_of_squarefree_step
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f8a439f1-a0ab-5ba6-a087-d4d78a6b3294

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_minimalLevel_of_steps_of_level_of_not_sq_dvd_of_not_cube_dvd_of_squarefree_step

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point in

theorem solution
    (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (_hΔ : W.Δ ≠ 0)
    (_hW : W.IsSemistableModel)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (_hirr : W.ModRepIsIrreducible p)
    (M₀ : ℕ) [NeZero M₀] (hres₀ : W.IsResiduallyModularOfLevel p M₀) (hp2M₀ : ¬ p ^ 2 ∣ M₀)
    (hM₀3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M₀)
    (hQ : ∀ M q : ℕ, Squarefree M → q.Prime → q ≠ p → q ∣ M → ¬ q ^ 2 ∣ M →
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).IsUnramifiedAt q →
      W.IsResiduallyModularOfLevel p M → W.IsResiduallyModularOfLevel p (M / q))
    (hSq : ∀ M q : ℕ, q.Prime → q ≠ p → q ^ 2 ∣ M → ¬ q ^ 3 ∣ M →
      W.IsResiduallyModularOfLevel p M → W.IsResiduallyModularOfLevel p (M / q))
    (hP : ∀ M : ℕ, W.IsResiduallyModularOfLevel p M →
      ((W.IsGoodPrimeFor p ∧ (p : ℤ) ∣ W.apOfModel p) → p ∣ M → ¬ p ^ 2 ∣ M →
        W.IsResiduallyModularOfLevel p (M / p)) ∧
      ((¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) → ¬ p ∣ M →
        W.IsResiduallyModularOfLevel p (M * p)))
    (hU : ∀ M q : ℕ, q.Prime → q ≠ p → ¬ q ∣ M → W.IsResiduallyModularOfLevel p M →
      ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).IsUnramifiedAt q) :
    ∃ N : ℕ, Squarefree N ∧
      (∀ q : ℕ, q.Prime → q ≠ p →
        (q ∣ N ↔ ¬ ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).IsUnramifiedAt q)) ∧
      (p ∣ N ↔ (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p)) ∧
      W.IsResiduallyModularOfLevel p N := by
  classical
  have hp : p.Prime := Fact.out
  set ρbar := (W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker with hρbar
  suffices H : ∀ M : ℕ, M ≠ 0 → ¬ p ^ 2 ∣ M → (∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M) →
      W.IsResiduallyModularOfLevel p M →
      ∃ N : ℕ, Squarefree N ∧ (∀ q : ℕ, q.Prime → q ≠ p → (q ∣ N ↔ ¬ ρbar.IsUnramifiedAt q)) ∧
        (p ∣ N ↔ (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p)) ∧ W.IsResiduallyModularOfLevel p N from
    H M₀ (NeZero.ne M₀) hp2M₀ hM₀3 hres₀
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro hM0 hp2M hM3 hresM

  by_cases hsq : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ^ 2 ∣ M
  · obtain ⟨q, hq, hqp, hq2⟩ := hsq
    have hqM : q ∣ M := (dvd_pow_self q two_ne_zero).trans hq2
    have hlt : M / q < M := Nat.div_lt_self (Nat.pos_of_ne_zero hM0) hq.one_lt
    have hMq0 : M / q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hqM) hq.pos).ne'
    exact ih (M / q) hlt hMq0 (fun h => hp2M (h.trans (Nat.div_dvd_of_dvd hqM)))
      (fun r hr hrp h => hM3 r hr hrp (h.trans (Nat.div_dvd_of_dvd hqM))) (hSq M q hq hqp hq2 (hM3 q hq hqp) hresM)
  push_neg at hsq

  have hMsqf : Squarefree M := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro q hq hq2
    rw [← pow_two] at hq2
    by_cases hqp : q = p
    · exact hp2M (hqp ▸ hq2)
    · exact hsq q hq hqp hq2

  by_cases hunr : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ M ∧ ρbar.IsUnramifiedAt q
  · obtain ⟨q, hq, hqp, hqM, hu⟩ := hunr
    have hlt : M / q < M := Nat.div_lt_self (Nat.pos_of_ne_zero hM0) hq.one_lt
    have hMq0 : M / q ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hqM) hq.pos).ne'
    exact ih (M / q) hlt hMq0 (fun h => hp2M (h.trans (Nat.div_dvd_of_dvd hqM)))
      (fun r hr hrp h => hM3 r hr hrp (h.trans (Nat.div_dvd_of_dvd hqM))) (hQ M q hMsqf hq hqp hqM (hsq q hq hqp) hu hresM)
  push_neg at hunr

  by_cases hss : (W.IsGoodPrimeFor p ∧ (p : ℤ) ∣ W.apOfModel p) ∧ p ∣ M
  · obtain ⟨hgs, hpM⟩ := hss
    have hlt : M / p < M := Nat.div_lt_self (Nat.pos_of_ne_zero hM0) hp.one_lt
    have hMp0 : M / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hpM) hp.pos).ne'
    exact ih (M / p) hlt hMp0 (fun h => hp2M (h.trans (Nat.div_dvd_of_dvd hpM)))
      (fun r hr hrp h => hM3 r hr hrp (h.trans (Nat.div_dvd_of_dvd hpM))) ((hP M hresM).1 hgs hpM hp2M)

  have hqiff : ∀ q : ℕ, q.Prime → q ≠ p → (q ∣ M ↔ ¬ ρbar.IsUnramifiedAt q) := fun q hq hqp =>
    ⟨fun hqM => hunr q hq hqp hqM, fun hram => by_contra fun hqM => hram (hU M q hq hqp hqM hresM)⟩
  by_cases hcond : ¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p
  · by_cases hpM : p ∣ M
    · exact ⟨M, hMsqf, hqiff, ⟨fun _ => hcond, fun _ => hpM⟩, hresM⟩
    · refine ⟨M * p, ?_, fun q hq hqp => ?_, ⟨fun _ => hcond, fun _ => dvd_mul_left p M⟩, (hP M hresM).2 hcond hpM⟩
      · exact (Nat.squarefree_mul (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM))).2
          ⟨hMsqf, hp.squarefree⟩
      · rw [← hqiff q hq hqp]
        constructor
        · intro h
          exact ((Nat.Prime.dvd_mul hq).1 h).resolve_right fun h' => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 h')
        · exact fun h => h.mul_right p
  · have hgs : W.IsGoodPrimeFor p ∧ (p : ℤ) ∣ W.apOfModel p := by
      by_contra h
      exact hcond (not_and_or.1 h)
    have hpM : ¬ p ∣ M := fun h => hss ⟨hgs, h⟩
    exact ⟨M, hMsqf, hqiff, ⟨fun h => absurd h hpM, fun h => absurd hgs (fun hg => h.elim (fun h1 => h1 hg.1) (fun h2 => h2 hg.2))⟩, hresM⟩

end S_WeierstrassCurve_exists_minimalLevel_of_steps_of_level_of_not_sq_dvd_of_not_cube_dvd_of_squarefree_step
end P2MW
export P2MW.S_WeierstrassCurve_exists_minimalLevel_of_steps_of_level_of_not_sq_dvd_of_not_cube_dvd_of_squarefree_step (solution)
