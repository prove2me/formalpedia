-- Prove2me | solution 1 for PersonalizedRM.RevenueGap.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:29:13.760639+00:00
-- url     : https://prove2.me/submissions/9d7eef5d-e010-4dfa-87e4-8b18912031a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model
import Theorems.Thm_PersonalizedRM_RevenueGap_theorem_1
import Theorems.Thm_PersonalizedRM_RevenueGap_revenue_lipschitz

open MeasureTheory ProbabilityTheory
open PersonalizedRM.RevenueGap

theorem solution : ∀ ψ : ℝ, 0 < ψ → ∃ Cψ : ℝ, 0 < Cψ ∧ ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (n J d : ℕ) (S : Fin n → Finset (Fin J)) (z : Fin n → Ω → Fin d → ℝ)
      (price : Fin n → Ω → Fin J → ℝ) (u : Fin n → Ω → ℝ) (y : Fin n → Ω → Option (Fin J))
      (θstar : Param J d) (θhat : Ω → Param J d) (pmin ν ρ : ℝ) (𝒮 : Set (Finset (Fin J))),
      0 < n →
      Assumption1 P S z price u y θstar pmin ψ → Assumption2 P S z price ν ρ →
      l1norm θstar ≤ R →
      (∀ ω, IsConstrainedMLE R
        (negLogLik S (fun i => z i ω) (fun i => price i ω) (fun i => y i ω)) (θhat ω)) →
      4 * Cψ * Real.log (ν * n) / (ν * min ρ 1 ^ 2) ≤ n →
      P {ω | ¬ ∀ zz : Fin d → ℝ, (∀ k, |zz k| ≤ 1) →
          ∀ (Sstar : Finset (Fin J)) (pstar : Fin J → ℝ) (Shat : Finset (Fin J))
            (phat : Fin J → ℝ),
            IsOracleDecision 𝒮 pmin θstar zz Sstar pstar →
            IsOracleDecision 𝒮 pmin (θhat ω) zz Shat phat →
            revenue θstar zz Sstar pstar - revenue θstar zz Shat phat ≤
              C / (ν * ρ) * (J : ℝ) ^ 4 * ((d : ℝ) + 1) *
                Real.sqrt (Real.log (2 * (n : ℝ) * J * ((d : ℝ) + 1)) / n)}
        ≤ ENNReal.ofReal (1 / n + 2 * J / (ν * n)) := by
  intro ψ hψ
  obtain ⟨Cψ, hCψ, hT1⟩ := theorem_1 ψ hψ
  refine ⟨Cψ, hCψ, fun R hR => ?_⟩
  set A := Real.exp R with hAdef
  have hA1 : 1 ≤ A := Real.one_le_exp hR.le
  have hA0 : 0 < A := Real.exp_pos R
  refine ⟨Real.sqrt 2 * (2 + A) ^ 2 * A, by positivity, ?_⟩
  intro Ω _ P _ n J d S z price u y θstar θhat pmin ν ρ 𝒮 hn hA1' hA2 hR' hmle hsize
  refine le_trans (measure_mono ?_) (hT1 R hR P n J d S z price u y θstar θhat pmin ν ρ hn hA1'
    hA2 hR' hmle hsize)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hB
  apply hω
  intro zz hz Sstar pstar Shat phat h1 h2
  have hpmin : 0 < pmin := hA1'.pmin_pos
  have hν : 0 < ν := hA2.nu_pos
  have hρ : 0 < ρ := hA2.rho_pos
  have hsub : ∀ p : Fin J → ℝ, p ∈ priceBox J pmin → p ∈ priceBox J 0 := by
    intro p hp
    simp only [priceBox, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies] at hp ⊢
    exact fun i => ⟨hpmin.le.trans (hp i).1, (hp i).2⟩
  set w := Real.sqrt ((J : ℝ) * ((d : ℝ) + 1)) with hw
  set Δ := ‖θhat ω - θstar‖ with hΔ
  set L := (J : ℝ) / 4 * w with hL
  have hlip1 := revenue_lipschitz θstar (θhat ω) zz hz Sstar pstar (hsub _ h1.2.1)
  have hlip2 := revenue_lipschitz θstar (θhat ω) zz hz Shat phat (hsub _ h2.2.1)
  rw [norm_sub_rev] at hlip1 hlip2
  have hopt : revenue (θhat ω) zz Sstar pstar ≤ revenue (θhat ω) zz Shat phat :=
    h2.2.2 Sstar h1.1 pstar h1.2.1
  have hgap : revenue θstar zz Sstar pstar - revenue θstar zz Shat phat ≤ 2 * (L * Δ) := by
    have a1 := (abs_le.mp hlip1).2
    have a2 := (abs_le.mp hlip2).1
    rw [hL]; linarith
  set K := 1 + Real.exp (-R) + ((J : ℝ) - 1) * A with hK
  set ℓ := Real.log (2 * (n : ℝ) * J * ((d : ℝ) + 1)) with hℓ
  set s := Real.sqrt (ℓ / n) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hw2 : w * w = (J : ℝ) * ((d : ℝ) + 1) := Real.mul_self_sqrt (by positivity)
  have hsq : Real.sqrt (2 * J * ((d : ℝ) + 1) * ℓ / n) = Real.sqrt 2 * w * s := by
    rw [show (2 : ℝ) * J * ((d : ℝ) + 1) * ℓ / n = 2 * ((J : ℝ) * ((d : ℝ) + 1)) * (ℓ / n) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  rw [hsq] at hB
  have hL0 : 0 ≤ L := by positivity
  have hexp : Real.exp (-R) = A⁻¹ := by rw [Real.exp_neg]
  have heq : 2 * (L * (2 * K ^ 2 / (Real.exp (-R) * ν * ρ) * (Real.sqrt 2 * w * s))) =
      (Real.sqrt 2 * A * ((d : ℝ) + 1) * s / (ν * ρ)) * (K ^ 2 * (J : ℝ) ^ 2) := by
    have hd : 2 * K ^ 2 / (Real.exp (-R) * ν * ρ) = 2 * K ^ 2 * A / (ν * ρ) := by
      rw [hexp]; field_simp
    rw [hd, hL]
    calc 2 * ((J : ℝ) / 4 * w * (2 * K ^ 2 * A / (ν * ρ) * (Real.sqrt 2 * w * s)))
        = (w * w) * (J : ℝ) * K ^ 2 * A * Real.sqrt 2 * s / (ν * ρ) := by ring
      _ = _ := by rw [hw2]; ring
  have hkey : K ^ 2 * (J : ℝ) ^ 2 ≤ (2 + A) ^ 2 * (J : ℝ) ^ 4 := by
    rcases Nat.eq_zero_or_pos J with hJ | hJ
    · subst hJ; simp
    · have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      have he1 : Real.exp (-R) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have he0 : 0 < Real.exp (-R) := Real.exp_pos _
      have hK0 : 0 ≤ K := by
        rw [hK]; have : 0 ≤ ((J : ℝ) - 1) * A := mul_nonneg (by linarith) hA0.le
        linarith
      have hKle : K ≤ (2 + A) * J := by
        rw [hK]; nlinarith
      have : K ^ 2 ≤ ((2 + A) * J) ^ 2 := pow_le_pow_left₀ hK0 hKle 2
      have hJ2 : (0 : ℝ) ≤ (J : ℝ) ^ 2 := by positivity
      calc K ^ 2 * (J : ℝ) ^ 2 ≤ ((2 + A) * J) ^ 2 * (J : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right this hJ2
        _ = (2 + A) ^ 2 * (J : ℝ) ^ 4 := by ring
  have hf0 : 0 ≤ Real.sqrt 2 * A * ((d : ℝ) + 1) * s / (ν * ρ) := by positivity
  calc revenue θstar zz Sstar pstar - revenue θstar zz Shat phat ≤ 2 * (L * Δ) := hgap
    _ ≤ 2 * (L * (2 * K ^ 2 / (Real.exp (-R) * ν * ρ) * (Real.sqrt 2 * w * s))) := by
        gcongr
    _ = (Real.sqrt 2 * A * ((d : ℝ) + 1) * s / (ν * ρ)) * (K ^ 2 * (J : ℝ) ^ 2) := heq
    _ ≤ (Real.sqrt 2 * A * ((d : ℝ) + 1) * s / (ν * ρ)) * ((2 + A) ^ 2 * (J : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hkey hf0
    _ = Real.sqrt 2 * (2 + A) ^ 2 * A / (ν * ρ) * (J : ℝ) ^ 4 * ((d : ℝ) + 1) * s := by ring
