-- Prove2me | solution 1 for QuantumHMMR.design_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T19:41:46.175197+00:00
-- url     : https://prove2.me/submissions/2106ea5e-16a2-4753-b093-3e86d8f5efd4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QuantumHMMR_lemma_4_1
import Theorems.Thm_QuantumHMMR_eq_18
import Definitions.Def_QuantumHMMR_advantage
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic
import Definitions.Def_QuantumHMMR_logSq

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1500000

open Filter Asymptotics
open scoped Topology

namespace PRUDesignDecay

lemma polynomial_decay (k : ℕ) (C a : ℝ) (ha : 0 < a) :
    Tendsto (fun j : ℕ => C * (j : ℝ) ^ k * Real.exp (-(a * j))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) a ha).comp
    tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.rpow_natCast, ← mul_assoc, neg_mul, mul_zero]
    using h.const_mul C

lemma spectral_decay (D : ℕ) (a K : ℝ) (ha : 0 < a) (hK : 0 ≤ K) :
    ∀ᶠ j : ℕ in atTop,
      K * ((j + D - 2).choose (D - 1) : ℝ) * Real.exp (-(a / 2)) ^ (j - D) ≤
        Real.exp (-(a / 4 * j)) := by
  let C : ℝ := K * 2 ^ (D - 1) * Real.exp (a / 2 * D)
  have hlim := polynomial_decay (D - 1) C (a / 4) (by positivity)
  have hsmall : ∀ᶠ j : ℕ in atTop,
      C * (j : ℝ) ^ (D - 1) * Real.exp (-(a / 4 * j)) ≤ 1 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_ge_atTop D] with j hsmall hj
  have hchoose : ((j + D - 2).choose (D - 1) : ℝ) ≤ (2 * (j : ℝ)) ^ (D - 1) := by
    calc
      _ ≤ ((j + D - 2 : ℕ) : ℝ) ^ (D - 1) := by exact_mod_cast Nat.choose_le_pow _ _
      _ ≤ _ := by
        gcongr
        exact_mod_cast (by omega : j + D - 2 ≤ 2 * j)
  calc
    _ ≤ K * (2 * (j : ℝ)) ^ (D - 1) * Real.exp (-(a / 2)) ^ (j - D) := by gcongr
    _ = (C * (j : ℝ) ^ (D - 1) * Real.exp (-(a / 4 * j))) *
          Real.exp (-(a / 4 * j)) := by
      rw [← Real.exp_nat_mul, Nat.cast_sub hj, mul_pow]
      have he : ((j : ℝ) - D) * (-(a / 2)) =
          a / 2 * D + (-(a / 4 * j) + -(a / 4 * j)) := by ring
      rw [he, Real.exp_add, Real.exp_add]
      dsimp [C]
      ring
    _ ≤ 1 * Real.exp (-(a / 4 * j)) := mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := one_mul _

lemma logSq_tendsto (β : ℝ) (hβ : 1 < β) :
    Tendsto (fun n : ℕ => QuantumHMMR.logSq β n) atTop atTop := by
  simpa only [QuantumHMMR.logSq, Function.comp_def] using
    (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      ((Real.tendsto_logb_atTop hβ).comp tendsto_natCast_atTop_atTop)

lemma logSq_bound (D : ℕ) (K a β : ℝ) (hK : 0 ≤ K) (ha : 0 < a) (hβ : 1 < β) :
    ∀ᶠ n : ℕ in atTop,
      let j := 3 * ⌈QuantumHMMR.logSq β n⌉₊
      D ≤ j ∧ 1 ≤ j ∧
      K * ((j + D - 2).choose (D - 1) : ℝ) * Real.exp (-(a / 2)) ^ (j - D) +
          Real.exp (-(n : ℝ)) ≤ Real.exp (-(a / 2 * QuantumHMMR.logSq β n)) := by
  let L : ℕ → ℝ := fun n => QuantumHMMR.logSq β n
  let J : ℕ → ℕ := fun n => 3 * ⌈L n⌉₊
  have hL : Tendsto L atTop atTop := logSq_tendsto β hβ
  have hL0 (n : ℕ) : 0 ≤ L n := sq_nonneg _
  have hJL (n : ℕ) : 3 * L n ≤ (J n : ℝ) := by
    dsimp [J]
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)
  have hJ : Tendsto J atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [hL.eventually (eventually_ge_atTop (k : ℝ))] with n hn
    have hk : (k : ℝ) ≤ (J n : ℝ) := by nlinarith [hJL n, hL0 n]
    exact_mod_cast hk
  have hslow : (fun n : ℕ => (3 * a / 4) * L n) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    exact ((Real.isLittleO_pow_logb_id_atTop (b := β) (n := 2)).const_mul_left
      (3 * a / 4)).comp_tendsto tendsto_natCast_atTop_atTop
  have htail : ∀ᶠ n : ℕ in atTop, (3 * a / 4) * L n ≤ n := by
    filter_upwards [hslow.bound (by norm_num : (0 : ℝ) < 1)] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * a / 4) (hL0 n)),
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), one_mul] using hn
  have hexp : Tendsto (fun n : ℕ => Real.exp (a / 4 * L n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hL.const_mul_atTop (by positivity))
  filter_upwards [hJ.eventually (spectral_decay D a K ha hK),
    hJ.eventually (eventually_ge_atTop D), hJ.eventually (eventually_ge_atTop 1),
    htail, hexp.eventually (eventually_ge_atTop 2)] with n hs hD h1 ht he
  change D ≤ J n ∧ 1 ≤ J n ∧ _
  refine ⟨hD, h1, ?_⟩
  have hm : Real.exp (-(a / 4 * (J n : ℝ))) ≤ Real.exp (-(3 * a / 4 * L n)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hJL n]
  have ht' : Real.exp (-(n : ℝ)) ≤ Real.exp (-(3 * a / 4 * L n)) :=
    Real.exp_le_exp.mpr (neg_le_neg ht)
  calc
    _ ≤ 2 * Real.exp (-(3 * a / 4 * L n)) := by linarith [hs.trans hm, ht']
    _ ≤ Real.exp (a / 4 * L n) * Real.exp (-(3 * a / 4 * L n)) := by gcongr
    _ = Real.exp (-(a / 2 * L n)) := by rw [← Real.exp_add]; congr 1; ring

end PRUDesignDecay

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory QuantumHMMR
open scoped Matrix
attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

theorem solution [∀ n, Fintype (Clifford.ProjectiveGroup n)]
    (G : Finset (Clifford.ProjectiveGroup 2)) (hG : IsCliffordGenSet G)
    (t : ℕ) (ht : 4 ≤ t) (γ a : ℝ) (hga : IsGapPair G t γ a) (A : ℕ) (hA1 : 1 ≤ A)
    (hA : ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((2 : ℝ) ^ n) ^ (2 * t) * (1 - (1 - ((A * n ^ 2 : ℕ) : ℝ)⁻¹) * γ / n) ^ (A * n ^ 2)
        ≤ Real.exp (-(n : ℝ)))
    (β : ℝ) (hβ : 1 < β) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let m := A * n ^ 2
      let M := balancedUnitaryMoment (stepLaw G n m) t
      let MH := balancedUnitaryMoment (haarLaw n) t
      let B := M ^ m - MH
      (∀ alg : AdaptiveAlg n t,
        ∀ Meff : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ, IsEffect Meff →
        ∀ Λ : Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
            ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ,
          IsAcceptanceMatrix alg Meff Λ → traceNorm Λ ≤ ((2 : ℝ) ^ n) ^ (2 * t) →
          ‖(Λᴴ * B ^ (3 * ⌈logSq β n⌉₊)).trace‖ ≤ Real.exp (-(2 * κ * logSq β n))) ∧
      advantage t (walkLaw G n m (3 * m * ⌈logSq β n⌉₊)) (haarLaw n) ≤
        ENNReal.ofReal (Real.exp (-(2 * κ * logSq β n))) := by
  have ha : 0 < a := hga.2.1
  obtain ⟨n₁, hn₁⟩ := eq_18 G hG t ht γ a hga A hA1 hA
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 (PRUDesignDecay.logSq_bound (Dt t)
    (2 * Dt t * 2 ^ Dt t) a β (by positivity) ha hβ)
  refine ⟨a / 4, by positivity, max n₁ n₂, ?_⟩
  intro n hn
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans hn
  have hn2 : n₂ ≤ n := (le_max_right _ _).trans hn
  let j : ℕ := 3 * ⌈logSq β n⌉₊
  have hscalar := hn₂ n hn2
  change Dt t ≤ j ∧ 1 ≤ j ∧ _ at hscalar
  have hdecay :
      2 * Dt t * 2 ^ Dt t * ((j + Dt t - 2).choose (Dt t - 1) : ℝ) *
        Real.exp (-(a / 2)) ^ (j - Dt t) + Real.exp (-(n : ℝ)) ≤
          Real.exp (-(2 * (a / 4) * logSq β n)) := by
    convert hscalar.2.2 using 1 <;> congr 2 <;> ring
  dsimp only
  constructor
  · intro alg Meff hMeff Λ hΛ hΛnorm
    exact ((hn₁ n hn1 alg Meff hMeff Λ hΛ hΛnorm).2.2.2 j hscalar.1).trans hdecay
  · unfold advantage
    refine iSup_le fun alg => iSup_le fun Meff => iSup_le fun hMeff => ?_
    obtain ⟨Λ, hΛ, hΛnorm⟩ := lemma_4_1 n t alg Meff hMeff
    have h18 := hn₁ n hn1 alg Meff hMeff Λ hΛ hΛnorm
    have hbound := (h18.2.2.2 j hscalar.1).trans hdecay
    have hprob := (h18.2.1 j hscalar.2.1).1
    rw [hprob, Complex.norm_real, Real.norm_eq_abs] at hbound
    have htime : A * n ^ 2 * j = 3 * (A * n ^ 2) * ⌈logSq β n⌉₊ := by dsimp [j]; ring
    rw [htime] at hbound
    exact ENNReal.ofReal_le_ofReal hbound

#print axioms solution
