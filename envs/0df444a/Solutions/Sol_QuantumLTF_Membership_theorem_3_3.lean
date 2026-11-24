-- Prove2me | solution 1 for QuantumLTF.Membership.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T11:14:00.473433+00:00
-- url     : https://prove2.me/submissions/203e2991-f57a-4329-9523-7c1906c2a644

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_regBasis
import Theorems.Thm_QuantumLTF_Membership_theorem_3_3_nonnegative

open QAlgorithms
open QuantumLTF.Membership

theorem solution (C₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε εg γ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < εg → εg ≤ 10 →
      0 < γ → γ ≤ 1 / 2 →
      let η : ℝ := rho n * εg / (48 * Real.pi * (3 * n + 1))
      let b : ℕ := ⌈Real.logb 2 ((3 * n + 1) / (rho n * εg))⌉₊
      ∀ Vb Vf W : ℕ, (Vb : ℝ) ≤ C₁ * (Real.log (1 / ε) + Real.log (1 / η)) →
        ∃ (m ℓo fo : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n * b + Vb + W) m)
          (oa : Fin n → (Fin ℓo ↪ Fin m)),
          Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C * Real.log (1 / γ) ∧
          (c.gateCount : ℝ) ≤ C * (n * (Real.log (n / εg)) ^ 2 + Real.log (1 / ε)) *
            Real.log (1 / γ) ∧
          ∀ (w p : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 →
            ∀ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, |fpVal Vb Vf (Htil x) - height w θ p (rho n • gridVec n b x)| ≤ η) →
            ∀ OH : Matrix (Qubits (n * b + Vb + W)) (Qubits (n * b + Vb + W)) ℂ,
              OH ∈ Matrix.unitaryGroup (Qubits (n * b + Vb + W)) ℂ →
              (∀ x, act OH (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) →
              open Classical in
              probEvent (act (c.unitary fun _ => OH) (zeroKet m))
                (fun z => ∀ i, |readFp (oa i) fo z - (-(w i) / inner ℝ w p)| ≤ εg) ≥ 1 - γ := by
  by_cases hC₁ : 0 ≤ C₁
  · exact theorem_3_3_nonnegative C₁ hC₁
  · refine ⟨1, by norm_num, ?_⟩
    intro n hn ε εg γ hε hε' hεg hεg' hγ hγ'
    dsimp only
    intro Vb Vf W hVb
    have hρ : 0 < rho n := by
      unfold rho
      positivity
    have hn0 : (0 : ℝ) < 3 * n + 1 := by positivity
    have hη : 0 < rho n * εg / (48 * Real.pi * (3 * n + 1)) := by positivity
    have hinvε : 1 < 1 / ε := by
      apply (lt_div_iff₀ hε).2
      nlinarith
    have hinvη : 1 < 1 / (rho n * εg / (48 * Real.pi * (3 * n + 1))) := by
      have hpi : 3 < Real.pi := Real.pi_gt_three
      have hρle : rho n ≤ 1 := by
        unfold rho
        exact pow_le_one₀ (by norm_num) (by norm_num)
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hnum : rho n * εg ≤ 10 := by nlinarith
      have hdenpos : 0 < 48 * Real.pi * (3 * (n : ℝ) + 1) := by positivity
      have hden : 10 < 48 * Real.pi * (3 * (n : ℝ) + 1) := by nlinarith
      have heta1 : rho n * εg / (48 * Real.pi * (3 * (n : ℝ) + 1)) < 1 :=
        (div_lt_one hdenpos).2 (lt_of_le_of_lt hnum hden)
      exact (one_lt_div hη).2 heta1
    have hlogs : 0 < Real.log (1 / ε) +
        Real.log (1 / (rho n * εg / (48 * Real.pi * (3 * n + 1)))) := by
      have h1 := Real.log_pos hinvε
      have h2 := Real.log_pos hinvη
      linarith
    have hneg : C₁ * (Real.log (1 / ε) +
        Real.log (1 / (rho n * εg / (48 * Real.pi * (3 * n + 1))))) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hC₁) hlogs
    have hVb0 : (0 : ℝ) ≤ Vb := by positivity
    exfalso
    linarith
