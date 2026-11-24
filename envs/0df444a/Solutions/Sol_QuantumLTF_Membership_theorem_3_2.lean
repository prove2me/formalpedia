-- Prove2me | solution 1 for QuantumLTF.Membership.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T11:08:04.170207+00:00
-- url     : https://prove2.me/submissions/242b5d05-d5ed-44e6-9ce4-c37bcf3bc547

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_IsFp
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_regBasis
import Theorems.Thm_QuantumLTF_Membership_theorem_3_2_nonnegative

open QAlgorithms
open QuantumLTF.Membership

theorem solution (C₁ C₂ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε η : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < η → η < 1 / 8 →
      ∀ (b : ℕ) (p : EuclideanSpace ℝ (Fin n)) (Bp fp : ℕ), (Bp : ℝ) ≤ C₁ * Real.log n →
        (∀ i, IsFp Bp fp (p i)) →
      ∀ (s : ℤ) (htil : ℝ) (Bh fh : ℕ), (Bh : ℝ) ≤ C₂ * Real.log (1 / ε) → IsFp Bh fh htil →
        ∃ (ℓ f Vb Vf W : ℕ)
          (c : OracleCircuit gatesRev (fun _ : Fin 1 => n * ℓ + 1) (n * b + Vb + W)),
          Uncontrolled c ∧
          (c.queryCount 0 : ℝ) ≤ C * Real.log (1 / η) ∧
          (c.gateCount : ℝ) ≤ C * n *
            (b + Real.log n + Real.log (1 / ε) + Real.log (1 / η)) ^ 2 * Real.log (1 / η) ∧
          (Vb : ℝ) ≤ C * (Real.log (1 / ε) + Real.log (1 / η)) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 → s = sgn (inner ℝ w p) →
            |htil - height w θ p 0| ≤ ε / 100 →
            ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, act (c.unitary fun _ => memOracle n ℓ f w θ)
                  (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) ∧
              ∀ x, |fpVal Vb Vf (Htil x) - height w θ p (rho n • gridVec n b x)| ≤ η := by
  by_cases hC₁ : 0 ≤ C₁
  · by_cases hC₂ : 0 ≤ C₂
    · exact theorem_3_2_nonnegative C₁ C₂ hC₁ hC₂
    · refine ⟨1, by norm_num, ?_⟩
      intro n hn ε η hε hε' hη hη' b p Bp fp hBp hp s htil Bh fh hBh hfp
      have hinv : 1 < 1 / ε := by
        apply (lt_div_iff₀ hε).2
        nlinarith
      have hlog : 0 < Real.log (1 / ε) := Real.log_pos hinv
      have hneg : C₂ * Real.log (1 / ε) < 0 :=
        mul_neg_of_neg_of_pos (lt_of_not_ge hC₂) hlog
      have hBh0 : (0 : ℝ) ≤ Bh := by positivity
      exfalso
      linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro n hn ε η hε hε' hη hη' b p Bp fp hBp hp
    have hnR : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn)
    have hlog : 0 < Real.log n := Real.log_pos hnR
    have hneg : C₁ * Real.log n < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hC₁) hlog
    have hBp0 : (0 : ℝ) ≤ Bp := by positivity
    exfalso
    linarith
