-- Prove2me | solution 1 for QuantumLTF.Membership.theorem_3_2_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:20:40.865838+00:00
-- url     : https://prove2.me/submissions/0e4875ec-b91a-4889-9f15-0bb2304c2e59

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
import Theorems.Thm_QuantumLTF_Membership_local_bisection_parameters
import Theorems.Thm_QuantumLTF_Membership_localizedAffineBisect_error
import Theorems.Thm_QuantumLTF_Membership_localizedAffineBisect_circuit
import Theorems.Thm_QuantumLTF_Membership_bisection_resource_scale

open QAlgorithms
open QuantumLTF.Membership

set_option maxHeartbeats 800000 in
theorem solution (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
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
  obtain ⟨Cu, hCu, hparam⟩ := local_bisection_parameters
  obtain ⟨Cc, hCc, hcirc⟩ := localizedAffineBisect_circuit C₁ C₂ hC₁ hC₂
  let C : ℝ := 1 + 2 * Cu + Cc * (Cu + 1) ^ 3 + Cc * (Cu + 1)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hCu0 : 0 ≤ Cu := le_of_lt hCu
  have hCc0 : 0 ≤ Cc := le_of_lt hCc
  refine ⟨C, hC, ?_⟩
  intro n hn ε η hε hε2 hη hη8 b p Bp fp hBp hp s htil Bh fh hBh hhtil
  obtain ⟨q, hq, hqerr⟩ := hparam η hη hη8
  obtain ⟨ℓ, f, Vb, Vf, W, c, hunc, hqueries, hgates, hwidth, hrun⟩ :=
    hcirc n hn ε hε hε2 b q p Bp fp hBp hp s htil Bh fh hBh hhtil
  have hLe : 0 ≤ Real.log (1 / ε) := by
    apply Real.log_nonneg
    exact (one_le_div hε).2 (le_trans hε2 (by norm_num))
  have hLη : 1 ≤ Real.log (1 / η) := by
    have h8 : (8 : ℝ) < 1 / η := (lt_div_iff₀ hη).2 (by nlinarith)
    have hlog : Real.log 8 < Real.log (1 / η) :=
      Real.strictMonoOn_log (by norm_num : (8 : ℝ) ∈ Set.Ioi 0)
        (lt_trans (by norm_num) h8) h8
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at hlog
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
      exact lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9
    have hlogform : Real.log (1 / η) = -Real.log η := by
      rw [one_div, Real.log_inv]
    norm_num at hlog
    linarith
  have hL0 : 0 ≤ Real.log (1 / η) := by linarith
  refine ⟨ℓ, f, Vb, Vf, W, c, hunc, ?_, ?_, ?_, ?_⟩
  · have hqc : (c.queryCount 0 : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast hqueries
    have hcoef : 2 * Cu ≤ C := by
      dsimp [C]
      nlinarith [mul_nonneg hCc0 (pow_nonneg (by linarith : 0 ≤ Cu + 1) 3),
        mul_nonneg hCc0 (by linarith : 0 ≤ Cu + 1)]
    calc
      (c.queryCount 0 : ℝ) ≤ 2 * (q : ℝ) := hqc
      _ ≤ (2 * Cu) * Real.log (1 / η) := by
        nlinarith [mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ C * Real.log (1 / η) := mul_le_mul_of_nonneg_right hcoef hL0
  · have hLn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hs := bisection_resource_scale
      (A := (b : ℝ) + Real.log n + Real.log (1 / ε))
      (L := Real.log (1 / η)) (U := Cu) (q := (q : ℝ))
      (by positivity) hLη hCu0 (Nat.cast_nonneg q) hq
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hR : 0 ≤
        ((b : ℝ) + Real.log n + Real.log (1 / ε) + Real.log (1 / η)) ^ 2 *
          Real.log (1 / η) := mul_nonneg (sq_nonneg _) hL0
    have hcoef : Cc * (Cu + 1) ^ 3 ≤ C := by
      dsimp [C]
      nlinarith [mul_nonneg hCu0 hCc0,
        mul_nonneg hCc0 (by linarith : 0 ≤ Cu + 1)]
    calc
      (c.gateCount : ℝ)
          ≤ Cc * n * ((b : ℝ) + Real.log n + Real.log (1 / ε) + q) ^ 2 * (q + 1) := hgates
      _ = (Cc * n) * (((b : ℝ) + Real.log n + Real.log (1 / ε) + q) ^ 2 * (q + 1)) := by ring
      _ ≤ (Cc * n) * ((Cu + 1) ^ 3 *
          ((b : ℝ) + Real.log n + Real.log (1 / ε) + Real.log (1 / η)) ^ 2 *
            Real.log (1 / η)) := mul_le_mul_of_nonneg_left hs (mul_nonneg hCc0 hn0)
      _ = (Cc * (Cu + 1) ^ 3) * (n *
          (((b : ℝ) + Real.log n + Real.log (1 / ε) + Real.log (1 / η)) ^ 2 *
            Real.log (1 / η))) := by ring
      _ ≤ C * (n *
          (((b : ℝ) + Real.log n + Real.log (1 / ε) + Real.log (1 / η)) ^ 2 *
            Real.log (1 / η))) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hn0 hR)
      _ = C * n *
          ((b : ℝ) + Real.log n + Real.log (1 / ε) + Real.log (1 / η)) ^ 2 *
            Real.log (1 / η) := by ring
  · have hsum : Real.log (1 / ε) + (q : ℝ) + 1 ≤
        (Cu + 1) * (Real.log (1 / ε) + Real.log (1 / η)) := by
      nlinarith [mul_nonneg hCu0 hLe]
    have hsum0 : 0 ≤ Real.log (1 / ε) + Real.log (1 / η) := add_nonneg hLe hL0
    have hcoef : Cc * (Cu + 1) ≤ C := by
      dsimp [C]
      nlinarith [mul_nonneg hCu0 hCc0,
        mul_nonneg hCc0 (pow_nonneg (by linarith : 0 ≤ Cu + 1) 3)]
    calc
      (Vb : ℝ) ≤ Cc * (Real.log (1 / ε) + (q : ℝ) + 1) := hwidth
      _ ≤ Cc * ((Cu + 1) * (Real.log (1 / ε) + Real.log (1 / η))) :=
        mul_le_mul_of_nonneg_left hsum hCc0
      _ = (Cc * (Cu + 1)) * (Real.log (1 / ε) + Real.log (1 / η)) := by ring
      _ ≤ C * (Real.log (1 / ε) + Real.log (1 / η)) :=
        mul_le_mul_of_nonneg_right hcoef hsum0
  · intro w θ hw ha ha3 hs hbase
    obtain ⟨Htil, hact, hval⟩ := hrun w θ hw ha ha3 hs hbase
    refine ⟨Htil, hact, ?_⟩
    intro x
    rw [hval x, hs]
    exact (localizedAffineBisect_error hn ε hε hε2 w p θ htil hw ha hbase x q).trans hqerr
