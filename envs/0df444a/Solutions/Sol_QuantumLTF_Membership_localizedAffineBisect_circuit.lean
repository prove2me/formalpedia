-- Prove2me | solution 1 for QuantumLTF.Membership.localizedAffineBisect_circuit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:30:56.390991+00:00
-- url     : https://prove2.me/submissions/448e6588-ff45-4b50-8da2-aeec5d40af79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_IsFp
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gridVec
import Definitions.Def_QuantumLTF_Membership_regBasis
import Theorems.Thm_QuantumLTF_Membership_localizedAffineBisect_circuit_core
open QAlgorithms
open QuantumLTF.Membership
set_option maxHeartbeats 800000 in
theorem solution (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ (b q : ℕ) (p : EuclideanSpace ℝ (Fin n)) (Bp fp : ℕ), (Bp : ℝ) ≤ C₁ * Real.log n →
        (∀ i, IsFp Bp fp (p i)) →
      ∀ (s : ℤ) (htil : ℝ) (Bh fh : ℕ), (Bh : ℝ) ≤ C₂ * Real.log (1 / ε) → IsFp Bh fh htil →
        ∃ (ℓ f Vb Vf W : ℕ)
          (c : OracleCircuit gatesRev (fun _ : Fin 1 => n * ℓ + 1) (n * b + Vb + W)),
          Uncontrolled c ∧ c.queryCount 0 ≤ 2 * q ∧
          (c.gateCount : ℝ) ≤ C * n * (b + Real.log n + Real.log (1 / ε) + q) ^ 2 * (q + 1) ∧
          (Vb : ℝ) ≤ C * (Real.log (1 / ε) + q + 1) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 → s = sgn (inner ℝ w p) →
            |htil - height w θ p 0| ≤ ε / 100 →
            ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, act (c.unitary fun _ => memOracle n ℓ f w θ)
                  (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) ∧
              ∀ x, fpVal Vb Vf (Htil x) =
                (affineBoundaryBisect p (rho n • gridVec n b x) s q
                  (htil - 1 / 4) (htil + 1 / 4)).run (ltf w θ) := by
  obtain ⟨Cc, hCc, hc⟩ := localizedAffineBisect_circuit_core
  let R : ℝ := 2 + C₁ + C₂
  let C : ℝ := Cc * R ^ 2 + Cc * R
  have hR : 0 < R := by dsimp [R]; positivity
  have hR0 : 0 ≤ R := hR.le
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn ε hε hε2 b q p Bp fp hBp hp s htil Bh fh hBh hh
  obtain ⟨ℓ, f, Vb, Vf, W, c, hu, hq, hg, hV, hrun⟩ := hc n b q p Bp fp hp s htil Bh fh hh
  have hLn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hLe : 0 ≤ Real.log (1 / ε) := Real.log_nonneg ((one_le_div hε).2 (hε2.trans (by norm_num)))
  let A : ℝ := (b : ℝ) + Real.log n + Real.log (1 / ε) + q
  let D : ℝ := (b : ℝ) + Bp + Bh + Real.log n + q
  let E : ℝ := Real.log (1 / ε) + q + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hLnA : Real.log n ≤ A := by dsimp [A]; linarith
  have hLeA : Real.log (1 / ε) ≤ A := by dsimp [A]; linarith
  have hC1A : C₁ * Real.log n ≤ C₁ * A := mul_le_mul_of_nonneg_left hLnA hC₁
  have hC2A : C₂ * Real.log (1 / ε) ≤ C₂ * A := mul_le_mul_of_nonneg_left hLeA hC₂
  have hbase : (b : ℝ) + Real.log n + q ≤ 2 * A := by dsimp [A]; linarith
  have hDA : D ≤ R * A := by
    calc
      D ≤ (b : ℝ) + Real.log n + q + C₁ * A + C₂ * A := by dsimp [D]; nlinarith
      _ ≤ 2 * A + C₁ * A + C₂ * A := by nlinarith [hbase]
      _ = R * A := by dsimp [R]; ring
  have hLeE : Real.log (1 / ε) ≤ E := by dsimp [E]; linarith
  have hC2E : C₂ * Real.log (1 / ε) ≤ C₂ * E := mul_le_mul_of_nonneg_left hLeE hC₂
  have hBhE : (Bh : ℝ) + q + 1 ≤ R * E := by
    calc
      (Bh : ℝ) + q + 1 ≤ (q + 1) + C₂ * E := by nlinarith
      _ ≤ R * E := by dsimp [R, E]; nlinarith [mul_nonneg hC₁ hE]
  refine ⟨ℓ, f, Vb, Vf, W, c, hu, hq, ?_, ?_, ?_⟩
  · change (c.gateCount : ℝ) ≤ C * n * A ^ 2 * (q + 1)
    calc
      (c.gateCount : ℝ) ≤ Cc * n * D ^ 2 * (q + 1) := hg
      _ ≤ Cc * n * (R * A) ^ 2 * (q + 1) := by gcongr
      _ = (Cc * R ^ 2) * n * A ^ 2 * (q + 1) := by ring
      _ ≤ C * n * A ^ 2 * (q + 1) := by
        have hcoef : Cc * R ^ 2 ≤ C := by dsimp [C]; nlinarith [mul_nonneg hCc.le (show 0 ≤ R by exact hR0)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n))
            (sq_nonneg A)) (by positivity)
  · calc
      (Vb : ℝ) ≤ Cc * ((Bh : ℝ) + q + 1) := hV
      _ ≤ Cc * (R * E) := by gcongr
      _ = (Cc * R) * E := by ring
      _ ≤ C * E := mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [sq_nonneg R]) hE
  · intro w θ _ _ _ _ _
    exact hrun w θ
