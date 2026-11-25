-- Prove2me | solution 1 for QuantumLTF.Membership.localizedAffineBisect_circuit_core
-- status  : ACCEPTED   (disprove)
-- author  : @Robin Kothari
-- created : 2026-11-24T23:51:59.277131+00:00
-- url     : https://prove2.me/submissions/754571dc-dc38-4e3a-b309-677b045b7fe0

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

open QAlgorithms QuantumLTF.Membership

theorem solution :
    ¬ (∃ C : ℝ, 0 < C ∧ ∀ (n b q : ℕ) (p : EuclideanSpace ℝ (Fin n)) (Bp fp : ℕ),
      (∀ i, IsFp Bp fp (p i)) →
      ∀ (s : ℤ) (htil : ℝ) (Bh fh : ℕ), IsFp Bh fh htil →
        ∃ (ℓ f Vb Vf W : ℕ)
          (c : OracleCircuit gatesRev (fun _ : Fin 1 => n * ℓ + 1) (n * b + Vb + W)),
          Uncontrolled c ∧ c.queryCount 0 ≤ 2 * q ∧
          (c.gateCount : ℝ) ≤ C * n *
            ((b : ℝ) + Bp + Bh + Real.log n + q) ^ 2 * (q + 1) ∧
          (Vb : ℝ) ≤ C * (Bh + q + 1) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ),
            ∃ Htil : (Fin n → Qubits b) → Qubits Vb,
              (∀ x, act (c.unitary fun _ => memOracle n ℓ f w θ)
                  (ket (regBasis n b Vb W x fun _ => false)) =
                ket (regBasis n b Vb W x (Htil x))) ∧
              ∀ x, fpVal Vb Vf (Htil x) =
                (affineBoundaryBisect p (rho n • gridVec n b x) s q
                  (htil - 1 / 4) (htil + 1 / 4)).run (ltf w θ)) := by
  rintro ⟨C, _hC, h⟩
  -- counterexample: n = 0, b = 0, q = 0, htil = 0
  obtain ⟨ℓ, f, Vb, Vf, W, c, _hU, hq, hg, _hV, hall⟩ :=
    h 0 0 0 0 0 0 (fun i => i.elim0) 1 0 0 0 ⟨le_refl 0, 0, by simp, by simp⟩
  have hg0 : c.gateCount = 0 := by
    have : (c.gateCount : ℝ) ≤ 0 := by simpa using hg
    exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
  have hq0 : c.queryCount 0 = 0 := by simpa using hq
  have hc : c = [] := by
    cases c with
    | nil => rfl
    | cons st rest =>
      exfalso
      cases st with
      | gate g =>
        simp [OracleCircuit.gateCount] at hg0
      | query k adj ctl wires hcw =>
        have hk : k = 0 := Subsingleton.elim _ _
        subst hk
        simp [OracleCircuit.queryCount, OracleStep.IsQueryTo] at hq0
  subst hc
  obtain ⟨Htil, h1, h2⟩ := hall 0 0
  let x : Fin 0 → Qubits 0 := fun i => i.elim0
  have hu : OracleCircuit.unitary ([] : OracleCircuit gatesRev (fun _ : Fin 1 => 0 * ℓ + 1)
      (0 * 0 + Vb + W)) (fun _ => memOracle 0 ℓ f 0 0) = 1 := rfl
  have e := h1 x
  rw [hu] at e
  simp only [act, Matrix.one_mulVec] at e
  have e' : ket (regBasis 0 0 Vb W x fun _ => false) = ket (regBasis 0 0 Vb W x (Htil x)) := e
  have hreg : regBasis 0 0 Vb W x (fun _ => false) = regBasis 0 0 Vb W x (Htil x) := by
    have := congrArg (fun v => v (regBasis 0 0 Vb W x fun _ => false)) e'
    simp only [ket, PiLp.single_apply] at this
    by_contra hne
    rw [if_pos trivial, if_neg hne] at this
    exact one_ne_zero this
  have hH : Htil x = fun _ => false := by
    funext i
    have := congrFun hreg (Fin.castAdd W (Fin.natAdd (0 * 0) i))
    simp only [regBasis, Fin.append_left, Fin.append_right] at this
    exact this.symm
  have h2x := h2 x
  rw [hH] at h2x
  simp only [affineBoundaryBisect, QueryTree.run, fpVal] at h2x
  have hb : bitsToNat (fun _ : Fin Vb => false) = 0 := by simp [bitsToNat]
  rw [hb] at h2x
  have hpos : (0 : ℝ) < (2 : ℝ) ^ Vb / 2 := by positivity
  have h2f : (0 : ℝ) < (2 : ℝ) ^ Vf := by positivity
  have : ((0 : ℕ) : ℝ) - (2 : ℝ) ^ Vb / 2 = 0 := by
    have := h2x
    norm_num at this
  simp only [Nat.cast_zero, zero_sub, neg_eq_zero] at this
  linarith

