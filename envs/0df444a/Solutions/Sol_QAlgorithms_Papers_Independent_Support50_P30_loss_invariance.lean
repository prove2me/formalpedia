-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P30.loss_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:12:19.918915+00:00
-- url     : https://prove2.me/submissions/42b19046-7d12-464d-9fdb-3c7658a67f16

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

open scoped Matrix Matrix.Norms.L2Operator

namespace X8LI

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P30

lemma layer_comm {n : ℕ} (W H : QnnOperator n) (h : H * W = W * H) (t : ℝ) :
    Commute W (qnnLayer H t) := by
  unfold qnnLayer
  apply Commute.exp_right
  exact ((Commute.symm h).smul_right _)

lemma circuit_comm {n L : ℕ} (W : QnnOperator n) (H : Fin L → QnnOperator n)
    (h : ∀ j, H j * W = W * H j) (theta : Fin L → ℝ) : Commute W (circuit H theta) := by
  unfold circuit orderedProd
  apply Commute.list_prod_right
  intro x hx
  rw [List.mem_reverse, List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  exact layer_comm W (H j) (h j) (theta j)

lemma loss_inv {n : ℕ} (U W rho O : QnnOperator n) (hW1 : W * Wᴴ = 1) (hW2 : Wᴴ * W = 1)
    (hU : W * U = U * W) (hO : O * W = W * O) :
    qnnLoss U (W * rho * Wᴴ) O = qnnLoss U rho O := by
  unfold qnnLoss
  have hU' : U * Wᴴ = Wᴴ * U := by
    calc U * Wᴴ = Wᴴ * W * U * Wᴴ := by rw [hW2, Matrix.one_mul]
      _ = Wᴴ * U * W * Wᴴ := by rw [Matrix.mul_assoc Wᴴ W U, hU, ← Matrix.mul_assoc]
      _ = Wᴴ * U := by rw [Matrix.mul_assoc _ W, hW1, Matrix.mul_one]
  have hUc : W * Uᴴ = Uᴴ * W := by
    have := congrArg Matrix.conjTranspose hU'
    simpa [Matrix.conjTranspose_mul] using this
  have e : U * (W * rho * Wᴴ) * Uᴴ * O = W * (U * rho * Uᴴ * Wᴴ * O) := by
    calc U * (W * rho * Wᴴ) * Uᴴ * O = (U * W) * rho * (Wᴴ * Uᴴ) * O := by
          simp only [Matrix.mul_assoc]
      _ = (W * U) * rho * (Uᴴ * Wᴴ) * O := by
          rw [← hU]
          have : Wᴴ * Uᴴ = Uᴴ * Wᴴ := by
            have := congrArg Matrix.conjTranspose hU
            simpa [Matrix.conjTranspose_mul] using this.symm
          rw [this]
      _ = W * (U * rho * Uᴴ * Wᴴ * O) := by simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm]
  have : U * rho * Uᴴ * Wᴴ * O * W = U * rho * Uᴴ * O := by
    have hO' : Wᴴ * O = O * Wᴴ := by
      calc Wᴴ * O = Wᴴ * O * W * Wᴴ := by rw [Matrix.mul_assoc _ W, hW1, Matrix.mul_one]
        _ = Wᴴ * W * O * Wᴴ := by rw [Matrix.mul_assoc Wᴴ O W, hO, ← Matrix.mul_assoc]
        _ = O * Wᴴ := by rw [hW2, Matrix.one_mul]
    calc U * rho * Uᴴ * Wᴴ * O * W = U * rho * Uᴴ * (Wᴴ * O) * W := by simp only [Matrix.mul_assoc]
      _ = U * rho * Uᴴ * O * (Wᴴ * W) := by rw [hO']; simp only [Matrix.mul_assoc]
      _ = U * rho * Uᴴ * O := by rw [hW2, Matrix.mul_one]
  rw [this]

end X8LI

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P30 in
theorem solution {n L : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]
    (R : G →* Matrix.unitaryGroup (Qubits n) ℂ) (hR : Continuous R)
    (H : Fin L → QnnOperator n) (hH : ∀ j, (H j).IsHermitian)
    (hcomm : ∀ j g, H j * (R g).val = (R g).val * H j)
    (O : QnnOperator n) (hO : O.IsHermitian)
    (hOcomm : ∀ g, O * (R g).val = (R g).val * O) :
    ∀ (theta : Fin L → ℝ) (rho : QnnDensity n) (g : G),
      qnnLoss (circuit H theta) ((R g).val * rho.val * (R g).val.conjTranspose) O =
        qnnLoss (circuit H theta) rho.val O := by
  intro theta rho g
  have hu := (R g).2
  have h1 : (R g).val * ((R g).val)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hu
  have h2 : ((R g).val)ᴴ * (R g).val = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
  exact X8LI.loss_inv _ _ _ _ h1 h2 (X8LI.circuit_comm _ H (fun j => hcomm j g) theta).eq (hOcomm g)
