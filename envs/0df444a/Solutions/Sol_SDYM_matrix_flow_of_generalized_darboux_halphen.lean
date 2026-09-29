-- Prove2me | solution 1 for SDYM.matrix_flow_of_generalized_darboux_halphen
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T00:58:14.806246+00:00
-- url     : https://prove2.me/submissions/cf637c3f-8de8-42c6-9ff6-f3e5c3da75b2

import Definitions.Def_SDYM_ChazyEquations
import Definitions.Def_SDYM_DarbouxHalphenRamanujan

open SDYM

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false


open Matrix in
theorem solution
    (s : Set ℂ) (w₁ w₂ w₃ x₁ x₂ x₃ : ℂ → ℂ)
    (A P M : ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (hDH : IsGeneralizedDHSolution s w₁ w₂ w₃ x₁ x₂ x₃)
    (hA : ∀ t : ℂ, A t = !![0, x₃ t, -x₂ t; -x₃ t, 0, x₁ t; x₂ t, -x₁ t, 0])
    (hPorth : ∀ t ∈ s, (P t).transpose * P t = 1)
    (hP : ∀ t ∈ s, ∀ i j, HasDerivAt (fun z => P z i j) ((-(P t * A t)) i j) t)
    (hM : ∀ t : ℂ, M t = P t * (Matrix.diagonal ![w₁ t, w₂ t, w₃ t] + A t) * (P t).transpose) :
    ∀ t ∈ s, ∀ i j, HasDerivAt (fun z => M z i j)
      (((M t).adjugate.transpose + (M t).transpose * M t
        - Matrix.trace (M t) • M t) i j) t := by
  obtain ⟨h1, h2, h3, g1, g2, g3⟩ := hDH
  intro t ht i j
  obtain ⟨X, hX⟩ : ∃ X : ℂ → Matrix (Fin 3) (Fin 3) ℂ,
      ∀ z, X z = Matrix.diagonal ![w₁ z, w₂ z, w₃ z] + A z := ⟨_, fun z => rfl⟩
  obtain ⟨Xd, hXd⟩ : ∃ Xd : Matrix (Fin 3) (Fin 3) ℂ, Xd =
      Matrix.diagonal ![w₂ t * w₃ t - w₁ t * (w₂ t + w₃ t) + (x₁ t ^ 2 + x₂ t ^ 2 + x₃ t ^ 2),
        w₃ t * w₁ t - w₂ t * (w₃ t + w₁ t) + (x₁ t ^ 2 + x₂ t ^ 2 + x₃ t ^ 2),
        w₁ t * w₂ t - w₃ t * (w₁ t + w₂ t) + (x₁ t ^ 2 + x₂ t ^ 2 + x₃ t ^ 2)]
      + !![0, -(x₃ t) * (w₁ t + w₂ t), -(-(x₂ t) * (w₃ t + w₁ t));
          -(-(x₃ t) * (w₁ t + w₂ t)), 0, -(x₁ t) * (w₂ t + w₃ t);
          -(x₂ t) * (w₃ t + w₁ t), -(-(x₁ t) * (w₂ t + w₃ t)), 0] := ⟨_, rfl⟩
  have hXe : ∀ k l, HasDerivAt (fun z => X z k l) (Xd k l) t := by
    intro k l
    simp only [hX, hA, hXd]
    fin_cases k <;> fin_cases l <;> simp <;>
      first
      | exact hasDerivAt_const _ _
      | (refine (h1 t ht).congr_deriv ?_ <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]) <;> ring)
      | (refine (h2 t ht).congr_deriv ?_ <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]) <;> ring)
      | (refine (h3 t ht).congr_deriv ?_ <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]) <;> ring)
      | (refine (g1 t ht).congr_deriv ?_ <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]) <;> ring)
      | (refine (g2 t ht).congr_deriv ?_ <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]) <;> ring)
      | (refine (g3 t ht).congr_deriv ?_ <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]) <;> ring)
      | (refine (g1 t ht).neg.congr_deriv ?_ <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]) <;> ring)
      | (refine (g2 t ht).neg.congr_deriv ?_ <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]) <;> ring)
      | (refine (g3 t ht).neg.congr_deriv ?_ <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply]) <;> ring)
  have hPt := hPorth t ht
  have hAt : (A t)ᵀ = -(A t) := by
    rw [hA t]
    ext k l
    fin_cases k <;> fin_cases l <;> simp
  have hdet : (P t).det ^ 2 = 1 := by
    have := congrArg Matrix.det hPt
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rw [sq]
    exact this
  have hadjP : (P t).adjugate = (P t).det • (P t)ᵀ := by
    calc (P t).adjugate = ((P t)ᵀ * P t) * (P t).adjugate := by rw [hPt, Matrix.one_mul]
      _ = (P t)ᵀ * (P t * (P t).adjugate) := by rw [Matrix.mul_assoc]
      _ = (P t)ᵀ * ((P t).det • (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by rw [Matrix.mul_adjugate]
      _ = (P t).det • (P t)ᵀ := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hadjPt : ((P t)ᵀ).adjugate = (P t).det • P t := by
    rw [← Matrix.adjugate_transpose, hadjP, Matrix.transpose_smul, Matrix.transpose_transpose]
  have hMt : M t = P t * X t * (P t)ᵀ := by rw [hM t, hX t]
  have hadjM : (M t).adjugate = P t * (X t).adjugate * (P t)ᵀ := by
    rw [hMt, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadjPt, hadjP]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [← sq, hdet, one_smul]
    simp only [Matrix.mul_assoc]
  have htr : Matrix.trace (M t) = Matrix.trace (X t) := by
    rw [hMt, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPt, Matrix.one_mul]
  have hK : -(A t * X t) + Xd + X t * A t
      = (X t).adjugate.transpose + (X t).transpose * X t - Matrix.trace (X t) • X t := by
    rw [hX t, hA t, hXd]
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp [Matrix.adjugate_fin_three, Matrix.trace_fin_three, Matrix.mul_apply,
        Fin.sum_univ_three, Matrix.vecMul, dotProduct] <;> ring
  have hc : ∀ Y : Matrix (Fin 3) (Fin 3) ℂ, (P t)ᵀ * (P t * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hPt, Matrix.one_mul]
  have E : -(P t * A t) * X t * (P t)ᵀ + P t * Xd * (P t)ᵀ + P t * X t * (-(P t * A t))ᵀ
      = (M t).adjugate.transpose + (M t).transpose * M t - Matrix.trace (M t) • M t := by
    calc _ = P t * (-(A t * X t) + Xd + X t * A t) * (P t)ᵀ := by
          rw [Matrix.transpose_neg, Matrix.transpose_mul, hAt]
          noncomm_ring
      _ = P t * ((X t).adjugate.transpose + (X t).transpose * X t
            - Matrix.trace (X t) • X t) * (P t)ᵀ := by rw [hK]
      _ = _ := by
          rw [htr, hadjM, hMt]
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add,
            Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_assoc, hc]
  have e : (fun z => M z i j) = fun z => ∑ l, (∑ k, P z i k * X z k l) * P z j l := by
    funext z
    rw [hM z, ← hX z]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [e, ← E]
  have hMd := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    (HasDerivAt.fun_sum (u := Finset.univ)
      (fun k _ => (hP t ht i k).mul (hXe k l))).mul (hP t ht j l))
  refine hMd.congr_deriv ?_
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_add_distrib, add_mul, Pi.mul_apply]
