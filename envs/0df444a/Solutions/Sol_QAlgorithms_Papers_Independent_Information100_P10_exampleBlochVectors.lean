-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P10.exampleBlochVectors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T17:58:33.983031+00:00
-- url     : https://prove2.me/submissions/2cd5fa00-24c5-4149-9d51-b941671ffffb

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10
namespace QAlgorithms.Papers.Independent.Information100.P10
open scoped ComplexConjugate

lemma b0 : natToBits 3 0 = ![false,false,false] := by decide
lemma b6 : natToBits 3 6 = ![true,true,false] := by decide
lemma b3 : natToBits 3 3 = ![false,true,true] := by decide
lemma b7 : natToBits 3 7 = ![true,true,true] := by decide

lemma inner_ket_act (A : Matrix (Qubits 3) (Qubits 3) ℂ) (x y : Qubits 3) :
    inner ℂ (ket x) (act A (ket y)) = A x y := by
  simp [ket, act, EuclideanSpace.inner_single_left, Matrix.mulVec_single]

lemma act_add (A : Matrix (Qubits 3) (Qubits 3) ℂ) (u v : Ket 3) : act A (u + v) = act A u + act A v := by
  simp [act, Matrix.mulVec_add]
lemma act_sub (A : Matrix (Qubits 3) (Qubits 3) ℂ) (u v : Ket 3) : act A (u - v) = act A u - act A v := by
  simp [act, Matrix.mulVec_sub]
lemma act_smul (A : Matrix (Qubits 3) (Qubits 3) ℂ) (c : ℂ) (u : Ket 3) : act A (c • u) = c • act A u := by
  simp [act, Matrix.mulVec_smul]

noncomputable def fam (cp ct sp st : ℝ) : Ket 3 :=
  (cp * ct : ℂ) • ket (natToBits 3 0) + (cp * st : ℂ) • ket (natToBits 3 6) +
  (sp * ct : ℂ) • ket (natToBits 3 3) - (sp * st : ℂ) • ket (natToBits 3 7)

lemma fam_eq (theta phi : ℝ) : threeQubitFamily theta phi =
    fam (Real.cos phi) (Real.cos theta) (Real.sin phi) (Real.sin theta) := by
  simp [threeQubitFamily, fam]

lemma bloch_fam (cp ct sp st : ℝ) (q a : Fin 3) : (bloch (fam cp ct sp st) q) a =
    ![![-2 * ct * st * sp ^ 2, 0, (ct ^ 2 - st ^ 2) * (cp ^ 2 + sp ^ 2)],
      ![0, 0, cp ^ 2 * (ct ^ 2 - st ^ 2) - sp ^ 2 * (ct ^ 2 + st ^ 2)],
      ![-2 * st ^ 2 * sp * cp, 0, (cp ^ 2 - sp ^ 2) * (ct ^ 2 + st ^ 2)]] q a := by
  simp only [bloch, fam, act_add, act_sub, act_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, inner_ket_act, b0, b6, b3, b7, localPauli, kronAll,
    Matrix.of_apply, Fin.prod_univ_three]
  fin_cases q <;> fin_cases a <;> simp [pauli, pauliX, pauliY, pauliZ, Matrix.one_apply] <;> ring

lemma norm_fam (cp ct sp st : ℝ) : ‖fam cp ct sp st‖ ^ 2 = (cp ^ 2 + sp ^ 2) * (ct ^ 2 + st ^ 2) := by
  have h1 : act (1 : Matrix (Qubits 3) (Qubits 3) ℂ) (fam cp ct sp st) = fam cp ct sp st := by
    simp [act]
  rw [@norm_sq_eq_re_inner ℂ]
  nth_rewrite 2 [← h1]
  simp only [fam, act_add, act_sub, act_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, inner_ket_act, b0, b6, b3, b7]
  simp [Matrix.one_apply]
  ring

end QAlgorithms.Papers.Independent.Information100.P10

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P10 in
theorem solution (theta phi : ℝ)
    (htheta : theta ∈ Set.Icc 0 (Real.pi / 2))
    (hphi : phi ∈ Set.Icc 0 (Real.pi / 2)) :
    IsState (threeQubitFamily theta phi) ∧
    bloch (threeQubitFamily theta phi) 0 = WithLp.toLp 2
      ![-2 * Real.cos theta * Real.sin theta * Real.sin phi ^ 2,
        0, Real.cos theta ^ 2 - Real.sin theta ^ 2] ∧
    bloch (threeQubitFamily theta phi) 1 = WithLp.toLp 2
      ![0, 0, (Real.cos theta ^ 2 - Real.sin theta ^ 2) * Real.cos phi ^ 2 -
        Real.sin phi ^ 2] ∧
    bloch (threeQubitFamily theta phi) 2 = WithLp.toLp 2
      ![-2 * Real.sin theta ^ 2 * Real.sin phi * Real.cos phi,
        0, Real.cos phi ^ 2 - Real.sin phi ^ 2] := by
  have hp := Real.cos_sq_add_sin_sq phi
  have ht := Real.cos_sq_add_sin_sq theta
  rw [fam_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := norm_fam (Real.cos phi) (Real.cos theta) (Real.sin phi) (Real.sin theta)
    rw [hp, ht, one_mul] at this
    unfold IsState
    nlinarith [norm_nonneg (fam (Real.cos phi) (Real.cos theta) (Real.sin phi) (Real.sin theta))]
  all_goals
    ext a
    rw [bloch_fam]
    fin_cases a <;> simp [hp, ht] <;> nlinarith [hp, ht]

