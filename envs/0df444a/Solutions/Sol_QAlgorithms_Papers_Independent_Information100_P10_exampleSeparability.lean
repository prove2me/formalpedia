-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P10.exampleSeparability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:03:22.4444+00:00
-- url     : https://prove2.me/submissions/f7aef8a2-4ff4-42a1-b281-1c75e8f0365f

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10
namespace QAlgorithms.Papers.Independent.Information100.P10
open scoped ComplexConjugate

lemma b0 : natToBits 3 0 = ![false,false,false] := by decide
lemma b6 : natToBits 3 6 = ![true,true,false] := by decide
lemma b3 : natToBits 3 3 = ![false,true,true] := by decide
lemma b7 : natToBits 3 7 = ![true,true,true] := by decide

lemma inner_ket_act {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (x y : ι) :
    inner ℂ (ket x : EuclideanSpace ℂ ι) (act A (ket y)) = A x y := by
  simp [ket, act, EuclideanSpace.inner_single_left, Matrix.mulVec_single]

lemma act_add {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) : act A (u + v) = act A u + act A v := by
  simp [act, Matrix.mulVec_add]
lemma act_sub {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) : act A (u - v) = act A u - act A v := by
  simp [act, Matrix.mulVec_sub]
lemma act_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ) (u : EuclideanSpace ℂ ι) : act A (c • u) = c • act A u := by
  simp [act, Matrix.mulVec_smul]
lemma norm_sq_act {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) :
    ‖v‖ ^ 2 = (inner ℂ v (act 1 v)).re := by
  rw [@norm_sq_eq_re_inner ℂ]; simp [act]

noncomputable def fam (cp ct sp st : ℝ) : Ket 3 :=
  (cp * ct : ℂ) • ket (natToBits 3 0) + (cp * st : ℂ) • ket (natToBits 3 6) +
  (sp * ct : ℂ) • ket (natToBits 3 3) - (sp * st : ℂ) • ket (natToBits 3 7)

lemma fam_eq (theta phi : ℝ) : threeQubitFamily theta phi =
    fam (Real.cos phi) (Real.cos theta) (Real.sin phi) (Real.sin theta) := by
  simp [threeQubitFamily, fam]

lemma norm_fam (cp ct sp st : ℝ) : ‖fam cp ct sp st‖ ^ 2 = (cp ^ 2 + sp ^ 2) * (ct ^ 2 + st ^ 2) := by
  have h1 : act (1 : Matrix (Qubits 3) (Qubits 3) ℂ) (fam cp ct sp st) = fam cp ct sp st := by
    simp [act]
  rw [@norm_sq_eq_re_inner ℂ]
  nth_rewrite 2 [← h1]
  simp only [fam, act_add, act_sub, act_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, inner_ket_act, b0, b6, b3, b7]
  simp [Matrix.one_apply]
  ring


lemma q3 (P : Qubits 3 → Prop) (h : ∀ a b c : Bool, P ![a, b, c]) : ∀ z, P z := by
  intro z
  have : z = ![z 0, z 1, z 2] := by funext i; fin_cases i <;> rfl
  rw [this]; exact h _ _ _

lemma q2 (P : Qubits 2 → Prop) (h : ∀ a b : Bool, P ![a, b]) : ∀ z, P z := by
  intro z
  have : z = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
  rw [this]; exact h _ _

lemma c0 : natToBits 2 0 = ![false,false] := by decide
lemma c3 : natToBits 2 3 = ![true,true] := by decide

lemma ket_apply {ι : Type*} [DecidableEq ι] (x y : ι) : (ket x : EuclideanSpace ℂ ι) y = if y = x then 1 else 0 := by
  simp [ket, EuclideanSpace.single_apply]

lemma fam_apply (cp ct sp st : ℝ) (a b c : Bool) : fam cp ct sp st ![a, b, c] =
    (if a = false ∧ b = false ∧ c = false then (cp * ct : ℂ) else 0) +
    (if a = true ∧ b = true ∧ c = false then (cp * st : ℂ) else 0) +
    (if a = false ∧ b = true ∧ c = true then (sp * ct : ℂ) else 0) -
    (if a = true ∧ b = true ∧ c = true then (sp * st : ℂ) else 0) := by
  cases a <;> cases b <;> cases c <;> simp [fam, ket_apply, b0, b6, b3, b7]

lemma pair_apply (theta : ℝ) (a b : Bool) : examplePair theta ![a, b] =
    (if a = false ∧ b = false then (Real.cos theta : ℂ) else 0) +
    (if a = true ∧ b = true then (Real.sin theta : ℂ) else 0) := by
  cases a <;> cases b <;> simp [examplePair, ket_apply, c0, c3]


lemma prod3 (f : Fin 3 → EuclideanSpace ℂ Bool) (a b c : Bool) :
    prodState f ![a, b, c] = f 0 a * f 1 b * f 2 c := by
  simp [prodState, Fin.prod_univ_three]

lemma prod2 (f : Fin 2 → EuclideanSpace ℂ Bool) (a b : Bool) :
    prodState f ![a, b] = f 0 a * f 1 b := by
  simp [prodState, Fin.prod_univ_two]

lemma rank3 {psi : Ket 3} (h : FullySeparable psi) :
    psi ![false, false, false] * psi ![true, true, false] =
      psi ![true, false, false] * psi ![false, true, false] := by
  obtain ⟨z, f, -, -, rfl⟩ := h
  simp only [PiLp.smul_apply, smul_eq_mul, prod3]
  ring

lemma rank2 {psi : Ket 2} (h : FullySeparable psi) :
    psi ![false, false] * psi ![true, true] = psi ![true, false] * psi ![false, true] := by
  obtain ⟨z, f, -, -, rfl⟩ := h
  simp only [PiLp.smul_apply, smul_eq_mul, prod2]
  ring

lemma norm_ket1 (b : Bool) : IsState (ket b : EuclideanSpace ℂ Bool) := by
  simp [IsState, ket]

lemma norm_comb (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    IsState ((x : ℂ) • (ket false : EuclideanSpace ℂ Bool) - (y : ℂ) • ket true) := by
  unfold IsState
  have h2 : ‖((x : ℂ) • (ket false : EuclideanSpace ℂ Bool) - (y : ℂ) • ket true)‖ ^ 2 = 1 := by
    rw [norm_sq_act]
    simp only [act_sub, act_smul, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, inner_ket_act]
    simp [Matrix.one_apply]
    nlinarith [h]
  have := norm_nonneg ((x : ℂ) • (ket false : EuclideanSpace ℂ Bool) - (y : ℂ) • ket true)
  nlinarith

lemma pair_state (theta : ℝ) : IsState (examplePair theta) := by
  unfold IsState
  have h2 : ‖examplePair theta‖ ^ 2 = 1 := by
    rw [norm_sq_act]
    simp only [examplePair, act_add, act_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_ket_act, c0, c3]
    simp [Matrix.one_apply, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    nlinarith [Real.cos_sq_add_sin_sq theta]
  have := norm_nonneg (examplePair theta)
  nlinarith

lemma z1 : (fun _ : Fin 1 => false) = ![false] := by funext i; fin_cases i; rfl

lemma append_eq (theta : ℝ) : threeQubitFamily theta 0 = appendKet (examplePair theta) (zeroKet 1) := by
  ext z
  revert z
  refine q3 _ (fun a b c => ?_)
  have e1 : (fun i : Fin 2 => (![a, b, c] : Qubits 3) (Fin.castAdd 1 i)) = ![a, b] := by
    funext i; fin_cases i <;> rfl
  have e2 : (fun j : Fin 1 => (![a, b, c] : Qubits 3) (Fin.natAdd 2 j)) = ![c] := by
    funext i; fin_cases i; rfl
  rw [fam_eq]
  simp only [appendKet, tensorVec, qubitsAppendEquiv, Equiv.coe_fn_mk, e1, e2, PiLp.toLp_apply, fam_apply, pair_apply]
  cases a <;> cases b <;> cases c <;> simp [zeroKet, ket_apply, z1]

lemma hf3 (f0 f1 f2 : EuclideanSpace ℂ Bool) (h0 : IsState f0) (h1 : IsState f1) (h2 : IsState f2) :
    ∀ q, IsState (![f0, f1, f2] q) := by
  intro q; fin_cases q
  · exact h0
  · exact h1
  · exact h2

lemma sep_of (cp ct sp st : ℝ) (f : Fin 3 → EuclideanSpace ℂ Bool) (hf : ∀ q, IsState (f q))
    (h : ∀ a b c : Bool, fam cp ct sp st ![a, b, c] = f 0 a * f 1 b * f 2 c) :
    FullySeparable (fam cp ct sp st) := by
  refine ⟨1, f, by simp, hf, ?_⟩
  ext z
  revert z
  refine q3 _ (fun a b c => ?_)
  simp only [one_smul, prod3, h]

end QAlgorithms.Papers.Independent.Information100.P10

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P10 in
theorem solution (theta phi : ℝ)
    (htheta : theta ∈ Set.Icc 0 (Real.pi / 2))
    (hphi : phi ∈ Set.Icc 0 (Real.pi / 2)) :
    IsState (threeQubitFamily theta phi) ∧
    (0 < theta → theta < Real.pi / 2 →
      IsState (examplePair theta) ∧ ¬ FullySeparable (examplePair theta) ∧
      threeQubitFamily theta 0 = appendKet (examplePair theta) (zeroKet 1) ∧
      ¬ FullySeparable (threeQubitFamily theta 0)) ∧
    FullySeparable (threeQubitFamily 0 0) ∧
    FullySeparable (threeQubitFamily (Real.pi / 2) 0) ∧
    FullySeparable (threeQubitFamily theta (Real.pi / 2)) ∧
    FullySeparable (threeQubitFamily (Real.pi / 2) phi) := by
  have hp := Real.cos_sq_add_sin_sq phi
  have ht := Real.cos_sq_add_sin_sq theta
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fam_eq]
    have := norm_fam (Real.cos phi) (Real.cos theta) (Real.sin phi) (Real.sin theta)
    rw [hp, ht, one_mul] at this
    unfold IsState
    nlinarith [norm_nonneg (fam (Real.cos phi) (Real.cos theta) (Real.sin phi) (Real.sin theta))]
  · intro h0 h1
    have hc : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
    have hs : 0 < Real.sin theta := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    refine ⟨pair_state theta, ?_, append_eq theta, ?_⟩
    · intro hsep
      have := rank2 hsep
      simp only [pair_apply] at this
      simp at this
      rcases this with h | h <;>
      · have h' := congrArg Complex.re h
        simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re] at h'
        linarith
    · intro hsep
      have := rank3 hsep
      rw [fam_eq] at this
      simp only [fam_apply] at this
      simp at this
      rcases this with h | h <;>
      · have h' := congrArg Complex.re h
        simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re] at h'
        linarith
  · rw [fam_eq]
    simp only [Real.cos_zero, Real.sin_zero]
    refine sep_of _ _ _ _ (fun _ => ket false) (fun _ => norm_ket1 _) ?_
    intro a b c; rw [fam_apply]
    cases a <;> cases b <;> cases c <;> simp [ket_apply]
  · rw [fam_eq]
    simp only [Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two]
    refine sep_of _ _ _ _ ![ket true, ket true, ket false] (hf3 _ _ _ (norm_ket1 _) (norm_ket1 _) (norm_ket1 _)) ?_
    intro a b c; rw [fam_apply]
    cases a <;> cases b <;> cases c <;> simp [ket_apply]
  · rw [fam_eq]
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two]
    refine sep_of _ _ _ _ ![(Real.cos theta : ℂ) • ket false - (Real.sin theta : ℂ) • ket true, ket true, ket true]
      (hf3 _ _ _ (norm_comb _ _ ht) (norm_ket1 _) (norm_ket1 _)) ?_
    intro a b c; rw [fam_apply]
    cases a <;> cases b <;> cases c <;> simp [ket_apply]
  · rw [fam_eq]
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two]
    refine sep_of _ _ _ _ ![ket true, ket true, (Real.cos phi : ℂ) • ket false - (Real.sin phi : ℂ) • ket true]
      (hf3 _ _ _ (norm_ket1 _) (norm_ket1 _) (norm_comb _ _ hp)) ?_
    intro a b c; rw [fam_apply]
    cases a <;> cases b <;> cases c <;> simp [ket_apply]
