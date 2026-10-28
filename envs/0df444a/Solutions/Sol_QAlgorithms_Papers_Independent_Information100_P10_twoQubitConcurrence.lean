-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P10.twoQubitConcurrence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:25:39.698541+00:00
-- url     : https://prove2.me/submissions/278d3116-90ad-4c82-8568-6dd2b842db9a

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_geometricMinimum
namespace QAlgorithms.Papers.Independent.Information100.P10
open scoped ComplexConjugate

lemma e0 : natToBits 2 0 = ![false,false] := by decide
lemma e1 : natToBits 2 1 = ![false,true] := by decide
lemma e2 : natToBits 2 2 = ![true,false] := by decide
lemma e3 : natToBits 2 3 = ![true,true] := by decide

lemma E_inner_ket_act {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (x y : ι) :
    inner ℂ (ket x : EuclideanSpace ℂ ι) (act A (ket y)) = A x y := by
  simp [ket, act, EuclideanSpace.inner_single_left, Matrix.mulVec_single]
lemma E_act_add {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) :
    act A (u + v) = act A u + act A v := by simp [act, Matrix.mulVec_add]
lemma E_act_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ) (u : EuclideanSpace ℂ ι) :
    act A (c • u) = c • act A u := by simp [act, Matrix.mulVec_smul]
lemma E_norm_sq_act {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) :
    ‖v‖ ^ 2 = (inner ℂ v (act 1 v)).re := by
  rw [@norm_sq_eq_re_inner ℂ]; simp [act]
lemma E_ket_apply {ι : Type*} [DecidableEq ι] (x y : ι) :
    (ket x : EuclideanSpace ℂ ι) y = if y = x then 1 else 0 := by
  simp [ket, EuclideanSpace.single_apply]

lemma E_q2 (P : Qubits 2 → Prop) (h : ∀ a b : Bool, P ![a, b]) : ∀ z, P z := by
  intro z
  have : z = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
  rw [this]; exact h _ _

noncomputable def W2 (w0 w1 w2 w3 : ℂ) : Ket 2 :=
  w0 • ket ![false,false] + w1 • ket ![false,true] + w2 • ket ![true,false] + w3 • ket ![true,true]

lemma E_expand (psi : Ket 2) : psi =
    W2 (psi ![false,false]) (psi ![false,true]) (psi ![true,false]) (psi ![true,true]) := by
  unfold W2
  ext z; revert z
  refine E_q2 _ (fun a b => ?_)
  cases a <;> cases b <;> simp [E_ket_apply]

lemma W2_norm (w0 w1 w2 w3 : ℂ) : ‖W2 w0 w1 w2 w3‖ ^ 2 =
    (w0.re ^ 2 + w0.im ^ 2) + (w1.re ^ 2 + w1.im ^ 2) + (w2.re ^ 2 + w2.im ^ 2) + (w3.re ^ 2 + w3.im ^ 2) := by
  rw [E_norm_sq_act]
  simp only [W2, E_act_add, E_act_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    E_inner_ket_act]
  simp [Matrix.one_apply]
  ring

lemma W2_bloch (w0 w1 w2 w3 : ℂ) : ‖bloch (W2 w0 w1 w2 w3) 0‖ ^ 2 + ‖bloch (W2 w0 w1 w2 w3) 1‖ ^ 2 =
    (2 * (w0.re * w2.re + w0.im * w2.im + w1.re * w3.re + w1.im * w3.im)) ^ 2 +
    (2 * (w0.re * w2.im - w0.im * w2.re + w1.re * w3.im - w1.im * w3.re)) ^ 2 +
    ((w0.re ^ 2 + w0.im ^ 2) + (w1.re ^ 2 + w1.im ^ 2) - (w2.re ^ 2 + w2.im ^ 2) - (w3.re ^ 2 + w3.im ^ 2)) ^ 2 +
    ((2 * (w0.re * w1.re + w0.im * w1.im + w2.re * w3.re + w2.im * w3.im)) ^ 2 +
    (2 * (w0.re * w1.im - w0.im * w1.re + w2.re * w3.im - w2.im * w3.re)) ^ 2 +
    ((w0.re ^ 2 + w0.im ^ 2) - (w1.re ^ 2 + w1.im ^ 2) + (w2.re ^ 2 + w2.im ^ 2) - (w3.re ^ 2 + w3.im ^ 2)) ^ 2) := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp only [bloch, PiLp.toLp_apply, W2, E_act_add, E_act_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, E_inner_ket_act, localPauli, kronAll, Matrix.of_apply, Fin.prod_univ_two]
  simp [pauli, pauliX, pauliY, pauliZ, Matrix.one_apply]
  ring

lemma W2_conj (w0 w1 w2 w3 : ℂ) : (WithLp.toLp 2 (fun z => conj (W2 w0 w1 w2 w3 z)) : Ket 2) =
    W2 (conj w0) (conj w1) (conj w2) (conj w3) := by
  ext z; revert z
  refine E_q2 _ (fun a b => ?_)
  cases a <;> cases b <;> simp [W2, E_ket_apply]

lemma W2_conc (w0 w1 w2 w3 : ℂ) : concurrence (W2 w0 w1 w2 w3) ^ 2 =
    4 * ((w0.re * w3.re - w0.im * w3.im - (w1.re * w2.re - w1.im * w2.im)) ^ 2 +
      (w0.re * w3.im + w0.im * w3.re - (w1.re * w2.im + w1.im * w2.re)) ^ 2) := by
  unfold concurrence
  rw [W2_conj, Complex.sq_norm, Complex.normSq_apply]
  simp only [W2, E_act_add, E_act_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, E_inner_ket_act, kronAll, Matrix.of_apply, Fin.prod_univ_two]
  simp [pauliY]
  ring

end QAlgorithms.Papers.Independent.Information100.P10

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P10 in
open scoped ComplexConjugate in
theorem solution (psi : Ket 2) (hpsi : IsState psi) :
    let w := fun j => psi (natToBits 2 j)
    entanglementDistance psi = 8 *
      (‖w 0‖ ^ 2 * ‖w 3‖ ^ 2 + ‖w 1‖ ^ 2 * ‖w 2‖ ^ 2 -
        2 * (conj (w 0) * conj (w 3) * w 1 * w 2).re) ∧
    entanglementDistance psi = 2 * concurrence psi ^ 2 ∧
    concurrence psi ∈ Set.Icc (0 : ℝ) 1 ∧
    StrictMonoOn (fun c : ℝ => 2 * c ^ 2) (Set.Icc 0 1) := by
  intro w
  have hED := (geometricMinimum psi hpsi).2.2.2.2.1
  simp only [Fin.sum_univ_two, Nat.cast_ofNat] at hED
  have hE := E_expand psi
  simp only [w, e0, e1, e2, e3]
  set w0 := psi ![false, false]
  set w1 := psi ![false, true]
  set w2 := psi ![true, false]
  set w3 := psi ![true, true]
  clear_value w0 w1 w2 w3
  subst hE
  have hn := W2_norm w0 w1 w2 w3
  rw [show ‖W2 w0 w1 w2 w3‖ = 1 from hpsi, one_pow] at hn
  have hb := W2_bloch w0 w1 w2 w3
  have hc := W2_conc w0 w1 w2 w3
  have hED' : entanglementDistance (W2 w0 w1 w2 w3) = 2 * concurrence (W2 w0 w1 w2 w3) ^ 2 := by
    rw [hED, hc]
    rw [show (2:ℝ) - (‖bloch (W2 w0 w1 w2 w3) 0‖ ^ 2 + ‖bloch (W2 w0 w1 w2 w3) 1‖ ^ 2) =
      2 - (‖bloch (W2 w0 w1 w2 w3) 0‖ ^ 2 + ‖bloch (W2 w0 w1 w2 w3) 1‖ ^ 2) from rfl, hb]
    linear_combination (2 * ((w0.re ^ 2 + w0.im ^ 2) + (w1.re ^ 2 + w1.im ^ 2) + (w2.re ^ 2 + w2.im ^ 2) + (w3.re ^ 2 + w3.im ^ 2) + 1)) * hn
  refine ⟨?_, hED', ⟨norm_nonneg _, ?_⟩, ?_⟩
  · rw [hED', hc]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    ring
  · have hsq : concurrence (W2 w0 w1 w2 w3) ^ 2 ≤ 1 := by
      rw [hc]
      have key : 4 * ((w0.re * w3.re - w0.im * w3.im - (w1.re * w2.re - w1.im * w2.im)) ^ 2 +
          (w0.re * w3.im + w0.im * w3.re - (w1.re * w2.im + w1.im * w2.re)) ^ 2) =
          ((w0.re ^ 2 + w0.im ^ 2) + (w1.re ^ 2 + w1.im ^ 2) + (w2.re ^ 2 + w2.im ^ 2) + (w3.re ^ 2 + w3.im ^ 2)) ^ 2 - ((2 * (w0.re * w2.re + w0.im * w2.im + w1.re * w3.re + w1.im * w3.im)) ^ 2 +
          (2 * (w0.re * w2.im - w0.im * w2.re + w1.re * w3.im - w1.im * w3.re)) ^ 2 +
          ((w0.re ^ 2 + w0.im ^ 2) + (w1.re ^ 2 + w1.im ^ 2) - (w2.re ^ 2 + w2.im ^ 2) - (w3.re ^ 2 + w3.im ^ 2)) ^ 2) := by
        ring
      rw [key, ← hn]
      linarith [sq_nonneg (2 * (w0.re * w2.re + w0.im * w2.im + w1.re * w3.re + w1.im * w3.im)),
        sq_nonneg (2 * (w0.re * w2.im - w0.im * w2.re + w1.re * w3.im - w1.im * w3.re)),
        sq_nonneg ((w0.re ^ 2 + w0.im ^ 2) + (w1.re ^ 2 + w1.im ^ 2) - (w2.re ^ 2 + w2.im ^ 2) - (w3.re ^ 2 + w3.im ^ 2))]
    nlinarith [norm_nonneg (concurrence (W2 w0 w1 w2 w3)), sq_nonneg (concurrence (W2 w0 w1 w2 w3) - 1)]
  · intro x hx y hy hxy
    simp only [Set.mem_Icc] at hx hy
    show 2 * x ^ 2 < 2 * y ^ 2
    nlinarith
