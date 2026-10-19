-- Prove2me | solution 1 for QAlgorithms.Nannicini.schmidtDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:07:31.987744+00:00
-- url     : https://prove2.me/submissions/2d7c61d5-5448-4f56-bc4f-060e3523f702

import Definitions.Def_QAlgorithms_Defs_Measurement
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
open QAlgorithms
open scoped ComplexConjugate

private theorem tensor_inner {A B : Type*} [Fintype A] [Fintype B]
    (u x : EuclideanSpace ℂ A) (v y : EuclideanSpace ℂ B) :
    inner ℂ (tensorVec u v) (tensorVec x y) = inner ℂ u x * inner ℂ v y := by
  simp only [PiLp.inner_apply, tensorVec, RCLike.inner_apply,
    map_mul, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

private theorem schmidt {A B : Type*} [Fintype A] [Fintype B]
    (ψ : EuclideanSpace ℂ (A × B)) (hψ : IsState ψ) :
    ∃ (r : ℕ) (lam : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ A)
      (w : Fin r → EuclideanSpace ℂ B),
      Orthonormal ℂ u ∧ Orthonormal ℂ w ∧ (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j ^ 2 = 1 ∧
        ψ = ∑ j, (lam j : ℂ) • tensorVec (u j) (w j) := by
  classical
  let T : EuclideanSpace ℂ A →ₗ[ℂ] EuclideanSpace ℂ B :=
    { toFun := fun x => WithLp.toLp 2 (fun b => ∑ a, ψ (a,b) * x a)
      map_add' := by intro x y; ext b; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intro c x; ext b; simp [Finset.mul_sum, mul_left_comm] }
  let S := T.isSymmetric_adjoint_comp_self
  let e := S.eigenvectorBasis rfl
  let v := fun i => T (e i)
  have hvorth {i j : Fin (Module.finrank ℂ (EuclideanSpace ℂ A))} (hij : i ≠ j) :
      inner ℂ (v i) (v j) = 0 := by
    change inner ℂ (T (e i)) (T (e j)) = 0
    rw [← T.adjoint_inner_right]
    change inner ℂ (e i) ((T.adjoint ∘ₗ T) (e j)) = 0
    rw [S.apply_eigenvectorBasis rfl j, inner_smul_right, e.orthonormal.inner_eq_zero hij,
      mul_zero]
  let c := fun i => WithLp.toLp 2 (fun a => conj (e i a))
  have hc : Orthonormal ℂ c := by
    rw [orthonormal_iff_ite]
    intro i j
    have hh := congrArg conj ((orthonormal_iff_ite.mp e.orthonormal) i j)
    simpa [c, PiLp.inner_apply, map_sum, mul_comm] using hh
  let J := {i : Fin (Module.finrank ℂ (EuclideanSpace ℂ A)) // v i ≠ 0}
  let u : J → EuclideanSpace ℂ A := fun i => c i.val
  let w : J → EuclideanSpace ℂ B := fun i => ((‖v i.val‖⁻¹ : ℝ) : ℂ) • v i.val
  let lam : J → ℝ := fun i => ‖v i.val‖
  have hu : Orthonormal ℂ u := hc.comp Subtype.val Subtype.val_injective
  have hw : Orthonormal ℂ w := by
    constructor
    · intro i
      simp [w, norm_smul, Complex.norm_real,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr i.property)]
    · intro i j hij
      have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp [w, inner_smul_left, inner_smul_right, hvorth hij']
  have hrow (a : A) (b : B) : ψ (a,b) = ∑ i, c i a * v i b := by
    have hh := congrArg (fun x => T x b) (e.sum_repr' (ket a))
    simpa [T, c, v, ket, map_sum, map_smul, PiLp.inner_apply, mul_comm] using hh.symm
  have hweight (i : J) : (lam i : ℂ) • w i = v i.val := by
    have hn : (‖v i.val‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr i.property
    simp only [lam, w, Complex.ofReal_inv, smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hdecomp : ψ = ∑ i : J, (lam i : ℂ) • tensorVec (u i) (w i) := by
    ext p
    rcases p with ⟨a,b⟩
    rw [hrow]
    have hterm (i : J) : c i.val a * v i.val b =
        ((lam i : ℂ) • tensorVec (u i) (w i)) (a,b) := by
      have hh := congrArg (fun x => x b) (hweight i)
      change (lam i : ℂ) * w i b = v i.val b at hh
      change c i.val a * v i.val b = (lam i : ℂ) * (c i.val a * w i b)
      rw [← hh]
      ring
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    simp_rw [← hterm]
    have hh := Fintype.sum_subtype_add_sum_subtype (fun i => v i ≠ 0)
      (fun i => c i a * v i b)
    have hz : (∑ i : {i // ¬ v i ≠ 0}, c i.val a * v i.val b) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [not_not.mp i.property]
    rw [hz, add_zero] at hh
    exact hh.symm
  have htw : Orthonormal ℂ (fun i : J => tensorVec (u i) (w i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [tensor_inner, (orthonormal_iff_ite.mp hu) i j,
      (orthonormal_iff_ite.mp hw) i j]
    split_ifs <;> simp
  have hsum : ∑ i : J, lam i ^ 2 = 1 := by
    have hh := htw.inner_sum (fun i => (lam i : ℂ)) (fun i => (lam i : ℂ)) Finset.univ
    have hh' : (∑ i : J, (lam i : ℂ)^2) = 1 := by
      calc
        _ = inner ℂ ψ ψ := by simpa [hdecomp, pow_two] using hh.symm
        _ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
    exact_mod_cast hh'
  let q := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, lam ∘ q, u ∘ q, w ∘ q, hu.comp q q.injective,
    hw.comp q q.injective, fun i => norm_nonneg _, ?_, ?_⟩
  · change (∑ i, lam (q i) ^ 2) = 1
    rw [q.sum_comp (fun i => lam i ^ 2)]
    exact hsum
  · change ψ = ∑ i, (lam (q i) : ℂ) • tensorVec (u (q i)) (w (q i))
    rw [q.sum_comp (fun i => (lam i : ℂ) • tensorVec (u i) (w i))]
    exact hdecomp

theorem solution {ma mb : ℕ} (ψ : EuclideanSpace ℂ (Qubits ma × Qubits mb))
    (hψ : IsState ψ) :
    ∃ (r : ℕ) (lam : Fin r → ℝ) (φA : Fin r → EuclideanSpace ℂ (Qubits ma))
      (φB : Fin r → EuclideanSpace ℂ (Qubits mb)),
      Orthonormal ℂ φA ∧ Orthonormal ℂ φB ∧ (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j ^ 2 = 1 ∧
        ψ = ∑ j, (lam j : ℂ) • tensorVec (φA j) (φB j) :=
  schmidt ψ hψ
