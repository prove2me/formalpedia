-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.one_bit_teleportation
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T04:08:03.312063+00:00
-- url     : https://prove2.me/submissions/b31e7771-6776-476d-8c15-a9209835b29f

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P21
namespace QAlgorithms.Papers.Independent.Intakenext100.P52

private theorem act_inner_unitary {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (x y : Vec I) :
    inner ℂ (act U x) (act U y) = inner ℂ x y := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, act]
  rw [dotProduct_comm (U.mulVec (WithLp.ofLp y)), dotProduct_comm (WithLp.ofLp y)]
  change star (U.mulVec (WithLp.ofLp x)) ⬝ᵥ (U.mulVec (WithLp.ofLp y)) = _
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have h : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff'.mp hU)
  rw [h, Matrix.vecMul_one]

private theorem act_norm_unitary {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (x : Vec I) :
    ‖act U x‖ = ‖x‖ := by
  exact (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin U)).mpr
    (act_inner_unitary U hU) x

private theorem pauliByproduct_unitary (x z : Bool) :
    pauliByproduct x z ∈ Matrix.unitaryGroup Bool ℂ := by
  cases x <;> cases z <;> apply Matrix.mem_unitaryGroup_iff.mpr <;>
    ext i j <;> cases i <;> cases j <;>
    norm_num [pauliByproduct, pauliX, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

private theorem sum_bits_succ (n : ℕ) (f : Qubits (n+1) → ℂ) :
    (∑ z, f z) = ∑ a : Bool, ∑ s : Qubits n, f (Fin.cons a s) := by
  calc
    _ = ∑ p : Bool × Qubits n, f (Fin.cons p.1 p.2) :=
      Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).symm f
        (fun p => f (Fin.cons p.1 p.2)) (fun z => by simp [Fin.consEquiv])
    _ = _ := Fintype.sum_prod_type _

private theorem hadamard_unitary : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext a b
  cases a <;> cases b <;>
    norm_num [hadamard, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fintype.sum_bool, Complex.ofReal_inv, ← pow_two, inv_pow, h2]

private theorem phaseGate_unitary (theta : ℝ) : phaseGate theta ∈ Matrix.unitaryGroup Bool ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext a b
  cases a <;> cases b <;>
    simp [phaseGate, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fintype.sum_bool, ← Complex.exp_conj, ← Complex.exp_add]

private theorem wGate_unitary (theta : ℝ) : wGate theta ∈ Matrix.unitaryGroup Bool ℂ :=
  (Matrix.unitaryGroup Bool ℂ).mul_mem hadamard_unitary (phaseGate_unitary theta)
end QAlgorithms.Papers.Independent.Intakenext100.P52
private theorem cons_two {n : ℕ} (a : Bool) (s : Qubits (n+2)) :
    @Fin.cons (n+2) (fun _ => Bool) a s (2 : Fin (n+3)) = s 1 := by
  change @Fin.cons (n+2) (fun _ => Bool) a s (Fin.succ (1 : Fin (n+2))) = s 1
  exact Fin.cons_succ _ _ _
private theorem cons_mk_two (a : Bool) (s : Qubits 2) (h : 2 < 3) :
    @Fin.cons 2 (fun _ => Bool) a s ⟨2,h⟩ = s 1 := by
  change @Fin.cons 2 (fun _ => Bool) a s (Fin.succ (1 : Fin 2)) = s 1
  exact Fin.cons_succ _ _ _

open QAlgorithms.Papers.Independent.Intakenext100.P52
noncomputable section

open scoped Matrix ComplexConjugate



open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Figures 6–7, PDF pp.9–10: negative angle and branch normalization retained.
The two X-measurement chain is included in source Pauli order X^(s2) Z^(s1). -/
theorem solution (psi : Vec Bool) (hpsi : IsState psi) :
    (∀ theta : ℝ, ∀ s : Bool,
      let b := lineBranch 1 (fun _ => theta) (fun _ => s) psi
      b = ((Real.sqrt 2)⁻¹ : ℂ) • act (pauliX ^ s.toNat * wGate (-theta)) psi ∧
      ‖b‖ ^ 2 = (1 / 2 : ℝ)) ∧
    (∀ s : Bool, lineBranch 1 (fun _ => 0) (fun _ => s) psi =
      ((Real.sqrt 2)⁻¹ : ℂ) • act (pauliX ^ s.toNat * hadamard) psi) ∧
    (∀ s : Fin 2 → Bool, lineBranch 2 (fun _ => 0) s psi =
      (1 / 2 : ℂ) • act (pauliByproduct (s 1) (s 0)) psi) := by
  have hb (theta : ℝ) (s : Bool) :
      lineBranch 1 (fun _ => theta) (fun _ => s) psi =
        ((Real.sqrt 2)⁻¹ : ℂ) • act (pauliX ^ s.toNat * wGate (-theta)) psi := by
    ext b
    cases s <;> cases b <;>
      norm_num [lineBranch, sum_bits_succ, Fintype.sum_bool, Fintype.sum_unique,
        Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Fin.prod_univ_succ, Fin.prod_univ_zero, czPhase, equatorial, act, wGate,
        phaseGate, hadamard, pauliX, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        ← Complex.exp_conj] <;> simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ] <;> ring
  have htwo (s : Fin 2 → Bool) : lineBranch 2 (fun _ => 0) s psi =
      (1 / 2 : ℂ) • act (pauliByproduct (s 1) (s 0)) psi := by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    ext b
    have he : s = ![s 0,s 1] := by ext i; fin_cases i <;> rfl
    rw [he]
    generalize s 0 = c; generalize s 1 = d
    cases c <;> cases d <;> cases b <;>
      norm_num [lineBranch, sum_bits_succ, Fintype.sum_bool, Fintype.sum_unique,
        cons_mk_two, cons_two, Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Fin.prod_univ_succ, Fin.prod_univ_zero, czPhase, equatorial, act,
        pauliByproduct, pauliX, pauliZ, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Complex.ofReal_inv, ← pow_two, inv_pow, h2] <;> simp only [cons_mk_two, cons_two, Fin.cons_zero, Fin.cons_one, Fin.cons_succ] <;> ring
  have hn : ‖((Real.sqrt 2)⁻¹ : ℂ)‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (by norm_num)]
    norm_num
  have hX : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
    simpa [pauliByproduct] using pauliByproduct_unitary true false
  refine ⟨?_, ?_, htwo⟩
  · intro theta s
    dsimp only
    refine ⟨hb theta s, ?_⟩
    have hU := (Matrix.unitaryGroup Bool ℂ).mul_mem
      ((Matrix.unitaryGroup Bool ℂ).pow_mem hX s.toNat) (wGate_unitary (-theta))
    rw [hb, norm_smul, act_norm_unitary _ hU, show ‖psi‖ = 1 from hpsi, mul_one]
    exact hn
  · intro s
    have hz : phaseGate 0 = 1 := by ext a b; simp [phaseGate]
    simpa [wGate, hz] using hb 0 s