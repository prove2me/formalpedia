-- Prove2me | solution 1 for ThornStringBits.cycLaplacian_eigenvalue_is_fourier
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T20:10:20.697644+00:00
-- url     : https://prove2.me/submissions/f6567eab-2860-4f53-b6c6-3332a27c4337

import Mathlib
import Definitions.Def_ThornStringBits_Defs

set_option autoImplicit false

namespace F10d1548

open Real Matrix ThornStringBits

lemma pow_mod_of_pow_eq_one {z : ℂ} {N : ℕ} (hz : z ^ N = 1) (m : ℕ) :
    z ^ (m % N) = z ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m N, pow_add, pow_mul, hz, one_pow, one_mul]

lemma cycL_form (n : ℕ) (i j : Fin (n + 1)) :
    cycLaplacian (n + 1) i j =
      (if i = j then 2 else 0) - (if j = finRotate (n + 1) i then 1 else 0)
        - (if i = finRotate (n + 1) j then 1 else 0) := by
  have hs : ∀ i : Fin (n + 1), ((finRotate (n + 1) i : Fin (n + 1)) : ℕ) = (i.val + 1) % (n + 1) := by
    intro i
    rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  unfold cycLaplacian
  have c1 : (j.val = (i.val + 1) % (n + 1)) ↔ j = finRotate (n + 1) i := by
    rw [Fin.ext_iff, hs]
  have c2 : (i.val = (j.val + 1) % (n + 1)) ↔ i = finRotate (n + 1) j := by
    rw [Fin.ext_iff, hs]
  simp only [c1, c2]

lemma rot_pow (n : ℕ) {z : ℂ} (hz : z ^ (n + 1) = 1) (j : Fin (n + 1)) :
    z ^ ((finRotate (n + 1) j : Fin (n + 1)) : ℕ) = z * z ^ (j : ℕ) := by
  rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod, pow_mod_of_pow_eq_one hz]
  ring

lemma col_sum (n : ℕ) {z : ℂ} (hz : z ^ (n + 1) = 1) (j : Fin (n + 1)) :
    ∑ i, ((cycLaplacian (n + 1) i j : ℝ) : ℂ) * z ^ (i : ℕ)
      = (2 - z - z⁻¹) * z ^ (j : ℕ) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  set e := finRotate (n + 1)
  have h1 : ∑ i : Fin (n + 1), ((if i = j then (2:ℝ) else 0 : ℝ) : ℂ) * z ^ (i : ℕ)
      = 2 * z ^ (j : ℕ) := by
    simp [apply_ite (fun x : ℝ => (x : ℂ)), ite_mul]
  have h2 : ∑ i : Fin (n + 1), ((if j = e i then (1:ℝ) else 0 : ℝ) : ℂ) * z ^ (i : ℕ)
      = z ^ ((e.symm j : Fin (n + 1)) : ℕ) := by
    have : ∀ i, (j = e i) ↔ (e.symm j = i) := fun i => by
      rw [Equiv.symm_apply_eq]
    simp [apply_ite (fun x : ℝ => (x : ℂ)), ite_mul, this]
  have h3 : ∑ i : Fin (n + 1), ((if i = e j then (1:ℝ) else 0 : ℝ) : ℂ) * z ^ (i : ℕ)
      = z ^ ((e j : Fin (n + 1)) : ℕ) := by
    simp [apply_ite (fun x : ℝ => (x : ℂ)), ite_mul]
  have hsym : z * z ^ ((e.symm j : Fin (n + 1)) : ℕ) = z ^ (j : ℕ) := by
    rw [← rot_pow n hz (e.symm j)]
    simp [e]
  have hsym' : z ^ ((e.symm j : Fin (n + 1)) : ℕ) = z⁻¹ * z ^ (j : ℕ) := by
    rw [← hsym, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
  simp only [cycL_form, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
  rw [h1, h2, h3, hsym', rot_pow n hz j]
  ring

theorem main (M : ℕ) (μ : ℝ)
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (cycLaplacian M)) μ) :
    ∃ k : ℕ, k < M ∧ μ = 4 * Real.sin (π * k / M) ^ 2 := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hLv : cycLaplacian M *ᵥ v = μ • v := by
    have := Module.End.mem_eigenspace_iff.mp hv.1
    simpa [Matrix.toLin'_apply] using this
  cases M with
  | zero =>
    exact absurd (Subsingleton.elim v 0) hv0
  | succ n =>
    set ζ : ℂ := Complex.exp (2 * π * Complex.I / ((n + 1 : ℕ) : ℂ)) with hζ
    have hprim : IsPrimitiveRoot ζ (n + 1) := Complex.isPrimitiveRoot_exp (n + 1) (by omega)
    -- the complexified eigenvector
    set u : Fin (n + 1) → ℂ := fun j => (v j : ℂ) with hu
    have hu0 : u ≠ 0 := by
      intro h
      apply hv0
      funext j
      have := congrFun h j
      simpa [hu] using this
    set x : Fin (n + 1) → ℂ := fun j => ζ ^ (j : ℕ) with hx
    have hxinj : Function.Injective x := by
      intro a b hab
      exact Fin.ext (hprim.pow_inj a.isLt b.isLt hab)
    have hdet : (Matrix.vandermonde x).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hxinj
    have hex : ∃ k : Fin (n + 1), (u ᵥ* Matrix.vandermonde x) k ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hu0 (Matrix.eq_zero_of_vecMul_eq_zero hdet (funext hcon))
    obtain ⟨k, hk⟩ := hex
    set z : ℂ := ζ ^ (k : ℕ) with hzdef
    have hz : z ^ (n + 1) = 1 := by
      rw [hzdef, ← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    set w : ℂ := ∑ i, u i * z ^ (i : ℕ) with hw
    have hwk : w = (u ᵥ* Matrix.vandermonde x) k := by
      simp only [hw, Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, hx, hzdef]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← pow_mul, ← pow_mul]
      ring
    have hw0 : w ≠ 0 := hwk ▸ hk
    have hrow : ∀ i, ∑ j, cycLaplacian (n + 1) i j * v j = μ * v i := by
      intro i
      have := congrFun hLv i
      simpa [Matrix.mulVec, dotProduct] using this
    have key : (μ : ℂ) * w = (2 - z - z⁻¹) * w := by
      calc (μ : ℂ) * w = ∑ i, ((μ * v i : ℝ) : ℂ) * z ^ (i : ℕ) := by
              rw [hw, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              simp [hu]; ring
        _ = ∑ i, ((∑ j, cycLaplacian (n + 1) i j * v j : ℝ) : ℂ) * z ^ (i : ℕ) := by
              simp only [hrow]
        _ = ∑ i, ∑ j, (v j : ℂ) * (((cycLaplacian (n + 1) i j : ℝ) : ℂ) * z ^ (i : ℕ)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Complex.ofReal_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              push_cast; ring
        _ = ∑ j, (v j : ℂ) * ∑ i, ((cycLaplacian (n + 1) i j : ℝ) : ℂ) * z ^ (i : ℕ) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
        _ = ∑ j, (v j : ℂ) * ((2 - z - z⁻¹) * z ^ (j : ℕ)) := by
              simp only [col_sum n hz]
        _ = (2 - z - z⁻¹) * w := by
              rw [hw, Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              simp [hu]; ring
    have hμc : (μ : ℂ) = 2 - z - z⁻¹ := mul_right_cancel₀ hw0 key
    refine ⟨k, k.isLt, ?_⟩
    -- evaluate z + z⁻¹
    set θ : ℝ := 2 * π * (k : ℕ) / ((n + 1 : ℕ) : ℝ) with hθ
    have hzexp : z = Complex.exp (θ * Complex.I) := by
      rw [hzdef, hζ, ← Complex.exp_nat_mul, hθ]
      congr 1
      push_cast
      ring
    have hzinv : z⁻¹ = Complex.exp (-(θ * Complex.I)) := by
      rw [hzexp, Complex.exp_neg]
    have hsum : z + z⁻¹ = ((2 * Real.cos θ : ℝ) : ℂ) := by
      rw [hzinv, hzexp]
      push_cast
      rw [Complex.cos]
      ring_nf
    have hμr : μ = 2 - 2 * Real.cos θ := by
      have : (μ : ℂ) = ((2 - 2 * Real.cos θ : ℝ) : ℂ) := by
        rw [hμc]
        have : (2 : ℂ) - z - z⁻¹ = 2 - (z + z⁻¹) := by ring
        rw [this, hsum]
        push_cast; ring
      exact_mod_cast this
    have hθ2 : θ = 2 * (π * ((k : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
      rw [hθ]; ring
    rw [hμr, hθ2, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq (π * ((k : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
    linarith

end F10d1548

open Real Matrix ThornStringBits in
theorem solution (M : ℕ) (μ : ℝ)
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (cycLaplacian M)) μ) :
    ∃ k : ℕ, k < M ∧ μ = 4 * Real.sin (π * k / M) ^ 2 := by
  exact F10d1548.main M μ hμ
