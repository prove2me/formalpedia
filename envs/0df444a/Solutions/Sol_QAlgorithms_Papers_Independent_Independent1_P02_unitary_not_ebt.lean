-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.unitary_not_ebt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T17:53:44.727709+00:00
-- url     : https://prove2.me/submissions/ab1d2fb2-59ed-4750-94e9-7a1e4d135247

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P02
open scoped Matrix ComplexOrder ComplexConjugate
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


theorem solution (d : ℕ) (hd : 2 ≤ d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    conjugationEndomorphism U ∉ ebtSet d := by
  rintro ⟨hEB, -⟩
  set Um : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ) with hUm
  have hUU : Um * star Um = 1 := Matrix.mem_unitaryGroup_iff.1 U.2
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  let er : Fin 2 → Fin d → ℂ := fun r j => if (j : ℕ) = (r : ℕ) then 1 else 0
  let ψ : Fin 2 × Fin d → ℂ := fun p => (star Um *ᵥ er p.1) p.2
  let X : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ := (1/2 : ℂ) • Matrix.vecMulVec ψ (star ψ)
  have hφ : ∀ r, Um *ᵥ (fun i => ψ (r, i)) = er r := by
    intro r
    show Um *ᵥ (star Um *ᵥ er r) = er r
    rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hφ' : ∀ r j, ∑ i, Um j i * ψ (r, i) = er r j := by
    intro r j; have := congrFun (hφ r) j; simpa [Matrix.mulVec, dotProduct] using this
  have hnorm : ∀ r, ∑ i, ψ (r, i) * star (ψ (r, i)) = 1 := by
    intro r
    have h1 : ∑ i, ψ (r, i) * star (ψ (r, i)) = star (fun i => ψ (r, i)) ⬝ᵥ (fun i => ψ (r, i)) := by
      simp [dotProduct, mul_comm]
    rw [h1]
    show star (star Um *ᵥ er r) ⬝ᵥ (star Um *ᵥ er r) = 1
    rw [Matrix.star_mulVec, ← Matrix.star_eq_conjTranspose, star_star, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
    rw [dotProduct, Finset.sum_eq_single (⟨r, by omega⟩ : Fin d)]
    · simp [er]
    · intro b _ hb
      have : (b : ℕ) ≠ (r : ℕ) := fun h => hb (Fin.ext h)
      simp [er, this]
    · simp
  have hX : IsDensityMatrix X := by
    refine ⟨(Matrix.posSemidef_vecMulVec_self_star ψ).smul
      (by have h : (0:ℂ) ≤ ((1/2:ℝ):ℂ) := Complex.zero_le_real.2 (by norm_num)
          simpa using h), ?_⟩
    simp only [X, Matrix.trace_smul, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, smul_eq_mul, Matrix.smul_apply, ← Finset.mul_sum, hnorm]
    norm_num
  obtain ⟨q, w, A, B, hw, hAB, hY⟩ := hEB 2 (by norm_num) X hX
  set Y := idTensorSuperop (conjugationEndomorphism U) X with hYdef
  have hYe : ∀ p q, Y p q = (1/2 : ℂ) * er p.1 p.2 * star (er q.1 q.2) := by
    intro p q
    have hY1 : Y p q = (Um * (Matrix.of fun i i' => X (p.1, i) (q.1, i')) * Umᴴ) p.2 q.2 := by
      simp only [hYdef, idTensorSuperop, Matrix.of_apply]
      show (krausApply (fun _ : Fin 1 => (U : Matrix (Fin d) (Fin d) ℂ)) _) p.2 q.2 = _
      simp [krausApply, hUm]
    rw [hY1, ← hφ' p.1 p.2, ← hφ' q.1 q.2]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [X, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]; ring
  let M := Entanglement.partialTransposeFirst Y
  have hMpsd : M.PosSemidef := by
    have : M = ∑ j, (w j : ℂ) • Matrix.kronecker (A j)ᵀ (B j) := by
      ext p q
      simp only [M, Entanglement.partialTransposeFirst, Matrix.of_apply]
      rw [hY]
      simp [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
    rw [this]
    refine Matrix.posSemidef_sum _ (fun j _ => ?_)
    exact (((hAB j).1.1.transpose).kronecker (hAB j).2.1).smul (by exact_mod_cast hw j)
  let v : Fin 2 × Fin d → ℂ := Pi.single (0, i1) 1 - Pi.single (1, i0) 1
  have key := hMpsd.dotProduct_mulVec_nonneg v
  have hval : star v ⬝ᵥ (M *ᵥ v) = -1 := by
    simp only [v, star_sub, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, Pi.star_single, star_one,
      Matrix.mulVec_single, single_dotProduct, mul_one, one_mul]
    simp only [M, Entanglement.partialTransposeFirst, Matrix.of_apply, hYe]
    simp [er, i0, i1]
    norm_num
  rw [hval] at key
  norm_num at key

end
