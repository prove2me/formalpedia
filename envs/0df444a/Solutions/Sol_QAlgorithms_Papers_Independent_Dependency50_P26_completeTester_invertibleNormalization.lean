-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.completeTester_invertibleNormalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:11:32.212076+00:00
-- url     : https://prove2.me/submissions/69c0f568-a340-4481-9cee-36bbd1813df2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

theorem S173C_main (s : Signature) (n k : ℕ)
    (P : Fin k → Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ)
    (hP : CombTester s (n+1) k P) (hic : InformationallyComplete P)
    (T : Matrix (Fin (s.input n) × Basis s n) _ ℂ)
    (hsum : (∑ i, P i) = Matrix.kronecker (1 : Matrix (Fin (s.output n)) _ ℂ) T) :
    IsUnit T := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let o0 : Fin (s.output n) := ⟨0, s.output_pos n⟩
  let w : Basis s (n+1) → ℂ := fun z =>
    if (z : Fin (s.output n) × (Fin (s.input n) × Basis s n)).1 = o0 then
      v (z : Fin (s.output n) × (Fin (s.input n) × Basis s n)).2 else 0
  have hw0 : w ≠ 0 := by
    intro h
    apply hv0
    funext x
    have := congrFun h ((o0, x) : Fin (s.output n) × (Fin (s.input n) × Basis s n))
    simp only [w, if_true] at this
    exact this
  have hkw : (Matrix.kronecker (1 : Matrix (Fin (s.output n)) _ ℂ) T) *ᵥ w = 0 := by
    funext z
    obtain ⟨o', x'⟩ := (z : Fin (s.output n) × (Fin (s.input n) × Basis s n))
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    change ∑ y : Fin (s.output n) × (Fin (s.input n) × Basis s n),
      Matrix.kronecker (1 : Matrix (Fin (s.output n)) _ ℂ) T (o', x') y * w y = 0
    rw [Fintype.sum_prod_type]
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, w]
    rw [Finset.sum_eq_single o']
    · by_cases h : o' = o0
      · simp only [if_true, one_mul, h]
        have := congrFun hv x'
        simpa [Matrix.mulVec, dotProduct] using this
      · simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have hPw : ∀ i, P i *ᵥ w = 0 := by
    have hs : ∑ i, star w ⬝ᵥ (P i *ᵥ w) = 0 := by
      rw [← dotProduct_sum]
      have : ∑ i, P i *ᵥ w = (∑ i, P i) *ᵥ w := by
        rw [Matrix.sum_mulVec]
      have hkw' : (∑ i, P i) *ᵥ w = 0 := by rw [hsum]; exact hkw
      rw [this, hkw', dotProduct_zero]
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ star w ⬝ᵥ (P i *ᵥ w) := fun i _ => (hP.2.2.1 i).dotProduct_mulVec_nonneg w
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hs i (Finset.mem_univ i)
    exact ((hP.2.2.1 i).dotProduct_mulVec_zero_iff w).mp this
  have hPt : ∀ i, (P i).transpose *ᵥ star w = 0 := by
    intro i
    have hh := (hP.2.2.1 i).1
    funext a
    have := congrFun (hPw i) a
    have e : ((P i).transpose *ᵥ star w) a = star ((P i *ᵥ w) a) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.star_apply, star_sum,
        star_mul']
      refine Finset.sum_congr rfl fun b _ => ?_
      have := congrFun (congrFun hh.eq a) b
      simp only [Matrix.conjTranspose_apply] at this
      rw [← this, star_star, mul_comm]
    rw [e, this]; simp

  obtain ⟨c, hc⟩ := hic 1
  have : star w = 0 := by
    have h1 : (1 : Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ) *ᵥ star w = 0 := by
      rw [hc, Matrix.sum_mulVec]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Matrix.smul_mulVec, hPt i, smul_zero]
    rwa [Matrix.one_mulVec] at h1
  exact hw0 (by simpa using this)

end QAlgorithms.Papers.Independent.Dependency50.P26

open QAlgorithms.Papers.Independent.Dependency50.P26 in
theorem solution (s : Signature) (n k : ℕ)
    (P : Fin k → Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ)
    (hP : CombTester s (n+1) k P) (hic : InformationallyComplete P)
    (T : Matrix (Fin (s.input n) × Basis s n) _ ℂ)
    (hT : ThetaNormalized s n T)
    (hsum : (∑ i, P i) = Matrix.kronecker (1 : Matrix (Fin (s.output n)) _ ℂ) T) :
    IsUnit T := S173C_main s n k P hP hic T hsum
