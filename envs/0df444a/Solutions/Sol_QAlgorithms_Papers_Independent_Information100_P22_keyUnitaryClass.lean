-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.keyUnitaryClass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:22:36.253449+00:00
-- url     : https://prove2.me/submissions/502e9b1c-2f29-47f3-a26f-d729b3043c9c

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma X7KU_main {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (R : EuclideanSpace ℂ (S × S))
    (hmax : traceRight (pureDensity R) = (Fintype.card S : ℂ)⁻¹ • (1 : Matrix S S ℂ)) :
    ∃ V : Matrix.unitaryGroup S ℂ,
      R = act (Matrix.kronecker (1 : Matrix S S ℂ) (V : Matrix S S ℂ)) (bell S) := by
  set D : ℝ := (Fintype.card S : ℝ) with hD
  have hDpos : 0 < D := by rw [hD]; exact_mod_cast Fintype.card_pos
  set c : ℂ := ((Real.sqrt D : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast (Real.sqrt_pos.2 hDpos).ne'
  have hcc : c * conj c = (Fintype.card S : ℂ) := by
    rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hDpos.le, hD]
    push_cast; rfl
  let M : Matrix S S ℂ := Matrix.of fun s n => R (s, n)
  let W : Matrix S S ℂ := c • M
  have hW : W * star W = 1 := by
    ext s s'
    have h := congrFun (congrFun hmax s) s'
    simp only [traceRight, pureDensity, Matrix.of_apply] at h
    simp only [W, M, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, smul_eq_mul, Complex.star_def]
    have : ∑ x, c * R (s, x) * (conj c * conj (R (s', x))) =
        (c * conj c) * ∑ x, R (s, x) * conj (R (s', x)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => by ring)
    rw [this, h, hcc, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]
  have hWu : W ∈ Matrix.unitaryGroup S ℂ := Matrix.mem_unitaryGroup_iff.2 hW
  have hW' : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.1 hWu
  have hV : Wᵀ ∈ Matrix.unitaryGroup S ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have : star Wᵀ = (star W)ᵀ := by
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose, Matrix.transpose_map]
    rw [this, ← Matrix.transpose_mul, hW', Matrix.transpose_one]
  refine ⟨⟨Wᵀ, hV⟩, ?_⟩
  ext ⟨s, n⟩
  simp only [act, bell, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    WithLp.ofLp_toLp]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
  · rw [Finset.sum_eq_single s]
    · simp only [Matrix.one_apply_eq, one_mul, if_pos rfl, W, M, Matrix.transpose_apply,
        Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [if_pos trivial, mul_comm c, mul_assoc]
      have : c * ((Real.sqrt (Fintype.card S : ℝ))⁻¹ : ℂ) = 1 := by
        rw [hc, hD]; push_cast
        exact mul_inv_cancel₀ (by rw [← hD]; exact_mod_cast (Real.sqrt_pos.2 hDpos).ne')
      rw [this, mul_one]
    · intro b _ hb
      simp only [Matrix.one_apply_eq, one_mul]
      rw [if_neg (Ne.symm hb), mul_zero]
    · simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro x _
    rw [Matrix.one_apply_ne (Ne.symm hb)]; simp
  · simp

end

end QAlgorithms.Papers.Independent.Information100.P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

end

end QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 in
theorem solution (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R)
    (hmax : rhoS R = mixed (Signals m k)) :
    ∃ V : Matrix.unitaryGroup (Signals m k) ℂ,
      R = act (Matrix.kronecker (1 : Op (Signals m k)) (V : Op _)) (bell (Signals m k)) :=
  X7KU_main R hmax

end
