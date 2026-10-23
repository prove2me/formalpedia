-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P14.rotatedSqueezing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:00:37.834685+00:00
-- url     : https://prove2.me/submissions/31c6bd99-62c3-425a-8155-98750853b739

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
noncomputable section
open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Frontier18.P14

lemma x8_mat (z : ℝ) :
    amplifierDoubled z =
      balancedDoubled.conjTranspose * oppositeSqueezes z * balancedDoubled := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have h2' : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [sq, h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [amplifierDoubled, balancedDoubled, oppositeSqueezes, balanced, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.conjTranspose_apply] <;>
    field_simp <;> (try simp only [h2']) <;> ring

theorem x8_main (theta : ℝ) :
    amplifierDoubled (theta / 2) =
      balancedDoubled.conjTranspose * oppositeSqueezes (theta / 2) * balancedDoubled ∧
    (∀ j : Fin 2,
      let s : ℂ := if j = 0 then 1 else -1
      let a := annihilate 2 j
      let ad := create 2 j
      let ap := (Real.cosh (theta / 2) : ℂ) • a + (s * (Real.sinh (theta / 2) : ℂ)) • ad
      let adp := (Real.cosh (theta / 2) : ℂ) • ad + (s * (Real.sinh (theta / 2) : ℂ)) • a
      quadratureQ ap adp =
        (Real.exp ((if j = 0 then theta else -theta) / 2) : ℂ) • quadratureQ a ad ∧
      quadratureP ap adp =
        (Real.exp ((if j = 0 then -theta else theta) / 2) : ℂ) • quadratureP a ad) := by
  refine ⟨x8_mat _, fun j => ?_⟩
  intro s a ad ap adp
  have hQ : ∀ c d : ℂ, quadratureQ (c • a + d • ad) (c • ad + d • a) =
      (c + d) • quadratureQ a ad := by
    intro c d; unfold quadratureQ; module
  have hP : ∀ c d : ℂ, quadratureP (c • a + d • ad) (c • ad + d • a) =
      (c - d) • quadratureP a ad := by
    intro c d; unfold quadratureP; module
  refine ⟨hQ _ _ |>.trans ?_, hP _ _ |>.trans ?_⟩ <;> congr 1 <;>
    fin_cases j <;> simp [s, Complex.cosh, Complex.sinh] <;> ring_nf

end QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Frontier18.P14 in
theorem solution (theta : ℝ) :
    amplifierDoubled (theta / 2) =
      balancedDoubled.conjTranspose * oppositeSqueezes (theta / 2) * balancedDoubled ∧
    (∀ j : Fin 2,
      let s : ℂ := if j = 0 then 1 else -1
      let a := annihilate 2 j
      let ad := create 2 j
      let ap := (Real.cosh (theta / 2) : ℂ) • a + (s * (Real.sinh (theta / 2) : ℂ)) • ad
      let adp := (Real.cosh (theta / 2) : ℂ) • ad + (s * (Real.sinh (theta / 2) : ℂ)) • a
      quadratureQ ap adp =
        (Real.exp ((if j = 0 then theta else -theta) / 2) : ℂ) • quadratureQ a ad ∧
      quadratureP ap adp =
        (Real.exp ((if j = 0 then -theta else theta) / 2) : ℂ) • quadratureP a ad) :=
  x8_main theta
