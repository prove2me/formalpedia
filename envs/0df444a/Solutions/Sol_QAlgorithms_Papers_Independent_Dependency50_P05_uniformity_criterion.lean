-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P05.uniformity_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:28:43.407762+00:00
-- url     : https://prove2.me/submissions/ed7705c9-9787-4f13-a78f-4bbbb1d48fcb

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace X6P05U

open QAlgorithms.Papers.Independent.Dependency50.P05

lemma jB_eq {A B : System} (T : Supermap A B) : jB T = T 1 := by
  ext p q
  have h1 : (1 : Matrix (ChoiRegister A) (ChoiRegister A) ℂ) =
      ∑ a : ChoiRegister A, Matrix.single a a 1 := by
    ext x y
    rw [Matrix.sum_apply, Finset.sum_eq_single x (fun b _ hb => by simp [Matrix.single_apply, hb])
      (by simp)]
    simp [Matrix.single_apply, Matrix.one_apply]
  rw [h1, map_sum]
  simp only [jB, QAlgorithms.traceLeft, Matrix.of_apply, superChoi, Matrix.sum_apply]

lemma uniform_eq (A : System) :
    uniformChannel A = ((A.output : ℂ))⁻¹ • (1 : Matrix (ChoiRegister A) (ChoiRegister A) ℂ) := by
  unfold uniformChannel uniformDensity
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  show (1 : Matrix (In A) (In A) ℂ) a c * (((Fintype.card (Out A) : ℂ))⁻¹ • (1 : Matrix (Out A) (Out A) ℂ)) b d = _
  simp only [Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul, Fintype.card_fin]
  split_ifs <;> simp_all

end X6P05U

open QAlgorithms.Papers.Independent.Dependency50.P05 X6P05U in
theorem solution {A B : System} (hin : A.input = B.input)
    (hout : A.output = B.output) (T : Supermap A B) (hT : IsSuperchannel T) :
    PreservesUniformity T ↔ jB T = 1 := by
  unfold PreservesUniformity
  have hc' : ((A.output : ℂ))⁻¹ = ((B.output : ℂ))⁻¹ := by rw [hout]
  rw [jB_eq, uniform_eq, uniform_eq, map_smul, hc']
  have hc : ((B.output : ℂ))⁻¹ ≠ 0 := by
    have : (B.output : ℂ) ≠ 0 := by exact_mod_cast B.output_pos.ne'
    exact inv_ne_zero this
  constructor
  · intro h; exact smul_right_injective _ hc h
  · intro h; rw [h]
