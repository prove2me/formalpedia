-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P17.adComposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:11:51.961407+00:00
-- url     : https://prove2.me/submissions/2d1450a3-1c4a-45dc-81a3-7a5947560078

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq


lemma g73h_ad_formula (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    adChannel eta X = !![X 0 0 + (1-eta) * X 1 1, (Real.sqrt eta : ℂ) * X 0 1;
      (Real.sqrt eta : ℂ) * X 1 0, eta * X 1 1] := by
  have c1 : ((Real.sqrt eta : ℂ)) * (Real.sqrt eta : ℂ) = eta := by
    exact_mod_cast Real.mul_self_sqrt h0
  have c3 : ((Real.sqrt (1-eta) : ℂ)) * (Real.sqrt (1-eta) : ℂ) = 1-eta := by
    exact_mod_cast Real.mul_self_sqrt (by linarith)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [adChannel, QAlgorithms.krausApply, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, adKraus, Fin.isValue] <;>
    simp [Complex.conj_ofReal] <;> ring_nf <;> simp only [sq, c1, c3] <;> ring

/-- PDF p.3: concatenation equality is on all operators, including its linear
extension to inputs entangled with an arbitrary retained reference. -/
theorem solution (eta eta2 : ℝ) (h1 : eta ∈ Set.Icc (0 : ℝ) 1)
    (h2 : eta2 ∈ Set.Icc (0 : ℝ) 1) :
    adChannel eta ∘ adChannel eta2 = adChannel (eta*eta2) := by
  funext X
  have hs6 : Real.sqrt (eta*eta2) = Real.sqrt eta * Real.sqrt eta2 := Real.sqrt_mul h1.1 _
  have c6 : ((Real.sqrt (eta*eta2) : ℂ)) = (Real.sqrt eta : ℂ) * (Real.sqrt eta2 : ℂ) := by
    exact_mod_cast hs6
  have c1 : ((Real.sqrt eta : ℂ)) * (Real.sqrt eta : ℂ) = eta := by
    exact_mod_cast Real.mul_self_sqrt h1.1
  have c2 : ((Real.sqrt eta2 : ℂ)) * (Real.sqrt eta2 : ℂ) = eta2 := by
    exact_mod_cast Real.mul_self_sqrt h2.1
  simp only [Function.comp_apply]
  rw [g73h_ad_formula eta2 h2.1 h2.2, g73h_ad_formula eta h1.1 h1.2,
    g73h_ad_formula (eta*eta2) (mul_nonneg h1.1 h2.1) (by nlinarith [h1.1, h1.2, h2.1, h2.2])]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c6] <;> ring_nf



end
