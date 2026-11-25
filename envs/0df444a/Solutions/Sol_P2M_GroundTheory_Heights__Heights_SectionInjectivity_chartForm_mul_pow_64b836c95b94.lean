-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionInjectivity_chartForm_mul_pow_64b836c95b94
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:15:18.813632+00:00
-- url     : https://prove2.me/submissions/4e6774b5-9a0b-4b0e-bf11-f9ee3647fe60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroMore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.SectionInjectivity
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.SectionInjectivity
theorem _root_.solution {P : ArithVariety n} {num₁ den₁ num₂ den₂ : MvPolynomial (Coord n) ℤ}
    {c : (k : ι) → Fin (n k + 1)} {d₁ d₂ : ι → ℕ} {f₁ f₂ : MvPolynomial (Coord n) ℤ} (t : ℕ)
    (h₁ : den₁ * f₁ - num₁ * chartMonomial c d₁ ∈ P.ideal)
    (h₂ : den₂ * f₂ - num₂ * chartMonomial c d₂ ∈ P.ideal) :
    den₁ * den₂ ^ t * (f₁ * f₂ ^ t) - num₁ * num₂ ^ t * chartMonomial c (d₁ + t • d₂) ∈ P.ideal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h₁ h₂ ⊢
  rw [chartMonomial_add, chartMonomial_nsmul]
  simp only [map_mul, map_pow] at h₁ h₂ ⊢
  calc _ = (Ideal.Quotient.mk P.ideal den₁ * Ideal.Quotient.mk P.ideal f₁) *
        (Ideal.Quotient.mk P.ideal den₂ * Ideal.Quotient.mk P.ideal f₂) ^ t := by ring
    _ = _ := by rw [h₁, h₂]; ring
end GroundTheory.Heights₂.Heights.SectionInjectivity
