-- Prove2me | solution 1 for PI.QnHermHaar.relCov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:16:31.008092+00:00
-- url     : https://prove2.me/submissions/857232c5-65c4-4093-8ede-7fea4fb472fb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (Y Yb : Fin m → A) (Hm P Q : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ)
    (hYb : ∀ c, Yb c = ∑ l, Hm l c • star (Y l)) (hQ : ∀ i j, star (Q i j) = P j i)
    (hHP : ∀ k b, ∑ j, Hm k j * P j b = P k b * ((ε b : ℤ) : ℂ)) (c : Fin m) :
    covC P Yb c = ((ε c : ℤ) : ℂ) • star (vecC Q Y c) := by
  simp only [covC, vecC, hYb, star_sum, star_smul, hQ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  rw [Finset.sum_congr rfl (fun j _ => mul_comm (P j c) (Hm k j)), hHP k c]
  ring
end PI.QnHermHaar
