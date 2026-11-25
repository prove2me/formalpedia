-- Prove2me | solution 1 for PI.QnHermHaar.starConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:19:14.818597+00:00
-- url     : https://prove2.me/submissions/5b1de8d5-f5f1-43c5-8712-a54d750d2518

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
import Theorems.Thm_PI_QnHermHaar_sum_four_comm_version
import Theorems.Thm_PI_QnHermHaar_intCastMul


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
    (E : Fin m → Fin m → A) (Hm P Q : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ)
    (hstar : ∀ a b, star (E a b) = ∑ c, ∑ d, (Hm c b * Hm a d) • E c d)
    (hP : ∀ i j, star (P i j) = Q j i) (hQ : ∀ i j, star (Q i j) = P j i)
    (hHP : ∀ k b, ∑ j, Hm k j * P j b = P k b * ((ε b : ℤ) : ℂ))
    (hQH : ∀ a l, ∑ i, Q a i * Hm i l = ((ε a : ℤ) : ℂ) * Q a l) (a b : Fin m) :
    star (Econj E P Q a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * Econj E P Q b a := by
  simp only [Econj, star_sum, star_smul, hstar, Finset.smul_sum, smul_smul, star_mul', hP, hQ]
  rw [sum_four_comm_version]
  simp only [← Finset.sum_smul, intCastMul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  congr 1
  have h1 : ∑ i, ∑ j, Q a i * P j b * (Hm k j * Hm i l) = (∑ i, Q a i * Hm i l) * (∑ j, Hm k j * P j b) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  rw [h1, hQH, hHP]
  push_cast
  ring
end PI.QnHermHaar
