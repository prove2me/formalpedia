-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SecDegreeGe_eval_specRest_2d6681cf764e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:38.806898+00:00
-- url     : https://prove2.me/submissions/56cfd4e2-d21f-4e48-b538-e3e844eac68a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecFiniteUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowFormHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecDegreeGe

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
open GroundTheory.Heights₂.Heights.SecDegreeGe
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.SecDegreeGe
theorem _root_.solution (ψ : k →+* R) (f : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R) (v : Fin n → R) :
    eval v (Vertical.specRest ψ f y) =
      eval₂ ψ (fun ij => Fin.cases (motive := fun _ => R) (v ij.2)
        (fun i => y (.inl (i, ij.2))) ij.1) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Vertical.specRest]
  | add p q hp hq => simp only [Vertical.specRest] at hp hq ⊢; simp [hp, hq]
  | mul_X p ij hp =>
    simp only [Vertical.specRest] at hp ⊢
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases with
    | zero => simp [hp]
    | succ i => simp [hp]
end GroundTheory.Heights₂.Heights.SecDegreeGe
