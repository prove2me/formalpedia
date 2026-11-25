-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SecDegreeGe_map_eval_specRest_c1db2bdd1d7e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:09.629333+00:00
-- url     : https://prove2.me/submissions/97f98639-1b5f-49ab-bca7-99bfdd6c8330

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecDegreeGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecFiniteUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowFormHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecDegreeGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SecDegreeGe_eval_specRest_2d6681cf764e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_eval_specRest_c1d6a2947cb7


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
theorem _root_.solution (ψ : k →+* R) (φ : R →+* S) (f : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R) :
    φ (eval (fun j => y (.inr j)) (Vertical.specRest ψ f y)) =
      eval (fun j => φ (y (.inr j))) (Vertical.specRest (φ.comp ψ) f (φ ∘ y)) := by
  rw [eval_specRest, eval_specRest, MvPolynomial.eval₂_comp_left]
  congr 1
  funext ⟨i, j⟩
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl
end GroundTheory.Heights₂.Heights.SecDegreeGe
