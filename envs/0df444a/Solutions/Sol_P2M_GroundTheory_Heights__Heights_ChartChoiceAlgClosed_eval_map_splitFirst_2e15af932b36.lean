-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_eval_map_splitFirst_2e15af932b36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:43.418662+00:00
-- url     : https://prove2.me/submissions/5072d26d-ee85-45da-8c34-9c7d8699d9f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartChoiceAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartChoiceAlgClosed

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
open GroundTheory.Heights₂.Heights.ChartChoiceAlgClosed
variable {F : Type} [Field F] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartChoiceAlgClosed
theorem _root_.solution (J : Ideal (MvPolynomial (Fin e × Fin n) F)) (t : Fin n → F)
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    eval (fun m => Ideal.Quotient.mk J (C (t m))) (map (Ideal.Quotient.mk J) (splitFirst F e n f)) =
      Ideal.Quotient.mk J (specFirst f t) := by
  rw [eval_map]
  have h : (eval₂Hom (Ideal.Quotient.mk J) (fun m => Ideal.Quotient.mk J (C (t m)))).comp
      (splitFirst F e n).toRingHom = (Ideal.Quotient.mk J).comp (bind₁ (specFirstVar t)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [splitFirst, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, m⟩
      induction i using Fin.cases <;> simp [splitFirst, specFirstVar]
  exact RingHom.congr_fun h f
end GroundTheory.Heights₂.Heights.ChartChoiceAlgClosed
