-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isFiniteProjection_point_aeed13c83c28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:38.384327+00:00
-- url     : https://prove2.me/submissions/08b14b53-c199-489b-887b-d0086af18a3a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mk_ker_eval_eq_7d4f06cbd06a

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (p : Fin n → ℂ) (A : Matrix (Fin 0) (Fin n) ℂ) :
    IsFiniteProjection (RingHom.ker (MvPolynomial.eval p)) A := by
  have hC : ∀ a : MvPolynomial (Fin 0) ℂ, a = C (MvPolynomial.eval (fun i => i.elim0) a) := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c => simp
    | add a b ha hb => rw [map_add, C_add, ← ha, ← hb]
    | mul_X a i _ => exact i.elim0
  have hproj : ∀ c : ℂ, projHom (RingHom.ker (MvPolynomial.eval p)) A (C c) = algebraMap ℂ _ c := by
    intro c
    simp [projHom, pullback]
  have : (RingHom.ker (MvPolynomial.eval p)).IsPrime := RingHom.ker_isPrime _
  refine ⟨?_, ?_⟩
  · intro a b h
    rw [hC a, hC b, hproj, hproj] at h
    rw [hC a, hC b, (algebraMap ℂ _).injective h]
  · refine RingHom.Finite.of_surjective _ fun z => ?_
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨C (MvPolynomial.eval p q), by
      show projHom _ A (C (MvPolynomial.eval p q)) = _
      rw [hproj, mk_ker_eval_eq]⟩
end GroundTheory.Heights₂.Heights
