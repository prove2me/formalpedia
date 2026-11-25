-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_mem_zeroSet_mulVec_eq_4f161ad796b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:32:01.450073+00:00
-- url     : https://prove2.me/submissions/efd696e2-c016-4028-a791-05868a03ac85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFiniteFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFiniteFibreDim

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
open MvPolynomial MeasureTheory
open scoped Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {B : Matrix (Fin d) (Fin n) ℂ} (hB : ComplexSets.IsFiniteProjection J B) (x : Fin d → ℂ) :
    ∃ z ∈ ComplexSets.zeroSet J, B *ᵥ z = x := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (ComplexSets.projHom J B).toRingHom.toAlgebra
  have _ : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ⟨fun y => hB.finite.to_isIntegral y⟩
  have _ : (RingHom.ker (eval x)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := MvPolynomial (Fin n) ℂ ⧸ J) (RingHom.ker (eval x)) (by
      intro q hq
      have hq0 : q = 0 := hB.injective (by rw [RingHom.mem_ker] at hq; exact hq.trans (map_zero _).symm)
      rw [hq0]; exact Ideal.zero_mem _)
  have hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨z, hz⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hQ'
  have hmem : ∀ q, Ideal.Quotient.mk J q ∈ Q ↔ eval z q = 0 := fun q => by
    rw [← Ideal.mem_comap, hz, mem_vanishingIdeal_singleton_iff]; rfl
  refine ⟨z, fun q hq => (hmem q).1 ?_, funext fun i => ?_⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 hq]; exact Q.zero_mem
  · have hi : X i - C (x i) ∈ RingHom.ker (eval x) := by simp [RingHom.mem_ker]
    rw [← hQP, Ideal.mem_comap] at hi
    change ComplexSets.projHom J B (X i - C (x i)) ∈ Q at hi
    have h1 : ComplexSets.projHom J B (X i - C (x i)) =
        Ideal.Quotient.mk J (ComplexSets.linPoly B i - C (x i)) := by
      simp [ComplexSets.projHom, ComplexSets.pullback]
    rw [h1, hmem, map_sub, eval_C, sub_eq_zero] at hi
    rw [← hi]
    simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct]
end GroundTheory.Heights₂.Heights
