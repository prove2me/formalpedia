-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.glev_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:00.559795+00:00
-- url     : https://prove2.me/submissions/d6aef97d-14b4-4bf8-996a-820d8dfd3bc8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_exp_mulVec_fix
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_inU_rsmul
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_exp_mem_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
open PI.QnHermHaar.HermitianAdjointLemmas
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.QnHermHaar.HermitianAdjointLemmas
theorem _root_.solution {i : Fin (r + 1)} {g X : Mx k r} (hg : g ∈ Glev k r i) (hX : inLieLev k r i X)
    (t : ℝ) : g * NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  have e : ∀ v, X *ᵥ v = 0 → (g * NormedSpace.exp ((t : ℂ) • X)) *ᵥ v = g *ᵥ v := by
    intro v hv
    rw [← Matrix.mulVec_mulVec, exp_mulVec_fix _ v (by rw [Matrix.smul_mulVec, hv, smul_zero])]
  show _ ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val → _
  refine ⟨WeylGroupFacts.uh_mul hg'.1 (exp_mem_uh (inU_rsmul hX.1 t)), fun a ha => ?_⟩
  obtain ⟨h1, h2⟩ := hX.2 a ha
  obtain ⟨g1, g2⟩ := hg'.2 a ha
  exact ⟨by rw [e _ h1, g1], by rw [e _ h2, g2]⟩
end PI.QnHermHaar.HermitianAdjointLemmas
