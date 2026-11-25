-- Prove2me | solution 1 for PI.QnHermHaar.elementary_generator_preserves_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:56.084225+00:00
-- url     : https://prove2.me/submissions/520f2ad7-865b-482d-b363-c557a3a54271

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorPreservesTest
import Theorems.Thm_PI_QnHermHaar_tst_lie
import Theorems.Thm_PI_QnHermHaar_tst_rdV_eq
import Theorems.Thm_PI_QnHermHaar_tst_rdV_zero
import Theorems.Thm_Formalism_REAL_withTop_enat_infty_add_one_le_infty


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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.QnHermHaar
theorem _root_.solution : EabTest := by
  intro k r i a b f hf
  unfold TestF CptOn at hf ⊢
  obtain ⟨hs, K, hK, hKf⟩ := hf
  obtain ⟨h1, h2⟩ := tst_lie (k := k) i a b
  refine ⟨?_, K, hK, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hs g₀ hg₀
    have hd := hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
    refine ⟨U, fun g => fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) +
      Complex.I • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)),
      hU, hg₀U, ?_, ?_⟩
    · exact (hd.clm_apply (mulRightRealCLM _).contDiff.contDiffOn).add
        ((hd.clm_apply (mulRightRealCLM _).contDiff.contDiffOn).const_smul Complex.I)
    · intro g hg hgG
      show RdV _ f g + Complex.I • RdV _ f g = _
      rw [tst_rdV_eq f F U g _ hU hg hgG hF hfF h1, tst_rdV_eq f F U g _ hU hg hgG hF hfF h2]
  · intro g hg hgK
    show RdV _ f g + Complex.I • RdV _ f g = 0
    rw [tst_rdV_zero f K hK.isClosed hKf _ h1 g hg hgK, tst_rdV_zero f K hK.isClosed hKf _ h2 g hg hgK,
      smul_zero, add_zero]
end PI.QnHermHaar
