-- Prove2me | solution 1 for PI.QnHermHaar.HermitianAdjointLemmas.ec_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:28:09.995919+00:00
-- url     : https://prove2.me/submissions/2263cb80-034a-4cb1-9614-90eca0160117

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_rd_ext
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_conj
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_supp_single
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_conj_single_expand
import Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_ec_phi

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
theorem _root_.solution {i : Fin (r + 1)} {f : Mx k r → ℂ} (hf : SmoothLev k r i Set.univ f) {g : Mx k r}
    (hg : g ∈ Glev k r i) (a b : Fin (mdim k r i)) :
    RdV (hpart1 (Hpk k r) (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r)) f g +
      Complex.I • RdV (hpart2 (Hpk k r)
        (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r)) f g =
    ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EH k r (posL k r i c) (posL k r i d) f g := by
  obtain ⟨L, hL⟩ := rd_ext hf hg
  rw [ec_phi hL (supp_conj (supp_single i a b)), conj_single_expand, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, ← ec_phi hL (supp_single i c d)]
  rfl
end PI.QnHermHaar.HermitianAdjointLemmas
