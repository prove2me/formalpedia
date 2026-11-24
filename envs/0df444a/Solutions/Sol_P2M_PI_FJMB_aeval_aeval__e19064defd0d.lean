-- Prove2me | solution 1 for P2M_PI_FJMB_aeval_aeval__e19064defd0d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:57.927221+00:00
-- url     : https://prove2.me/submissions/a4bf5c48-8572-4aa7-ac23-38ba8fd73a9d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution {K : Type*} [CommRing K] [Algebra ℂ K] (g : σ → K) (φ : σ → MvPolynomial σ ℂ)
    (f : MvPolynomial σ ℂ) : aeval g (aeval φ f) = aeval (fun v => aeval g (φ v)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f h hf hh => simp only [map_add, hf, hh]
  | mul_X f w hf => simp only [map_mul, aeval_X, hf]
end PI.FJMB
