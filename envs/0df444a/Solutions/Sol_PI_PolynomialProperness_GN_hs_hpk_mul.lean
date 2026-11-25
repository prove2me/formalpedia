-- Prove2me | solution 1 for PI.PolynomialProperness.GN.hs_hpk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:07.317839+00:00
-- url     : https://prove2.me/submissions/9e579d94-1002-4918-80af-151dcf3e44f9

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_sig


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.GN
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace PI.PolynomialProperness.GN
theorem _root_.solution {k r : ℕ} (M : B.Mat k r) : hs (Hpk k r * M) = hs M := by
  unfold hs
  have e : ∀ i j, (Hpk k r * M) i j = GBasic.sgn k r i * M (GBasic.sig k r i) j := by
    intro i j
    rw [mul_apply]
    simp only [GBasic.Hpk_eq k r i, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hs1 : ∀ i, Complex.normSq (GBasic.sgn k r i) = 1 := by
    intro i; unfold GBasic.sgn; split_ifs <;> simp
  simp only [e, Complex.normSq_mul, hs1, one_mul]
  exact Equiv.sum_comp (Function.Involutive.toPerm _ (GBasic.sig_sig k r))
    (fun i => ∑ j, Complex.normSq (M i j))
end PI.PolynomialProperness.GN
