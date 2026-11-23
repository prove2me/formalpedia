-- Prove2me | solution 1 for PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:45.230004+00:00
-- url     : https://prove2.me/submissions/4d7d52e2-84e4-4662-a474-50f5a5b267a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_MemZeroLocusGLIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.UnipApproxD.IntegersDenseFiniteAdeles
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
private theorem val_K_lemma (v : HeightOneSpectrum R) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k := by
  first
  | exact valuedAdicCompletion_eq_valuation' v k
  | exact valuedAdicCompletion_eq_valuation' k
  | exact valuedAdicCompletion_eq_valuation v k
  | exact valuedAdicCompletion_eq_valuation k
  | rfl
end PI.UnipApproxD.IntegersDenseFiniteAdeles
namespace PI.UnipApproxD
open NumberField IsDedekindDomain
end PI.UnipApproxD
end
end

set_option autoImplicit false
noncomputable section
open PI PI.UnipApproxD PI.UnipApproxD.IntegersDenseFiniteAdeles
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace PI.UnipApproxD.IntegersDenseFiniteAdeles
theorem _root_.solution (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  rw [val_K_lemma]
  first
  | exact valuation_of_algebraMap v r
  | exact v.valuation_of_algebraMap r
  | simp [valuation_of_algebraMap]
end PI.UnipApproxD.IntegersDenseFiniteAdeles
