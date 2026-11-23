-- Prove2me | solution 1 for PI.UnipApproxD.IntegersDenseFiniteAdeles.int_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:45.676817+00:00
-- url     : https://prove2.me/submissions/81f241aa-39fa-4846-ad83-fe57221dfe68

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
    algebraMap K (v.adicCompletion K) (algebraMap R K r) ∈ v.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers, val_K_lemma, valuation_of_algebraMap]
  first
  | exact v.intValuation_le_one r
  | exact intValuation_le_one v r
  | exact intValuation_le_one r
end PI.UnipApproxD.IntegersDenseFiniteAdeles
