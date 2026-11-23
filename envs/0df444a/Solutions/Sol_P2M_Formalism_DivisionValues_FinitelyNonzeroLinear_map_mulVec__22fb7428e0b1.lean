-- Prove2me | solution 1 for P2M_Formalism_DivisionValues_FinitelyNonzeroLinear_map_mulVec__22fb7428e0b1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:31.256373+00:00
-- url     : https://prove2.me/submissions/d69b4bee-c3ab-4728-a475-ffb9f9c205cf

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
variable {j}
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (x : Fin n → K) :
    (A.map j) *ᵥ (fun i => j (x i)) = fun i => j ((A *ᵥ x) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
end Formalism.DivisionValues.FinitelyNonzeroLinear
