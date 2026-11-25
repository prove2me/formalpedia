-- Prove2me | solution 1 for PI.IsoDetW.Loc.count_spanSingleton_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:33.837032+00:00
-- url     : https://prove2.me/submissions/b25b370e-c3cc-4436-8682-83b31adbf206

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
namespace PI.IsoDetW.Loc
theorem _root_.solution (P : HeightOneSpectrum R) (D : ι → K) (hD : ∀ i, D i ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) (∏ i, D i)) =
      ∑ i, FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors R) (D i)) := by
  have : FractionalIdeal.spanSingleton (nonZeroDivisors R) (∏ i, D i) =
      ∏ i, FractionalIdeal.spanSingleton (nonZeroDivisors R) (D i) := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha,
        ← FractionalIdeal.spanSingleton_mul_spanSingleton, ih]
  rw [this, FractionalIdeal.count_prod K P _ _ (fun i _ =>
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (hD i))]
end PI.IsoDetW.Loc
