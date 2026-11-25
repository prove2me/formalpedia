-- Prove2me | solution 1 for PI.IsoDetW.Loc.toNat_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:33.3588+00:00
-- url     : https://prove2.me/submissions/1910fad7-9921-414f-992f-6259811b370d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat

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
  {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
omit [DecidableEq ι]
namespace PI.IsoDetW.Loc
theorem _root_.solution (f : ι → ℕ∞) (hf : ∀ i, f i ≠ ⊤) : (∑ i, f i).toNat = ∑ i, (f i).toNat := by
  have : (∑ i, f i) = ((∑ i, (f i).toNat : ℕ) : ℕ∞) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => (ENat.natCast_toNat (hf i)).symm
  rw [this, ENat.toNat_natCast]
end PI.IsoDetW.Loc
