-- Prove2me | solution 1 for P2M_Formalism_ELL_WeierstrassCoordinateSubstitution_X_ne_zero__047225846678
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:28.056826+00:00
-- url     : https://prove2.me/submissions/cba89294-393a-4754-bc38-f5a6a3fe204e

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassCoordinateSubstitution
variable {K : Type u} [Field K]
namespace Formalism.ELL.WeierstrassCoordinateSubstitution
theorem _root_.solution {σ : Type} (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ K) ≠ 0 := by
  intro h
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
  simp at h1
end Formalism.ELL.WeierstrassCoordinateSubstitution
