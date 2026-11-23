-- Prove2me | solution 1 for P2M_Formalism_L2_S_L6_UnitaryStandardVectors_Z_ne__2f739ef805d0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:56.014414+00:00
-- url     : https://prove2.me/submissions/fefffa87-1eb9-41fe-a59a-902f2a4c273d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.L6 Formalism.L2.S.L6.UnitaryStandardVectors
variable {m : ℕ}
variable (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hZ
namespace Formalism.L2.S.L6.UnitaryStandardVectors
theorem _root_.solution (i : Fin m) : Z i (π i) ≠ 0 := (hZ i (π i)).mpr (hπ i).symm
end Formalism.L2.S.L6.UnitaryStandardVectors
