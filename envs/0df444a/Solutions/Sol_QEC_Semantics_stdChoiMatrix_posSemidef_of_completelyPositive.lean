-- Prove2me | solution 1 for QEC.Semantics.stdChoiMatrix_posSemidef_of_completelyPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:26.420539+00:00
-- url     : https://prove2.me/submissions/3a1b6581-cbe4-40d3-8160-896fec83284e

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Choi
import Theorems.Thm_QEC_Semantics_choiMatrix_posSemidef_of_completelyPositive

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics
theorem _root_.solution
    (Φ : Operator H →ₗ[Complex] Operator K)
    (hΦ : CompletelyPositive Φ) :
    (stdChoiMatrix Φ).PosSemidef := by
  exact choiMatrix_posSemidef_of_completelyPositive Φ hΦ
    (stdOrthonormalBasis Complex H) (stdOrthonormalBasis Complex K)
end QEC.Semantics
