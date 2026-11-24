-- Prove2me | solution 1 for P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_a68189d70cdc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:41.281778+00:00
-- url     : https://prove2.me/submissions/8ebd016e-7474-409c-bc34-9738a59bc0b7

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ComplexConjugate
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.LemmaU
open Formalism.DoubleCosetMeasures
variable {F : Type} [Field F] {a t : ℕ}
namespace Formalism.DoubleCosetMeasures.P.LemmaU
theorem _root_.solution (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (g : Matrix (Fin a) (Fin a) F) :
    toRows₂ (x * g) = toRows₂ x * g := by
  ext i j
  simp [toRows₂, Matrix.mul_apply]
end Formalism.DoubleCosetMeasures.P.LemmaU
