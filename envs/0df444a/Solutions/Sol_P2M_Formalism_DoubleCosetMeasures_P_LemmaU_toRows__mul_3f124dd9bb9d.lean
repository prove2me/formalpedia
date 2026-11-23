-- Prove2me | solution 1 for P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_3f124dd9bb9d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:24.84032+00:00
-- url     : https://prove2.me/submissions/d77bb2b1-9af9-4f69-9143-3eca5b315ccb

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
    toRows₁ (x * g) = toRows₁ x * g := by
  ext i j
  simp [toRows₁, Matrix.mul_apply]
end Formalism.DoubleCosetMeasures.P.LemmaU
