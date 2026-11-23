-- Prove2me | solution 1 for UpperTheory.V.ThmBab.a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:52.932263+00:00
-- url     : https://prove2.me/submissions/8e10c3a5-9060-42ae-a219-84d8856bb877

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Theorems.Thm_UpperTheory_V_BShape_mono
import Theorems.Thm_UpperTheory_Top_VVle_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open UpperTheory UpperTheory.V
open Formalism.HC UpperTheory.Top
namespace UpperTheory.V
namespace ThmBab
theorem _root_.solution {K : BConst} {Ct : ℝ} (h : ThmBab K Ct) : ThmBa K Ct :=
  BShape.mono (fun _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, fun x solution b => (h.2 x solution b).1⟩) h
end ThmBab
end UpperTheory.V
