-- Prove2me | solution 1 for UpperTheory.V.primeSetBoundData_of_primitiveChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:17:20.462806+00:00
-- url     : https://prove2.me/submissions/ddac5148-142c-4e2f-ab97-1eb745f800cc

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Theorems.Thm_UpperTheory_V_AbF_hasMu_cyc
import Theorems.Thm_UpperTheory_V_prime_of_mem_Bchi


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
theorem _root_.solution (ψ : PChar) : OddPrimesWithRootsOfUnity (Bchi ψ) (Lchi ψ) := fun _ hl =>
  ⟨(prime_of_mem_Bchi hl).1, (prime_of_mem_Bchi hl).2, AbF.hasMu_cyc (prime_of_mem_Bchi hl).1.pos (NeZero.pos _)⟩
end UpperTheory.V
