-- Prove2me | solution 1 for P2M_Formalism_LatticeIndexTer_subgroupData_length_chain__bd85a5aaefa7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:27.849546+00:00
-- url     : https://prove2.me/submissions/66453bdf-8792-4090-8629-5b8c7c754b90

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ChainLength
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPowSmulMem
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
import Theorems.Thm_UpperTheory_Reformulated_B_JointEigenvalueBoundsFromAnyDatum_length_chain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.subgroupData
variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
namespace Formalism.LatticeIndexTer.subgroupData
theorem _root_.solution {A B C : Submodule O X} (hAB : A ≤ B) (hBC : B ≤ C) :
    Module.length O (C ⧸ A.comap C.subtype) =
      Module.length O (B ⧸ A.comap B.subtype) + Module.length O (C ⧸ B.comap C.subtype) :=
  _root_.UpperTheory.Reformulated.B.JointEigenvalueBoundsFromAnyDatum.length_chain hAB hBC
end Formalism.LatticeIndexTer.subgroupData
