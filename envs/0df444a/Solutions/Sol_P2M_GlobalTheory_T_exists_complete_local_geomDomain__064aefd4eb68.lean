-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_complete_local_geomDomain__064aefd4eb68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:56:47.132847+00:00
-- url     : https://prove2.me/submissions/81e3d53e-2169-4acb-a0e6-b66b8d612e35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteLocalGeomDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteLocalGeomDomainStatement
import Theorems.Thm_GlobalTheory_SepRing_exists_complete_local_geomDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k'] [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧ Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by
  first | exact @GlobalTheory.SepRing.exists_complete_local_geomDomain | exact GlobalTheory.SepRing.exists_complete_local_geomDomain | (intros; apply GlobalTheory.SepRing.exists_complete_local_geomDomain <;> assumption)
end _root_.GlobalTheory.T
