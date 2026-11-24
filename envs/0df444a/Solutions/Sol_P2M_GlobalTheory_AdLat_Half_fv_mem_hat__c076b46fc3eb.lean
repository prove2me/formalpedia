-- Prove2me | solution 1 for P2M_GlobalTheory_AdLat_Half_fv_mem_hat__c076b46fc3eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:04:41.348215+00:00
-- url     : https://prove2.me/submissions/9744ceca-fc41-42dd-9506-a6730f694101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralTmulOneMulMemAdelicCompletion
import Theorems.Thm_GlobalTheory_AdLat_adele_one_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Half
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat.Half
namespace _root_.GlobalTheory.AdLat.Half
theorem _root_.solution (L : Set (Fin n → E)) (y : Fin n → E)
    (hy : y ∈ L) : _root_.GlobalTheory.AdLat.fv F y ∈ _root_.GlobalTheory.AdLat.hat F L :=
  AddSubgroup.subset_closure ⟨1, _root_.GlobalTheory.AdLat.adele_one_integral F, y, hy, rfl⟩
end _root_.GlobalTheory.AdLat.Half
end GlobalTheory.AdLat.Half
