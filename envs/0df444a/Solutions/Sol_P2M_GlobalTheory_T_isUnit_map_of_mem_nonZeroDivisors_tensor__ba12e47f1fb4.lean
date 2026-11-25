-- Prove2me | solution 1 for P2M_GlobalTheory_T_isUnit_map_of_mem_nonZeroDivisors_tensor__ba12e47f1fb4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:07.747748+00:00
-- url     : https://prove2.me/submissions/ee1b0837-e069-4be8-bb82-ab8689939081

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitMapOfMemNonZeroDivisorsTensor
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitMapOfMemNonZeroDivisorsTensorStatement
import Theorems.Thm_GlobalTheory_isUnit_map_of_mem_nonZeroDivisors_tensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C] (φ : U ⊗[T] C →+* L ⊗[F] K), Function.Injective φ → (∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) → ∀ s ∈ nonZeroDivisors (U ⊗[T] C), IsUnit (φ s) := by
  first | exact @GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor | exact GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor | (intros; apply GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor <;> assumption)
end _root_.GlobalTheory.T
