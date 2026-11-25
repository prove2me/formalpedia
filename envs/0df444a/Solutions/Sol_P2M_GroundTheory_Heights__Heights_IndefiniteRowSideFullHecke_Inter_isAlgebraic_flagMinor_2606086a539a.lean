-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isAlgebraic_flagMinor_2606086a539a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:23.956208+00:00
-- url     : https://prove2.me/submissions/5c860cf4-fbfb-49c4-a3cb-ef3166f2ed16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_det_mem_subring_25f6a2c0f529
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_leadMinor_mem_pivotAlgP_593e98f45199
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMatrix_mem_pivotAlgP_13573ffee2ff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_of_mem_pivotAlgP_39117ec39eaa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (h₁ : FlagPivotIdentity.Statement)
    (hne : ∀ a : Fin (n - 1), leadMinor (genMat F n) a ≠ 0) (q : Σ j, PluckerBlocks n n j) :
    IsAlgebraic (pivotAlg F n)
      (⟨flagMinor (genMat F n) q.1 q.2, Algebra.subset_adjoin ⟨q, rfl⟩⟩ : flagMinorAlg F n) := by
  obtain ⟨j, S⟩ := q
  obtain ⟨c, hc⟩ := exists_of_mem_pivotAlgP F n (y := ∏ a ∈ Finset.Iic j, leadMinor (genMat F n) a)
    (Subalgebra.prod_mem _ fun a _ => leadMinor_mem_pivotAlgP F n a)
  obtain ⟨d, hd⟩ := exists_of_mem_pivotAlgP F n
    (y := leadMinor (genMat F n) j * flagMinor (pivotMatrix (genMat F n)) j S)
    (Subalgebra.mul_mem _ (leadMinor_mem_pivotAlgP F n j)
      (det_mem_subring (pivotAlgP F n).toSubring _ fun r s => pivotMatrix_mem_pivotAlgP F n j r _))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (Finset.prod_ne_zero_iff.mpr fun a _ => hne a) hc.symm
  have h1 : c • (⟨flagMinor (genMat F n) j S, Algebra.subset_adjoin ⟨⟨j, S⟩, rfl⟩⟩ : flagMinorAlg F n) =
      algebraMap (pivotAlg F n) (flagMinorAlg F n) d := by
    apply Subtype.val_injective
    change ((c : flagMinorAlg F n) : MvPolynomial (Fin n × Fin n) F) * flagMinor (genMat F n) j S =
      ((d : flagMinorAlg F n) : MvPolynomial (Fin n × Fin n) F)
    rw [hc, hd, ← h₁ (MvPolynomial (Fin n × Fin n) F) n (genMat F n) j S, mul_comm]
  exact IsAlgebraic.of_smul (mem_nonZeroDivisors_of_ne_zero hc0) (h1 ▸ isAlgebraic_algebraMap d)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
