-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_fibreLift_075fadd65d1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:32.508533+00:00
-- url     : https://prove2.me/submissions/86e535fe-d7d1-488b-b11c-77ba6c3ba4b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLengthSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_anti_2b5a3c1121df

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) (α : degZeroLoc (contractPrime j P') {W}) :
    ∃ β : (W' : Ideal (MRing ι' F)) → degZeroLoc P' {W'},
      ∀ W' ∈ fibrePrimes j P' W,
        (β W' : FractionRing (MRing ι' F ⧸ P')) = contractFracMap j P' (α : _) := by
  classical
  refine ⟨fun W' => if hm : contractFracMap j P' (α : _) ∈ degZeroLoc P' {W'} then ⟨_, hm⟩ else 0,
    fun W' hW' => ?_⟩
  have hm : contractFracMap j P' (α : _) ∈ degZeroLoc P' {W'} :=
    degZeroLoc_anti P' (Set.singleton_subset_iff.mpr hW')
      (map_degZeroLoc_le j P' W (Subalgebra.mem_map.mpr ⟨_, α.2, rfl⟩))
  simp only [dif_pos hm]
end GroundTheory.Heights₂.Heights.FieldNumbers
