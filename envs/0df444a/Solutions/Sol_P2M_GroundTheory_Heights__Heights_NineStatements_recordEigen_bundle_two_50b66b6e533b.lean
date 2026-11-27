-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_recordEigen_bundle_two_50b66b6e533b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:03:52.857811+00:00
-- url     : https://prove2.me/submissions/c003f5d5-b13a-4908-98fe-9cc598e0e53d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_smallBlockTwo_eigenRecord_3fc6d307bd88
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_smallBlockTwo_m1Prime_0200493cebd2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_two_mem_primesB_38317b996a21

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    2 ≤ 2 ∧ (∀ p ∈ (∅ : Finset ℕ), p.Prime) ∧ (∅ : Finset ℕ).card ≤ 2 ∧
      EigenRecordAt (fun _ => ι) 1 (smallBlockTwo ι) ∧ OrderBoundAtPrime (fun _ => ι) 1 (primesB 2 ∅) (smallBlockTwo ι) :=
  ⟨le_rfl, by simp, by simp, smallBlockTwo_eigenRecord ι le_rfl,
    smallBlockTwo_m1Prime ι le_rfl (two_mem_primesB le_rfl ∅)⟩
end GroundTheory.Heights₂.Heights.NineStatements
