-- Prove2me | solution 1 for P2M_GlobalTheory_JR_NormalFormL_sum_mulVec__fc8d7b839a0b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:47.321348+00:00
-- url     : https://prove2.me/submissions/53d72532-c197-41c1-817c-aa927e946ab4

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.NormalFormL
theorem _root_.solution {ι : Type} (s : Finset ι) (M : ι → Matrix (Fin r) (Fin r) k) (v : Fin r → k) :
    (∑ i ∈ s, M i) *ᵥ v = ∑ i ∈ s, M i *ᵥ v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, ih]
end GlobalTheory.JR.NormalFormL
