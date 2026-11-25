-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_mem_sub_iff_6462ffb5cff7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:46:32.083851+00:00
-- url     : https://prove2.me/submissions/c42e23bb-53aa-46b0-8f08-bdf603afa67d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPointGenerated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PointGenerated_mem_sub_iff_of_subset_eb0277a5cb67

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.PointGenerated
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.PointGenerated
theorem _root_.solution (hx : IsSubvar x (primeOf (S := k) x) 0) (Q : LineBundle k x) (I J : Chart x)
    (y : Ω) : y ∈ Q.sub I ↔ y ∈ Q.sub J := by
  let K : Chart x := ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩
  rw [← mem_sub_iff_of_subset hx Q (show I.1 ⊆ K.1 from Finset.subset_union_left),
    mem_sub_iff_of_subset hx Q (show J.1 ⊆ K.1 from Finset.subset_union_right)]
end GroundTheory.Heights₂.Heights.Kleiman.PointGenerated
