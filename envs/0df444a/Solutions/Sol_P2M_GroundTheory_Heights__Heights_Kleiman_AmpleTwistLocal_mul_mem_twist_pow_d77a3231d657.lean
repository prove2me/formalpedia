-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_twist_pow_d77a3231d657
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:07.47837+00:00
-- url     : https://prove2.me/submissions/876cb9f7-62a4-4a1b-90f0-f938544dfc0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmpleAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_pow_768a0aeb472a

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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal
theorem _root_.solution (Q H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {z w : Ω}
    (hz : z ∈ (Q.twist (H.pow c)).sub I) (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (Q.twist (H.pow (c + d))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => z * w ∈ (Q.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, mul_mem_pow H I hq d hw, y, hy, ?_⟩
    simp only [smul_eq_mul]; ring
  · rw [zero_mul]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_mul]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    rw [chartRing_smul_def, mul_assoc, ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hz
end GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal
