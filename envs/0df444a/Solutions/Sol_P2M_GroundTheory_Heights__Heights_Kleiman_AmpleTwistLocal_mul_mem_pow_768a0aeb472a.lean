-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_pow_768a0aeb472a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:49.768107+00:00
-- url     : https://prove2.me/submissions/19bd9719-da79-495b-a4c4-066d304873b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmpleAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mem_chartRing_of_mem_zero_d23a951cca05

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
theorem _root_.solution (H : SubSystem S x Ω) (I : Chart x) {c : ℕ} {z : Ω}
    (hz : z ∈ (H.pow c).sub I) (d : ℕ) {w : Ω} (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (H.pow (c + d)).sub I := by
  induction d generalizing w with
  | zero =>
    change w ∈ twistMod S x 0 I at hw
    have h := Submodule.smul_mem ((H.pow c).sub I)
      (⟨w, mem_chartRing_of_mem_zero hw⟩ : chartRing S x I) hz
    rw [chartRing_smul_def] at h
    rwa [Nat.add_zero, mul_comm]
  | succ d ih =>
    change w ∈ Submodule.span _ _ at hw
    refine Submodule.span_induction
      (p := fun w _ => z * w ∈ ((H.pow (c + d)).twist H).sub I) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨q, hq, y, hy, rfl⟩
      refine Submodule.subset_span ⟨q, hq, z * y, ih hy, ?_⟩
      simp only [smul_eq_mul]; ring
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
    · intro a w _ hw
      rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hw
end GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal
