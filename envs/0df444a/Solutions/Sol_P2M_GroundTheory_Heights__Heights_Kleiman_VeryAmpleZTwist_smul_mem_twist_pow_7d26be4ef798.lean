-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_smul_mem_twist_pow_7d26be4ef798
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:14:01.475181+00:00
-- url     : https://prove2.me/submissions/fc7184b1-4418-4ea7-8a18-d9b6a30e76c7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_chart_smul_eq_66ee2ccdfd04
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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
theorem _root_.solution (G : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {w : Ω}
    (hw : w ∈ (H.pow c).sub I) {z : E} (hz : z ∈ (G.twist (H.pow d)).sub I) :
    w • z ∈ (G.twist (H.pow (d + c))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction (p := fun z _ => w • z ∈ (G.twist (H.pow (d + c))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, AmpleTwistLocal.mul_mem_pow H I hq c hw, y, hy, ?_⟩
    rw [smul_smul, mul_comm]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro b e _ _ hb he; rw [smul_add]; exact Submodule.add_mem _ hb he
  · intro c' z _ hz
    rw [chart_smul_eq, smul_smul, mul_comm, ← smul_smul, ← chart_smul_eq]
    exact Submodule.smul_mem _ c' hz
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
