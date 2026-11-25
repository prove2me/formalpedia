-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_smul_mem_twist_pow_e1c974636e30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:12:19.461685+00:00
-- url     : https://prove2.me/submissions/633affdc-3992-42b5-9f0d-aea216bcaf83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZExtend
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
open Filter
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZExtend
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZExtend
theorem _root_.solution (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {a b : ℕ} {z : E}
    {w : Ω} (hz : z ∈ (F.twist (H.pow a)).sub I) (hw : w ∈ (H.pow b).sub I) :
    w • z ∈ (F.twist (H.pow (a + b))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => w • z ∈ (F.twist (H.pow (a + b))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, AmpleTwistLocal.mul_mem_pow H I hq b hw, y, hy, ?_⟩
    rw [smul_smul, mul_comm]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro z z' _ _ hz hz'; rw [smul_add]; exact Submodule.add_mem _ hz hz'
  · intro t z _ hz
    have e : w • (t • z) = t • (w • z) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ t hz
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZExtend
