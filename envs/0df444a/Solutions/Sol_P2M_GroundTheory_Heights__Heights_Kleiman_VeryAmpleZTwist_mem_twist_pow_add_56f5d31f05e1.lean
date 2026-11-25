-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_mem_twist_pow_add_56f5d31f05e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:43:39.223466+00:00
-- url     : https://prove2.me/submissions/74354f9f-701c-47aa-9dd8-45c0a443b5c7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_smul_mem_twist_pow_7d26be4ef798

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
theorem _root_.solution (G : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {a b : ℕ} {z : E}
    (hz : z ∈ ((G.twist (H.pow a)).twist (H.pow b)).sub I) : z ∈ (G.twist (H.pow (a + b))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction (p := fun z _ => z ∈ (G.twist (H.pow (a + b))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    exact smul_mem_twist_pow G H I hq hy
  · exact Submodule.zero_mem _
  · intro b e _ _ hb he; exact Submodule.add_mem _ hb he
  · intro c z _ hz; exact Submodule.smul_mem _ c hz
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
