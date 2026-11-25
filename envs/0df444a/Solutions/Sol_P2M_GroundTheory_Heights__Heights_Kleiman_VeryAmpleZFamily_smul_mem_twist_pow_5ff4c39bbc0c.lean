-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_smul_mem_twist_pow_5ff4c39bbc0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:03:57.91626+00:00
-- url     : https://prove2.me/submissions/2b5fe553-c2a5-4ffb-85bb-c612a592dc2c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZFamily
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
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ} {h : Fin (r + 1) → Ω}
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
theorem _root_.solution (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {z : E}
    {q : Ω} (hz : z ∈ (F.twist (H.pow c)).sub I) (hq : q ∈ (H.pow d).sub I) :
    q • z ∈ (F.twist (H.pow (c + d))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => q • z ∈ (F.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨p, hp, y, hy, rfl⟩
    exact Submodule.subset_span ⟨p * q, AmpleTwistLocal.mul_mem_pow H I hp d hq, y, hy, by
      rw [smul_smul, mul_comm]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    rw [Subalgebra.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ a hz
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
