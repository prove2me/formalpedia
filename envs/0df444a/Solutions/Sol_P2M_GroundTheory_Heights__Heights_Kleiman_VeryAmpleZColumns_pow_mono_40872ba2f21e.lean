-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_pow_mono_40872ba2f21e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:36.424614+00:00
-- url     : https://prove2.me/submissions/60a149e7-dca8-4ed8-b414-a819502da23e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZColumns
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_prod_mem_pow_64c1a3dc0e85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_smul_mem_twist_pow_613b8211fa30

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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ}
variable {G : SubSystem S x E} {H : SubSystem S x Ω} {h : Fin (r + 1) → Ω} {I : Chart x}
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
theorem _root_.solution (hH : ∀ j, h j ∈ H.sub I) {J : Chart h} {e : E} {n : ℕ}
    (he : xProd J ^ n • e ∈ (G.twist (H.pow (J.1.card * n))).sub I) (k : ℕ) :
    xProd J ^ (n + k) • e ∈ (G.twist (H.pow (J.1.card * (n + k)))).sub I := by
  have hq : xProd J ^ k ∈ H.sub I ^ (J.1.card * k) := by
    rw [pow_mul]; exact Submodule.pow_mem_pow _ (prod_mem_pow _ h hH J.1) k
  have := smul_mem_twist_pow hq he
  rwa [show J.1.card * (n + k) = J.1.card * n + J.1.card * k by ring, pow_add,
    mul_comm (xProd J ^ n), mul_smul]
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
