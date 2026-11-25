-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mem_da6fc1cf715f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:28:00.745346+00:00
-- url     : https://prove2.me/submissions/c4e9c83e-9c73-48d6-8fdc-63c3a55cc1ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_isHomogeneous_4a7cd1fe755c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_mem_monos_27cdb6de9abb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_aeval_monoProd_6aa38ad48f99

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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
theorem _root_.solution (I J : Chart x) : chartRatio I J ∈ chartRing S x I :=
  ⟨monoProd J.1 ^ I.1.card, monoProd I.1 ^ J.1.card, J.1.card * I.1.card,
    pow_mem (monoProd_mem_monos subset_rfl) _, (monoProd_isHomogeneous J.1).pow _,
    by rw [mul_comm]; exact (monoProd_isHomogeneous I.1).pow _,
    by simp only [chartRatio, xProd, map_pow, aeval_monoProd]⟩
end GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
