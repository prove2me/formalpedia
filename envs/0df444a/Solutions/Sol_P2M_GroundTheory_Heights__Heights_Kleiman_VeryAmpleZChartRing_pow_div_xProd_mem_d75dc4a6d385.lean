-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartRing_pow_div_xProd_mem_d75dc4a6d385
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:24.928805+00:00
-- url     : https://prove2.me/submissions/4883cc5c-55f1-4112-abd1-b89e29c07e3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZChartRing
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_aeval_monoProd_6aa38ad48f99
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_isHomogeneous_4a7cd1fe755c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_monoProd_mem_monos_27cdb6de9abb


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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZChartRing
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZChartRing
theorem _root_.solution {r : ℕ} {h : Fin (r + 1) → Ω} (J : Chart h) (j : Fin (r + 1)) :
    h j ^ J.1.card / xProd J ∈ chartRing S h J :=
  ⟨X j ^ J.1.card, AmpleAffineGen.monoProd J.1, J.1.card, AmpleAffineGen.monoProd_mem_monos subset_rfl,
    by simpa using (isHomogeneous_X S j).pow J.1.card, AmpleAffineGen.monoProd_isHomogeneous J.1,
    by rw [map_pow, aeval_X, AmpleAffineGen.aeval_monoProd, xProd]⟩
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZChartRing
