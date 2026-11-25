-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellConeS_res_bcc5079ec5bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:18.277237+00:00
-- url     : https://prove2.me/submissions/06c41412-ead6-4b90-a22d-27a65d640d80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_not_4e0646e9c831
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_subset_d748224c1d3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_locRes_374e5d5036f2


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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution (I J : StdCell N) (h : I.1 ⊆ J.1) (m : LocMod S N M.coneSub I.1) :
    M.cellConeS J (locResS I J h m) = supportRes S x I J h (M.cellConeS I m) := by
  by_cases hJ : J.1 ⊆ support x
  · rw [supportRes_of_subset h hJ, LinearMap.id_apply]
    change M.cellCone J (locRes h m) = M.cellCone I m
    rw [M.cellCone_of_subset hJ, M.cellCone_of_subset (h.trans hJ)]
    exact locCone_locRes M h hJ m
  · rw [supportRes_of_not h hJ, LinearMap.zero_apply]
    change M.cellCone J _ = 0
    rw [M.cellCone_of_not hJ]
    rfl
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman
