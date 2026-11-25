-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_pot_fin_cons_31ce65ad0242
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:22.898245+00:00
-- url     : https://prove2.me/submissions/c7b65c6e-89f6-426c-a0f7-feca4120867d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PoincareLelongRegularised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsRegLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAbsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PotFinCons
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} (M : HermLine ι)
    (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]
end GroundTheory.Heights₂.Heights.Targets
