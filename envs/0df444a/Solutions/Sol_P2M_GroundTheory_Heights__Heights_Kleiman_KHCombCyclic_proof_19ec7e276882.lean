-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_proof_19ec7e276882
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:02:49.95583+00:00
-- url     : https://prove2.me/submissions/5636876b-6664-4db6-977e-b6b8965914c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombCyclicSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombCyclic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_singOne_cocycle_ebe7863fb360
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHCombCyclic_cyclic_cohom_2409c2a8089e

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace KHCombCyclic
theorem _root_.solution (hC : KHCombContract.Statement) : KHCombCyclic.Statement := by
  intro S _ K _ _ ι _ _ J n hJ
  exact ⟨KHCombCyclic.singOne_cocycle J n hJ, fun f hf => KHCombCyclic.cyclic_cohom hC J n hJ f hf⟩
end KHCombCyclic
end GroundTheory.Heights₂.Heights.Kleiman
