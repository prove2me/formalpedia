-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_PoincareLelongAlt_of_found_e6d09a0ad8bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:50.175816+00:00
-- url     : https://prove2.me/submissions/93585f56-5420-4ab9-bc63-110ee71598e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PoincareLelongRegularised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PoincareLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PoincareLelongAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_isSmoothHerm_regLine_b405ba1f59a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_log_regLine_0e45a6823993
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_regLine_a_dcb8ccb69f0f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
namespace GroundTheory.Heights₂.Heights.Targets
namespace PoincareLelongAlt
theorem _root_.solution (hSt : StokesStatement) (hReg : PoincareLelongRegularised.Statement)
    (hLim : PoincareLelongLimit.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula := by
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hS : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)) =
        ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (regLog A s ε) := by
    intro ε hε
    have h := hSt K ι P n L (regLine A s ε ha hsa) B hP hL (isSmoothHerm_regLine hA hε ha hsa) hB
      (regLine_a A s ε ha hsa) hBa
    rw [log_regLine] at h
    exact h.symm
  exact tendsto_nhds_unique (hReg K ι P n L A B s hP hL hA hB hBa hs)
    ((hLim K ι P n L A B s hP hL hA hB hBa hs).congr' (eventually_nhdsWithin_of_forall hS))
end PoincareLelongAlt
end GroundTheory.Heights₂.Heights.Targets
