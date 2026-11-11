-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGrowth.base_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:04:32.567168+00:00
-- url     : https://prove2.me/submissions/41a5b86d-cd2d-43ce-90be-aeea2a031f84

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_base_shared_with_central

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
namespace QEC.Coding.BDL26RXIncidenceHullGrowth
theorem _root_.solution (q r : BaseQubit) : SharedZPath baseTannerSquarePresentation q r := by
  obtain ⟨z,hq,hcenter⟩ := base_shared_with_central q
  obtain ⟨w,hr,hcenter'⟩ := base_shared_with_central r
  exact SharedZPath.snoc
    (SharedZPath.snoc (SharedZPath.refl (P := baseTannerSquarePresentation) q) z hq hcenter)
    w hcenter' hr
end QEC.Coding.BDL26RXIncidenceHullGrowth
