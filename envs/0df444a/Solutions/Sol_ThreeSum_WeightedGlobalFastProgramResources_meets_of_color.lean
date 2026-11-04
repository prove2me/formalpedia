-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFastProgramResources.meets_of_color
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:53:07.460474+00:00
-- url     : https://prove2.me/submissions/59abf0b0-adaa-4ae5-96f4-ebb577e989df

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
import Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_global_ok
import Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_color_ok
import Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_scan_bounds
import Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_lift_color
import Theorems.Thm_ThreeSum_LightWeightedGlobalFastProgramProof_meets_of_colors


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFastProgramResources
open Light LightWeightedGlobalFastProgram LightWeightedGlobalFastProgramProof
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalFastProgramResources
theorem _root_.solution {lim : Limits} {M b p K κ n src free depth colorMain colorTime : ℕ}
    [Fact p.Prime] (color : Program) (colorNeed : ℕ→ℕ→Need) (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hM : 1<M) (hb : 1<b) (hn : 0<n) (hsrc : src≤free)
    (H : (need M b p K κ colorNeed n (n^κ)).Ok lim free depth)
    (hcolor : ∀c<p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ)), ∀ν₀,
      Receipt M b p K κ n free c μ ν₀→
      ∀ (i : ℕ) (hi : i < ColorParameters.count (LightColorParametersCosts.width n)) (ν : ℕ→ℤ),
      Kept ν₀ ν (scanFree M b p K κ n free)→
      Seg ν (scanFree M b p K κ n free) (ColorParameters.fields (ColorParameters.parameter hi))→
      ∀dd, (colorNeed n (n^κ)).Ok lim (scanFree M b p K κ n free+6) dd→
      Meets lim color colorMain dd
        [src,n,LightWeightedGlobalGlobalPrelude.params free,scanFree M b p K κ n free,
          scanFree M b p K κ n free+6] ν colorTime
        (fun z ξ=>(z=0∨z=1) ∧ (z=1↔ColorClassLists.witness (ColorParameters.parameter hi) x) ∧
          Kept ν ξ (scanFree M b p K κ n free))) :
    Meets lim (program M b p K κ color colorMain) (mainEntry color) depth [src,n,free] μ
      (time M b p K κ colorTime n)
      (fun z ν=>(z=0∨z=1) ∧ (z=1↔Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by
  have B := scan_bounds H
  apply meets_of_colors color x μ hM hb hn hsrc (global_ok H) B.1 B.2.1 B.2.2
  intro c hc ν₀ hreceipt i hi ν hkeep hfields dd hd
  exact lift_color (hcolor c hc ν₀ hreceipt i hi ν hkeep hfields dd (color_ok H hd))
end ThreeSum.WeightedGlobalFastProgramResources
