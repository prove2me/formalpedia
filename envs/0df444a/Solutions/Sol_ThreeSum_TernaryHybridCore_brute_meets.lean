-- Prove2me | solution 1 for ThreeSum.TernaryHybridCore.brute_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:04.886773+00:00
-- url     : https://prove2.me/submissions/796f7453-5e11-4caa-9edf-fd6d14667dcb

import Definitions.Def_Submission_ThreeSum_TernaryHybridResources
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_SolvesN_append
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_append
import Theorems.Thm_Light_Solves_meets
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_1b87db5b0e9f9b11
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_6cd6f72823a59258
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_ec604c008ed4b1df
import Definitions.Def_WeightedCache3SUM_Alias_eb09b223848624eb
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCore
open Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
namespace ThreeSum.TernaryHybridCore
theorem _root_.solution {lim : Limits} {fastP : Program} {fastProc κ cutoff src n U free d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hn : 0<n) (hsrc : src+n≤free) (H : (LightBruteThreeSum.need n U).Ok lim free d)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hx : ∀ i, |x i|≤(U : ℤ)) :
    Meets lim (program fastP fastProc κ cutoff) (fastP.length+3) d [n,U,src,free] μ (LightBruteThreeSum.time n)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ ν=μ) := by
  have hh := LightBruteThreeSum.meets (P := LightBruteThreeSum.program) (pMain := 3)
    (pScan := 2) (pRow := 0) (pDivide := 1) x μ rfl rfl rfl rfl hn hsrc H hread hx
  have hrun := (ReportingHostRelocation.meets hh fastP).append
    [LightNatPower.body,body fastP.length fastProc κ cutoff]
  exact hrun
end ThreeSum.TernaryHybridCore
