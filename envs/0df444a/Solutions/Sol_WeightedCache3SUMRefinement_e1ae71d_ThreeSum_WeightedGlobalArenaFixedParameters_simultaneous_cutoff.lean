-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFixedParameters.simultaneous_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:24.430077+00:00
-- url     : https://prove2.me/submissions/64ed893e-2b73-48ce-864a-43acc3ecf563

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSignedSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCarryBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCollisionRate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedNativeDrift
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaFixedParameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFixedParameters_exists_parameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaFixedParameters_natural_cutoff

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFixedParameters
open Filter WeightedGlobalCoverScale WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalOversizeOverhead WeightedGlobalSignedPadding WeightedGlobalArenaBudgetExistence
open WeightedGlobalPairedCollisionRate WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 3000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFixedParameters
theorem _root_.solution {K : ℕ} (hK : 100000000000000000000≤K) (κ c d N : ℕ) :
    ∃t m n0 : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      carryExponent m (2^t) (κ : ℝ)<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      (9*pairFactor m (familyLength K m) K)^4*(outputSize m)^(4*K+3)≤((nativePrime K m)^(2*K))^4 ∧
      9<nativePrime K m ∧ charge K m<(7483/10000 : ℝ) ∧
      ∀n≥n0,InputGuards K m (2^t) κ n := by
  obtain ⟨t,m,ht,hN,hg,ho,hc,hd,hp,hdrift,hp9,hcharge⟩ :=
    exists_parameters hK (κ := (κ : ℝ)) (by positivity) c d N
  have hb : 1<2^t := by
    have hh := Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (show 1≤t by omega)
    norm_num at hh
    omega
  obtain ⟨n0,hn0⟩ := natural_cutoff (by omega : 0<K) hg.1 hb κ hc
  exact ⟨t,m,n0,ht,hN,hg,ho,hc,hd,hp,hdrift,hp9,hcharge,hn0⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaFixedParameters
