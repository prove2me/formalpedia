-- Prove2me | solution 1 for ReciprocityTheory.Cheb.power_series_diagonal_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:18:14.69952+00:00
-- url     : https://prove2.me/submissions/b4ae93e5-53ac-4d2f-b330-a3372bb06565

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitB
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitC
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitE
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
import Theorems.Thm_ReciprocityTheory_Cheb_PE_cyclotomicField_le_mul_Pcl_add_const
import Theorems.Thm_ReciprocityTheory_Cheb_chebyshev_log_bounded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution : S1 := by
  intro E _ _ l _ hirr
  obtain ⟨C, hC⟩ := PE_cyclotomicField_le_mul_Pcl_add_const E l hirr
  obtain ⟨CE, hE⟩ := chebyshev_log_bounded E
  obtain ⟨CM, hM⟩ := chebyshev_log_bounded (CyclotomicField l E)
  refine ⟨CE + CM + C, ?_⟩
  have hmem : Set.Ioc (1:ℝ) 2 ∈ 𝓝[>] (1:ℝ) := Ioc_mem_nhdsGT (by norm_num)
  filter_upwards [hmem] with s hs
  have h1 := hC s hs.1
  have h2 := (abs_le.mp (hE s hs)).2
  have h3 := (abs_le.mp (hM s hs)).1
  linarith
end ReciprocityTheory.Cheb
