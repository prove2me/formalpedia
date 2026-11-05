-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankCoordinate.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:14:30.487498+00:00
-- url     : https://prove2.me/submissions/6326375d-fe78-48e6-b042-ec51b85d0aff

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankCoordinate
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankCoordinate
theorem _root_.solution (N L n : ℕ) : time N L n≤3000*(N+L+1)*(n+1) := by
  have hm := LightTernaryMetadata.time_bound (2*N) n
  have hp := LightTernaryPass.time_bound L n
  unfold time
  nlinarith only [hm,hp]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankCoordinate
