-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.eventually_encodedQubits_cast_le_cMax_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:24:06.88228+00:00
-- url     : https://prove2.me/submissions/4a7eaae8-daff-41d1-bfd8-9e84486cb47f

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_TwoPassDimension
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_encodedQubits_cast_le_cMax_log_bound

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v
open QEC.Locality.BKQLDPCFamily
variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]
namespace QEC.Locality.BKQLDPCFamily
theorem _root_.solution
    (family : BKQLDPCFamily iota kappa)
    (hfamily : family.EventuallyCMaxAtMostBKLogThreshold) :
    family.EventuallyOnValidIndices (fun i ↦
      (family.encodedQubits i.1 : ℝ) ≤
        ((3 * Real.log i.1 / (bkEntropyGap * Real.log 3)) *
            (3 * Real.log i.1 / (bkEntropyGap * Real.log 3))) * i.1 /
          (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
            ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)))) := by
  rcases hfamily with ⟨start, hstart⟩
  exact ⟨start, fun n hn hvalid ↦
    family.encodedQubits_cast_le_cMax_log_bound ⟨n, hvalid⟩
      (hstart n hn hvalid)⟩
end QEC.Locality.BKQLDPCFamily
