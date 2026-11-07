-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.eventually_encodedQubits_cast_le_uniform_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:22:37.001197+00:00
-- url     : https://prove2.me/submissions/ce5bbf85-d09b-4048-87b7-98660e499bcb

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_TwoPassDimension
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_encodedQubits_cast_le_uniform_ceiling

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
    (hfamily : family.UniformCMaxBelowOne) :
    ∃ ceiling : ℝ, 0 < ceiling ∧ ceiling < 1 ∧
      family.EventuallyOnValidIndices (fun i ↦
        (family.encodedQubits i.1 : ℝ) ≤
          ((3 / (bkEntropyGap * (1 - ceiling))) *
              (3 / (bkEntropyGap * (1 - ceiling)))) * i.1 /
            (((family.distance i.1 : ℝ) ^ (1 - family.cMax i)) *
              ((family.distance i.1 : ℝ) ^ (1 - family.cMax i)))) := by
  rcases hfamily with ⟨ceiling, hceiling0, hceiling1, start, hstart⟩
  refine ⟨ceiling, hceiling0, hceiling1, start, ?_⟩
  intro n hn hvalid
  exact family.encodedQubits_cast_le_uniform_ceiling ⟨n, hvalid⟩
    hceiling0.le hceiling1 (hstart n hn hvalid)
end QEC.Locality.BKQLDPCFamily
