-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.eventually_recurrence_le_cMax_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:14:20.660511+00:00
-- url     : https://prove2.me/submissions/8e5c47b2-98ef-462b-9fc4-b8725c7376cf

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_recurrence_le_cMax_log_bound

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
open QEC.Locality.BKQLDPCFamily
variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]
namespace QEC.Locality.BKQLDPCFamily
theorem _root_.solution
    (family : BKQLDPCFamily iota kappa)
    (hfamily : family.EventuallyCMaxAtMostBKLogThreshold) :
    family.EventuallyOnValidIndices (fun i ↦
      (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
          (family.distance i.1) i.1 : ℝ) ≤
        (3 * Real.log i.1 / (bkEntropyGap * Real.log 3)) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i)) := by
  rcases hfamily with ⟨start, hstart⟩
  exact ⟨start, fun n hn hvalid ↦
    family.recurrence_le_cMax_log_bound ⟨n, hvalid⟩ (hstart n hn hvalid)⟩
end QEC.Locality.BKQLDPCFamily
