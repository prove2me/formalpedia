-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.eventually_recurrence_le_cMax_logarithmic_gap_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:14:21.4432+00:00
-- url     : https://prove2.me/submissions/cc10c6c0-3f25-4b2d-8f74-0163c8cef527

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_recurrence_le_cMax_logarithmic_gap_bound

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
    (family : BKQLDPCFamily iota kappa) {gamma : ℝ} (hgamma : 0 < gamma)
    (hfamily : family.EventuallyOnValidIndices (fun i ↦
      gamma ≤ (1 - family.cMax i) * Real.log i.1)) :
    family.EventuallyOnValidIndices (fun i ↦
      (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
          (family.distance i.1) i.1 : ℝ) ≤
        (3 * Real.log i.1 / (bkEntropyGap * gamma)) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i)) := by
  rcases hfamily with ⟨start, hstart⟩
  exact ⟨start, fun n hn hvalid ↦
    family.recurrence_le_cMax_logarithmic_gap_bound ⟨n, hvalid⟩ hgamma
      (hstart n hn hvalid)⟩
end QEC.Locality.BKQLDPCFamily
