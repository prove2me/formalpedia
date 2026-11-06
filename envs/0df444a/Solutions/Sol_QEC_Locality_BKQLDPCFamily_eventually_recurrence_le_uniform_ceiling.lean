-- Prove2me | solution 1 for QEC.Locality.BKQLDPCFamily.eventually_recurrence_le_uniform_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:14:29.128191+00:00
-- url     : https://prove2.me/submissions/c8d6bd35-1a58-44ee-9ac6-ccda02c95203

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_BKQLDPCFamily_recurrence_le_uniform_ceiling

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
    (hfamily : family.UniformCMaxBelowOne) :
    ∃ ceiling : ℝ, 0 < ceiling ∧ ceiling < 1 ∧
      family.EventuallyOnValidIndices (fun i ↦
        (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
            (family.distance i.1) i.1 : ℝ) ≤
          (3 / (bkEntropyGap * (1 - ceiling))) * i.1 /
            (family.distance i.1 : ℝ) ^ (1 - family.cMax i)) := by
  rcases hfamily with ⟨ceiling, hceiling0, hceiling1, start, hstart⟩
  refine ⟨ceiling, hceiling0, hceiling1, start, ?_⟩
  intro n hn hvalid
  exact family.recurrence_le_uniform_ceiling ⟨n, hvalid⟩ hceiling0.le hceiling1
    (hstart n hn hvalid)
end QEC.Locality.BKQLDPCFamily
