-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.nsq_root
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:13:52.605927+00:00
-- url     : https://prove2.me/submissions/54bb9410-af65-4d46-9d86-71c5ecbbdc91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {ε : Fin n → Bool}

theorem ReciprocityTheory.ChartRestriction.DS.nsq_root {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by
  simp only [nsq, dot, root, Pi.sub_apply]
  have hba : b ≠ a := fun h => hab h.symm
  simp [Pi.single_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite, hab, hba]
  norm_num


end

theorem solution {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    ReciprocityTheory.ChartRestriction.DS.nsq (ReciprocityTheory.ChartRestriction.DS.root a b) = 2 :=
  ReciprocityTheory.ChartRestriction.DS.nsq_root hab
