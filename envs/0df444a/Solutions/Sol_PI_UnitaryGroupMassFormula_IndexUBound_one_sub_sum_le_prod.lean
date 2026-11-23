-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IndexUBound.one_sub_sum_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:37.122279+00:00
-- url     : https://prove2.me/submissions/17dff342-fd59-4274-9010-bed2ca160ce0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexUpperBound_OneSubSumLeProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IndexUBound
open Finset
namespace PI.UnitaryGroupMassFormula.IndexUBound
theorem _root_.solution {ι : Type*} [DecidableEq ι] (s : Finset ι) (P b : ι → ℝ)
    (hP0 : ∀ i ∈ s, 0 ≤ P i) (hP1 : ∀ i ∈ s, P i ≤ 1) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hPb : ∀ i ∈ s, 1 - b i ≤ P i) : 1 - ∑ i ∈ s, b i ≤ ∏ i ∈ s, P i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hm : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have hQ0 : 0 ≤ ∏ i ∈ s, P i := Finset.prod_nonneg fun i hi => hP0 i (hm i hi)
    have hQ1 : ∏ i ∈ s, P i ≤ 1 :=
      Finset.prod_le_one (fun i hi => hP0 i (hm i hi)) (fun i hi => hP1 i (hm i hi))
    have h := ih (fun i hi => hP0 i (hm i hi)) (fun i hi => hP1 i (hm i hi))
      (fun i hi => hb i (hm i hi)) (fun i hi => hPb i (hm i hi))
    have ha1 := hP1 a (Finset.mem_insert_self a s)
    have hab := hPb a (Finset.mem_insert_self a s)
    nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hQ1)]
end PI.UnitaryGroupMassFormula.IndexUBound
