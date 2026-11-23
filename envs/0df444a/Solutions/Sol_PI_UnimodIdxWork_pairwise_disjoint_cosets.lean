-- Prove2me | solution 1 for PI.UnimodIdxWork.pairwise_disjoint_cosets
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:51.87973+00:00
-- url     : https://prove2.me/submissions/96e354ac-bd76-48b9-a49c-2135289b995f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnimodIdx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Pointwise Set Function
noncomputable section
open PI PI.UnimodIdxWork
variable {G : Type} [Group G]
namespace PI.UnimodIdxWork
theorem _root_.solution (A H : Subgroup G) :
    Pairwise (Disjoint on fun q : H ⧸ A.subgroupOf H =>
      ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G)) := by
  intro p q hpq
  refine Set.disjoint_left.mpr ?_
  intro y hy1 hy2
  apply hpq
  obtain ⟨a, ha, ha'⟩ := Set.mem_smul_set.mp hy1
  obtain ⟨b, hb, hb'⟩ := Set.mem_smul_set.mp hy2
  rw [smul_eq_mul] at ha' hb'
  have hpq' : (((p.out : H) : G))⁻¹ * ((q.out : H) : G) = a * b⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, hb', ← ha', inv_mul_cancel_left]
  have hmem : (p.out : H)⁻¹ * (q.out : H) ∈ A.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    push_cast
    rw [hpq']
    exact A.mul_mem (Subgroup.mem_inf.mp ha).1 (A.inv_mem (Subgroup.mem_inf.mp hb).1)
  have key : (QuotientGroup.mk (p.out : H) : H ⧸ A.subgroupOf H) = QuotientGroup.mk (q.out : H) :=
    QuotientGroup.eq.mpr hmem
  rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at key
end PI.UnimodIdxWork
