-- Prove2me | solution 1 for PI.UnimodIdxWork.subgroup_eq_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:52.351475+00:00
-- url     : https://prove2.me/submissions/a32cecc3-d502-4c78-8d69-3be60e770e7d

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
    (H : Set G) = ⋃ q : H ⧸ A.subgroupOf H, ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G) := by
  ext y
  simp only [Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · intro hy
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (A.subgroupOf H) (⟨y, hy⟩ : H)
    refine ⟨(QuotientGroup.mk (⟨y, hy⟩ : H) : H ⧸ A.subgroupOf H),
      Set.mem_smul_set.mpr ⟨(((QuotientGroup.mk (⟨y, hy⟩ : H) : H ⧸ A.subgroupOf H).out : H) : G)⁻¹ * y,
        ?_, by simp [smul_eq_mul]⟩⟩
    have hG : (((QuotientGroup.mk (⟨y, hy⟩ : H) : H ⧸ A.subgroupOf H).out : H) : G)
        = y * ((h : H) : G) := by
      have := congrArg (fun x : H => (x : G)) hh
      simpa using this
    have hA : ((h : H) : G) ∈ A := Subgroup.mem_subgroupOf.mp h.2
    have hH : ((h : H) : G) ∈ H := (h : H).2
    rw [hG, mul_inv_rev, inv_mul_cancel_right]
    exact (SetLike.mem_coe).mpr (Subgroup.mem_inf.mpr ⟨A.inv_mem hA, H.inv_mem hH⟩)
  · rintro ⟨q, hq⟩
    obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hq
    have hz' : z ∈ A ⊓ H := hz
    exact H.mul_mem (q.out : H).2 (Subgroup.mem_inf.mp hz').2
end PI.UnimodIdxWork
