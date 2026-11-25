-- Prove2me | solution 1 for PI.UnimodIdxWork.measure_subgroup_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:16.334454+00:00
-- url     : https://prove2.me/submissions/c96f3a6b-c770-4f9e-989d-b337ce9cdba8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnimodIdx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
import Theorems.Thm_PI_UnimodIdxWork_subgroup_eq_iUnion
import Theorems.Thm_PI_UnimodIdxWork_pairwise_disjoint_cosets

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]
namespace PI.UnimodIdxWork
theorem _root_.solution (μ : Measure G) [IsMulLeftInvariant μ] (A H : Subgroup G)
    (hA : IsOpen (A : Set G)) (hH : IsCompact (H : Set G)) (hHo : IsOpen (H : Set G)) :
    μ H = (A.relIndex H : ENNReal) * μ (A ⊓ H : Subgroup G) := by
  have hAH : IsOpen ((A ⊓ H : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hA.inter hHo
  have hfin : Finite (H ⧸ A.subgroupOf H) := by
    obtain ⟨t, ht⟩ := hH.elim_finite_subcover
      (fun q : H ⧸ A.subgroupOf H => ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G))
      (fun q => hAH.smul _) (subgroup_eq_iUnion A H).subset
    refine Set.finite_univ_iff.mp ((t.finite_toSet).subset fun q _ => ?_)
    have hq : ((q.out : H) : G) ∈ (H : Set G) := (q.out : H).2
    obtain ⟨i, hi, hmem⟩ := Set.mem_iUnion₂.mp (ht hq)
    have hself : ((q.out : H) : G) ∈ ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G) :=
      Set.mem_smul_set.mpr ⟨1, (A ⊓ H).one_mem, by simp⟩
    have hiq : i = q := by
      by_contra hne
      exact Set.disjoint_left.mp (pairwise_disjoint_cosets A H hne) hmem hself
    rw [← hiq]
    exact Finset.mem_coe.mpr hi
  letI := Fintype.ofFinite (H ⧸ A.subgroupOf H)
  have hcard : A.relIndex H = Fintype.card (H ⧸ A.subgroupOf H) := by
    unfold Subgroup.relIndex Subgroup.index
    exact Nat.card_eq_fintype_card
  calc μ (H : Set G)
      = μ (⋃ q : H ⧸ A.subgroupOf H, ((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G)) := by
        rw [← subgroup_eq_iUnion A H]
    _ = ∑' q : H ⧸ A.subgroupOf H, μ (((q.out : H) : G) • ((A ⊓ H : Subgroup G) : Set G)) :=
        measure_iUnion (pairwise_disjoint_cosets A H) fun q => (hAH.smul _).measurableSet
    _ = ∑' _q : H ⧸ A.subgroupOf H, μ ((A ⊓ H : Subgroup G) : Set G) := by
        congr 1; funext q; rw [measure_smul]
    _ = (A.relIndex H : ENNReal) * μ (A ⊓ H : Subgroup G) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
end PI.UnimodIdxWork
