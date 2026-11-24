-- Prove2me | solution 1 for PositivityTheory.ThKF0.FinLine.decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:01.399923+00:00
-- url     : https://prove2.me/submissions/48d25931-f7bf-46f9-bdae-47ad63274ba9

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Filter Topology
open scoped Classical
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.FinLine
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
namespace PositivityTheory.ThKF0.FinLine
theorem _root_.solution {φ : G → ℂ} (hφ : φ ∈ SB G) (U : OpenAddSubgroup G) (hU : ∀ u ∈ U, ∀ x, φ (x + u) = φ x) :
    ∃ t : Finset (G ⧸ U.toAddSubgroup), (∀ q, q ∈ t ↔ φ q.out ≠ 0) ∧ φ = ∑ q ∈ t, φ q.out • ind U q.out := by
  have := QuotientAddGroup.discreteTopology (N := U.toAddSubgroup) U.isOpen
  have hfin : ((QuotientAddGroup.mk : G → G ⧸ U.toAddSubgroup) '' tsupport φ).Finite :=
    (IsCompact.image hφ.2 QuotientAddGroup.continuous_mk).finite_of_discrete
  have hf : {q : G ⧸ U.toAddSubgroup | φ q.out ≠ 0}.Finite :=
    hfin.subset fun q hq => ⟨q.out, subset_tsupport _ hq, QuotientAddGroup.out_eq' q⟩
  refine ⟨hf.toFinset, fun q => hf.mem_toFinset, funext fun y => ?_⟩
  have hind : ∀ q : G ⧸ U.toAddSubgroup, ind U q.out y = if (y : G ⧸ U.toAddSubgroup) = q then 1 else 0 := by
    intro q
    have : (y : G ⧸ U.toAddSubgroup) = q ↔ y - q.out ∈ U := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      exact QuotientAddGroup.eq_iff_sub_mem
    simp only [ind, this]
  have h2 : -y + (y : G ⧸ U.toAddSubgroup).out ∈ U := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
  have h3 := hU _ h2 y
  rw [add_neg_cancel_left] at h3
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  split_ifs with h
  · exact h3.symm
  · rw [← h3]
    by_contra hne
    exact h (hf.mem_toFinset.2 hne)
end PositivityTheory.ThKF0.FinLine
