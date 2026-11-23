-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.sb_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:09.711086+00:00
-- url     : https://prove2.me/submissions/09fd5090-c9c2-4b3a-8950-6599f1dcf973

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_of_mem
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_ind_of_not

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution [IsTopologicalAddGroup V] {φ : V → ℂ} (hφ : SB φ) {L : AddSubgroup V} (hL : IsOpen (L : Set V))
    (hinv : ∀ x, ∀ l ∈ L, φ (x + l) = φ x) : ∃ s : Finset V, φ = ∑ a ∈ s, φ a • ind a L := by
  classical
  have := QuotientAddGroup.discreteTopology hL
  have hfin : ((QuotientAddGroup.mk : V → V ⧸ L) '' tsupport φ).Finite :=
    (hφ.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine ⟨hfin.toFinset.image Quotient.out, funext fun x => ?_⟩
  have hq : ∀ c : V ⧸ L, x - c.out ∈ L ↔ c = QuotientAddGroup.mk x := fun c => by
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq', eq_comm]
  rw [Finset.sum_apply, Finset.sum_image fun a _ b _ h => Quotient.out_injective h]
  simp only [Pi.smul_apply, smul_eq_mul]
  refine Eq.trans ?_ (Finset.sum_eq_single (QuotientAddGroup.mk x : V ⧸ L) (fun c _ hc => ?_) fun hx => ?_).symm
  · have := hinv (QuotientAddGroup.mk x : V ⧸ L).out _ ((hq _).2 rfl)
    rw [add_sub_cancel] at this
    rw [ind_of_mem ((hq _).2 rfl), mul_one, this]
  · rw [ind_of_not (mt (hq c).1 hc), mul_zero]
  · have h0 : φ (QuotientAddGroup.mk x : V ⧸ L).out = 0 := by
      by_contra hne
      exact hx (hfin.mem_toFinset.2 ⟨_, subset_tsupport _ hne, QuotientAddGroup.out_eq' _⟩)
    rw [h0, zero_mul]
end PositivityTheory.PlacePermOperatorBicommutantSpan
