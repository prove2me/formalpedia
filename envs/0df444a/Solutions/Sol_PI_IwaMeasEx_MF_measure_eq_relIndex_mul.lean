-- Prove2me | solution 1 for PI.IwaMeasEx.MF.measure_eq_relIndex_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:44:15.753147+00:00
-- url     : https://prove2.me/submissions/c5f220b7-1cd8-49df-8ac7-202154403bc6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IwasawaMeasureExistence_MeasureEqRelIndexMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IwaMeasEx PI.IwaMeasEx.MF
open MeasureTheory Measure Set
open scoped ENNReal NNReal
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
namespace PI.IwaMeasEx.MF
theorem _root_.solution (μ : Measure G) [IsMulLeftInvariant μ] {U W : Subgroup G} (hWU : W ≤ U)
    (hU : MeasurableSet (U : Set G)) (hW : MeasurableSet (W : Set G)) (hfin : W.relIndex U ≠ 0) :
    μ U = W.relIndex U * μ W := by
  classical
  have hcard : Nat.card (U ⧸ W.subgroupOf U) = W.relIndex U := rfl
  haveI : Finite (U ⧸ W.subgroupOf U) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hfin)
  letI : Fintype (U ⧸ W.subgroupOf U) := Fintype.ofFinite _
  choose r hr using fun q : U ⧸ W.subgroupOf U => QuotientGroup.mk_surjective q
  have hC : (U : Set G) = ⋃ q, (fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk (⟨x, hx⟩ : U) : U ⧸ W.subgroupOf U), ?_⟩
      have h := QuotientGroup.eq.mp (hr (QuotientGroup.mk (⟨x, hx⟩ : U)))
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    · rintro ⟨q, hq⟩
      have e : x = ((r q : U) : G) * (((r q : U) : G)⁻¹ * x) := by group
      rw [e]
      exact U.mul_mem (r q).2 (hWU hq)
  have hdisj : Pairwise (Function.onFun Disjoint fun q => (fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G)) := by
    intro q q' hne
    change Disjoint ((fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G))
      ((fun x => ((r q' : U) : G)⁻¹ * x) ⁻¹' (W : Set G))
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    apply hne
    simp only [Set.mem_preimage, SetLike.mem_coe] at hx hx'
    rw [← hr q, ← hr q']
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have key : ((r q : U) : G)⁻¹ * ((r q' : U) : G) ∈ W := by
      have e : ((r q : U) : G)⁻¹ * ((r q' : U) : G) =
          (((r q : U) : G)⁻¹ * x) * (((r q' : U) : G)⁻¹ * x)⁻¹ := by group
      rw [e]
      exact W.mul_mem hx (W.inv_mem hx')
    simpa using key
  have hmeas : ∀ q, MeasurableSet ((fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G)) :=
    fun q => hW.preimage (measurable_const_mul _)
  have hval : ∀ q, μ ((fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G)) = μ W :=
    fun q => measure_preimage_mul μ _ _
  have hfc : (Fintype.card (U ⧸ W.subgroupOf U) : ℝ≥0∞) = (W.relIndex U : ℝ≥0∞) := by
    rw [← Nat.card_eq_fintype_card, hcard]
  rw [hC, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hfc]
end PI.IwaMeasEx.MF
