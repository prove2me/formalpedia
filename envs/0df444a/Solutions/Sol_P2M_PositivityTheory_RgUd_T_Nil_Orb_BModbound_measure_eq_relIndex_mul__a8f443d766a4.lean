-- Prove2me | solution 1 for P2M_PositivityTheory_RgUd_T_Nil_Orb_BModbound_measure_eq_relIndex_mul__a8f443d766a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:47:45.401769+00:00
-- url     : https://prove2.me/submissions/8bcc904d-62e8-4c60-bf03-eda54b74b464

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_HaarMeasureGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module ValuativeRel MeasureTheory
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound
namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound
theorem _root_.solution (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G) (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) (hi : H.relIndex K ≠ 0) :
    μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by
  classical
  have hfi : (H.addSubgroupOf K).FiniteIndex := ⟨hi⟩
  haveI : Finite (K ⧸ H.addSubgroupOf K) := AddSubgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K ⧸ H.addSubgroupOf K) := Fintype.ofFinite _
  let c : (K ⧸ H.addSubgroupOf K) → Set G :=
    fun q => (fun x => -((Quotient.out q : K) : G) + x) ⁻¹' (H : Set G)
  have hmem : ∀ q x, x ∈ c q ↔ -((Quotient.out q : K) : G) + x ∈ H := fun q x => Iff.rfl
  have hU : (K : Set G) = ⋃ q ∈ (Finset.univ : Finset (K ⧸ H.addSubgroupOf K)), c q := by
    ext x
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨QuotientAddGroup.mk (⟨x, hx⟩ : K), ?_⟩
      rw [hmem]
      have h1 : ((Quotient.out (QuotientAddGroup.mk (⟨x, hx⟩ : K) : K ⧸ H.addSubgroupOf K) : K) :
          K ⧸ H.addSubgroupOf K) = QuotientAddGroup.mk (⟨x, hx⟩ : K) := QuotientAddGroup.out_eq' _
      have h2 := QuotientAddGroup.eq.1 h1
      simpa [AddSubgroup.mem_addSubgroupOf] using h2
    · rintro ⟨q, hq⟩
      have h1 : -((Quotient.out q : K) : G) + x ∈ K := hHK ((hmem q x).1 hq)
      have h2 := K.add_mem (Quotient.out q : K).2 h1
      simpa using h2
  have hd : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (K ⧸ H.addSubgroupOf K))) c := by
    intro q _ q' _ hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    have h1 := (hmem q x).1 hx
    have h2 := (hmem q' x).1 hx'
    have h3 : -((Quotient.out q : K) : G) + ((Quotient.out q' : K) : G) ∈ H := by
      have := H.add_mem h1 (H.neg_mem h2)
      simpa [add_assoc] using this
    have h4 : ((Quotient.out q : K) : K ⧸ H.addSubgroupOf K) = (Quotient.out q' : K) := by
      apply QuotientAddGroup.eq.2
      simpa [AddSubgroup.mem_addSubgroupOf] using h3
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h4
  have hm : ∀ q ∈ (Finset.univ : Finset (K ⧸ H.addSubgroupOf K)), MeasurableSet (c q) :=
    fun q _ => (measurable_const_add _) hH
  have hμ : ∀ q, μ (c q) = μ (H : Set G) := fun q =>
    MeasureTheory.measure_preimage_add μ _ _
  rw [hU, MeasureTheory.measure_biUnion_finset hd hm]
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
end PositivityTheory.RgUd.T.Nil.Orb.BModbound
