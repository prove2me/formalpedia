-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_DoubleCosetCovolume_proof_725d3a3e6c3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:55:59.562278+00:00
-- url     : https://prove2.me/submissions/82dbfe82-b455-491a-ba8f-46bd156e7451

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_isOpen_leftCosetSet_d0ad5d875986
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_isCompact_leftCosetSet_882460967c4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_null_3c91a03dca52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_nullMeasurableSet_preimage_prod_48ed4e534389
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_lt_top_261478f0703a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_sliceGroup_67318eca5e77


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
set_option linter.unusedSectionVars false
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace DoubleCosetCovolume
theorem _root_.solution (G G₁ G₂ : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] :
    DoubleCosetCovolume.Statement G G₁ G₂ := by
  intro Φ Γ _ K S hKc hKo hinj hcover hFD μ _
  classical
  let R := doubleCosetSetoid Φ Γ K

  let rep : Quotient R → G₂ := fun q =>
    if h : ∃ t ∈ S, Quotient.mk R t = q then h.choose else 1
  have rep_spec : ∀ t ∈ S, rep (Quotient.mk R t) ∈ S ∧
      Quotient.mk R (rep (Quotient.mk R t)) = Quotient.mk R t := by
    intro t ht
    have h : ∃ t' ∈ S, Quotient.mk R t' = Quotient.mk R t := ⟨t, ht, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec
  let T : Finset (Quotient R) := S.image (Quotient.mk R)
  have hT : ∀ q ∈ T, rep q ∈ S ∧ Quotient.mk R (rep q) = q := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hq
    exact rep_spec t ht

  let F : G₂ → Set G₁ := fun s =>
    if hs : s ∈ S then (hFD s hs (Measure.haar : Measure G₁)).choose else ∅
  have hF : ∀ s ∈ S, IsFundamentalDomain (sliceGroup Φ Γ K s) (F s) Measure.haar ∧
      (Measure.haar : Measure G₁) (F s) < ∞ := by
    intro s hs
    simp only [F, dif_pos hs]
    exact (hFD s hs Measure.haar).choose_spec
  have hVo := isOpen_leftCosetSet hKo
  have hVc := isCompact_leftCosetSet hKc
  let P : G₂ → Set G := fun s => Φ ⁻¹' (F s ×ˢ leftCosetSet K s)
  refine ⟨⋃ q ∈ T, P (rep q), IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_, ?_⟩
  ·
    refine NullMeasurableSet.biUnion T.countable_toSet fun q hq => ?_
    exact nullMeasurableSet_preimage_prod (hVo _) (hVc _) (hF _ (hT q hq).1).1.nullMeasurableSet
  ·
    let Nbad : G₂ → Set G₁ := fun s => {a | ¬ ∃ δ : sliceGroup Φ Γ K s, δ • a ∈ F s}
    let B : Set G := ⋃ η : Γ, ⋃ s ∈ S,
      (fun x => (η : G)⁻¹ * x) ⁻¹' (Φ ⁻¹' (Nbad s ×ˢ leftCosetSet K s))
    have hB : μ B = 0 := by
      refine measure_iUnion_null fun η => ?_
      refine (measure_biUnion_null_iff S.countable_toSet).2 fun s hs => ?_
      rw [measure_preimage_mul]
      exact measure_preimage_prod_null (hVo _) (hVc _) (ae_iff.1 (hF s hs).1.ae_covers)
    refine ae_iff.2 (measure_mono_null ?_ hB)
    intro x hx
    by_contra hxB
    apply hx
    obtain ⟨γ, hγ, t, ht, k, hk, hxt⟩ := hcover (Φ x).2
    have ht' : Quotient.mk R t = Quotient.mk R (Φ x).2 := Quotient.sound ⟨γ, hγ, k, hk, hxt⟩
    obtain ⟨hs, hsq⟩ := rep_spec t ht
    obtain ⟨η, hη, k', hk', hx2⟩ : R (rep (Quotient.mk R t)) (Φ x).2 :=
      Quotient.exact (hsq.trans ht')
    have e2 : (Φ ((η : G)⁻¹ * x)).2 = rep (Quotient.mk R t) * k' := by
      simp [hx2, mul_assoc]
    have hgood : ¬ (Φ ((η : G)⁻¹ * x)).1 ∈ Nbad (rep (Quotient.mk R t)) := by
      intro hbad
      apply hxB
      refine mem_iUnion.2 ⟨⟨η, hη⟩, mem_iUnion₂.2 ⟨_, hs, ?_⟩⟩
      refine ⟨hbad, ?_⟩
      show (rep (Quotient.mk R t))⁻¹ * (Φ ((η : G)⁻¹ * x)).2 ∈ K
      rw [e2, inv_mul_cancel_left]
      exact hk'
    simp only [Nbad, Set.mem_ofPred_eq, not_not] at hgood
    obtain ⟨δ, hδ⟩ := hgood
    obtain ⟨ζ, hζ, hζK, hζ1⟩ := mem_sliceGroup.1 δ.2
    refine ⟨⟨ζ * η⁻¹, Γ.mul_mem hζ (Γ.inv_mem hη)⟩, ?_⟩
    refine mem_iUnion₂.2 ⟨Quotient.mk R t, Finset.mem_image_of_mem _ ht, ?_⟩
    show Φ ((ζ * η⁻¹ : G) * x) ∈ F _ ×ˢ leftCosetSet K _
    rw [mul_assoc, map_mul]
    refine ⟨?_, ?_⟩
    · rw [Prod.fst_mul, hζ1]
      exact hδ
    · show (rep (Quotient.mk R t))⁻¹ * ((Φ ζ).2 * (Φ ((η : G)⁻¹ * x)).2) ∈ K
      rw [e2]
      have : (rep (Quotient.mk R t))⁻¹ * ((Φ ζ).2 * (rep (Quotient.mk R t) * k')) =
          (rep (Quotient.mk R t))⁻¹ * (Φ ζ).2 * rep (Quotient.mk R t) * k' := by
        simp only [mul_assoc]
      rw [this]
      exact K.mul_mem hζK hk'
  ·
    intro g hg
    let M : G₂ → Set G := fun s => ⋃ (h : (Φ g).1 ∈ sliceGroup Φ Γ K s),
      Φ ⁻¹' ((((⟨(Φ g).1, h⟩ : sliceGroup Φ Γ K s) • F s) ∩ F s) ×ˢ leftCosetSet K s)
    have hM : μ (⋃ s ∈ S, M s) = 0 := by
      refine (measure_biUnion_null_iff S.countable_toSet).2 fun s hs => ?_
      refine measure_iUnion_null fun h => ?_
      refine measure_preimage_prod_null (hVo _) (hVc _) ?_
      have hne : (⟨(Φ g).1, h⟩ : sliceGroup Φ Γ K s) ≠ 1 := by
        intro h1
        exact hg (Subtype.ext (hinj g g.2 (congrArg Subtype.val h1)))
      have := (hF s hs).1.aedisjoint hne
      simpa [Function.onFun, AEDisjoint] using this
    refine measure_mono_null ?_ hM
    rintro z ⟨hz1, hz2⟩
    rw [mem_smul_set_iff_inv_smul_mem] at hz1
    obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hz1
    obtain ⟨q', hq', hzq'⟩ := mem_iUnion₂.1 hz2
    have hgz : Φ (g⁻¹ • z) = ((Φ g).1⁻¹ * (Φ z).1, (Φ g).2⁻¹ * (Φ z).2) := by
      rw [Subgroup.smul_def, smul_eq_mul, map_mul]
      simp [Prod.ext_iff]
    obtain ⟨hzF, hzK⟩ := hzq
    obtain ⟨hzF', hzK'⟩ := hzq'
    change (Φ (g⁻¹ • z)).1 ∈ F (rep q) at hzF
    change (Φ (g⁻¹ • z)).2 ∈ leftCosetSet K (rep q) at hzK
    rw [hgz] at hzF hzK
    simp only at hzF hzK
    change (rep q)⁻¹ * ((Φ g).2⁻¹ * (Φ z).2) ∈ K at hzK
    change (rep q')⁻¹ * (Φ z).2 ∈ K at hzK'
    have e1 : Quotient.mk R (rep q) = Quotient.mk R (Φ z).2 :=
      Quotient.sound ⟨g, g.2, _, hzK, by group⟩
    have e2 : Quotient.mk R (rep q') = Quotient.mk R (Φ z).2 :=
      Quotient.sound ⟨1, Γ.one_mem, _, hzK', by simp⟩
    have hqq : q = q' := by
      rw [← (hT q hq).2, ← (hT q' hq').2, e1, e2]
    subst hqq
    have hslice : (Φ g).1 ∈ sliceGroup Φ Γ K (rep q) := by
      refine mem_sliceGroup.2 ⟨g, g.2, ?_, rfl⟩
      have : (rep q)⁻¹ * (Φ g).2 * rep q =
          ((rep q)⁻¹ * (Φ z).2) * ((rep q)⁻¹ * ((Φ g).2⁻¹ * (Φ z).2))⁻¹ := by
        group
      rw [this]
      exact K.mul_mem hzK' (K.inv_mem hzK)
    refine mem_iUnion₂.2 ⟨rep q, (hT q hq).1, mem_iUnion.2 ⟨hslice, ?_⟩⟩
    refine ⟨⟨?_, hzF'⟩, hzK'⟩
    rw [mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
    exact hzF
  ·
    exact fun g => (measurePreserving_smul g μ).quasiMeasurePreserving
  ·
    refine (measure_biUnion_finset_le T _).trans_lt (ENNReal.sum_lt_top.2 fun q hq => ?_)
    exact measure_preimage_prod_lt_top (hVo _) (hVc _) (hF _ (hT q hq).1).2
end DoubleCosetCovolume
end GroundTheory.Heights₂.Heights.FiniteCovolume
