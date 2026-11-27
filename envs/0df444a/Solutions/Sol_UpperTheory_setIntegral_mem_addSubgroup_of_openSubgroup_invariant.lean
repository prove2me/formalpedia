-- Prove2me | solution 1 for UpperTheory.setIntegral_mem_addSubgroup_of_openSubgroup_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:40:33.990153+00:00
-- url     : https://prove2.me/submissions/b76d3a14-6091-44fd-8715-42c19d55b72a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledIntegerPeriodic
import Definitions.Def_Development_AutomorphicArithmetic_DivisorFrames_SetIntegralMemAddSubgroupOfOpenSubgroupInvariant
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise
namespace UpperTheory
theorem _root_.solution :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulRightInvariant] (J : Subgroup G), IsOpen (J : Set G) → μ (J : Set G) = 1 → ∀ S : Set G, IsCompact S → (∀ j ∈ J, ∀ g ∈ S, j * g ∈ S) → ∀ f : G → ℂ, (∀ j ∈ J, ∀ g, f (j * g) = f g) → ∀ M : AddSubgroup ℂ, (∀ g ∈ S, f g ∈ M) → ∫ g in S, f g ∂μ ∈ M := by
  intro G _ _ _ _ _ μ _ J hJ hμ S hS hSJ f hf M hM
  classical
  let C : G → Set G := fun a => (fun x => x * a⁻¹) ⁻¹' (J : Set G)
  have hCo : ∀ a, IsOpen (C a) := fun a => hJ.preimage (continuous_id.mul continuous_const)
  have hCμ : ∀ a, μ (C a) = 1 := fun a => by
    simp only [C]; rw [measure_preimage_mul_right, hμ]
  have hCf : ∀ a, Set.EqOn f (fun _ => f a) (C a) := fun a x hx => by
    have := hf (x * a⁻¹) hx a
    rw [inv_mul_cancel_right] at this
    exact this
  have hCi : ∀ a, IntegrableOn f (C a) μ := fun a => by
    refine IntegrableOn.congr_fun ?_ (hCf a).symm (hCo a).measurableSet
    exact integrableOn_const (by rw [hCμ]; simp)
  have hCint : ∀ a, ∫ g in C a, f g ∂μ = f a := fun a => by
    rw [setIntegral_congr_fun (hCo a).measurableSet (hCf a), setIntegral_const]
    simp [Measure.real, hCμ]
  have key : ∀ t : Finset G, (∀ g ∈ t, f g ∈ M) →
      IntegrableOn f (⋃ g ∈ t, C g) μ ∧ ∫ g in ⋃ g ∈ t, C g, f g ∂μ ∈ M := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp
    | insert a t ha ih =>
      intro h
      obtain ⟨h1, h2⟩ := ih fun g hg => h g (Finset.mem_insert_of_mem hg)
      rw [Finset.set_biUnion_insert]
      refine ⟨(hCi a).union h1, ?_⟩
      by_cases hd : Disjoint (C a) (⋃ g ∈ t, C g)
      · rw [setIntegral_union hd
          (isOpen_biUnion fun g _ => hCo g).measurableSet (hCi a) h1, hCint]
        exact M.add_mem (h a (Finset.mem_insert_self _ _)) h2
      · rw [Set.not_disjoint_iff] at hd
        obtain ⟨x, hx1, hx2⟩ := hd
        simp only [Set.mem_iUnion] at hx2
        obtain ⟨b, hb, hxb⟩ := hx2
        have hsub : C a ⊆ ⋃ g ∈ t, C g := by
          intro y hy
          simp only [Set.mem_iUnion]
          refine ⟨b, hb, ?_⟩
          have := J.mul_mem (J.mul_mem hy (J.inv_mem hx1)) hxb
          show y * b⁻¹ ∈ (J : Set G)
          simpa [mul_assoc] using this
        rw [Set.union_eq_self_of_subset_left hsub]
        exact h2
  obtain ⟨t, ht, hcov⟩ := hS.elim_nhds_subcover C (fun x _ => (hCo x).mem_nhds (by
    show x * x⁻¹ ∈ (J : Set G)
    simp))
  have hEq : S = ⋃ g ∈ t, C g := by
    refine Set.Subset.antisymm hcov ?_
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨b, hb, hyb⟩ := hy
    have := hSJ _ hyb b (ht b hb)
    simpa using this
  rw [hEq]
  exact (key t fun g hg => hM g (ht g hg)).2
end UpperTheory
