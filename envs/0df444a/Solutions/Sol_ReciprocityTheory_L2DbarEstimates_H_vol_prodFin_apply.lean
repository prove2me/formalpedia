-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.vol_prodFin_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:52:39.582959+00:00
-- url     : https://prove2.me/submissions/ae3fb3ce-7f34-42b1-addd-178e5797c9a2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NeedBergmanClosed
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaOps
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_NearContinuousOfSmoothR
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_OntoWithBoundTop
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_VolProdFinApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
section SlopeTestRemainingChoices
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
private theorem isLocalHomeomorph_fun_prod_fin_fst (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (p : ℕ) : IsLocalHomeomorph (fun q : M × Fin p => z q.1) := by
  have hfst : IsLocalHomeomorph (Prod.fst : M × Fin p → M) := by
    rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
    intro q
    refine ⟨Prod.snd ⁻¹' {q.2}, ((isOpen_discrete _).preimage continuous_snd).mem_nhds (by simp), ?_⟩
    let H : (Prod.snd ⁻¹' {q.2} : Set (M × Fin p)) ≃ₜ M :=
      { toFun := fun u => u.1.1
        invFun := fun x => ⟨(x, q.2), by simp⟩
        left_inv := fun u => by
          obtain ⟨⟨x, j⟩, hj⟩ := u
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hj
          subst hj
          rfl
        right_inv := fun x => rfl
        continuous_toFun := continuous_fst.comp continuous_subtype_val
        continuous_invFun := Continuous.subtype_mk (by fun_prop) fun x => by simp }
    exact H.isOpenEmbedding
  exact hz.comp hfst
end SlopeTestRemainingChoices
end ReciprocityTheory.L2DbarEstimates.H
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    (S : Set (M × Fin p)) (hS : MeasurableSet S) :
    vol n (fun q : M × Fin p => z q.1) S = ∑ i, vol n z ((fun x => (x, i)) ⁻¹' S) := by
  have hzq := isLocalHomeomorph_fun_prod_fin_fst n z hz p
  have hcover : S = ⋃ i, S ∩ Prod.snd ⁻¹' {i} := by
    ext q
    simp
  have hmeas : ∀ i : Fin p, MeasurableSet (S ∩ Prod.snd ⁻¹' {i}) := fun i =>
    hS.inter (measurable_snd (measurableSet_singleton i))
  have hdisj : Pairwise (Function.onFun Disjoint fun i : Fin p => S ∩ Prod.snd ⁻¹' {i}) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro q ⟨_, hi⟩ ⟨_, hj⟩
    exact hij ((Set.mem_singleton_iff.1 hi).symm.trans (Set.mem_singleton_iff.1 hj))
  conv_lhs => rw [hcover]
  rw [measure_iUnion hdisj hmeas, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vol_apply n _ hzq _ (hmeas i),
    vol_apply n z hz _ (hS.preimage (by fun_prop : Measurable fun x : M => (x, i)))]
  unfold volFun
  refine lintegral_congr fun y => ?_
  have hset : (S ∩ Prod.snd ⁻¹' {i}) ∩ (fun q : M × Fin p => z q.1) ⁻¹' {y} =
      (fun x : M => (x, i)) '' ((fun x : M => (x, i)) ⁻¹' S ∩ z ⁻¹' {y}) := by
    ext ⟨x, j⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hxS, rfl⟩, hy⟩
      exact ⟨x, ⟨hxS, hy⟩, rfl, rfl⟩
    · rintro ⟨x', ⟨hxS, hy⟩, rfl, rfl⟩
      exact ⟨⟨hxS, rfl⟩, hy⟩
  rw [hset, Set.InjOn.encard_image (fun a _ b _ h => congrArg Prod.fst h)]
end ReciprocityTheory.L2DbarEstimates.H
