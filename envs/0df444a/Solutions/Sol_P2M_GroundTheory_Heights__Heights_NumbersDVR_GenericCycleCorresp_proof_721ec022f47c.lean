-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_proof_721ec022f47c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:42.385644+00:00
-- url     : https://prove2.me/submissions/fbd73d6c-c4c8-4359-b619-43637ae9e9ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_length_eq_71c9a88ca5af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_disjoint_nonZeroDivisors_549f4b0b165b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace GenericCycleCorresp
theorem _root_.solution : GenericCycleCorresp.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P s _ _ _ n
  classical
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C (σ := (Σ k, ι k)) (R := O))
  have hgen : ∀ W : Ideal (MRing ι O),
      genFib W = W.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))) := fun _ => rfl
  set J := P ⊔ Ideal.span {s}
  set s' := MvPolynomial.map (algebraMap O (FractionRing O)) s
  have hJ : genFib P ⊔ Ideal.span {s'} =
      J.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    rfl
  have hϖM : (C ϖ : MRing ι O) ∈ M := ⟨ϖ, mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero, rfl⟩
  have hcorr : ∀ W : Ideal (MRing ι O), W.IsPrime → (C ϖ : MRing ι O) ∉ W →
      (genFib W).IsPrime ∧
        (genFib W).comap (algebraMap (MRing ι O) (MRing ι (FractionRing O))) = W := by
    intro W hWp hWϖ
    have hd := GenericCycleCorresp.disjoint_nonZeroDivisors hϖ W hWϖ
    exact ⟨IsLocalization.isPrime_of_isPrime_disjoint M _ W hWp hd,
      IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O)) hWp hd⟩
  have hmin : ∀ W : Ideal (MRing ι O), W ∈ J.minimalPrimes → (C ϖ : MRing ι O) ∉ W →
      genFib W ∈ (genFib P ⊔ Ideal.span {s'}).minimalPrimes := by
    intro W hWm hWϖ
    rw [hJ, IsLocalization.minimalPrimes_map M]
    show (genFib W).comap (algebraMap (MRing ι O) (MRing ι (FractionRing O))) ∈ J.minimalPrimes
    rw [(hcorr W hWm.1.1 hWϖ).2]
    exact hWm
  have hkey : ∀ W : Ideal (MRing ι O), W ∈ J.minimalPrimes → (C ϖ : MRing ι O) ∉ W →
      divCycle P s W = divCycle (genFib P) s' (genFib W) := by
    intro W hWm hWϖ
    haveI hWp : W.IsPrime := hWm.1.1
    obtain ⟨hWp', hcomap⟩ := hcorr W hWp hWϖ
    have hrel : IsRelevant (genFib W) ↔ IsRelevant W := by
      refine forall_congr' fun k => exists_congr fun i => not_congr ?_
      have hX : (X ⟨k, i⟩ : MRing ι (FractionRing O)) =
          algebraMap (MRing ι O) (MRing ι (FractionRing O)) (X ⟨k, i⟩) := (MvPolynomial.map_X _ _).symm
      rw [hX, ← Ideal.mem_comap, hcomap]
    have hl : ∀ (h₁ : W.IsPrime) (h₂ : (genFib W).IsPrime),
        @multAt _ _ _ _ J W h₁ = @multAt _ _ _ _ (genFib P ⊔ Ideal.span {s'}) (genFib W) h₂ := by
      intro h₁ h₂
      unfold multAt
      rw [hJ]
      haveI : (W.map (algebraMap (MRing ι O) (MRing ι (FractionRing O)))).IsPrime := h₂
      exact GenericCycleCorresp.length_eq M J W
        (GenericCycleCorresp.disjoint_nonZeroDivisors hϖ W hWϖ)
    unfold divCycle
    by_cases hr : IsRelevant W
    · rw [dif_pos ⟨hWm, hr⟩, dif_pos ⟨hmin W hWm hWϖ, hrel.mpr hr⟩, hl]
    · rw [dif_neg (fun h => hr h.2), dif_neg (fun h => hr (hrel.mp h.2))]
  have hsupp : ∀ (Q : Ideal (MRing ι (FractionRing O))) (x) (W : Ideal (MRing ι (FractionRing O))),
      divCycle Q x W ≠ 0 → W ∈ (Q ⊔ Ideal.span {x}).minimalPrimes := by
    intro Q x W h
    unfold divCycle at h
    split_ifs at h with hh
    · exact hh.1
    · exact absurd rfl h
  have hsupp0 : ∀ W : Ideal (MRing ι O), divCycle P s W ≠ 0 → W ∈ J.minimalPrimes := by
    intro W h
    unfold divCycle at h
    split_ifs at h with hh
    · exact hh.1
    · exact absurd rfl h
  unfold cycEval
  let A : Set (Ideal (MRing ι O)) := {W | W ∈ J.minimalPrimes ∧ (C ϖ : MRing ι O) ∉ W}
  let B : Set (Ideal (MRing ι (FractionRing O))) := (genFib P ⊔ Ideal.span {s'}).minimalPrimes
  have hA : (∑ᶠ W, divCycle P s W * (if (C ϖ : MRing ι O) ∈ W then 0 else n (genFib W))) =
      ∑ᶠ W ∈ A, divCycle P s W * (if (C ϖ : MRing ι O) ∈ W then 0 else n (genFib W)) := by
    rw [finsum_mem_def]
    congr 1
    funext W
    symm
    rw [Set.indicator_apply_eq_self]
    intro hW
    by_cases hϖW : (C ϖ : MRing ι O) ∈ W
    · rw [if_pos hϖW, mul_zero]
    · have : divCycle P s W = 0 := by
        by_contra h
        exact hW ⟨hsupp0 W h, hϖW⟩
      rw [this, zero_mul]
  have hB : (∑ᶠ W, divCycle (genFib P) s' W * n W) = ∑ᶠ W ∈ B, divCycle (genFib P) s' W * n W := by
    rw [finsum_mem_def]
    congr 1
    funext W
    symm
    rw [Set.indicator_apply_eq_self]
    intro hW
    have : divCycle (genFib P) s' W = 0 := by
      by_contra h
      exact hW (hsupp _ _ W h)
    rw [this, zero_mul]
  rw [hA, hB]
  refine finsum_mem_eq_of_bijOn genFib ⟨?_, ?_, ?_⟩ ?_
  · intro W hW
    exact hmin W hW.1 hW.2
  · intro W₁ hW₁ W₂ hW₂ h
    rw [← (hcorr W₁ hW₁.1.1.1 hW₁.2).2, ← (hcorr W₂ hW₂.1.1.1 hW₂.2).2]
    exact congrArg _ h
  · intro W' hW'
    have hW'p : W'.IsPrime := hW'.1.1
    have hW'm := hW'
    change W' ∈ (genFib P ⊔ Ideal.span {s'}).minimalPrimes at hW'm
    rw [hJ, IsLocalization.minimalPrimes_map M] at hW'm
    refine ⟨W'.comap (algebraMap (MRing ι O) (MRing ι (FractionRing O))), ⟨hW'm, ?_⟩, ?_⟩
    · intro h
      rw [Ideal.mem_comap] at h
      exact hW'p.ne_top (Ideal.eq_top_of_isUnit_mem _ h
        (IsLocalization.map_units (MRing ι (FractionRing O)) (⟨_, hϖM⟩ : M)))
    · exact IsLocalization.map_under M (MRing ι (FractionRing O)) W'
  · intro W hW
    rw [if_neg hW.2, hkey W hW.1 hW.2]
end GenericCycleCorresp
end GroundTheory.Heights₂.Heights.NumbersDVR
