-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_WWRatioBasis_proof_5b4ea3f75b4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:01:43.039525+00:00
-- url     : https://prove2.me/submissions/b57508c2-72ba-4e99-8199-f84771ccae9c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StWWRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsAlgebraicMapAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PWWRatioBasis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RatioField_det_ne_zero_6f39006dc751
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RatioField_isAlgebraic_map_adjoin_2b59eaf5fe04
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RatioField_lineVal_cramer_594cefa83bd9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RatioField_map_mem_8496003472e3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace WWRatioBasis
theorem _root_.solution (hM : MobiusAlgIndep.Statement) : WWRatioBasis.Statement := by
  intro Ω _ _ ι ν κ _ _ _ E _ _ Φ _ _ _ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF hxt hδ hδF hφ hgF hg ha
  obtain ⟨hden, hr⟩ := hM Ω Φ 2 a (φ k₁ (e 0)) (φ k₁ (e 1)) (φ k₀ (e 0)) (φ k₀ (e 1)) ha
    (RatioField.det_ne_zero e b φ g (x i₀) hx k₀ k₁ hφ hg)
  set F := IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)
  set W := T.wwCoord x δ e φ (a 0) (a 1)
  let c : ∀ k, T.wwIdx ι ν κ k := fun k => T.WBlk.casesOn (motive := fun k => T.wwIdx ι ν κ k) k i₀ l₀ k₀ k₀
  let r : Fin 2 → Φ := fun j => T.lineVal e (φ k₁) (a j) / T.lineVal e (φ k₀) (a j)
  let t' : Fin (d + 2) → Φ := fun n => Sum.elim (fun m => algebraMap Ω Φ (t m)) r (finSumFinEquiv.symm n)
  have ht'n : ∀ m, algebraMap Ω Φ (t m) ∈ Set.range t' := fun m =>
    ⟨finSumFinEquiv (Sum.inl m), by simp [t']⟩
  have hr' : ∀ j, r j ∈ Set.range t' := fun j => ⟨finSumFinEquiv (Sum.inr j), by simp [t']⟩
  have hrC : ∀ j, r j ∈ coneRatios W c := fun j => by
    fin_cases j
    exacts [⟨⟨.line0, k₁⟩, rfl⟩, ⟨⟨.line1, k₁⟩, rfl⟩]

  have hline : ∀ (L : IntermediateField ℚ Φ), (∀ z ∈ F, algebraMap Ω Φ z ∈ L) → (∀ j, r j ∈ L) →
      ∀ j k, T.lineVal e (φ k) (a j) / T.lineVal e (φ k₀) (a j) ∈ L := by
    intro L hF hrL j k
    have hgF' : ∀ k q, g k q ∈ F := hgF
    rw [RatioField.lineVal_cramer e b φ g (x i₀) k₀ k₁ k hφ hg, add_div, mul_div_assoc,
      mul_div_assoc, div_self (show T.lineVal e (φ k₀) (a j) ≠ 0 from hden j)]
    refine L.add_mem (L.mul_mem (hF _ ?_) (L.one_mem)) (L.mul_mem (hF _ ?_) (hrL j)) <;>
      exact F.div_mem (F.sub_mem (F.mul_mem (hgF' _ _) (hgF' _ _)) (F.mul_mem (hgF' _ _) (hgF' _ _)))
        (F.sub_mem (F.mul_mem (hgF' _ _) (hgF' _ _)) (F.mul_mem (hgF' _ _) (hgF' _ _)))

  have hcases : ∀ (L : IntermediateField ℚ Φ), (∀ z ∈ F, algebraMap Ω Φ z ∈ L) → (∀ j, r j ∈ L) →
      ∀ y ∈ coneRatios W c, y ∈ L := by
    rintro L hF hrL _ ⟨⟨blk, i⟩, rfl⟩
    cases blk
    · simpa [W, c, T.wwCoord, map_div₀] using hF _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    · simpa [W, c, T.wwCoord, map_div₀] using hF _ (hδF i)
    · exact hline L hF hrL 0 i
    · exact hline L hF hrL 1 i
  refine ⟨c, t', fun k => ?_, ?_, fun n => ?_, fun y hy => ?_⟩
  · cases k
    exacts [(map_ne_zero _).mpr hx, (map_ne_zero _).mpr hδ, hden 0, hden 1]
  · have hti : AlgebraicIndependent ℚ fun m => algebraMap Ω Φ (t m) :=
      ht.map' (f := (algebraMap Ω Φ).toRatAlgHom) (algebraMap Ω Φ).injective
    refine (algebraicIndependent_equiv' (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)) ?_).mpr
      (hti.sumElim_of_tower (S := Ω) (by rintro _ ⟨m, rfl⟩; exact ⟨t m, rfl⟩) hr)
    funext n
    simp only [Function.comp, Equiv.trans_apply, t']
    cases finSumFinEquiv.symm n <;> rfl
  · have hbase : ∀ z ∈ F, algebraMap Ω Φ z ∈ IntermediateField.adjoin ℚ (coneRatios W c) :=
      fun z hz => RatioField.map_mem (S := Set.range fun j => x j / x i₀) (fun w hw => by
        obtain ⟨j, rfl⟩ := hw
        exact IntermediateField.subset_adjoin _ _ ⟨⟨.base, j⟩, by simp [W, c, T.wwCoord, map_div₀]⟩) hz
    obtain ⟨m | j, rfl⟩ := finSumFinEquiv.surjective n
    · simpa [t'] using hbase _ (htF m)
    · simpa [t'] using IntermediateField.subset_adjoin _ _ (hrC j)
  · have hL := hcases ((algebraicClosure (IntermediateField.adjoin ℚ (Set.range t')) Φ).restrictScalars ℚ)
      (fun z hz => (IntermediateField.mem_restrictScalars ℚ).mpr (mem_algebraicClosure_iff.mpr
        (RatioField.isAlgebraic_map_adjoin (S := Set.range fun j => x j / x i₀) ht
          (fun w hw => by obtain ⟨j, rfl⟩ := hw; exact hxt j) ht'n hz)))
      (fun j => (IntermediateField.mem_restrictScalars ℚ).mpr (mem_algebraicClosure_iff.mpr
        (isAlgebraic_algebraMap (⟨r j, IntermediateField.subset_adjoin _ _ (hr' j)⟩ :
          IntermediateField.adjoin ℚ (Set.range t'))))) y hy
    exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars ℚ).mp hL)
end WWRatioBasis
end GroundTheory.Heights₂.Heights.Inter
