-- Prove2me | solution 1 for WeierstrassProjModel.thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0fab01fa-66f2-5437-8075-4f5790ecbc17

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Limits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

section AbstractHelper

theorem aux_thirdLaw_density {S Y₁ Y₂ Z E : Scheme.{u}}
    (f₁ : Y₁ ⟶ S) (f₂ : Y₂ ⟶ S) (g : Z ⟶ S)
    [IsOpenImmersion f₁] [IsOpenImmersion f₂] [IsOpenImmersion g]
    [IsIntegral S] [Nonempty Z]
    (τ₁ : Y₁ ⟶ E) (τ₂ : Y₂ ⟶ E) (σ : Z ⟶ E)
    [IsSeparated (terminal.from E)]
    (h₁ : pullback.fst f₁ g ≫ τ₁ = pullback.snd f₁ g ≫ σ)
    (h₂ : pullback.fst f₂ g ≫ τ₂ = pullback.snd f₂ g ≫ σ) :
    pullback.fst f₁ f₂ ≫ τ₁ = pullback.snd f₁ f₂ ≫ τ₂ := by
  rcases isEmpty_or_nonempty ↥(pullback f₁ f₂) with hVe | hVne
  · exact (isInitialOfIsEmpty (X := pullback f₁ f₂)).hom_ext _ _
  haveI : IsIntegral ↑(pullback f₁ f₂) :=
    isIntegral_of_isOpenImmersion (pullback.fst f₁ f₂ ≫ f₁)
  let ι : pullback (pullback.fst f₁ f₂ ≫ f₁) g ⟶ pullback f₁ f₂ :=
    pullback.fst (pullback.fst f₁ f₂ ≫ f₁) g
  haveI hW₀ne : Nonempty ↑(pullback (pullback.fst f₁ f₂ ≫ f₁) g) := by
    have hgen_g : genericPoint S ∈ Set.range g.base :=
      ((genericPoint_spec S).mem_open_set_iff (IsOpenImmersion.isOpen_range g)).mpr
        (by rw [Set.univ_inter]; exact Set.range_nonempty _)
    have hgen_V : genericPoint S ∈ Set.range (pullback.fst f₁ f₂ ≫ f₁).base :=
      ((genericPoint_spec S).mem_open_set_iff
        (IsOpenImmersion.isOpen_range (pullback.fst f₁ f₂ ≫ f₁))).mpr
        (by rw [Set.univ_inter]; exact Set.range_nonempty _)
    obtain ⟨v, hv⟩ := hgen_V
    have hvmem : v ∈ Set.range (pullback.fst (pullback.fst f₁ f₂ ≫ f₁) g).base := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hv]; exact hgen_g
    obtain ⟨w, _⟩ := hvmem
    exact ⟨w⟩
  haveI : IsSchemeTheoreticallyDominant ι := by
    haveI : IsDominant ι :=
      ⟨(IsOpenImmersion.isOpen_range ι).dense (Set.range_nonempty ι.base)⟩
    exact IsSchemeTheoreticallyDominant.of_isDominant ι
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated
    (terminal.from E) (Subsingleton.elim _ _) ι ?_
  have hW₀cond : ι ≫ pullback.fst f₁ f₂ ≫ f₁ = pullback.snd (pullback.fst f₁ f₂ ≫ f₁) g ≫ g :=
    pullback.condition
  obtain ⟨α, hα_fst, hα_snd⟩ :
      ∃ α : pullback (pullback.fst f₁ f₂ ≫ f₁) g ⟶ pullback f₁ g,
        α ≫ pullback.fst f₁ g = ι ≫ pullback.fst f₁ f₂
          ∧ α ≫ pullback.snd f₁ g = pullback.snd (pullback.fst f₁ f₂ ≫ f₁) g :=
    ⟨pullback.lift _ _ (by rw [Category.assoc]; exact hW₀cond),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨β, hβ_fst, hβ_snd⟩ :
      ∃ β : pullback (pullback.fst f₁ f₂ ≫ f₁) g ⟶ pullback f₂ g,
        β ≫ pullback.fst f₂ g = ι ≫ pullback.snd f₁ f₂
          ∧ β ≫ pullback.snd f₂ g = pullback.snd (pullback.fst f₁ f₂ ≫ f₁) g :=
    ⟨pullback.lift _ _ (by
        rw [Category.assoc, ← pullback.condition (f := f₁) (g := f₂)]; exact hW₀cond),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  rw [← Category.assoc, ← hα_fst, Category.assoc, h₁, ← Category.assoc, hα_snd,
    ← hβ_snd, Category.assoc, ← h₂, ← Category.assoc, hβ_fst, Category.assoc]

end AbstractHelper

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

scoped instance (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) :
    IsOpenImmersion (kw_lrSixU_locMap W i j l) := by
  unfold kw_lrSixU_locMap; infer_instance

theorem solution
    (i j : Fin 3) [IsDomain ((𝒜 i) ⊗[R] (𝒜 j))]
    (hne : ∃ l, kw_lrSixU W i j l ≠ 0)
    (u₃ : Fin 3 → (𝒜 i) ⊗[R] (𝒜 j))
    (toE₃ : ∀ k : Fin 3,
      Spec (CommRingCat.of (Localization.Away (u₃ k))) ⟶ projModelCR W.toProjective)
    (hcompat₃ : ∀ (k : Fin 3) (l : Fin 3 ⊕ Fin 3),
      pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
          (kw_lrSixU_locMap W i j l)
        ≫ toE₃ k
      = pullback.snd
          (Spec.map (CommRingCat.ofHom
            (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
          (kw_lrSixU_locMap W i j l)
        ≫ kw_lrSixU_toE W i j l)
    (k k' : Fin 3) :
    pullback.fst
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k')))))
      ≫ toE₃ k
    = pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k')))))
      ≫ toE₃ k' := by
  obtain ⟨l₀, hl₀⟩ := hne
  haveI : Nontrivial (Localization.Away (kw_lrSixU W i j l₀)) := by
    rw [← not_subsingleton_iff_nontrivial, IsLocalization.subsingleton_iff
      (M := Submonoid.powers (kw_lrSixU W i j l₀))]
    rintro ⟨n, hn⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp only [h0, pow_zero] at hn; exact one_ne_zero hn
    · exact hl₀ ((pow_eq_zero_iff hpos.ne').mp hn)
  haveI : Nonempty (Spec (CommRingCat.of (Localization.Away (kw_lrSixU W i j l₀)))) :=
    inferInstance
  haveI : IsSeparated (terminal.from (projModelCR W.toProjective)) := by
    rw [show terminal.from (projModelCR W.toProjective)
        = projModelStrCR W.toProjective ≫ terminal.from _ from Subsingleton.elim _ _]
    infer_instance
  haveI : IsIntegral (Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j)))) := inferInstance
  exact aux_thirdLaw_density
    (Spec.map (CommRingCat.ofHom (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k)))))
    (Spec.map (CommRingCat.ofHom (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (u₃ k')))))
    (kw_lrSixU_locMap W i j l₀)
    (toE₃ k) (toE₃ k') (kw_lrSixU_toE W i j l₀)
    (hcompat₃ k l₀) (hcompat₃ k' l₀)

end

end S_WeierstrassProjModel_thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat
end P2MW
export P2MW.S_WeierstrassProjModel_thirdLaw_selfCompat_of_isDomain_of_lrSixU_compat (solution)
