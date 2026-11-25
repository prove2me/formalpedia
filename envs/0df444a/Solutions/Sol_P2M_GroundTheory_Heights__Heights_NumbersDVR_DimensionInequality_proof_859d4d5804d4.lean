-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DimensionInequality_proof_859d4d5804d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:17.963832+00:00
-- url     : https://prove2.me/submissions/1ec00cc4-65bd-4b65-9b1f-952f0647d2f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequalitySteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimensionInequality
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimensionInequality_tower_step_cfa42bc38561

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
universe u v
open Cardinal
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace DimensionInequality
theorem _root_.solution (h₁ : DimensionInequalityOneGenerator.Statement.{u, v})
    (h₂ : DimensionInequalityOneGenerator.Statement.{v, v}) :
    DimensionInequality.Statement.{u, v} := by
  classical
  intro A B _ _ _ _ _ _ _ hinj P _

  suffices key : ∀ (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [Algebra A B] (x : Fin n → B),
      Algebra.adjoin A (Set.range x) = ⊤ → Function.Injective (algebraMap A B) →
      ∀ (P : Ideal B) [P.IsPrime] (p : Ideal A) [p.IsPrime] [P.LiesOver p],
        ofENat P.height + Algebra.trdeg (A ⧸ p) (B ⧸ P) ≤ ofENat p.height + Algebra.trdeg A B by
    obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
    refine key s.card B (fun i ↦ (s.equivFin.symm i : B)) ?_ hinj P (P.under A)
    rw [← hs]
    congr 1
    ext b
    refine ⟨?_, fun hb ↦ ⟨s.equivFin ⟨b, hb⟩, by simp⟩⟩
    rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  intro n
  induction n with
  | zero =>
    intro B _ _ _ x hx hinj P _ p _ _
    obtain rfl : p = P.under A := Ideal.LiesOver.over
    refine h₁ A B 0 ?_ hinj P
    rw [eq_top_iff, ← hx]
    exact Algebra.adjoin_mono (by simp [Set.range_eq_empty])
  | succ n ih =>
    intro B _ _ _ x hx hinj P _ p _ _
    set C : Subalgebra A B := Algebra.adjoin A (Set.range (x ∘ Fin.succ)) with hC
    let y : Fin n → C := fun i ↦ ⟨x i.succ, Algebra.subset_adjoin ⟨i, rfl⟩⟩
    have hy : Algebra.adjoin A (Set.range y) = ⊤ := by
      apply Subalgebra.map_injective (f := C.val) Subtype.val_injective
      rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]
      rfl
    have hAC : Function.Injective (algebraMap A C) := fun a b hab ↦
      hinj (congrArg Subtype.val hab :)
    have hCB : Function.Injective (algebraMap C B) := Subtype.val_injective
    have : Algebra.FiniteType A C :=
      ⟨⟨Finset.univ.image y, by simpa [Finset.coe_image] using hy⟩⟩
    have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
    have hB : Algebra.adjoin C {x 0} = ⊤ := by
      apply Subalgebra.restrictScalars_injective A
      rw [Subalgebra.restrictScalars_top, ← Algebra.adjoin_union_eq_adjoin_adjoin, eq_top_iff, ← hx]
      apply Algebra.adjoin_mono
      rintro _ ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero => exact Or.inr rfl
      | succ j => exact Or.inl ⟨j, rfl⟩
    have : (P.under C).LiesOver p := Ideal.LiesOver.tower_bot P (P.under C) p
    exact DimensionInequality.tower_step hAC hCB P (P.under C) p
      (ih C y hy hAC (P.under C) p) (h₂ C B (x 0) hB hCB P)
end DimensionInequality
end GroundTheory.Heights₂.Heights.NumbersDVR
