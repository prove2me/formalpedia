-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalGraphMass_image_repr_eq_graph_e6a69d43be56
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:59.449437+00:00
-- url     : https://prove2.me/submissions/92caa247-034c-492e-81cf-220a0cafbd8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.LocalGraphMass
theorem _root_.solution (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I₀ : Finset (Fin n)) {d : ℕ} (hd : I₀.card = d) (Ω : Set (I₀ → ℂ))
    (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)) (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω)
    (hfix : ∀ w ∈ Ω, frameProj b I₀ (g w) = w) :
    ∃ (m : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω' : Set (EuclideanSpace ℂ (Fin d)))
      (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
      IsOpen Ω' ∧ DifferentiableOn ℂ F Ω' ∧ b.repr '' (g '' Ω) = graphPt e F '' Ω' := by
  classical
  let σ : I₀ ≃ Fin d := Fintype.equivFinOfCardEq (by simp [hd])
  let m := Fintype.card {j : Fin n // j ∉ I₀}
  let τ : {j : Fin n // j ∉ I₀} ≃ Fin m := Fintype.equivFin _
  let e : Fin n ≃ Fin d ⊕ Fin m := (Equiv.sumCompl (· ∈ I₀)).symm.trans (Equiv.sumCongr σ τ)
  let P : EuclideanSpace ℂ (Fin d) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i => EuclideanSpace.proj (σ i)
  let Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    (EuclideanSpace.equiv (Fin m) ℂ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k => innerSL ℂ (b (τ.symm k)))
  have hP : ∀ x i, P x i = x (σ i) := fun x i => rfl
  have hQ : ∀ z k, Q z k = inner ℂ (b (τ.symm k)) z := fun z k => rfl
  have hPsurj : Function.Surjective P := fun w =>
    ⟨(EuclideanSpace.equiv (Fin d) ℂ).symm (fun i => w (σ.symm i)), by funext i; simp [hP]⟩
  refine ⟨m, e, P ⁻¹' Ω, Q ∘ g ∘ P, hΩ.preimage P.continuous, ?_, ?_⟩
  · exact Q.differentiable.comp_differentiableOn
      (hg.comp P.differentiable.differentiableOn fun x hx => hx)
  · have key : ∀ x ∈ P ⁻¹' Ω, graphPt e (Q ∘ g ∘ P) x = b.repr (g (P x)) := by
      intro x hx
      have hfx := hfix (P x) hx
      ext j
      by_cases hj : j ∈ I₀
      · have he : e j = Sum.inl (σ ⟨j, hj⟩) := by
          simp [e, Equiv.sumCompl_symm_apply_of_pos hj]
        have := congrFun hfx ⟨j, hj⟩
        simp only [frameProj, hP] at this
        simp [graphPt, he, b.repr_apply_apply, this]
      · have he : e j = Sum.inr (τ ⟨j, hj⟩) := by
          simp [e, Equiv.sumCompl_symm_apply_of_neg hj]
        simp [graphPt, he, b.repr_apply_apply, hQ]
    rw [Set.image_congr key, ← Set.image_image (fun w => b.repr (g w)) P,
      Set.image_preimage_eq Ω hPsurj, Set.image_image]
end GroundTheory.Heights₂.Heights.LocalGraphMass
