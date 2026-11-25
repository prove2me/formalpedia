-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_graphChart_of_frameGraphGeneric_e48f490dadb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:40.226331+00:00
-- url     : https://prove2.me/submissions/be577677-a832-46b1-8287-204f55ead64c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularOffHypersurface
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotientMinimalPrimeAddOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_fin_2badd790bb42


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
open MvPolynomial Filter Topology ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hG : FrameGraphGeneric.Statement) {n e : ℕ}
    (W : Ideal (MvPolynomial (Fin n) ℂ)) (hW : W.IsPrime)
    (he : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = e) :
    ∃ h : MvPolynomial (Fin n) ℂ, h ∉ W ∧ ∀ z ∈ zeroSet W, eval z h ≠ 0 →
      ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin e → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ y ∈ O, A (g y) = y) ∧ zeroSet W ∩ V = g '' O := by
  obtain ⟨I₀, h, hcard, hhW, hreg⟩ := hG n e W hW he (EuclideanSpace.basisFun (Fin n) ℂ)
  let T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
    ((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))
  have hT : ∀ x i, T x i = x i := fun x i => rfl
  have hS : ∀ w i, S w i = w i := fun w i => rfl
  have hST : ∀ x, S (T x) = x := fun x => funext fun i => by rw [hS, hT]
  have hTS : ∀ w, T (S w) = w := fun w => by ext i; rw [hT, hS]
  have hZ : ∀ x : Fin n → ℂ, x ∈ zeroSet W ↔ T x ∈ zeroSetEuc W := by
    intro x
    have hx : (fun i => T x i) = x := funext fun i => hT x i
    simp only [zeroSet, zeroSetEuc, Set.mem_ofPred_eq, hx]
  refine ⟨h, hhW, fun z hz hzh => ?_⟩
  have hzh' : eval (fun i => T z i) h ≠ 0 := by
    have hx : (fun i => T z i) = z := funext fun i => hT z i
    rwa [hx]
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩ := hreg (T z) ((hZ z).mp hz) hzh'
  let eI : I₀ ≃ Fin e := I₀.equivFinOfCardEq hcard
  let Ψ : (Fin e → ℂ) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (eI i)
  let A : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) :=
    ContinuousLinearMap.pi fun k : Fin e =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) ((eI.symm k : I₀) : Fin n)
  have hΨ : ∀ y i, Ψ y i = y (eI i) := fun y i => rfl
  have hA : ∀ x k, A x k = x ((eI.symm k : I₀) : Fin n) := fun x k => rfl
  have hO : IsOpen (Ψ ⁻¹' Ω) := hΩ.preimage Ψ.continuous
  refine ⟨A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩
  · exact IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn
      (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))
  · intro y hy
    ext k
    have h1 := congrFun (hproj (Ψ y) hy) (eI.symm k)
    simp only [frameProj, EuclideanSpace.basisFun_inner] at h1
    show A (S (g (Ψ y))) k = y k
    rw [hA, hS, h1, hΨ, Equiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨hxZ, hxV⟩
      have hmem : T x ∈ zeroSetEuc W ∩ V := ⟨(hZ x).mp hxZ, hxV⟩
      rw [hgraph] at hmem
      obtain ⟨w, hw, hgw⟩ := hmem
      have hΨw : Ψ (fun k => w (eI.symm k)) = w := funext fun i => by simp [hΨ]
      refine ⟨fun k => w (eI.symm k), ?_, ?_⟩
      · show Ψ _ ∈ Ω
        rwa [hΨw]
      · simp only [hΨw, hgw, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (Ψ y) ∈ zeroSetEuc W ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      refine ⟨(hZ _).mpr ?_, ?_⟩
      · rw [hTS]
        exact hmem.1
      · show T (S (g (Ψ y))) ∈ V
        rw [hTS]
        exact hmem.2
end GroundTheory.Heights₂.Heights
