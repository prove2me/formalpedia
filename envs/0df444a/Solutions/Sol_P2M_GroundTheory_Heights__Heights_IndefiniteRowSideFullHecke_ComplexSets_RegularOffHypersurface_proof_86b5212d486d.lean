-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RegularOffHypersurface_proof_86b5212d486d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:15.635053+00:00
-- url     : https://prove2.me/submissions/233d5494-db36-4921-ac95-51c3d0d643b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularOffHypersurface
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_ringKrullDim_quotient_eq_nat_0ca07877d78b
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace RegularOffHypersurface
theorem _root_.solution (hG : FrameGraphGeneric.Statement) : RegularOffHypersurface.Statement := by
  intro σ _ I hI
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm
  set J : Ideal (MvPolynomial (Fin n) ℂ) := I.comap φ
  have hJ : J.IsPrime := Ideal.IsPrime.comap _
  have hφ : ∀ (x : σ → ℂ) (q : MvPolynomial (Fin n) ℂ), eval x (φ q) = eval (x ∘ e.symm) q := fun x q => by
    simp [φ, eval_rename]
  obtain ⟨d, hd⟩ := exists_ringKrullDim_quotient_eq_nat J hJ
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, q, hcard, hqJ, hreg⟩ := hG n d J hJ hd b

  let T : (σ → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
      (ContinuousLinearMap.pi fun i : Fin n => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm i))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (σ → ℂ) :=
    (ContinuousLinearMap.pi fun s : σ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (e s)).comp
      ((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))
  have hT : ∀ x i, T x i = x (e.symm i) := fun x i => rfl
  have hS : ∀ w s, S w s = w (e s) := fun w s => rfl
  have hST : ∀ x, S (T x) = x := fun x => funext fun s => by simp [hS, hT]
  have hTS : ∀ w, T (S w) = w := fun w => by ext i; simp [hS, hT]
  have hZ : ∀ x : σ → ℂ, x ∈ zeroSetIn I ↔ T x ∈ zeroSetEuc J := by
    intro x
    have hx : (fun i => T x i) = x ∘ e.symm := rfl
    simp only [zeroSetIn, zeroSetEuc, Set.mem_ofPred_eq, hx]
    constructor
    · intro h p hp
      rw [← hφ]
      exact h _ (Ideal.mem_comap.mp hp)
    · intro h p hp
      have := h (φ.symm p) (by simpa [J, Ideal.mem_comap] using hp)
      rwa [← hφ, AlgEquiv.apply_symm_apply] at this
  refine ⟨φ q, fun h => hqJ (Ideal.mem_comap.mpr h), ?_⟩
  intro z hz hzh
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩ :=
    hreg (T z) ((hZ z).mp hz) (by rwa [hφ] at hzh)
  let eI : I₀ ≃ Fin d := I₀.equivFinOfCardEq hcard
  let Ψ : (Fin d → ℂ) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (eI i)
  let A : (σ → ℂ) →L[ℂ] (Fin d → ℂ) :=
    ContinuousLinearMap.pi fun k : Fin d =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm (eI.symm k))
  have hΨ : ∀ y i, Ψ y i = y (eI i) := fun y i => rfl
  have hA : ∀ x k, A x k = x (e.symm (eI.symm k)) := fun x k => rfl
  have hO : IsOpen (Ψ ⁻¹' Ω) := hΩ.preimage Ψ.continuous
  refine ⟨hz, d, A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩
  · exact analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn
      (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))
  · intro y hy
    ext k
    have h1 := congrFun (hproj (Ψ y) hy) (eI.symm k)
    simp only [frameProj, b, EuclideanSpace.basisFun_inner] at h1
    show A (S (g (Ψ y))) k = y k
    rw [hA, hS, Equiv.apply_symm_apply, h1, hΨ, Equiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨hxZ, hxV⟩
      have hmem : T x ∈ zeroSetEuc J ∩ V := ⟨(hZ x).mp hxZ, hxV⟩
      rw [hgraph] at hmem
      obtain ⟨u, hu, hgu⟩ := hmem
      have hΨu : Ψ (fun k => u (eI.symm k)) = u := funext fun i => by simp [hΨ]
      refine ⟨fun k => u (eI.symm k), ?_, ?_⟩
      · show Ψ _ ∈ Ω
        rwa [hΨu]
      · simp only [hΨu, hgu, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (Ψ y) ∈ zeroSetEuc J ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      refine ⟨(hZ _).mpr ?_, ?_⟩
      · rw [hTS]; exact hmem.1
      · show T (S (g (Ψ y))) ∈ V
        rw [hTS]; exact hmem.2
end RegularOffHypersurface
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
