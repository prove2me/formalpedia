-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveRegularOffFinite_proof_e2d6f877467f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:55.772401+00:00
-- url     : https://prove2.me/submissions/04397c34-3cd2-4124-8a06-c7cad445dabe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveRegularOffFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveProperClosedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveRegularOffFinite

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
open MvPolynomial ComplexSets Filter Topology
namespace GroundTheory.Heights₂.Heights
namespace CurveRegularOffFinite
theorem _root_.solution (hG : FrameGraphGeneric.Statement)
    (hP : CurveProperClosedFinite.Statement) : CurveRegularOffFinite.Statement := by
  intro n W hW hdim
  have hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim]; rfl
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, q, hcard, hqW, hreg⟩ := hG n 1 W hW hd b
  obtain ⟨i₀, hI₀⟩ := Finset.card_eq_one.mp hcard
  have hi₀ : i₀ ∈ I₀ := by rw [hI₀]; exact Finset.mem_singleton_self i₀
  have hsub : ∀ j : I₀, j = ⟨i₀, hi₀⟩ := fun j => Subtype.ext (Finset.mem_singleton.mp (hI₀ ▸ j.2))
  have hKW : ¬ Ideal.span {q} ≤ W := fun h => hqW (h (Ideal.subset_span rfl))
  refine ⟨zeroSet W ∩ zeroSet (Ideal.span {q}), hP n W _ hW hdim hKW, ?_⟩
  intro x hx hxF
  have hqx : eval x q ≠ 0 := by
    intro h0
    refine hxF ⟨hx, fun p hp => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    simp [h0]

  let T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
    ((EuclideanSpace.equiv (Fin n) ℂ) : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ))
  have hST : ∀ y, S (T y) = y := fun y => rfl
  have hTS : ∀ w, T (S w) = w := fun w => rfl
  have hZ : ∀ y : Fin n → ℂ, y ∈ zeroSet W ↔ T y ∈ zeroSetEuc W := fun y => Iff.rfl
  obtain ⟨Ω, V, g, hΩ, hV, hxV, hg, hproj, hgraph⟩ := hreg (T x) ((hZ x).mp hx) hqx

  let ι : ℂ →L[ℂ] (I₀ → ℂ) := ContinuousLinearMap.pi fun _ : I₀ => ContinuousLinearMap.id ℂ ℂ
  let A : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i₀
  have hO : IsOpen (ι ⁻¹' Ω) := hΩ.preimage ι.continuous
  refine ⟨A, ι ⁻¹' Ω, T ⁻¹' V, fun y => S (g (ι y)), hO, hV.preimage T.continuous, hxV, ?_, ?_, ?_⟩
  · exact (S.differentiable.comp_differentiableOn
      (hg.comp ι.differentiable.differentiableOn fun y hy => hy)).analyticOnNhd hO
  · intro y hy
    have h1 := congrFun (hproj (ι y) hy) ⟨i₀, hi₀⟩
    simp only [frameProj, b, EuclideanSpace.basisFun_inner] at h1
    exact h1
  · ext x'
    constructor
    · rintro ⟨hx'Z, hx'V⟩
      have hmem : T x' ∈ zeroSetEuc W ∩ V := ⟨(hZ x').mp hx'Z, hx'V⟩
      rw [hgraph] at hmem
      obtain ⟨u, hu, hgu⟩ := hmem
      have hιu : ι (u ⟨i₀, hi₀⟩) = u := funext fun j => by rw [hsub j]; rfl
      refine ⟨u ⟨i₀, hi₀⟩, ?_, ?_⟩
      · show ι _ ∈ Ω
        rwa [hιu]
      · simp only [hιu, hgu, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (ι y) ∈ zeroSetEuc W ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      exact ⟨(hZ _).mpr (by rw [hTS]; exact hmem.1), by show T (S (g (ι y))) ∈ V; rw [hTS]; exact hmem.2⟩
end CurveRegularOffFinite
end GroundTheory.Heights₂.Heights
