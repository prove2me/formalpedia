-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_proof_01b524ff3ac5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:00:22.525809+00:00
-- url     : https://prove2.me/submissions/692eebda-f296-4c4c-a103-c8803b7bc4a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartNormPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartNormPtsA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartNormPts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_div_0794543b621c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_one_810125b09b0c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_smul_homog_55357c1b3f89
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
namespace ChartNormPts
theorem _root_.solution : ChartNormPts.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G j hv hP' hj z' hw hz1
  classical
  have hcast : ∀ p : MRing ι', eval z' (map (Int.castRingHom ℂ) p) = aeval z' p := fun p => by
    rw [eval_map, aeval_def, algebraMap_int_eq]
  have hcoef : (eval₂Hom (Int.castRingHom ℂ) fun p => z' (v p)) =
      (aeval (z' ∘ v) : MRing ι →ₐ[ℤ] ℂ).toRingHom := by
    ext c
    · simp
    · simp
  have hφ : (algebraMap G.Φ G.Φ').comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom =
      (aeval (G.x' ∘ v) : MRing ι →ₐ[ℤ] G.Φ').toRingHom := by
    ext c
    · simp
    · simp [G.compat]
  rw [hφ, hcoef]
  constructor
  · intro hz F hF
    have hH : ChartNormPts.homogenise v (fun q : Σ k : FibreBlock κ, ι' k.1 => (⟨q.1.1, q.2⟩ : Σ k', ι' k'))
        (fun q => ⟨q.1.1, j q.1⟩) F ∈ P' := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker]
      show aeval G.x' _ = 0
      rw [ChartNormPts.aeval_homogenise_div v _ _ F G.x' fun q => hj q.1, hF, mul_zero]
    have h0 := hz.2 _ hH
    rwa [hcast, ChartNormPts.aeval_homogenise_one v _ _ F z' fun q => hz1 q.1] at h0
  · intro hF
    refine ⟨fun k' => ?_, fun f hf => ?_⟩
    · by_cases h : k' ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := h
        obtain ⟨i, hi⟩ := hw.1 k
        replace hi : z' (v ⟨k, i⟩) ≠ 0 := hi
        revert hi
        generalize hq : v ⟨k, i⟩ = q
        obtain ⟨k₀, i₀⟩ := q
        intro hi
        have e : k₀ = κ k := by rw [← hv.2.2.1 ⟨k, i⟩, hq]
        subst e
        exact ⟨i₀, hi⟩
      · exact ⟨j ⟨k', h⟩, by rw [hz1 ⟨k', h⟩]; exact one_ne_zero⟩
    obtain ⟨S, hS, rfl⟩ := hP'
    suffices hle : Ideal.span S ≤ RingHom.ker (aeval z' : MRing ι' →ₐ[ℤ] ℂ) by
      rw [hcast]; exact hle hf
    rw [Ideal.span_le]
    intro g hg
    obtain ⟨a, ha⟩ := hS g hg
    let σ : (Σ k', ι' k') → MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι) := fun q' =>
      if h : q'.1 ∈ Set.range κ then C (X (hv.2.2.2 q' h).choose) else X ⟨⟨q'.1, h⟩, q'.2⟩
    have hcomp : ∀ {R : Type} [CommRing R] (ψ : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι) →+* R),
        ψ (aeval σ g) = aeval (fun q' => ψ (σ q')) g := fun ψ =>
      comp_aeval_apply (f := σ) ψ.toIntAlgHom g
    have h1 := hF (aeval σ g)
    rw [← coe_eval₂Hom, ← coe_eval₂Hom, hcomp, hcomp] at h1
    let c : K' → G.Φ' := fun k' => if h : k' ∈ Set.range κ then 1 else (G.x' ⟨k', j ⟨k', h⟩⟩)⁻¹
    have hx : (fun q' => eval₂Hom (aeval (G.x' ∘ v) : MRing ι →ₐ[ℤ] G.Φ').toRingHom
        (fun q => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩) (σ q')) = fun q' => c q'.1 * G.x' q' := by
      funext q'
      by_cases h : q'.1 ∈ Set.range κ
      · simp only [σ, c, dif_pos h, coe_eval₂Hom, eval₂_C, one_mul]
        simp [(hv.2.2.2 q' h).choose_spec]
      · simp only [σ, c, dif_neg h, coe_eval₂Hom, eval₂_X]
        rw [div_eq_inv_mul]
    have hz : (fun q' => eval₂Hom (aeval (z' ∘ v) : MRing ι →ₐ[ℤ] ℂ).toRingHom
        (fun q => z' ⟨q.1.1, q.2⟩) (σ q')) = z' := by
      funext q'
      by_cases h : q'.1 ∈ Set.range κ
      · simp only [σ, dif_pos h, coe_eval₂Hom, eval₂_C]
        simp [(hv.2.2.2 q' h).choose_spec]
      · simp only [σ, dif_neg h, coe_eval₂Hom, eval₂_X]
    rw [hx, hz, ChartNormPts.aeval_smul_homog g a ha] at h1
    have hg0 : aeval G.x' g = 0 := by
      have : g ∈ RingHom.ker (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ') := by
        rw [G.genericFibre_ker_target]; exact Ideal.subset_span hg
      exact this
    exact h1 (by rw [hg0, mul_zero])
end ChartNormPts
end GroundTheory.Heights₂.Heights.Inter
