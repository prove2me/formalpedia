-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_coeffs_extend_fb862d39adb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:32:31.360088+00:00
-- url     : https://prove2.me/submissions/ad47a479-b9fe-40b8-a212-389422f502c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeaklyHolomorphicIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_differentiableAt_coeff_prod_X_sub_C_05324d52b041
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_coeff_prod_X_sub_C_le_d2f0b17beeaf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_eval_eq_pow_add_sum_6a2fccd0c6eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_prod_X_sub_C_monic_natDegree_1840b3efbccf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicOnSubset_differentiableAt_comp_a8c1a300de3d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_LocalTrace_proof_fb74460c5495
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_proof_9f4f3171a0d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_proof_5560ddb795d4


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
open Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {k m : ℕ} (Z W : Set (σ → ℂ))
    (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (D : Set (Fin k → ℂ)) (δ g : (Fin k → ℂ) → ℂ) (φ : (σ → ℂ) → ℂ) (M : ℝ)
    (hDo : IsOpen D) (hgd : DifferentiableOn ℂ g D)
    (hgne : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, g t ≠ 0)
    (hgδ : ∀ y ∈ D, g y ≠ 0 → δ y ≠ 0)
    (hsheets : ∀ y ∈ D, δ y ≠ 0 → ∃ (O : Set (Fin k → ℂ)) (s : Fin m → (Fin k → ℂ) → σ → ℂ),
        IsOpen O ∧ y ∈ O ∧ (∀ j, DifferentiableOn ℂ (s j) O) ∧
        ∀ y' ∈ O, (∀ j, s j y' ∈ Z ∩ W ∧ A (s j y') = y') ∧
          Function.Injective (fun j => s j y') ∧
          ∀ z ∈ Z ∩ W, A z = y' → z ∈ Set.range (fun j => s j y'))
    (hφ : HolomorphicOnSubset φ {x | x ∈ Z ∩ W ∧ A x ∈ D ∧ g (A x) ≠ 0})
    (hM : ∀ x ∈ Z ∩ W, A x ∈ D → g (A x) ≠ 0 → ‖φ x‖ ≤ M) :
    ∃ c : Fin m → (Fin k → ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (c j) D) ∧
      ∀ y ∈ D, g y ≠ 0 → ∀ s : Fin m → σ → ℂ, (∀ j, s j ∈ Z ∩ W ∧ A (s j) = y) →
        Function.Injective s → (∀ z ∈ Z ∩ W, A z = y → z ∈ Set.range s) →
        ∀ t : ℂ, t ^ m + ∑ j, c j y * t ^ (j : ℕ) = ∏ j, (t - φ (s j)) := by
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q : (Fin k → ℂ) → Polynomial ℂ,
      ∀ y, Q y = ∏ᶠ x ∈ {x | x ∈ Z ∩ W ∧ A x = y}, (Polynomial.X - Polynomial.C (φ x)) := ⟨_, fun _ => rfl⟩
  have hQs : ∀ (y : Fin k → ℂ) (s : Fin m → σ → ℂ), (∀ j, s j ∈ Z ∩ W ∧ A (s j) = y) →
      Function.Injective s → (∀ z ∈ Z ∩ W, A z = y → z ∈ Set.range s) →
      Q y = ∏ j, (Polynomial.X - Polynomial.C (φ (s j))) := by
    intro y s hs hinj hcov
    have hset : {x | x ∈ Z ∩ W ∧ A x = y} = Set.range s := by
      ext z
      constructor
      · rintro ⟨hz, hAz⟩
        exact hcov z hz hAz
      · rintro ⟨j, rfl⟩
        exact hs j
    rw [hQ, hset, finprod_mem_range hinj, finprod_eq_prod_of_fintype]
  have hcd : ∀ n : ℕ, DifferentiableOn ℂ (fun y => (Q y).coeff n) (D ∩ {t | g t ≠ 0}) := by
    rintro n y ⟨hyD, hyg⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD (hgδ y hyD hyg)
    have hev : (fun y => (Q y).coeff n) =ᶠ[𝓝 y]
        fun y' => (∏ i, (Polynomial.X - Polynomial.C (φ (s i y')))).coeff n := by
      filter_upwards [hOo.mem_nhds hyO] with y' hy'
      rw [hQs y' (fun i => s i y') (hsO y' hy').1 (hsO y' hy').2.1 (hsO y' hy').2.2]
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    refine differentiableAt_coeff_prod_X_sub_C Finset.univ (fun i y' => φ (s i y')) y (fun i _ => ?_) n
    refine hφ.differentiableAt_comp ((hsd i).differentiableAt (hOo.mem_nhds hyO)) ?_
    have hgc : ContinuousAt g y := (hgd.differentiableAt (hDo.mem_nhds hyD)).continuousAt
    filter_upwards [hOo.mem_nhds hyO, hDo.mem_nhds hyD, hgc.eventually_ne hyg] with y' h1 h2 h3
    have hs' := (hsO y' h1).1 i
    exact ⟨hs'.1, by rw [hs'.2]; exact h2, by rw [hs'.2]; exact h3⟩
  set M' : ℝ := max M 1
  have hcb : ∀ n : ℕ, ∀ y ∈ D ∩ {t | g t ≠ 0}, ‖(Q y).coeff n‖ ≤ (2 * M') ^ m := by
    rintro n y ⟨hyD, hyg⟩
    obtain ⟨O, s, hOo, hyO, hsd, hsO⟩ := hsheets y hyD (hgδ y hyD hyg)
    obtain ⟨h1, h2, h3⟩ := hsO y hyO
    rw [hQs y (fun i => s i y) h1 h2 h3]
    have := norm_coeff_prod_X_sub_C_le Finset.univ (fun i => φ (s i y)) (le_max_right M 1)
      (fun i _ => (hM _ (h1 i).1 (by rw [(h1 i).2]; exact hyD) (by rw [(h1 i).2]; exact hyg)).trans
        (le_max_left M 1)) n
    simpa using this
  have hext : ∀ j : Fin m, ∃ F : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F D ∧
      Set.EqOn F (fun y => (Q y).coeff j) (D ∩ {t | g t ≠ 0}) := by
    intro j
    exact RiemannExtensionAnalytic.proof k D g (fun y => (Q y).coeff j) hDo hgd hgne (hcd j) (fun τ _ =>
      ⟨Set.univ, Filter.univ_mem, isBounded_iff_forall_norm_le.2 ⟨(2 * M') ^ m, by
        rintro _ ⟨y, ⟨⟨_, hyD⟩, hyg⟩, rfl⟩
        exact hcb j y ⟨hyD, hyg⟩⟩⟩)
  choose c hcD hceq using hext
  refine ⟨c, hcD, ?_⟩
  intro y hyD hyg s hs hinj hcov t
  have hQy := hQs y s hs hinj hcov
  obtain ⟨hmon, hdeg⟩ := prod_X_sub_C_monic_natDegree (fun j => φ (s j))
  have hcy : ∀ j : Fin m, c j y = (∏ i, (Polynomial.X - Polynomial.C (φ (s i)))).coeff j := by
    intro j
    rw [hceq j ⟨hyD, hyg⟩]
    dsimp only
    rw [hQy]
  simp_rw [hcy]
  rw [← monic_eval_eq_pow_add_sum hmon hdeg t, Polynomial.eval_prod]
  simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
