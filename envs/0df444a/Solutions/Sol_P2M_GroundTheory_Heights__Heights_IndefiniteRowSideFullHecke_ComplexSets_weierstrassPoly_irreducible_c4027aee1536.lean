-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPoly_irreducible_c4027aee1536
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:23.264346+00:00
-- url     : https://prove2.me/submissions/a0d3671f-0d47-4af1-b144-f40785f74447

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassPolynomialRing
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPoly_monic_2d2bc204a188
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_germValue_polyToGerm_212cae8864c7

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
open Topology Filter Polynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) (hc0 : ∀ j, c j 0 = 0)
    (hirr : Irreducible (polyToGerm σ (weierstrassPoly c hc))) : Irreducible (weierstrassPoly c hc) := by
  have hm := weierstrassPoly_monic c hc
  refine ⟨fun hu => hirr.not_isUnit (hu.map _), fun a b hab => ?_⟩
  have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hab]; exact hm
  obtain ⟨u, hu⟩ : IsUnit a.leadingCoeff := IsUnit.of_mul_eq_one _ hlc
  have ha' : (a * C (↑u⁻¹ : holGerms (0 : σ → ℂ))).Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, ← hu, Units.mul_inv]
  have hb' : (b * C (u : holGerms (0 : σ → ℂ))).Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, hu, mul_comm, hlc]
  have hab' : weierstrassPoly c hc = (a * C (↑u⁻¹ : holGerms (0 : σ → ℂ))) * (b * C (u : holGerms (0 : σ → ℂ))) := by
    rw [hab, show (a * C (↑u⁻¹ : holGerms (0 : σ → ℂ))) * (b * C (u : holGerms (0 : σ → ℂ))) =
      a * b * C ((↑u⁻¹ : holGerms (0 : σ → ℂ)) * u) by rw [C_mul]; ring, Units.inv_mul, C_1, mul_one]
  have hmap : (weierstrassPoly c hc).map (germValue 0) = X ^ d := by
    simp only [weierstrassPoly, finPoly, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
      Polynomial.map_mul, map_C]
    have : ∀ j, germValue 0 (mkGerm (c j) (hc j)) = 0 := fun j => hc0 j
    simp [this]

  have key : ∀ (a' b' : (holGerms (0 : σ → ℂ))[X]), a'.Monic → b'.Monic → weierstrassPoly c hc = a' * b' →
      IsUnit (polyToGerm σ a') → a' = 1 := by
    intro a' b' ha'm hb'm he hunit
    have hdvdX : a'.map (germValue 0) ∣ X ^ d := ⟨b'.map (germValue 0), by rw [← Polynomial.map_mul, ← he, hmap]⟩
    obtain ⟨k, -, hassoc⟩ := (dvd_prime_pow prime_X d).1 hdvdX
    have hka : a'.map (germValue 0) = X ^ k := eq_of_monic_of_associated (ha'm.map _) (monic_X_pow k) hassoc
    have hv := (hunit.map (germValue 0)).ne_zero
    rw [germValue_polyToGerm, hka, eval_pow, eval_X] at hv
    have hk0 : k = 0 := by
      by_contra hk0; exact hv (zero_pow hk0)
    have hdeg0 : a'.natDegree = 0 := by
      rw [← ha'm.natDegree_map (germValue 0), hka, hk0, pow_zero, natDegree_one]
    exact ha'm.natDegree_eq_zero.1 hdeg0
  rw [hab', map_mul] at hirr
  rcases hirr.isUnit_or_isUnit rfl with h1 | h1
  · left
    have e := key _ _ ha' hb' hab' h1
    have : a = C (u : holGerms (0 : σ → ℂ)) := by
      calc a = (a * C (↑u⁻¹ : holGerms (0 : σ → ℂ))) * C (u : holGerms (0 : σ → ℂ)) := by
              rw [mul_assoc, ← C_mul, Units.inv_mul, C_1, mul_one]
        _ = C (u : holGerms (0 : σ → ℂ)) := by rw [e, one_mul]
    rw [this]; exact isUnit_C.2 u.isUnit
  · right
    have e := key _ _ hb' ha' (by rw [hab', mul_comm]) h1
    have : b = C (↑u⁻¹ : holGerms (0 : σ → ℂ)) := by
      calc b = (b * C (u : holGerms (0 : σ → ℂ))) * C (↑u⁻¹ : holGerms (0 : σ → ℂ)) := by
              rw [mul_assoc, ← C_mul, Units.mul_inv, C_1, mul_one]
        _ = C (↑u⁻¹ : holGerms (0 : σ → ℂ)) := by rw [e, one_mul]
    rw [this]; exact isUnit_C.2 u⁻¹.isUnit
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
