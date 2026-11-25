-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_simpleRoot_isolated_a6f4f915c882
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:09.56182+00:00
-- url     : https://prove2.me/submissions/fb589f78-4260-49dd-bef0-a8687180fe41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedIffRootFull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormSheetedIffRootFull

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
theorem _root_.solution {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (τ : ℂ)
    (hcont : ∀ j, ContinuousAt (a j) t)
    (hsep : (Polynomial.X ^ N + ∑ j, Polynomial.C (a j t) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hroot : τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) = 0) :
    ∃ ε > 0, ∀ s, dist s t < ε → ∀ T₁ T₂ : ℂ, dist T₁ τ < ε → dist T₂ τ < ε →
      T₁ ^ N + ∑ j, a j s * T₁ ^ (j : ℕ) = 0 → T₂ ^ N + ∑ j, a j s * T₂ ^ (j : ℕ) = 0 → T₁ = T₂ := by

  set D : (Fin d → ℂ) × ℂ × ℂ → ℂ := fun v =>
    ∑ m ∈ Finset.range N, v.2.1 ^ m * v.2.2 ^ (N - 1 - m) +
      ∑ j : Fin N, a j v.1 * ∑ m ∈ Finset.range (j : ℕ), v.2.1 ^ m * v.2.2 ^ ((j : ℕ) - 1 - m) with hDdef
  have hkey : ∀ s T₁ T₂, (T₁ ^ N + ∑ j, a j s * T₁ ^ (j : ℕ)) - (T₂ ^ N + ∑ j, a j s * T₂ ^ (j : ℕ)) =
      D (s, T₁, T₂) * (T₁ - T₂) := by
    intro s T₁ T₂
    rw [hDdef, add_mul, geom_sum₂_mul, Finset.sum_mul]
    simp_rw [mul_assoc, geom_sum₂_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hc : ∀ j, ContinuousAt (fun v : (Fin d → ℂ) × ℂ × ℂ => a j v.1) (t, τ, τ) :=
    fun j => (hcont j).comp continuousAt_fst
  have hcD : ContinuousAt D (t, τ, τ) := by
    rw [hDdef]
    fun_prop (disch := assumption)
  have hD0 : D (t, τ, τ) ≠ 0 := by
    have h1 := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ) (by
      simpa [Polynomial.eval₂_finsetSum] using hroot)
    convert h1 using 1
    simp only [hDdef, geom_sum₂_self, Polynomial.derivative_add, Polynomial.derivative_X_pow,
      Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum, RingHom.id_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcD.eventually_ne hD0)
  refine ⟨ε, hε, fun s hs T₁ T₂ h₁ h₂ hr₁ hr₂ => ?_⟩
  have hne : D (s, T₁, T₂) ≠ 0 := hball (by simp [Prod.dist_eq, hs, h₁, h₂])
  have h := hkey s T₁ T₂
  rw [hr₁, hr₂, sub_zero, eq_comm] at h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hne)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
