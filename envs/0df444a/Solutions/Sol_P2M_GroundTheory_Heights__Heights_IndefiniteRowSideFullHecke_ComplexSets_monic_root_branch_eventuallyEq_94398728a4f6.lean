-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_root_branch_eventuallyEq_94398728a4f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:08.78185+00:00
-- url     : https://prove2.me/submissions/1b746fad-0829-48e3-87f6-b02ae43e555f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormFullBranchConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormFullBranchConstant

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
open Filter Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (s : Fin d → ℂ)
    (u v : (Fin d → ℂ) → ℂ) (ha : ∀ j, ContinuousAt (a j) s) (hu : ContinuousAt u s)
    (hv : ContinuousAt v s) (huv : u s = v s)
    (hsep : (Polynomial.X ^ N + ∑ j, Polynomial.C (a j s) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hru : ∀ᶠ t in 𝓝 s, u t ^ N + ∑ j, a j t * u t ^ (j : ℕ) = 0)
    (hrv : ∀ᶠ t in 𝓝 s, v t ^ N + ∑ j, a j t * v t ^ (j : ℕ) = 0) : u =ᶠ[𝓝 s] v := by
  set Q : (Fin d → ℂ) → ℂ → ℂ → ℂ := fun t x y =>
    ∑ i ∈ Finset.range N, x ^ i * y ^ (N - 1 - i) +
      ∑ j : Fin N, a j t * ∑ i ∈ Finset.range j, x ^ i * y ^ ((j : ℕ) - 1 - i) with hQdef
  have hQ : ∀ t x y, (x ^ N + ∑ j, a j t * x ^ (j : ℕ)) - (y ^ N + ∑ j, a j t * y ^ (j : ℕ)) =
      Q t x y * (x - y) := by
    intro t x y
    rw [hQdef, add_mul, geom_sum₂_mul, Finset.sum_mul]
    simp_rw [mul_assoc, geom_sum₂_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hQs : Q s (u s) (u s) ≠ 0 := by
    have h := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := u s)
      (by simpa [Polynomial.eval₂_id, Polynomial.eval_finsetSum] using hru.self_of_nhds)
    convert h using 1
    simp [hQdef, Polynomial.eval₂_id, Polynomial.eval_finsetSum, geom_sum₂_self, Polynomial.derivative_X_pow]
  have hc : ContinuousAt (fun t => Q t (u t) (v t)) s := by
    simp only [hQdef]
    fun_prop
  have hne : ∀ᶠ t in 𝓝 s, Q t (u t) (v t) ≠ 0 := hc.eventually_ne (by rw [← huv]; exact hQs)
  filter_upwards [hru, hrv, hne] with t h1 h2 h3
  have h := hQ t (u t) (v t)
  rw [h1, h2, sub_self] at h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_left h3)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
