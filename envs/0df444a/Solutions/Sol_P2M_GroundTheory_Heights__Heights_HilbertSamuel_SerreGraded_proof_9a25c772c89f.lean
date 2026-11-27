-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_proof_9a25c772c89f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:57:27.109775+00:00
-- url     : https://prove2.me/submissions/619914c3-72fe-4f56-be18-1c63088b9f2a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_pow_mem_8f4bb2b91237
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_X_5d3e9f420ff7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_smul_eq_af68eef4f60e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_monomial_mem_013043894e40
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_torsion_bound_7e4614d2b7b2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
theorem _root_.solution : SerreGraded.Statement := by
  intro Ω _ q r w d t ⟨u, hu⟩
  classical
  let _ : Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω) := (act w).toAlgebra
  have hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w := rfl
  obtain ⟨E, hE⟩ := torsion_bound w d t hA u
  refine ⟨E, fun n hn s hs => ?_⟩
  have step : ∀ k, s * w u ^ (k + 1) ∈ gradedSpan w d t (n + k + 1) →
      s * w u ^ k ∈ gradedSpan w d t (n + k) := by
    intro k hk
    have hm := monomial_mem w d t hA hk
    have htors : ∀ j, w j ≠ 0 → ∃ D : ℕ, (MvPolynomial.X j ^ D : MvPolynomial (Fin q) ℤ) •
        (C (s * w u ^ (k + 1)) * X ^ (n + k + 1)) ∈ shifted w d t u := by
      intro j hj
      obtain ⟨D, hD⟩ := hs j hj
      refine ⟨D, Submodule.mem_map.mpr ⟨C (s * w j ^ D * w u ^ k) * X ^ (n + D + k),
        monomial_mem w d t hA (mul_pow_mem w d t u hD k), ?_⟩⟩
      rw [LinearMap.mulLeft_apply, smul_eq w hA, map_pow, act_X]
      simp only [C_mul, C_pow]
      ring
    obtain ⟨z, hz, hz'⟩ := hE _ hm htors (n + k) (by omega)
    rw [coeff_C_mul_X_pow, if_pos rfl] at hz'
    have hcancel : w u * (s * w u ^ k) = w u * z := by rw [← hz']; ring
    rw [mul_left_cancel₀ hu hcancel]
    exact hz
  have desc : ∀ D, s * w u ^ D ∈ gradedSpan w d t (n + D) → s ∈ gradedSpan w d t n := by
    intro D
    induction D with
    | zero => intro h; simpa using h
    | succ D ih => exact fun h => ih (step D h)
  obtain ⟨D, hD⟩ := hs u hu
  exact desc D hD
end GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
