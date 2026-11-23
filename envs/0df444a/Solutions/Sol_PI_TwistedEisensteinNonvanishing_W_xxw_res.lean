-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.xxw_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:50.888209+00:00
-- url     : https://prove2.me/submissions/5b082653-c1c0-4341-9515-4db65a33c03a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_FreeCoordinateAffineInvertible
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_xxw_mem_Ufl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {n c : ℕ} {ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} (hρ : R1cond E n c ρ) (v : Fin n → E) :
    ρ (inX E n c v) = inX E n c (resX ρ v) := by
  have hinX : ∀ u : Fin n → E, inX E n c u ∈ Ufl E n c 0 := by
    intro u
    rw [xxw_mem_Ufl]
    intro l hl
    simp only [inX, LinearMap.pi_apply, dif_neg (show ¬ l.1 < n by omega), LinearMap.zero_apply]
  have hsum : inX E n c v = ∑ p : Fin n, v p • eN E (n + c) p.1 := by
    funext l
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, eN, mul_ite, mul_one, mul_zero]
    by_cases hl : l.1 < n
    · simp only [inX, LinearMap.pi_apply, dif_pos hl, LinearMap.proj_apply]
      rw [Finset.sum_eq_single ⟨l.1, hl⟩]
      · simp
      · intro p _ hp
        rw [if_neg]
        intro h
        exact hp (Fin.ext h.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp only [inX, LinearMap.pi_apply, dif_neg hl, LinearMap.zero_apply]
      symm
      apply Finset.sum_eq_zero
      intro p _
      rw [if_neg]
      intro h
      have := p.isLt
      omega
  funext l
  by_cases hl : l.1 < n
  · rw [hsum, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [inX, LinearMap.pi_apply, dif_pos hl, LinearMap.proj_apply, resX, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [mul_comm]
    rfl
  · have h1 := hρ.1 0 _ (hinX v)
    rw [xxw_mem_Ufl] at h1
    rw [h1 l (by omega)]
    simp only [inX, LinearMap.pi_apply, dif_neg hl, LinearMap.zero_apply]
end PI.TwistedEisensteinNonvanishing.W
