-- Prove2me | solution 1 for PI.Dv.Tr.trace_finite_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:04.365471+00:00
-- url     : https://prove2.me/submissions/0aaf9f8a-78ec-4989-ad60-89856fef25d3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFiniteOrder
import Theorems.Thm_PI_Dv_Tr_root_pow_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open Module
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
namespace PI.Dv.Tr
theorem _root_.solution (f : Module.End K W) (m : ℕ) (hm : 0 < m) (hf : f ^ m = 1) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W f)‖ ≤ finrank K W ∧ IsIntegral ℤ (LinearMap.trace K W f) := by
  classical
  let b := Module.finBasis K W
  set A := LinearMap.toMatrix b b f with hAdef
  set B : Matrix (Fin (finrank K W)) (Fin (finrank K W)) ℂ := σ.mapMatrix A with hBdef
  have htr : σ (LinearMap.trace K W f) = B.trace := by
    rw [LinearMap.trace_eq_matrix_trace K b, hBdef]
    simp [Matrix.trace, map_sum, RingHom.mapMatrix_apply, hAdef]
  have hApow : ∀ k : ℕ, A ^ k = LinearMap.toMatrix b b (f ^ k) := by
    intro k
    induction k with
    | zero => simp [LinearMap.toMatrix_one]
    | succ k ih => rw [pow_succ, ih, pow_succ, LinearMap.toMatrix_mul]
  have hB : B ^ m = 1 := by
    rw [hBdef, ← map_pow, hApow, hf, LinearMap.toMatrix_one, map_one]
  have hroots : ∀ μ ∈ B.charpoly.roots, μ ^ m = 1 := fun μ hμ => root_pow_eq_one B m hB μ hμ
  have hsum : B.trace = B.charpoly.roots.sum := Matrix.trace_eq_sum_roots_charpoly B
  constructor
  · rw [htr, hsum]
    refine (norm_multiset_sum_le _).trans ?_
    have hmap : B.charpoly.roots.map (fun μ => ‖μ‖) = B.charpoly.roots.map (fun _ => (1 : ℝ)) :=
      Multiset.map_congr rfl fun μ hμ => Complex.norm_eq_one_of_pow_eq_one (hroots μ hμ) hm.ne'
    rw [hmap, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]
    have hc := Polynomial.card_roots' B.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hc
    exact_mod_cast hc
  · have hint : IsIntegral ℤ (σ (LinearMap.trace K W f)) := by
      rw [htr, hsum]
      exact IsIntegral.multiset_sum fun μ hμ =>
        IsIntegral.of_pow hm (by rw [hroots μ hμ]; exact isIntegral_one)
    exact (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).mp hint
end PI.Dv.Tr
