-- Prove2me | solution 1 for PI.HermLatFin.UnitaryGroupMassFormula.hform_trace_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:23.389482+00:00
-- url     : https://prove2.me/submissions/1acd65a9-12e3-4dc5-84c5-6f613633baf8

import Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HformTracePos
import Theorems.Thm_PI_HermLatFin_UnitaryGroupMassFormula_hform_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexOrder
noncomputable section
open PI PI.HermLatFin PI.HermLatFin.UnitaryGroupMassFormula
variable {E : Type} [Field E] [NumberField E]
variable [StarRing E] {n : ℕ}
namespace PI.HermLatFin.UnitaryGroupMassFormula
theorem _root_.solution (σ : E →+* E) (hst : ∀ a : E, star a = σ a)
    (hσ : ∀ τ : E →+* ℂ, ∀ a : E, τ (σ a) = starRingEnd ℂ (τ a))
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ τ : E →+* ℂ, (J.map τ).PosDef)
    (x : Fin n → E) (hx : x ≠ 0) : 0 < Algebra.trace ℚ E (hform J x x) := by
  haveI : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have key : ∀ τ : E →ₐ[ℚ] ℂ, 0 < τ (hform J x x) := by
    intro τ
    have hτσ : ∀ a : E, τ (σ a) = star (τ a) := fun a => by
      rw [← starRingEnd_apply]
      exact hσ τ.toRingHom a
    have e : τ (hform J x x) =
        star (fun i => τ (x i)) ⬝ᵥ (J.map τ) *ᵥ (fun i => τ (x i)) := by
      rw [hform_apply]
      simp only [map_sum]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.map_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_mul, hst, hτσ]
      ring
    rw [e]
    refine (hJ τ.toRingHom).dotProduct_mulVec_pos ?_
    intro h0
    apply hx
    funext i
    have h1 := congrFun h0 i
    exact (map_eq_zero_iff _ τ.toRingHom.injective).1 h1
  have hsum : 0 < ∑ τ : E →ₐ[ℚ] ℂ, τ (hform J x x) :=
    Finset.sum_pos (fun τ _ => key τ) Finset.univ_nonempty
  rw [← trace_eq_sum_embeddings ℂ, eq_ratCast, ← Complex.ofReal_ratCast, Complex.zero_lt_real,
    Rat.cast_pos] at hsum
  exact hsum
end PI.HermLatFin.UnitaryGroupMassFormula
