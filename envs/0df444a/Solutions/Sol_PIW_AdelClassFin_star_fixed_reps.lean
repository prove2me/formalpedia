-- Prove2me | solution 1 for PIW.AdelClassFin.star_fixed_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:18:52.020858+00:00
-- url     : https://prove2.me/submissions/90684602-d10a-4eb3-9bc0-4155420e58b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open NumberField
open scoped nonZeroDivisors
namespace PIW.AdelClassFin
theorem _root_.solution (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) :
    ∃ R : Set E, R.Finite ∧ (N ≠ 0 → ∀ β : 𝓞 E, star (algebraMap (𝓞 E) E β) = algebraMap (𝓞 E) E β →
      ∃ r ∈ R, ∃ s : 𝓞 E, algebraMap (𝓞 E) E β = r + N * algebraMap (𝓞 E) E s ∧
        star (algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E s) := by
  classical
  by_cases hN : N = 0
  · exact ⟨∅, Set.finite_empty, fun h => absurd hN h⟩
  let I : Ideal (𝓞 E) := Ideal.span {(N : 𝓞 E)}
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let P : 𝓞 E → Prop := fun β => star (algebraMap (𝓞 E) E β) = algebraMap (𝓞 E) E β
  let pick : 𝓞 E ⧸ I → E := fun q =>
    if h : ∃ β, P β ∧ Ideal.Quotient.mk I β = q then algebraMap (𝓞 E) E h.choose else 0
  refine ⟨Set.range pick, Set.finite_range pick, fun _ β hβ => ?_⟩
  have h : ∃ b, P b ∧ Ideal.Quotient.mk I b = Ideal.Quotient.mk I β := ⟨β, hβ, rfl⟩
  obtain ⟨hP, hq⟩ := h.choose_spec
  have hP' : star (algebraMap (𝓞 E) E h.choose) = algebraMap (𝓞 E) E h.choose := hP
  have hpick : pick (Ideal.Quotient.mk I β) = algebraMap (𝓞 E) E h.choose := by
    simp only [pick, dif_pos h]
  have hmem : β - h.choose ∈ I := Ideal.Quotient.eq.mp hq.symm
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
  have e1 := congrArg (algebraMap (𝓞 E) E) hs
  rw [map_mul, map_sub, map_natCast] at e1
  refine ⟨pick (Ideal.Quotient.mk I β), ⟨_, rfl⟩, s, ?_, ?_⟩
  · rw [hpick]
    linear_combination (-1 : E) * e1
  · have e2 := congrArg star e1
    rw [star_mul', star_natCast, star_sub, hβ, hP', ← e1] at e2
    exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr hN) e2
end PIW.AdelClassFin
