-- Prove2me | solution 1 for PI.VolStabW.fix2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:56.122615+00:00
-- url     : https://prove2.me/submissions/9467e610-b4d3-487f-8650-edc91cbe7cb4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace PI.VolStabW
theorem _root_.solution {F : Type} [Field F] (C : Matrix (Fin 2) (Fin 2) F) (hC : C ≠ 1) (u : Fin 2 → F)
    (hu : u ≠ 0) (hCu : Matrix.mulVec C u = u) :
    ∃ k0 k1 : Fin 2, k0 ≠ k1 ∧ u k0 ≠ 0 ∧ ∃ ρ : F, ∀ (K : Type) [Field K] [Algebra F K]
      (x : Fin 2 → K), Matrix.mulVec (C.map (algebraMap F K)) x = x → x k1 = algebraMap F K ρ * x k0 := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : Fin 2, (C - 1) r 0 ≠ 0 ∨ (C - 1) r 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hC
    have : C - 1 = 0 := by
      ext i j
      fin_cases j
      · exact (h i).1
      · exact (h i).2
    exact sub_eq_zero.1 this
  have hrow : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin 2 → K),
      Matrix.mulVec (C.map (algebraMap F K)) x = x →
        algebraMap F K ((C - 1) r 0) * x 0 + algebraMap F K ((C - 1) r 1) * x 1 = 0 := by
    intro K _ _ x hx
    have h := congrFun hx r
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] at h
    simp only [Matrix.sub_apply, Matrix.one_apply, map_sub]
    fin_cases r <;> simp at h ⊢ <;> linear_combination h
  have hrowu := hrow F u (by simpa using hCu)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hrowu
  by_cases hβ : (C - 1) r 1 ≠ 0
  · refine ⟨0, 1, by decide, ?_, -((C - 1) r 0) / (C - 1) r 1, fun K _ _ x hx => ?_⟩
    · intro h0
      apply hu
      have h1 : u 1 = 0 := by
        rw [h0, mul_zero, zero_add] at hrowu
        exact (mul_eq_zero.1 hrowu).resolve_left hβ
      ext i
      fin_cases i
      · exact h0
      · exact h1
    · have h := hrow K x hx
      have hβK : algebraMap F K ((C - 1) r 1) ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact hβ
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
  · push Not at hβ
    have hα : (C - 1) r 0 ≠ 0 := hr.resolve_right (by rw [hβ]; exact fun h => h rfl)
    have hu0 : u 0 = 0 := by
      rw [hβ, zero_mul, add_zero] at hrowu
      exact (mul_eq_zero.1 hrowu).resolve_left hα
    refine ⟨1, 0, by decide, ?_, 0, fun K _ _ x hx => ?_⟩
    · intro h1
      apply hu
      ext i
      fin_cases i
      · exact hu0
      · exact h1
    · have h := hrow K x hx
      rw [hβ, map_zero, zero_mul, add_zero] at h
      have hαK : algebraMap F K ((C - 1) r 0) ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact hα
      rw [map_zero, zero_mul]
      exact (mul_eq_zero.1 h).resolve_left hαK
end PI.VolStabW
