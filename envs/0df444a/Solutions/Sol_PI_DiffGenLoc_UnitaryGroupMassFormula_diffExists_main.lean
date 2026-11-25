-- Prove2me | solution 1 for PI.DiffGenLoc.UnitaryGroupMassFormula.diffExists_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:13.830832+00:00
-- url     : https://prove2.me/submissions/4000e889-03b8-4ad8-82ee-86d530f23bdd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiffGenLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDifferentGenerators_DiffExistsMain
import Theorems.Thm_PI_DiffGenLoc_UnitaryGroupMassFormula_val_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DiffGenLoc PI.DiffGenLoc.UnitaryGroupMassFormula
open NumberField IsDedekindDomain WithZero
namespace PI.DiffGenLoc.UnitaryGroupMassFormula
theorem _root_.solution {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : DiffExists v := by
  classical
  have hI : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hne : ∀ x : 𝓞 F, x ≠ 0 → v.intValuation x ≠ 0 := fun x hx => by
    first
      | exact v.intValuation_ne_zero x hx
      | exact v.intValuation_ne_zero' x hx
      | exact (map_ne_zero _).2 hx
      | simpa using hx
  let f : 𝓞 F → ℕ := fun x =>
    if hx : x = 0 then 0 else (-(Multiplicative.toAdd (WithZero.unzero (hne x hx)))).toNat
  have hfdef : ∀ z (hz : z ≠ 0), f z = (-(Multiplicative.toAdd (WithZero.unzero (hne z hz)))).toNat :=
    fun z hz => dif_neg hz
  have key : ∀ z : 𝓞 F, ∀ hz : z ≠ 0,
      v.intValuation z = ((Multiplicative.ofAdd (-(f z : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro z hz
    have hu : ((WithZero.unzero (hne z hz) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = v.intValuation z :=
      WithZero.coe_unzero _
    have hle : Multiplicative.toAdd (WithZero.unzero (hne z hz)) ≤ 0 := by
      have h1 : ((WithZero.unzero (hne z hz) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
          ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
        rw [hu, WithZero.coe_one]
        exact v.intValuation_le_one z
      rw [WithZero.coe_le_coe] at h1
      have h2 := Multiplicative.toAdd_le.2 h1
      simpa using h2
    rw [hfdef z hz, Int.toNat_of_nonneg (by linarith), neg_neg, ofAdd_toAdd, hu]
  have hP : ∃ n, ∃ x ∈ differentIdeal ℤ (𝓞 F), x ≠ 0 ∧ f x = n := ⟨_, y, hyI, hy0, rfl⟩
  obtain ⟨x₀, hx₀I, hx₀0, hfx₀⟩ := Nat.find_spec hP
  refine ⟨algebraMap F (Fv F v) (x₀ : F), ?_, ?_, x₀, hx₀I, rfl⟩
  · intro h
    apply hx₀0
    have h1 : ((x₀ : F)) = 0 := (algebraMap F (Fv F v)).injective (h.trans (map_zero _).symm)
    exact_mod_cast h1
  · intro x hxI
    rw [val_alg, val_alg]
    by_cases hx : x = 0
    · simp [hx]
    have hmin : Nat.find hP ≤ f x := Nat.find_min' hP ⟨x, hxI, hx, rfl⟩
    rw [key x hx, key x₀ hx₀0, WithZero.coe_le_coe, Multiplicative.ofAdd_le, neg_le_neg_iff, Nat.cast_le, hfx₀]
    exact hmin
end PI.DiffGenLoc.UnitaryGroupMassFormula
