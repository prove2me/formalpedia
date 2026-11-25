-- Prove2me | solution 1 for PI.PinHostLoc.UnitaryGroupMassFormula.irr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:40.662818+00:00
-- url     : https://prove2.me/submissions/15d7200d-b839-42dd-811f-64dd18c8667e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PinHostLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalResidueCharacter_ResCharEq
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_le_exp_neg_one_of_lt_one
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_vF
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_exists_val
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_natVal
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_vF_lt
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField ValuativeRel WithZero
open PI PI.PinHostLoc PI.PinHostLoc.UnitaryGroupMassFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)
namespace PI.PinHostLoc.UnitaryGroupMassFormula
theorem _root_.solution {g : ℕ} (hg0 : g ≠ 0) (hin : ((g : ℕ) : 𝓞 F) ∈ p.asIdeal)
    (hnot : ((g : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2) : Irreducible ((g : ℕ) : 𝒪[A.Fp]) := by
  have hne : ((g : ℕ) : 𝓞 F) ≠ 0 := fun h => hg0 (by
    have h' := congrArg (algebraMap (𝓞 F) F) h
    rw [map_natCast, map_zero] at h'
    exact_mod_cast h')
  have hge : WithZero.exp (-1) ≤ p.valuation F ((g : ℕ) : F) := by
    rw [natVal]
    have h2 : ¬ p.intValuation ((g : ℕ) : 𝓞 F) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
      hnot ((p.intValuation_le_pow_iff_mem _ 2).mp h)
    have hz : p.intValuation ((g : ℕ) : 𝓞 F) ≠ 0 := p.intValuation_ne_zero _ hne
    rw [← WithZero.exp_log hz] at h2 ⊢
    rw [WithZero.exp_le_exp] at h2 ⊢
    omega
  have hlt : ValuativeRel.valuation A.Fp (A.ιF ((g : ℕ) : F)) < 1 := by
    have h := (vF_lt A ((g : ℕ) : F) 1).mpr (by
      rw [map_one, natVal]
      exact (p.intValuation_lt_one_iff_mem _).mpr hin)
    simp only [map_one] at h
    exact h
  have hcoe : (((g : ℕ) : 𝒪[A.Fp]) : A.Fp) = A.ιF ((g : ℕ) : F) := by simp
  have hgne : A.ιF ((g : ℕ) : F) ≠ 0 := (map_ne_zero A.ιF).mpr (Nat.cast_ne_zero.mpr hg0)
  refine ⟨?_, ?_⟩
  · rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one, hcoe]
    exact hlt
  · intro a b hab
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨ha, hb⟩ := hcon
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at ha hb
    have hab' : (a : A.Fp) * (b : A.Fp) = A.ιF ((g : ℕ) : F) := by
      rw [← hcoe, hab]
      norm_cast
    have hab0 : (a : A.Fp) * (b : A.Fp) ≠ 0 := by
      rw [hab']
      exact hgne
    have ha0 : (a : A.Fp) ≠ 0 := left_ne_zero_of_mul hab0
    have hva : ValuativeRel.valuation A.Fp (a : A.Fp) ≠ 0 :=
      (ValuativeRel.valuation A.Fp).ne_zero_iff.mpr ha0
    obtain ⟨x, hx⟩ := exists_val A (a : A.Fp) ha0
    have hxlt : p.valuation F x < 1 := by
      have h := (vF_lt A x 1).mp (by
        simp only [map_one]
        rw [hx]
        exact ha)
      simp only [map_one] at h
      exact h
    have hle : ValuativeRel.valuation A.Fp (a : A.Fp) ≤
        ValuativeRel.valuation A.Fp (A.ιF ((g : ℕ) : F)) := by
      rw [← hx, vF A]
      exact (le_exp_neg_one_of_lt_one hxlt).trans hge
    rw [← hab', map_mul] at hle
    have h1 := mul_le_mul' (le_refl (ValuativeRel.valuation A.Fp (a : A.Fp))⁻¹) hle
    rw [← mul_assoc, inv_mul_cancel₀ hva, one_mul] at h1
    exact absurd hb (not_lt.mpr h1)
end PI.PinHostLoc.UnitaryGroupMassFormula
