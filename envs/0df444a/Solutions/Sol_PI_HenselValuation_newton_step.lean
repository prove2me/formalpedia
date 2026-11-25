-- Prove2me | solution 1 for PI.HenselValuation.newton_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:16.053743+00:00
-- url     : https://prove2.me/submissions/b7e67718-e0f4-4aa8-822c-4fc0e57c1086

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Hensel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HenselOpenValuation_IsOpenLeVal
import Theorems.Thm_PI_HenselValuation_val_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Polynomial Topology
open PI PI.HenselValuation
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace PI.HenselValuation
theorem _root_.solution (f : Polynomial 𝒪[F]) (a b : 𝒪[F])
    (hba : valuation F ((b - a : 𝒪[F]) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F))
    (hfb : valuation F ((f.eval b : 𝒪[F]) : F) <
      valuation F ((f.derivative.eval a : 𝒪[F]) : F) ^ 2)
    (hne : f.eval b ≠ 0) :
    ∃ b' : 𝒪[F], valuation F ((b' - a : 𝒪[F]) : F) <
        valuation F ((f.derivative.eval a : 𝒪[F]) : F) ∧
      valuation F ((f.eval b' : 𝒪[F]) : F) < valuation F ((f.eval b : 𝒪[F]) : F) := by
  have hc0 : valuation F ((f.derivative.eval a : 𝒪[F]) : F) ≠ 0 :=
    (lt_of_le_of_lt zero_le hba).ne'
  obtain ⟨z, hz⟩ := Polynomial.evalSubFactor f.derivative b a
  have hdiff : ((f.derivative.eval b : 𝒪[F]) : F) - ((f.derivative.eval a : 𝒪[F]) : F) =
      (z : F) * ((b - a : 𝒪[F]) : F) := by
    exact_mod_cast congrArg Subtype.val hz
  have hdb : valuation F ((f.derivative.eval b : 𝒪[F]) : F) =
      valuation F ((f.derivative.eval a : 𝒪[F]) : F) := by
    apply Valuation.map_eq_of_sub_lt
    rw [hdiff, Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one z)) hba
  have hdb0 : ((f.derivative.eval b : 𝒪[F]) : F) ≠ 0 := by
    intro h0
    apply hc0
    rw [← hdb, h0, Valuation.map_zero]
  have hfb0 : ((f.eval b : 𝒪[F]) : F) ≠ 0 := by
    intro h0
    exact hne (by exact_mod_cast h0)
  obtain ⟨h, hh⟩ : ∃ h : F, h = -((f.eval b : 𝒪[F]) : F) / ((f.derivative.eval b : 𝒪[F]) : F) :=
    ⟨_, rfl⟩
  have hhd : h * ((f.derivative.eval b : 𝒪[F]) : F) = -((f.eval b : 𝒪[F]) : F) := by
    rw [hh, div_mul_cancel₀ _ hdb0]
  have hvh : valuation F h * valuation F ((f.derivative.eval a : 𝒪[F]) : F) =
      valuation F ((f.eval b : 𝒪[F]) : F) := by
    rw [← hdb, ← Valuation.map_mul, hhd, Valuation.map_neg]
  have hh0 : valuation F h ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hvh
    exact hfb0 ((Valuation.zero_iff _).mp hvh.symm)
  have hhc : valuation F h < valuation F ((f.derivative.eval a : 𝒪[F]) : F) := by
    by_contra hlt
    have hle := not_lt.mp hlt
    have hsq : valuation F ((f.derivative.eval a : 𝒪[F]) : F) ^ 2 ≤
        valuation F ((f.eval b : 𝒪[F]) : F) := by
      rw [pow_two, ← hvh]
      exact mul_le_mul' hle le_rfl
    exact absurd hfb (not_lt.mpr hsq)
  have hmem : h ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).mpr
    (hhc.le.trans (val_le_one _))
  obtain ⟨hO, hcoe⟩ : ∃ hO : 𝒪[F], (hO : F) = h := ⟨⟨h, hmem⟩, rfl⟩
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion f b hO
  have hk' : ((f.eval (b + hO) : 𝒪[F]) : F) = ((f.eval b : 𝒪[F]) : F) +
      ((f.derivative.eval b : 𝒪[F]) : F) * (hO : F) + (k : F) * (hO : F) ^ 2 := by
    exact_mod_cast congrArg Subtype.val hk
  rw [hcoe] at hk'
  refine ⟨b + hO, ?_, ?_⟩
  · have hsum : ((b + hO - a : 𝒪[F]) : F) = ((b - a : 𝒪[F]) : F) + h := by
      push_cast
      rw [hcoe]
      ring
    rw [hsum]
    exact Valuation.map_add_lt _ hba hhc
  · have hval : ((f.eval (b + hO) : 𝒪[F]) : F) = (k : F) * h ^ 2 := by
      rw [hk']
      linear_combination hhd
    rw [hval, Valuation.map_mul, Valuation.map_pow, ← hvh, pow_two]
    calc valuation F (k : F) * (valuation F h * valuation F h)
        ≤ valuation F h * valuation F h :=
          mul_le_of_le_one_left' (val_le_one k)
      _ < valuation F h * valuation F ((f.derivative.eval a : 𝒪[F]) : F) :=
          mul_lt_mul_of_pos_left hhc (lt_of_le_of_ne zero_le (Ne.symm hh0))
end PI.HenselValuation
