-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CommMult.commMult_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:35.573363+00:00
-- url     : https://prove2.me/submissions/f7328e33-75b9-49bc-ac5b-197f88796a15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_SchurStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CommutingMultiplicity_CommMultOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CommMult
open Matrix
namespace PI.UnitaryGroupMassFormula.CommMult
theorem _root_.solution (hS : SchurStep) (hI : InjStep) (hA : AvStep) : PI.UMultOne.CommutantMult := by
  intro H _ _ _ _ _ _ N M π σ hπ hσ hirr hcomm Hm hHm
  have key : ∀ T₁ ∈ Hm, T₁ ≠ 0 → ∀ T₂ ∈ Hm, ∃ c : ℂ, c • T₁ = T₂ := by
    intro T₁ h₁ hne T₂ h₂
    rw [hHm] at h₁ h₂
    obtain ⟨X, hX⟩ := hI H N M π σ hirr T₁ h₁ hne
    obtain ⟨S, hSeq, hST⟩ := hA H N M π σ hπ hσ T₁ X h₁ hX
    obtain ⟨c, hc⟩ := hS H M σ hirr (S * T₂) (fun g => by
      rw [← Matrix.mul_assoc, hSeq g, Matrix.mul_assoc, h₂ g, Matrix.mul_assoc])
    refine ⟨c, ?_⟩
    by_contra hne'
    set T := T₂ - c • T₁ with hT
    have hT0 : T ≠ 0 := sub_ne_zero.mpr (Ne.symm hne')
    have hTeq : ∀ g, ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T =
        T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) := fun g => by
      rw [hT, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h₁ g, h₂ g]
    have hST0 : S * T = 0 := by
      rw [hT, Matrix.mul_sub, Matrix.mul_smul, hST, hc, sub_self]
    obtain ⟨X', hX'⟩ := hI H N M π σ hirr T hTeq hT0
    obtain ⟨S', hS'eq, hS'T⟩ := hA H N M π σ hπ hσ T X' hTeq hX'
    have hP : ∀ h, ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (T₁ * S') =
        (T₁ * S') * ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun g => by
      rw [← Matrix.mul_assoc, h₁ g, Matrix.mul_assoc, hS'eq g, Matrix.mul_assoc]
    have hQ : ∀ h, ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (T * S) =
        (T * S) * ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun g => by
      rw [← Matrix.mul_assoc, hTeq g, Matrix.mul_assoc, hSeq g, Matrix.mul_assoc]
    have hPQ := hcomm _ _ hP hQ
    have e1 : T₁ * S' * (T * S) = T₁ * S := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc S', hS'T, Matrix.one_mul]
    have e2 : T * S * (T₁ * S') = T * S' := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, hST, Matrix.one_mul]
    have e3 : T₁ * S = T * S' := by rw [← e1, ← e2, hPQ]
    have e4 : S = 0 := by
      calc S = S * T₁ * S := by rw [hST, Matrix.one_mul]
        _ = S * T * S' := by rw [Matrix.mul_assoc, e3, ← Matrix.mul_assoc]
        _ = 0 := by rw [hST0, Matrix.zero_mul]
    rw [e4, Matrix.zero_mul] at hST
    have hM : M = 0 := by
      by_contra hM
      have h := congrFun (congrFun hST ⟨0, Nat.pos_of_ne_zero hM⟩) ⟨0, Nat.pos_of_ne_zero hM⟩
      simp at h
    subst hM
    exact hT0 (Matrix.ext fun _ j => j.elim0)
  by_cases h0 : ∃ T₁ ∈ Hm, T₁ ≠ 0
  · obtain ⟨T₁, h₁, hne⟩ := h0
    apply finrank_le_one (⟨T₁, h₁⟩ : Hm)
    intro w
    obtain ⟨c, hc⟩ := key T₁ h₁ hne w.1 w.2
    exact ⟨c, Subtype.ext hc⟩
  · push Not at h0
    have hb : Hm = ⊥ := (Submodule.eq_bot_iff _).mpr h0
    subst hb
    simp
end PI.UnitaryGroupMassFormula.CommMult
