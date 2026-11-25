-- Prove2me | solution 1 for PI.FJMP.pure_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:42.806084+00:00
-- url     : https://prove2.me/submissions/952bb606-e6ce-4a8e-bf17-5e7d93840b2a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
namespace PI.FJMP
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι → κ → ℕ) (pos : ι → κ → Bool)
    (h : ∑ a, |∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))| = ∑ a, ∑ c, (x a c : ℤ))
    (a : ι) (c : κ) (hx : x a c ≠ 0) :
    (∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) ≠ 0 ∧
      (pos a c = true ↔ 0 < ∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) := by
  have hrow : ∀ a, |∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))| ≤ ∑ c, (x a c : ℤ) := by
    intro a
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
    split_ifs <;> simp
  have heq : |∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))| = ∑ c, (x a c : ℤ) :=
    (Finset.sum_eq_sum_iff_of_le (fun a _ => hrow a)).mp h a (Finset.mem_univ a)
  have hxpos : (0 : ℤ) < x a c := by exact_mod_cast Nat.pos_of_ne_zero hx
  have hle : (x a c : ℤ) ≤ ∑ c, (x a c : ℤ) :=
    Finset.single_le_sum (f := fun c => (x a c : ℤ)) (fun c _ => Nat.cast_nonneg _) (Finset.mem_univ c)
  rcases le_or_gt 0 (∑ c, (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) with hs | hs
  · rw [abs_of_nonneg hs] at heq
    have hz : ∑ c, ((x a c : ℤ) - (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) = 0 := by
      rw [Finset.sum_sub_distrib, heq, sub_self]
    have hnn : ∀ c ∈ Finset.univ, 0 ≤ (x a c : ℤ) - (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ)) := by
      intro c _
      split_ifs <;> omega
    have hc0 : (x a c : ℤ) - (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz c (Finset.mem_univ c)
    have hpc : pos a c = true := by
      by_contra hpc
      rw [if_neg hpc] at hc0
      omega
    refine ⟨by omega, ?_⟩
    rw [hpc]
    exact ⟨fun _ => by omega, fun _ => rfl⟩
  · rw [abs_of_neg hs] at heq
    have hz : ∑ c, ((x a c : ℤ) + (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ))) = 0 := by
      rw [Finset.sum_add_distrib]
      linarith
    have hnn : ∀ c ∈ Finset.univ, 0 ≤ (x a c : ℤ) + (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ)) := by
      intro c _
      split_ifs <;> omega
    have hc0 : (x a c : ℤ) + (if pos a c = true then (x a c : ℤ) else -(x a c : ℤ)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz c (Finset.mem_univ c)
    have hpc : pos a c = false := by
      by_contra hpc
      rw [if_pos (by simpa using hpc)] at hc0
      omega
    refine ⟨hs.ne, ?_⟩
    rw [hpc]
    constructor
    · intro h'
      exact absurd h' (by decide)
    · intro h'
      exact absurd h' (not_lt.mpr hs.le)
end PI.FJMP
