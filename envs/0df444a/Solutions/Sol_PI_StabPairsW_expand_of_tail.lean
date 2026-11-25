-- Prove2me | solution 1 for PI.StabPairsW.expand_of_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:27:41.22665+00:00
-- url     : https://prove2.me/submissions/898a363e-8f86-4f67-94f3-f6712416666e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (b : Fin (r + 1))
    (y : Fin (2 * r + k + 1) → ℂ) (hy : ∀ i : Fin (2 * r + k + 1), b.val ≤ i.val → y i = fvec k r z b i) :
    y = ∑ a, coefOf (k := k) b y a • fvec k r z a := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
  simp only [coefOf, if_pos rfl, one_mul]
  have hrest : ∀ a ∈ Finset.univ.erase b, (if a = b then (1 : ℂ) else
      if h : a.val < b.val then y (eI k r ⟨a.val, by omega⟩) else 0) * fvec k r z a i =
      if h : a.val < b.val ∧ i.val = a.val then y i else 0 := by
    intro a ha
    have hab : a ≠ b := Finset.ne_of_mem_erase ha
    rw [if_neg hab]
    by_cases hlt : a.val < b.val
    · rw [dif_pos hlt]
      have har : a.val < r := by omega
      have hf : fvec k r z a = bvec (eI k r ⟨a.val, har⟩) := by simp [fvec, har]
      rw [hf]
      by_cases hia : i.val = a.val
      · rw [dif_pos ⟨hlt, hia⟩]
        have hi : i = eI k r ⟨a.val, har⟩ := Fin.ext (by simp [eI, hia])
        subst hi
        simp [bvec]
      · rw [dif_neg (fun h => hia h.2)]
        have hi : i ≠ eI k r ⟨a.val, har⟩ := fun h => hia (by rw [h]; simp [eI])
        simp [bvec, Pi.single_apply, hi]
    · rw [dif_neg hlt, dif_neg (fun h => hlt h.1), zero_mul]
  rw [Finset.sum_congr rfl hrest]
  by_cases hib : b.val ≤ i.val
  · rw [hy i hib, Finset.sum_eq_zero]
    · simp
    · intro a _
      rw [dif_neg]
      omega
  · have hir : i.val < r := by omega
    have hfb : fvec k r z b i = 0 := by
      unfold fvec
      split_ifs with hbr
      · have hne : i ≠ eI k r ⟨b.val, hbr⟩ := fun h => by
          have := congrArg Fin.val h
          simp [eI] at this
          omega
        simp [bvec, Pi.single_apply, hne]
      · exact hz i (Or.inl hir)
    rw [hfb, mul_zero, zero_add]
    rw [Finset.sum_eq_single ⟨i.val, by omega⟩]
    · rw [dif_pos ⟨by simp; omega, rfl⟩]
    · intro a _ ha
      rw [dif_neg]
      rintro ⟨-, h2⟩
      exact ha (Fin.ext h2.symm)
    · intro ha
      exfalso
      apply ha
      rw [Finset.mem_erase]
      refine ⟨fun h => ?_, Finset.mem_univ _⟩
      have := congrArg Fin.val h
      simp at this
      omega
end PI.StabPairsW
