-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.sqrt_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:00:09.033194+00:00
-- url     : https://prove2.me/submissions/8b6c04c8-d002-4d90-b807-de5b018e11b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedSqrt
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {E : Type} [Field E] [CharZero E] (k : Subfield E) (h : E[X]) (hm : h.Monic)
    (hk : ∀ i, (h ^ 2).coeff i ∈ k) : ∀ i, h.coeff i ∈ k := by
  have key : ∀ m i : ℕ, h.natDegree ≤ i + m → h.coeff i ∈ k := by
    intro m
    induction m with
    | zero =>
      intro i hi
      rcases Nat.eq_or_lt_of_le (by simpa using hi : h.natDegree ≤ i) with h1 | h1
      · rw [← h1, hm.coeff_natDegree]; exact k.one_mem
      · rw [coeff_eq_zero_of_natDegree_lt h1]; exact k.zero_mem
    | succ m ih =>
      intro i hi
      by_cases h0 : h.natDegree ≤ i + m
      · exact ih i h0
      have hin : i < h.natDegree := by omega
      set n := h.natDegree with hn
      have hmem : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (i + n),
          h.coeff x.1 * h.coeff x.2 - (if x = (i, n) then h.coeff i else 0)
            - (if x = (n, i) then h.coeff i else 0) ∈ k := by
        rintro ⟨a, b⟩ hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        simp only at hx
        by_cases ha : a = i
        · have hb : b = n := by omega
          subst ha; subst hb
          have hne : ¬ ((a, h.natDegree) = (h.natDegree, a)) := by
            intro he
            have := (Prod.mk.injEq _ _ _ _ ▸ he : a = h.natDegree ∧ h.natDegree = a).1
            omega
          rw [if_pos rfl, if_neg hne, hm.coeff_natDegree]
          simp [k.zero_mem]
        by_cases ha' : a = n
        · have hb : b = i := by omega
          subst hb
          rw [ha']
          have hne : ¬ ((n, b) = (b, n)) := by
            intro he
            have := (Prod.mk.injEq _ _ _ _ ▸ he : n = b ∧ b = n).1
            omega
          rw [if_neg hne, if_pos rfl, hn, hm.coeff_natDegree]
          simp [k.zero_mem]
        have hne1 : ¬ ((a, b) = (i, n)) := fun he => ha (congrArg Prod.fst he)
        have hne2 : ¬ ((a, b) = (n, i)) := fun he => ha' (congrArg Prod.fst he)
        rw [if_neg hne1, if_neg hne2, sub_zero, sub_zero]
        rcases lt_or_gt_of_ne ha with h1 | h1
        · have : n < b := by omega
          show h.coeff a * h.coeff b ∈ k
          rw [coeff_eq_zero_of_natDegree_lt this, mul_zero]; exact k.zero_mem
        · rcases lt_or_gt_of_ne ha' with h2 | h2
          · exact k.mul_mem (ih a (by omega)) (ih b (by omega))
          · show h.coeff a * h.coeff b ∈ k
            rw [coeff_eq_zero_of_natDegree_lt h2, zero_mul]; exact k.zero_mem
      have hsum := k.sum_mem hmem
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← coeff_mul, ← pow_two,
        Finset.sum_ite_eq', Finset.sum_ite_eq',
        if_pos (by simp),
        if_pos (by simp [add_comm])] at hsum
      have h2 : (2 : E) * h.coeff i ∈ k := by
        have := k.sub_mem (hk (i + n)) hsum
        have e : (h ^ 2).coeff (i + n) - ((h ^ 2).coeff (i + n) - h.coeff i - h.coeff i)
            = 2 * h.coeff i := by ring
        rwa [e] at this
      have h2k : (2 : E) ∈ k := by
        have := k.add_mem k.one_mem k.one_mem
        rwa [one_add_one_eq_two] at this
      have := k.mul_mem (k.inv_mem h2k) h2
      rwa [← mul_assoc, inv_mul_cancel₀ (two_ne_zero), one_mul] at this
  intro i
  exact key h.natDegree i (by omega)
end ReciprocityTheory.ChartRestriction.L1
