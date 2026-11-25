-- Prove2me | solution 1 for P2M_Formalism_L2_Pj_GenSect_exists_pderiv_ne_zero_lt__42a374650296
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:09:46.639287+00:00
-- url     : https://prove2.me/submissions/0985b69c-759a-4a86-98a5-9dc2fc123254

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial Cardinal
open MvPolynomial
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution {K : Type*} [Field K] [CharZero K] {ι : Type*}
    (P : MvPolynomial ι K) (hP : 0 < P.totalDegree) :
    ∃ i, pderiv i P ≠ 0 ∧ (pderiv i P).totalDegree < P.totalDegree := by
  classical
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
  obtain ⟨s, hs, hsd⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.2 hP0)
    (fun s : ι →₀ ℕ => s.sum fun _ e => e)
  have htd : P.totalDegree = s.sum fun _ e => e := hsd
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [htd] at hP
    simp at hP
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hs0 (Finsupp.ext h)
  have hdeg : ∀ t : ι →₀ ℕ, t i ≠ 0 →
      (t.sum fun _ e => e) = ((t - Finsupp.single i 1).sum fun _ e => e) + 1 := by
    intro t ht
    have hle : Finsupp.single i 1 ≤ t := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ht)
    conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hder : pderiv i P =
      ∑ t ∈ P.support, monomial (t - Finsupp.single i 1) (coeff t P * (t i : K)) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pderiv_monomial]
  refine ⟨i, ?_, ?_⟩
  · intro h0
    have hc := congrArg (coeff (s - Finsupp.single i 1)) h0
    rw [hder, coeff_sum, coeff_zero, Finset.sum_eq_single s] at hc
    · rw [coeff_monomial, if_pos rfl] at hc
      exact mul_ne_zero (mem_support_iff.1 hs) (by exact_mod_cast hi) hc
    · intro t _ hts
      rw [coeff_monomial]
      split_ifs with heq
      · by_cases hti : t i = 0
        · simp [hti]
        · exfalso
          apply hts
          have h1 : Finsupp.single i 1 ≤ t := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hti)
          have h2 : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
          rw [← tsub_add_cancel_of_le h1, ← tsub_add_cancel_of_le h2, heq]
      · rfl
    · intro hns
      exact absurd hs hns
  · have hpos : (⊥ : ℕ) < s.sum fun _ e => e := by
      rw [← htd]
      exact hP
    rw [htd, hder]
    refine lt_of_le_of_lt (totalDegree_finset_sum _ _) ((Finset.sup_lt_iff hpos).2 fun t ht => ?_)
    by_cases hti : t i = 0
    · simpa [hti, htd] using hP
    · refine lt_of_le_of_lt (totalDegree_monomial_le _ _) ?_
      have h1 := hdeg t hti
      have h2 : (t.sum fun _ e => e) ≤ s.sum fun _ e => e := by
        rw [← htd]
        exact le_totalDegree ht
      rw [h1] at h2
      exact h2
end Formalism.L2.Pj.GenSect
