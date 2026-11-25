-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_newton_2741b236fc44
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:13:41.646369+00:00
-- url     : https://prove2.me/submissions/ffd2b214-c686-4669-8b3c-ee92f059fd78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_append_874772440c65
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_replicate_0a9c60c52f49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_long_625589269fc3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_binomPoly_totalDegree_cf40ef0210b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_eval_binomPoly_aa54a0e3201d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Finset fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
variable {K : Type} [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
theorem _root_.solution (c : ℕ) (s : Finset K) : ∀ (n : ℕ) (g : (K → ℕ) → ℚ),
    (∀ L : List K, L.length = n + 1 → listDiff L g = 0) →
    ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ n ∧
      (∀ x y : K → ℚ, (∀ i ∈ s, x i = y i) → eval x P = eval y P) ∧
      ∀ t : K → ℕ, (∀ i ∉ s, t i = 0) → g t = eval (fun i => (t i : ℚ) + c) P := by
  induction s using Finset.induction_on with
  | empty =>
    intro n g _
    refine ⟨C (g 0), by rw [totalDegree_C]; exact Nat.zero_le _, fun x y _ => by simp,
      fun t ht => ?_⟩
    have : t = 0 := funext fun i => ht i (Finset.notMem_empty i)
    simp [this]
  | insert k s hk ih =>
    intro n g hg
    have hg' := listDiff_long hg
    have hsub : ∀ j, ∀ L : List K, L.length = n - j + 1 →
        listDiff L ((Δ_[(Pi.single k 1 : K → ℕ)])^[j] g) = 0 := by
      intro j L hL
      rw [← listDiff_replicate, ← listDiff_append]
      exact hg' _ (by simp; omega)
    choose P hPdeg hPloc hPval using fun j => ih (n - j) _ (hsub j)
    have hzero : ∀ j, n + 1 ≤ j → (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g = 0 := fun j hj => by
      rw [← listDiff_replicate]; exact hg' _ (by simp; omega)
    refine ⟨∑ j ∈ range (n + 1), binomPoly c k j * P j, ?_, ?_, ?_⟩
    · refine totalDegree_finsetSum_le fun j hj => ?_
      have := mem_range.mp hj
      refine (totalDegree_mul _ _).trans ?_
      have h1 := binomPoly_totalDegree c k j
      have h2 := hPdeg j
      omega
    · intro x y hxy
      simp only [map_sum, map_mul]
      refine sum_congr rfl fun j _ => ?_
      rw [hPloc j x y fun i hi => hxy i (mem_insert_of_mem hi)]
      congr 1
      unfold binomPoly
      simp [hxy k (mem_insert_self k s)]
    · intro t ht
      set y : K → ℕ := Function.update t k 0 with hy
      have hyt : t = y + t k • (Pi.single k 1 : K → ℕ) := by
        funext i
        by_cases h : i = k
        · subst h; simp [hy]
        · simp [hy, h]
      have hys : ∀ i ∉ s, y i = 0 := by
        intro i hi
        by_cases h : i = k
        · subst h; simp [hy]
        · simp only [hy, Function.update_of_ne h]; exact ht i (by simp [h, hi])
      have hty : ∀ i ∈ s, (t i : ℚ) + c = (y i : ℚ) + c := by
        intro i hi
        have : i ≠ k := fun h => hk (h ▸ hi)
        simp [hy, Function.update_of_ne this]
      have e1 : ∑ j ∈ range (t k + 1), (t k).choose j • (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g y
          = ∑ j ∈ range (n + t k + 1), ((t k).choose j : ℚ) * (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g y := by
        simp only [nsmul_eq_mul]
        refine sum_subset (s₁ := range (t k + 1)) (fun j hj => by rw [mem_range] at hj ⊢; omega) fun j _ hj => ?_
        rw [mem_range, not_lt] at hj
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
      have e2 : eval (fun i => (t i : ℚ) + c) (∑ j ∈ range (n + 1), binomPoly c k j * P j)
          = ∑ j ∈ range (n + t k + 1), ((t k).choose j : ℚ) * (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g y := by
        rw [map_sum]
        refine Eq.trans ?_ (sum_subset (s₁ := range (n + 1)) (fun j hj => by rw [mem_range] at hj ⊢; omega) fun j _ hj => ?_)
        · refine sum_congr rfl fun j _ => ?_
          rw [map_mul, eval_binomPoly c k j _ (t k) rfl, hPval j y hys,
            hPloc j _ (fun i => (y i : ℚ) + c) hty]
        · rw [mem_range, not_lt] at hj
          rw [hzero j hj]
          simp
      calc g t = g (y + t k • (Pi.single k 1 : K → ℕ)) := congrArg g hyt
        _ = ∑ j ∈ range (t k + 1), (t k).choose j • (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g y :=
          shift_eq_sum_fwdDiff_iter _ g (t k) y
        _ = _ := by rw [e1, e2]
end GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
