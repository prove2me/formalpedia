-- Prove2me | solution 1 for SRAudit.TwoPhase.proposition_D_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T22:54:06.946915+00:00
-- url     : https://prove2.me/submissions/b7e187d0-7dd8-4941-b815-3f8827835604

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting

namespace SRAudit.TwoPhase.SolD2

open SRAudit.TwoPhase

variable {ι : Type} [DecidableEq ι]

theorem Var_closed (P : Params) (hP : P.Standing) (π : Network ι → ℝ) :
    ∀ n, ∀ γ : State ι, γ.U.card = n → Var P π γ = π γ.g - crp P * γ.U.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro γ hn
    by_cases h : γ.U.Nonempty
    · rw [Var, dif_pos h]
      set c := P.a + P.u * P.r
      set e := P.u * P.w * P.z
      have hce : crp P ≤ c := min_le_right _ _
      have hee : crp P ≤ e := min_le_left _ _
      have hcard : (0:ℝ) ≤ γ.U.card := by positivity
      -- every branch value equals the same constant
      have hb : ∀ i : γ.U, -P.a - P.u * P.r + Var P π (vet γ i.val)
          = π γ.g - crp P * γ.U.card + (crp P - c) := by
        intro i
        have hlt : (vet γ i.val).U.card < n := by
          rw [← hn]; simpa [vet] using Finset.card_erase_lt_of_mem i.property
        rw [ih _ hlt _ rfl]
        have h1 := Finset.card_erase_add_one i.property
        have h2 : ((γ.U.erase i.val).card : ℝ) + 1 = γ.U.card := by exact_mod_cast h1
        simp only [vet, c]
        linear_combination (-(crp P)) * h2
      have hs : γ.U.attach.sup' (by simpa using h) (fun i =>
          -P.a - P.u * P.r + Var P π (vet γ i.val)) = π γ.g - crp P * γ.U.card + (crp P - c) := by
        apply le_antisymm
        · exact Finset.sup'_le _ _ (fun i _ => (hb i).le)
        · obtain ⟨i, hi⟩ := h
          exact (hb ⟨i, hi⟩).symm.le.trans (Finset.le_sup' (fun i : γ.U =>
            -P.a - P.u * P.r + Var P π (vet γ i.val)) (Finset.mem_attach _ ⟨i, hi⟩))
      rw [hs]
      simp only [ppValue, zeta]
      rcases min_choice e c with hm | hm
      · have hm' : crp P = e := hm
        rw [hm'] at hce ⊢
        rw [max_eq_left]
        · simp only [e]; ring
        · simp only [e]; nlinarith
      · have hm' : crp P = c := hm
        rw [hm'] at hee ⊢
        rw [max_eq_right]
        · ring
        · simp only [e] at hee; nlinarith
    · have hU : γ.U = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      rw [Var, dif_neg h]; simp [ppValue, zeta, hU]

end SRAudit.TwoPhase.SolD2

open SRAudit.TwoPhase SRAudit.TwoPhase.SolD2 in
theorem solution {ι : Type} [DecidableEq ι] (P : Params)
    (hP : P.Standing) (π : Network ι → ℝ) (γ : State ι) :
    Var P π γ = π γ.g - crp P * γ.U.card ∧
    (P.a + P.u * P.r ≤ P.u * P.w * P.z →
      ∀ i ∈ γ.U, Qar P π γ (.ar i) = Var P π γ) ∧
    (P.u * P.w * P.z ≤ P.a + P.u * P.r →
      Qar P π γ .pp = Var P π γ) := by
  have hV := Var_closed P hP π _ γ rfl
  refine ⟨hV, ?_, ?_⟩
  · intro hce i hi
    have hc : crp P = P.a + P.u * P.r := min_eq_right hce
    have hv := Var_closed P hP π _ (vet γ i) rfl
    have h1 := Finset.card_erase_add_one hi
    have h2 : ((γ.U.erase i).card : ℝ) + 1 = γ.U.card := by exact_mod_cast h1
    simp only [Qar, if_pos hi]
    rw [hv, hV]
    simp only [vet, hc]
    linear_combination (-(P.a + P.u * P.r)) * h2
  · intro hec
    have hc : crp P = P.u * P.w * P.z := min_eq_left hec
    simp only [Qar, ppValue, zeta]
    rw [hV, hc]; ring
