-- Prove2me | solution 1 for TheoryOfGames.SimpleGames.disjoint_iff_essential
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:59:59.234071+00:00
-- url     : https://prove2.me/submissions/e44eaf03-f7b4-44d3-8092-57707b3c2503

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing

namespace A8168d22Aux

open TheoryOfGames.SimpleGames

theorem sum_le {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) (S : Finset (Fin n)) :
    ∑ k ∈ S, v {k} ≤ v S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hv.1]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.insert_eq]
    have hd : Disjoint ({a} : Finset (Fin n)) S := Finset.disjoint_singleton_left.mpr ha
    have := hv.2.2 {a} S hd
    linarith

theorem flat_of_gamma {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hg : ∑ j, v {j} = 0) (S : Finset (Fin n)) : IsFlat v S := by
  unfold IsFlat
  have h1 := sum_le v hv S
  have h2 := sum_le v hv Sᶜ
  have h3 := hv.2.1 S
  have h4 := Finset.sum_add_sum_compl S (fun k => v {k})
  linarith

theorem gamma_of_ines {n : ℕ} (v : Finset (Fin n) → ℝ) (h : IsInessential v) :
    ∑ j, v {j} = 0 := by
  cases n with
  | zero => simp
  | succ k =>
    have h0 := h {0}
    unfold reducedForm at h0
    simp only [Finset.sum_singleton] at h0
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have : (1 / ((k + 1 : ℕ) : ℝ)) * ∑ j, v {j} = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · simp at h'; exact absurd h' (by positivity)
    · exact h'

theorem ines_of_gamma {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hg : ∑ j, v {j} = 0) : IsInessential v := by
  intro S
  unfold reducedForm
  rw [hg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have := flat_of_gamma v hv hg S
  unfold IsFlat at this
  simp only [mul_zero, Finset.sum_const_zero]
  linarith

end A8168d22Aux

open TheoryOfGames.SimpleGames in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) :
    ((∀ S : Finset (Fin n), ¬ (S ∈ winningSets v ∧ S ∈ losingSets v)) ↔ ¬ IsInessential v) ∧
    (IsInessential v → winningSets v = Set.univ ∧ losingSets v = Set.univ) := by
  refine ⟨⟨fun h hi => ?_, fun hne S hS => ?_⟩, fun hi => ?_⟩
  · have hg := A8168d22Aux.gamma_of_ines v hi
    exact h ∅ ⟨A8168d22Aux.flat_of_gamma v hv hg _, A8168d22Aux.flat_of_gamma v hv hg _⟩
  · apply hne
    apply A8168d22Aux.ines_of_gamma v hv
    obtain ⟨hW, hL⟩ := hS
    have hW' : v Sᶜ = ∑ k ∈ Sᶜ, v {k} := hW
    have hL' : v S = ∑ k ∈ S, v {k} := hL
    have h3 := hv.2.1 S
    have h4 := Finset.sum_add_sum_compl S (fun k => v {k})
    linarith
  · have hg := A8168d22Aux.gamma_of_ines v hi
    refine ⟨Set.eq_univ_of_forall fun S => ?_, Set.eq_univ_of_forall fun S => ?_⟩
    · exact A8168d22Aux.flat_of_gamma v hv hg _
    · exact A8168d22Aux.flat_of_gamma v hv hg _
