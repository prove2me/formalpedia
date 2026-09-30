-- Prove2me | solution 1 for UnderstandingML.kraft_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T13:48:15.298566+00:00
-- url     : https://prove2.me/submissions/4719f576-9b5f-4b6a-9d9b-0869d81e4f6d

import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic


/-- Kraft's inequality for a finite prefix-free family of binary strings whose lengths are
bounded by `N`, proved by induction on `N` by splitting on the first bit. -/
theorem UnderstandingML.kraft_inequality_of_length_le (N : ℕ) :
    ∀ F : Finset (List Bool), (∀ σ ∈ F, σ.length ≤ N) →
    (∀ σ ∈ F, ∀ τ ∈ F, σ ≠ τ → ¬ (σ <+: τ)) →
    ∑ σ ∈ F, (1 / 2 : ℝ) ^ σ.length ≤ 1 := by
  induction N with
  | zero =>
    intro F hlen hpf
    have hsub : F ⊆ {[]} := by
      intro σ hσ
      have := hlen σ hσ
      simp_all
    calc ∑ σ ∈ F, (1 / 2 : ℝ) ^ σ.length
        ≤ ∑ σ ∈ ({[]} : Finset (List Bool)), (1 / 2 : ℝ) ^ σ.length :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 := by simp
  | succ N ih =>
    intro F hlen hpf
    by_cases hnil : [] ∈ F
    · have hF : F = {[]} := by
        ext σ
        simp only [Finset.mem_singleton]
        constructor
        · intro hσ
          by_contra hne
          exact hpf [] hnil σ hσ (Ne.symm hne) (List.nil_prefix)
        · rintro rfl; exact hnil
      subst hF
      simp
    · have key : ∀ b : Bool,
          ∑ σ ∈ F.filter (fun σ => σ.head? = some b), (1 / 2 : ℝ) ^ σ.length ≤ 1 / 2 := by
        intro b
        have hinj : Set.InjOn (List.cons b)
            (List.cons b ⁻¹' ↑(F.filter (fun σ => σ.head? = some b))) :=
          fun x _ y _ h => List.cons_injective h
        rw [← Finset.sum_preimage (List.cons b) _ hinj]
        · have h2 := ih ((F.filter (fun σ => σ.head? = some b)).preimage (List.cons b) hinj)
            (by
              intro σ hσ
              simp only [Finset.mem_preimage, Finset.mem_filter] at hσ
              have := hlen _ hσ.1
              simp at this
              omega)
            (by
              intro σ hσ τ hτ hne hst
              simp only [Finset.mem_preimage, Finset.mem_filter] at hσ hτ
              exact hpf _ hσ.1 _ hτ.1 (by simpa using hne) (List.cons_prefix_cons.mpr ⟨rfl, hst⟩))
          simp only [List.length_cons, pow_succ, ← Finset.sum_mul]
          nlinarith
        · intro x hx hr
          simp only [Finset.mem_filter] at hx
          exfalso
          apply hr
          match x, hx with
          | c :: t, ⟨_, h⟩ =>
            simp at h
            exact ⟨t, by rw [h]⟩
      rw [← Finset.sum_filter_add_sum_filter_not F (fun σ => σ.head? = some true)]
      have hc : F.filter (fun σ => ¬ σ.head? = some true) =
          F.filter (fun σ => σ.head? = some false) := by
        apply Finset.filter_congr
        intro σ hσ
        match σ with
        | [] => exact absurd hσ hnil
        | c :: t => cases c <;> simp
      rw [hc]
      linarith [key true, key false]

/-- **Lemma 7.6 (Kraft Inequality).** -/
theorem solution (S : Set (List Bool))
    (hpf : ∀ σ ∈ S, ∀ τ ∈ S, σ ≠ τ → ¬ (σ <+: τ)) :
    ∀ F : Finset (List Bool), ↑F ⊆ S → ∑ σ ∈ F, (1 / 2 : ℝ) ^ σ.length ≤ 1 := by
  intro F hF
  exact UnderstandingML.kraft_inequality_of_length_le (F.sup List.length) F
    (fun σ hσ => Finset.le_sup (f := List.length) hσ)
    (fun σ hσ τ hτ => hpf σ (hF hσ) τ (hF hτ))
