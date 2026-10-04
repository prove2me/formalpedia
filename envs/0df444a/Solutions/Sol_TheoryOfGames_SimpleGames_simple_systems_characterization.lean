-- Prove2me | solution 1 for TheoryOfGames.SimpleGames.simple_systems_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:37:19.725915+00:00
-- url     : https://prove2.me/submissions/1bdf564c-4ae5-4792-9128-70b7fb174dea

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing

set_option autoImplicit false

namespace P2M44c2af83
open TheoryOfGames.SimpleGames

lemma sum_le {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : IsCharFunction v) (S : Finset (Fin n)) :
    ∑ k ∈ S, v {k} ≤ v S := by
  induction S using Finset.induction_on with
  | empty => simp [hv.1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.insert_eq]
    have := hv.2.2 {a} s (Finset.disjoint_singleton_left.mpr ha)
    linarith

lemma flat_mono {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : IsCharFunction v) {S T : Finset (Fin n)}
    (hS : IsFlat v S) (hTS : T ⊆ S) : IsFlat v T := by
  unfold IsFlat at *
  have h1 := sum_le hv T
  have h2 := sum_le hv (S \ T)
  have h3 := hv.2.2 T (S \ T) Finset.disjoint_sdiff
  rw [Finset.union_sdiff_of_subset hTS] at h3
  have h4 := Finset.sum_sdiff hTS (f := fun k => v {k})
  linarith

lemma ess_sum {n : ℕ} {v : Finset (Fin n) → ℝ} (hv : IsCharFunction v)
    (hne : ¬ IsInessential v) : ∑ k, v {k} ≠ 0 := by
  intro h0
  apply hne
  intro S
  unfold reducedForm
  rw [h0]
  simp only [mul_zero, add_zero, Finset.sum_neg_distrib]
  have h1 := sum_le hv S
  have h2 := sum_le hv Sᶜ
  have h3 := hv.2.1 S
  have h4 := Finset.sum_add_sum_compl S (fun k => v {k})
  linarith

end P2M44c2af83

open TheoryOfGames.SimpleGames in
theorem solution {n : ℕ} (W L : Set (Finset (Fin n))) :
    (∃ v : Finset (Fin n) → ℝ, IsCharFunction v ∧ IsSimple v ∧
        winningSets v = W ∧ losingSets v = L) ↔
      ((∀ S : Finset (Fin n), S ∈ W ↔ S ∉ L) ∧
        (∀ S : Finset (Fin n), S ∈ W ↔ Sᶜ ∈ L) ∧
        (∀ S T : Finset (Fin n), S ∈ W → S ⊆ T → T ∈ W) ∧
        (∀ S T : Finset (Fin n), S ∈ L → T ⊆ S → T ∈ L) ∧
        (∅ ∈ L ∧ ∀ i : Fin n, ({i} : Finset (Fin n)) ∈ L)) := by
  constructor
  · rintro ⟨v, hv, hs, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro S
      constructor
      · intro hW hL
        apply P2M44c2af83.ess_sum hv hs.1
        have h3 := hv.2.1 S
        have h4 := Finset.sum_add_sum_compl S (fun k => v {k})
        simp only [winningSets, losingSets, Set.mem_setOf_eq, IsFlat] at hW hL
        linarith
      · intro hL
        rcases hs.2 S with h | h
        · exact h
        · exact absurd h hL
    · intro S
      exact Iff.rfl
    · intro S T hS hST
      exact P2M44c2af83.flat_mono hv hS (Finset.compl_subset_compl.mpr hST)
    · intro S T hS hTS
      exact P2M44c2af83.flat_mono hv hS hTS
    · refine ⟨?_, fun i => ?_⟩
      · show IsFlat v ∅
        simp [IsFlat, hv.1]
      · show IsFlat v {i}
        simp [IsFlat]
  · rintro ⟨ha, hb, hc, hd, he0, he1⟩
    classical
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        exfalso
        have h1 := (hb ∅).mpr
        have h2 : (∅ : Finset (Fin 0))ᶜ = ∅ := by
          ext x
          exact x.elim0
        rw [h2] at h1
        exact (ha ∅).mp (h1 he0) he0
      · exact h
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    let v : Finset (Fin n) → ℝ := fun S => if S ∈ L then -(S.card : ℝ) else (n : ℝ) - S.card
    have hvL : ∀ X, X ∈ L → v X = -(X.card : ℝ) := fun X h => by simp [v, h]
    have hvW : ∀ X, X ∉ L → v X = (n : ℝ) - X.card := fun X h => by simp [v, h]
    have hv1 : ∀ k : Fin n, v {k} = -1 := fun k => by rw [hvL _ (he1 k)]; simp
    have hWof : ∀ X, X ∉ L → X ∈ W := fun X h => (ha X).mpr h
    have hflat : ∀ S, IsFlat v S ↔ S ∈ L := by
      intro S
      have hsum : ∑ k ∈ S, v {k} = -(S.card : ℝ) := by simp [hv1]
      unfold IsFlat
      rw [hsum]
      by_cases h : S ∈ L
      · rw [hvL S h]
        exact ⟨fun _ => h, fun _ => rfl⟩
      · rw [hvW S h]
        constructor
        · intro h'
          exact absurd (by linarith : (n : ℝ) = 0) hnR
        · intro h'
          exact absurd h' h
    have hcard : ∀ S : Finset (Fin n), (S.card : ℝ) + (Sᶜ.card : ℝ) = n := by
      intro S
      have := Finset.card_add_card_compl S
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have hchar : IsCharFunction v := by
      unfold IsCharFunction
      refine ⟨?_, ?_, ?_⟩
      · rw [hvL _ he0]; simp
      · intro S
        have hc' := hcard S
        by_cases h : S ∈ L
        · have hSc : Sᶜ ∉ L := by
            intro h'
            exact (ha S).mp ((hb S).mpr h') h
          rw [hvW _ hSc, hvL _ h]
          linarith
        · have hSc : Sᶜ ∈ L := (hb S).mp (hWof S h)
          rw [hvL _ hSc, hvW _ h]
          linarith
      · intro S T hST
        have hcu : ((S ∪ T).card : ℝ) = S.card + T.card := by
          exact_mod_cast Finset.card_union_of_disjoint hST
        have hnn : (0 : ℝ) ≤ n := by positivity
        have hTsub : T ⊆ Sᶜ := by
          intro x hx
          rw [Finset.mem_compl]
          exact Finset.disjoint_right.mp hST hx
        have hSsub : S ⊆ Tᶜ := by
          intro x hx
          rw [Finset.mem_compl]
          exact Finset.disjoint_left.mp hST hx
        by_cases hS : S ∈ L
        · by_cases hT : T ∈ L
          · rw [hvL _ hS, hvL _ hT]
            by_cases hU : S ∪ T ∈ L
            · rw [hvL _ hU]; linarith
            · rw [hvW _ hU]; linarith
          · have hS' : S ∈ L := hd Tᶜ S ((hb T).mp (hWof T hT)) hSsub
            have hU : S ∪ T ∉ L :=
              (ha _).mp (hc T _ (hWof T hT) Finset.subset_union_right)
            rw [hvL _ hS', hvW _ hT, hvW _ hU]
            linarith
        · have hT : T ∈ L := hd Sᶜ T ((hb S).mp (hWof S hS)) hTsub
          have hU : S ∪ T ∉ L :=
            (ha _).mp (hc S _ (hWof S hS) Finset.subset_union_left)
          rw [hvW _ hS, hvL _ hT, hvW _ hU]
          linarith
    have hWeq : winningSets v = W := by
      ext S
      show IsFlat v Sᶜ ↔ S ∈ W
      rw [hflat]
      exact (hb S).symm
    have hLeq : losingSets v = L := by
      ext S
      exact hflat S
    refine ⟨v, hchar, ?_, hWeq, hLeq⟩
    unfold IsSimple
    refine ⟨?_, fun S => ?_⟩
    · intro hI
      have h := hI {⟨0, hn⟩}
      unfold reducedForm at h
      have hsumall : ∑ j : Fin n, v {j} = -(n : ℝ) := by simp [hv1]
      rw [hsumall, Finset.sum_singleton, hv1] at h
      have hdiv : 1 / (n : ℝ) * (-(n : ℝ)) = -1 := by field_simp
      rw [hdiv] at h
      norm_num at h
    · rw [hWeq, hLeq]
      by_cases h : S ∈ L
      · exact Or.inr h
      · exact Or.inl (hWof S h)
