-- Prove2me | solution 1 for PrivLittlestone.eq_21
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:10:44.933475+00:00
-- url     : https://prove2.me/submissions/9833b62e-85e2-44e1-baac-79345ac0e260

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_PrivLittlestone_localUniverse
import Definitions.Def_PrivLittlestone_rankLayer
import Definitions.Def_PrivLittlestone_restrictCls
import Definitions.Def_PrivLittlestone_rankOf
import Definitions.Def_PrivLittlestone_witnessSpace
import Definitions.Def_PrivLittlestone_IsWitnessAssignment
import Definitions.Def_PrivLittlestone_versionCell
import Definitions.Def_PrivLittlestone_selDesc
import Definitions.Def_PrivLittlestone_selD

section
set_option autoImplicit false

namespace PrivLittlestone.Dev.Sel

variable {X : Type*}

theorem selDesc_mono (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) {k k' : ℕ} (hk : k ≤ k') : selDesc H d Aw V k ⊆ selDesc H d Aw V k' := by
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; exact subset_rfl
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with h | h
    · refine (ih (by omega)).trans ?_
      intro g hg
      simp only [selDesc]
      split_ifs
      · exact Or.inl hg
      · exact hg
    · have : k = k' + 1 := by omega
      subst this; exact subset_rfl

theorem selDesc_prop (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) (k : ℕ) :
    ∀ g ∈ selDesc H d Aw V k, g ∈ V ∧ d - k ≤ rankOf H d g := by
  induction k with
  | zero => intro g hg; exact ⟨hg.1, by simp [hg.2]⟩
  | succ k ih =>
    intro g hg
    simp only [selDesc] at hg
    split_ifs at hg with hk
    · rcases hg with hg | hg
      · have := ih g hg; exact ⟨this.1, by omega⟩
      · exact ⟨hg.1, by rw [hg.2.1]⟩
    · have := ih g hg; exact ⟨this.1, by omega⟩

theorem coverage (H : Set (X → Bool)) (d : ℕ) (Aw : (X → Bool) → Finset X)
    (V : Set (X → Bool)) (hVU : V ⊆ localUniverse H d) (h : X → Bool) (hh : h ∈ V) :
    ∃ g ∈ selD H d Aw V, h ∈ witnessSpace H d Aw g ∧ rankOf H d h ≤ rankOf H d g ∧
      (h ∉ selD H d Aw V → rankOf H d h < rankOf H d g) := by
  classical
  by_cases hsel : h ∈ selD H d Aw V
  · exact ⟨h, hsel, ⟨hVU hh, fun _ _ => rfl⟩, le_rfl, fun hn => absurd hsel hn⟩
  · have hrd : rankOf H d h ≤ d := Nat.findGreatest_le _
    have hrlt : rankOf H d h < d := by
      by_contra hc
      apply hsel
      have : rankOf H d h = d := by omega
      apply selDesc_mono H d Aw V (Nat.zero_le d)
      exact ⟨hh, this⟩
    have hnot : h ∉ selDesc H d Aw V (d - rankOf H d h) :=
      fun hm => hsel (selDesc_mono H d Aw V (Nat.sub_le d _) hm)
    have hk : d - rankOf H d h = (d - rankOf H d h - 1) + 1 := by omega
    rw [hk] at hnot
    simp only [selDesc] at hnot
    rw [if_pos (by omega)] at hnot
    have : ¬ (h ∈ selDesc H d Aw V (d - rankOf H d h - 1) ∨
        h ∈ {h ∈ V | rankOf H d h = d - (d - rankOf H d h - 1 + 1) ∧
          ∀ g ∈ selDesc H d Aw V (d - rankOf H d h - 1), h ∉ witnessSpace H d Aw g}) := hnot
    push Not at this
    obtain ⟨h1, h2⟩ := this
    have h3 : ¬ ∀ g ∈ selDesc H d Aw V (d - rankOf H d h - 1), h ∉ witnessSpace H d Aw g := by
      intro hall
      exact h2 ⟨hh, by omega, hall⟩
    push Not at h3
    obtain ⟨g, hg, hgW⟩ := h3
    have hgp := selDesc_prop H d Aw V _ g hg
    have hgsel : g ∈ selD H d Aw V :=
      selDesc_mono H d Aw V (by omega : d - rankOf H d h - 1 ≤ d) hg
    have hr : rankOf H d h + 1 ≤ rankOf H d g := by have := hgp.2; omega
    exact ⟨g, hgsel, hgW, by omega, fun _ => by omega⟩

end PrivLittlestone.Dev.Sel

namespace PrivLittlestone

open PrivLittlestone.Dev.Sel

theorem chk_eq_21 {X : Type*} (H : Set (X → Bool)) (d : ℕ) (hH : H.Nonempty)
    (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d) (Aw : (X → Bool) → Finset X)
    (hAw : IsWitnessAssignment H d Aw) (S : List (X × Bool)) (v : Fin S.length → Bool)
    (hV : (versionCell H d S v).Nonempty) :
    ∀ h ∈ versionCell H d S v, ∃ g ∈ selD H d Aw (versionCell H d S v),
      h ∈ witnessSpace H d Aw g ∧ rankOf H d h ≤ rankOf H d g ∧
        (h ∉ selD H d Aw (versionCell H d S v) → rankOf H d h < rankOf H d g) :=
  fun h hh => coverage H d Aw _ (fun f hf => hf.1) h hh

end PrivLittlestone
end

theorem solution : type_of% @PrivLittlestone.chk_eq_21 := @PrivLittlestone.chk_eq_21
