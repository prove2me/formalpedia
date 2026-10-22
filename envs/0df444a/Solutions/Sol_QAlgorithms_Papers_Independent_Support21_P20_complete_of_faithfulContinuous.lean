-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P20.complete_of_faithfulContinuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T07:17:43.747189+00:00
-- url     : https://prove2.me/submissions/67f1cf01-c5cc-4ebe-8713-e7adcc7878ac

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

theorem g67c_key (A : Type u) [BooleanAlgebra A]
    (nu : A → ℝ≥0) (hnu : IsPositiveContinuousValuation nu)
    (hfaithful : ∀ a, nu a = 0 → a = ⊥)
    (hcountable : ∀ s : Set A, s.Countable → ∃ a : A, IsLUB s a) (s : Set A) :
    ∃ t ⊆ s, t.Countable ∧ ∃ a, IsLUB t a ∧ IsLUB s a := by
  classical
  obtain ⟨⟨hbot, hmod⟩, hmono, -⟩ := hnu
  let V : Set ℝ := {r | ∃ t ⊆ s, t.Countable ∧ ∃ a, IsLUB t a ∧ r = (nu a : ℝ)}
  have hVne : V.Nonempty := by
    obtain ⟨a, ha⟩ := hcountable ∅ Set.countable_empty
    exact ⟨_, ∅, Set.empty_subset _, Set.countable_empty, a, ha, rfl⟩
  have hVbdd : BddAbove V := by
    refine ⟨(nu ⊤ : ℝ), ?_⟩
    rintro r ⟨t, -, -, a, -, rfl⟩
    exact_mod_cast hmono le_top
  set M := sSup V
  have hch : ∀ n : ℕ, ∃ t ⊆ s, t.Countable ∧ ∃ a, IsLUB t a ∧ M - 1 / ((n : ℝ) + 1) < nu a := by
    intro n
    have hlt : M - 1 / ((n : ℝ) + 1) < M := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨r, ⟨t, hts, htc, a, ha, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hVne hlt
    exact ⟨t, hts, htc, a, ha, hr⟩
  choose T hTs hTc aT haT hlt using hch
  set t := ⋃ n, T n
  have hts : t ⊆ s := Set.iUnion_subset hTs
  have htc : t.Countable := Set.countable_iUnion hTc
  obtain ⟨a, ha⟩ := hcountable t htc
  have hsub : ∀ n, nu (aT n) ≤ nu a := fun n =>
    hmono ((haT n).2 (fun x hx => ha.1 (Set.mem_iUnion.2 ⟨n, hx⟩)))
  refine ⟨t, hts, htc, a, ha, ?_, ?_⟩
  · intro x hx
    obtain ⟨b, hb⟩ := hcountable (insert x t) (htc.insert x)
    have hab : a ≤ b := ha.2 (fun y hy => hb.1 (Set.mem_insert_of_mem x hy))
    have hbV : (nu b : ℝ) ≤ M :=
      le_csSup hVbdd ⟨insert x t, Set.insert_subset hx hts, htc.insert x, b, hb, rfl⟩
    have hdec : nu a + nu (b \ a) = nu b := by
      have := hmod a (b \ a)
      rw [sup_sdiff_self_right, sup_eq_right.2 hab, inf_sdiff_self_right, hbot, add_zero] at this
      exact this
    have hz : nu (b \ a) = 0 := by
      have hle : ∀ n : ℕ, (nu (b \ a) : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
        intro n
        have h1 := hlt n
        have h2 : (nu (aT n) : ℝ) ≤ nu a := by exact_mod_cast hsub n
        have h3 : (nu a : ℝ) + nu (b \ a) = nu b := by exact_mod_cast hdec
        linarith
      have h0 : (nu (b \ a) : ℝ) ≤ 0 := by
        apply le_of_forall_pos_le_add
        intro ε hε
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        linarith [hle n]
      have : (nu (b \ a) : ℝ) = 0 := le_antisymm h0 (NNReal.coe_nonneg _)
      exact_mod_cast this
    have hba := hfaithful _ hz
    have : b ≤ a := by rw [sdiff_eq_bot_iff] at hba; exact hba
    exact (hb.1 (Set.mem_insert x t)).trans this
  · intro u hu
    exact ha.2 (fun y hy => hu (hts hy))

theorem solution (A : Type u) [BooleanAlgebra A]
    (nu : A → ℝ≥0) (hnu : IsPositiveContinuousValuation nu)
    (hfaithful : ∀ a, nu a = 0 → a = ⊥)
    (hcountable : ∀ s : Set A, s.Countable → ∃ a : A, IsLUB s a) :
    (∀ s : Set A, ∃ a : A, IsLUB s a) ∧
    ∀ (B : Type v) [CompleteBooleanAlgebra B] (f : BoundedLatticeHom A B),
      (∀ (s : Set A) (a : A), s.Countable → IsLUB s a → IsLUB (f '' s) (f a)) →
      ∀ (s : Set A) (a : A), IsLUB s a → IsLUB (f '' s) (f a) := by
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨t, -, -, a, -, ha⟩ := g67c_key A nu hnu hfaithful hcountable s
    exact ⟨a, ha⟩
  · intro B _ f hf s a ha
    obtain ⟨t, hts, htc, a', hta', ha'⟩ := g67c_key A nu hnu hfaithful hcountable s
    have he : a' = a := ha'.unique ha
    subst he
    have hfm : Monotone f := OrderHomClass.mono f
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hfm (ha.1 hx)
    · intro u hu
      exact (hf t a' htc hta').2 (fun y ⟨x, hx, hxy⟩ => hu ⟨x, hts hx, hxy⟩)
