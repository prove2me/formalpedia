-- Prove2me | solution 1 for OnlineRandomization.Potential.potential_nonneg_on_play
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:18:36.707256+00:00
-- url     : https://prove2.me/submissions/799aab13-8960-442f-a28f-81baa4a20132

import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

open Classical

namespace OnlineRandomization.Potential

theorem orq_pexp_eq_sum {X : Type*} (q : PMF X) (f : X → ℝ) (T : Finset X)
    (hT : ∀ z, q z ≠ 0 → z ∈ T) : pexp q f = ∑ z ∈ T, (q z).toReal * f z := by
  unfold pexp
  apply tsum_eq_sum
  intro z hz
  have : q z = 0 := by
    by_contra h; exact hz (hT z h)
  simp [this]

theorem orq_pexp_pure {X : Type*} (x : X) (f : X → ℝ) : pexp (PMF.pure x) f = f x := by
  rw [orq_pexp_eq_sum _ f {x} (fun z hz => by
    rw [PMF.pure_apply] at hz
    split_ifs at hz with h
    · simp [h]
    · exact absurd rfl hz)]
  simp

theorem orq_pexp_bind {A X : Type*} [Fintype A] (p : PMF A) (f : A → PMF X) (h : X → ℝ)
    (T : Finset X) (hT : ∀ z, (p.bind f) z ≠ 0 → z ∈ T) :
    pexp (p.bind f) h = ∑ a : A, (p a).toReal * pexp (f a) h := by
  rw [orq_pexp_eq_sum _ h T hT]
  have hfa : ∀ a, p a ≠ 0 → pexp (f a) h = ∑ z ∈ T, (f a z).toReal * h z := by
    intro a ha
    apply orq_pexp_eq_sum
    intro z hz
    apply hT
    rw [← PMF.mem_support_iff, PMF.mem_support_bind_iff]
    exact ⟨a, (PMF.mem_support_iff _ _).2 ha, (PMF.mem_support_iff _ _).2 hz⟩
  have : ∀ a : A, (p a).toReal * pexp (f a) h = ∑ z ∈ T, (p a).toReal * ((f a z).toReal * h z) := by
    intro a
    by_cases ha : p a = 0
    · simp [ha]
    · rw [hfa a ha, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [PMF.bind_apply, tsum_fintype (L := SummationFilter.unconditional A),
    ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _)), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_mul]; ring

theorem orq_fin {R A : Type*} [Fintype A] (g : BehAlg R A) (S : OnlineAdv R A) (k : ℕ) :
    ∀ r a b, ∃ T : Finset (List R × List A × List A),
      ∀ z, behPlayAux g S k r a b z ≠ 0 → z ∈ T := by
  induction k with
  | zero =>
    intro r a b
    refine ⟨{(r, a, b)}, fun z hz => ?_⟩
    simp only [behPlayAux, PMF.pure_apply] at hz
    split_ifs at hz with h
    · simp [h]
    · exact absurd rfl hz
  | succ k ih =>
    intro r a b
    rcases hn : S.next a with _ | x
    · refine ⟨{(r, a, b)}, fun z hz => ?_⟩
      simp only [behPlayAux, hn, PMF.pure_apply] at hz
      split_ifs at hz with h
      · simp [h]
      · exact absurd rfl hz
    · choose T hT using fun a' : A => ih (r ++ [x]) (a ++ [a']) (b ++ [S.ans a])
      refine ⟨Finset.univ.biUnion T, fun z hz => ?_⟩
      simp only [behPlayAux, hn] at hz
      rw [← PMF.mem_support_iff, PMF.mem_support_bind_iff] at hz
      obtain ⟨a', -, h2⟩ := hz
      exact Finset.mem_biUnion.2 ⟨a', Finset.mem_univ _, hT a' z ((PMF.mem_support_iff _ _).1 h2)⟩

theorem orq_len {R A : Type*} [Fintype A] (g : BehAlg R A) (S : OnlineAdv R A) (k : ℕ) :
    ∀ r a b, a.length = r.length → b.length = r.length →
      ∀ z, behPlayAux g S k r a b z ≠ 0 → z.2.1.length = z.1.length ∧ z.2.2.length = z.1.length := by
  induction k with
  | zero =>
    intro r a b ha hb z hz
    simp only [behPlayAux, PMF.pure_apply] at hz
    split_ifs at hz with h
    · subst h; exact ⟨ha, hb⟩
    · exact absurd rfl hz
  | succ k ih =>
    intro r a b ha hb z hz
    rcases hn : S.next a with _ | x
    · simp only [behPlayAux, hn, PMF.pure_apply] at hz
      split_ifs at hz with h
      · subst h; exact ⟨ha, hb⟩
      · exact absurd rfl hz
    · simp only [behPlayAux, hn] at hz
      rw [← PMF.mem_support_iff, PMF.mem_support_bind_iff] at hz
      obtain ⟨a', -, h2⟩ := hz
      exact ih _ _ _ (by simp [ha]) (by simp [hb]) z ((PMF.mem_support_iff _ _).1 h2)

theorem orq_pot {R A : Type*} [Fintype A] (F : Game R A) (α : ℝ → ℝ)
    (g : BehAlg R A) (Φ : List R → List A → List A → ℝ) (hΦ : IsAugPotential F α g Φ)
    (S : OnlineAdv R A) (k : ℕ) :
    ∀ r a b, a.length = r.length → b.length = r.length →
      Φ r a b ≤ pexp (behPlayAux g S k r a b) (fun z => Φ z.1 z.2.1 z.2.2) := by
  induction k with
  | zero =>
    intro r a b _ _
    simp [behPlayAux, orq_pexp_pure]
  | succ k ih =>
    intro r a b ha hb
    rcases hn : S.next a with _ | x
    · simp [behPlayAux, hn, orq_pexp_pure]
    · simp only [behPlayAux, hn]
      obtain ⟨T, hT⟩ := orq_fin g S (k + 1) r a b
      simp only [behPlayAux, hn] at hT
      rw [orq_pexp_bind _ _ _ T hT]
      refine (hΦ.le_step r a b ha hb x (S.ans a)).trans ?_
      apply Finset.sum_le_sum
      intro a' _
      exact mul_le_mul_of_nonneg_left (ih _ _ _ (by simp [ha]) (by simp [hb]))
        ENNReal.toReal_nonneg

theorem orq_nonneg {R A : Type*} [Fintype A] (F : Game R A) (α : ℝ → ℝ)
    (g : BehAlg R A) (Φ : List R → List A → List A → ℝ) (hΦ : IsAugPotential F α g Φ)
    (S : OnlineAdv R A) :
    0 ≤ pexp (behPlay g S) (fun z => Φ z.1 z.2.1 z.2.2) := by
  have := orq_pot F α g Φ hΦ S S.depth [] [] [] rfl rfl
  rw [hΦ.zero] at this
  exact this

theorem orq_lemma {R A : Type*} [Fintype A] (F : Game R A) (α : ℝ → ℝ)
    (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) :
    IsCompetitiveOnlineBeh F α g := by
  intro S
  have h0 := orq_nonneg F α g Φ hΦ S
  obtain ⟨T, hT⟩ := orq_fin g S S.depth [] [] []
  have hL := orq_len g S S.depth [] [] [] rfl rfl
  unfold behPlay at h0 ⊢
  rw [orq_pexp_eq_sum _ _ T hT] at h0 ⊢
  rw [orq_pexp_eq_sum _ _ T hT]
  have : ∑ z ∈ T, (behPlayAux g S S.depth [] [] [] z).toReal * F.cost z.1 z.2.1 ≤
      ∑ z ∈ T, ((behPlayAux g S S.depth [] [] [] z).toReal * α (F.cost z.1 z.2.2) -
        (behPlayAux g S S.depth [] [] [] z).toReal * Φ z.1 z.2.1 z.2.2) := by
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : behPlayAux g S S.depth [] [] [] z = 0
    · simp [hz]
    · obtain ⟨h1, h2⟩ := hL z hz
      have := hΦ.le_residue z.1 z.2.1 z.2.2 h1 h2
      have hp : 0 ≤ (behPlayAux g S S.depth [] [] [] z).toReal := ENNReal.toReal_nonneg
      nlinarith
  rw [Finset.sum_sub_distrib] at this
  linarith

end OnlineRandomization.Potential

open OnlineRandomization.Potential


theorem solution {R A : Type*} [Fintype A] (F : Game R A) (α : ℝ → ℝ)
    (g : BehAlg R A) (Φ : List R → List A → List A → ℝ) (hΦ : IsAugPotential F α g Φ)
    (S : OnlineAdv R A) :
    0 ≤ pexp (behPlay g S) (fun z => Φ z.1 z.2.1 z.2.2) := by
  exact orq_nonneg F α g Φ hΦ S
