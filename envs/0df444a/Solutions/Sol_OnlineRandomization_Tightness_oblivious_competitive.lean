-- Prove2me | solution 1 for OnlineRandomization.Tightness.oblivious_competitive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:42:33.221314+00:00
-- url     : https://prove2.me/submissions/307b7ee2-a594-4e03-a3a0-7429f4d9fd49

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame



namespace OnlineRandomization.Tightness

open MeasureTheory

lemma mate_ne {t : ℕ} (x : Fin t × Bool) : x ≠ mate x := by
  intro h
  have := congrArg Prod.snd h
  simp [mate] at this

lemma mate_mate {t : ℕ} (x : Fin t × Bool) : mate (mate x) = x := by
  simp [mate]

lemma integral_unif (t : ℕ) [NeZero t] (f : Fin t × Bool → ℝ) :
    ∫ ω, f ω ∂(unifAlg t).μ = (∑ ω, f ω) / (2 * (t : ℝ)) := by
  simp only [unifAlg]
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, smul_eq_mul]
  rw [← Finset.mul_sum]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  push_cast
  field_simp

lemma card_A (t : ℕ) : (Finset.univ : Finset (Fin t × Bool)).card = 2 * t := by
  simp [Finset.card_univ, Fintype.card_prod]; ring

lemma sum_pairCost (t : ℕ) (m M : ℝ) (y : Fin t × Bool) :
    ∑ ω, pairCost m M ω y = 1 + M + (2 * (t : ℝ) - 2) * m := by
  have h : ∀ ω : Fin t × Bool, pairCost m M ω y =
      m + ((if ω = y then 1 - m else 0) + (if ω = mate y then M - m else 0)) := by
    intro ω
    unfold pairCost
    by_cases h1 : ω = y
    · subst h1; simp [mate_ne ω]
    · by_cases h2 : ω = mate y
      · subst h2; simp [(mate_ne y).symm]
      · simp [h1, h2]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, card_A, nsmul_eq_mul]
  push_cast; ring

lemma opt_nonneg {t : ℕ} [NeZero t] (m M : ℝ) (hm : 1 ≤ m) (hM1 : 1 ≤ M) (r : List (Fin t × Bool)) :
    0 ≤ (matesGame t m M).opt r ∧ (r ≠ [] → 1 ≤ (matesGame t m M).opt r) := by
  have key : ∀ a : List (Fin t × Bool), a.length = r.length →
      0 ≤ matesCost m M r a ∧ (r ≠ [] → 1 ≤ matesCost m M r a) := by
    intro a hl
    match r, a, hl with
    | [], _, _ => simp [matesCost]
    | [_], _, _ => simp [matesCost]
    | _ :: _ :: _, a1 :: _, _ =>
      simp only [matesCost, pairCost]
      constructor
      · split_ifs <;> linarith
      · intro; split_ifs <;> linarith
    | _ :: _ :: _, [], hl => simp at hl
  constructor
  · apply Finset.le_inf'
    intro f _
    exact (key _ (by simp)).1
  · intro hr
    apply Finset.le_inf'
    intro f _
    exact (key _ (by simp)).2 hr

lemma costOn_const {t : ℕ} (m M : ℝ) (ω : Fin t × Bool) (x y : Fin t × Bool)
    (rest : List (Fin t × Bool)) :
    DetAlg.costOn (matesGame t m M) (fun _ => ω) (x :: y :: rest) = pairCost m M ω y := by
  simp only [DetAlg.costOn, DetAlg.answers, matesGame, List.length_cons]
  rw [List.range_succ_eq_map]
  simp [matesCost]

theorem obl_gen (t : ℕ) [NeZero t] (m M β : ℝ) (hm : 1 ≤ m) (hM : 1 ≤ M)
    (hβ : (2 * (t : ℝ) - 2) * m + M + 1 ≤ 2 * (t : ℝ) * β) :
    IsCompetitiveObl (matesGame t m M) (fun x => β * x) (unifAlg t) := by
  have ht : (1 : ℝ) ≤ t := by
    have := NeZero.pos t
    exact_mod_cast this
  have hβ1 : 1 ≤ β := by
    by_contra h
    push_neg at h
    nlinarith
  intro r
  obtain ⟨h0, h1⟩ := opt_nonneg m M hm hM r
  rw [integral_unif]
  match r, h0, h1 with
  | [], h0, _ =>
    simp [DetAlg.costOn, DetAlg.answers, matesGame, matesCost]
    positivity
  | [x], _, h1 =>
    have := h1 (by simp)
    have hc : ∀ ω : Fin t × Bool, DetAlg.costOn (matesGame t m M) ((unifAlg t).alg ω) [x] = 1 := by
      intro ω; simp [DetAlg.costOn, DetAlg.answers, matesGame, matesCost]
    simp only [hc, Finset.sum_const, card_A, nsmul_eq_mul]
    generalize (matesGame t m M).opt [x] = o at this ⊢
    have h2 : β ≤ β * o := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ 2 * t)]
  | x :: y :: rest, _, h1 =>
    have := h1 (by simp)
    simp only [unifAlg, costOn_const, sum_pairCost]
    generalize (matesGame t m M).opt (x :: y :: rest) = o at this ⊢
    have h2 : β ≤ β * o := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ 2 * t)]

theorem oblivious_core (t : ℕ) [NeZero t] (m M β : ℝ) (hm : 1 ≤ m) (hM : 1 ≤ M)
    (hβ : β = ((2 * (t : ℝ) - 2) * m + M + 1) / (2 * (t : ℝ))) :
    IsCompetitiveObl (matesGame t m M) (fun x => β * x) (unifAlg t) := by
  have ht : (0 : ℝ) < t := by
    have := NeZero.pos t
    exact_mod_cast this
  apply obl_gen t m M β hm hM
  rw [hβ]; field_simp; rfl

end OnlineRandomization.Tightness

open OnlineRandomization.Tightness


theorem solution (t : ℕ) [NeZero t] (m M β : ℝ) (hm : 1 ≤ m) (hM : 1 ≤ M)
    (hβ : β = ((2 * (t : ℝ) - 2) * m + M + 1) / (2 * (t : ℝ))) :
    IsCompetitiveObl (matesGame t m M) (fun x => β * x) (unifAlg t) := by
  exact oblivious_core t m M β hm hM hβ
