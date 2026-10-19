-- Prove2me | solution 1 for RareDisease.Endogenous.best_response_A
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T17:17:17.274411+00:00
-- url     : https://prove2.me/submissions/61fb56eb-8f1c-4f36-beb5-73d966c7f3ed

import Mathlib
import Definitions.Def_RareDisease_Endogenous_Setting

open RareDisease.Endogenous

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false

lemma rare_quadA (a b p e : ℝ) (ha : 0 < a) (hb : 0 < b) (he : 0 < e) :
    p * (1 - b * p / e) - a * e ^ 2 ≤ 1 / (64 * a * b ^ 2) ∧
    (1 / (64 * a * b ^ 2) ≤ p * (1 - b * p / e) - a * e ^ 2 →
      p = 1 / (16 * a * b ^ 2) ∧ e = 1 / (8 * a * b)) := by
  have hid : 1 / (64 * a * b ^ 2) - (p * (1 - b * p / e) - a * e ^ 2) =
      a * (e - 1 / (8 * a * b)) ^ 2 + b / e * (p - e / (2 * b)) ^ 2 := by
    field_simp
    <;> ring
  have h1 := mul_nonneg ha.le (sq_nonneg (e - 1 / (8 * a * b)))
  have h2 := mul_nonneg (div_pos hb he).le (sq_nonneg (p - e / (2 * b)))
  constructor
  · linarith
  · intro h
    have hz1 : a * (e - 1 / (8 * a * b)) ^ 2 = 0 := by linarith
    have hz2 : b / e * (p - e / (2 * b)) ^ 2 = 0 := by linarith
    have heq : e = 1 / (8 * a * b) := sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz1).resolve_left ha.ne'))
    have hpq : p = e / (2 * b) := sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz2).resolve_left (div_pos hb he).ne'))
    refine ⟨?_, heq⟩
    rw [hpq, heq]
    field_simp
    <;> ring

lemma rare_quadB (a b p e : ℝ) (ha : 0 < a) (hb : 0 < b) (he : 0 < e) :
    e * p * (1 - b * p) - a * e ^ 2 ≤ 1 / (64 * a * b ^ 2) ∧
    (1 / (64 * a * b ^ 2) ≤ e * p * (1 - b * p) - a * e ^ 2 →
      p = 1 / (2 * b) ∧ e = 1 / (8 * a * b)) := by
  have hid : 1 / (64 * a * b ^ 2) - (e * p * (1 - b * p) - a * e ^ 2) =
      a * (e - 1 / (8 * a * b)) ^ 2 + e * b * (p - 1 / (2 * b)) ^ 2 := by
    field_simp
    <;> ring
  have h1 := mul_nonneg ha.le (sq_nonneg (e - 1 / (8 * a * b)))
  have h2 := mul_nonneg (mul_pos he hb).le (sq_nonneg (p - 1 / (2 * b)))
  constructor
  · linarith
  · intro h
    have hz1 : a * (e - 1 / (8 * a * b)) ^ 2 = 0 := by linarith
    have hz2 : e * b * (p - 1 / (2 * b)) ^ 2 = 0 := by linarith
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz2).resolve_left (mul_pos he hb).ne')),
      sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz1).resolve_left ha.ne'))⟩

noncomputable def rareXA (k α β : ℝ) : ℝ × ℝ :=
  (1 / (16 * (1 - α) * k * (1 - β) ^ 2), 1 / (8 * (1 - α) * k * (1 - β)))
noncomputable def rareXB (k α β : ℝ) : ℝ × ℝ :=
  (1 / (2 * (1 - β)), 1 / (8 * (1 - α) * k * (1 - β)))
noncomputable def rareW (k α β : ℝ) : ℝ := 1 / (64 * (1 - α) * k * (1 - β))
noncomputable def rareS (k α β : ℝ) : ℝ :=
  α / (64 * (1 - α) ^ 2 * k * (1 - β) ^ 2) + β / (32 * (1 - α) * k * (1 - β) ^ 2)

lemma rare_brA (k α β : ℝ) (hk : 0 < k) (hp : IsPolicy α β) :
    BRA k α β = {rareXA k α β} := by
  have ha : 0 < 1 - α := sub_pos.mpr hp.1.2
  have hb : 0 < 1 - β := sub_pos.mpr hp.2.2
  have hap : 0 < (rareXA k α β).1 := by dsimp [rareXA]; positivity
  have hae : 0 < (rareXA k α β).2 := by dsimp [rareXA]; positivity
  have hval : profitA k α β (rareXA k α β).1 (rareXA k α β).2 =
      1 / (64 * ((1 - α) * k) * (1 - β) ^ 2) := by
    dsimp [profitA, rareXA]
    field_simp
    <;> ring
  ext x
  constructor
  · intro hx
    have ht := hx.2.2 _ _ hap.le hae
    rw [hval] at ht
    have hq := (rare_quadA ((1 - α) * k) (1 - β) x.1 x.2 (mul_pos ha hk) hb hx.2.1).2 ht
    apply Set.mem_singleton_iff.mpr
    apply Prod.ext
    · simpa [rareXA, mul_assoc] using hq.1
    · simpa [rareXA, mul_assoc] using hq.2
  · rintro rfl
    refine ⟨hap.le, hae, ?_⟩
    intro p e _ he
    rw [hval]
    exact (rare_quadA ((1 - α) * k) (1 - β) p e (mul_pos ha hk) hb he).1

theorem solution (k α β : ℝ) (hk : 0 < k) (hpolicy : IsPolicy α β) :
    BRA k α β = {
      (1 / (16 * (1 - α) * k * (1 - β) ^ 2),
       1 / (8 * (1 - α) * k * (1 - β)))} := by
  simpa only [rareXA] using rare_brA k α β hk hpolicy
