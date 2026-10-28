-- Prove2me | solution 2 for RareDisease.Endogenous.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:41.345779+00:00
-- url     : https://prove2.me/submissions/e368aa64-f5ba-446b-ab62-9399112209d2

import Mathlib
import Definitions.Def_RareDisease_Endogenous_Setting
import Theorems.Thm_RareDisease_Endogenous_proposition_1
import Theorems.Thm_RareDisease_Endogenous_proposition_1_outcome

-- carved verbatim out of submission 67fa73b7-319f-471a-8148-1dfb46361956, lines 396-416

section
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

lemma rare_brB (k α β : ℝ) (hk : 0 < k) (hp : IsPolicy α β) :
    BRB k α β = {rareXB k α β} := by
  have ha : 0 < 1 - α := sub_pos.mpr hp.1.2
  have hb : 0 < 1 - β := sub_pos.mpr hp.2.2
  have hap : 0 < (rareXB k α β).1 := by dsimp [rareXB]; positivity
  have hae : 0 < (rareXB k α β).2 := by dsimp [rareXB]; positivity
  have hval : profitB k α β (rareXB k α β).1 (rareXB k α β).2 =
      1 / (64 * ((1 - α) * k) * (1 - β) ^ 2) := by
    dsimp [profitB, rareXB]
    field_simp
    <;> ring
  ext x
  constructor
  · intro hx
    have ht := hx.2.2 _ _ hap.le hae
    rw [hval] at ht
    have hq := (rare_quadB ((1 - α) * k) (1 - β) x.1 x.2 (mul_pos ha hk) hb hx.2.1).2 ht
    apply Set.mem_singleton_iff.mpr
    apply Prod.ext
    · simpa [rareXB, mul_assoc] using hq.1
    · simpa [rareXB, mul_assoc] using hq.2
  · rintro rfl
    refine ⟨hap.le, hae, ?_⟩
    intro p e _ he
    rw [hval]
    exact (rare_quadB ((1 - α) * k) (1 - β) p e (mul_pos ha hk) hb he).1

lemma rare_star (k B : ℝ) (hk : 0 < k) (hB : 0 < B) :
    0 < 1 - alphaStar k B ∧ 1 - alphaStar k B < 1 ∧
    64 * B * k * (1 - alphaStar k B) ^ 2 + (1 - alphaStar k B) = 1 ∧
    rareW k (alphaStar k B) 0 = 2 * B / (Real.sqrt (256 * B * k + 1) - 1) := by
  let s := Real.sqrt (256 * B * k + 1)
  have hsq : s ^ 2 = 256 * B * k + 1 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs : 1 < s := by nlinarith [mul_pos hB hk]
  have hs1 : 0 < s + 1 := by linarith
  have hm : 0 < s - 1 := by linarith
  have hrel : 128 * B * k * (1 - alphaStar k B) = s - 1 := by
    dsimp [alphaStar, s]
    field_simp
    <;> ring
  have hq : 1 - alphaStar k B = 2 / (s + 1) := by
    apply (eq_div_iff hs1.ne').mpr
    have hp : 0 < 128 * B * k := by positivity
    nlinarith [hrel]
  have hpos : 0 < 1 - alphaStar k B := hq ▸ div_pos (by norm_num) hs1
  refine ⟨hpos, ?_, ?_, ?_⟩
  · rw [hq]
    exact (div_lt_iff₀ hs1).mpr (by linarith)
  · rw [hq]
    field_simp
    nlinarith [hsq]
  · dsimp [rareW]
    simp only [sub_zero, mul_one]
    apply (div_eq_div_iff (by positivity : 64 * (1 - alphaStar k B) * k ≠ 0) hm.ne').mpr
    nlinarith [hrel]

lemma rare_star_policy (k B : ℝ) (hk : 0 < k) (hB : 0 < B) :
    IsPolicy (alphaStar k B) 0 := by
  have h := rare_star k B hk hB
  exact ⟨⟨by linarith [h.2.1], by linarith [h.1]⟩, by constructor <;> norm_num⟩

lemma rare_price (k B : ℝ) (hk : 0 < k) (hB : 0 < B) :
    (B < k - 1 / 8 → (rareXA k (alphaStar k B) 0).1 < (rareXB k (alphaStar k B) 0).1) ∧
    (k - 1 / 8 < B → (rareXB k (alphaStar k B) 0).1 < (rareXA k (alphaStar k B) 0).1) ∧
    (B = k - 1 / 8 → (rareXA k (alphaStar k B) 0).1 = (rareXB k (alphaStar k B) 0).1) := by
  have hs := rare_star k B hk hB
  have hqs := hs.1
  let t := 8 * (1 - alphaStar k B) * k
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht : 8 * B * t ^ 2 + t = 8 * k := by
    have hh := congrArg (fun z : ℝ => 8 * k * z) hs.2.2.1
    dsimp [t]
    nlinarith [hh]
  have hpa : (rareXA k (alphaStar k B) 0).1 = 1 / (2 * t) := by
    dsimp [rareXA, t]
    norm_num
    ring
  have hpb : (rareXB k (alphaStar k B) 0).1 = 1 / 2 := by simp [rareXB]
  rw [hpa, hpb]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have ht1 : 1 < t := by
      by_contra hn
      have ht2 : t ≤ 1 := le_of_not_gt hn
      have hsq : t ^ 2 ≤ 1 := by simpa using (sq_le_sq₀ htpos.le (by norm_num : (0 : ℝ) ≤ 1)).mpr ht2
      have hh := mul_le_mul_of_nonneg_left hsq hB.le
      nlinarith
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  · intro h
    have ht1 : t < 1 := by
      by_contra hn
      have ht2 : 1 ≤ t := le_of_not_gt hn
      have hsq : 1 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
      have hh := mul_le_mul_of_nonneg_left hsq hB.le
      nlinarith
    apply (div_lt_div_iff₀ (by norm_num) (by positivity)).mpr
    linarith
  · intro h
    have hz : (t - 1) * (8 * B * (t + 1) + 1) = 0 := by nlinarith
    have hp : 0 < 8 * B * (t + 1) + 1 := by positivity
    have ht1 : t = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hp.ne')
    rw [ht1]
    norm_num

theorem solution (k B : ℝ) (hk : 0 < k) (hB : 0 < B) :
    IsOptimalA k B (alphaStar k B) 0 ∧
    IsOptimalB k B (alphaStar k B) 0 ∧
    ∀ α β α' β' : ℝ, IsOptimalA k B α β → IsOptimalB k B α' β' →
      ∀ x ∈ BRA k α β, ∀ y ∈ BRB k α' β',
        (B < k - 1 / 8 → x.1 < y.1) ∧
        (k - 1 / 8 < B → y.1 < x.1) ∧
        (B = k - 1 / 8 → x.1 = y.1) := by
  have hA := RareDisease.Endogenous.proposition_1 k B hk hB
  have hB' := RareDisease.Endogenous.proposition_1_outcome k B hk hB
  refine ⟨hA.1, hB'.1, ?_⟩
  intro α β α' β' hoA hoB x hx y hy
  obtain ⟨rfl, rfl⟩ := (hA.2.1 α β).mp hoA
  obtain ⟨rfl, rfl⟩ := (hB'.2.1 α' β').mp hoB
  have hp := rare_star_policy k B hk hB
  rw [rare_brA _ _ _ hk hp] at hx
  rw [rare_brB _ _ _ hk hp] at hy
  rcases Set.mem_singleton_iff.mp hx with rfl
  rcases Set.mem_singleton_iff.mp hy with rfl
  exact rare_price k B hk hB

end
