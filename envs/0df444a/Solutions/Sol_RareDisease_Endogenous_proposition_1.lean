-- Prove2me | solution 1 for RareDisease.Endogenous.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T17:17:21.47855+00:00
-- url     : https://prove2.me/submissions/f194647c-6005-4c8c-b3bf-98c5fbb9f46a

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

lemma rare_valsA (k α β : ℝ) (hk : 0 < k) (hp : IsPolicy α β) :
    welfareA β (rareXA k α β).1 (rareXA k α β).2 = rareW k α β ∧
    spendA k α β (rareXA k α β).1 (rareXA k α β).2 = rareS k α β ∧
    profitA k α β (rareXA k α β).1 (rareXA k α β).2 = rareW k α β / (1 - β) := by
  have ha : 0 < 1 - α := sub_pos.mpr hp.1.2
  have hb : 0 < 1 - β := sub_pos.mpr hp.2.2
  dsimp [welfareA, spendA, profitA, rareXA, rareW, rareS]
  constructor
  · field_simp
    <;> ring
  constructor
  · field_simp
    <;> ring
  · field_simp
    <;> ring

lemma rare_valsB (k α β : ℝ) (hk : 0 < k) (hp : IsPolicy α β) :
    welfareB β (rareXB k α β).1 (rareXB k α β).2 = rareW k α β ∧
    spendB k α β (rareXB k α β).1 (rareXB k α β).2 = rareS k α β ∧
    profitB k α β (rareXB k α β).1 (rareXB k α β).2 = rareW k α β / (1 - β) := by
  have ha : 0 < 1 - α := sub_pos.mpr hp.1.2
  have hb : 0 < 1 - β := sub_pos.mpr hp.2.2
  dsimp [welfareB, spendB, profitB, rareXB, rareW, rareS]
  constructor
  · field_simp
    <;> ring
  constructor
  · field_simp
    <;> ring
  · field_simp
    <;> ring

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

lemma rare_spend_id (k α β : ℝ) (hk : 0 < k) (hp : IsPolicy α β) :
    64 * k * ((1 - α) * (1 - β)) ^ 2 * rareS k α β =
      1 - (1 - α) * (1 - β) + β * (1 - α) := by
  have ha : 0 < 1 - α := sub_pos.mpr hp.1.2
  have hb : 0 < 1 - β := sub_pos.mpr hp.2.2
  dsimp [rareS]
  field_simp
  <;> ring

lemma rare_star_policy (k B : ℝ) (hk : 0 < k) (hB : 0 < B) :
    IsPolicy (alphaStar k B) 0 := by
  have h := rare_star k B hk hB
  exact ⟨⟨by linarith [h.2.1], by linarith [h.1]⟩, by constructor <;> norm_num⟩

lemma rare_star_spend (k B : ℝ) (hk : 0 < k) (hB : 0 < B) :
    rareS k (alphaStar k B) 0 = B := by
  have hs := rare_star k B hk hB
  have hqs := hs.1
  have hid := rare_spend_id k (alphaStar k B) 0 hk (rare_star_policy k B hk hB)
  simp only [sub_zero, mul_one, zero_mul, add_zero] at hid
  have hpos : 0 < 64 * k * (1 - alphaStar k B) ^ 2 := by positivity
  nlinarith [hs.2.2.1]

lemma rare_budget_q (k B α β : ℝ) (hk : 0 < k) (hB : 0 < B)
    (hp : IsPolicy α β) (hbudget : rareS k α β ≤ B) :
    1 - alphaStar k B ≤ (1 - α) * (1 - β) := by
  have ha : 0 < 1 - α := sub_pos.mpr hp.1.2
  have hb : 0 < 1 - β := sub_pos.mpr hp.2.2
  have hq : 0 < (1 - α) * (1 - β) := mul_pos ha hb
  have hstar := rare_star k B hk hB
  have hid := rare_spend_id k α β hk hp
  have hb0 := mul_nonneg hp.2.1 ha.le
  have hmul := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 64 * k * ((1 - α) * (1 - β)) ^ 2 by positivity)
  by_contra hn
  have hl : (1 - α) * (1 - β) < 1 - alphaStar k B := lt_of_not_ge hn
  have hsq : ((1 - α) * (1 - β)) ^ 2 < (1 - alphaStar k B) ^ 2 := sq_lt_sq₀ hq.le hstar.1.le |>.2 hl
  have hd := mul_lt_mul_of_pos_left hsq (show 0 < 64 * B * k by positivity)
  nlinarith [hstar.2.2.1]

lemma rare_budget_w (k B α β : ℝ) (hk : 0 < k) (hB : 0 < B)
    (hp : IsPolicy α β) (hbudget : rareS k α β ≤ B) :
    rareW k α β ≤ rareW k (alphaStar k B) 0 := by
  have ha : 0 < 1 - α := sub_pos.mpr hp.1.2
  have hb : 0 < 1 - β := sub_pos.mpr hp.2.2
  have hs := rare_star k B hk hB
  have hqs := hs.1
  have hq := rare_budget_q k B α β hk hB hp hbudget
  dsimp [rareW]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hq hk.le]

lemma rare_budget_unique (k B α β : ℝ) (hk : 0 < k) (hB : 0 < B)
    (hp : IsPolicy α β) (hbudget : rareS k α β ≤ B)
    (hw : rareW k (alphaStar k B) 0 ≤ rareW k α β) :
    α = alphaStar k B ∧ β = 0 := by
  have ha : 0 < 1 - α := sub_pos.mpr hp.1.2
  have hb : 0 < 1 - β := sub_pos.mpr hp.2.2
  have hs := rare_star k B hk hB
  have hqs := hs.1
  have hq := rare_budget_q k B α β hk hB hp hbudget
  dsimp [rareW] at hw
  have hc := (div_le_div_iff₀ (by positivity) (by positivity)).mp hw
  have hqeq : (1 - α) * (1 - β) = 1 - alphaStar k B := by
    have hh : 64 * k * ((1 - α) * (1 - β)) ≤ 64 * k * (1 - alphaStar k B) := by nlinarith [hc]
    exact le_antisymm ((mul_le_mul_iff_right₀ (show 0 < 64 * k by positivity)).mp hh) hq
  have hid := rare_spend_id k α β hk hp
  have hmul := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 64 * k * ((1 - α) * (1 - β)) ^ 2 by positivity)
  rw [hqeq] at hid hmul
  have hz : β * (1 - α) = 0 := by nlinarith [hs.2.2.1, mul_nonneg hp.2.1 ha.le]
  have hbzero := (mul_eq_zero.mp hz).resolve_right ha.ne'
  refine ⟨?_, hbzero⟩
  rw [hbzero] at hqeq
  linarith [hqeq]

def rareOpt (k B α β : ℝ) : Prop :=
  IsPolicy α β ∧ rareS k α β ≤ B ∧
    ∀ α' β', IsPolicy α' β' → rareS k α' β' ≤ B → rareW k α' β' ≤ rareW k α β

lemma rare_optA (k B α β : ℝ) (hk : 0 < k) : IsOptimalA k B α β ↔ rareOpt k B α β := by
  constructor
  · rintro ⟨hp, x, hx, hbudget, hmax⟩
    rw [rare_brA k α β hk hp] at hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    have hv := rare_valsA k α β hk hp
    rw [hv.2.1] at hbudget
    refine ⟨hp, hbudget, ?_⟩
    intro α' β' hp' hb'
    have hv' := rare_valsA k α' β' hk hp'
    have hh := hmax α' β' (rareXA k α' β') (by rw [rare_brA k α' β' hk hp']; exact Set.mem_singleton _) hp' (hv'.2.1 ▸ hb')
    simpa only [hv'.1, hv.1] using hh
  · rintro ⟨hp, hbudget, hmax⟩
    have hv := rare_valsA k α β hk hp
    refine ⟨hp, rareXA k α β, ?_, hv.2.1 ▸ hbudget, ?_⟩
    · rw [rare_brA k α β hk hp]
      exact Set.mem_singleton _
    · intro α' β' y hy hp' hb'
      rw [rare_brA k α' β' hk hp'] at hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      have hv' := rare_valsA k α' β' hk hp'
      rw [hv'.2.1] at hb'
      rw [hv'.1, hv.1]
      exact hmax α' β' hp' hb'

lemma rare_optB (k B α β : ℝ) (hk : 0 < k) : IsOptimalB k B α β ↔ rareOpt k B α β := by
  constructor
  · rintro ⟨hp, x, hx, hbudget, hmax⟩
    rw [rare_brB k α β hk hp] at hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    have hv := rare_valsB k α β hk hp
    rw [hv.2.1] at hbudget
    refine ⟨hp, hbudget, ?_⟩
    intro α' β' hp' hb'
    have hv' := rare_valsB k α' β' hk hp'
    have hh := hmax α' β' (rareXB k α' β') (by rw [rare_brB k α' β' hk hp']; exact Set.mem_singleton _) hp' (hv'.2.1 ▸ hb')
    simpa only [hv'.1, hv.1] using hh
  · rintro ⟨hp, hbudget, hmax⟩
    have hv := rare_valsB k α β hk hp
    refine ⟨hp, rareXB k α β, ?_, hv.2.1 ▸ hbudget, ?_⟩
    · rw [rare_brB k α β hk hp]
      exact Set.mem_singleton _
    · intro α' β' y hy hp' hb'
      rw [rare_brB k α' β' hk hp'] at hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      have hv' := rare_valsB k α' β' hk hp'
      rw [hv'.2.1] at hb'
      rw [hv'.1, hv.1]
      exact hmax α' β' hp' hb'

lemma rare_opt_star (k B : ℝ) (hk : 0 < k) (hB : 0 < B) : rareOpt k B (alphaStar k B) 0 :=
  ⟨rare_star_policy k B hk hB, (rare_star_spend k B hk hB).le, fun α β hp hb => rare_budget_w k B α β hk hB hp hb⟩

lemma rare_opt_unique (k B α β : ℝ) (hk : 0 < k) (hB : 0 < B) :
    rareOpt k B α β ↔ α = alphaStar k B ∧ β = 0 := by
  constructor
  · intro h
    exact rare_budget_unique k B α β hk hB h.1 h.2.1
      (h.2.2 _ _ (rare_star_policy k B hk hB) (rare_star_spend k B hk hB).le)
  · rintro ⟨rfl, rfl⟩
    exact rare_opt_star k B hk hB

lemma rare_propA (k B : ℝ) (hk : 0 < k) (hB : 0 < B) :
    IsOptimalA k B (alphaStar k B) 0 ∧
    (∀ α β : ℝ, IsOptimalA k B α β ↔ α = alphaStar k B ∧ β = 0) ∧
    (∀ x ∈ BRA k (alphaStar k B) 0,
      spendA k (alphaStar k B) 0 x.1 x.2 = B ∧
      welfareA 0 x.1 x.2 = 2 * B / (Real.sqrt (256 * B * k + 1) - 1) ∧
      profitA k (alphaStar k B) 0 x.1 x.2 =
        2 * B / (Real.sqrt (256 * B * k + 1) - 1)) := by
  refine ⟨(rare_optA _ _ _ _ hk).mpr (rare_opt_star k B hk hB), ?_, ?_⟩
  · intro α β
    exact (rare_optA _ _ _ _ hk).trans (rare_opt_unique _ _ _ _ hk hB)
  · intro x hx
    have hp := rare_star_policy k B hk hB
    rw [rare_brA _ _ _ hk hp] at hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    have hv := rare_valsA _ _ _ hk hp
    have hw := (rare_star k B hk hB).2.2.2
    exact ⟨hv.2.1.trans (rare_star_spend k B hk hB), hv.1.trans hw, by simpa only [sub_zero, div_one, hw] using hv.2.2⟩

theorem solution (k B : ℝ) (hk : 0 < k) (hB : 0 < B) :
    IsOptimalA k B (alphaStar k B) 0 ∧
    (∀ α β : ℝ, IsOptimalA k B α β ↔ α = alphaStar k B ∧ β = 0) ∧
    (∀ x ∈ BRA k (alphaStar k B) 0,
      spendA k (alphaStar k B) 0 x.1 x.2 = B ∧
      welfareA 0 x.1 x.2 = 2 * B / (Real.sqrt (256 * B * k + 1) - 1) ∧
      profitA k (alphaStar k B) 0 x.1 x.2 =
        2 * B / (Real.sqrt (256 * B * k + 1) - 1)) := by
  exact rare_propA k B hk hB
