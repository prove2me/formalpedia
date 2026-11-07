-- Prove2me | solution 1 for OffPlatformThreats.Leakage.proposition_3_leakage_interval
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T15:31:51.967406+00:00
-- url     : https://prove2.me/submissions/64ecfc81-4743-4cff-afc7-7cc7bb2441c5

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_IsSelectedEq
import Definitions.Def_OffPlatformThreats_Leakage_omegaStar
import Definitions.Def_OffPlatformThreats_Leakage_aLeak
import Definitions.Def_OffPlatformThreats_Leakage_bLeak

set_option autoImplicit false

namespace OPTLeakHelp
open OffPlatformThreats.Leakage

lemma dite_unique_eq {P : ℝ → Prop} {inst : Decidable (∃! x, P x)} (L : ℝ) (hL : P L)
    (hu : ∀ y, P y → y = L) : (@dite ℝ (∃! x, P x) inst (fun h => h.exists.choose) (fun _ => 0)) = L := by
  rw [dif_pos ⟨L, hL, hu⟩]
  exact hu _ (Exists.choose_spec _)

lemma sq_le_sq_iff' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x ^ 2 ≤ y ^ 2 ↔ x ≤ y := by
  constructor
  · intro h; by_contra h'; push_neg at h'; nlinarith
  · intro h; nlinarith

lemma demand_core (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi) (hmu : 0 < m.mu)
    (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 < d) (lam : ℝ) :
    (0 ≤ lam ∧ lam < m.mu ∧ d - m.c * waitTime m n lam = 0) ↔
      lam = m.mu * (n * d) / (m.c * m.phi + n * d) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hA : 0 < m.c * m.phi := mul_pos hc hphi
  have hX : 0 < (n:ℝ) * d := mul_pos hn' hd
  have hY : 0 < m.c * m.phi + n * d := by linarith
  unfold waitTime
  constructor
  · rintro ⟨h0, h1, h2⟩
    have hml : 0 < m.mu - lam := by linarith
    have hne : (n:ℝ) * (m.mu - lam) ≠ 0 := (mul_pos hn' hml).ne'
    rw [eq_div_iff hY.ne']
    have h3 : m.c * (lam / (n * (m.mu - lam)) * m.phi) * (n * (m.mu - lam))
        = m.c * m.phi * lam := by field_simp
    have h4 : m.c * (lam / (n * (m.mu - lam)) * m.phi) = d := by linarith
    rw [h4] at h3
    nlinarith [h3]
  · intro h
    have hL0 : 0 ≤ lam := by rw [h]; exact div_nonneg (mul_nonneg hmu.le hX.le) hY.le
    have hL1 : lam < m.mu := by
      rw [h, div_lt_iff₀ hY]; nlinarith
    refine ⟨hL0, hL1, ?_⟩
    have hml : m.mu - lam = m.mu * (m.c * m.phi) / (m.c * m.phi + n * d) := by
      rw [h]; field_simp; try ring
    rw [hml, h]
    field_simp
    ring

lemma onDemand_eq (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi) (hmu : 0 < m.mu)
    (n : ℕ) (q : ℝ) :
    onDemand m n q = if 1 ≤ n ∧ q < m.v then
      m.mu * (n * (m.v - q)) / (m.c * m.phi + n * (m.v - q)) else 0 := by
  unfold onDemand
  by_cases h : 1 ≤ n ∧ q < m.v
  · rw [if_pos h]
    have hd : 0 < m.v - q := by linarith [h.2]
    apply dite_unique_eq
    · unfold OnDemandEq; rw [if_pos h]
      exact (demand_core m hc hphi hmu n h.1 _ hd _).2 rfl
    · intro y hy
      unfold OnDemandEq at hy; rw [if_pos h] at hy
      exact (demand_core m hc hphi hmu n h.1 _ hd _).1 hy
  · rw [if_neg h]
    apply dite_unique_eq
    · unfold OnDemandEq; rw [if_neg h]
    · intro y hy
      unfold OnDemandEq at hy; rw [if_neg h] at hy
      exact hy

lemma offDemand_eq (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi) (hmu : 0 < m.mu)
    (q : ℝ) :
    offDemand m q = if q + m.Ro < m.v then
      m.mu * (1 * ((m.v - m.Ro) - q)) / (m.c * m.phi + 1 * ((m.v - m.Ro) - q)) else 0 := by
  unfold offDemand
  by_cases h : q + m.Ro < m.v
  · rw [if_pos h]
    have hd : 0 < m.v - q - m.Ro := by linarith
    have key := demand_core m hc hphi hmu 1 le_rfl (m.v - q - m.Ro) hd
    have hL : m.mu * (1 * ((m.v - m.Ro) - q)) / (m.c * m.phi + 1 * ((m.v - m.Ro) - q))
        = m.mu * (((1:ℕ):ℝ) * (m.v - q - m.Ro)) / (m.c * m.phi + ((1:ℕ):ℝ) * (m.v - q - m.Ro)) := by
      push_cast; ring_nf
    apply dite_unique_eq
    · unfold OffDemandEq; rw [if_pos h]
      obtain ⟨a1, a2, a3⟩ := (key _).2 hL
      exact ⟨a1, a2, by linarith⟩
    · intro y hy
      unfold OffDemandEq at hy; rw [if_pos h] at hy
      obtain ⟨a1, a2, a3⟩ := hy
      rw [hL]
      exact (key y).1 ⟨a1, a2, by linarith⟩
  · rw [if_neg h]
    apply dite_unique_eq
    · unfold OffDemandEq; rw [if_neg h]
    · intro y hy
      unfold OffDemandEq at hy; rw [if_neg h] at hy
      exact hy

lemma sSup_eq_of {f : ℝ → ℝ} {M : ℝ} (hle : ∀ x, 0 ≤ x → f x ≤ M) (x0 : ℝ) (hx0 : 0 ≤ x0)
    (hfx : f x0 = M) : sSup (f '' Set.Ici 0) = M :=
  IsGreatest.csSup_eq ⟨⟨x0, hx0, hfx⟩, by rintro _ ⟨x, hx, rfl⟩; exact hle x hx⟩

lemma rev_le (A μ n u q s : ℝ) (hA : 0 < A) (hμ : 0 ≤ μ) (hn : 0 < n) (hq : q < u)
    (hs : n * u = A * (s ^ 2 - 1)) :
    q * (μ * (n * (u - q)) / (A + n * (u - q))) ≤ μ * A / n * (s - 1) ^ 2 := by
  have hX : 0 < n * (u - q) := mul_pos hn (by linarith)
  have hY : 0 < A + n * (u - q) := by linarith
  have iden : A * (s - 1) ^ 2 * (A + n * (u - q)) - q * (n * (u - q)) * n
      = (A * (s - 1) - n * (u - q)) ^ 2 := by
    linear_combination (-(n * (u - q))) * hs
  have e1 : q * (μ * (n * (u - q)) / (A + n * (u - q)))
      = μ * (q * (n * (u - q)) * n) / (n * (A + n * (u - q))) := by
    field_simp
  have e2 : μ * A / n * (s - 1) ^ 2
      = μ * (A * (s - 1) ^ 2 * (A + n * (u - q))) / (n * (A + n * (u - q))) := by
    field_simp
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ hμ
  nlinarith [iden, sq_nonneg (A * (s - 1) - n * (u - q))]

lemma rev_attain (A μ n u s : ℝ) (hA : 0 < A) (hn : 0 < n) (hs1 : 1 < s)
    (hs : n * u = A * (s ^ 2 - 1)) :
    0 ≤ u - A * (s - 1) / n ∧ u - A * (s - 1) / n < u ∧
    (u - A * (s - 1) / n) * (μ * (n * (u - (u - A * (s - 1) / n)))
        / (A + n * (u - (u - A * (s - 1) / n)))) = μ * A / n * (s - 1) ^ 2 := by
  have h1 : n * (u - (u - A * (s - 1) / n)) = A * (s - 1) := by field_simp; try ring
  have hu : u = A * (s ^ 2 - 1) / n := by rw [eq_div_iff hn.ne']; linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [sub_nonneg, div_le_iff₀ hn]
    have e : A * (s ^ 2 - 1) - A * (s - 1) = A * (s - 1) * s := by ring
    have := mul_pos (mul_pos hA (show (0:ℝ) < s - 1 by linarith)) (show (0:ℝ) < s by linarith)
    linarith
  · have : 0 < A * (s - 1) / n := div_pos (mul_pos hA (by linarith)) hn
    linarith
  · rw [h1]
    have hY : A + A * (s - 1) = A * s := by ring
    have hs0 : s ≠ 0 := by positivity
    rw [hY, hu]
    field_simp
    ring

/-- `g2` in the normalized form. -/
lemma g2_form (m : Market) (n x : ℝ) :
    g2 m n x = m.mu * (m.c * m.phi) / n * (Real.sqrt (1 + n * x / (m.c * m.phi)) - 1) ^ 2 := by
  unfold g2; ring

lemma g2_nonneg (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi) (hmu : 0 < m.mu)
    (n x : ℝ) (hn : 0 ≤ n) : 0 ≤ g2 m n x := by
  rw [g2_form]
  exact mul_nonneg (div_nonneg (mul_nonneg hmu.le (mul_pos hc hphi).le) hn) (sq_nonneg _)

lemma sqrt_facts (A y : ℝ) (hA : 0 < A) (hy : 0 ≤ y) :
    1 ≤ Real.sqrt (1 + y / A) ∧ Real.sqrt (1 + y / A) ^ 2 = 1 + y / A := by
  have h0 : 0 ≤ y / A := div_nonneg hy hA.le
  refine ⟨?_, Real.sq_sqrt (by linarith)⟩
  rw [show (1:ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (by linarith)

lemma Up_zero (m : Market) (n : ℕ) : Up m 0 n = -m.K := by
  unfold Up
  exact sSup_eq_of (fun x _ => by simp) 0 le_rfl (by simp)

lemma Up_eq (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi) (hmu : 0 < m.mu)
    (hv : 0 ≤ m.v) (ω : ℝ) (hω : 0 ≤ ω) (n : ℕ) (hn : 1 ≤ n) :
    Up m ω n = ω * g2 m n m.v - m.K := by
  have hA : 0 < m.c * m.phi := mul_pos hc hphi
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (1 + (n:ℝ) * m.v / (m.c * m.phi)) := ⟨_, rfl⟩
  obtain ⟨hs1, hs2⟩ := sqrt_facts (m.c * m.phi) ((n:ℝ) * m.v) hA (mul_nonneg hn'.le hv)
  rw [← hs_def] at hs1 hs2
  have hs : (n:ℝ) * m.v = m.c * m.phi * (s ^ 2 - 1) := by
    rw [hs2]; field_simp; try ring
  have hg : g2 m n m.v = m.mu * (m.c * m.phi) / n * (s - 1) ^ 2 := by
    rw [g2_form, ← hs_def]
  have hg0 : 0 ≤ g2 m n m.v := g2_nonneg m hc hphi hmu _ _ hn'.le
  unfold Up
  have hle : ∀ x, 0 ≤ x → ω * x * onDemand m n x - m.K ≤ ω * g2 m n m.v - m.K := by
    intro x hx
    rw [onDemand_eq m hc hphi hmu]
    split_ifs with h
    · have := rev_le (m.c * m.phi) m.mu n m.v x s hA hmu.le hn' h.2 hs
      rw [hg]
      have : ω * x * (m.mu * (n * (m.v - x)) / (m.c * m.phi + n * (m.v - x)))
          ≤ ω * (m.mu * (m.c * m.phi) / n * (s - 1) ^ 2) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith) hω
      linarith
    · have : 0 ≤ ω * g2 m n m.v := mul_nonneg hω hg0
      simp only [mul_zero]; linarith
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · -- v = 0: everything is `-K`
    have hg' : g2 m n m.v = 0 := by rw [g2_form, ← hv0]; simp
    refine sSup_eq_of hle 0 le_rfl ?_
    rw [hg']; simp
  · have hs1' : 1 < s := by
      by_contra h; push_neg at h
      have : s = 1 := le_antisymm h hs1
      rw [this] at hs; have : (n:ℝ) * m.v = 0 := by rw [hs]; ring
      have : 0 < (n:ℝ) * m.v := mul_pos hn' hvpos
      linarith
    obtain ⟨a1, a2, a3⟩ := rev_attain (m.c * m.phi) m.mu n m.v s hA hn' hs1' hs
    refine sSup_eq_of hle _ a1 ?_
    rw [onDemand_eq m hc hphi hmu, if_pos ⟨hn, a2⟩, mul_assoc, a3, hg]

lemma Uo_eq (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi) (hmu : 0 < m.mu)
    (hRo : 0 ≤ m.Ro) :
    Uo m = g2 m 1 (max (m.v - m.Ro) 0) - m.K := by
  have hA : 0 < m.c * m.phi := mul_pos hc hphi
  unfold Uo
  rcases le_or_gt (m.v - m.Ro) 0 with hvr | hvr
  · rw [max_eq_right hvr]
    have hg : g2 m 1 0 = 0 := by rw [g2_form]; simp
    rw [hg]
    refine sSup_eq_of (fun x hx => ?_) 0 le_rfl ?_
    · rw [offDemand_eq m hc hphi hmu, if_neg (by linarith)]; simp
    · rw [offDemand_eq m hc hphi hmu, if_neg (by linarith)]; simp
  · rw [max_eq_left hvr.le]
    set u := m.v - m.Ro with hu_def
    obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (1 + (1:ℝ) * u / (m.c * m.phi)) := ⟨_, rfl⟩
    obtain ⟨hs1, hs2⟩ := sqrt_facts (m.c * m.phi) ((1:ℝ) * u) hA (by linarith)
    rw [← hs_def] at hs1 hs2
    have hs : (1:ℝ) * u = m.c * m.phi * (s ^ 2 - 1) := by
      rw [hs2]; field_simp; try ring
    have hg : g2 m 1 u = m.mu * (m.c * m.phi) / 1 * (s - 1) ^ 2 := by
      rw [g2_form, ← hs_def]
    have hg0 : 0 ≤ g2 m 1 u := g2_nonneg m hc hphi hmu _ _ zero_le_one
    have hle : ∀ x, 0 ≤ x → x * offDemand m x - m.K ≤ g2 m 1 u - m.K := by
      intro x hx
      rw [offDemand_eq m hc hphi hmu]
      split_ifs with h
      · have := rev_le (m.c * m.phi) m.mu 1 u x s hA hmu.le one_pos (by linarith) hs
        rw [hg]; linarith
      · simp only [mul_zero]; linarith
    have hs1' : 1 < s := by
      by_contra h; push_neg at h
      have : s = 1 := le_antisymm h hs1
      rw [this] at hs; linarith
    obtain ⟨a1, a2, a3⟩ := rev_attain (m.c * m.phi) m.mu 1 u s hA one_pos hs1' hs
    refine sSup_eq_of hle _ a1 ?_
    rw [offDemand_eq m hc hphi hmu, if_pos (by linarith), a3, hg]

lemma exists_selected (m : Market) (ω : ℝ) (h : ∃ np no, IsParticipationEq m ω np no) :
    ∃ np no, IsSelectedEq m ω np no := by
  classical
  obtain ⟨np, no, hE⟩ := h
  have hk : np ≤ m.N := le_trans (Nat.le_add_right _ _) hE.1
  have hP : ∃ no, IsParticipationEq m ω
      (Nat.findGreatest (fun k => ∃ no, IsParticipationEq m ω k no) m.N) no :=
    Nat.findGreatest_spec (P := fun k => ∃ no, IsParticipationEq m ω k no) hk ⟨no, hE⟩
  obtain ⟨no', hE'⟩ := hP
  exact ⟨_, no', hE', fun np' no'' h' =>
    Nat.le_findGreatest (le_trans (Nat.le_add_right _ _) h'.1) ⟨no'', h'⟩⟩

/-- Off-platform profitability is the `b`-condition. -/
lemma M1 (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi) (hmu : 0 < m.mu)
    (hK : 0 ≤ m.K) :
    (m.K ≤ g2 m 1 (max (m.v - m.Ro) 0) ∧ 0 < g2 m 1 (max (m.v - m.Ro) 0)) ↔
      (m.Ro < bLeak m ∨ (m.Ro = bLeak m ∧ 0 < m.K)) := by
  have hA : 0 < m.c * m.phi := mul_pos hc hphi
  have hAm : 0 < m.c * m.phi * m.mu := mul_pos hA hmu
  set w := max (m.v - m.Ro) 0 with hw_def
  have hw0 : 0 ≤ w := le_max_right _ _
  have hwv : m.v - m.Ro ≤ w := le_max_left _ _
  obtain ⟨t, ht_def⟩ : ∃ t, t = Real.sqrt (1 + (1:ℝ) * w / (m.c * m.phi)) := ⟨_, rfl⟩
  obtain ⟨ht1, ht2⟩ := sqrt_facts (m.c * m.phi) ((1:ℝ) * w) hA (by linarith)
  rw [← ht_def] at ht1 ht2
  have htw : m.c * m.phi * t ^ 2 = m.c * m.phi + w := by
    rw [ht2]; field_simp; try ring
  obtain ⟨k, hk_def⟩ : ∃ k, k = Real.sqrt (m.K / (m.c * m.phi * m.mu)) := ⟨_, rfl⟩
  have hk0 : 0 ≤ k := by rw [hk_def]; exact Real.sqrt_nonneg _
  have hk2 : k ^ 2 = m.K / (m.c * m.phi * m.mu) := by
    rw [hk_def]; exact Real.sq_sqrt (div_nonneg hK hAm.le)
  have hKk : m.K = m.c * m.phi * m.mu * k ^ 2 := by
    rw [hk2]; field_simp
  have hb : bLeak m = m.v + m.c * m.phi * (1 - (1 + k) ^ 2) := by
    unfold bLeak; rw [← hk_def]
  have hG : g2 m 1 w = m.c * m.phi * m.mu * (t - 1) ^ 2 := by
    rw [g2_form, ← ht_def]; ring
  rw [hG, hb]
  have E1 : m.K ≤ m.c * m.phi * m.mu * (t - 1) ^ 2 ↔ k ≤ t - 1 := by
    rw [hKk, mul_le_mul_iff_of_pos_left hAm]
    exact sq_le_sq_iff' hk0 (by linarith)
  have E2 : k ≤ t - 1 ↔ m.c * m.phi * (1 + k) ^ 2 ≤ m.c * m.phi + w := by
    rw [← htw, mul_le_mul_iff_of_pos_left hA, sq_le_sq_iff' (by linarith) (by linarith)]
    constructor <;> intro h <;> linarith
  have E3 : 0 < m.c * m.phi * m.mu * (t - 1) ^ 2 ↔ 0 < w := by
    constructor
    · intro h
      by_contra hw; push_neg at hw
      have hw' : w = 0 := le_antisymm hw hw0
      have : t ^ 2 = 1 := by rw [hw'] at htw; nlinarith
      have : t = 1 := by nlinarith
      rw [this] at h; simp at h
    · intro h
      have : 1 < t := by
        by_contra hle; push_neg at hle
        have : t = 1 := le_antisymm hle ht1
        rw [this] at htw; linarith
      have : 0 < (t - 1) ^ 2 := by positivity
      positivity
  rw [E1, E2, E3]
  have hkk : 0 ≤ m.c * m.phi * ((1 + k) ^ 2 - 1) := mul_nonneg hA.le (by nlinarith)
  constructor
  · rintro ⟨h1, h2⟩
    have hw' : w = m.v - m.Ro := by
      rw [hw_def]; apply max_eq_left
      by_contra h; push_neg at h
      have : w = 0 := by rw [hw_def]; exact max_eq_right h.le
      linarith
    rcases eq_or_lt_of_le hK with hK0 | hKp
    · left
      have : k = 0 := by
        have : k ^ 2 = 0 := by rw [hk2, ← hK0]; simp
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      rw [this]
      have e : m.c * m.phi * (1 - (1 + 0) ^ 2) = 0 := by ring
      linarith
    · rcases lt_or_eq_of_le (show m.Ro ≤ m.v + m.c * m.phi * (1 - (1 + k) ^ 2) by linarith)
        with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hKp⟩
  · intro h
    have hRb : m.Ro ≤ m.v + m.c * m.phi * (1 - (1 + k) ^ 2) := by
      rcases h with h | ⟨h, _⟩ <;> linarith
    refine ⟨by linarith, ?_⟩
    rcases h with h | ⟨h, hKp⟩
    · linarith
    · have hkp : 0 < k := by
        have : 0 < k ^ 2 := by rw [hk2]; exact div_pos hKp hAm
        nlinarith
      have : 0 < m.c * m.phi * ((1 + k) ^ 2 - 1) := mul_pos hA (by nlinarith)
      linarith

/-- Under off-platform profitability, the threshold condition of (23) is `Ro ≤ a`. -/
lemma M2 (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi) (hmu : 0 < m.mu)
    (hRo : 0 ≤ m.Ro) (hN : 1 ≤ m.N) (hvR : m.Ro < m.v)
    (hKG : m.K ≤ g2 m 1 (max (m.v - m.Ro) 0)) :
    (Khat m ≤ m.c * m.phi * m.mu / m.N
        * (Real.sqrt (1 + m.N * m.v / (m.c * m.phi)) - 1) ^ 2
        - m.mu * m.Ro * (1 - Real.sqrt (m.c * m.phi / (m.c * m.phi + m.N * m.v)))) ↔
      m.Ro ≤ aLeak m := by
  have hA : 0 < m.c * m.phi := mul_pos hc hphi
  have hNr : (1:ℝ) ≤ m.N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < m.N := by linarith
  have hv : 0 < m.v := by linarith
  have hKh : Khat m = g2 m 1 (m.v - m.Ro) := by
    unfold Khat; rw [max_eq_right hKG, max_eq_left (by linarith)]
  rw [hKh]
  obtain ⟨S, hS_def⟩ : ∃ S, S = Real.sqrt (1 + (m.N:ℝ) * m.v / (m.c * m.phi)) := ⟨_, rfl⟩
  obtain ⟨hS1, hS2⟩ := sqrt_facts (m.c * m.phi) ((m.N:ℝ) * m.v) hA (by positivity)
  rw [← hS_def] at hS1 hS2
  have hS : m.c * m.phi * S ^ 2 = m.c * m.phi + m.N * m.v := by
    rw [hS2]; field_simp; try ring
  obtain ⟨T, hT_def⟩ : ∃ T, T = Real.sqrt (1 + (1:ℝ) * (m.v - m.Ro) / (m.c * m.phi)) :=
    ⟨_, rfl⟩
  obtain ⟨hT1, hT2⟩ := sqrt_facts (m.c * m.phi) ((1:ℝ) * (m.v - m.Ro)) hA (by linarith)
  rw [← hT_def] at hT1 hT2
  have hT : m.c * m.phi * T ^ 2 = m.c * m.phi + (m.v - m.Ro) := by
    rw [hT2]; field_simp; try ring
  obtain ⟨r, hr_def⟩ : ∃ r, r = Real.sqrt (((m.N:ℝ) - 1) / m.N) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr_def]; exact Real.sqrt_nonneg _
  have hr2 : r ^ 2 = ((m.N:ℝ) - 1) / m.N := by
    rw [hr_def]; exact Real.sq_sqrt (div_nonneg (by linarith) hN0.le)
  have hr : (m.N:ℝ) * r ^ 2 = m.N - 1 := by rw [hr2]; field_simp
  have hr1 : r ≤ 1 := by
    by_contra h; push_neg at h
    have h1 : 1 < r ^ 2 := by nlinarith
    have h2 : (m.N:ℝ) * 1 < m.N * r ^ 2 := mul_lt_mul_of_pos_left h1 hN0
    linarith
  have hS0 : 0 < S := by linarith
  have hsq : Real.sqrt (m.c * m.phi / (m.c * m.phi + m.N * m.v)) = 1 / S := by
    rw [eq_div_iff hS0.ne', hS_def, ← Real.sqrt_mul (div_nonneg hA.le (by positivity))]
    rw [show m.c * m.phi / (m.c * m.phi + m.N * m.v) * (1 + m.N * m.v / (m.c * m.phi)) = 1 by
      field_simp]
    simp
  have ha : aLeak m = m.v + m.c * m.phi * (1 - ((1 - r) * S + r) ^ 2) := by
    unfold aLeak; rw [← hr_def, ← hS_def]
  have hG : g2 m 1 (m.v - m.Ro) = m.c * m.phi * m.mu * (T - 1) ^ 2 := by
    rw [g2_form, ← hT_def]; ring
  rw [hG, ha, ← hS_def, hsq]
  have hST : T ≤ S := by
    rw [← sq_le_sq_iff' (by linarith) (by linarith)]
    have : m.c * m.phi * T ^ 2 ≤ m.c * m.phi * S ^ 2 := by
      rw [hT, hS]; nlinarith
    exact le_of_mul_le_mul_left this hA
  have hpos : 0 < (m.N:ℝ) * S := mul_pos hN0 hS0
  have hR : (m.N:ℝ) * S * (m.c * m.phi * m.mu / m.N * (S - 1) ^ 2 - m.mu * m.Ro * (1 - 1 / S))
      = m.c * m.phi * m.mu * S * (S - 1) ^ 2 - m.N * m.mu * m.Ro * (S - 1) := by
    field_simp; try ring
  have hid : m.c * m.phi * m.mu * S * (S - 1) ^ 2 - m.N * m.mu * m.Ro * (S - 1)
      - m.N * S * (m.c * m.mu * m.phi * (T - 1) ^ 2)
      = m.mu * (m.c * m.phi) * (m.N * r ^ 2 * (S - 1) ^ 2 - m.N * (T - S) ^ 2) := by
    linear_combination (-(m.N * m.mu * (S - 1))) * hT + (m.mu * (S - 1)) * hS
      + (-(m.mu * m.c * m.phi * (S - 1) ^ 2)) * hr
  have hAm : 0 < m.mu * (m.c * m.phi) := mul_pos hmu hA
  calc (m.c * m.phi * m.mu * (T - 1) ^ 2 ≤
        m.c * m.phi * m.mu / m.N * (S - 1) ^ 2 - m.mu * m.Ro * (1 - 1 / S))
      ↔ (S - T) ^ 2 ≤ (r * (S - 1)) ^ 2 := by
        rw [← mul_le_mul_iff_of_pos_left hpos, hR]
        constructor
        · intro h
          have h' : 0 ≤ m.mu * (m.c * m.phi) * (m.N * r ^ 2 * (S - 1) ^ 2 - m.N * (T - S) ^ 2) := by
            rw [← hid]; linarith
          have h'' : 0 ≤ m.N * r ^ 2 * (S - 1) ^ 2 - m.N * (T - S) ^ 2 := by
            by_contra hx; push_neg at hx
            have := mul_neg_of_pos_of_neg hAm hx; linarith
          have e : (m.N:ℝ) * ((r * (S - 1)) ^ 2 - (S - T) ^ 2)
              = m.N * r ^ 2 * (S - 1) ^ 2 - m.N * (T - S) ^ 2 := by ring
          by_contra hx; push_neg at hx
          have := mul_neg_of_pos_of_neg hN0 (show (r * (S - 1)) ^ 2 - (S - T) ^ 2 < 0 by linarith)
          linarith
        · intro h
          have h'' : 0 ≤ m.N * r ^ 2 * (S - 1) ^ 2 - m.N * (T - S) ^ 2 := by
            have : 0 ≤ (m.N:ℝ) * ((r * (S - 1)) ^ 2 - (S - T) ^ 2) :=
              mul_nonneg hN0.le (by linarith)
            have e : (m.N:ℝ) * ((r * (S - 1)) ^ 2 - (S - T) ^ 2)
                = m.N * r ^ 2 * (S - 1) ^ 2 - m.N * (T - S) ^ 2 := by ring
            linarith
          have := mul_nonneg hAm.le h''
          rw [← hid] at this
          linarith
    _ ↔ S - T ≤ r * (S - 1) := sq_le_sq_iff' (by linarith) (mul_nonneg hr0 (by linarith))
    _ ↔ ((1 - r) * S + r) ^ 2 ≤ T ^ 2 := by
        have := mul_nonneg (sub_nonneg.2 hr1) hS0.le
        rw [sq_le_sq_iff' (by linarith) (by linarith)]
        constructor <;> intro h <;> linarith
    _ ↔ m.Ro ≤ m.v + m.c * m.phi * (1 - ((1 - r) * S + r) ^ 2) := by
        rw [← mul_le_mul_iff_of_pos_left hA, hT]
        constructor <;> intro h <;> linarith

lemma main (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi)
    (hmu : 0 < m.mu) (hRo : 0 ≤ m.Ro) (hv : 0 ≤ m.v) (hK : 0 ≤ m.K) (hN : 1 ≤ m.N) :
    (∃ np no : ℕ, IsSelectedEq m (omegaStar m) np no) ∧
    ∀ np no : ℕ, IsSelectedEq m (omegaStar m) np no →
      (0 < no ↔ aLeak m < m.Ro ∧ (m.Ro < bLeak m ∨ (m.Ro = bLeak m ∧ 0 < m.K))) := by
  have hA : 0 < m.c * m.phi := mul_pos hc hphi
  have hN0 : (0:ℝ) < m.N := by exact_mod_cast hN
  have hUo := Uo_eq m hc hphi hmu hRo
  set Go := g2 m 1 (max (m.v - m.Ro) 0) with hGo_def
  have hGo0 : 0 ≤ Go := g2_nonneg m hc hphi hmu _ _ zero_le_one
  have hM1 := M1 m hc hphi hmu hK
  rw [← hGo_def] at hM1
  have hKh : Khat m = max m.K Go := rfl
  by_cases hω0 : omegaStar m = 0
  · rw [hω0]
    by_cases hP : m.K ≤ Go ∧ 0 < Go
    · -- leakage
      have hvR : m.Ro < m.v := by
        by_contra h; push_neg at h
        have : Go = 0 := by rw [hGo_def, max_eq_right (by linarith), g2_form]; simp
        linarith [hP.2]
      have hcond : ¬ (Khat m ≤ m.c * m.phi * m.mu / m.N
          * (Real.sqrt (1 + m.N * m.v / (m.c * m.phi)) - 1) ^ 2
          - m.mu * m.Ro * (1 - Real.sqrt (m.c * m.phi / (m.c * m.phi + m.N * m.v)))) := by
        intro hc'
        have hGN : 0 < g2 m m.N m.v := by
          have hvp : 0 < m.v := by linarith
          obtain ⟨hs1, hs2⟩ := sqrt_facts (m.c * m.phi) ((m.N:ℝ) * m.v) hA (by positivity)
          have hgt : 1 < Real.sqrt (1 + (m.N:ℝ) * m.v / (m.c * m.phi)) := by
            rw [show (1:ℝ) = Real.sqrt 1 by simp]
            apply Real.sqrt_lt_sqrt (by norm_num)
            have : 0 < (m.N:ℝ) * m.v / (m.c * m.phi) := by positivity
            linarith
          rw [g2_form]
          have : 0 < (Real.sqrt (1 + (m.N:ℝ) * m.v / (m.c * m.phi)) - 1) ^ 2 := by
            have : 0 < Real.sqrt (1 + (m.N:ℝ) * m.v / (m.c * m.phi)) - 1 := by linarith
            positivity
          exact mul_pos (div_pos (mul_pos hmu hA) hN0) this
        have : omegaStar m = Khat m / g2 m m.N m.v := by unfold omegaStar; rw [if_pos hc']
        rw [hω0, hKh, max_eq_right hP.1] at this
        have : Go / g2 m m.N m.v > 0 := div_pos hP.2 hGN
        linarith
      have hM2 := M2 m hc hphi hmu hRo hN hvR hP.1
      have hRHS : aLeak m < m.Ro ∧ (m.Ro < bLeak m ∨ (m.Ro = bLeak m ∧ 0 < m.K)) := by
        refine ⟨?_, hM1.1 hP⟩
        by_contra h; push_neg at h
        exact hcond (hM2.2 h)
      refine ⟨exists_selected m 0 ⟨0, m.N, ?_⟩, fun np no hsel => ?_⟩
      · refine ⟨by simp, fun h => absurd h (lt_irrefl 0), fun _ => ⟨?_, ?_⟩, fun h => ?_⟩
        · rw [Up_zero, hUo]; exact max_le (by linarith) (by linarith [hP.1])
        · rw [Up_zero, hUo]; linarith [hP.2]
        · simp at h
      · obtain ⟨⟨h1, h2, h3, h4⟩, _⟩ := hsel
        refine iff_of_true ?_ hRHS
        have hnp : np = 0 := by
          by_contra hne
          have := h2 (Nat.pos_of_ne_zero hne)
          rw [Up_zero, hUo] at this
          have a1 := le_max_left (Go - m.K) 0
          have a2 := le_max_right (Go - m.K) 0
          linarith [hP.2]
        by_contra hno; push_neg at hno
        have hno0 : no = 0 := by omega
        have := (h4 (by omega)).2
        rw [hUo] at this
        linarith [hP.1]
    · -- no leakage
      have hRHS : ¬ (aLeak m < m.Ro ∧ (m.Ro < bLeak m ∨ (m.Ro = bLeak m ∧ 0 < m.K))) :=
        fun h => hP (hM1.2 h.2)
      have hno : ∀ np no, IsParticipationEq m 0 np no → no = 0 := by
        intro np no hE
        by_contra hne
        obtain ⟨b1, b2⟩ := hE.2.2.1 (Nat.pos_of_ne_zero hne)
        rw [Up_zero, hUo] at b1 b2
        exact hP ⟨by linarith [le_max_right (-m.K) 0], by linarith⟩
      refine ⟨?_, fun np no hsel => iff_of_false (by rw [hno np no hsel.1]; simp) hRHS⟩
      apply exists_selected
      rcases lt_or_ge Go m.K with hlt | hge
      · refine ⟨0, 0, by simp, fun h => absurd h (lt_irrefl 0),
          fun h => absurd h (lt_irrefl 0), fun _ => ⟨?_, ?_⟩⟩
        · rw [Up_zero]; linarith
        · rw [hUo]; linarith
      · have hG0 : Go = 0 := by
          by_contra h; exact hP ⟨hge, lt_of_le_of_ne hGo0 (Ne.symm h)⟩
        have hK0 : m.K = 0 := by linarith
        refine ⟨m.N, 0, by simp, fun _ => ?_, fun h => absurd h (lt_irrefl 0),
          fun h => by simp at h⟩
        rw [Up_zero, hUo, hG0, hK0]; simp
  · -- ω* ≠ 0: everyone on the platform
    have hcond : Khat m ≤ m.c * m.phi * m.mu / m.N
          * (Real.sqrt (1 + m.N * m.v / (m.c * m.phi)) - 1) ^ 2
          - m.mu * m.Ro * (1 - Real.sqrt (m.c * m.phi / (m.c * m.phi + m.N * m.v))) := by
      by_contra h
      exact hω0 (by unfold omegaStar; rw [if_neg h])
    have hωe : omegaStar m = Khat m / g2 m m.N m.v := by unfold omegaStar; rw [if_pos hcond]
    have hGN : g2 m m.N m.v ≠ 0 := by
      intro h0; rw [h0, div_zero] at hωe; exact hω0 hωe
    have hKh0 : 0 ≤ Khat m := le_trans hK (le_max_left _ _)
    have hω_nn : 0 ≤ omegaStar m := by
      rw [hωe]; exact div_nonneg hKh0 (g2_nonneg m hc hphi hmu _ _ hN0.le)
    have hUpN : Up m (omegaStar m) m.N = Khat m - m.K := by
      rw [Up_eq m hc hphi hmu hv _ hω_nn m.N hN, hωe, div_mul_cancel₀ _ hGN]
    have hEqN : IsParticipationEq m (omegaStar m) m.N 0 := by
      refine ⟨by simp, fun _ => ?_, fun h => absurd h (lt_irrefl 0), fun h => by simp at h⟩
      rw [hUpN, hUo, hKh]
      exact max_le (by linarith [le_max_right m.K Go]) (by linarith [le_max_left m.K Go])
    refine ⟨exists_selected m _ ⟨m.N, 0, hEqN⟩, fun np no hsel => ?_⟩
    have hnp := hsel.2 m.N 0 hEqN
    have h1 := hsel.1.1
    have hno0 : no = 0 := by omega
    refine iff_of_false (by rw [hno0]; simp) ?_
    rintro ⟨ha, hb⟩
    have hP := hM1.2 hb
    have hvR : m.Ro < m.v := by
      by_contra h; push_neg at h
      have : Go = 0 := by rw [hGo_def, max_eq_right (by linarith), g2_form]; simp
      linarith [hP.2]
    have hM2 := M2 m hc hphi hmu hRo hN hvR hP.1
    have := hM2.1 hcond
    linarith

end OPTLeakHelp

open OffPlatformThreats.Leakage in
theorem solution (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi)
    (hmu : 0 < m.mu) (hRo : 0 ≤ m.Ro) (hv : 0 ≤ m.v) (hK : 0 ≤ m.K) (hN : 1 ≤ m.N) :
    (∃ np no : ℕ, IsSelectedEq m (omegaStar m) np no) ∧
    ∀ np no : ℕ, IsSelectedEq m (omegaStar m) np no →
      (0 < no ↔ aLeak m < m.Ro ∧ (m.Ro < bLeak m ∨ (m.Ro = bLeak m ∧ 0 < m.K))) := by
  exact OPTLeakHelp.main m hc hphi hmu hRo hv hK hN
