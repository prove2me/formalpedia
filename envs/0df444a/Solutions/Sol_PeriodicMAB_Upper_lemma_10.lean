-- Prove2me | solution 1 for PeriodicMAB.Upper.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T00:19:59.712306+00:00
-- url     : https://prove2.me/submissions/23cbab34-dab3-416f-aba1-17d2967f729c

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral
import Definitions.Def_PeriodicMAB_Upper_Policy

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
open PeriodicMAB.Upper

section Struct
variable {K : ℕ} [NeZero K] (σ δ : ℝ) (T n : ℕ) (Phat : Fin K → ℕ) (Y : Fin K → ℕ → ℝ)
  (h : List (Decision K)) (t : ℕ)

/-- Round `s'` of the tournament ended in Step 14. -/
def pmab10_passed (s' : ℕ) : Prop :=
  (¬ ∃ k ∈ activeSet σ n Phat Y h t s', σ / 2 ^ s' < wHat σ δ Phat h n s' k t) ∧
    ¬ (∀ k ∈ activeSet σ n Phat Y h t s', wHat σ δ Phat h n s' k t ≤ σ / Real.sqrt T)

lemma pmab10_tourney : ∀ (f s0 : ℕ),
    (∃ a s, tourney σ δ T n Phat Y h t f s0 = (a, s, true) ∧ s0 ≤ s ∧ s < s0 + f ∧
        (∀ s' ∈ Ico s0 s, pmab10_passed σ δ T n Phat Y h t s') ∧
        a ∈ activeSet σ n Phat Y h t s ∧ σ / 2 ^ s < wHat σ δ Phat h n s a t) ∨
    (∃ a s, tourney σ δ T n Phat Y h t f s0 = (a, s, false) ∧ s0 ≤ s ∧ s < s0 + f ∧
        (∀ s' ∈ Ico s0 s, pmab10_passed σ δ T n Phat Y h t s') ∧
        (∀ k ∈ activeSet σ n Phat Y h t s, wHat σ δ Phat h n s k t ≤ σ / Real.sqrt T) ∧
        a = argmaxOver (activeSet σ n Phat Y h t s) (fun k => mHat Phat Y h n s k t)) ∨
    ((∀ s' ∈ Ico s0 (s0 + f), pmab10_passed σ δ T n Phat Y h t s') ∧
      tourney σ δ T n Phat Y h t f s0 =
        (argmaxOver (activeSet σ n Phat Y h t (s0 + f - 1))
          (fun k => mHat Phat Y h n (s0 + f - 1) k t), s0 + f - 1, false)) := by
  intro f
  induction f with
  | zero =>
    intro s0
    right; right
    refine ⟨fun s' hs' => by simp at hs', ?_⟩
    simp [tourney]
  | succ f ih =>
    intro s0
    by_cases h1 : ∃ k ∈ activeSet σ n Phat Y h t s0, σ / 2 ^ s0 < wHat σ δ Phat h n s0 k t
    · left
      have hne : ((activeSet σ n Phat Y h t s0).filter
          (fun k => σ / 2 ^ s0 < wHat σ δ Phat h n s0 k t)).Nonempty := by
        obtain ⟨k, hk, hk'⟩ := h1
        exact ⟨k, Finset.mem_filter.mpr ⟨hk, hk'⟩⟩
      refine ⟨_, s0, by rw [tourney, if_pos h1], le_rfl, by omega,
        fun s' hs' => by simp at hs', ?_⟩
      unfold firstOf
      rw [dif_pos hne]
      exact Finset.mem_filter.mp (Finset.min'_mem _ hne)
    by_cases h2 : ∀ k ∈ activeSet σ n Phat Y h t s0, wHat σ δ Phat h n s0 k t ≤ σ / Real.sqrt T
    · right; left
      refine ⟨_, s0, by rw [tourney, if_neg h1, if_pos h2], le_rfl, by omega,
        fun s' hs' => by simp at hs', h2, rfl⟩
    have hpass : pmab10_passed σ δ T n Phat Y h t s0 := ⟨h1, h2⟩
    have htour : tourney σ δ T n Phat Y h t (f + 1) s0 = tourney σ δ T n Phat Y h t f (s0 + 1) := by
      rw [tourney, if_neg h1, if_neg h2]
    have hext : ∀ s, (∀ s' ∈ Ico (s0 + 1) s, pmab10_passed σ δ T n Phat Y h t s') →
        ∀ s' ∈ Ico s0 s, pmab10_passed σ δ T n Phat Y h t s' := by
      intro s hs s' hs'
      rcases Nat.eq_or_lt_of_le (Finset.mem_Ico.mp hs').1 with heq | hlt
      · rw [← heq]; exact hpass
      · exact hs s' (Finset.mem_Ico.mpr ⟨hlt, (Finset.mem_Ico.mp hs').2⟩)
    rcases ih (s0 + 1) with ⟨a, s, hr, hs1, hs2, hp, rest⟩ | ⟨a, s, hr, hs1, hs2, hp, rest⟩ | ⟨hp, hr⟩
    · left; exact ⟨a, s, htour ▸ hr, by omega, by omega, hext s hp, rest⟩
    · right; left; exact ⟨a, s, htour ▸ hr, by omega, by omega, hext s hp, rest⟩
    · right; right
      refine ⟨by have := hext (s0 + 1 + f) hp; rwa [show s0 + 1 + f = s0 + (f + 1) by ring] at this, ?_⟩
      rw [htour, hr, show s0 + 1 + f - 1 = s0 + (f + 1) - 1 by omega]

lemma pmab10_argmax (A : Finset (Fin K)) (f : Fin K → ℝ) (hA : A.Nonempty) :
    argmaxOver A f ∈ A ∧ ∀ k ∈ A, f k ≤ f (argmaxOver A f) := by
  classical
  obtain ⟨k0, hk0, hk0'⟩ := Finset.exists_max_image A f hA
  have hne : (A.filter (fun k => ∀ k' ∈ A, f k' ≤ f k)).Nonempty :=
    ⟨k0, Finset.mem_filter.mpr ⟨hk0, hk0'⟩⟩
  have hmem : argmaxOver A f ∈ A.filter (fun k => ∀ k' ∈ A, f k' ≤ f k) := by
    unfold argmaxOver firstOf
    convert Finset.min'_mem _ hne
    rw [dif_pos]
  exact Finset.mem_filter.mp hmem

end Struct

theorem solution {Ω : Type*} (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ)
    {K : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (Tper : Fin K → ℕ) (T n g : ℕ) (δ : ℝ)
    (hper : ∀ k, IsMinPeriod (μ k) (Tper k)) (hA1 : Assumption1 μ T)
    (hA3 : Assumption3 T n g Tper) (hnK : n * K ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (ω : Ω) (hω : ω ∈ eventE μ ε σ δ T n Tper) (t : ℕ) (ht : t ∈ Icc (n * K + 1) T)
    (a : Fin K) (s : ℕ) (step9 : Bool)
    (hdec : decisionAt σ δ T n Tper (reward μ ε ω) t = (a, s, step9))
    (kstar : Fin K) (hstar : ∀ k, μ k t ≤ μ kstar t) :
    (∀ s' ∈ Icc 1 s, kstar ∈ activeAt σ δ T n Tper (reward μ ε ω) s' t) ∧
    (step9 = true → s = 1 → μ kstar t - μ a t ≤ 1) ∧
    (step9 = true → 2 ≤ s → μ kstar t - μ a t ≤ 8 * σ / 2 ^ s) ∧
    (step9 = false → μ kstar t - μ a t ≤ 2 * σ / Real.sqrt T) := by
  set Y := reward μ ε ω with hY
  set h := runHist σ δ T n Tper Y (t - 1) with hh
  set S := Nat.log 2 T with hS
  set A := fun s' => activeSet σ n Tper Y h t s' with hA
  set m := fun s' k => mHat Tper Y h n s' k t with hm
  set w := fun s' k => wHat σ δ Tper h n s' k t with hw
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  rw [Finset.mem_Icc] at ht
  -- T ≥ 5
  obtain ⟨hT4K, hg2, hsqg, hTk⟩ := hA3
  have hKpos : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hT5 : 5 ≤ T := by omega
  -- the event ℰ at epoch t
  have hE : ∀ s' ∈ Icc 1 S, ∀ k, |m s' k - μ k t| ≤ w s' k :=
    fun s' hs' k => hω k t (Finset.mem_Icc.mpr ⟨ht.1, ht.2⟩) s' hs'
  -- 2^S ≥ √T
  have hSqrt : Real.sqrt T ≤ 2 ^ S := by
    have hlt : T < 2 ^ (S + 1) := Nat.lt_pow_succ_log_self (by norm_num) T
    have hTR : (T : ℝ) < 2 * 2 ^ S := by
      have : (T : ℝ) < ((2 ^ (S + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
      push_cast at this; rw [pow_succ] at this; linarith
    have hT5R : (5 : ℝ) ≤ T := by exact_mod_cast hT5
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith
  have hS1 : 1 ≤ S := by
    rw [hS]; exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  -- characterize the decision
  have hdec' : tourney σ δ T n Tper Y h t S 1 = (a, s, step9) := by
    rw [← hdec, decisionAt, decision, if_neg (by omega)]
  have hpass_w : ∀ s', pmab10_passed σ δ T n Tper Y h t s' →
      ∀ k ∈ A s', w s' k ≤ σ / 2 ^ s' := by
    intro s' hp k hk
    by_contra hc; push Not at hc
    exact hp.1 ⟨k, hk, hc⟩
  -- part 1 from the passed rounds
  have part1 : ∀ s1, (∀ s' ∈ Ico 1 s1, pmab10_passed σ δ T n Tper Y h t s') → s1 ≤ S →
      ∀ s' ∈ Icc 1 s1, kstar ∈ A s' := by
    intro s1 hp hs1S s' hs'
    obtain ⟨hs'1, hs's1⟩ := Finset.mem_Icc.mp hs'
    induction s' with
    | zero => omega
    | succ s'' ih =>
      rcases Nat.eq_zero_or_pos s'' with h0 | hpos
      · subst h0; simp [hA, activeSet]
      have hin : kstar ∈ A s'' := ih (Finset.mem_Icc.mpr ⟨hpos, by omega⟩) hpos (by omega)
      have hps := hp s'' (Finset.mem_Ico.mpr ⟨hpos, by omega⟩)
      have hEs := hE s'' (Finset.mem_Icc.mpr ⟨hpos, by omega⟩)
      have hws := hpass_w s'' hps
      show kstar ∈ activeSet σ n Tper Y h t (s'' + 1)
      rw [activeSet, if_neg (by omega), Finset.mem_filter]
      refine ⟨hin, ?_⟩
      have hne : (activeSet σ n Tper Y h t s'').Nonempty := ⟨kstar, hin⟩
      unfold maxOver
      rw [dif_pos hne]
      have : ∀ k ∈ activeSet σ n Tper Y h t s'', mHat Tper Y h n s'' k t ≤
          mHat Tper Y h n s'' kstar t + 2 * σ / 2 ^ s'' := by
        intro k hk
        have e1 := abs_le.mp (hEs k)
        have e2 := abs_le.mp (hEs kstar)
        have w1 := hws k hk
        have w2 := hws kstar hin
        have := hstar k
        simp only [hm, hw] at e1 e2 w1 w2
        have : 2 * (σ : ℝ) / 2 ^ s'' = σ / 2 ^ s'' + σ / 2 ^ s'' := by ring
        linarith
      have := Finset.sup'_le hne (fun k => mHat Tper Y h n s'' k t) this
      linarith
  rcases pmab10_tourney σ δ T n Tper Y h t S 1 with
    ⟨a', s', hr, hs1, hs2, hp, haA, hwide⟩ | ⟨a', s', hr, hs1, hs2, hp, hnarrow, harg⟩ | ⟨hp, hr⟩
  · -- Step 9
    rw [hdec'] at hr
    have hr' := hr.symm
    simp only [Prod.mk.injEq] at hr'
    obtain ⟨rfl, rfl, rfl⟩ := hr'
    have P1 := part1 s' hp (by omega)
    refine ⟨P1, ?_, ?_, by simp⟩
    · intro _ _
      have h1 := (hA1 kstar t (by omega) ht.2).2
      have h2 := (hA1 a' t (by omega) ht.2).1
      linarith
    · intro _ hs2'
      -- round s' - 1 passed and `a'` survived the screening into round s'
      obtain ⟨r, rfl⟩ : ∃ r, s' = r + 1 := ⟨s' - 1, by omega⟩
      have hr1 : 1 ≤ r := by omega
      have hps := hp r (Finset.mem_Ico.mpr ⟨hr1, by omega⟩)
      have hEs := hE r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩)
      have hws := hpass_w r hps
      have hkin : kstar ∈ A r := P1 r (Finset.mem_Icc.mpr ⟨hr1, by omega⟩)
      have haA' : a' ∈ activeSet σ n Tper Y h t (r + 1) := haA
      rw [activeSet, if_neg (by omega), Finset.mem_filter] at haA'
      obtain ⟨har, hscreen⟩ := haA'
      have hne : (activeSet σ n Tper Y h t r).Nonempty := ⟨kstar, hkin⟩
      unfold maxOver at hscreen
      rw [dif_pos hne] at hscreen
      have hle := Finset.le_sup' (fun k => mHat Tper Y h n r k t) hkin
      have e1 := abs_le.mp (hEs a')
      have e2 := abs_le.mp (hEs kstar)
      have w1 := hws a' har
      have w2 := hws kstar hkin
      simp only [hm, hw] at e1 e2 w1 w2 hle
      have : 8 * (σ : ℝ) / 2 ^ (r + 1) = 4 * (σ / 2 ^ r) := by rw [pow_succ]; field_simp; ring
      rw [this]
      have : 2 * (σ : ℝ) / 2 ^ r = 2 * (σ / 2 ^ r) := by ring
      rw [this] at hscreen
      linarith
  · -- Step 12
    rw [hdec'] at hr
    have hr' := hr.symm
    simp only [Prod.mk.injEq] at hr'
    obtain ⟨rfl, rfl, rfl⟩ := hr'
    have P1 := part1 s' hp (by omega)
    refine ⟨P1, by simp, by simp, fun _ => ?_⟩
    have hkin : kstar ∈ A s' := P1 s' (Finset.mem_Icc.mpr ⟨hs1, le_rfl⟩)
    have hne : (activeSet σ n Tper Y h t s').Nonempty := ⟨kstar, hkin⟩
    obtain ⟨hamem, hamax⟩ := pmab10_argmax (activeSet σ n Tper Y h t s')
      (fun k => mHat Tper Y h n s' k t) hne
    rw [← harg] at hamem hamax
    have hEs := hE s' (Finset.mem_Icc.mpr ⟨hs1, by omega⟩)
    have e1 := abs_le.mp (hEs a')
    have e2 := abs_le.mp (hEs kstar)
    have w1 := hnarrow a' hamem
    have w2 := hnarrow kstar hkin
    have := hamax kstar hkin
    simp only [hm, hw] at e1 e2 w1 w2 this
    have : 2 * (σ : ℝ) / Real.sqrt T = σ / Real.sqrt T + σ / Real.sqrt T := by ring
    linarith
  · -- fuel exhausted: impossible, since round S would have ended in Step 11
    exfalso
    have hpS := hp S (Finset.mem_Ico.mpr ⟨hS1, by omega⟩)
    apply hpS.2
    intro k hk
    have := hpass_w S hpS k hk
    calc wHat σ δ Tper h n S k t ≤ σ / 2 ^ S := this
      _ ≤ σ / Real.sqrt T := by
        apply div_le_div_of_nonneg_left hσR.le _ hSqrt
        apply Real.sqrt_pos.mpr; exact_mod_cast (by omega : 0 < T)
