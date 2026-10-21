-- Prove2me | solution 1 for YoungConventions.AdaptivePlay.example_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:23:21.386099+00:00
-- url     : https://prove2.me/submissions/9e28797a-25f4-4938-b426-c251f9976817

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReplyDistribution
import Definitions.Def_YoungConventions_AdaptivePlay_adaptivePlay
import Definitions.Def_YoungConventions_AdaptivePlay_yieldGame

set_option autoImplicit false
open YoungConventions.AdaptivePlay

theorem yca_P_nonneg {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, Fintype (S i)] {m : ℕ} [NeZero m]
    (p : ∀ i, History S m → S i → ℝ) (hp0 : ∀ i h x, 0 ≤ p i h x) (h h' : History S m) :
    0 ≤ adaptivePlay p h h' := by
  unfold adaptivePlay
  split_ifs
  · exact Finset.prod_nonneg (fun i _ => hp0 i h _)
  · exact le_rfl

theorem yca_P_rowsum {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] {m : ℕ} [NeZero m]
    (p : ∀ i, History S m → S i → ℝ) (hp1 : ∀ i h, ∑ x, p i h x = 1) (h : History S m) :
    ∑ h', adaptivePlay p h h' = 1 := by
  classical
  have hm : 0 < m := NeZero.pos m
  let L : Fin m := ⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩
  let φ : (∀ i, S i) → History S m :=
    fun s t => if ht : t.val + 1 < m then h ⟨t.val + 1, ht⟩ else s
  have hφL : ∀ s, φ s L = s := by
    intro s; simp only [φ, L]; rw [dif_neg (by omega)]
  have hinj : Function.Injective φ := fun s s' hss => by
    have := congrFun hss L
    rwa [hφL, hφL] at this
  have hsucc : ∀ h', IsSuccessor h h' ↔ h' = φ (h' L) := by
    intro h'
    constructor
    · intro hs
      funext t
      by_cases ht : t.val + 1 < m
      · simp only [φ, dif_pos ht]; exact hs t ht
      · have : t = L := by apply Fin.ext; simp only [L]; omega
        subst this
        exact (hφL _).symm
    · intro e t ht
      have := congrFun e t
      rw [this]
      simp only [φ, dif_pos ht]
  calc ∑ h', adaptivePlay p h h'
      = ∑ h' ∈ Finset.univ.filter (fun h' => IsSuccessor h h'), ∏ i, p i h (h' L i) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun h' _ => ?_)
        by_cases hs : IsSuccessor h h' <;> simp [adaptivePlay, hs, L]
    _ = ∑ h' ∈ Finset.univ.image φ, ∏ i, p i h (h' L i) := by
        congr 1
        ext h'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hs; exact ⟨h' L, ((hsucc h').mp hs).symm⟩
        · rintro ⟨s, rfl⟩; exact (hsucc _).mpr (by rw [hφL])
    _ = ∑ s : ∀ i, S i, ∏ i, p i h (φ s L i) :=
        Finset.sum_image hinj.injOn
    _ = ∑ s : ∀ i, S i, ∏ i, p i h (s i) := by simp_rw [hφL]
    _ = ∏ i, ∑ x, p i h x := (Fintype.prod_sum (fun i x => p i h x)).symm
    _ = 1 := by simp [hp1 _ h]

theorem yca_stoch_pow {H : Type*} [Fintype H] [DecidableEq H] (A : Matrix H H ℝ)
    (h0 : ∀ a b, 0 ≤ A a b) (h1 : ∀ a, ∑ b, A a b = 1) :
    ∀ n : ℕ, (∀ a b, 0 ≤ (A ^ n) a b) ∧ ∀ a, ∑ b, (A ^ n) a b = 1 := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [pow_zero, Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ]
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [Matrix.mul_apply]
      exact Finset.sum_nonneg (fun c _ => mul_nonneg (ih.1 a c) (h0 c b))
    · simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, h1, mul_one]
      exact ih.2 a


theorem yca_yield_step (m : ℕ) [NeZero m]
    (p : ∀ i : Fin 2, History (fun _ : Fin 2 => Bool) m → Bool → ℝ)
    (hp : IsBestReplyDistribution (S := fun _ : Fin 2 => Bool) yieldGame m p)
    (h h'' : History (fun _ : Fin 2 => Bool) m) (hh : ∀ t, h t 0 = h t 1)
    (hA : 0 < adaptivePlay p h h'') : ∀ t, h'' t 0 = h'' t 1 := by
  have hm : 0 < m := NeZero.pos m
  unfold adaptivePlay at hA
  by_cases hs : IsSuccessor h h''
  swap
  · rw [if_neg hs] at hA; exact absurd hA (lt_irrefl _)
  rw [if_pos hs] at hA
  set L : Fin m := ⟨m - 1, Nat.sub_lt (NeZero.pos m) Nat.one_pos⟩ with hL
  -- every factor is positive
  have hfac : ∀ i : Fin 2, 0 < p i h (h'' L i) := by
    intro i
    by_contra hn
    have h0 : p i h (h'' L i) = 0 := le_antisymm (not_lt.mp hn) (hp.1 _ _ _)
    have : ∏ i, p i h (h'' L i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [this] at hA
    exact lt_irrefl _ hA
  -- sample = whole history
  have hbr : ∀ i : Fin 2, ∀ y : Bool,
      ∑ t : Fin m, yieldGame i (Function.update (h t) i y) ≤
        ∑ t : Fin m, yieldGame i (Function.update (h t) i (h'' L i)) := by
    intro i y
    obtain ⟨K, hK, hbest⟩ := (hp.2.2 i h _).mp (hfac i)
    have hKu : K = Finset.univ := Finset.eq_univ_of_card K (by simpa using hK)
    subst hKu
    exact hbest y
  have hu0 : ∀ y t, yieldGame 0 (Function.update (h t) 0 y) =
      if y = true ∧ h t 1 = false then 1 else if y = false ∧ h t 1 = true then Real.sqrt 2 else 0 := by
    intro y t; simp [yieldGame, Function.update]
  have hu1 : ∀ y t, yieldGame 1 (Function.update (h t) 1 y) =
      if h t 0 = true ∧ y = false then Real.sqrt 2 else if h t 0 = false ∧ y = true then 1 else 0 := by
    intro y t; simp [yieldGame, Function.update]
  have hF : ∀ y, ∑ t : Fin m, yieldGame 1 (Function.update (h t) 1 y) =
      ∑ t : Fin m, yieldGame 0 (Function.update (h t) 0 y) := by
    intro y
    apply Finset.sum_congr rfl
    intro t _
    rw [hu0, hu1, hh t]
    cases h t 1 <;> cases y <;> simp
  have hbool : ∀ (F : Bool → ℝ) (a b : Bool), F a = F b → a ≠ b → F true = F false := by
    intro F a b hab hne
    cases a <;> cases b
    · exact absurd rfl hne
    · exact hab.symm
    · exact hab
    · exact absurd rfl hne
  have hsame : h'' L 0 = h'' L 1 := by
    have h0 := hbr 0
    have h1 := hbr 1
    generalize h'' L 0 = x0 at h0 ⊢
    generalize h'' L 1 = x1 at h1 ⊢
    have hFx : ∑ t : Fin m, yieldGame 0 (Function.update (h t) 0 x0) =
        ∑ t : Fin m, yieldGame 0 (Function.update (h t) 0 x1) := by
      apply le_antisymm
      · have := h1 x0; rw [hF, hF] at this; exact this
      · exact h0 x1
    by_contra hne
    have hTF := hbool (fun y => ∑ t : Fin m, yieldGame 0 (Function.update (h t) 0 y)) x0 x1 hFx hne
    have hT : ∑ t : Fin m, yieldGame 0 (Function.update (h t) 0 true) =
        ((Finset.univ.filter (fun t : Fin m => h t 0 = false)).card : ℝ) := by
      rw [← Finset.sum_boole]
      apply Finset.sum_congr rfl
      intro t _
      rw [hu0, ← hh t]; cases h t 0 <;> simp
    have hFa : ∑ t : Fin m, yieldGame 0 (Function.update (h t) 0 false) =
        ((Finset.univ.filter (fun t : Fin m => h t 0 = true)).card : ℝ) * Real.sqrt 2 := by
      rw [← Finset.sum_boole, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [hu0, ← hh t]; cases h t 0 <;> simp
    simp only [hT, hFa] at hTF
    have hab : (Finset.univ.filter (fun t : Fin m => h t 0 = true)).card +
        (Finset.univ.filter (fun t : Fin m => h t 0 = false)).card = m := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
        (fun t : Fin m => h t 0 = true)
      simpa using this
    generalize (Finset.univ.filter (fun t : Fin m => h t 0 = true)).card = a at hTF hab
    generalize (Finset.univ.filter (fun t : Fin m => h t 0 = false)).card = b at hTF hab
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · subst ha0
      simp at hTF
      omega
    · apply irrational_sqrt_two
      refine ⟨(b : ℚ) / a, ?_⟩
      have hapos' : (0 : ℝ) < a := by exact_mod_cast hapos
      push_cast
      field_simp
      linarith
  intro t
  by_cases ht : t.val + 1 < m
  · have e := hs t ht
    rw [e]; exact hh _
  · have : t = L := by apply Fin.ext; simp only [hL]; omega
    rw [this]; exact hsame

theorem solution (m : ℕ) [NeZero m]
    (p : ∀ i : Fin 2, History (fun _ : Fin 2 => Bool) m → Bool → ℝ)
    (hp : IsBestReplyDistribution (S := fun _ : Fin 2 => Bool) yieldGame m p)
    (h : History (fun _ : Fin 2 => Bool) m) (hh : ∀ t, h t 0 = h t 1)
    (n : ℕ) (h' : History (fun _ : Fin 2 => Bool) m)
    (hpos : 0 < (adaptivePlay p ^ n) h h') :
    ∀ t, h' t 0 = h' t 1 := by
  have hP0 := yca_P_nonneg p hp.1
  have hP1 := yca_P_rowsum p hp.2.1
  have hst := yca_stoch_pow (adaptivePlay p) hP0 hP1
  have key : ∀ n : ℕ, ∀ (h h' : History (fun _ : Fin 2 => Bool) m),
      0 < (adaptivePlay p ^ n) h h' → (∀ t, h t 0 = h t 1) → ∀ t, h' t 0 = h' t 1 := by
    intro n
    induction n with
    | zero =>
      intro h h' hpos hh
      rw [pow_zero, Matrix.one_apply] at hpos
      by_cases e : h = h'
      · subst e; exact hh
      · rw [if_neg e] at hpos; exact absurd hpos (lt_irrefl _)
    | succ n ih =>
      intro h h' hpos hh
      rw [pow_succ', Matrix.mul_apply] at hpos
      have hex : ∃ h'', 0 < adaptivePlay p h h'' * (adaptivePlay p ^ n) h'' h' := by
        by_contra hn
        push_neg at hn
        exact absurd hpos (not_lt.mpr (Finset.sum_nonpos (fun h'' _ => hn h'')))
      obtain ⟨h'', hpos2⟩ := hex
      have h1 : 0 < adaptivePlay p h h'' :=
        lt_of_le_of_ne (hP0 h h'') (fun e => by rw [← e, zero_mul] at hpos2; exact lt_irrefl _ hpos2)
      have h2 : 0 < (adaptivePlay p ^ n) h'' h' :=
        lt_of_le_of_ne ((hst n).1 h'' h') (fun e => by rw [← e, mul_zero] at hpos2; exact lt_irrefl _ hpos2)
      exact ih h'' h' h2 (yca_yield_step m p hp h h'' hh h1)
  exact key n h h' hpos hh
