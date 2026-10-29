-- Prove2me | solution 1 for TailOptCaching.ETLRU.value_etlru_eq_optValue
-- status  : ACCEPTED   (prove)
-- author  : @rgmohan
-- created : 2026-10-29T05:56:35.482132+00:00
-- url     : https://prove2.me/submissions/159b43b9-ce17-4274-84ec-ea125417088e

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model
import Theorems.Thm_TailOptCaching_ETLRU_next_turn_expected_TEL
import Theorems.Thm_TailOptCaching_ETLRU_optValue_le_value

/-!
# ET-LRU attains the finite-horizon Bellman optimum

Self-derived proof (it does not use the paper's exchange step, which is false in general).

* **Token decomposition.** For real `c` and `X : ℕ`,
  `(c − X)⁺ + Σ_{x<X} clamp(c − x, 0, 1) = c⁺`. Hence the `x`-th cached token of conversation `i`
  (0-indexed) carries the value `tok i L x = E[clamp(L + Q_i − ξ − x, 0, 1)] ∈ [0, 1]`, and
  `nextTEL z + K z = Base z`, where `K z` sums the keys `λ_i · tok` of cached tokens and `Base z`
  depends only on `(n, λ, L)`, which every policy shares.
* **Dominance invariant `Dom`.** Couple ET-LRU (state `zG`) with any policy (state `zπ`) on the
  same exogenous path. Every token held by `zπ` but not `zG` has key at most every `zG` token,
  and is worth `0` when `zG` has a free slot. This implies `nextTEL zG ≤ nextTEL zπ`, and it is
  preserved by one step: decay scales every key by the same factor, and the arriving
  conversation's tokens are replaced by fresh tokens whose keys are at least as large.
* **Induction** on the horizon, using the proved milestone `next_turn_expected_TEL` to compare
  stage costs, gives `value σ ≤ optValue`; the proved milestone `optValue_le_value` gives `≥`.
-/

open scoped ENNReal
open MeasureTheory

namespace TailOptCaching.ETLRU
namespace ETLRUProof

/-! ## A. Token decomposition -/

/-- Clamp a real number to `[0, 1]`. -/
noncomputable def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

lemma clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

lemma clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma clamp01_mono : Monotone clamp01 := fun _ _ h =>
  max_le_max le_rfl (min_le_min le_rfl h)

/-- One-token step: `(c − 1)⁺ + clamp(c) = c⁺` in `ℝ≥0∞`. -/
lemma ofReal_step (c : ℝ) :
    ENNReal.ofReal (c - 1) + ENNReal.ofReal (clamp01 c) = ENNReal.ofReal c := by
  rcases le_total c 0 with h | h
  · have h1 : clamp01 c = 0 := by
      unfold clamp01; exact max_eq_left (le_trans (min_le_right _ _) h)
    rw [h1, ENNReal.ofReal_of_nonpos (by linarith), ENNReal.ofReal_of_nonpos h,
      ENNReal.ofReal_zero, add_zero]
  rcases le_total c 1 with h' | h'
  · have h1 : clamp01 c = c := by
      unfold clamp01; rw [min_eq_right h']; exact max_eq_right h
    rw [h1, ENNReal.ofReal_of_nonpos (by linarith), zero_add]
  · have h1 : clamp01 c = 1 := by
      unfold clamp01; rw [min_eq_left h']; exact max_eq_right zero_le_one
    rw [h1, ← ENNReal.ofReal_add (by linarith) zero_le_one]
    congr 1; ring

/-- Token identity: `(c − X)⁺ + Σ_{x<X} clamp(c − x) = c⁺`. -/
lemma ofReal_tokens (c : ℝ) : ∀ X : ℕ,
    ENNReal.ofReal (c - X) + ∑ x ∈ Finset.range X, ENNReal.ofReal (clamp01 (c - x)) =
      ENNReal.ofReal c
  | 0 => by simp
  | X + 1 => by
    rw [Finset.sum_range_succ, ← ofReal_tokens c X, ← ofReal_step (c - X)]
    have : c - ((X + 1 : ℕ) : ℝ) = c - X - 1 := by push_cast; ring
    rw [this]; ring

variable (P : Params)

/-- Value of the `x`-th (0-indexed) cached token of conversation `i` with length `L`. -/
noncomputable def tok (i L x : ℕ) : ℝ≥0∞ :=
  ∑' Q : ℕ, P.Qlaw i Q * ENNReal.ofReal (clamp01 ((L : ℝ) + Q - P.ξ - x))

/-- Expected tail excess of conversation `i` with length `L` and `X` cached tokens. -/
noncomputable def Ex (i L X : ℕ) : ℝ≥0∞ :=
  ∑' Q : ℕ, P.Qlaw i Q * ENNReal.ofReal ((L : ℝ) + Q - X - P.ξ)

lemma Ex_add_tok (i L X : ℕ) :
    Ex P i L X + ∑ x ∈ Finset.range X, tok P i L x = Ex P i L 0 := by
  unfold Ex tok
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_add]
  congr 1; funext Q
  rw [← Finset.mul_sum, ← mul_add]
  have h1 : ((L : ℝ) + Q - ((0 : ℕ) : ℝ) - P.ξ) = (L : ℝ) + Q - P.ξ := by push_cast; ring
  have h2 : ((L : ℝ) + Q - X - P.ξ) = (L : ℝ) + Q - P.ξ - X := by ring
  rw [h1, h2, ofReal_tokens]

lemma tok_le_one (i L x : ℕ) : tok P i L x ≤ 1 := by
  unfold tok
  calc ∑' Q : ℕ, P.Qlaw i Q * ENNReal.ofReal (clamp01 ((L : ℝ) + Q - P.ξ - x))
      ≤ ∑' Q : ℕ, P.Qlaw i Q := by
        refine ENNReal.tsum_le_tsum fun Q => ?_
        calc P.Qlaw i Q * ENNReal.ofReal (clamp01 _) ≤ P.Qlaw i Q * 1 := by
              gcongr; exact ENNReal.ofReal_le_one.2 (clamp01_le_one _)
          _ = P.Qlaw i Q := mul_one _
    _ = 1 := (P.Qlaw i).tsum_coe

lemma tok_ne_top (i L x : ℕ) : tok P i L x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (tok_le_one P i L x)

/-- Tokens deeper in the cache are worth less. -/
lemma tok_anti (i L : ℕ) {x x' : ℕ} (h : x ≤ x') : tok P i L x' ≤ tok P i L x := by
  unfold tok
  refine ENNReal.tsum_le_tsum fun Q => ?_
  gcongr
  apply clamp01_mono
  have : (x : ℝ) ≤ x' := by exact_mod_cast h
  linarith

/-- Longer conversations make every token worth more. -/
lemma tok_mono_L (i x : ℕ) {L L' : ℕ} (h : L ≤ L') : tok P i L x ≤ tok P i L' x := by
  unfold tok
  refine ENNReal.tsum_le_tsum fun Q => ?_
  gcongr
  apply clamp01_mono
  have : (L : ℝ) ≤ L' := by exact_mod_cast h
  linarith

/-! ## B. Keys, the identity `nextTEL + K = Base`, and the counting argument -/

/-- Key of token `x` of conversation `i` in state `z`: `λ_i · tok`. -/
noncomputable def key (z : State) (i x : ℕ) : ℝ≥0∞ := ENNReal.ofReal (z.lam i) * tok P i (z.L i) x

/-- Total key of the cached tokens. -/
noncomputable def K (z : State) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range z.n, ∑ x ∈ Finset.range (z.X i), key P z i x

/-- Policy-independent part of `nextTEL`: the value with an empty cache. -/
noncomputable def Base (z : State) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range z.n, ENNReal.ofReal (z.lam i) * Ex P i (z.L i) 0

lemma key_ne_top (z : State) (i x : ℕ) : key P z i x ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top (tok_ne_top P _ _ _)

lemma K_ne_top (z : State) : K P z ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun i _ => ENNReal.sum_ne_top.2 fun x _ => key_ne_top P z i x

lemma nextTEL_add_K (z : State) : nextTEL P z + K P z = Base P z := by
  unfold nextTEL K Base key
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, ← mul_add]
  congr 1
  exact Ex_add_tok P i (z.L i) (z.X i)

/-- Truncated-subtraction bookkeeping: if `Σ a ≤ Σ b` then `Σ (a − b) ≤ Σ (b − a)`. -/
lemma sum_tsub_le {n : ℕ} (a b : ℕ → ℕ)
    (h : ∑ i ∈ Finset.range n, a i ≤ ∑ i ∈ Finset.range n, b i) :
    ∑ i ∈ Finset.range n, (a i - b i) ≤ ∑ i ∈ Finset.range n, (b i - a i) := by
  have key : ∑ i ∈ Finset.range n, (a i - b i) + ∑ i ∈ Finset.range n, b i =
      ∑ i ∈ Finset.range n, (b i - a i) + ∑ i ∈ Finset.range n, a i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by omega
  omega

/-- Per-conversation inequality, for a threshold `t` separating the two kinds of tokens. -/
lemma per_conv (k : ℕ → ℝ≥0∞) (t : ℝ≥0∞) (XG Xp : ℕ)
    (hG : ∀ y < XG, t ≤ k y) (hp : ∀ x, XG ≤ x → x < Xp → k x ≤ t) :
    ∑ x ∈ Finset.range Xp, k x + ((XG - Xp : ℕ) : ℝ≥0∞) * t ≤
      ∑ x ∈ Finset.range XG, k x + ((Xp - XG : ℕ) : ℝ≥0∞) * t := by
  rcases le_total Xp XG with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, zero_mul, add_zero,
      ← Finset.sum_range_add_sum_Ico _ h]
    gcongr
    calc ((XG - Xp : ℕ) : ℝ≥0∞) * t = ∑ _x ∈ Finset.Ico Xp XG, t := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ ∑ x ∈ Finset.Ico Xp XG, k x :=
          Finset.sum_le_sum fun x hx => hG x (Finset.mem_Ico.1 hx).2
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, zero_mul, add_zero,
      ← Finset.sum_range_add_sum_Ico _ h]
    gcongr
    calc ∑ x ∈ Finset.Ico XG Xp, k x ≤ ∑ _x ∈ Finset.Ico XG Xp, t :=
          Finset.sum_le_sum fun x hx => hp x (Finset.mem_Ico.1 hx).1 (Finset.mem_Ico.1 hx).2
      _ = ((Xp - XG : ℕ) : ℝ≥0∞) * t := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

/-- Counting argument. If every token held only by `Xp` is worth at most every token of `XG`,
and is worth `0` whenever `XG` has a free slot, and both fit in capacity `C`, then the tokens of
`XG` are worth at least as much in total. -/
lemma sum_keys_le (C n : ℕ) (k : ℕ → ℕ → ℝ≥0∞) (hk : ∀ i x, k i x ≠ ⊤) (XG Xp : ℕ → ℕ)
    (_hGC : ∑ i ∈ Finset.range n, XG i ≤ C) (hpC : ∑ i ∈ Finset.range n, Xp i ≤ C)
    (hdom : ∀ i < n, ∀ x, XG i ≤ x → x < Xp i →
      (∀ j < n, ∀ y < XG j, k i x ≤ k j y) ∧ (∑ j ∈ Finset.range n, XG j < C → k i x = 0)) :
    ∑ i ∈ Finset.range n, ∑ x ∈ Finset.range (Xp i), k i x ≤
      ∑ i ∈ Finset.range n, ∑ x ∈ Finset.range (XG i), k i x := by
  -- Threshold `t`: `0` if `XG` has a free slot, else the largest key held only by `Xp`.
  set S := (Finset.range n).sigma fun i => Finset.Ico (XG i) (Xp i) with hS
  have hmemS : ∀ i x, (⟨i, x⟩ : Σ _ : ℕ, ℕ) ∈ S ↔ i < n ∧ XG i ≤ x ∧ x < Xp i := by
    intro i x; simp [hS, Finset.mem_sigma, Finset.mem_Ico]
  obtain ⟨t, ht, hGt, hpt, hcount⟩ : ∃ t : ℝ≥0∞, t ≠ ⊤ ∧
      (∀ j < n, ∀ y < XG j, t ≤ k j y) ∧ (∀ i < n, ∀ x, XG i ≤ x → x < Xp i → k i x ≤ t) ∧
      (∑ i ∈ Finset.range n, (Xp i - XG i) ≤ ∑ i ∈ Finset.range n, (XG i - Xp i) ∨ t = 0) := by
    by_cases hfree : ∑ j ∈ Finset.range n, XG j < C
    · exact ⟨0, ENNReal.zero_ne_top, fun _ _ _ _ => bot_le,
        fun i hi x h1 h2 => le_of_eq ((hdom i hi x h1 h2).2 hfree), Or.inr rfl⟩
    rcases S.eq_empty_or_nonempty with hE | hne
    · refine ⟨0, ENNReal.zero_ne_top, fun _ _ _ _ => bot_le, fun i hi x h1 h2 => ?_,
        Or.inr rfl⟩
      have : (⟨i, x⟩ : Σ _ : ℕ, ℕ) ∈ S := (hmemS i x).2 ⟨hi, h1, h2⟩
      rw [hE] at this; exact absurd this (Finset.notMem_empty _)
    refine ⟨S.sup' hne fun p => k p.1 p.2, ?_, ?_, ?_, Or.inl ?_⟩
    · exact ne_of_lt ((Finset.sup'_lt_iff hne).2 fun p _ => lt_top_iff_ne_top.2 (hk _ _))
    · intro j hj y hy
      exact Finset.sup'_le hne _ fun p hp => by
        obtain ⟨hpi, hp1, hp2⟩ := (hmemS p.1 p.2).1 hp
        exact (hdom p.1 hpi p.2 hp1 hp2).1 j hj y hy
    · intro i hi x h1 h2
      exact Finset.le_sup' (f := fun p : Σ _ : ℕ, ℕ => k p.1 p.2) ((hmemS i x).2 ⟨hi, h1, h2⟩)
    · exact sum_tsub_le Xp XG (le_trans hpC (not_lt.1 hfree))
  have hsum := Finset.sum_le_sum fun i (hi : i ∈ Finset.range n) =>
    per_conv (k i) t (XG i) (Xp i) (hGt i (Finset.mem_range.1 hi))
      (hpt i (Finset.mem_range.1 hi))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Nat.cast_sum, ← Nat.cast_sum] at hsum
  have hfin : ((∑ i ∈ Finset.range n, (XG i - Xp i) : ℕ) : ℝ≥0∞) * t ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ht
  have hBA : ((∑ i ∈ Finset.range n, (Xp i - XG i) : ℕ) : ℝ≥0∞) * t ≤
      ((∑ i ∈ Finset.range n, (XG i - Xp i) : ℕ) : ℝ≥0∞) * t := by
    rcases hcount with h | h
    · gcongr
    · simp [h]
  exact (ENNReal.add_le_add_iff_right hfin).1 (hsum.trans (add_le_add le_rfl hBA))

/-! ## C. The dominance invariant -/

/-- `Dom zG zπ`: every token held by `zπ` but not by `zG` has key at most every `zG` token, and
is worth `0` when `zG` has a free slot. Keys are read from `zG`; the two states share `λ`, `L`. -/
def Dom (zG zπ : State) : Prop :=
  ∀ i < zG.n, ∀ x, zG.X i ≤ x → x < zπ.X i →
    (∀ j < zG.n, ∀ y < zG.X j, key P zG i x ≤ key P zG j y) ∧
    (∑ j ∈ Finset.range zG.n, zG.X j < P.C → key P zG i x = 0)

lemma dom_refl (z : State) : Dom P z z := fun _ _ _ h1 h2 => absurd h2 (not_lt.2 h1)

/-- Shared exogenous coordinates. -/
def SameExo (zG zπ : State) : Prop := zπ.n = zG.n ∧ zπ.lam = zG.lam ∧ zπ.L = zG.L

lemma key_eq_of_exo {zG zπ : State} (h : SameExo zG zπ) : key P zπ = key P zG := by
  obtain ⟨-, hl, hL⟩ := h
  funext i x; simp only [key, hl, hL]

lemma Base_eq_of_exo {zG zπ : State} (h : SameExo zG zπ) : Base P zπ = Base P zG := by
  obtain ⟨hn, hl, hL⟩ := h
  simp only [Base, hn, hl, hL]

/-- Dominance gives the ET-LRU state the smaller next-turn objective. -/
lemma nextTEL_le_of_dom {zG zπ : State} (hG : WellFormed P zG) (hπ : WellFormed P zπ)
    (hx : SameExo zG zπ) (hd : Dom P zG zπ) : nextTEL P zG ≤ nextTEL P zπ := by
  have hK : K P zπ ≤ K P zG := by
    have hk := key_eq_of_exo P hx
    unfold K
    rw [hk, hx.1]
    refine sum_keys_le P.C zG.n (key P zG) (key_ne_top P zG) zG.X zπ.X hG.2.2.2 ?_ hd
    rw [← hx.1]; exact hπ.2.2.2
  have h1 := nextTEL_add_K P zG
  have h2 := nextTEL_add_K P zπ
  rw [Base_eq_of_exo P hx, ← h1] at h2
  refine (ENNReal.add_le_add_iff_right (K_ne_top P zπ)).1 ?_
  calc nextTEL P zG + K P zπ ≤ nextTEL P zG + K P zG := add_le_add le_rfl hK
    _ = nextTEL P zπ + K P zπ := h2.symm

/-! ## D. Structure of an ET-LRU decision -/

section Decision

variable (s : State) (θ q a : ℕ)

/-- Per-conversation cap on the decision `Y`: the arriving conversation may cache its whole new
length, the others may only keep what they had. -/
def bnd (i : ℕ) : ℕ := if i = θ then s.L θ + q + a else s.X i

lemma feasible_iff (Y : ℕ → ℕ) :
    Feasible P s θ q a Y ↔
      (∀ i, Y i ≤ bnd s θ q a i) ∧ ∑ i ∈ Finset.range (nAfter s θ), Y i ≤ P.C := by
  unfold Feasible bnd
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ?_, h3⟩
    by_cases hi : i = θ
    · subst hi; simpa using h1
    · simpa [hi] using h2 i hi
  · rintro ⟨h1, h3⟩
    refine ⟨by simpa using h1 θ, fun i hi => by simpa [hi] using h1 i, h3⟩

/-- Total key of a cache vector, for a fixed key function. -/
noncomputable def Kf (k : ℕ → ℕ → ℝ≥0∞) (n : ℕ) (Y : ℕ → ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range n, ∑ x ∈ Finset.range (Y i), k i x

lemma K_post (Y : ℕ → ℕ) (YG : ℕ → ℕ) :
    K P (post P s θ q a Y) = Kf (key P (post P s θ q a YG)) (nAfter s θ) Y := rfl

lemma Kf_incr (k : ℕ → ℕ → ℝ≥0∞) (n : ℕ) (Y : ℕ → ℕ) {i : ℕ} (hi : i < n) :
    Kf k n (Function.update Y i (Y i + 1)) = Kf k n Y + k i (Y i) := by
  unfold Kf
  have hpt : ∀ l ∈ Finset.range n,
      ∑ x ∈ Finset.range (Function.update Y i (Y i + 1) l), k l x =
        ∑ x ∈ Finset.range (Y l), k l x + (if l = i then k i (Y i) else 0) := by
    intro l _
    by_cases hl : l = i
    · subst hl; simp [Finset.sum_range_succ]
    · simp [Function.update_of_ne hl, hl]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_range.2 hi)]

lemma Kf_swap (k : ℕ → ℕ → ℝ≥0∞) (n : ℕ) (Y : ℕ → ℕ) {i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) (hYj : 1 ≤ Y j) :
    Kf k n (Function.update (Function.update Y i (Y i + 1)) j (Y j - 1)) + k j (Y j - 1) =
      Kf k n Y + k i (Y i) := by
  unfold Kf
  have hpt : ∀ l ∈ Finset.range n,
      ∑ x ∈ Finset.range (Function.update (Function.update Y i (Y i + 1)) j (Y j - 1) l), k l x
        + (if l = j then k j (Y j - 1) else 0) =
        ∑ x ∈ Finset.range (Y l), k l x + (if l = i then k i (Y i) else 0) := by
    intro l _
    by_cases hlj : l = j
    · subst hlj
      have : Y l = (Y l - 1) + 1 := by omega
      rw [Function.update_self, if_pos rfl, if_neg (Ne.symm hij), add_zero]
      conv_rhs => rw [this, Finset.sum_range_succ]
    · by_cases hli : l = i
      · subst hli; simp [Function.update_of_ne hlj, hlj, Finset.sum_range_succ]
      · simp [Function.update_of_ne hlj, Function.update_of_ne hli, hlj, hli]
  have := Finset.sum_congr rfl hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    if_pos (Finset.mem_range.2 hi), if_pos (Finset.mem_range.2 hj)] at this
  exact this

lemma sum_incr (n : ℕ) (Y : ℕ → ℕ) {i : ℕ} (hi : i < n) :
    ∑ l ∈ Finset.range n, Function.update Y i (Y i + 1) l = ∑ l ∈ Finset.range n, Y l + 1 := by
  have hpt : ∀ l ∈ Finset.range n,
      Function.update Y i (Y i + 1) l = Y l + (if l = i then 1 else 0) := by
    intro l _
    by_cases hl : l = i
    · subst hl; simp
    · simp [Function.update_of_ne hl, hl]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_range.2 hi)]

lemma sum_swap (n : ℕ) (Y : ℕ → ℕ) {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j)
    (hYj : 1 ≤ Y j) :
    ∑ l ∈ Finset.range n, Function.update (Function.update Y i (Y i + 1)) j (Y j - 1) l =
      ∑ l ∈ Finset.range n, Y l := by
  have hpt : ∀ l ∈ Finset.range n,
      Function.update (Function.update Y i (Y i + 1)) j (Y j - 1) l + (if l = j then 1 else 0) =
        Y l + (if l = i then 1 else 0) := by
    intro l _
    by_cases hlj : l = j
    · subst hlj; simp [Ne.symm hij]; omega
    · by_cases hli : l = i
      · subst hli; simp [Function.update_of_ne hlj, hlj]
      · simp [Function.update_of_ne hlj, Function.update_of_ne hli, hlj, hli]
  have := Finset.sum_congr rfl hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    if_pos (Finset.mem_range.2 hi), if_pos (Finset.mem_range.2 hj)] at this
  omega

lemma key_anti (z : State) (i : ℕ) {x x' : ℕ} (h : x ≤ x') : key P z i x' ≤ key P z i x :=
  mul_le_mul_right (tok_anti P i _ h) _

variable {s θ q a}
variable (YG : ℕ → ℕ) (hfe : Feasible P s θ q a YG)
  (hmin : ∀ Y, Feasible P s θ q a Y →
    nextTEL P (post P s θ q a YG) ≤ nextTEL P (post P s θ q a Y))
  (hB : Base P (post P s θ q a YG) ≠ ⊤)

include hmin hB in
/-- No feasible decision has a strictly larger total key than the ET-LRU decision. -/
lemma no_better {Y : ℕ → ℕ} (hY : Feasible P s θ q a Y) :
    ¬ K P (post P s θ q a YG) < K P (post P s θ q a Y) := by
  intro hlt
  have h1 := nextTEL_add_K P (post P s θ q a YG)
  have h2 := nextTEL_add_K P (post P s θ q a Y)
  have hBe : Base P (post P s θ q a Y) = Base P (post P s θ q a YG) := rfl
  have hnt : nextTEL P (post P s θ q a YG) ≠ ⊤ :=
    ne_top_of_le_ne_top hB (h1 ▸ le_self_add)
  have := ENNReal.add_lt_add_of_le_of_lt hnt (hmin Y hY) hlt
  rw [h1, h2, hBe] at this
  exact lt_irrefl _ this

include hfe hmin hB in
/-- (E1) A token ET-LRU could keep but drops is worth at most every token it keeps. -/
lemma dropped_le_kept {i x j y : ℕ} (hi : i < nAfter s θ) (hx1 : YG i ≤ x)
    (hx2 : x < bnd s θ q a i) (hj : j < nAfter s θ) (hy : y < YG j) :
    key P (post P s θ q a YG) i x ≤ key P (post P s θ q a YG) j y := by
  set k := key P (post P s θ q a YG) with hk
  by_contra hlt
  push Not at hlt
  have hlt' : k j (YG j - 1) < k i (YG i) :=
    lt_of_le_of_lt (key_anti P _ j (by omega)) (lt_of_lt_of_le hlt (key_anti P _ i hx1))
  have hij : i ≠ j := by
    rintro rfl
    exact absurd hlt' (not_lt.2 (key_anti P _ i (Nat.sub_le _ _)))
  have hfe' := (feasible_iff P s θ q a YG).1 hfe
  set Y' := Function.update (Function.update YG i (YG i + 1)) j (YG j - 1) with hY'
  have hY'f : Feasible P s θ q a Y' := by
    refine (feasible_iff P s θ q a Y').2 ⟨fun l => ?_, ?_⟩
    · by_cases hlj : l = j
      · subst hlj; simp only [hY', Function.update_self]
        exact le_trans (Nat.sub_le _ _) (hfe'.1 l)
      · by_cases hli : l = i
        · subst hli; simp only [hY', Function.update_of_ne hlj, Function.update_self]; omega
        · simp only [hY', Function.update_of_ne hlj, Function.update_of_ne hli]; exact hfe'.1 l
    · rw [hY', sum_swap _ YG hi hj hij (by omega)]; exact hfe'.2
  apply no_better P YG hmin hB hY'f
  rw [K_post P s θ q a Y' YG, K_post P s θ q a YG YG]
  have hsw := Kf_swap k (nAfter s θ) YG hi hj hij (by omega)
  have hne : Kf k (nAfter s θ) Y' ≠ ⊤ := by
    rw [← K_post P s θ q a Y' YG]; exact K_ne_top P _
  have : Kf k (nAfter s θ) YG + k i (YG i) < Kf k (nAfter s θ) Y' + k i (YG i) := by
    rw [← hsw]; exact ENNReal.add_lt_add_left hne hlt'
  exact lt_of_add_lt_add_right this

include hfe hmin hB in
/-- (E2) With a free slot, every token ET-LRU could keep but drops is worth `0`. -/
lemma dropped_zero_of_free (hfree : ∑ l ∈ Finset.range (nAfter s θ), YG l < P.C) {i x : ℕ}
    (hi : i < nAfter s θ) (hx1 : YG i ≤ x) (hx2 : x < bnd s θ q a i) :
    key P (post P s θ q a YG) i x = 0 := by
  set k := key P (post P s θ q a YG) with hk
  by_contra hne0
  have hpos : k i (YG i) ≠ 0 := fun h0 => hne0 (le_antisymm (h0 ▸ key_anti P _ i hx1) bot_le)
  have hfe' := (feasible_iff P s θ q a YG).1 hfe
  set Y' := Function.update YG i (YG i + 1) with hY'
  have hY'f : Feasible P s θ q a Y' := by
    refine (feasible_iff P s θ q a Y').2 ⟨fun l => ?_, ?_⟩
    · by_cases hli : l = i
      · subst hli; simp only [hY', Function.update_self]; omega
      · simp only [hY', Function.update_of_ne hli]; exact hfe'.1 l
    · rw [hY', sum_incr _ YG hi]; omega
  apply no_better P YG hmin hB hY'f
  rw [K_post P s θ q a Y' YG, K_post P s θ q a YG YG, hY', Kf_incr k _ YG hi]
  have hne : Kf k (nAfter s θ) YG ≠ ⊤ := by
    rw [← K_post P s θ q a YG YG]; exact K_ne_top P _
  exact ENNReal.lt_add_right hne hpos

include hfe hmin hB in
/-- (Count) If at least `C` available tokens are worth at least `κ > 0`, then every token kept
by ET-LRU is worth at least `κ`, and its cache is full. -/
lemma kept_ge_of_count (κ : ℝ≥0∞) (hκ : κ ≠ 0) (A : ℕ → ℕ)
    (hA : ∀ j < nAfter s θ, A j ≤ bnd s θ q a j)
    (hAk : ∀ j < nAfter s θ, ∀ y < A j, κ ≤ key P (post P s θ q a YG) j y)
    (hC : P.C ≤ ∑ j ∈ Finset.range (nAfter s θ), A j) :
    (∀ j < nAfter s θ, ∀ y < YG j, κ ≤ key P (post P s θ q a YG) j y) ∧
      P.C ≤ ∑ j ∈ Finset.range (nAfter s θ), YG j := by
  have hfe' := (feasible_iff P s θ q a YG).1 hfe
  constructor
  · intro j0 hj0 y0 hy0
    by_contra hlt
    push Not at hlt
    have hAY : ∀ j ∈ Finset.range (nAfter s θ), A j ≤ YG j := by
      intro j hj
      have hj := Finset.mem_range.1 hj
      by_contra hc
      push Not at hc
      have e1 := dropped_le_kept P YG hfe hmin hB hj le_rfl (lt_of_lt_of_le hc (hA j hj)) hj0 hy0
      exact absurd (lt_of_le_of_lt e1 hlt) (not_lt.2 (hAk j hj (YG j) hc))
    have hA0 : A j0 < YG j0 := by
      by_contra hc
      push Not at hc
      exact absurd (hAk j0 hj0 y0 (by omega)) (not_le.2 hlt)
    have := Finset.sum_lt_sum hAY ⟨j0, Finset.mem_range.2 hj0, hA0⟩
    omega
  · by_contra hfree
    push Not at hfree
    have hAY : ∀ j ∈ Finset.range (nAfter s θ), A j ≤ YG j := by
      intro j hj
      have hj := Finset.mem_range.1 hj
      by_contra hc
      push Not at hc
      have e2 := dropped_zero_of_free P YG hfe hmin hB hfree hj le_rfl
        (lt_of_lt_of_le hc (hA j hj))
      exact hκ (le_antisymm (e2 ▸ hAk j hj (YG j) hc) bot_le)
    have := Finset.sum_le_sum hAY
    omega

end Decision

/-! ## E. One step of the coupled dynamics preserves the invariant -/

lemma wf_post {z : State} (hz : WellFormed P z) {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1)
    {θ q a : ℕ} (hθ : θ ≤ z.n) {Y : ℕ → ℕ} (hY : Feasible P (decay d z) θ q a Y) :
    WellFormed P (post P (decay d z) θ q a Y) := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  obtain ⟨f1, f2, f3⟩ := hY
  simp only [WellFormed, post, decay, nAfter] at *
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i => ?_, f3⟩
  · by_cases hiθ : i = θ
    · subst hiθ; simp [P.lamBar_pos i]
    · have hin : i < z.n := by omega
      obtain ⟨l0, l1⟩ := h1 i hin
      simp only [Function.update_of_ne hiθ]
      exact ⟨mul_pos hd0 l0, le_trans (mul_le_of_le_one_left l0.le hd1) l1⟩
  · have hiθ : i ≠ θ := by omega
    obtain ⟨e1, e2, e3⟩ := h2 i (by omega)
    simp only [Function.update_of_ne hiθ, e1, e2, mul_zero, true_and]
    have := f2 i hiθ; omega
  · by_cases hiθ : i = θ
    · subst hiθ; simpa using f1
    · simp only [Function.update_of_ne hiθ]; exact le_trans (f2 i hiθ) (h3 i)

lemma key_post_ne (z : State) {d : ℝ} (hd0 : 0 < d) {θ q a i : ℕ} (hi : i ≠ θ) (Y : ℕ → ℕ)
    (x : ℕ) :
    key P (post P (decay d z) θ q a Y) i x = ENNReal.ofReal d * key P z i x := by
  simp only [key, post, decay, Function.update_of_ne hi, ENNReal.ofReal_mul hd0.le, mul_assoc]

lemma key_le_post_self {z : State} (hz : WellFormed P z) (d : ℝ) {θ : ℕ} (q a : ℕ)
    (Y : ℕ → ℕ) (y : ℕ) :
    key P z θ y ≤ key P (post P (decay d z) θ q a Y) θ y := by
  simp only [key, post, decay, Function.update_self]
  have hlam : z.lam θ ≤ P.lamBar θ := by
    by_cases h : θ < z.n
    · exact (hz.1 θ h).2
    · rw [(hz.2.1 θ (not_lt.1 h)).1]; exact (P.lamBar_pos θ).le
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hlam) (tok_mono_L P θ y (by omega))

/-- The invariant survives one coupled step (decay `d`, arrival `θ` with `q`, `a`), when ET-LRU
chooses `YG` and the other policy chooses any feasible `YP`. -/
lemma dom_post {zG zπ : State} (hG : WellFormed P zG) (hπ : WellFormed P zπ)
    (hx : SameExo zG zπ) (hD : Dom P zG zπ) {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1)
    {θ q a : ℕ} {YG YP : ℕ → ℕ} (hfe : Feasible P (decay d zG) θ q a YG)
    (hmin : ∀ Y, Feasible P (decay d zG) θ q a Y →
      nextTEL P (post P (decay d zG) θ q a YG) ≤ nextTEL P (post P (decay d zG) θ q a Y))
    (hB : Base P (post P (decay d zG) θ q a YG) ≠ ⊤)
    (hYP : Feasible P (decay d zπ) θ q a YP) :
    Dom P (post P (decay d zG) θ q a YG) (post P (decay d zπ) θ q a YP) := by
  obtain ⟨hn, hlam, hL⟩ := hx
  intro i hi x hx1 hx2
  change i < nAfter (decay d zG) θ at hi
  change YG i ≤ x at hx1
  change x < YP i at hx2
  change (∀ j < nAfter (decay d zG) θ, ∀ y < YG j,
      key P (post P (decay d zG) θ q a YG) i x ≤ key P (post P (decay d zG) θ q a YG) j y) ∧
    (∑ j ∈ Finset.range (nAfter (decay d zG) θ), YG j < P.C →
      key P (post P (decay d zG) θ q a YG) i x = 0)
  obtain ⟨p1, p2, -⟩ := hYP
  have hLθ : YP θ ≤ zG.L θ + q + a := by
    have : (decay d zπ).L θ = zG.L θ := by simp [decay, hL]
    omega
  by_cases hav : i = θ ∨ x < zG.X i
  · -- The token was available to ET-LRU, which dropped it.
    have hb : x < bnd (decay d zG) θ q a i := by
      unfold bnd
      split_ifs with hiθ
      · subst hiθ; show x < zG.L i + q + a; omega
      · rcases hav with h | h
        · exact absurd h hiθ
        · exact h
    exact ⟨fun j hj y hy => dropped_le_kept P YG hfe hmin hB hi hx1 hb hj hy,
      fun hfree => dropped_zero_of_free P YG hfe hmin hB hfree hi hx1 hb⟩
  · -- The token was already held only by the other policy before this step.
    push Not at hav
    obtain ⟨hiθ, hle⟩ := hav
    have hYPi : YP i ≤ zπ.X i := p2 i hiθ
    have hin : i < zG.n := by
      by_contra hc
      have := (hπ.2.1 i (by rw [hn]; omega)).2.2
      omega
    have hDi := hD i hin x hle (by omega)
    set k' := key P (post P (decay d zG) θ q a YG) with hk'
    have hκ : k' i x = ENNReal.ofReal d * key P zG i x := key_post_ne P zG hd0 hiθ YG x
    by_cases hz : k' i x = 0
    · exact ⟨fun _ _ _ _ => hz ▸ bot_le, fun _ => hz⟩
    have hkey : key P zG i x ≠ 0 := fun h0 => hz (by rw [hκ, h0, mul_zero])
    have hfull : P.C ≤ ∑ j ∈ Finset.range zG.n, zG.X j := by
      by_contra hc; exact hkey (hDi.2 (not_le.1 hc))
    have hnn : zG.n ≤ nAfter (decay d zG) θ := by simp [nAfter, decay]
    have hcnt := kept_ge_of_count P YG hfe hmin hB (k' i x) hz zG.X
      (fun j _ => by
        unfold bnd
        split_ifs with hj
        · subst hj; show zG.X j ≤ zG.L j + q + a; have := hG.2.2.1 j; omega
        · exact le_rfl)
      (fun j _ y hy => by
        have hjn : j < zG.n := by
          by_contra hc; have := (hG.2.1 j (not_lt.1 hc)).2.2; omega
        have hij := hDi.1 j hjn y hy
        by_cases hjθ : j = θ
        · subst hjθ
          calc k' i x = ENNReal.ofReal d * key P zG i x := hκ
            _ ≤ key P zG i x := mul_le_of_le_one_left' (ENNReal.ofReal_le_one.2 hd1)
            _ ≤ key P zG j y := hij
            _ ≤ k' j y := key_le_post_self P hG d q a YG y
        · rw [hκ, key_post_ne P zG hd0 hjθ YG y]
          exact mul_le_mul_right hij _)
      (le_trans hfull (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hnn)))
    exact ⟨fun j hj y hy => hcnt.1 j hj y hy, fun hfree => absurd hcnt.2 (not_le.2 hfree)⟩

/-! ## F. Comparing one stage, and the induction -/

lemma ae_Ioc (r : ℕ → ℝ) : ∀ᵐ d ∂(P.decayLaw r), d ∈ Set.Ioc (0 : ℝ) 1 := by
  rw [ae_iff]; exact P.decayLaw_mem r

lemma arrivalExp_add (s : State) (F G : ℕ → ℕ → ℕ → ℝ≥0∞) :
    arrivalExp P s (fun θ q a => F θ q a + G θ q a) = arrivalExp P s F + arrivalExp P s G := by
  simp only [arrivalExp, mul_add, ENNReal.tsum_add, Finset.sum_add_distrib]

lemma arrivalExp_mono (s : State) {F G : ℕ → ℕ → ℕ → ℝ≥0∞}
    (h : ∀ θ, θ ≤ s.n → ∀ q a, F θ q a ≤ G θ q a) : arrivalExp P s F ≤ arrivalExp P s G := by
  unfold arrivalExp
  refine Finset.sum_le_sum fun θ hθ => mul_le_mul_right (ENNReal.tsum_le_tsum fun q =>
    mul_le_mul_right (ENNReal.tsum_le_tsum fun a => mul_le_mul_right ?_ _) _) _
  exact h θ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hθ)) q a

lemma arrivalExp_congr {s s' : State} (hn : s.n = s'.n) (hl : s.lam = s'.lam)
    (F : ℕ → ℕ → ℕ → ℝ≥0∞) : arrivalExp P s F = arrivalExp P s' F := by
  simp only [arrivalExp, arrivalProb, hn, hl]

/-- Expected stage cost of the next arrival: ET-LRU's state is no worse. -/
lemma stage_le {zG zπ : State} (hG : WellFormed P zG) (hπ : WellFormed P zπ)
    (hx : SameExo zG zπ) (hD : Dom P zG zπ) {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    arrivalExp P (decay d zG) (fun θ q _ => stageCost P (decay d zG) θ q) ≤
      arrivalExp P (decay d zπ) (fun θ q _ => stageCost P (decay d zπ) θ q) := by
  have eG := next_turn_expected_TEL P zG hG d hd0 hd1
  have eπ := next_turn_expected_TEL P zπ hπ d hd0 hd1
  obtain ⟨hn, hlam, hL⟩ := hx
  rw [hn, hlam] at eπ
  set c := ENNReal.ofReal (P.lamConv + d * ∑ i ∈ Finset.range zG.n, zG.lam i) with hc
  have hsum : 0 ≤ ∑ i ∈ Finset.range zG.n, zG.lam i :=
    Finset.sum_nonneg fun i hi => (hG.1 i (Finset.mem_range.1 hi)).1.le
  have hc0 : c ≠ 0 := by
    rw [hc]; exact (ENNReal.ofReal_pos.2 (by nlinarith [P.lamConv_pos])).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  refine (ENNReal.mul_le_mul_iff_left hc0 hctop).1 ?_
  rw [eG, eπ]
  gcongr
  exact nextTEL_le_of_dom P hG hπ ⟨hn, hlam, hL⟩ hD

/-- If the empty-cache baseline is infinite, every policy's value is infinite. -/
lemma optValue_top {z : State} (hz : WellFormed P z) (hT : Base P z = ⊤) (r : ℕ) :
    optValue P (r + 1) z = ⊤ := by
  have hnt : nextTEL P z = ⊤ := by
    by_contra h
    exact (ENNReal.add_ne_top.2 ⟨h, K_ne_top P z⟩) (nextTEL_add_K P z ▸ hT)
  haveI := P.decayLaw_prob z.lam
  rw [optValue, eq_top_iff]
  calc (⊤ : ℝ≥0∞) = ∫⁻ _, ⊤ ∂(P.decayLaw z.lam) := by simp [lintegral_const, measure_univ]
    _ ≤ _ := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_Ioc P z.lam] with d hd
      obtain ⟨hd0, hd1⟩ := hd
      have e := next_turn_expected_TEL P z hz d hd0 hd1
      rw [hnt, ENNReal.mul_top (ENNReal.ofReal_pos.2 hd0).ne', top_add] at e
      have hA : arrivalExp P (decay d z) (fun θ q _ => stageCost P (decay d z) θ q) = ⊤ := by
        rcases ENNReal.mul_eq_top.1 e with ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd h ENNReal.ofReal_ne_top
        · exact h
      rw [arrivalExp_add, hA, top_add]

/-- Main induction: under the invariant, ET-LRU's value is at most the Bellman optimum. -/
theorem value_le_optValue_of_inv (σ : Policy) (hσ : IsETLRU P σ) (r : ℕ) :
    ∀ (k : ℕ) (zG zπ : State), WellFormed P zG → WellFormed P zπ → SameExo zG zπ →
      (Dom P zG zπ ∨ Base P zπ = ⊤) → value P σ r k zG ≤ optValue P r zπ := by
  induction r with
  | zero => intro k zG zπ _ _ _ _; simp [value, optValue]
  | succ r ih =>
    intro k zG zπ hG hπ hx hinv
    rcases hinv with hD | hT
    swap
    · rw [optValue_top P hπ hT r]; exact le_top
    rw [value, optValue, hx.2.1]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_Ioc P zG.lam] with d hd
    obtain ⟨hd0, hd1⟩ := hd
    rw [arrivalExp_add, arrivalExp_add]
    refine add_le_add (stage_le P hG hπ hx hD hd0 hd1) ?_
    have hn' : (decay d zG).n = (decay d zπ).n := hx.1.symm
    have hl' : (decay d zG).lam = (decay d zπ).lam := by simp [decay, hx.2.1]
    rw [arrivalExp_congr P hn' hl']
    refine arrivalExp_mono P _ fun θ hθ q a => ?_
    have hθG : θ ≤ (decay d zG).n := hn' ▸ hθ
    obtain ⟨hfe, hmin⟩ := hσ k (decay d zG) θ q a hθG
    refine le_iInf₂ fun Y hY => ih (k + 1) _ _ (wf_post P hG hd0 hd1 hθG hfe)
      (wf_post P hπ hd0 hd1 hθ hY) ?_ ?_
    · refine ⟨?_, ?_, ?_⟩
      · simp [post, nAfter, decay, hx.1]
      · simp [post, decay, hx.2.1]
      · simp [post, decay, hx.2.2]
    · by_cases hT : Base P (post P (decay d zπ) θ q a Y) = ⊤
      · exact Or.inr hT
      · refine Or.inl (dom_post P hG hπ hx hD hd0 hd1 hfe hmin ?_ hY)
        have hxp : SameExo (post P (decay d zG) θ q a (σ k (decay d zG) θ q a))
            (post P (decay d zπ) θ q a Y) :=
          ⟨by simp [post, nAfter, decay, hx.1], by simp [post, decay, hx.2.1],
            by simp [post, decay, hx.2.2]⟩
        rwa [← Base_eq_of_exo P hxp]

theorem value_le_optValue (σ : Policy) (hσ : IsETLRU P σ) (M k : ℕ) (z : State)
    (hz : WellFormed P z) : value P σ M k z ≤ optValue P M z :=
  value_le_optValue_of_inv P σ hσ M k z z hz hz ⟨rfl, rfl, rfl⟩ (Or.inl (dom_refl P z))

end ETLRUProof
end TailOptCaching.ETLRU

open TailOptCaching.ETLRU in
theorem solution (P : Params) (σ : Policy) (hσ : IsETLRU P σ) (M k : ℕ)
    (z : State) (hz : WellFormed P z) :
    value P σ M k z = optValue P M z :=
  le_antisymm (ETLRUProof.value_le_optValue P σ hσ M k z hz)
    (optValue_le_value P σ (fun k s θ q a h => (hσ k s θ q a h).1) M k z)
