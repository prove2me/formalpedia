-- Prove2me | solution 1 for YoungConventions.AdaptivePlay.absorbing_iff_convention
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:20:36.082407+00:00
-- url     : https://prove2.me/submissions/7782bef3-2246-49a2-a088-659d21510023

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReplyDistribution
import Definitions.Def_YoungConventions_AdaptivePlay_adaptivePlay
import Definitions.Def_YoungConventions_AdaptivePlay_IsConvention
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReply

set_option autoImplicit false
open YoungConventions.AdaptivePlay

theorem yca_sample_const {ι : Type*} [DecidableEq ι] {S : ι → Type*} {m : ℕ}
    (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) (K : Finset (Fin m)) (hK : 0 < K.card)
    (i : ι) (x : S i) :
    IsSampleBestReply u (fun _ : Fin m => s) K i x ↔ IsBestReply u i s x := by
  unfold IsSampleBestReply IsBestReply
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hK' : (0 : ℝ) < K.card := by exact_mod_cast hK
  constructor
  · intro hh y
    exact le_of_mul_le_mul_left (hh y) hK'
  · intro hh y
    exact mul_le_mul_of_nonneg_left (hh y) hK'.le

theorem yca_conv_absorb {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (h : History S m) (hc : IsConvention u h) : adaptivePlay p h h = 1 := by
  obtain ⟨s, hs, rfl⟩ := hc
  have hsucc : IsSuccessor (fun _ : Fin m => s) (fun _ => s) := fun t ht => rfl
  have hall : ∀ i, p i (fun _ => s) (s i) = 1 := by
    intro i
    have hzero : ∀ x, x ≠ s i → p i (fun _ => s) x = 0 := by
      intro x hx
      by_contra hne
      have hpos : 0 < p i (fun _ => s) x := lt_of_le_of_ne (hp.1 i _ x) (Ne.symm hne)
      obtain ⟨K, hK, hbest⟩ := (hp.2.2 i _ x).mp hpos
      have hbr := (yca_sample_const u s K (by omega) i x).mp hbest (s i)
      rw [Function.update_eq_self] at hbr
      have h2 := hs i x hx
      linarith
    have hsum := hp.2.1 i (fun _ => s)
    rw [Finset.sum_eq_single (s i) (fun x _ hx => hzero x hx) (by simp)] at hsum
    exact hsum
  unfold adaptivePlay
  rw [if_pos hsucc]
  exact Finset.prod_eq_one (fun i _ => hall i)

theorem yca_absorb_conv {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (h : History S m) (hh : adaptivePlay p h h = 1) : IsConvention u h := by
  have hm : 0 < m := NeZero.pos m
  have hsucc : IsSuccessor h h := by
    by_contra hn
    unfold adaptivePlay at hh
    rw [if_neg hn] at hh
    exact zero_ne_one hh
  have hconst : ∀ n (hn : n < m), h ⟨n, hn⟩ = h ⟨0, hm⟩ := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      rw [← ih (by omega)]
      exact (hsucc ⟨n, by omega⟩ hn).symm
  obtain ⟨s, hheq⟩ : ∃ s : ∀ i, S i, h = fun _ => s :=
    ⟨h ⟨0, hm⟩, funext (fun t => hconst t.val t.isLt)⟩
  subst hheq
  have hprod : ∏ i, p i (fun _ => s) (s i) = 1 := by
    unfold adaptivePlay at hh
    rw [if_pos hsucc] at hh
    exact hh
  have hle1 : ∀ i x, p i (fun _ : Fin m => s) x ≤ 1 := by
    intro i x
    rw [← hp.2.1 i (fun _ => s)]
    exact Finset.single_le_sum (f := fun x => p i (fun _ : Fin m => s) x)
      (fun y _ => hp.1 i _ y) (Finset.mem_univ x)
  have hone : ∀ j, p j (fun _ : Fin m => s) (s j) = 1 := by
    intro j
    have h1 := (Finset.mul_prod_erase Finset.univ (fun i => p i (fun _ : Fin m => s) (s i))
      (Finset.mem_univ j))
    have h2 : ∏ i ∈ Finset.univ.erase j, p i (fun _ : Fin m => s) (s i) ≤ 1 :=
      Finset.prod_le_one (fun i _ => hp.1 i _ _) (fun i _ => hle1 i _)
    have h3 : 0 ≤ ∏ i ∈ Finset.univ.erase j, p i (fun _ : Fin m => s) (s i) :=
      Finset.prod_nonneg (fun i _ => hp.1 i _ _)
    have h4 := hp.1 j (fun _ : Fin m => s) (s j)
    have h5 := hle1 j (s j)
    rw [hprod] at h1
    nlinarith
  have hzero : ∀ i y, y ≠ s i → p i (fun _ : Fin m => s) y = 0 := by
    intro i y hy
    have hsum := hp.2.1 i (fun _ => s)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (s i)), hone i] at hsum
    have h0 : ∑ x ∈ Finset.univ.erase (s i), p i (fun _ : Fin m => s) x = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hp.1 i _ x)).mp h0 y
      (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ _⟩)
  refine ⟨s, ?_, rfl⟩
  intro i y hy
  -- s i is a best reply to s
  obtain ⟨K0, -, hK0⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin m))) (n := k)
    (by simpa using hkm)
  have hbr : IsBestReply u i s (s i) := by
    have hpos : 0 < p i (fun _ : Fin m => s) (s i) := by rw [hone i]; norm_num
    obtain ⟨K, hK, hbest⟩ := (hp.2.2 i _ (s i)).mp hpos
    exact (yca_sample_const u s K (by omega) i (s i)).mp hbest
  have hnot : ¬ IsSampleBestReply u (fun _ : Fin m => s) K0 i y := by
    intro hb
    have := (hp.2.2 i (fun _ => s) y).mpr ⟨K0, hK0, hb⟩
    rw [hzero i y hy] at this
    exact lt_irrefl _ this
  rw [yca_sample_const u s K0 (by omega) i y] at hnot
  unfold IsBestReply at hnot
  push_neg at hnot
  obtain ⟨z, hz⟩ := hnot
  have h3 := hbr z
  rw [Function.update_eq_self] at h3
  linarith

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

theorem yca_pow_diag {H : Type*} [Fintype H] [DecidableEq H] (A : Matrix H H ℝ)
    (h0 : ∀ a b, 0 ≤ A a b) (h1 : ∀ a, ∑ b, A a b = 1) (a : H) (ha : A a a = 1) :
    ∀ n : ℕ, (A ^ n) a a = 1 := by
  have hz : ∀ b, b ≠ a → A a b = 0 := by
    intro b hb
    have hsum := h1 a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ha] at hsum
    have : ∑ x ∈ Finset.univ.erase a, A a x = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => h0 a x)).mp this b
      (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩)
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply, Finset.sum_eq_single a (fun b _ hb => by rw [hz b hb, zero_mul])
      (by simp), ha, ih, one_mul]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : k ≤ m)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (h : History S m) :
    adaptivePlay p h h = 1 ↔ IsConvention u h :=
  ⟨yca_absorb_conv u k m hk hkm p hp h, yca_conv_absorb u k m hk p hp h⟩
