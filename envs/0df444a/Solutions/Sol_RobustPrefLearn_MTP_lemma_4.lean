-- Prove2me | solution 1 for RobustPrefLearn.MTP.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T15:00:34.552499+00:00
-- url     : https://prove2.me/submissions/609d78d9-56d5-4147-af3e-85dc7a8ce61b

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp

open scoped ENNReal

namespace MTPAux10
open RobustPrefLearn.MTP

lemma rank_ge_one {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X : Fin K) (hX : X ∈ S.1) :
    1 ≤ relRank τ S X :=
  Finset.card_pos.2 ⟨X, Finset.mem_filter.2 ⟨hX, le_rfl⟩⟩

lemma rank_le_card {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X : Fin K) :
    relRank τ S X ≤ S.1.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma rank_strict {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X X' : Fin K)
    (hX' : X' ∈ S.1) (hlt : τ X < τ X') : relRank τ S X < relRank τ S X' := by
  unfold relRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨X', Finset.mem_filter.2 ⟨hX', le_rfl⟩, ?_⟩
    intro h
    exact absurd (Finset.mem_filter.1 h).2 (not_le.2 hlt)
  · intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.trans hlt.le⟩

lemma rank_lt_iff {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X X' : Fin K)
    (hX : X ∈ S.1) (hX' : X' ∈ S.1) : relRank τ S X < relRank τ S X' ↔ τ X < τ X' := by
  constructor
  · intro h
    by_contra hc
    rcases (not_lt.1 hc).lt_or_eq with h' | h'
    · exact absurd (rank_strict τ S X' X hX h') (not_lt.2 h.le)
    · rw [τ.injective h'] at h; exact lt_irrefl _ h
  · exact rank_strict τ S X X' hX'

lemma rank_inj {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X X' : Fin K)
    (hX : X ∈ S.1) (hX' : X' ∈ S.1) (h : relRank τ S X = relRank τ S X') : X = X' := by
  by_contra hne
  rcases lt_or_gt_of_ne (fun e : τ X = τ X' => hne (τ.injective e)) with h1 | h1
  · exact absurd h (rank_strict τ S X X' hX' h1).ne
  · exact absurd h.symm (rank_strict τ S X' X hX h1).ne

/-- The rank map `S → Fin |S|`, `X ↦ τ(X|S) - 1`, is a bijection. -/
noncomputable def rankEquiv {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) : S.1 ≃ Fin S.1.card :=
  Equiv.ofBijective (fun x => ⟨relRank τ S x.1 - 1, by
      have := rank_le_card τ S x.1; have := rank_ge_one τ S x.1 x.2; omega⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp⟩
    intro x y hxy
    simp only [Fin.mk.injEq] at hxy
    have := rank_ge_one τ S x.1 x.2; have := rank_ge_one τ S y.1 y.2
    exact Subtype.ext (rank_inj τ S x.1 y.1 x.2 y.2 (by omega)))

lemma rankEquiv_val {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (x : S.1) :
    ((rankEquiv τ S x : Fin S.1.card) : ℕ) = relRank τ S x.1 - 1 := rfl

/-- Chain property of `p`-separability along consecutive ranks. -/
lemma psep_chain {K : ℕ} (p : ℝ) (hp0 : 0 < p) (f : Pref K) (σf : Equiv.Perm (Fin K))
    (hps : PSep p f σf) (hfnn : ∀ S X, 0 ≤ f S X) (S : DS K) :
    ∀ d : ℕ, ∀ i j : Fin K, i ∈ S.1 → j ∈ S.1 → relRank σf S i = relRank σf S j + d →
      f S i ≤ p ^ d * f S j := by
  intro d
  induction d with
  | zero =>
    intro i j hi hj h
    rw [rank_inj σf S i j hi hj (by simpa using h)]; simp
  | succ d ih =>
    intro i j hi hj h
    -- the element of rank `r(j) + d`
    have hlt : relRank σf S j + d - 1 < S.1.card := by
      have := rank_le_card σf S i; omega
    obtain ⟨m, hm⟩ := (rankEquiv σf S).surjective ⟨relRank σf S j + d - 1, hlt⟩
    have hmv := congrArg Fin.val hm
    rw [rankEquiv_val] at hmv
    simp only at hmv
    have hm1 := rank_ge_one σf S m.1 m.2
    have hj1 := rank_ge_one σf S j hj
    have hrm : relRank σf S m.1 = relRank σf S j + d := by omega
    have h1 : f S i ≤ p * f S m.1 :=
      hps S m.1 i m.2 hi ((rank_lt_iff σf S m.1 i m.2 hi).1 (by omega))
    have h2 := ih m.1 j m.2 hj hrm
    calc f S i ≤ p * f S m.1 := h1
      _ ≤ p * (p ^ d * f S j) := by gcongr
      _ = p ^ (d + 1) * f S j := by ring

/-- The supermartingale inequality: `∑_{X∈S} f(X|S) f^OA_σ(X|S)/f^OA_{σ_f}(X|S) ≤ 1`. -/
theorem ratio_sum_le_one {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K)) (hps : PSep p f σf)
    (σ : Equiv.Perm (Fin K)) (S : DS K) :
    ∑ X ∈ S.1, f S X * (oa p σ S X / oa p σf S X) ≤ 1 := by
  classical
  have hfnn : ∀ S X, 0 ≤ f S X := by
    intro S X
    by_cases hX : X ∈ S.1
    · exact ((hf.1 S X).1 hX).le
    · exact ((hf.1 S X).2 hX).ge
  set n := S.1.card
  have hc : 0 < (1 - p) / (1 - p ^ n) := by
    have : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by have := S.2; omega)
    apply div_pos <;> linarith
  set rσ := fun X => relRank σ S X
  set rf := fun X => relRank σf S X
  have hratio : ∀ X ∈ S.1, oa p σ S X / oa p σf S X = p ^ (rσ X - 1) / p ^ (rf X - 1) := by
    intro X hX
    simp only [oa, if_pos hX, rσ, rf]
    rw [mul_div_mul_left _ _ hc.ne']
  -- move to the subtype
  let u : S.1 → ℝ := fun x => f S x.1 / p ^ (rf x.1 - 1)
  let w : S.1 → ℝ := fun x => p ^ (rf x.1 - 1)
  let π : Equiv.Perm S.1 := (rankEquiv σ S).trans (rankEquiv σf S).symm
  have hπ : ∀ x, rf (π x).1 = rσ x.1 := by
    intro x
    have h1 : rankEquiv σf S (π x) = rankEquiv σ S x := by simp [π]
    have h2 := congrArg Fin.val h1
    rw [rankEquiv_val, rankEquiv_val] at h2
    have := rank_ge_one σf S (π x).1 (π x).2
    have := rank_ge_one σ S x.1 x.2
    simp only [rf, rσ]; omega
  have hmono : Monovary u w := by
    intro i j hij
    simp only [w] at hij
    have hlt : rf j.1 - 1 < rf i.1 - 1 := (pow_lt_pow_iff_right_of_lt_one₀ hp0 hp1).1 hij
    have hi1 := rank_ge_one σf S i.1 i.2
    have hj1 := rank_ge_one σf S j.1 j.2
    have hch := psep_chain p hp0 f σf hps hfnn S (rf i.1 - rf j.1) i.1 j.1 i.2 j.2
      (by simp only [rf] at hlt ⊢; omega)
    simp only [u]
    rw [div_le_div_iff₀ (pow_pos hp0 _) (pow_pos hp0 _)]
    have e : rf i.1 - 1 = (rf j.1 - 1) + (rf i.1 - rf j.1) := by simp only [rf] at hlt ⊢; omega
    rw [e, pow_add]
    calc f S i.1 * p ^ (rf j.1 - 1) ≤ p ^ (rf i.1 - rf j.1) * f S j.1 * p ^ (rf j.1 - 1) := by
          gcongr
      _ = f S j.1 * (p ^ (rf j.1 - 1) * p ^ (rf i.1 - rf j.1)) := by ring
  have hre := hmono.sum_mul_comp_perm_le_sum_mul (σ := π)
  have hsum1 : ∑ x : S.1, u x * w x = 1 := by
    have : ∀ x : S.1, u x * w x = f S x.1 := by
      intro x; simp only [u, w]; field_simp
    simp_rw [this]
    rw [Finset.sum_coe_sort S.1 (fun X => f S X)]
    exact hf.2.1 S
  have hsum2 : ∑ x : S.1, u x * w (π x) = ∑ X ∈ S.1, f S X * (oa p σ S X / oa p σf S X) := by
    rw [← Finset.sum_coe_sort S.1]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [u, w, hπ x]
    rw [hratio x.1 x.2]
    ring
  rw [← hsum2, ← hsum1]
  exact hre

end MTPAux10

namespace MTPAux5
open RobustPrefLearn.MTP

/-- Rankings satisfying (A-3) for the same preference induce the same strict order. -/
lemma order_transfer {K : ℕ} (g : Pref K) (σ τ : Equiv.Perm (Fin K)) (hσ : Ranks g σ)
    (hτ : Ranks g τ) (X X' : Fin K) (hne : X ≠ X') : σ X < σ X' ↔ τ X < τ X' := by
  have hcard : 2 ≤ ({X, X'} : Finset (Fin K)).card := by rw [Finset.card_pair hne]
  set S : DS K := ⟨{X, X'}, hcard⟩
  have h1 : X ∈ S.1 := by simp [S]
  have h2 : X' ∈ S.1 := by simp [S]
  rw [← hσ S X X' h1 h2 hne, hτ S X X' h1 h2 hne]

lemma psep_transfer {K : ℕ} (p : ℝ) (g : Pref K) (σ τ : Equiv.Perm (Fin K)) (hσ : Ranks g σ)
    (hτ : Ranks g τ) (hps : PSep p g σ) : PSep p g τ := by
  intro S X X' hX hX' hlt
  have hne : X ≠ X' := fun e => by rw [e] at hlt; exact lt_irrefl _ hlt
  exact hps S X X' hX hX' ((order_transfer g σ τ hσ hτ X X' hne).2 hlt)

lemma psep_of_rank {K : ℕ} (p : ℝ) (g : Pref K) (τ : Equiv.Perm (Fin K))
    (hg : g ∈ MpRank p τ) : PSep p g τ := by
  obtain ⟨σ0, hR0, hP0⟩ := hg.1.2.2
  exact psep_transfer p g σ0 τ hR0 hg.2 hP0

lemma sum_rank {K : ℕ} (g : ℕ → ℝ) (T : Finset (Fin K)) :
    ∑ X ∈ T, g (T.filter (fun k => k ≤ X)).card = ∑ j ∈ Finset.range T.card, g (j + 1) := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a T ha ih =>
    have haT : a ∉ T := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert haT, Finset.card_insert_of_notMem haT, Finset.sum_range_succ]
    have h1 : (insert a T).filter (fun k => k ≤ a) = insert a T := by
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · exact (ha x hx).le
    have h2 : ∀ X ∈ T, (insert a T).filter (fun k => k ≤ X) = T.filter (fun k => k ≤ X) := by
      intro X hX
      rw [Finset.filter_insert, if_neg (not_le.2 (ha X hX))]
    rw [h1, Finset.card_insert_of_notMem haT, Finset.sum_congr rfl (fun X hX => by rw [h2 X hX]),
      ih]
    ring

lemma relRank_one {K : ℕ} (S : DS K) (X : Fin K) :
    relRank (1 : Equiv.Perm (Fin K)) S X = (S.1.filter (fun k => k ≤ X)).card := by
  unfold relRank
  congr 1

lemma hv {K : ℕ} (m k : Fin K) : ((sigmaHat m) k).val =
    if k.val < m.val then k.val + 1 else if k.val = m.val then 0 else k.val := by
  unfold sigmaHat
  by_cases h : k ≤ m
  · rw [Fin.coe_cycleRange_of_le h]
    by_cases h' : k = m
    · subst h'; simp
    · have : k.val < m.val := lt_of_le_of_ne h (fun e => h' (Fin.ext e))
      rw [if_neg h', if_pos this]
  · rw [Fin.cycleRange_of_gt (not_le.1 h)]
    have : ¬ k.val < m.val := fun e => h (le_of_lt e)
    have : ¬ k.val = m.val := fun e => h (le_of_eq (Fin.ext e))
    simp_all

lemma relRank_hat {K : ℕ} (m : Fin K) (S : DS K) (X : Fin K) :
    relRank (sigmaHat m) S X =
      if X < m then (S.1.filter (fun k => k ≤ X)).card + (if m ∈ S.1 then 1 else 0)
      else if X = m then (if m ∈ S.1 then 1 else 0)
      else (S.1.filter (fun k => k ≤ X)).card := by
  unfold relRank
  simp only [Finset.card_filter]
  have key : ∀ k : Fin K, (if sigmaHat m k ≤ sigmaHat m X then 1 else 0 : ℕ) =
      if X < m then (if k ≤ X then 1 else 0) + (if k = m then 1 else 0)
      else if X = m then (if k = m then 1 else 0)
      else (if k ≤ X then 1 else 0) := by
    intro k
    simp only [Fin.le_def, hv m k, hv m X]
    simp only [Fin.lt_def, Fin.ext_iff]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl (fun k _ => key k)]
  split_ifs <;> simp_all [Finset.sum_add_distrib, Finset.sum_ite_eq']

/-- Split a sum over `S ∋ k` into the parts before `k`, at `k` and after `k`. -/
lemma sum_split {K : ℕ} (S : Finset (Fin K)) (k : Fin K) (hk : k ∈ S) (F : Fin K → ℝ) :
    ∑ X ∈ S, F X = ∑ X ∈ S.filter (fun X => X < k), F X + F k +
      ∑ X ∈ S.filter (fun X => k < X), F X := by
  classical
  have : ∀ X, F X = (if X < k then F X else 0) + (if X = k then F X else 0) +
      (if k < X then F X else 0) := by
    intro X
    rcases lt_trichotomy X k with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.2 h.le]
  rw [Finset.sum_congr rfl (fun X _ => this X), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_filter, Finset.sum_filter, Finset.sum_ite_eq' S k F, if_pos hk]

end MTPAux5

namespace MTPAux4
open RobustPrefLearn.MTP

/-- The permutation of `S` sending `X` to the element whose `σ_k`-rank in `S` equals the
`σ̂_k`-rank of `X`. -/
noncomputable def piS {K : ℕ} (σk : Equiv.Perm (Fin K)) (k : Fin K) (S : DS K) : Equiv.Perm S.1 :=
  (MTPAux10.rankEquiv (sigmaHat k) S).trans (MTPAux10.rankEquiv σk S).symm

lemma rank_piS {K : ℕ} (σk : Equiv.Perm (Fin K)) (k : Fin K) (S : DS K) (x : S.1) :
    relRank σk S (piS σk k S x).1 = relRank (sigmaHat k) S x.1 := by
  have h1 : MTPAux10.rankEquiv σk S (piS σk k S x) = MTPAux10.rankEquiv (sigmaHat k) S x := by
    simp [piS]
  have h2 := congrArg Fin.val h1
  rw [MTPAux10.rankEquiv_val, MTPAux10.rankEquiv_val] at h2
  have := MTPAux10.rank_ge_one σk S _ (piS σk k S x).2
  have := MTPAux10.rank_ge_one (sigmaHat k) S _ x.2
  omega

/-- `σ_k` and `σ̂_k` order the pair `(π x, π x')` resp. `(x, x')` in the same way. -/
lemma lt_piS {K : ℕ} (σk : Equiv.Perm (Fin K)) (k : Fin K) (S : DS K) (x x' : S.1) :
    σk (piS σk k S x).1 < σk (piS σk k S x').1 ↔ sigmaHat k x.1 < sigmaHat k x'.1 := by
  rw [← MTPAux10.rank_lt_iff σk S _ _ (piS σk k S x).2 (piS σk k S x').2, rank_piS, rank_piS,
    MTPAux10.rank_lt_iff (sigmaHat k) S _ _ x.2 x'.2]

/-- The rearranged preference `f̂`. -/
noncomputable def fhat {K : ℕ} (σk : Equiv.Perm (Fin K)) (k : Fin K) (f : Pref K) : Pref K :=
  fun S X => if hX : X ∈ S.1 then f S (piS σk k S ⟨X, hX⟩).1 else 0

lemma fhat_mem {K : ℕ} (p : ℝ) (σk : Equiv.Perm (Fin K)) (k : Fin K) (f : Pref K)
    (hf : f ∈ MpRank p σk) : fhat σk k f ∈ MpRank p (sigmaHat k) := by
  classical
  have hps := MTPAux5.psep_of_rank p f σk hf
  have hR := hf.2
  have hRanks : Ranks (fhat σk k f) (sigmaHat k) := by
    intro S X X' hX hX' hne
    simp only [fhat, dif_pos hX, dif_pos hX']
    have hne' : (piS σk k S ⟨X, hX⟩).1 ≠ (piS σk k S ⟨X', hX'⟩).1 := by
      intro e
      apply hne
      have := (piS σk k S).injective (Subtype.ext e)
      exact congrArg Subtype.val this
    rw [hR S _ _ (piS σk k S ⟨X, hX⟩).2 (piS σk k S ⟨X', hX'⟩).2 hne', lt_piS]
  refine ⟨⟨fun S X => ⟨fun hX => ?_, fun hX => ?_⟩, fun S => ?_, sigmaHat k, hRanks, ?_⟩, hRanks⟩
  · simp only [fhat, dif_pos hX]; exact (hf.1.1 S _).1 (piS σk k S ⟨X, hX⟩).2
  · simp only [fhat, dif_neg hX]
  · rw [← Finset.sum_coe_sort S.1]
    have : ∀ x : S.1, fhat σk k f S x.1 = f S (piS σk k S x).1 := by
      intro x; simp only [fhat, dif_pos x.2]
    simp_rw [this]
    rw [Equiv.sum_comp (piS σk k S) (fun y : S.1 => f S y.1), Finset.sum_coe_sort S.1 (f S)]
    exact hf.1.2.1 S
  · intro S X X' hX hX' hlt
    simp only [fhat, dif_pos hX, dif_pos hX']
    exact hps S _ _ (piS σk k S ⟨X, hX⟩).2 (piS σk k S ⟨X', hX'⟩).2
      ((lt_piS σk k S ⟨X, hX⟩ ⟨X', hX'⟩).2 hlt)

/-- `σ̂_k` restricted to the versions other than `k` is the identity order. -/
lemma hat_lt_iff {K : ℕ} (k X X' : Fin K) (hX : X ≠ k) (hX' : X' ≠ k) :
    sigmaHat k X < sigmaHat k X' ↔ X < X' := by
  rw [Fin.lt_def, Fin.lt_def, MTPAux5.hv k X, MTPAux5.hv k X']
  have h1 : X.val ≠ k.val := fun e => hX (Fin.ext e)
  have h2 : X'.val ≠ k.val := fun e => hX' (Fin.ext e)
  split_ifs <;> omega

lemma piS_k {K : ℕ} (σk : Equiv.Perm (Fin K)) (k : Fin K) (hσk : (σk k).val = 0) (S : DS K)
    (hkS : k ∈ S.1) : (piS σk k S ⟨k, hkS⟩).1 = k := by
  have h := rank_piS σk k S ⟨k, hkS⟩
  have hk1 : relRank (sigmaHat k) S k = 1 := by
    unfold relRank
    rw [Finset.card_eq_one]
    refine ⟨k, ?_⟩
    ext a
    simp only [Finset.mem_filter, Finset.mem_singleton, Fin.le_def, MTPAux5.hv k a,
      MTPAux5.hv k k, lt_irrefl, if_false, if_true]
    constructor
    · rintro ⟨_, h⟩
      apply Fin.ext
      split_ifs at h with h1 h2 <;> omega
    · rintro rfl; simp [hkS]
  rw [hk1] at h
  -- the element of `σ_k`-rank `1` in `S` is `k`
  by_contra hne
  have hlt : σk k < σk (piS σk k S ⟨k, hkS⟩).1 := by
    rw [Fin.lt_def, hσk]
    have : σk (piS σk k S ⟨k, hkS⟩).1 ≠ σk k := fun e => hne (σk.injective e)
    have : (σk (piS σk k S ⟨k, hkS⟩).1).val ≠ (σk k).val := fun e => this (Fin.ext e)
    omega
  have := MTPAux10.rank_strict σk S k _ (piS σk k S ⟨k, hkS⟩).2 hlt
  have := MTPAux10.rank_ge_one σk S k hkS
  omega

lemma key_S {K : ℕ} (p : ℝ) (k : Fin K) (fstar : Pref K)
    (hfstar : fstar ∈ MpRank p (1 : Equiv.Perm (Fin K))) (σk : Equiv.Perm (Fin K))
    (hσk : (σk k).val = 0) (f : Pref K) (hf : f ∈ MpRank p σk) (S : DS K) :
    DS_ fstar (fhat σk k f) S ≤ DS_ fstar f S := by
  classical
  set π' : Equiv.Perm (Fin K) := Equiv.Perm.ofSubtype (piS σk k S) with hπ'
  have hπS : ∀ X (hX : X ∈ S.1), π' X = (piS σk k S ⟨X, hX⟩).1 := by
    intro X hX; rw [hπ', Equiv.Perm.ofSubtype_apply_of_mem _ hX]
  have hπout : ∀ X, X ∉ S.1 → π' X = X := by
    intro X hX; rw [hπ', Equiv.Perm.ofSubtype_apply_of_not_mem _ hX]
  have hπmem : ∀ X ∈ S.1, π' X ∈ S.1 := by
    intro X hX; rw [hπS X hX]; exact (piS σk k S ⟨X, hX⟩).2
  have hfh : ∀ X ∈ S.1, fhat σk k f S X = f S (π' X) := by
    intro X hX; simp only [fhat, dif_pos hX, hπS X hX]
  have hfpos : ∀ X ∈ S.1, 0 < f S X := fun X hX => (hf.1.1 S X).1 hX
  have hfspos : ∀ X ∈ S.1, 0 < fstar S X := fun X hX => (hfstar.1.1 S X).1 hX
  have hfhpos : ∀ X ∈ S.1, 0 < fhat σk k f S X := fun X hX => by
    rw [hfh X hX]; exact hfpos _ (hπmem X hX)
  -- reduce to the cross-entropy terms
  have hD : ∀ h : Pref K, (∀ X ∈ S.1, 0 < h S X) →
      DS_ fstar h S = ∑ X ∈ S.1, fstar S X * Real.log (fstar S X) -
        ∑ X ∈ S.1, fstar S X * Real.log (h S X) := by
    intro h hh
    unfold DS_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun X hX => ?_
    rw [Real.log_div (hfspos X hX).ne' (hh X hX).ne']; ring
  rw [hD _ hfhpos, hD _ hfpos]
  suffices hsuff : ∑ X ∈ S.1, fstar S X * Real.log (f S X) ≤
      ∑ X ∈ S.1, fstar S X * Real.log (fhat σk k f S X) by linarith
  -- the rearrangement on `S \ {k}`
  set s := S.1.erase k
  let u : Fin K → ℝ := fun X => fstar S X
  let g : Fin K → ℝ := fun X => Real.log (f S (π' X))
  have hmono : MonovaryOn u g s := by
    intro i hi j hj hij
    have hiS := Finset.mem_of_mem_erase hi
    have hjS := Finset.mem_of_mem_erase hj
    have hik := Finset.ne_of_mem_erase hi
    have hjk := Finset.ne_of_mem_erase hj
    simp only [g] at hij
    have hlt : f S (π' i) < f S (π' j) :=
      (Real.log_lt_log_iff (hfpos _ (hπmem i hiS)) (hfpos _ (hπmem j hjS))).1 hij
    rw [← hfh i hiS, ← hfh j hjS] at hlt
    have hne : i ≠ j := fun e => by rw [e] at hlt; exact lt_irrefl _ hlt
    have hRh := (fhat_mem p σk k f hf).2 S i j hiS hjS hne
    have h1 : ¬ sigmaHat k i < sigmaHat k j := fun h => absurd (hRh.2 h) (not_le.2 hlt)
    have h2 : sigmaHat k j < sigmaHat k i := by
      rcases lt_or_gt_of_ne (fun e : sigmaHat k i = sigmaHat k j => hne ((sigmaHat k).injective e))
        with h | h
      · exact absurd h h1
      · exact h
    have h3 : j < i := (hat_lt_iff k j i hjk hik).1 h2
    have := (hfstar.2 S j i hjS hiS hne.symm).2 (by simpa using h3)
    exact this
  have hsupp : {x | π'.symm x ≠ x} ⊆ (s : Set (Fin K)) := by
    intro x hx
    simp only [s, Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
    by_cases hxS : x ∈ S.1
    · refine ⟨hxS, fun e => hx ?_⟩
      subst e
      rw [Equiv.symm_apply_eq, hπS x hxS, piS_k σk x hσk S hxS]
    · exact absurd ((Equiv.symm_apply_eq π').2 (hπout x hxS).symm) hx
  have hre := hmono.sum_mul_comp_perm_le_sum_mul hsupp
  simp only [u, g, Equiv.apply_symm_apply] at hre
  -- add back the `k` term
  by_cases hkS : k ∈ S.1
  · rw [← Finset.sum_erase_add _ _ hkS, ← Finset.sum_erase_add _ _ hkS, hfh k hkS,
      hπS k hkS, piS_k σk k hσk S hkS]
    have : ∑ X ∈ s, fstar S X * Real.log (fhat σk k f S X) =
        ∑ X ∈ s, fstar S X * Real.log (f S (π' X)) :=
      Finset.sum_congr rfl fun X hX => by rw [hfh X (Finset.mem_of_mem_erase hX)]
    rw [this]
    linarith
  · have hs : s = S.1 := Finset.erase_eq_of_notMem hkS
    rw [← hs]
    have : ∑ X ∈ s, fstar S X * Real.log (fhat σk k f S X) =
        ∑ X ∈ s, fstar S X * Real.log (f S (π' X)) :=
      Finset.sum_congr rfl fun X hX => by rw [hfh X (Finset.mem_of_mem_erase hX)]
    rw [this]
    exact hre

end MTPAux4

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (k : Fin K)
    (fstar : Pref K) (hfstar : fstar ∈ MpRank p (1 : Equiv.Perm (Fin K)))
    (σk : Equiv.Perm (Fin K)) (hσk : (σk k).val = 0)
    (f : Pref K) (hf : f ∈ MpRank p σk) :
    ∃ fh ∈ MpRank p (sigmaHat k), ∀ lam ∈ simplex K, Dlam lam fstar fh ≤ Dlam lam fstar f :=
  ⟨MTPAux4.fhat σk k f, MTPAux4.fhat_mem p σk k f hf, fun lam hlam =>
    Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left
      (MTPAux4.key_S p k fstar hfstar σk hσk f hf S) (hlam.1 S)⟩
