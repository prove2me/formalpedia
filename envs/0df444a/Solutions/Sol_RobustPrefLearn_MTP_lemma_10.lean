-- Prove2me | solution 1 for RobustPrefLearn.MTP.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:30:11.477021+00:00
-- url     : https://prove2.me/submissions/6dbe444d-c9b2-430d-b19c-8f3ba1f46566

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp

open scoped ENNReal Topology

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


lemma toHist_snoc {K t : ℕ} (w : Fin t → Step K) (x : Step K) :
    toHist (Fin.snoc w x : Fin (t + 1) → Step K) = x :: toHist w := by
  unfold toHist
  rw [List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma toHist_zero {K : ℕ} (v : Fin 0 → Step K) : toHist v = [] := by
  simp [toHist]

lemma survives_cons {K : ℕ} (π : Policy K) (x : Step K) (h : List (Step K)) :
    survives π (x :: h) ↔ ¬ π.stop (x :: h) ∧ survives π h := by
  unfold survives
  constructor
  · intro H
    refine ⟨by simpa using H 0 (by simp), fun j hj => ?_⟩
    simpa using H (j + 1) (by simp; omega)
  · rintro ⟨H0, H⟩ j hj
    cases j with
    | zero => simpa using H0
    | succ j => simpa using H j (by simp at hj; omega)

lemma stopsAt_cons {K : ℕ} (π : Policy K) (x : Step K) (h : List (Step K)) :
    stopsAt π (x :: h) ↔ π.stop (x :: h) ∧ survives π h := by
  unfold stopsAt survives
  constructor
  · rintro ⟨H0, H⟩
    refine ⟨H0, fun j hj => ?_⟩
    simpa using H (j + 1) (by omega) (by simp; omega)
  · rintro ⟨H0, H⟩
    refine ⟨H0, fun j hj1 hj2 => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simpa using H j (by simp at hj2; omega)

/-- One-step likelihood ratio `f^OA_σ / f^OA_{σ'}` of a step, in `[0, ∞]`. -/
noncomputable def rho {K : ℕ} (p : ℝ) (σ σ' : Equiv.Perm (Fin K)) (x : Step K) : ℝ≥0∞ :=
  ENNReal.ofReal (oa p σ x.1 x.2 / oa p σ' x.1 x.2)

/-- The likelihood-ratio process `M_t = ∏_{ℓ ≤ t} f^OA_σ / f^OA_{σ'}`. -/
noncomputable def Mart {K : ℕ} (p : ℝ) (σ σ' : Equiv.Perm (Fin K)) (h : List (Step K)) : ℝ≥0∞ :=
  (h.map (rho p σ σ')).prod

lemma step_super {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (π : Policy K) (hπ : Admissible π)
    (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K)) (hps : PSep p f σf)
    (σ : Equiv.Perm (Fin K)) (h : List (Step K)) :
    ∑ x : Step K, π.disp h x.1 * ENNReal.ofReal (f x.1 x.2) * rho p σ σf x ≤ 1 := by
  rw [Fintype.sum_prod_type]
  have hfnn : ∀ S X, 0 ≤ f S X := by
    intro S X
    by_cases hX : X ∈ S.1
    · exact ((hf.1 S X).1 hX).le
    · exact ((hf.1 S X).2 hX).ge
  have hoa : ∀ τ : Equiv.Perm (Fin K), ∀ S X, 0 ≤ oa p τ S X := by
    intro τ S X
    unfold oa
    split_ifs
    · have : p ^ S.1.card < 1 := pow_lt_one₀ hp0.le hp1 (by have := S.2; omega)
      have : 0 < (1 - p) / (1 - p ^ S.1.card) := by apply div_pos <;> linarith
      positivity
    · exact le_rfl
  have hS : ∀ S : DS K, ∑ X : Fin K, ENNReal.ofReal (f S X) * rho p σ σf (S, X) ≤ 1 := by
    intro S
    unfold rho
    simp_rw [← ENNReal.ofReal_mul (hfnn S _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun X _ =>
      mul_nonneg (hfnn S X) (div_nonneg (hoa σ S X) (hoa σf S X)))]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have : ∑ X : Fin K, f S X * (oa p σ S X / oa p σf S X) =
        ∑ X ∈ S.1, f S X * (oa p σ S X / oa p σf S X) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro X _ hX
      simp [(hf.1 S X).2 hX]
    rw [this]
    exact ratio_sum_le_one p hp0 hp1 f hf σf hps σ S
  calc ∑ S : DS K, ∑ X : Fin K, π.disp h (S, X).1 * ENNReal.ofReal (f (S, X).1 (S, X).2) *
        rho p σ σf (S, X)
      = ∑ S : DS K, π.disp h S * ∑ X : Fin K, ENNReal.ofReal (f S X) * rho p σ σf (S, X) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun X _ => ?_
        simp only; ring
    _ ≤ ∑ S : DS K, π.disp h S * 1 := by
        gcongr with S
        exact hS S
    _ = 1 := by simp only [mul_one]; exact hπ h

open Classical in
lemma key_step_super {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (π : Policy K)
    (hπ : Admissible π) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K))
    (hps : PSep p f σf) (σ : Equiv.Perm (Fin K)) (t : ℕ) :
    (∑ v : Fin (t + 1) → Step K, if stopsAt π (toHist v) then
        pathProb π f (toHist v) * Mart p σ σf (toHist v) else 0) +
      (∑ v : Fin (t + 1) → Step K, if survives π (toHist v) then
        pathProb π f (toHist v) * Mart p σ σf (toHist v) else 0) ≤
      ∑ v : Fin t → Step K, if survives π (toHist v) then
        pathProb π f (toHist v) * Mart p σ σf (toHist v) else 0 := by
  rw [← Finset.sum_add_distrib]
  rw [← (Fin.snocEquiv (fun _ => Step K)).sum_comp]
  have hsn : ∀ i : Step K × (Fin t → Step K),
      (Fin.snocEquiv (fun _ => Step K)) i = (Fin.snoc i.2 i.1 : Fin (t + 1) → Step K) :=
    fun i => rfl
  simp only [hsn, toHist_snoc, stopsAt_cons, survives_cons]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_le_sum fun w _ => ?_
  have : ∀ x : Step K,
      ((if π.stop (x :: toHist w) ∧ survives π (toHist w) then
          pathProb π f (x :: toHist w) * Mart p σ σf (x :: toHist w) else 0) +
        (if ¬ π.stop (x :: toHist w) ∧ survives π (toHist w) then
          pathProb π f (x :: toHist w) * Mart p σ σf (x :: toHist w) else 0)) =
      (if survives π (toHist w) then
          pathProb π f (toHist w) * Mart p σ σf (toHist w) else 0) *
        (π.disp (toHist w) x.1 * ENNReal.ofReal (f x.1 x.2) * rho p σ σf x) := by
    intro x
    obtain ⟨S, X⟩ := x
    simp only [pathProb, Mart, List.map_cons, List.prod_cons]
    by_cases hs : survives π (toHist w) <;> by_cases hst : π.stop ((S, X) :: toHist w) <;>
      simp [hs, hst] <;> ring
  simp_rw [this, ← Finset.mul_sum]
  calc _ ≤ (if survives π (toHist w) then
          pathProb π f (toHist w) * Mart p σ σf (toHist w) else 0) * 1 := by
        gcongr
        exact step_super p hp0 hp1 π hπ f hf σf hps σ (toHist w)
    _ = _ := mul_one _

open Classical in
lemma partial_super {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (π : Policy K)
    (hπ : Admissible π) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K))
    (hps : PSep p f σf) (σ : Equiv.Perm (Fin K)) (t : ℕ) :
    (∑ v : Fin t → Step K, if survives π (toHist v) then
        pathProb π f (toHist v) * Mart p σ σf (toHist v) else 0) +
      ∑ s ∈ Finset.range (t + 1), ∑ v : Fin s → Step K, (if stopsAt π (toHist v) then
        pathProb π f (toHist v) * Mart p σ σf (toHist v) else 0) ≤ 1 := by
  induction t with
  | zero =>
    rw [Finset.sum_range_one, ← Finset.sum_add_distrib, Fintype.sum_unique]
    simp only [toHist_zero, pathProb, Mart, List.map_nil, List.prod_nil, mul_one]
    unfold survives stopsAt
    by_cases h0 : π.stop [] <;> simp [h0]
    split_ifs <;> simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    calc _ = (∑ v : Fin t → Step K, if survives π (toHist v) then
            pathProb π f (toHist v) * Mart p σ σf (toHist v) else 0) * 0 +
          ((∑ v : Fin (t + 1) → Step K, if stopsAt π (toHist v) then
            pathProb π f (toHist v) * Mart p σ σf (toHist v) else 0) +
          (∑ v : Fin (t + 1) → Step K, if survives π (toHist v) then
            pathProb π f (toHist v) * Mart p σ σf (toHist v) else 0)) +
          ∑ s ∈ Finset.range (t + 1), ∑ v : Fin s → Step K, (if stopsAt π (toHist v) then
            pathProb π f (toHist v) * Mart p σ σf (toHist v) else 0) := by
          rw [mul_zero, zero_add]; ring
      _ ≤ 0 + (∑ v : Fin t → Step K, if survives π (toHist v) then
            pathProb π f (toHist v) * Mart p σ σf (toHist v) else 0) +
          ∑ s ∈ Finset.range (t + 1), ∑ v : Fin s → Step K, (if stopsAt π (toHist v) then
            pathProb π f (toHist v) * Mart p σ σf (toHist v) else 0) := by
          rw [mul_zero]
          gcongr
          exact key_step_super p hp0 hp1 π hπ f hf σf hps σ t
      _ ≤ 1 := by rw [zero_add]; exact ih

open Classical in
/-- Ville's inequality in path form: `E_f[M_τ; τ < ∞] ≤ 1`. -/
theorem ville {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (π : Policy K)
    (hπ : Admissible π) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K))
    (hps : PSep p f σf) (σ : Equiv.Perm (Fin K)) :
    ∑' s : ℕ, ∑ v : Fin s → Step K, (if stopsAt π (toHist v) then
        pathProb π f (toHist v) * Mart p σ σf (toHist v) else 0) ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  cases n with
  | zero => simp
  | succ n =>
    exact le_trans le_add_self (partial_super p hp0 hp1 π hπ f hf σf hps σ n)

lemma g_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) :
    0 < 1 - ((m + 2 : ℕ) : ℝ) * p ^ (m + 1) + (((m + 2 : ℕ) : ℝ) - 1) * p ^ (m + 2) := by
  induction m with
  | zero => norm_num; nlinarith
  | succ m ih =>
    have hpm : 0 < p ^ (m + 1) := pow_pos hp0 _
    have key : 1 - ((m + 1 + 2 : ℕ) : ℝ) * p ^ (m + 1 + 1) +
        (((m + 1 + 2 : ℕ) : ℝ) - 1) * p ^ (m + 1 + 2) =
        (1 - ((m + 2 : ℕ) : ℝ) * p ^ (m + 1) + (((m + 2 : ℕ) : ℝ) - 1) * p ^ (m + 2)) +
          ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by
      push_cast; ring
    rw [key]
    have : 0 < ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by
      have : 0 < (1 - p) ^ 2 := by nlinarith
      positivity
    linarith

lemma aSeq_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    0 < aSeq p n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold aSeq
  have hl : 0 < Real.log (1 / p) := by
    apply Real.log_pos; rw [lt_one_div (by norm_num) hp0]; simpa using hp1
  have := g_pos p hp0 hp1 m
  have e : m + 2 - 1 = m + 1 := by omega
  rw [e]
  positivity

lemma aSeq_mono (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    aSeq p n ≤ aSeq p (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold aSeq
  have hl : 0 < Real.log (1 / p) := by
    apply Real.log_pos; rw [lt_one_div (by norm_num) hp0]; simpa using hp1
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 + 1 - 1 = m + 2 := by omega
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ hl.le
  have hpm : 0 < p ^ (m + 1) := pow_pos hp0 _
  have key : 1 - ((m + 2 + 1 : ℕ) : ℝ) * p ^ (m + 2) +
      (((m + 2 + 1 : ℕ) : ℝ) - 1) * p ^ (m + 2 + 1) =
      (1 - ((m + 2 : ℕ) : ℝ) * p ^ (m + 1) + (((m + 2 : ℕ) : ℝ) - 1) * p ^ (m + 2)) +
        ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by
    push_cast; ring
  rw [key]
  have : 0 ≤ ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by positivity
  linarith

lemma lamStar_nonneg (K : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ lamStar K p n := by
  have hb : 0 < bSeq p n := by
    unfold bSeq
    have : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
    linarith
  have ha := aSeq_pos p hp0 hp1 n hn
  unfold lamStar
  split_ifs
  · apply mul_nonneg hb.le
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le ha (aSeq_mono p hp0 hp1 n hn)
  · positivity

lemma lamStar_sum_pos (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < ∑ m ∈ Finset.Icc 2 K, lamStar K p m := by
  have hK' : lamStar K p K > 0 := by
    unfold lamStar
    rw [if_neg (lt_irrefl K)]
    have hb : 0 < bSeq p K := by
      unfold bSeq
      have : p ^ K < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
      linarith
    have := aSeq_pos p hp0 hp1 K hK
    positivity
  calc 0 < lamStar K p K := hK'
    _ ≤ _ := Finset.single_le_sum (f := fun m => lamStar K p m)
        (fun m hm => lamStar_nonneg K p hp0 hp1 m (Finset.mem_Icc.1 hm).1)
        (Finset.mem_Icc.2 ⟨hK, le_rfl⟩)

lemma card_topSet {K : ℕ} (σ : Equiv.Perm (Fin K)) (n : ℕ) (hn : n ≤ K) :
    (topSet σ n).card = n := by
  have : topSet σ n = (Finset.univ.filter (fun i : Fin K => i.val < n)).map σ.symm.toEmbedding := by
    ext X
    simp [topSet]
  rw [this, Finset.card_map, Fin.card_filter_val_lt]
  omega

lemma mle_nonempty {K : ℕ} [NeZero K] (p : ℝ) (h : List (Step K)) : (mle p h).Nonempty := by
  obtain ⟨σ, -, hσ⟩ := Finset.exists_max_image Finset.univ (fun σ => loglikOA p σ h)
    Finset.univ_nonempty
  exact ⟨σ, by simp [mle]; exact fun σ' => hσ σ' (Finset.mem_univ _)⟩

theorem mtp_admissible {K : ℕ} [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (S1 : DS K) (β : ℝ) : Admissible (mtp p S1 β) := by
  classical
  intro h
  simp only [mtp]
  by_cases hh : h = []
  · simp [hh]
  · simp only [hh, if_false]
    rw [← Finset.mul_sum]
    have hinner : ∀ σ ∈ mle p h, ∑ S : DS K, ∑ n ∈ Finset.Icc 2 K,
        (if S.1 = topSet σ n then
          ENNReal.ofReal (lamStar K p n / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) else 0) = 1 := by
      intro σ _
      rw [Finset.sum_comm]
      have : ∀ n ∈ Finset.Icc 2 K, ∑ S : DS K,
          (if S.1 = topSet σ n then
            ENNReal.ofReal (lamStar K p n / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) else 0) =
          ENNReal.ofReal (lamStar K p n / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) := by
        intro n hn
        obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
        have hc : 2 ≤ (topSet σ n).card := by rw [card_topSet σ n hn2]; exact hn1
        have e : ∀ S : DS K, (S.1 = topSet σ n ↔ S = ⟨topSet σ n, hc⟩) := by
          intro S; constructor
          · intro h'; exact Subtype.ext h'
          · intro h'; rw [h']
        simp_rw [e]
        simp
      rw [Finset.sum_congr rfl this]
      have hpos := lamStar_sum_pos K hK p hp0 hp1
      rw [← ENNReal.ofReal_sum_of_nonneg (fun n hn =>
        div_nonneg (lamStar_nonneg K p hp0 hp1 n (Finset.mem_Icc.1 hn).1) hpos.le)]
      rw [← Finset.sum_div, div_self hpos.ne', ENNReal.ofReal_one]
    rw [Finset.sum_comm, Finset.sum_congr rfl hinner]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    apply ENNReal.inv_mul_cancel
    · simpa using (mle_nonempty p h).ne_empty
    · simp

lemma pos_steps {K : ℕ} (p : ℝ) (π : Policy K) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) :
    ∀ h : List (Step K), pathProb π f h ≠ 0 → ∀ x ∈ h, x.2 ∈ x.1.1 := by
  intro h
  induction h with
  | nil => intro _ x hx; simp at hx
  | cons y h ih =>
    intro hne x hx
    obtain ⟨S, X⟩ := y
    simp only [pathProb] at hne
    have h1 : pathProb π f h ≠ 0 := fun h0 => hne (by rw [h0]; simp)
    have h2 : ENNReal.ofReal (f S X) ≠ 0 := fun h0 => hne (by rw [h0]; simp)
    rcases List.mem_cons.1 hx with rfl | hx
    · by_contra hX
      apply h2
      simp [(hf.1 S X).2 hX]
    · exact ih h1 x hx

lemma oa_pos {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (τ : Equiv.Perm (Fin K)) (S : DS K)
    (X : Fin K) (hX : X ∈ S.1) : 0 < oa p τ S X := by
  unfold oa
  rw [if_pos hX]
  have : p ^ S.1.card < 1 := pow_lt_one₀ hp0.le hp1 (by have := S.2; omega)
  have : 0 < (1 - p) / (1 - p ^ S.1.card) := by apply div_pos <;> linarith
  positivity

lemma Mart_eq {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ σ' : Equiv.Perm (Fin K)) :
    ∀ h : List (Step K), (∀ x ∈ h, x.2 ∈ x.1.1) →
      Mart p σ σ' h = ENNReal.ofReal (Real.exp (loglikOA p σ h - loglikOA p σ' h)) := by
  intro h
  induction h with
  | nil => intro _; simp [Mart, loglikOA]
  | cons y h ih =>
    intro hh
    obtain ⟨S, X⟩ := y
    have hX : X ∈ S.1 := hh (S, X) List.mem_cons_self
    have ih' := ih (fun x hx => hh x (List.mem_cons_of_mem _ hx))
    unfold Mart at ih' ⊢
    rw [List.map_cons, List.prod_cons, ih']
    unfold rho loglikOA
    simp only [List.map_cons, List.sum_cons]
    rw [← ENNReal.ofReal_mul (div_nonneg (oa_pos p hp0 hp1 σ S X hX).le
      (oa_pos p hp0 hp1 σ' S X hX).le)]
    congr 1
    have e : oa p σ S X / oa p σ' S X =
        Real.exp (Real.log (oa p σ S X) - Real.log (oa p σ' S X)) := by
      rw [Real.exp_sub, Real.exp_log (oa_pos p hp0 hp1 σ S X hX),
        Real.exp_log (oa_pos p hp0 hp1 σ' S X hX)]
    rw [e, ← Real.exp_add]
    congr 1
    ring

/-- On a wrong stop, some likelihood-ratio process against `σ_f` exceeds `e^β`. -/
lemma pointwise {K : ℕ} [NeZero K] (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (S1 : DS K) (β : ℝ)
    (hβ : 0 < β) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K))
    (hR : Ranks f σf) (h : List (Step K)) (hst : stopsAt (mtp p S1 β) h)
    (hw : ¬ IsTop f ((mtp p S1 β).select h)) :
    pathProb (mtp p S1 β) f h ≤ ∑ σ : Equiv.Perm (Fin K),
      pathProb (mtp p S1 β) f h * Mart p σ σf h * ENNReal.ofReal (Real.exp (-β)) := by
  classical
  by_cases h0 : pathProb (mtp p S1 β) f h = 0
  · rw [h0]; exact zero_le'
  have hsteps := pos_steps p (mtp p S1 β) f hf h h0
  obtain ⟨_, σ0, hσ0, hstop⟩ := hst.1
  have hne : (mle p h).Nonempty := ⟨σ0, hσ0⟩
  have hsel : (mtp p S1 β).select h = hne.choose.symm 0 := by
    simp only [mtp, dif_pos hne]
  have hc := hne.choose_spec
  -- all MLE rankings share the top of `σ0`
  have htop : hne.choose.symm 0 = σ0.symm 0 := by
    by_contra hdiff
    have hd : diffTop σ0 hne.choose := by
      intro k hk hk'
      have e1 : σ0 k = 0 := Fin.ext hk
      have e2 : hne.choose k = 0 := Fin.ext hk'
      apply hdiff
      rw [(Equiv.symm_apply_eq _).2 e2.symm, (Equiv.symm_apply_eq _).2 e1.symm]
    have h1 := hstop _ hd
    have h2 := (Finset.mem_filter.1 hσ0).2
    have h3 := (Finset.mem_filter.1 hc).2 σ0
    linarith
  -- `σ_f` has a different top than `σ0`
  have hdf : diffTop σ0 σf := by
    intro k hk hk'
    apply hw
    rw [hsel, htop]
    have e1 : σ0 k = 0 := Fin.ext hk
    have e2 : σf k = 0 := Fin.ext hk'
    have : σ0.symm 0 = k := by rw [← e1]; simp
    rw [this]
    exact ⟨σf, hR, hk'⟩
  have hb := hstop σf hdf
  have hM : ENNReal.ofReal (Real.exp β) ≤ Mart p σ0 σf h := by
    rw [Mart_eq p hp0 hp1 σ0 σf h hsteps]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hb)
  calc pathProb (mtp p S1 β) f h
      = pathProb (mtp p S1 β) f h * (ENNReal.ofReal (Real.exp β) *
          ENNReal.ofReal (Real.exp (-β))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, ENNReal.ofReal_one, mul_one]
    _ ≤ pathProb (mtp p S1 β) f h * (Mart p σ0 σf h * ENNReal.ofReal (Real.exp (-β))) := by
        gcongr
    _ = pathProb (mtp p S1 β) f h * Mart p σ0 σf h * ENNReal.ofReal (Real.exp (-β)) := by
        rw [mul_assoc]
    _ ≤ _ := Finset.single_le_sum (f := fun σ => pathProb (mtp p S1 β) f h * Mart p σ σf h *
          ENNReal.ofReal (Real.exp (-β))) (fun _ _ => zero_le') (Finset.mem_univ σ0)

end MTPAux10

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) [NeZero K] (hK : 2 ≤ K) :
    ∃ C : ℝ, ∀ p : ℝ, 0 < p → p < 1 → ∀ (S1 : DS K) (β : ℝ), 0 < β →
      ∀ f ∈ (Mp p : Set (Pref K)),
        probWrong (mtp p S1 β) f ≤ ENNReal.ofReal (C * Real.exp (-β)) := by
  classical
  refine ⟨(Nat.factorial K : ℝ), fun p hp0 hp1 S1 β hβ f hf => ?_⟩
  obtain ⟨σf, hR, hps⟩ := hf.2.2
  have hadm := MTPAux10.mtp_admissible hK p hp0 hp1 S1 β
  set e := ENNReal.ofReal (Real.exp (-β))
  have hpt : ∀ t (v : Fin t → Step K),
      (if stopsAt (mtp p S1 β) (toHist v) ∧ ¬ IsTop f ((mtp p S1 β).select (toHist v)) then
        pathProb (mtp p S1 β) f (toHist v) else 0) ≤
      ∑ σ : Equiv.Perm (Fin K), e * (if stopsAt (mtp p S1 β) (toHist v) then
        pathProb (mtp p S1 β) f (toHist v) * MTPAux10.Mart p σ σf (toHist v) else 0) := by
    intro t v
    split_ifs with h1 h2
    · refine (MTPAux10.pointwise p hp0 hp1 S1 β hβ f hf σf hR (toHist v) h1.1 h1.2).trans ?_
      apply le_of_eq
      refine Finset.sum_congr rfl fun σ _ => ?_
      ring
    · exact absurd h1.1 h2
    · exact zero_le'
    · exact zero_le'
  unfold probWrong
  calc ∑' t : ℕ, ∑ v : Fin t → Step K,
        (if stopsAt (mtp p S1 β) (toHist v) ∧ ¬ IsTop f ((mtp p S1 β).select (toHist v)) then
          pathProb (mtp p S1 β) f (toHist v) else 0)
      ≤ ∑' t : ℕ, ∑ v : Fin t → Step K, ∑ σ : Equiv.Perm (Fin K),
          e * (if stopsAt (mtp p S1 β) (toHist v) then
            pathProb (mtp p S1 β) f (toHist v) * MTPAux10.Mart p σ σf (toHist v) else 0) :=
        ENNReal.tsum_le_tsum fun t => Finset.sum_le_sum fun v _ => hpt t v
    _ = ∑ σ : Equiv.Perm (Fin K), e * ∑' t : ℕ, ∑ v : Fin t → Step K,
          (if stopsAt (mtp p S1 β) (toHist v) then
            pathProb (mtp p S1 β) f (toHist v) * MTPAux10.Mart p σ σf (toHist v) else 0) := by
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin _ → Step K))),
          ← Finset.mul_sum]
        rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ σ : Equiv.Perm (Fin K), e * 1 := by
        gcongr with σ
        exact MTPAux10.ville p hp0 hp1 _ hadm f hf σf hps σ
    _ = ENNReal.ofReal ((Nat.factorial K : ℝ) * Real.exp (-β)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, mul_one,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, nsmul_eq_mul]
