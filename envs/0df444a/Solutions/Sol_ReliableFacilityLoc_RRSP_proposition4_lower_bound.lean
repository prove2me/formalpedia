-- Prove2me | solution 1 for ReliableFacilityLoc.RRSP.proposition4_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T14:45:51.767923+00:00
-- url     : https://prove2.me/submissions/31054f83-d0a8-410f-9ed9-4456f43922f3

import Mathlib
import Definitions.Def_ReliableFacilityLoc_RRSP_RSP
import Definitions.Def_ReliableFacilityLoc_RRSP_RRSP

set_option autoImplicit false

open Finset

namespace RRSPProof

open ReliableFacilityLoc.RRSP ReliableFacilityLoc.Supermod

variable {J : ℕ}

/-- expected cost of a chain, each facility with its own failure probability -/
noncomputable def cQ (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) : List (Fin J) → ℝ
  | [] => phi
  | k :: L => (1 - q k) * d k + q k * cQ d phi q L

/-- cost of a chain with the positional (sorted) probabilities, starting at level `i` -/
noncomputable def cP (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) (σ : Fin J ≃ Fin J) :
    List (Fin J) → ℕ → ℝ
  | [], i => phi * ReliableFacilityLoc.RRSP.beta q σ i
  | k :: M, i => d k * ReliableFacilityLoc.RRSP.alpha q σ i + cP d phi q σ M (i + 1)

theorem cQ_le_phi (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) (hq0 : ∀ j, 0 ≤ q j)
    (hq1 : ∀ j, q j ≤ 1) : ∀ L : List (Fin J), (∀ k ∈ L, d k ≤ phi) → cQ d phi q L ≤ phi
  | [], _ => le_refl _
  | k :: L, h => by
    have ih := cQ_le_phi d phi q hq0 hq1 L (fun x hx => h x (by simp [hx]))
    have hk := h k (by simp)
    simp only [cQ]
    nlinarith [mul_le_mul_of_nonneg_left ih (hq0 k),
      mul_le_mul_of_nonneg_left hk (sub_nonneg.mpr (hq1 k))]

theorem cQ_ins (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) (hq0 : ∀ j, 0 ≤ q j)
    (hq1 : ∀ j, q j ≤ 1) (k : Fin J) : ∀ L : List (Fin J),
    cQ d phi q (L.orderedInsert (fun a b => d a ≤ d b) k) ≤ (1 - q k) * d k + q k * cQ d phi q L
  | [] => by simp [List.orderedInsert, cQ]
  | m :: L => by
    have ih := cQ_ins d phi q hq0 hq1 k L
    by_cases hkm : d k ≤ d m
    · simp [List.orderedInsert_cons, hkm, cQ]
    · simp only [List.orderedInsert_cons, hkm, if_false, cQ]
      replace hkm := not_le.mp hkm
      nlinarith [mul_le_mul_of_nonneg_left ih (hq0 m),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr (hq1 k)) (sub_nonneg.mpr (hq1 m)))
          (sub_nonneg.mpr hkm.le)]

theorem cQ_sortTrunc (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) (hq0 : ∀ j, 0 ≤ q j)
    (hq1 : ∀ j, q j ≤ 1) : ∀ L : List (Fin J),
    cQ d phi q ((L.filter (fun k => decide (d k < phi))).insertionSort (fun a b => d a ≤ d b))
      ≤ cQ d phi q L
  | [] => by simp [cQ]
  | k :: L => by
    have ih := cQ_sortTrunc d phi q hq0 hq1 L
    by_cases hk : d k < phi
    · rw [List.filter_cons_of_pos (by simpa using hk), List.insertionSort_cons]
      have := cQ_ins d phi q hq0 hq1 k
        ((L.filter (fun k => decide (d k < phi))).insertionSort (fun a b => d a ≤ d b))
      simp only [cQ]
      nlinarith [mul_le_mul_of_nonneg_left ih (hq0 k)]
    · rw [List.filter_cons_of_neg (by simpa using hk)]
      have hle := cQ_le_phi d phi q hq0 hq1
        ((L.filter (fun k => decide (d k < phi))).insertionSort (fun a b => d a ≤ d b)) (by
          intro x hx
          rw [List.mem_insertionSort, List.mem_filter] at hx
          have := hx.2
          simp only [decide_eq_true_eq] at this
          exact this.le)
      simp only [cQ]
      replace hk := not_lt.mp hk
      nlinarith [mul_le_mul_of_nonneg_left (hle.trans hk) (sub_nonneg.mpr (hq1 k)),
        mul_le_mul_of_nonneg_left ih (hq0 k)]

theorem beta_zero (q : Fin J → ℝ) (σ : Fin J ≃ Fin J) :
    ReliableFacilityLoc.RRSP.beta q σ 0 = 1 := by
  simp [ReliableFacilityLoc.RRSP.beta]

theorem beta_succ (q : Fin J → ℝ) (σ : Fin J ≃ Fin J) (i : ℕ) (h : i < J) :
    ReliableFacilityLoc.RRSP.beta q σ (i + 1)
      = ReliableFacilityLoc.RRSP.beta q σ i * q (σ ⟨i, h⟩) := by
  unfold ReliableFacilityLoc.RRSP.beta
  have : (univ.filter (fun ℓ : Fin J => (ℓ : ℕ) < i + 1))
      = insert ⟨i, h⟩ (univ.filter (fun ℓ : Fin J => (ℓ : ℕ) < i)) := by
    ext ℓ; simp [Fin.ext_iff]; omega
  rw [this, prod_insert (by simp), mul_comm]

theorem alpha_eq (q : Fin J → ℝ) (σ : Fin J ≃ Fin J) (i : ℕ) (h : i < J) :
    ReliableFacilityLoc.RRSP.alpha q σ i
      = ReliableFacilityLoc.RRSP.beta q σ i - ReliableFacilityLoc.RRSP.beta q σ (i + 1) := by
  rw [ReliableFacilityLoc.RRSP.alpha, dif_pos h, beta_succ q σ i h]; ring

theorem beta_le_prod (q : Fin J → ℝ) (σ : Fin J ≃ Fin J) (hq0 : ∀ j, 0 ≤ q j)
    (hσ : IsQOrdering q σ) (T : Finset (Fin J)) :
    ReliableFacilityLoc.RRSP.beta q σ T.card ≤ ∏ j ∈ T, q j := by
  classical
  have hσ' : Monotone (q ∘ σ) := hσ
  refine Finset.induction_on_max_value (fun x => σ.symm x) T ?_ ?_
  · simp [beta_zero]
  · intro a s has hmax ih
    have hcard : (insert a s).card ≤ J := by simpa using card_le_univ (insert a s)
    rw [card_insert_of_notMem has] at hcard ⊢
    have hlt : s.card < J := by omega
    rw [beta_succ q σ _ hlt, prod_insert has]
    have hle : s.card ≤ (σ.symm a : ℕ) := by
      have hsub : s.map σ.symm.toEmbedding ⊆ Iio (σ.symm a) := by
        intro y hy
        rw [mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [mem_Iio]
        refine lt_of_le_of_ne (hmax x hx) ?_
        intro heq
        have : x = a := σ.symm.injective heq
        exact has (this ▸ hx)
      have := card_le_card hsub
      simpa [Fin.card_Iio] using this
    have hqa : q (σ ⟨s.card, hlt⟩) ≤ q a := by
      have := hσ' (show (⟨s.card, hlt⟩ : Fin J) ≤ σ.symm a from hle)
      simpa using this
    calc ReliableFacilityLoc.RRSP.beta q σ s.card * q (σ ⟨s.card, hlt⟩)
        ≤ (∏ j ∈ s, q j) * q a := mul_le_mul ih hqa (hq0 _) (prod_nonneg fun _ _ => hq0 _)
      _ = q a * ∏ j ∈ s, q j := mul_comm _ _

theorem cP_gen (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) (σ : Fin J ≃ Fin J)
    (hq0 : ∀ j, 0 ≤ q j) (hσ : IsQOrdering q σ) :
    ∀ (M : List (Fin J)) (T : Finset (Fin J)) (c : ℝ),
    M.Nodup → M.Pairwise (fun a b => d a ≤ d b) → (∀ k ∈ M, k ∉ T) → (∀ k ∈ M, d k ≤ phi) →
    c ≤ phi → (∀ k ∈ M, c ≤ d k) →
    cP d phi q σ M T.card - c * ReliableFacilityLoc.RRSP.beta q σ T.card
      ≤ (∏ j ∈ T, q j) * cQ d phi q M - c * ∏ j ∈ T, q j
  | [], T, c, _, _, _, _, hc, _ => by
    simp only [cP, cQ]
    have := beta_le_prod q σ hq0 hσ T
    nlinarith [mul_le_mul_of_nonneg_left this (sub_nonneg.mpr hc)]
  | k :: M, T, c, hnd, hs, hT, hphi, hc, hck => by
    classical
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hs
    have hkT : k ∉ T := hT k (by simp)
    have hcard : (insert k T).card ≤ J := by simpa using card_le_univ (insert k T)
    rw [card_insert_of_notMem hkT] at hcard
    have hlt : T.card < J := by omega
    have ih := cP_gen d phi q σ hq0 hσ M (insert k T) (d k) hnd.2 hs.2
      (by
        intro x hx hxT
        rw [mem_insert] at hxT
        rcases hxT with rfl | hxT
        · exact hnd.1 hx
        · exact hT x (by simp [hx]) hxT)
      (fun x hx => hphi x (by simp [hx])) (hphi k (by simp)) (fun x hx => hs.1 x hx)
    rw [card_insert_of_notMem hkT, prod_insert hkT] at ih
    simp only [cP, cQ]
    rw [alpha_eq q σ _ hlt]
    have hb := beta_le_prod q σ hq0 hσ T
    have hck' : c ≤ d k := hck k (by simp)
    nlinarith [mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hck')]

theorem cP_le_cQ (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) (σ : Fin J ≃ Fin J)
    (hq0 : ∀ j, 0 ≤ q j) (hσ : IsQOrdering q σ) (M : List (Fin J)) (hnd : M.Nodup)
    (hs : M.Pairwise (fun a b => d a ≤ d b)) (hphi : ∀ k ∈ M, d k ≤ phi) :
    cP d phi q σ M 0 ≤ cQ d phi q M := by
  cases M with
  | nil => simp [cP, cQ, beta_zero]
  | cons k M' =>
    have := cP_gen d phi q σ hq0 hσ (k :: M') ∅ (d k) hnd hs (by simp) hphi (hphi k (by simp))
      (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact (List.pairwise_cons.mp hs).1 x hx)
    simpa [beta_zero] using this

theorem sum_filter_le (mu : Fin J → ℝ) (hmu : ∀ j, 0 ≤ mu j) (p : Fin J → Bool) :
    ∀ L : List (Fin J), ((L.filter p).map mu).sum ≤ (L.map mu).sum
  | [] => le_rfl
  | k :: L => by
    have ih := sum_filter_le mu hmu p L
    by_cases hk : p k = true
    · simp [List.filter_cons, hk]; linarith
    · simp [List.filter_cons, hk]; linarith [hmu k]

theorem mapIdx_const (f : Fin J → ℝ) : ∀ L : List (Fin J), (L.mapIdx fun _ k => f k) = L.map f
  | [] => rfl
  | k :: L => by simp [List.mapIdx_cons, mapIdx_const f L]

theorem rrsp_list (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) (mu : Fin J → ℝ)
    (σ : Fin J ≃ Fin J) : ∀ (L : List (Fin J)) (i : ℕ),
    (L.mapIdx fun n k => lam * d k * ReliableFacilityLoc.RRSP.alpha q σ (i + n) + mu k).sum
      + lam * phi * ReliableFacilityLoc.RRSP.beta q σ (i + L.length)
      = lam * cP d phi q σ L i + (L.map mu).sum
  | [], i => by simp [cP]; ring
  | k :: L, i => by
    have ih := rrsp_list lam d phi q mu σ L (i + 1)
    have hf : (fun n k => lam * d k * ReliableFacilityLoc.RRSP.alpha q σ (i + (n + 1)) + mu k)
        = (fun n k => lam * d k * ReliableFacilityLoc.RRSP.alpha q σ (i + 1 + n) + mu k) := by
      funext n k; rw [show i + (n + 1) = i + 1 + n by omega]
    have hl : i + (L.length + 1) = i + 1 + L.length := by omega
    simp only [List.mapIdx_cons, List.sum_cons, List.length_cons, List.map_cons, cP, add_zero]
    rw [hf, hl]
    linear_combination ih

theorem rsp_list (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) :
    ∀ (L : List (Fin J)) (c : ℝ),
    (L.mapIdx fun n k => lam * d k * ((1 - q k) * (c * ((L.take n).map q).prod))).sum
      + lam * phi * (c * (L.map q).prod) = lam * (c * cQ d phi q L)
  | [], c => by simp [cQ]; ring
  | k :: L, c => by
    have ih := rsp_list lam d phi q L (c * q k)
    simp only [List.mapIdx_cons, List.sum_cons, List.take_succ_cons, List.take_zero,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, cQ, mul_assoc] at ih ⊢
    linear_combination ih

variable {R : ℕ}

/-- the level assignment of a chain `L`: `L[r]` at level `r`, emergency at level `L.length` -/
noncomputable def mat (R : ℕ) (L : List (Fin J)) : Fin (J + 1) → Fin (R + 1) → ℝ := fun j r =>
  @Fin.lastCases J (fun _ => ℝ) (if (r : ℕ) = L.length then 1 else 0)
    (fun j' => if h : (r : ℕ) < L.length then (if L[(r : ℕ)] = j' then 1 else 0) else 0) j

theorem mat_last (L : List (Fin J)) (r : Fin (R + 1)) :
    mat R L (Fin.last J) r = if (r : ℕ) = L.length then 1 else 0 := by
  simp [mat]

theorem mat_cs (L : List (Fin J)) (j : Fin J) (r : Fin (R + 1)) :
    mat R L j.castSucc r
      = if h : (r : ℕ) < L.length then (if L[(r : ℕ)] = j then 1 else 0) else 0 := by
  simp [mat]

theorem mat_binary (L : List (Fin J)) (j : Fin (J + 1)) (r : Fin (R + 1)) :
    mat R L j r = 0 ∨ mat R L j r = 1 := by
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · rw [mat_last]; split_ifs <;> simp
  · rw [mat_cs]; split_ifs <;> simp

theorem sum_mat_cs_full (L : List (Fin J)) (hL : L.length ≤ R) (F : Fin J → ℕ → ℝ) :
    ∑ j : Fin J, ∑ r : Fin (R + 1), F j r * mat R L j.castSucc r
      = (L.mapIdx fun n k => F k n).sum := by
  rw [Finset.sum_comm]
  have h1 : ∀ r : Fin (R + 1), ∑ j : Fin J, F j r * mat R L j.castSucc r
      = (fun n : ℕ => if h : n < L.length then F L[n] n else 0) r := by
    intro r
    simp only [mat_cs]
    split_ifs with h
    · simp [mul_ite]
    · simp
  rw [Finset.sum_congr rfl (fun r _ => h1 r),
    Fin.sum_univ_eq_sum_range (fun n : ℕ => if h : n < L.length then F L[n] n else 0)]
  rw [List.mapIdx_eq_ofFn, List.sum_ofFn]
  have h2 : ∀ i : Fin L.length, F (L.get i) (i : ℕ)
      = (fun n : ℕ => if h : n < L.length then F L[n] n else 0) i := by
    intro i; simp [i.isLt]
  rw [Finset.sum_congr rfl (fun i _ => h2 i),
    Fin.sum_univ_eq_sum_range (fun n : ℕ => if h : n < L.length then F L[n] n else 0)]
  symm
  apply Finset.sum_subset (range_subset_range.mpr (by omega))
  intro n _ hn
  rw [mem_range] at hn
  simp [hn]

theorem sum_mat_cs (L : List (Fin J)) (hL : L.length ≤ R) (F : Fin J → ℕ → ℝ) :
    ∑ j : Fin J, ∑ r : Fin R, F j r * mat R L j.castSucc r.castSucc
      = (L.mapIdx fun n k => F k n).sum := by
  rw [← sum_mat_cs_full L hL F]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fin.sum_univ_castSucc (f := fun r => F j r * mat R L j.castSucc r)]
  have : mat R L j.castSucc (Fin.last R) = 0 := by
    rw [mat_cs, dif_neg (by simp; omega)]
  simp [this]

theorem sum_mat_last (L : List (Fin J)) (hL : L.length ≤ R) (G : ℕ → ℝ) :
    ∑ r : Fin (R + 1), G r * mat R L (Fin.last J) r = G L.length := by
  rw [Finset.sum_eq_single (⟨L.length, by omega⟩ : Fin (R + 1))]
  · simp [mat_last]
  · intro b _ hb
    rw [mat_last, if_neg]
    · simp
    · intro h; exact hb (Fin.ext h)
  · simp

theorem isLevel_mat (L : List (Fin J)) (hnd : L.Nodup) (hL : L.length ≤ R) :
    IsLevelAssignment (mat R L) where
  level_one r := by
    rw [Fin.sum_univ_castSucc]
    have h1 : ∑ j : Fin J, mat R L j.castSucc r = if (r : ℕ) < L.length then 1 else 0 := by
      simp only [mat_cs]
      split_ifs with h
      · simp
      · simp
    have h2 : ∑ s ∈ Iio r, mat R L (Fin.last J) s = if L.length < (r : ℕ) then 1 else 0 := by
      have : ∀ s : Fin (R + 1),
          mat R L (Fin.last J) s = if s = ⟨L.length, by omega⟩ then 1 else 0 := by
        intro s; rw [mat_last]; simp [Fin.ext_iff]
      simp only [this, Finset.sum_ite_eq', mem_Iio, Fin.lt_def]
    rw [h1, h2, mat_last]
    split_ifs <;> first | (exfalso; omega) | norm_num
  regular_once j := by
    by_cases hj : j ∈ L
    · obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hj
      refine (Finset.sum_le_sum (g := fun r : Fin R => if r = ⟨n, by omega⟩ then (1 : ℝ) else 0)
        ?_).trans ?_
      · intro r _
        rw [mat_cs]
        split_ifs with h1 h2 h3 <;> try norm_num
        exfalso; apply h3
        ext
        exact (hnd.getElem_inj_iff.mp h2)
      · rw [Finset.sum_ite_eq']; simp
    · refine (Finset.sum_eq_zero ?_).le.trans zero_le_one
      intro r _
      rw [mat_cs]
      split_ifs with h1 h2
      · exact absurd (h2 ▸ List.getElem_mem h1) hj
      · rfl
      · rfl
  emergency_once := by
    have := sum_mat_last L hL (fun _ => 1)
    simpa using this
  binary := mat_binary L

theorem W_eq {R : ℕ} (q : Fin J → ℝ) (Z P W : Fin (J + 1) → Fin (R + 1) → ℝ)
    (h : IsProbLinearization q Z P W) (hb : ∀ j r, Z j r = 0 ∨ Z j r = 1)
    (j : Fin (J + 1)) (r : Fin (R + 1)) : W j r = Z j r * P j r := by
  rcases hb j r with h0 | h1
  · rw [h0, zero_mul]
    have a := h.w_le_z j r
    have b := h.w_nonneg j r
    rw [h0] at a
    linarith
  · rw [h1, one_mul]
    have a := h.w_le_p j r
    have b := h.w_ge j r
    rw [h1] at b
    linarith

theorem P_formula (q : Fin J → ℝ) (hq1 : ∀ j, q j < 1) (L : List (Fin J))
    (P W : Fin (J + 1) → Fin (R + 1) → ℝ) (h : IsProbLinearization q (mat R L) P W) :
    ∀ (n : ℕ) (hn : n < R + 1), n ≤ L.length →
      ∀ j, P j ⟨n, hn⟩ = (1 - qExt q j) * ((L.take n).map q).prod
  | 0, hn, _, j => by simpa using h.prob_zero j
  | n + 1, hn, hle, j => by
    have hnR : n < R := by omega
    have hnL : n < L.length := by omega
    have e : (⟨n + 1, hn⟩ : Fin (R + 1)) = (⟨n, hnR⟩ : Fin R).succ := rfl
    rw [e, h.prob_succ j ⟨n, hnR⟩]
    have hW : ∀ k : Fin J, W k.castSucc (⟨n, hnR⟩ : Fin R).castSucc
        = (if L[n] = k then 1 else 0) * ((1 - q k) * ((L.take n).map q).prod) := by
      intro k
      rw [W_eq q _ P W h (mat_binary L) k.castSucc _]
      have hc : ((⟨n, hnR⟩ : Fin R).castSucc : Fin (R + 1)) = ⟨n, by omega⟩ := rfl
      rw [hc, P_formula q hq1 L P W h n (by omega) (by omega) k.castSucc, mat_cs]
      simp [hnL, qExt]
    simp only [hW]
    rw [Finset.sum_eq_single L[n]]
    · rw [if_pos rfl, one_mul]
      have hne : 1 - q L[n] ≠ 0 := by have := hq1 L[n]; linarith
      rw [List.take_succ, List.getElem?_eq_getElem hnL]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
        List.prod_append, List.prod_cons, List.prod_nil]
      field_simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

theorem rsp_mat (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) (mu : Fin J → ℝ)
    (hq1 : ∀ j, q j < 1) (L : List (Fin J)) (hL : L.length ≤ R)
    (P W : Fin (J + 1) → Fin (R + 1) → ℝ) (h : IsProbLinearization q (mat R L) P W) :
    rspObjective lam d phi mu (mat R L) W = lam * cQ d phi q L + (L.map mu).sum := by
  unfold rspObjective
  rw [Fin.sum_univ_castSucc]
  have e1 : ∑ j : Fin J, ∑ r : Fin (R + 1), lam * dExt d phi j.castSucc * W j.castSucc r
      = ∑ j : Fin J, ∑ r : Fin (R + 1),
          (lam * d j * ((1 - q j) * (1 * ((L.take r).map q).prod))) * mat R L j.castSucc r := by
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun r _ => ?_))
    rw [W_eq q _ P W h (mat_binary L) j.castSucc r]
    by_cases hr : (r : ℕ) ≤ L.length
    · have := P_formula q hq1 L P W h r r.isLt hr j.castSucc
      simp only [Fin.eta] at this
      rw [this]
      simp [dExt, qExt]
      ring
    · rw [mat_cs, dif_neg (by omega)]
      simp
  have e2 : ∑ r : Fin (R + 1), lam * dExt d phi (Fin.last J) * W (Fin.last J) r
      = ∑ r : Fin (R + 1), (lam * phi * (1 * ((L.take r).map q).prod)) * mat R L (Fin.last J) r := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [W_eq q _ P W h (mat_binary L) (Fin.last J) r]
    by_cases hr : (r : ℕ) ≤ L.length
    · have := P_formula q hq1 L P W h r r.isLt hr (Fin.last J)
      simp only [Fin.eta] at this
      rw [this]
      simp [dExt, qExt]
      ring
    · rw [mat_last, if_neg (by omega)]
      simp
  rw [e1, e2, sum_mat_cs_full L hL (fun j n => lam * d j * ((1 - q j) * (1 * ((L.take n).map q).prod))),
    sum_mat_last L hL (fun n => lam * phi * (1 * ((L.take n).map q).prod)),
    sum_mat_cs L hL (fun j _ => mu j), mapIdx_const, List.take_length]
  have := rsp_list lam d phi q L 1
  linarith

theorem rrsp_mat (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) (mu : Fin J → ℝ)
    (σ : Fin J ≃ Fin J) (L : List (Fin J)) (hL : L.length ≤ R) :
    rrspObjective lam d phi q mu σ (mat R L) = lam * cP d phi q σ L 0 + (L.map mu).sum := by
  unfold rrspObjective
  rw [sum_mat_cs L hL (fun j n => lam * d j * ReliableFacilityLoc.RRSP.alpha q σ n + mu j),
    sum_mat_last L hL (fun n => lam * phi * ReliableFacilityLoc.RRSP.beta q σ n)]
  have := rrsp_list lam d phi q mu σ L 0
  simp only [zero_add] at this
  exact this

theorem binary_sum_one {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ)
    (hb : ∀ i, v i = 0 ∨ v i = 1) (hs : ∑ i, v i = 1) :
    ∃ t, ∀ i, v i = if i = t then 1 else 0 := by
  have hnn : ∀ i, 0 ≤ v i := fun i => by rcases hb i with h | h <;> rw [h] <;> norm_num
  obtain ⟨t, ht⟩ : ∃ t, v t = 1 := by
    by_contra hne
    push Not at hne
    have : ∑ i, v i = 0 := Finset.sum_eq_zero (fun i _ => (hb i).resolve_right (hne i))
    linarith
  refine ⟨t, fun i => ?_⟩
  split_ifs with hit
  · rw [hit, ht]
  · rcases hb i with h | h
    · exact h
    · exfalso
      have := Finset.sum_le_sum_of_subset_of_nonneg (s := {i, t}) (t := univ) (f := v)
        (subset_univ _) (fun x _ _ => hnn x)
      rw [Finset.sum_pair hit] at this
      linarith

theorem binary_le_one_unique {ι : Type*} [Fintype ι] (v : ι → ℝ)
    (hb : ∀ i, v i = 0 ∨ v i = 1) (hs : ∑ i, v i ≤ 1) (a b : ι) (ha : v a = 1) (hb' : v b = 1) :
    a = b := by
  classical
  by_contra hab
  have hnn : ∀ i, 0 ≤ v i := fun i => by rcases hb i with h | h <;> rw [h] <;> norm_num
  have := Finset.sum_le_sum_of_subset_of_nonneg (s := {a, b}) (t := univ) (f := v)
    (subset_univ _) (fun x _ _ => hnn x)
  rw [Finset.sum_pair hab] at this
  linarith

theorem extract (Y : Fin (J + 1) → Fin (R + 1) → ℝ) (hY : IsLevelAssignment Y) :
    ∃ L : List (Fin J), L.Nodup ∧ L.length ≤ R ∧ Y = mat R L := by
  classical
  have hnn : ∀ j r, 0 ≤ Y j r := fun j r => by
    rcases hY.binary j r with h | h <;> rw [h] <;> norm_num
  obtain ⟨t, ht⟩ := binary_sum_one (fun r => Y (Fin.last J) r) (fun r => hY.binary _ r)
    hY.emergency_once
  have hIio : ∀ r : Fin (R + 1), ∑ s ∈ Iio r, Y (Fin.last J) s = if t < r then 1 else 0 := by
    intro r; simp only [ht, Finset.sum_ite_eq', mem_Iio]
  have hrow : ∀ r : Fin (R + 1), r ≤ t → ∃ j0, ∀ j, Y j r = if j = j0 then 1 else 0 := by
    intro r hr
    have h1 := hY.level_one r
    rw [hIio, if_neg (not_lt.mpr hr), add_zero] at h1
    exact binary_sum_one (fun j => Y j r) (fun j => hY.binary j r) h1
  have hrow_gt : ∀ r : Fin (R + 1), t < r → ∀ j, Y j r = 0 := by
    intro r hr j
    have h1 := hY.level_one r
    rw [hIio, if_pos hr] at h1
    have h0 : ∑ j, Y j r = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j r)).mp h0 j (mem_univ _)
  have hreg : ∀ r : Fin (R + 1), r < t →
      ∃ k : Fin J, ∀ j, Y j r = if j = k.castSucc then 1 else 0 := by
    intro r hr
    obtain ⟨j0, hj0⟩ := hrow r hr.le
    have hne : j0 ≠ Fin.last J := by
      intro e
      have := hj0 (Fin.last J)
      rw [ht, if_neg (ne_of_lt hr), if_pos e.symm] at this
      norm_num at this
    refine ⟨j0.castPred hne, fun j => ?_⟩
    rw [hj0 j, Fin.castSucc_castPred]
  choose kf hkf using hreg
  have hiR : ∀ i : Fin (t : ℕ), (i : ℕ) < R := fun i => by
    have := i.isLt; have := t.isLt; omega
  have hit : ∀ i : Fin (t : ℕ), (⟨i, by have := hiR i; omega⟩ : Fin (R + 1)) < t := fun i => by
    rw [Fin.lt_def]; exact i.isLt
  let k : Fin (t : ℕ) → Fin J := fun i => kf ⟨i, by have := hiR i; omega⟩ (hit i)
  have hk : ∀ i : Fin (t : ℕ), Y (k i).castSucc (⟨i, hiR i⟩ : Fin R).castSucc = 1 := by
    intro i
    have := hkf ⟨i, by have := hiR i; omega⟩ (hit i) (k i).castSucc
    rw [if_pos rfl] at this
    exact this
  refine ⟨List.ofFn k, ?_, ?_, ?_⟩
  · rw [List.nodup_ofFn]
    intro i i' e
    have h1 := hk i
    have h2 := hk i'
    rw [← e] at h2
    have := binary_le_one_unique (fun r : Fin R => Y (k i).castSucc r.castSucc)
      (fun r => hY.binary _ _) (hY.regular_once (k i)) ⟨i, hiR i⟩ ⟨i', hiR i'⟩ h1 h2
    ext
    simpa using congrArg Fin.val this
  · simp only [List.length_ofFn]
    have := t.isLt; omega
  · funext j r
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · rw [mat_last, ht r]
      simp [Fin.ext_iff]
    · rw [mat_cs]
      rcases lt_trichotomy r t with hlt | heq | hgt
      · have hr : (r : ℕ) < (List.ofFn k).length := by simpa using hlt
        rw [dif_pos hr, List.getElem_ofFn, hkf r hlt j'.castSucc]
        show (if j'.castSucc = (kf r hlt).castSucc then (1 : ℝ) else 0)
          = if kf r hlt = j' then 1 else 0
        simp [Fin.castSucc_inj, eq_comm]
      · subst heq
        rw [dif_neg (by simp)]
        obtain ⟨j0, hj0⟩ := hrow r le_rfl
        have hlast := hj0 (Fin.last J)
        rw [ht, if_pos rfl] at hlast
        have hj0l : j0 = Fin.last J := by
          by_contra hc
          rw [if_neg (Ne.symm hc)] at hlast
          norm_num at hlast
        rw [hj0, hj0l, if_neg (Fin.castSucc_ne_last j')]
      · rw [dif_neg (by simp; exact le_of_lt hgt), hrow_gt r hgt]

end RRSPProof

open Finset ReliableFacilityLoc.RRSP in
theorem solution {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1)
    (hmu : ∀ j, 0 ≤ mu j) (hR : 1 ≤ R) (σ : Fin J ≃ Fin J) (hσ : IsQOrdering q σ)
    (Y P W : Fin (J + 1) → Fin (R + 1) → ℝ) (h : IsRSPFeasible q Y P W) :
    ∃ Y' : Fin (J + 1) → Fin (R + 1) → ℝ, IsLevelAssignment Y' ∧
      rrspObjective lam d phi q mu σ Y' ≤ rspObjective lam d phi mu Y W := by
  obtain ⟨hY, hlin⟩ := h
  obtain ⟨L, hnd, hlen, rfl⟩ := RRSPProof.extract Y hY
  have hq1' : ∀ j, q j ≤ 1 := fun j => (hq1 j).le
  have : Std.Total (fun a b : Fin J => d a ≤ d b) := ⟨fun a b => le_total _ _⟩
  have : IsTrans (Fin J) (fun a b : Fin J => d a ≤ d b) := ⟨fun _ _ _ => le_trans⟩
  have hperm := List.perm_insertionSort (fun a b : Fin J => d a ≤ d b)
    (L.filter (fun k => decide (d k < phi)))
  have hMnd := hperm.nodup_iff.mpr (hnd.filter _)
  have hMlen : ((L.filter (fun k => decide (d k < phi))).insertionSort
      (fun a b : Fin J => d a ≤ d b)).length ≤ R := by
    rw [hperm.length_eq]; exact (List.length_filter_le _ _).trans hlen
  refine ⟨RRSPProof.mat R ((L.filter (fun k => decide (d k < phi))).insertionSort
      (fun a b : Fin J => d a ≤ d b)), RRSPProof.isLevel_mat _ hMnd hMlen, ?_⟩
  rw [RRSPProof.rrsp_mat lam d phi q mu σ _ hMlen,
    RRSPProof.rsp_mat lam d phi q mu hq1 L hlen P W hlin]
  have h1 := RRSPProof.cP_le_cQ d phi q σ hq0 hσ _ hMnd
    (List.pairwise_insertionSort _ _) (by
      intro x hx
      rw [List.mem_insertionSort, List.mem_filter] at hx
      have := hx.2
      simp only [decide_eq_true_eq] at this
      exact this.le)
  have h2 := RRSPProof.cQ_sortTrunc d phi q hq0 hq1' L
  have h3 : (((L.filter (fun k => decide (d k < phi))).insertionSort
      (fun a b : Fin J => d a ≤ d b)).map mu).sum ≤ (L.map mu).sum := by
    rw [(hperm.map mu).sum_eq]
    exact RRSPProof.sum_filter_le mu hmu _ L
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hlam]
