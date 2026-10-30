-- Prove2me | solution 1 for ValTrackRM.Public.line8_unreachable
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T05:25:34.720105+00:00
-- url     : https://prove2.me/submissions/5e976700-02c4-4dab-aff4-7c9222283841

import Mathlib
import Definitions.Def_ValTrackRM_Public_Model

open ValTrackRM.Public

namespace VTSol

variable {m k : ℕ}

lemma r_strict (r : ℕ → ℝ) (hr : ∀ j, j < m → r j < r (j + 1)) :
    ∀ a b, a < b → b ≤ m → r a < r b := by
  intro a b
  induction b with
  | zero => intro h; omega
  | succ b ih =>
    intro h hb
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h1 | h1
    · exact (ih h1 (by omega)).trans (hr b (by omega))
    · subst h1; exact hr a (by omega)

lemma r_mono (r : ℕ → ℝ) (hr : ∀ j, j < m → r j < r (j + 1)) :
    ∀ a b, a ≤ b → b ≤ m → r a ≤ r b := by
  intro a b h hb
  rcases h.lt_or_eq with h | h
  · exact (r_strict r hr a b h hb).le
  · rw [h]

lemma r_le_iff (r : ℕ → ℝ) (hr : ∀ j, j < m → r j < r (j + 1)) (a b : ℕ) (ha : a ≤ m)
    (hb : b ≤ m) : r a ≤ r b ↔ a ≤ b := by
  constructor
  · intro h; by_contra h'; push Not at h'
    exact absurd h (not_le.mpr (r_strict r hr b a h' ha))
  · intro h; exact r_mono r hr a b h hb

lemma r_pos (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (j : ℕ)
    (h1 : 1 ≤ j) (h2 : j ≤ m) : 0 < r j := by
  have := r_strict r hr 0 j (by omega) h2
  rwa [hr0] at this

lemma r_nonneg (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (j : ℕ)
    (h2 : j ≤ m) : 0 ≤ r j := by
  have := r_mono r hr 0 j (by omega) h2
  rwa [hr0] at this

lemma qj_pos (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (p : ℕ)
    (h1 : 1 ≤ p) (h2 : p ≤ m) : 0 < qj r p := by
  unfold qj
  have hp := r_pos r hr0 hr p h1 h2
  have hlt := r_strict r hr (p - 1) p (by omega) h2
  have : r (p - 1) / r p < 1 := (div_lt_one hp).mpr hlt
  linarith

lemma qj_mul (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (p : ℕ)
    (h1 : 1 ≤ p) (h2 : p ≤ m) : qj r p * r p = r p - r (p - 1) := by
  unfold qj
  have hp := r_pos r hr0 hr p h1 h2
  field_simp

lemma sum_Icc_eq_Ioc (f : ℕ → ℝ) (n : ℕ) : ∑ j ∈ Finset.Icc 1 n, f j = ∑ j ∈ Finset.Ioc 0 n, f j := by
  rfl

lemma qSum_split (r : ℕ → ℝ) (ℓ : ℕ) (hℓ : ℓ ≤ m) :
    qSum r m = ∑ j ∈ Finset.Icc 1 ℓ, qj r j + qTot r m ℓ := by
  unfold qSum qTot
  rw [sum_Icc_eq_Ioc, sum_Icc_eq_Ioc, Finset.sum_Ioc_consecutive _ (Nat.zero_le ℓ) hℓ]

lemma qTot_pos (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (ℓ : ℕ)
    (hℓ : ℓ < m) : 0 < qTot r m ℓ := by
  unfold qTot
  apply Finset.sum_pos
  · intro p hp; simp at hp; exact qj_pos r hr0 hr p (by omega) (by omega)
  · exact ⟨m, by simp; omega⟩

lemma qSum_pos (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (hm : 1 ≤ m) :
    0 < qSum r m := by
  have := qSum_split (m := m) r 0 (by omega)
  have h2 := qTot_pos r hr0 hr 0 (by omega)
  simp at this; linarith

/-- offer probabilities against an indicator of `p ≤ j`. -/
lemma sum_offer_ind (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1))
    (ℓ j : ℕ) (hℓ : ℓ < m) (hj : j ≤ m) (c : ℕ → ℝ) :
    ∑ p ∈ Finset.Ioc ℓ m, offerProb r m ℓ p * (if r p ≤ r j then c p else 0) =
      (∑ p ∈ Finset.Ioc ℓ j, qj r p * c p) / qTot r m ℓ := by
  unfold offerProb
  rw [Finset.sum_div]
  have : ∀ p ∈ Finset.Ioc ℓ m, qj r p / qTot r m ℓ * (if r p ≤ r j then c p else 0) =
      if p ≤ j then qj r p * c p / qTot r m ℓ else 0 := by
    intro p hp
    simp at hp
    have hiff := r_le_iff r hr p j (by omega) hj
    by_cases h : p ≤ j
    · rw [if_pos (hiff.mpr h), if_pos h]; ring
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]; ring
  rw [Finset.sum_congr rfl this, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p; simp; omega
  · intro _ _; rfl

lemma sum_offer (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1))
    (ℓ : ℕ) (hℓ : ℓ < m) : ∑ p ∈ Finset.Ioc ℓ m, offerProb r m ℓ p = 1 := by
  unfold offerProb
  rw [← Finset.sum_div]
  exact div_self (qTot_pos r hr0 hr ℓ hℓ).ne'

lemma telescope (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1))
    (ℓ j : ℕ) (hj : j ≤ m) (hℓj : ℓ ≤ j) :
    ∑ p ∈ Finset.Ioc ℓ j, qj r p * r p = r j - r ℓ := by
  induction j, hℓj using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn, ih (by omega), qj_mul r hr0 hr (n + 1) (by omega) hj]
    simp

lemma soldLaw_append (r : ℕ → ℝ) (sel : (Fin k → Fin (m + 1)) → Fin k)
    (W : List (Fin (m + 1))) (j : Fin (m + 1)) :
    soldLaw r sel (W ++ [j]) = lawStep r sel (levels sel W) j (soldLaw r sel W) := by
  unfold soldLaw
  simp [soldLawRev]

lemma levels_append (sel : (Fin k → Fin (m + 1)) → Fin k)
    (W : List (Fin (m + 1))) (j : Fin (m + 1)) :
    levels sel (W ++ [j]) = levelStep sel (levels sel W) j := by
  unfold levels
  simp

lemma lawStep_sum (r : ℕ → ℝ) (sel : (Fin k → Fin (m + 1)) → Fin k)
    (L : Fin k → Fin (m + 1)) (j : Fin (m + 1)) (μ : (Fin k → Bool) → ℝ)
    (g : (Fin k → Bool) → ℝ) :
    ∑ s', lawStep r sel L j μ s' * g s' =
      ∑ s, μ s * (if s (sel L) = false ∧ ((L (sel L) : ℕ) < m) then
        ∑ p ∈ Finset.Ioc (L (sel L) : ℕ) m, offerProb r m (L (sel L)) p *
          (if r p ≤ r j then g (Function.update s (sel L) true) else g s)
        else g s) := by
  unfold lawStep
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  split_ifs with h
  · simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 1
    split_ifs <;> simp
  · simp

/-- `F ℓ = (1/q) ∑_{j=1}^ℓ q^{(j)}`. -/
noncomputable def F (r : ℕ → ℝ) (m ℓ : ℕ) : ℝ := (1 / qSum r m) * ∑ j ∈ Finset.Icc 1 ℓ, qj r j

lemma one_sub_F (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (hm : 1 ≤ m)
    (ℓ : ℕ) (hℓ : ℓ ≤ m) : 1 - F r m ℓ = qTot r m ℓ / qSum r m := by
  have hq := qSum_pos r hr0 hr hm
  have := qSum_split (m := m) r ℓ hℓ
  unfold F
  field_simp
  linarith

lemma F_max (r : ℕ → ℝ) (ℓ j : ℕ) :
    F r m (max ℓ j) = F r m ℓ + (1 / qSum r m) * ∑ p ∈ Finset.Ioc ℓ j, qj r p := by
  unfold F
  rcases le_total j ℓ with h | h
  · rw [max_eq_left h, Finset.Ioc_eq_empty (by omega)]; simp
  · rw [max_eq_right h, ← mul_add, sum_Icc_eq_Ioc, sum_Icc_eq_Ioc,
      Finset.sum_Ioc_consecutive _ (Nat.zero_le ℓ) h]

lemma mass_split (μ : (Fin k → Bool) → ℝ) (i : Fin k) :
    ∑ s, μ s * (if s i = false then 1 else 0) =
      ∑ s, μ s - ∑ s, μ s * (if s i = true then 1 else 0) := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  cases s i <;> simp

lemma ec1_gen (hm : 1 ≤ m) (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (W : List (Fin (m + 1))) :
    (∑ s, soldLaw r sel W s = 1) ∧
      ∀ i, probSold r sel W i = F r m (levels sel W i) := by
  induction W using List.reverseRecOn with
  | nil =>
    constructor
    · simp [soldLaw, soldLawRev]
    · intro i
      simp only [probSold, soldLaw, soldLawRev, F, levels, List.reverse_nil, List.foldl_nil]
      simp only [Fin.val_zero, Finset.Icc_eq_empty_of_lt (show 1 > 0 by omega), Finset.sum_empty,
        mul_zero]
      apply Finset.sum_eq_zero
      intro x _
      split_ifs with h1 h2 <;> simp_all
  | append_singleton W j ih =>
    obtain ⟨hmass, hps⟩ := ih
    set L := levels sel W with hL
    set i0 := sel L with hi0
    set μ := soldLaw r sel W with hμ
    have hℓm : ((L i0 : ℕ)) ≤ m := Nat.lt_succ_iff.mp (L i0).isLt
    have hjm : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
    constructor
    · have h := lawStep_sum r sel L j μ (fun _ => 1)
      simp only [mul_one, ite_self] at h
      rw [soldLaw_append, h]
      refine (Finset.sum_congr rfl ?_).trans hmass
      intro s _
      by_cases hc : s (sel L) = false ∧ ((L (sel L) : ℕ)) < m
      · rw [if_pos hc, sum_offer r hr0 hr _ hc.2, mul_one]
      · rw [if_neg hc, mul_one]
    · intro i'
      unfold probSold
      rw [soldLaw_append, lawStep_sum, levels_append]
      unfold levelStep
      rw [← hL, ← hi0]
      by_cases hii : i' = i0
      · rw [hii]
        simp only [hi0, Function.update_self, ↓reduceIte]
        have : ∀ s : Fin k → Bool,
            (if s (sel L) = false ∧ ((L (sel L) : ℕ)) < m then
              ∑ p ∈ Finset.Ioc (L (sel L) : ℕ) m, offerProb r m (L (sel L)) p *
                (if r p ≤ r j then (1:ℝ)
                  else (if s (sel L) = true then 1 else 0))
            else (if s (sel L) = true then 1 else 0)) =
            (if s (sel L) = true then 1 else 0) + (if s (sel L) = false then 1 else 0) *
              (if ((L (sel L) : ℕ)) < m then
                ∑ p ∈ Finset.Ioc (L (sel L) : ℕ) m, offerProb r m (L (sel L)) p *
                  (if r p ≤ r j then 1 else 0) else 0) := by
          intro s
          cases hs : s (sel L) <;> by_cases hl : ((L (sel L) : ℕ)) < m <;> simp [hl]
        rw [Finset.sum_congr rfl (fun s _ => by rw [this s])]
        simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
        rw [mass_split, hmass]
        have hps' := hps (sel L)
        unfold probSold at hps'
        rw [hps']
        rw [Fin.coe_max, F_max]
        split_ifs with hl
        · rw [sum_offer_ind r hr0 hr _ _ hl hjm (fun _ => 1), one_sub_F r hr0 hr hm _ hℓm]
          have := qTot_pos r hr0 hr _ hl
          simp only [mul_one, hi0]
          field_simp
        · have : ((L (sel L) : ℕ)) = m := by omega
          rw [this, Finset.Ioc_eq_empty (by omega)]
          simp
      · rw [Function.update_of_ne hii]
        rw [← hps i']
        unfold probSold
        apply Finset.sum_congr rfl
        intro s _
        congr 1
        simp only [Function.update_of_ne hii, ite_self]
        by_cases hc : s (sel L) = false ∧ ((L (sel L) : ℕ)) < m
        · rw [if_pos hc, ← Finset.sum_mul, sum_offer r hr0 hr _ hc.2, one_mul]
        · rw [if_neg hc]

lemma stepRev_formula (hm : 1 ≤ m) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (W : List (Fin (m + 1))) (j : Fin (m + 1)) :
    stepRev r sel W j = (1 / qSum r m) *
      (r (max (levels sel W (sel (levels sel W)) : ℕ) (j : ℕ)) -
        r (levels sel W (sel (levels sel W)))) := by
  obtain ⟨hmass, hps⟩ := ec1_gen hm r hr0 hr sel W
  set L := levels sel W with hL
  set i0 := sel L with hi0
  have hℓm : ((L i0 : ℕ)) ≤ m := Nat.lt_succ_iff.mp (L i0).isLt
  have hjm : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
  unfold stepRev
  rw [← hL, ← hi0]
  have : ∀ s : Fin k → Bool,
      (if s i0 = false ∧ ((L i0 : ℕ)) < m then
        ∑ p ∈ Finset.Ioc (L i0 : ℕ) m, offerProb r m (L i0) p * (if r p ≤ r j then r p else 0)
        else 0) = (if s i0 = false then 1 else 0) * (if ((L i0 : ℕ)) < m then
        ∑ p ∈ Finset.Ioc (L i0 : ℕ) m, offerProb r m (L i0) p * (if r p ≤ r j then r p else 0)
        else 0) := by
    intro s; cases s i0 <;> by_cases hl : ((L i0 : ℕ)) < m <;> simp [hl]
  rw [Finset.sum_congr rfl (fun s _ => by rw [this s])]
  simp only [← mul_assoc, ← Finset.sum_mul]
  rw [mass_split, hmass]
  have hps' := hps i0
  unfold probSold at hps'
  rw [hps']
  split_ifs with hl
  · rw [sum_offer_ind r hr0 hr _ _ hl hjm (fun p => r p), one_sub_F r hr0 hr hm _ hℓm]
    have := qTot_pos r hr0 hr _ hl
    rcases le_total (j : ℕ) (L i0 : ℕ) with h | h
    · rw [max_eq_left h, Finset.Ioc_eq_empty (by omega)]
      simp
    · rw [max_eq_right h, telescope r hr0 hr _ _ hjm h]
      field_simp
  · have : ((L i0 : ℕ)) = m := by omega
    rw [this, max_eq_left (by omega)]
    simp

theorem sol_EC1 {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) (t : ℕ) (ht : t ≤ V.length) (i : Fin k) :
    probSold r sel (V.take t) i =
      (1 / qSum r m) * ∑ j ∈ Finset.Icc 1 (levels sel (V.take t) i : ℕ), qj r j :=
  (ec1_gen hm r hr0 hr sel _).2 i

theorem sol_line8 {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) (t : ℕ) (ht : t ≤ V.length) (i : Fin k)
    (hi : levels sel (V.take t) i = Fin.last m) :
    probSold r sel (V.take t) i = 1 := by
  rw [(ec1_gen hm r hr0 hr sel _).2 i, hi]
  unfold F
  simp only [Fin.val_last]
  exact one_div_mul_cancel (qSum_pos r hr0 hr hm).ne'

theorem sol_EC2 {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) (t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ V.length) :
    (((levels sel (V.take (t - 1)) (assigned sel V t) : ℕ) < (valIdx V t : ℕ)) →
      stepRevenue r sel V t =
        (1 / qSum r m) * (r (valIdx V t) - r (levels sel (V.take (t - 1)) (assigned sel V t)))) ∧
    (((valIdx V t : ℕ) ≤ (levels sel (V.take (t - 1)) (assigned sel V t) : ℕ)) →
      stepRevenue r sel V t = 0) := by
  unfold stepRevenue assigned
  rw [stepRev_formula hm r hr0 hr]
  constructor
  · intro h
    rw [max_eq_right h.le]
  · intro h
    rw [max_eq_left h]
    simp

lemma sum_update_r (r : ℕ → ℝ) (L : Fin k → Fin (m + 1)) (i0 : Fin k) (x : Fin (m + 1)) :
    ∑ i, r (Function.update L i0 x i) = ∑ i, r (L i) - r (L i0) + r x := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
    ← Finset.add_sum_erase _ (fun i => r (L i)) (Finset.mem_univ i0)]
  simp only [Function.update_self]
  have : ∑ i ∈ Finset.univ.erase i0, r (Function.update L i0 x i) =
      ∑ i ∈ Finset.univ.erase i0, r (L i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [this]; ring

theorem sol_EC3 {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) (t : ℕ) (ht : t ≤ V.length) :
    ∑ t' ∈ Finset.Icc 1 t, stepRevenue r sel V t' =
      (1 / qSum r m) * ∑ i, r (levels sel (V.take t) i) := by
  induction t with
  | zero =>
    simp [levels, hr0]
  | succ t ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
    have htl : t < V.length := by omega
    have htake : V.take (t + 1) = V.take t ++ [V[t]] := by
      rw [List.take_succ, List.getElem?_eq_getElem htl]; rfl
    have hval : valIdx V (t + 1) = V[t] := by
      simp [valIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl]
    unfold stepRevenue
    simp only [Nat.add_sub_cancel]
    rw [hval, stepRev_formula hm r hr0 hr, htake, levels_append]
    unfold levelStep
    rw [sum_update_r, Fin.coe_max]
    ring

end VTSol

namespace VTSolB

variable {m k : ℕ}

lemma r_strict (r : ℕ → ℝ) (hr : ∀ j, j < m → r j < r (j + 1)) :
    ∀ a b, a < b → b ≤ m → r a < r b := by
  intro a b
  induction b with
  | zero => intro h; omega
  | succ b ih =>
    intro h hb
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h1 | h1
    · exact (ih h1 (by omega)).trans (hr b (by omega))
    · subst h1; exact hr a (by omega)

lemma r_mono (r : ℕ → ℝ) (hr : ∀ j, j < m → r j < r (j + 1)) :
    ∀ a b, a ≤ b → b ≤ m → r a ≤ r b := by
  intro a b h hb
  rcases h.lt_or_eq with h | h
  · exact (r_strict r hr a b h hb).le
  · rw [h]

lemma r_nonneg (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1)) (j : ℕ)
    (h2 : j ≤ m) : 0 ≤ r j := by
  have := r_mono r hr 0 j (by omega) h2
  rwa [hr0] at this

lemma levels_append (sel : (Fin k → Fin (m + 1)) → Fin k)
    (W : List (Fin (m + 1))) (j : Fin (m + 1)) :
    levels sel (W ++ [j]) = levelStep sel (levels sel W) j := by
  unfold levels
  simp

/-- `T` is a top-`k` sub-multiset of `X`. -/
def IsTopK (T X : Multiset ℝ) (k : ℕ) : Prop :=
  Multiset.card T = k ∧ T ≤ X ∧ ∀ a ∈ T, ∀ b ∈ X - T, b ≤ a

lemma IsTopK.unique {T1 T2 X : Multiset ℝ} {k : ℕ} (h1 : IsTopK T1 X k) (h2 : IsTopK T2 X k) :
    T1 = T2 := by
  by_contra hne
  have hn12 : ¬ T1 ≤ T2 := fun h =>
    hne (Multiset.eq_of_le_of_card_le h (by rw [h1.1, h2.1]))
  have hn21 : ¬ T2 ≤ T1 := fun h =>
    hne (Multiset.eq_of_le_of_card_le h (by rw [h1.1, h2.1])).symm
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero (fun h => hn12 (tsub_eq_zero_iff_le.mp h))
  obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero (fun h => hn21 (tsub_eq_zero_iff_le.mp h))
  have hab : a ≤ b := h2.2.2 b (Multiset.mem_of_le tsub_le_self hb) a
    (Multiset.mem_of_le (tsub_le_tsub_right h1.2.1 _) ha)
  have hba : b ≤ a := h1.2.2 a (Multiset.mem_of_le tsub_le_self ha) b
    (Multiset.mem_of_le (tsub_le_tsub_right h2.2.1 _) hb)
  have := le_antisymm hab hba
  subst this
  rw [Multiset.mem_sub] at ha hb
  omega

lemma sum_le_of_forall (P : Multiset ℝ) :
    ∀ Q : Multiset ℝ, Multiset.card P = Multiset.card Q → (∀ a ∈ P, ∀ b ∈ Q, a ≤ b) →
      P.sum ≤ Q.sum := by
  induction P using Multiset.induction_on with
  | empty =>
    intro Q hc _
    rw [Multiset.card_zero, eq_comm, Multiset.card_eq_zero] at hc
    simp [hc]
  | cons a P ih =>
    intro Q hc hle
    have hQ : Q ≠ 0 := by
      intro h; rw [h] at hc; simp at hc
    obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hQ
    obtain ⟨Q', rfl⟩ := Multiset.exists_cons_of_mem hb
    simp only [Multiset.sum_cons, Multiset.card_cons, add_left_inj] at hc ⊢
    have h1 : a ≤ b := hle a (Multiset.mem_cons_self _ _) b (Multiset.mem_cons_self _ _)
    have h2 := ih Q' hc (fun x hx y hy =>
      hle x (Multiset.mem_cons_of_mem hx) y (Multiset.mem_cons_of_mem hy))
    linarith

lemma IsTopK.sum_le {T X A : Multiset ℝ} {k : ℕ} (hT : IsTopK T X k) (hA : A ≤ X)
    (hcA : Multiset.card A = k) : A.sum ≤ T.sum := by
  have e1 := Multiset.sub_add_inter A T
  have e2 := Multiset.sub_add_inter T A
  rw [Multiset.inter_comm] at e2
  have hc : Multiset.card (A - T) = Multiset.card (T - A) := by
    have c1 := congrArg Multiset.card e1
    have c2 := congrArg Multiset.card e2
    rw [Multiset.card_add] at c1 c2
    have := hT.1
    omega
  have hs := sum_le_of_forall (A - T) (T - A) hc (fun a ha b hb =>
    hT.2.2 b (Multiset.mem_of_le tsub_le_self hb) a
      (Multiset.mem_of_le (tsub_le_tsub_right hA _) ha))
  have s1 := congrArg Multiset.sum e1
  have s2 := congrArg Multiset.sum e2
  rw [Multiset.sum_add] at s1 s2
  linarith

lemma IsTopK.step {x w : ℝ} {R X : Multiset ℝ} {k : ℕ} (h : IsTopK (x ::ₘ R) X k)
    (hmin : ∀ z ∈ R, x ≤ z) : IsTopK (max x w ::ₘ R) (w ::ₘ X) k := by
  obtain ⟨hc, hle, htop⟩ := h
  rcases le_total w x with hw | hw
  · rw [max_eq_left hw]
    refine ⟨hc, hle.trans (Multiset.le_cons_self _ _), ?_⟩
    intro a ha b hb
    have hsub : w ::ₘ X - x ::ₘ R ≤ w ::ₘ (X - x ::ₘ R) := by
      rw [tsub_le_iff_right, Multiset.cons_add, tsub_add_cancel_of_le hle]
    have hb' := Multiset.mem_of_le hsub hb
    rcases Multiset.mem_cons.mp hb' with hb' | hb'
    · subst hb'
      rcases Multiset.mem_cons.mp ha with ha | ha
      · rw [ha]; exact hw
      · exact hw.trans (hmin a ha)
    · exact htop a ha b hb'
  · rw [max_eq_right hw]
    have hRX : R ≤ X := (Multiset.le_cons_self _ _).trans hle
    refine ⟨by simpa using hc, Multiset.cons_le_cons _ hRX, ?_⟩
    intro a ha b hb
    rw [Multiset.sub_cons, Multiset.erase_cons_head] at hb
    have hsub : X - R ≤ x ::ₘ (X - x ::ₘ R) := by
      rw [tsub_le_iff_right, Multiset.cons_add, ← Multiset.add_cons, tsub_add_cancel_of_le hle]
    have hb' := Multiset.mem_of_le hsub hb
    rcases Multiset.mem_cons.mp hb' with hb' | hb'
    · subst hb'
      rcases Multiset.mem_cons.mp ha with ha | ha
      · rw [ha]; exact hw
      · exact hmin a ha
    · have hbx : b ≤ x := htop x (Multiset.mem_cons_self _ _) b hb'
      rcases Multiset.mem_cons.mp ha with ha | ha
      · rw [ha]; exact hbx.trans hw
      · exact htop a (Multiset.mem_cons_of_mem ha) b hb'

/-- the padded valuation multiset -/
noncomputable def Xm (r : ℕ → ℝ) (k : ℕ) (W : List (Fin (m + 1))) : Multiset ℝ :=
  (↑(W.map (fun j : Fin (m + 1) => r j)) : Multiset ℝ) + Multiset.replicate k 0

lemma topK_isTopK (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1))
    (k : ℕ) (W : List (Fin (m + 1))) :
    IsTopK (↑(topK r k W)) (Xm r k W) k := by
  set S := (W.map (fun j : Fin (m + 1) => r j)).mergeSort (fun a b => decide (b ≤ a)) with hS
  set Y := S ++ List.replicate k 0 with hY
  have hperm : (Y : Multiset ℝ) = Xm r k W := by
    unfold Xm
    rw [hY, ← Multiset.coe_add, Multiset.coe_replicate]
    congr 1
    exact Multiset.coe_eq_coe.mpr (List.mergeSort_perm _ _)
  have hSpw : S.Pairwise (fun a b => decide (b ≤ a)) := by
    apply List.pairwise_mergeSort
    · intro a b c h1 h2; simp at h1 h2 ⊢; linarith
    · intro a b; simp; exact le_total b a
  have hpw : Y.Pairwise (fun a b => b ≤ a) := by
    rw [hY, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact hSpw.imp (fun h => by simpa using h)
    · exact List.pairwise_replicate.mpr (Or.inr le_rfl)
    · intro a ha b hb
      rw [List.eq_of_mem_replicate hb]
      have ha' : a ∈ W.map (fun j : Fin (m + 1) => r j) := (List.mergeSort_perm _ _).subset ha
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha'
      exact r_nonneg r hr0 hr j (Nat.lt_succ_iff.mp j.isLt)
  have htk : topK r k W = Y.take k := by
    have hc : ∀ W' : List (Fin (m + 1)),
        List.flatMap (fun a : Fin (m + 1) => [(a : ℕ)]) W' = W'.map Fin.val := by
      intro W'; induction W' with
      | nil => rfl
      | cons a W' ih => rw [List.flatMap_cons, List.map_cons, ih]; rfl
    have hmap : W.map (fun j => r j) = W.map (fun j : Fin (m + 1) => r j) := by
      show List.map r (List.flatMap (fun a : Fin (m + 1) => [(a : ℕ)]) W) = _
      rw [hc, List.map_map]; rfl
    unfold topK
    rw [hmap, hY, hS]
  rw [htk, ← hperm]
  have hsplit : (Y : Multiset ℝ) = ↑(Y.take k) + ↑(Y.drop k) := by
    rw [Multiset.coe_add, List.take_append_drop]
  refine ⟨?_, ?_, ?_⟩
  · simp [hY]
  · rw [hsplit]; exact Multiset.le_add_right _ _
  · intro a ha b hb
    rw [hsplit, add_tsub_cancel_left] at hb
    have := (List.pairwise_append.mp (by rw [List.take_append_drop]; exact hpw :
      (Y.take k ++ Y.drop k).Pairwise (fun a b => b ≤ a))).2.2
    exact this a ha b hb

lemma levels_isTopK (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0) (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k)
    (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (W : List (Fin (m + 1))) :
    IsTopK (Finset.univ.val.map (fun i => r (levels sel W i))) (Xm r k W) k := by
  induction W using List.reverseRecOn with
  | nil =>
    have : Finset.univ.val.map (fun i => r (levels sel ([] : List (Fin (m + 1))) i)) =
        Multiset.replicate k 0 := by
      simp [levels, hr0]
    rw [this]
    refine ⟨by simp, by simp [Xm], ?_⟩
    simp [Xm]
  | append_singleton W j ih =>
    set L := levels sel W with hL
    set i0 := sel L with hi0
    have hu : (Finset.univ : Finset (Fin k)) = insert i0 (Finset.univ.erase i0) := by
      rw [Finset.insert_erase (Finset.mem_univ _)]
    have hnot : i0 ∉ Finset.univ.erase i0 := Finset.notMem_erase _ _
    set R := (Finset.univ.erase i0).val.map (fun i => r (L i)) with hR
    have hM : Finset.univ.val.map (fun i => r (L i)) = r (L i0) ::ₘ R := by
      rw [hu, Finset.insert_val_of_notMem hnot, Multiset.map_cons]
    have hM' : Finset.univ.val.map (fun i => r (levels sel (W ++ [j]) i)) =
        max (r (L i0)) (r j) ::ₘ R := by
      rw [levels_append, hu, Finset.insert_val_of_notMem hnot, Multiset.map_cons]
      unfold levelStep
      rw [← hL, ← hi0, Function.update_self]
      congr 1
      · rw [Fin.coe_max]
        rcases le_total (L i0 : ℕ) (j : ℕ) with h | h
        · rw [max_eq_right h, max_eq_right
            (r_mono r hr _ _ h (Nat.lt_succ_iff.mp j.isLt))]
        · rw [max_eq_left h, max_eq_left
            (r_mono r hr _ _ h (Nat.lt_succ_iff.mp (L i0).isLt))]
      · rw [hR]
        apply Multiset.map_congr rfl
        intro i hi
        rw [Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_def.mpr hi))]
    rw [hM']
    have hX : Xm r k (W ++ [j]) = r j ::ₘ Xm r k W := by
      unfold Xm
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [Multiset.coe_eq_coe.mpr (List.perm_append_singleton _ _)]
      rw [← Multiset.cons_coe, Multiset.cons_add]
    rw [hX]
    rw [hM] at ih
    apply ih.step
    intro z hz
    rw [hR] at hz
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hz
    exact r_mono r hr _ _ (hsel L i) (Nat.lt_succ_iff.mp (L i).isLt)

theorem sol_EC4 {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) (t : ℕ) (ht : t ≤ V.length) :
    (List.ofFn fun i => r (levels sel (V.take t) i)).Perm (topK r k (V.take t)) := by
  rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map]
  exact (levels_isTopK hk r hr0 hr sel hsel _).unique (topK_isTopK r hr0 hr k _)

/-- realize a sub-multiset of an image as the image of a sub-finset. -/
lemma exists_finset_of_le {ι : Type*} [DecidableEq ι] (g : ι → ℝ) (U : Finset ι) :
    ∀ B : Multiset ℝ, B ≤ U.val.map g → ∃ S ⊆ U, S.val.map g = B := by
  induction U using Finset.induction_on with
  | empty =>
    intro B hB
    refine ⟨∅, subset_refl _, ?_⟩
    simp at hB; simp [hB]
  | insert a U ha ih =>
    intro B hB
    rw [Finset.insert_val_of_notMem ha, Multiset.map_cons] at hB
    by_cases hga : g a ∈ B
    · have : B.erase (g a) ≤ U.val.map g := by
        have := Multiset.erase_le_erase (g a) hB
        rwa [Multiset.erase_cons_head] at this
      obtain ⟨S, hS, hSB⟩ := ih _ this
      have haS : a ∉ S := fun h => ha (hS h)
      refine ⟨insert a S, Finset.insert_subset_insert _ hS, ?_⟩
      rw [Finset.insert_val_of_notMem haS, Multiset.map_cons, hSB, Multiset.cons_erase hga]
    · obtain ⟨S, hS, hSB⟩ := ih B ((Multiset.le_cons_of_notMem hga).mp hB)
      exact ⟨S, hS.trans (Finset.subset_insert _ _), hSB⟩

theorem sol_opt {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) :
    opt r k V = (topK r k V).sum := by
  have hT := topK_isTopK r hr0 hr k V
  set g : Fin V.length → ℝ := fun t => r (V.get t) with hg
  have hXg : Xm r k V = Finset.univ.val.map g + Multiset.replicate k 0 := by
    unfold Xm
    rw [Fin.univ_val_map]
    congr 1
    rw [hg]
    congr 1
    apply List.ext_getElem <;> simp
  unfold opt
  apply le_antisymm
  · apply Finset.sup'_le
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    have hA : S.val.map g + Multiset.replicate (k - S.card) 0 ≤ Xm r k V := by
      rw [hXg]
      exact add_le_add (Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.subset_univ _)))
        ((Multiset.replicate_le_replicate _).mpr (by omega))
    have := hT.sum_le hA (by
      rw [Multiset.card_add, Multiset.card_map, Finset.card_val, Multiset.card_replicate]; omega)
    rw [Multiset.sum_coe, Multiset.sum_add, Multiset.sum_replicate, smul_zero, add_zero] at this
    exact this
  · set B := (↑(topK r k V) : Multiset ℝ).filter (· ≠ 0) with hB
    have hBle : B ≤ Finset.univ.val.map g := by
      have h1 : B ≤ (Xm r k V).filter (· ≠ 0) := Multiset.filter_le_filter _ hT.2.1
      rw [hXg, Multiset.filter_add] at h1
      have h2 : (Multiset.replicate k (0:ℝ)).filter (· ≠ 0) = 0 := by
        rw [Multiset.filter_eq_nil]; intro a ha; rw [Multiset.eq_of_mem_replicate ha]; simp
      rw [h2, add_zero] at h1
      exact h1.trans (Multiset.filter_le _ _)
    obtain ⟨S, -, hSB⟩ := exists_finset_of_le g Finset.univ B hBle
    have hcard : S.card ≤ k := by
      have := congrArg Multiset.card hSB
      rw [Multiset.card_map, Finset.card_val] at this
      rw [this, ← hT.1]
      exact Multiset.card_le_card (Multiset.filter_le _ _)
    have hsum : ∑ t ∈ S, r (V.get t) = (topK r k V).sum := by
      have : ∑ t ∈ S, r (V.get t) = (S.val.map g).sum := rfl
      rw [this, hSB, hB, ← Multiset.sum_coe]
      have := Multiset.sum_filter_add_sum_filter_not (· ≠ (0:ℝ)) (s := (↑(topK r k V) : Multiset ℝ))
      have h0 : ((↑(topK r k V) : Multiset ℝ).filter (fun x => ¬ x ≠ 0)).sum = 0 := by
        apply Multiset.sum_eq_zero
        intro x hx
        simpa using (Multiset.mem_filter.mp hx).2
      linarith
    rw [← hsum]
    exact Finset.le_sup' (fun S => ∑ t ∈ S, r (V.get t))
      (by simp [Finset.mem_filter]; exact hcard)

end VTSolB

theorem solution {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) (t : ℕ) (ht : t ≤ V.length) (i : Fin k)
    (hi : levels sel (V.take t) i = Fin.last m) :
    probSold r sel (V.take t) i = 1 :=
  VTSol.sol_line8 hm hk r hr0 hr sel hsel V t ht i hi
