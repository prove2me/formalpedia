-- Prove2me | solution 1 for SublinearChoresMMS.Disposal.lemma_3_2_steps_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T09:22:36.018171+00:00
-- url     : https://prove2.me/submissions/26fcae86-7867-452d-89cd-5cd3519ba540

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Slots
import Definitions.Def_SublinearChoresMMS_Disposal_Prepared
section
noncomputable section

namespace SublinearChoresMMS.Disposal.Dev.L33.PartC

open SublinearChoresMMS.Disposal
open Finset

/-! ### Generic helpers -/

lemma sum_ite_le_of_unique {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (a : ι → ℝ) (b : ℝ) (hb : 0 ≤ b) (huniq : ∀ x y, P x → P y → x = y)
    (ha : ∀ x, P x → a x ≤ b) : ∑ x, (if P x then a x else 0) ≤ b := by
  rw [← Finset.sum_filter]
  by_cases h : ∃ x, P x
  · obtain ⟨x, hx⟩ := h
    have : univ.filter P = {x} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun hy => huniq _ _ hy hx, fun hy => hy ▸ hx⟩
    rw [this, sum_singleton]
    exact ha x hx
  · push_neg at h
    have : univ.filter P = ∅ := by
      ext y
      simp [h y]
    rw [this, sum_empty]
    exact hb

lemma card_filter_div_le {α : Type*} (S : Finset α) (f : α → ℕ) (hf : Set.InjOn f S)
    (d s : ℕ) (hd : 0 < d) : (S.filter (fun g => f g / d = s)).card ≤ d := by
  calc (S.filter (fun g => f g / d = s)).card ≤ (Ico (s * d) (s * d + d)).card := by
        apply card_le_card_of_injOn f
        · intro g hg
          simp only [coe_filter, Set.mem_setOf_eq] at hg
          simp only [coe_Ico, Set.mem_Ico]
          have h1 := Nat.div_add_mod (f g) d
          have h2 := Nat.mod_lt (f g) hd
          rw [hg.2] at h1
          constructor
          · rw [Nat.mul_comm]; omega
          · rw [Nat.mul_comm]; omega
        · exact hf.mono (fun x hx => (mem_filter.mp hx).1)
    _ = d := by simp

/-! ### Positions -/

lemma position_le_val {m : ℕ} (S : Finset (Fin m)) (g : Fin m) : position S g ≤ g.val := by
  unfold position
  calc (S.filter (fun x => x.val < g.val)).card ≤ (Iio g).card := by
        apply card_le_card
        intro x hx
        simp only [mem_filter] at hx
        rw [mem_Iio]
        exact Fin.lt_iff_val_lt_val.mpr hx.2
    _ = g.val := Fin.card_Iio g

lemma position_mono {m : ℕ} (S : Finset (Fin m)) {g h : Fin m} (hgh : g ≤ h) :
    position S g ≤ position S h := by
  unfold position
  apply card_le_card
  intro x hx
  simp only [mem_filter] at hx ⊢
  have := Fin.le_iff_val_le_val.mp hgh
  exact ⟨hx.1, by omega⟩

lemma position_lt {m : ℕ} (S : Finset (Fin m)) {g h : Fin m} (hg : g ∈ S) (hgh : g < h) :
    position S g < position S h := by
  unfold position
  apply card_lt_card
  have hgh' := Fin.lt_iff_val_lt_val.mp hgh
  rw [ssubset_iff_of_subset]
  · refine ⟨g, ?_, ?_⟩
    · simp only [mem_filter]; exact ⟨hg, hgh'⟩
    · simp
  · intro x hx
    simp only [mem_filter] at hx ⊢
    exact ⟨hx.1, by omega⟩

lemma position_injOn {m : ℕ} (S : Finset (Fin m)) : Set.InjOn (position S) S := by
  intro g hg h hh he
  rcases lt_trichotomy g h with H | H | H
  · exact absurd he (ne_of_lt (position_lt S hg H))
  · exact H
  · exact absurd he.symm (ne_of_lt (position_lt S hh H))

lemma position_lt_card {m : ℕ} (S : Finset (Fin m)) {g : Fin m} (hg : g ∈ S) :
    position S g < S.card := by
  unfold position
  apply card_lt_card
  rw [ssubset_iff_of_subset (filter_subset _ _)]
  exact ⟨g, hg, by simp⟩

lemma position_surj {m : ℕ} (S : Finset (Fin m)) {k : ℕ} (hk : k < S.card) :
    ∃ g ∈ S, position S g = k := by
  have hsub : S.image (position S) ⊆ range S.card := by
    intro x hx
    simp only [mem_image] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact mem_range.mpr (position_lt_card S hg)
  have hcard : (range S.card).card ≤ (S.image (position S)).card := by
    rw [card_range, card_image_of_injOn (position_injOn S)]
  have heq := eq_of_subset_of_card_le hsub hcard
  have hk' : k ∈ S.image (position S) := by rw [heq]; exact mem_range.mpr hk
  simpa using hk'

lemma val_le_K_add_position {m : ℕ} (Z : Finset (Fin m)) (K : ℕ) (hK : Z.card ≤ K)
    (g : Fin m) : g.val ≤ K + position (univ \ Z) g := by
  have h1 : Iio g ⊆ ((univ \ Z).filter (fun x => x.val < g.val)) ∪ Z := by
    intro x hx
    rw [mem_Iio] at hx
    by_cases hxZ : x ∈ Z
    · exact mem_union_right _ hxZ
    · apply mem_union_left
      simp only [mem_filter, mem_sdiff, mem_univ, true_and]
      exact ⟨hxZ, Fin.lt_iff_val_lt_val.mp hx⟩
  have h2 := card_le_card h1
  rw [Fin.card_Iio] at h2
  have h3 := card_union_le ((univ \ Z).filter (fun x => x.val < g.val)) Z
  unfold position
  omega

/-! ### The shift -/

lemma shift_sum_le {m : ℕ} (Z : Finset (Fin m)) (K : ℕ) (hK : Z.card ≤ K) (F w : Fin m → ℝ)
    (hF : ∀ g, 0 ≤ F g) (hw0 : ∀ g, 0 ≤ w g)
    (hw : ∀ e g : Fin m, g.val ≤ e.val → w e ≤ w g) :
    ∑ e, w e * (if e.val < K then 0 else ∑ g : Fin m,
        if g ∉ Z ∧ position (univ \ Z) g = e.val - K then F g else 0)
      ≤ ∑ g, if g ∉ Z then w g * F g else 0 := by
  have step : ∀ e : Fin m, w e * (if e.val < K then 0 else ∑ g : Fin m,
        if g ∉ Z ∧ position (univ \ Z) g = e.val - K then F g else 0) =
      ∑ g : Fin m, if g ∉ Z ∧ e.val = K + position (univ \ Z) g then w e * F g else 0 := by
    intro e
    split_ifs with he
    · rw [mul_zero]
      symm
      apply sum_eq_zero
      intro g _
      rw [if_neg]
      omega
    · rw [mul_sum]
      apply sum_congr rfl
      intro g _
      by_cases hg : g ∉ Z
      · by_cases hp : position (univ \ Z) g = e.val - K
        · rw [if_pos ⟨hg, hp⟩, if_pos ⟨hg, by omega⟩]
        · rw [if_neg (fun h => hp h.2), if_neg (fun h => hp (by omega)), mul_zero]
      · rw [if_neg (fun h => hg h.1), if_neg (fun h => hg h.1), mul_zero]
  rw [sum_congr rfl (fun e _ => step e), sum_comm]
  apply sum_le_sum
  intro g _
  by_cases hg : g ∉ Z
  · rw [if_pos hg]
    apply sum_ite_le_of_unique (fun e : Fin m => g ∉ Z ∧ e.val = K + position (univ \ Z) g)
    · exact mul_nonneg (hw0 g) (hF g)
    · intro x y hx hy
      exact Fin.ext (hx.2.trans hy.2.symm)
    · intro e he
      have := val_le_K_add_position Z K hK g
      exact mul_le_mul_of_nonneg_right (hw e g (by omega)) (hF g)
  · rw [if_neg hg]
    apply le_of_eq
    apply sum_eq_zero
    intro e _
    rw [if_neg]
    exact fun h => hg h.1

/-! ### Basic facts about the definitions -/

section basic

variable {n m q : ℕ}

def slotIdx (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) : ℕ :=
  if t.val + 1 = n / q then position (G P t) g / denominator n q t else g.val / q

lemma rawSlot_eq (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) (s : ℕ) :
    rawSlot P t g s = if s = slotIdx P t g then rawBase P t g else 0 := rfl

lemma slotIdx_le (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) : slotIdx P t g ≤ g.val := by
  unfold slotIdx
  split_ifs
  · exact (Nat.div_le_self _ _).trans (position_le_val _ _)
  · exact Nat.div_le_self _ _

lemma rawBase_nonneg (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) : 0 ≤ rawBase P t g := by
  unfold rawBase
  split_ifs <;> positivity

lemma rawSlot_nonneg (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) (s : ℕ) :
    0 ≤ rawSlot P t g s := by
  rw [rawSlot_eq]
  split_ifs
  · exact rawBase_nonneg _ _ _
  · exact le_rfl

lemma rawSlot_sum (P : Labels n m q) (t : Fin (n / q)) (g : Fin m) :
    ∑ s : Fin (m + 1), rawSlot P t g s.val = rawBase P t g := by
  have hk : slotIdx P t g < m + 1 := by
    have := slotIdx_le P t g
    have := g.isLt
    omega
  simp only [rawSlot_eq]
  rw [sum_eq_single ⟨slotIdx P t g, hk⟩]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext h)
  · intro h
    exact absurd (mem_univ _) h

lemma card_Z_le_K {R : Finset (Fin n)} (p : Packings n m q R) (i : Ordinary R) :
    (Z (p i)).card ≤ K p := by
  unfold K
  exact le_sup (f := fun i => (Z (p i)).card) (mem_univ i)

lemma G_unique (P : Labels n m q) {t t' : Fin (n / q)} {e : Fin m} (h : e ∈ G P t)
    (h' : e ∈ G P t') : t = t' := by
  unfold G at h h'
  simp only [mem_filter, mem_univ, true_and] at h h'
  rw [h] at h'
  exact Fin.ext (Option.some_injective _ h')

/-! ### Blocks and the bound `cost (G t) ≤ denominator` -/

def blk (hdiv : q ∣ m) (e : Fin m) : Fin (m / q) :=
  ⟨e.val / q, Nat.div_lt_div_of_lt_of_dvd hdiv e.isLt⟩

lemma mem_G_iff (P : Labels n m q) (hdiv : q ∣ m) (t : Fin (n / q)) (e : Fin m) :
    e ∈ G P t ↔ (P (blk hdiv e)).map (fun v => min v.val (n / q - 1)) = some t.val := by
  unfold G mergedLabel blk
  simp only [mem_filter, mem_univ, true_and]
  rw [dif_pos (Nat.div_lt_div_of_lt_of_dvd hdiv e.isLt)]

lemma le_rep (c : Cost n m) (i : Fin n) (hanti : Antitone (c i)) (hdiv : q ∣ m) (e : Fin m) :
    c i e ≤ representativeCost c i q (blk hdiv e) := by
  unfold representativeCost blk
  have h : e.val / q * q < m := lt_of_le_of_lt (Nat.div_mul_le_self _ _) e.isLt
  split_ifs with h'
  · apply hanti
    exact Fin.le_iff_val_le_val.mpr (Nat.div_mul_le_self _ _)
  · exact absurd h h'

lemma rep_nonneg (c : Cost n m) (i : Fin n) (hpos : ∀ e, 0 < c i e) (r : Fin (m / q)) :
    0 ≤ representativeCost c i q r := by
  unfold representativeCost
  split_ifs
  · exact (hpos _).le
  · exact le_rfl

lemma bins_sum_le (hq : 0 < q) (hqn : q ≤ n) (t : Fin (n / q)) :
    ∑ v : Fin (binCount n q), (if min v.val (n / q - 1) = t.val then binCapacity n q v else 0)
      ≤ (denominator n q t : ℝ) / q := by
  have hL : 0 < n / q := Nat.div_pos hqn hq
  have hbc : binCount n q ≤ n / q + 1 := by unfold binCount; split_ifs <;> omega
  have hcap0 : ∀ v, 0 ≤ binCapacity n q v := by
    intro v; unfold binCapacity; split_ifs <;> positivity
  have ht := t.isLt
  calc ∑ v : Fin (binCount n q), (if min v.val (n / q - 1) = t.val then binCapacity n q v else 0)
      ≤ ∑ v : Fin (binCount n q), ((if v.val = t.val then binCapacity n q v else 0) +
          (if t.val + 1 = n / q ∧ v.val = n / q then binCapacity n q v else 0)) := by
        apply sum_le_sum
        intro v _
        have hv := v.isLt
        split_ifs <;> first | linarith [hcap0 v] | (exfalso; omega)
    _ = (∑ v : Fin (binCount n q), (if v.val = t.val then binCapacity n q v else 0)) +
          ∑ v : Fin (binCount n q),
            (if t.val + 1 = n / q ∧ v.val = n / q then binCapacity n q v else 0) :=
        sum_add_distrib
    _ ≤ 1 + (if t.val + 1 = n / q then ((n % q : ℕ) : ℝ) / q else 0) := by
        apply add_le_add
        · apply sum_ite_le_of_unique (fun v : Fin (binCount n q) => v.val = t.val)
          · exact zero_le_one
          · intro x y hx hy; exact Fin.ext (hx.trans hy.symm)
          · intro v hv
            unfold binCapacity
            rw [if_pos (by omega)]
        · by_cases hlast : t.val + 1 = n / q
          · rw [if_pos hlast]
            apply sum_ite_le_of_unique
              (fun v : Fin (binCount n q) => t.val + 1 = n / q ∧ v.val = n / q)
            · positivity
            · intro x y hx hy; exact Fin.ext (hx.2.trans hy.2.symm)
            · intro v hv
              unfold binCapacity
              rw [if_neg (by omega)]
          · rw [if_neg hlast]
            apply le_of_eq
            apply sum_eq_zero
            intro v _
            rw [if_neg]
            exact fun h => hlast h.1
    _ = (denominator n q t : ℝ) / q := by
        have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
        unfold denominator
        split_ifs
        · push_cast
          rw [add_div, div_self hq']
        · push_cast
          rw [add_zero, add_zero, div_self hq']

lemma cost_G_le (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m) (c : Cost n m) (i : Fin n)
    (hpos : ∀ e, 0 < c i e) (hanti : Antitone (c i)) (P : Labels n m q)
    (hP : ValidPacking c i P) (t : Fin (n / q)) :
    ∑ e ∈ G P t, c i e ≤ (denominator n q t : ℝ) := by
  classical
  have s1 : ∑ e ∈ G P t, c i e ≤ ∑ e : Fin m,
      (if (P (blk hdiv e)).map (fun v => min v.val (n / q - 1)) = some t.val then
        representativeCost c i q (blk hdiv e) else 0) := by
    rw [← sum_filter]
    have : univ.filter (fun e =>
        (P (blk hdiv e)).map (fun v => min v.val (n / q - 1)) = some t.val) = G P t := by
      ext e
      simp [mem_G_iff P hdiv]
    rw [this]
    exact sum_le_sum (fun e _ => le_rep c i hanti hdiv e)
  have s2 : ∑ e : Fin m,
      (if (P (blk hdiv e)).map (fun v => min v.val (n / q - 1)) = some t.val then
        representativeCost c i q (blk hdiv e) else 0)
      ≤ ∑ b : Fin (m / q), (q : ℝ) *
        (if (P b).map (fun v => min v.val (n / q - 1)) = some t.val then
          representativeCost c i q b else 0) := by
    rw [← sum_fiberwise univ (blk hdiv)]
    apply sum_le_sum
    intro b _
    rw [sum_congr rfl (g := fun _ => if (P b).map (fun v => min v.val (n / q - 1)) = some t.val
        then representativeCost c i q b else 0)
      (by intro e he; simp only [mem_filter] at he; rw [he.2])]
    rw [sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by split_ifs; exact rep_nonneg c i hpos b; exact le_rfl)
    have hset : univ.filter (fun e => blk hdiv e = b) =
        univ.filter (fun e : Fin m => e.val / q = b.val) := by
      ext e
      simp [blk, Fin.ext_iff]
    have : (univ.filter (fun e => blk hdiv e = b)).card ≤ q := by
      rw [hset]
      exact card_filter_div_le univ (fun e : Fin m => e.val) (fun x _ y _ h => Fin.ext h) q b.val hq
    exact_mod_cast this
  have s3 : ∑ b : Fin (m / q),
      (if (P b).map (fun v => min v.val (n / q - 1)) = some t.val then
        representativeCost c i q b else 0)
      ≤ ∑ v : Fin (binCount n q),
        (if min v.val (n / q - 1) = t.val then binCapacity n q v else 0) := by
    have e1 : ∀ b, (if (P b).map (fun v => min v.val (n / q - 1)) = some t.val then
        representativeCost c i q b else 0) =
        ∑ v : Fin (binCount n q), if P b = some v then
          (if min v.val (n / q - 1) = t.val then representativeCost c i q b else 0) else 0 := by
      intro b
      cases hPb : P b with
      | none => simp
      | some v0 => simp [eq_comm]
    rw [sum_congr rfl (fun b _ => e1 b), sum_comm]
    apply sum_le_sum
    intro v _
    split_ifs with hv
    · exact hP.2 v
    · simp [hv]
  calc ∑ e ∈ G P t, c i e ≤ _ := s1
    _ ≤ _ := s2
    _ = (q : ℝ) * ∑ b : Fin (m / q),
        (if (P b).map (fun v => min v.val (n / q - 1)) = some t.val then
          representativeCost c i q b else 0) := by rw [mul_sum]
    _ ≤ (q : ℝ) * ((denominator n q t : ℝ) / q) :=
        mul_le_mul_of_nonneg_left (s3.trans (bins_sum_le hq hqn t)) (by positivity)
    _ = denominator n q t := by
        have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
        field_simp

end basic

/-! ## Part C: prepared bundles and their shifted slots -/

theorem prop_le_one {n m : ℕ} (hn : 0 < n) (c : Cost n m) (hc : Normalized c) (i : Fin n) :
    propShare c i ≤ 1 := by
  have hmu := hc.2.2 i
  unfold mu costShare at hmu
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : LittleCharity.MMS.mms (fun S => -∑ e ∈ S, c i e) n univ ≤ -(cost c i univ / n) := by
    unfold LittleCharity.MMS.mms
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    apply ciSup_le
    intro f
    obtain ⟨j, -, hj⟩ := exists_le_of_sum_le (s := univ)
      (f := fun _ : Fin n => cost c i univ / n)
      (g := fun j => ∑ e ∈ univ.filter (fun g => f g = j), c i e) univ_nonempty (by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [sum_fiberwise]
        have : (n : ℝ) * (cost c i univ / n) = cost c i univ := by field_simp
        rw [this]
        rfl)
    have hj' : cost c i univ / n ≤ ∑ e ∈ univ.filter (fun g => f g = j), c i e := hj
    calc _ ≤ -∑ e ∈ univ.filter (fun g => f g = j), c i e := ciInf_le (Set.finite_range _).bddBelow j
      _ ≤ _ := by linarith
  unfold propShare
  linarith

theorem fc_shiftedBase_le_one {n m q : ℕ} (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (i : Ordinary R) (t : Fin (n / q)) :
    fractionalCost c i.val (shiftedBase p i t) ≤ 1 := by
  have hcpos := hc.1 i.val
  have hanti : Antitone (c i.val) := (hc.2.1 i.val).antitone
  have hd : (0 : ℝ) < denominator n q t := by
    unfold denominator; exact_mod_cast (by omega : 0 < q + if t.val + 1 = n / q then n % q else 0)
  unfold fractionalCost shiftedBase
  refine (shift_sum_le (Z (p i)) (K p) (card_Z_le_K p i) (rawBase (p i) t) (c i.val)
    (rawBase_nonneg _ _) (fun g => (hcpos g).le)
    (fun e g h => hanti (Fin.le_iff_val_le_val.mpr h))).trans ?_
  calc ∑ g, (if g ∉ Z (p i) then c i.val g * rawBase (p i) t g else 0)
      ≤ ∑ g, (if g ∈ G (p i) t then c i.val g / denominator n q t else 0) := by
        apply sum_le_sum
        intro g _
        by_cases hZ : g ∈ Z (p i)
        · rw [if_neg (not_not.mpr hZ)]
          split_ifs
          · exact div_nonneg (hcpos g).le hd.le
          · exact le_rfl
        · rw [if_pos hZ]
          unfold rawBase
          by_cases hG : g ∈ G (p i) t
          · rw [if_pos ⟨hZ, hG⟩, if_pos hG, mul_one_div]
          · rw [if_neg (fun h => hG h.2), if_neg hG, mul_zero]
    _ = (∑ g ∈ G (p i) t, c i.val g) / denominator n q t := by
        rw [sum_ite_mem, univ_inter, sum_div]
    _ ≤ 1 := by
        rw [div_le_one hd]
        exact cost_G_le hq hqn hdiv c i.val hcpos hanti (p i) (hp i) t

theorem shiftedSlot_nonneg {n m q : ℕ} {R : Finset (Fin n)} (p : Packings n m q R)
    (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) (s : ℕ) : 0 ≤ shiftedSlot p i t e s := by
  unfold shiftedSlot
  split_ifs
  · exact le_rfl
  · apply sum_nonneg
    intro g _
    split_ifs
    · exact rawSlot_nonneg _ _ _ _
    · exact le_rfl

theorem shiftedSlot_sum_slots {n m q : ℕ} (hq : 0 < q) {R : Finset (Fin n)}
    (p : Packings n m q R) (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) :
    ∑ s : Fin (m + 1), shiftedSlot p i t e s.val = shiftedBase p i t e := by
  unfold shiftedSlot shiftedBase
  by_cases he : e.val < K p
  · simp [he]
  · simp only [if_neg he]
    rw [sum_comm]
    apply sum_congr rfl
    intro g _
    split_ifs
    · exact rawSlot_sum _ _ _
    · simp

end SublinearChoresMMS.Disposal.Dev.L33.PartC
end
end

section
noncomputable section

namespace SublinearChoresMMS.Disposal.Dev.L33.PartAB

open SublinearChoresMMS.Disposal
open Finset

/-! ## Part A: abstract slot rounding (Birkhoff–von Neumann) -/

/-! ## Part B: general unit-slots -/

end SublinearChoresMMS.Disposal.Dev.L33.PartAB
end
end

section
noncomputable section

namespace SublinearChoresMMS.Disposal.Dev.L33.PartD

open SublinearChoresMMS.Disposal
open Finset

section

variable {n m q : ℕ}

/-! ### Elementary facts -/

lemma mem_H {R : Finset (Fin n)} (p : Packings n m q R) (e : Fin m) :
    e ∈ H p ↔ e.val < K p := by
  simp [H]

lemma cost_nonneg (c : Cost n m) (hc : Normalized c) (i : Fin n) (S : Finset (Fin m)) :
    0 ≤ cost c i S :=
  sum_nonneg fun e _ => (hc.1 i e).le

lemma shiftedBase_H {R : Finset (Fin n)} (p : Packings n m q R) (i : Ordinary R)
    (t : Fin (n / q)) {e : Fin m} (he : e ∈ H p) : shiftedBase p i t e = 0 := by
  unfold shiftedBase
  rw [if_pos ((mem_H p e).1 he)]

lemma shiftedBase_nonneg (hq : 0 < q) {R : Finset (Fin n)} (p : Packings n m q R)
    (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) : 0 ≤ shiftedBase p i t e := by
  rw [← PartC.shiftedSlot_sum_slots hq p i t e]
  exact sum_nonneg fun s _ => PartC.shiftedSlot_nonneg p i t e s

lemma denom_ge (hn : 0 < n) (c : Cost n m) (hc : Normalized c) {R : Finset (Fin n)}
    (p : Packings n m q R) (i : Fin n) :
    cost c i (H p) ≤ (n : ℝ) * (1 - propShare c i) + cost c i (H p) := by
  have := PartC.prop_le_one hn c hc i
  have : (0 : ℝ) ≤ n * (1 - propShare c i) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  linarith

lemma tau_nonneg (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (i : Ordinary R) (t : Fin (n / q)) :
    0 ≤ tau c p i t := by
  unfold tau
  apply div_nonneg
  · linarith [PartC.fc_shiftedBase_le_one hq hqn hdiv c hc R p hp i t]
  · exact (cost_nonneg c hc i.val _).trans (denom_ge hn c hc p i.val)

lemma tau_mul_cost (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (i : Ordinary R) (t : Fin (n / q)) :
    tau c p i t * cost c i.val (H p) ≤ 1 - fractionalCost c i.val (shiftedBase p i t) := by
  have hN : 0 ≤ 1 - fractionalCost c i.val (shiftedBase p i t) := by
    linarith [PartC.fc_shiftedBase_le_one hq hqn hdiv c hc R p hp i t]
  have hCD := denom_ge hn c hc p i.val
  have hC := cost_nonneg c hc i.val (H p)
  unfold tau
  rcases eq_or_lt_of_le (hC.trans hCD) with h | h
  · rw [← h, div_zero, zero_mul]
    exact hN
  · rw [div_mul_eq_mul_div, div_le_iff₀ h]
    exact mul_le_mul_of_nonneg_left hCD hN

lemma fc_completed (c : Cost n m) {R : Finset (Fin n)} (p : Packings n m q R)
    (i : Ordinary R) (t : Fin (n / q)) :
    fractionalCost c i.val (completed c p i t) =
      tau c p i t * cost c i.val (H p) + fractionalCost c i.val (shiftedBase p i t) := by
  have hcost : cost c i.val (H p) = ∑ e, if e ∈ H p then c i.val e else 0 := by
    show ∑ e ∈ H p, c i.val e = _
    rw [sum_ite_mem, univ_inter]
  rw [hcost, mul_sum]
  unfold fractionalCost
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  unfold completed
  by_cases he : e ∈ H p
  · rw [if_pos he, if_pos he, shiftedBase_H p i t he]
    ring
  · rw [if_neg he, if_neg he]
    ring

lemma completed_nonneg (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) :
    0 ≤ completed c p i t e := by
  unfold completed
  split_ifs
  · exact tau_nonneg hn hq hqn hdiv c hc R p hp i t
  · exact shiftedBase_nonneg hq p i t e

lemma fc_completed_le_one (hn : 0 < n) (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (p : Packings n m q R)
    (hp : ∀ i, ValidPacking c i.val (p i)) (i : Ordinary R) (t : Fin (n / q)) :
    fractionalCost c i.val (completed c p i t) ≤ 1 := by
  rw [fc_completed]
  linarith [tau_mul_cost hn hq hqn hdiv c hc R p hp i t]

/-! ### Realized fractions -/

/-! ### Slot fractions -/

/-! ### The three hypotheses of the rounding theorem -/

/-! ### Bundles of an integral assignment -/

end

end SublinearChoresMMS.Disposal.Dev.L33.PartD

namespace SublinearChoresMMS.Disposal

open Finset

end SublinearChoresMMS.Disposal
end
end

section
noncomputable section

namespace SublinearChoresMMS.Disposal.Dev.L32.PartX

open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.L33
open Finset

/-! ### Denominators -/

lemma denominator_pos {n q : ℕ} (hq : 0 < q) (t : Fin (n / q)) : 0 < denominator n q t := by
  unfold denominator; omega

lemma q_le_denominator {n q : ℕ} (t : Fin (n / q)) : q ≤ denominator n q t := by
  unfold denominator; omega

lemma sum_denominator_nat {n q : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    (∑ t : Fin (n / q), denominator n q t) = n := by
  have hL : 0 < n / q := Nat.div_pos hqn hq
  unfold denominator
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  rw [sum_eq_single (⟨n / q - 1, by omega⟩ : Fin (n / q))]
  · simp only
    rw [if_pos (by omega)]
    exact Nat.div_add_mod' n q
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by simp; omega))
  · intro h; exact absurd (mem_univ _) h

lemma sum_denominator {n q : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    (∑ t : Fin (n / q), (denominator n q t : ℝ)) = n := by
  rw [← Nat.cast_sum, sum_denominator_nat hq hqn]

theorem eta_sum {n q : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    (∑ t : Fin (n / q), eta n q t) = 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hq hqn)
  unfold eta
  rw [← sum_div, sum_denominator hq hqn, div_self hn.ne']

theorem eta_bounds {n q : ℕ} (hq : 0 < q) (hqn : q ≤ n) (t : Fin (n / q)) :
    (q : ℝ) / n ≤ eta n q t ∧ eta n q t ≤ 2 * q / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hq hqn)
  unfold eta
  constructor
  · apply div_le_div_of_nonneg_right _ hn.le
    exact_mod_cast q_le_denominator t
  · apply div_le_div_of_nonneg_right _ hn.le
    have : denominator n q t ≤ 2 * q := by
      unfold denominator
      have := Nat.mod_lt n hq
      split_ifs <;> omega
    exact_mod_cast this

/-! ### The shifted base -/

lemma sum_denom_rawBase {n m q : ℕ} (hq : 0 < q) (P : Labels n m q) (g : Fin m) (hg : g ∉ Z P) :
    (∑ t : Fin (n / q), (denominator n q t : ℝ) * rawBase P t g) = 1 := by
  have hg' := hg
  unfold Z at hg'
  simp only [mem_filter, mem_univ, true_and, not_not] at hg'
  obtain ⟨t0, ht0, -⟩ := hg'
  rw [sum_eq_single t0]
  · unfold rawBase
    rw [if_pos ⟨hg, ht0⟩]
    have : (0 : ℝ) < denominator n q t0 := by exact_mod_cast denominator_pos hq t0
    field_simp
  · intro t _ ht
    unfold rawBase
    rw [if_neg, mul_zero]
    intro h
    exact ht (PartC.G_unique P h.2 ht0)
  · intro h; exact absurd (mem_univ _) h

theorem denom_shiftedBase {n m q : ℕ} (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m)
    {R : Finset (Fin n)} (p : Packings n m q R) (i : Ordinary R) (e : Fin m)
    (he : K p ≤ e.val) :
    (∑ t : Fin (n / q), (denominator n q t : ℝ) * shiftedBase p i t e) = 1 := by
  classical
  unfold shiftedBase
  simp only [if_neg (show ¬ e.val < K p by omega)]
  simp_rw [mul_sum]
  rw [sum_comm]
  have hcardZ := PartC.card_Z_le_K p i
  have hS : e.val - K p < (univ \ Z (p i)).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    have := e.isLt
    omega
  obtain ⟨g0, hg0, hpos0⟩ := PartC.position_surj _ hS
  have hg0Z : g0 ∉ Z (p i) := by simpa using hg0
  rw [sum_eq_single g0]
  · simp_rw [mul_ite, mul_zero]
    rw [← sum_denom_rawBase hq (p i) g0 hg0Z]
    apply sum_congr rfl
    intro t _
    rw [if_pos ⟨hg0Z, hpos0⟩]
  · intro g _ hg
    apply sum_eq_zero
    intro t _
    rw [if_neg, mul_zero]
    rintro ⟨hgZ, hgpos⟩
    apply hg
    apply PartC.position_injOn (univ \ Z (p i)) (by simpa using hgZ) hg0
    rw [hgpos, hpos0]
  · intro h; exact absurd (mem_univ _) h

/-! ### Completed bundles -/

section completed

variable {n m q : ℕ}

lemma sum_denom_fc (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m) (c : Cost n m)
    {R : Finset (Fin n)} (p : Packings n m q R) (i : Ordinary R) :
    (∑ t : Fin (n / q), (denominator n q t : ℝ) * fractionalCost c i.val (shiftedBase p i t)) =
      cost c i.val univ - cost c i.val (H p) := by
  classical
  unfold fractionalCost
  have h1 : ∀ t : Fin (n / q), (denominator n q t : ℝ) * ∑ e, c i.val e * shiftedBase p i t e =
      ∑ e, c i.val e * ((denominator n q t : ℝ) * shiftedBase p i t e) := by
    intro t; rw [mul_sum]; apply sum_congr rfl; intro e _; ring
  simp_rw [h1]
  rw [sum_comm]
  simp_rw [← mul_sum]
  have h2 : ∀ e : Fin m, c i.val e * (∑ t : Fin (n / q),
      (denominator n q t : ℝ) * shiftedBase p i t e) = if e ∈ H p then 0 else c i.val e := by
    intro e
    split_ifs with he
    · simp [PartD.shiftedBase_H p i _ he]
    · rw [denom_shiftedBase hq hqn hdiv p i e (by rw [PartD.mem_H] at he; omega), mul_one]
  simp_rw [h2]
  have h3 : cost c i.val univ = ∑ e, c i.val e := rfl
  have h4 : cost c i.val (H p) = ∑ e, if e ∈ H p then c i.val e else 0 := by
    show ∑ e ∈ H p, c i.val e = _
    rw [sum_ite_mem, univ_inter]
  rw [h3, h4, eq_sub_iff_add_eq, ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  split_ifs <;> ring

/-- The normalising denominator of `tau` equals `Σ_s d_s (1 - fc(sb_s))`. -/
lemma D_eq (hq : 0 < q) (hqn : q ≤ n) (hdiv : q ∣ m) (c : Cost n m)
    {R : Finset (Fin n)} (p : Packings n m q R) (i : Ordinary R) :
    (n : ℝ) * (1 - propShare c i.val) + cost c i.val (H p) =
      ∑ t : Fin (n / q), (denominator n q t : ℝ) *
        (1 - fractionalCost c i.val (shiftedBase p i t)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hq hqn)
  simp_rw [mul_sub, mul_one]
  rw [sum_sub_distrib, sum_denominator hq hqn, sum_denom_fc hq hqn hdiv c p i]
  unfold propShare
  field_simp
  ring

lemma D_pos (hq : 0 < q) (hqn : q ≤ n) (hqm : q ≤ m) (c : Cost n m) (hc : Normalized c)
    {R : Finset (Fin n)} (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i))
    (i : Ordinary R) :
    0 < (n : ℝ) * (1 - propShare c i.val) + cost c i.val (H p) := by
  have hn : 0 < n := lt_of_lt_of_le hq hqn
  have hm : 0 < m := lt_of_lt_of_le hq hqm
  have hmq : 0 < m / q := Nat.div_pos hqm hq
  have hprop := PartC.prop_le_one hn c hc i.val
  have h0 : (⟨0, hm⟩ : Fin m) ∈ Z (p i) := by
    unfold Z
    simp only [mem_filter, mem_univ, true_and, not_exists, not_and]
    intro t ht
    unfold G mergedLabel at ht
    simp only [mem_filter, mem_univ, true_and] at ht
    rw [dif_pos (by simpa using hmq)] at ht
    rw [(hp i).1 _ (by simp)] at ht
    simp at ht
  have hK : 0 < K p := by
    have := PartC.card_Z_le_K p i
    have := card_pos.mpr ⟨_, h0⟩
    omega
  have hH : (⟨0, hm⟩ : Fin m) ∈ H p := by rw [PartD.mem_H]; exact hK
  have hcH : 0 < cost c i.val (H p) :=
    lt_of_lt_of_le (hc.1 i.val _) (single_le_sum (fun e _ => (hc.1 i.val e).le) hH)
  have : (0 : ℝ) ≤ n * (1 - propShare c i.val) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  linarith

theorem completed_facts {n m q : ℕ} (hq : 0 < q) (hqn : q ≤ n) (hqm : q ≤ m) (hdiv : q ∣ m)
    (c : Cost n m) (hc : Normalized c) (R : Finset (Fin n)) (hRn : R.card < n)
    (p : Packings n m q R) (hp : ∀ i, ValidPacking c i.val (p i)) :
    (∀ i e, (∑ t, eta n q t * completed c p i t e) = 1 / (n : ℝ)) ∧
    (∀ i t, fractionalCost c i.val (completed c p i t) ≤ 1) ∧
    (∀ i t e, 0 ≤ completed c p i t e ∧ completed c p i t e ≤ 1 / (q : ℝ)) := by
  have hn : 0 < n := lt_of_lt_of_le hq hqn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨?_, ?_, ?_⟩
  · intro i e
    unfold eta completed
    by_cases he : e ∈ H p
    · simp only [if_pos he]
      unfold tau
      have hD := D_pos hq hqn hqm c hc p hp i
      have hDe := D_eq hq hqn hdiv c p i
      have : ∀ t : Fin (n / q), (denominator n q t : ℝ) / n *
          ((1 - fractionalCost c i.val (shiftedBase p i t)) /
            ((n : ℝ) * (1 - propShare c i.val) + cost c i.val (H p))) =
          ((denominator n q t : ℝ) * (1 - fractionalCost c i.val (shiftedBase p i t))) /
            (n * ((n : ℝ) * (1 - propShare c i.val) + cost c i.val (H p))) := by
        intro t; field_simp
      simp_rw [this]
      rw [← sum_div, ← hDe]
      field_simp
    · simp only [if_neg he]
      have hK : K p ≤ e.val := by rw [PartD.mem_H] at he; omega
      have := denom_shiftedBase hq hqn hdiv p i e hK
      simp_rw [div_mul_eq_mul_div]
      rw [← sum_div, this]
  · intro i t
    exact PartD.fc_completed_le_one hn hq hqn hdiv c hc R p hp i t
  · intro i t e
    refine ⟨PartD.completed_nonneg hn hq hqn hdiv c hc R p hp i t e, ?_⟩
    unfold completed
    by_cases he : e ∈ H p
    · rw [if_pos he]
      unfold tau
      have hD := D_pos hq hqn hqm c hc p hp i
      rw [div_le_div_iff₀ hD hqR, one_mul, D_eq hq hqn hdiv c p i]
      have hN : ∀ s, 0 ≤ 1 - fractionalCost c i.val (shiftedBase p i s) := fun s => by
        linarith [PartC.fc_shiftedBase_le_one hq hqn hdiv c hc R p hp i s]
      calc (1 - fractionalCost c i.val (shiftedBase p i t)) * q
          ≤ (denominator n q t : ℝ) * (1 - fractionalCost c i.val (shiftedBase p i t)) := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast q_le_denominator t) (hN t)
        _ ≤ _ := single_le_sum (f := fun s => (denominator n q s : ℝ) *
              (1 - fractionalCost c i.val (shiftedBase p i s)))
            (fun s _ => mul_nonneg (Nat.cast_nonneg _) (hN s)) (mem_univ t)
    · rw [if_neg he]
      have hK : K p ≤ e.val := by rw [PartD.mem_H] at he; omega
      have hsum := denom_shiftedBase hq hqn hdiv p i e hK
      have hnn : ∀ s, 0 ≤ shiftedBase p i s e := fun s => PartD.shiftedBase_nonneg hq p i s e
      have h1 : (denominator n q t : ℝ) * shiftedBase p i t e ≤ 1 := by
        rw [← hsum]
        exact single_le_sum (f := fun s => (denominator n q s : ℝ) * shiftedBase p i s e)
          (fun s _ => mul_nonneg (Nat.cast_nonneg _) (hnn s)) (mem_univ t)
      rw [le_div_iff₀ hqR]
      calc shiftedBase p i t e * q ≤ shiftedBase p i t e * denominator n q t :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast q_le_denominator t) (hnn t)
        _ ≤ 1 := by linarith

end completed

/-! ### Counting profiles -/

section counting

lemma eq_of_no_jump {β : Type*} (μ : ℕ → β) (a : ℕ) :
    ∀ k, (∀ r ∈ Ioc a (a + k), μ r = μ (r - 1)) → μ (a + k) = μ a := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    have h1 := h (a + (k + 1)) (by simp only [mem_Ioc]; omega)
    have h2 := ih (fun r hr => h r (by simp only [mem_Ioc] at hr ⊢; omega))
    rw [h1]
    simpa [show a + (k + 1) - 1 = a + k by omega] using h2

lemma changes_le_jumps {β : Type*} [DecidableEq β] (μ : ℕ → β) (s : ℕ → ℕ) :
    ∀ N, (∀ j < N, s j ≤ s (j + 1)) →
      ((range N).filter (fun j => μ (s (j + 1)) ≠ μ (s j))).card ≤
        ((Ioc (s 0) (s N)).filter (fun r => μ r ≠ μ (r - 1))).card := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro hs
    have ih' := ih (fun j hj => hs j (by omega))
    have hN := hs N (by omega)
    have hmono : ∀ j, j ≤ N → s 0 ≤ s j := by
      intro j
      induction j with
      | zero => intro _; exact le_rfl
      | succ j ihj => intro hj; exact (ihj (by omega)).trans (hs j (by omega))
    have hs0 := hmono N le_rfl
    have hsub : Ioc (s 0) (s N) ⊆ Ioc (s 0) (s (N + 1)) := by
      intro r hr; simp only [mem_Ioc] at hr ⊢; omega
    rw [range_add_one, filter_insert]
    split_ifs with hch
    · have hdisj : Disjoint ((Ioc (s 0) (s N)).filter (fun r => μ r ≠ μ (r - 1)))
          ((Ioc (s N) (s (N + 1))).filter (fun r => μ r ≠ μ (r - 1))) := by
        rw [disjoint_left]
        intro r h1 h2
        simp only [mem_filter, mem_Ioc] at h1 h2
        omega
      have hne : ((Ioc (s N) (s (N + 1))).filter (fun r => μ r ≠ μ (r - 1))).Nonempty := by
        by_contra hemp
        rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at hemp
        apply hch
        have := eq_of_no_jump μ (s N) (s (N + 1) - s N)
          (fun r hr => by
            have := hemp (by simpa [show s N + (s (N + 1) - s N) = s (N + 1) by omega] using hr)
            simpa using this)
        rwa [show s N + (s (N + 1) - s N) = s (N + 1) by omega] at this
      calc (insert N ((range N).filter (fun j => μ (s (j + 1)) ≠ μ (s j)))).card
          ≤ ((range N).filter (fun j => μ (s (j + 1)) ≠ μ (s j))).card + 1 := card_insert_le _ _
        _ ≤ ((Ioc (s 0) (s N)).filter (fun r => μ r ≠ μ (r - 1))).card +
              ((Ioc (s N) (s (N + 1))).filter (fun r => μ r ≠ μ (r - 1))).card := by
            have := hne.card_pos; omega
        _ = (((Ioc (s 0) (s N)).filter (fun r => μ r ≠ μ (r - 1))).disjUnion
              ((Ioc (s N) (s (N + 1))).filter (fun r => μ r ≠ μ (r - 1))) hdisj).card :=
            (card_disjUnion _ _ _).symm
        _ ≤ _ := by
            apply card_le_card
            intro r hr
            simp only [disjUnion_eq_union, mem_union, mem_filter, mem_Ioc] at hr ⊢
            rcases hr with h | h
            · exact ⟨⟨h.1.1, by omega⟩, h.2⟩
            · exact ⟨⟨by omega, h.1.2⟩, h.2⟩
    · exact ih'.trans (card_le_card (filter_subset_filter _ hsub))

lemma card_image_range_le {β : Type*} [DecidableEq β] (f : ℕ → β) :
    ∀ N, ((range (N + 1)).image f).card ≤ 1 + ((range N).filter (fun j => f (j + 1) ≠ f j)).card := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [range_add_one (n := N + 1), image_insert]
    by_cases hch : f (N + 1) = f N
    · have hmem : f (N + 1) ∈ (range (N + 1)).image f := by
        rw [hch]; exact mem_image_of_mem f (by simp)
      rw [insert_eq_of_mem hmem]
      refine ih.trans ?_
      have := card_le_card (filter_subset_filter (fun j => f (j + 1) ≠ f j)
        (range_subset_range.mpr (by omega : N ≤ N + 1)))
      omega
    · have hf : (range (N + 1)).filter (fun j => f (j + 1) ≠ f j) =
          insert N ((range N).filter (fun j => f (j + 1) ≠ f j)) := by
        rw [range_add_one, filter_insert, if_pos hch]
      rw [hf]
      have hnot : N ∉ (range N).filter (fun j => f (j + 1) ≠ f j) := by simp
      rw [card_insert_of_notMem hnot]
      have := card_insert_le (f (N + 1)) ((range (N + 1)).image f)
      omega

end counting

section labels

variable {n m q : ℕ}

/-- Block index of the surviving chore of rank `j` (zero when there is none). -/
def sblk (P : Labels n m q) (j : ℕ) : ℕ :=
  if h : j < (univ \ Z P).card then (Classical.choose (PartC.position_surj _ h)).val / q else 0

lemma sblk_spec (P : Labels n m q) {j : ℕ} (h : j < (univ \ Z P).card) :
    ∃ g : Fin m, g ∉ Z P ∧ position (univ \ Z P) g = j ∧ sblk P j = g.val / q := by
  have hs := Classical.choose_spec (PartC.position_surj _ h)
  refine ⟨_, by simpa using hs.1, hs.2, ?_⟩
  unfold sblk
  rw [dif_pos h]

lemma sblk_mono (P : Labels n m q) {j : ℕ} (h : j + 1 < (univ \ Z P).card) :
    sblk P j ≤ sblk P (j + 1) := by
  obtain ⟨g, hg, hgp, hgs⟩ := sblk_spec P (j := j) (by omega)
  obtain ⟨g', hg', hgp', hgs'⟩ := sblk_spec P h
  rw [hgs, hgs']
  apply Nat.div_le_div_right
  by_contra hlt
  push_neg at hlt
  have := PartC.position_mono (univ \ Z P) (Fin.le_iff_val_le_val.mpr hlt.le)
  omega

lemma sblk_le (hdiv : q ∣ m) (P : Labels n m q) (j : ℕ) : sblk P j ≤ m / q - 1 := by
  by_cases h : j < (univ \ Z P).card
  · obtain ⟨g, -, -, hgs⟩ := sblk_spec P h
    rw [hgs]
    have := Nat.div_lt_div_of_lt_of_dvd hdiv g.isLt
    omega
  · unfold sblk; rw [dif_neg h]; omega

def mu' (P : Labels n m q) (b : ℕ) : Option (Fin (binCount n q)) :=
  if h : b < m / q then P ⟨b, h⟩ else none

def Psi (n q : ℕ) (o : Option (Fin (binCount n q))) : Fin (n / q) → ℝ := fun t =>
  if o.map (fun v => min v.val (n / q - 1)) = some t.val then 1 / (denominator n q t : ℝ) else 0

def Fj (P : Labels n m q) (j : ℕ) : Fin (n / q) → ℝ := fun t =>
  ∑ g : Fin m, if g ∉ Z P ∧ position (univ \ Z P) g = j then rawBase P t g else 0

lemma rawBase_eq_Psi (hdiv : q ∣ m) (P : Labels n m q) (g : Fin m) (hg : g ∉ Z P) (t : Fin (n / q)) :
    rawBase P t g = Psi n q (mu' P (g.val / q)) t := by
  unfold rawBase Psi mu'
  rw [dif_pos (Nat.div_lt_div_of_lt_of_dvd hdiv g.isLt)]
  have := PartC.mem_G_iff P hdiv t g
  unfold PartC.blk at this
  by_cases hG : g ∈ G P t
  · rw [if_pos ⟨hg, hG⟩, if_pos (this.mp hG)]
  · rw [if_neg (fun h => hG h.2), if_neg (fun h => hG (this.mpr h))]

lemma Fj_lt (hdiv : q ∣ m) (P : Labels n m q) {j : ℕ} (h : j < (univ \ Z P).card) :
    Fj P j = Psi n q (mu' P (sblk P j)) := by
  obtain ⟨g, hg, hgp, hgs⟩ := sblk_spec P h
  funext t
  unfold Fj
  rw [sum_eq_single g, if_pos ⟨hg, hgp⟩, hgs, rawBase_eq_Psi hdiv P g hg t]
  · intro g' _ hne
    rw [if_neg]
    rintro ⟨hg'Z, hg'p⟩
    apply hne
    exact PartC.position_injOn (univ \ Z P) (by simpa using hg'Z) (by simpa using hg)
      (hg'p.trans hgp.symm)
  · intro hh; exact absurd (mem_univ _) hh

lemma Fj_ge (P : Labels n m q) {j : ℕ} (h : (univ \ Z P).card ≤ j) : Fj P j = 0 := by
  funext t
  unfold Fj
  apply sum_eq_zero
  intro g _
  rw [if_neg]
  rintro ⟨hg, hgp⟩
  have := PartC.position_lt_card (univ \ Z P) (g := g) (by simpa using hg)
  omega

lemma jumps_le_segments (P : Labels n m q) :
    ((Ioc 0 (m / q - 1)).filter (fun r => mu' P r ≠ mu' P (r - 1))).card ≤ segments P + 1 := by
  unfold segments
  split_ifs with h
  · rw [Ioc_eq_empty (by omega)]; simp
  · set T := (univ.filter (fun r : Fin (m / q) =>
      ∃ h : 0 < r.val, 1 < r.val ∧ P r ≠ P ⟨r.val - 1, by omega⟩))
    have hsub : (Ioc 0 (m / q - 1)).filter (fun r => mu' P r ≠ mu' P (r - 1)) ⊆
        insert 1 (T.map Fin.valEmbedding) := by
      intro r hr
      simp only [mem_filter, mem_Ioc] at hr
      rw [mem_insert]
      by_cases h1 : r = 1
      · exact Or.inl h1
      · right
        rw [mem_map]
        refine ⟨⟨r, by omega⟩, ?_, rfl⟩
        simp only [T, mem_filter, mem_univ, true_and]
        refine ⟨show 0 < r by omega, show 1 < r by omega, ?_⟩
        intro heq
        apply hr.2
        unfold mu'
        rw [dif_pos (by omega), dif_pos (by omega)]
        exact heq
    calc _ ≤ (insert 1 (T.map Fin.valEmbedding)).card := card_le_card hsub
      _ ≤ T.card + 1 := by rw [← card_map Fin.valEmbedding (s := T)]; exact card_insert_le _ _
      _ ≤ _ := by omega

lemma Fj_changes (hdiv : q ∣ m) (P : Labels n m q) (N : ℕ) :
    ((range N).filter (fun j => Fj P (j + 1) ≠ Fj P j)).card ≤ segments P + 2 := by
  classical
  set k := (univ \ Z P).card
  have hsub : (range N).filter (fun j => Fj P (j + 1) ≠ Fj P j) ⊆
      insert (k - 1) ((range (k - 1)).filter
        (fun j => mu' P (sblk P (j + 1)) ≠ mu' P (sblk P j))) := by
    intro j hj
    simp only [mem_filter, mem_range] at hj
    rw [mem_insert]
    by_cases h1 : j + 1 < k
    · right
      simp only [mem_filter, mem_range]
      refine ⟨by omega, ?_⟩
      intro heq
      apply hj.2
      rw [Fj_lt hdiv P h1, Fj_lt hdiv P (by omega : j < k), heq]
    · by_cases h2 : j < k
      · left; omega
      · exfalso
        apply hj.2
        rw [Fj_ge P (by omega), Fj_ge P (by omega)]
  have hj := changes_le_jumps (mu' P) (sblk P) (k - 1) (fun j hj => sblk_mono P (by omega))
  have hIoc : (Ioc (sblk P 0) (sblk P (k - 1))).filter (fun r => mu' P r ≠ mu' P (r - 1)) ⊆
      (Ioc 0 (m / q - 1)).filter (fun r => mu' P r ≠ mu' P (r - 1)) := by
    apply filter_subset_filter
    intro r hr
    have := sblk_le hdiv P (k - 1)
    simp only [mem_Ioc] at hr ⊢
    omega
  have h3 := card_le_card hIoc
  have h4 := jumps_le_segments P
  have h5 := card_le_card hsub
  have h6 := card_insert_le (k - 1) ((range (k - 1)).filter
        (fun j => mu' P (sblk P (j + 1)) ≠ mu' P (sblk P j)))
  omega

end labels

lemma profiles_le_sum {n m q : ℕ} (hdiv : q ∣ m) (c : Cost n m) {R : Finset (Fin n)}
    (p : Packings n m q R) :
    profiles c p ≤ 2 + ∑ i, (segments (p i) + 2) := by
  classical
  unfold profiles
  set P0 : Ordinary R → Fin (n / q) → ℝ := fun i t => tau c p i t
  set Φ : ℕ → Ordinary R → Fin (n / q) → ℝ := fun j i t => Fj (p i) j t
  have hsub : univ.image (fun e : Fin m => fun (i : Ordinary R) (t : Fin (n / q)) =>
      completed c p i t e) ⊆ insert P0 ((range (m + 1)).image Φ) := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨e, -, rfl⟩ := hx
    rw [mem_insert]
    by_cases he : e ∈ H p
    · left
      funext i t
      unfold completed
      rw [if_pos he]
    · right
      rw [mem_image]
      refine ⟨e.val - K p, by simp; omega, ?_⟩
      funext i t
      unfold completed
      rw [if_neg he]
      unfold shiftedBase
      rw [if_neg (by rw [PartD.mem_H] at he; omega)]
      rfl
  have h1 := card_le_card hsub
  have h2 := card_insert_le P0 ((range (m + 1)).image Φ)
  have h3 := card_image_range_le Φ m
  have hbi : (range m).filter (fun j => Φ (j + 1) ≠ Φ j) ⊆
      univ.biUnion (fun i => (range m).filter (fun j => Fj (p i) (j + 1) ≠ Fj (p i) j)) := by
    intro j hj
    simp only [mem_filter, mem_range] at hj
    rw [mem_biUnion]
    by_contra hall
    push_neg at hall
    apply hj.2
    funext i t
    have := hall i (mem_univ _)
    simp only [mem_filter, mem_range, not_and, not_not] at this
    exact congrFun (this hj.1) t
  have h4 := (card_le_card hbi).trans card_biUnion_le
  have h5 : ∑ i, ((range m).filter (fun j => Fj (p i) (j + 1) ≠ Fj (p i) j)).card ≤
      ∑ i, (segments (p i) + 2) := sum_le_sum (fun i _ => Fj_changes hdiv (p i) m)
  have h1' : (univ.image (fun e : Fin m => fun (i : Ordinary R) (t : Fin (n / q)) =>
      completed c p i t e)).card ≤ (insert P0 ((range (m + 1)).image Φ)).card := by
    convert h1
  omega

theorem profiles_le (B : ℝ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (m q : ℕ) (c : Cost n m),
    0 < q → q ≤ n → q ∣ m → ∀ R : Finset (Fin n), ∀ p : Packings n m q R,
    (∀ i, (segments (p i) : ℝ) ≤ B * (n / q : ℕ) ^ 3) → profiles c p ≤ n ^ 5 := by
  refine ⟨⌈|B|⌉₊ + 4, ?_⟩
  intro n hn m q c hq hqn hdiv R p hseg
  have hmain := profiles_le_sum hdiv c p
  have hB : |B| ≤ ⌈|B|⌉₊ := Nat.le_ceil _
  have hnR : (⌈|B|⌉₊ : ℝ) + 4 ≤ n := by exact_mod_cast hn
  have hn4 : (4 : ℝ) ≤ n := by linarith [abs_nonneg B]
  have hL : ((n / q : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n q
  have hseg' : ∀ i, (segments (p i) : ℝ) ≤ |B| * (n : ℝ) ^ 3 := by
    intro i
    refine (hseg i).trans ?_
    have h0 : (0 : ℝ) ≤ ((n / q : ℕ) : ℝ) ^ 3 := by positivity
    calc B * ((n / q : ℕ) : ℝ) ^ 3 ≤ |B| * ((n / q : ℕ) : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right (le_abs_self B) h0
      _ ≤ |B| * (n : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hL 3) (abs_nonneg B)
  have hcard : (Fintype.card (Ordinary R) : ℝ) ≤ n := by
    have := Fintype.card_subtype_le (fun i : Fin n => i ∉ R)
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hsum : ((∑ i, (segments (p i) + 2) : ℕ) : ℝ) ≤ n * (|B| * (n : ℝ) ^ 3 + 2) := by
    push_cast
    calc ∑ i, ((segments (p i) : ℝ) + 2) ≤ ∑ _i : Ordinary R, (|B| * (n : ℝ) ^ 3 + 2) :=
          sum_le_sum (fun i _ => by linarith [hseg' i])
      _ = (Fintype.card (Ordinary R) : ℝ) * (|B| * (n : ℝ) ^ 3 + 2) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ n * (|B| * (n : ℝ) ^ 3 + 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  have hmainR : (profiles c p : ℝ) ≤ 2 + n * (|B| * (n : ℝ) ^ 3 + 2) := by
    have : (profiles c p : ℝ) ≤ ((2 + ∑ i, (segments (p i) + 2) : ℕ) : ℝ) := by
      exact_mod_cast hmain
    push_cast at this hsum ⊢
    linarith
  have hfin : 2 + (n : ℝ) * (|B| * (n : ℝ) ^ 3 + 2) ≤ (n : ℝ) ^ 5 := by
    have hn0 : (0 : ℝ) ≤ n := by linarith
    have hB' : |B| + 4 ≤ (n : ℝ) := by linarith
    have h4 : (n : ℝ) ^ 4 * (|B| + 4) ≤ (n : ℝ) ^ 4 * n :=
      mul_le_mul_of_nonneg_left hB' (by positivity)
    have h3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    have h6 : (n : ℝ) ≤ (n : ℝ) ^ 4 := by
      calc (n : ℝ) = n * 1 := by ring
        _ ≤ n * (n : ℝ) ^ 3 := mul_le_mul_of_nonneg_left h3 hn0
        _ = (n : ℝ) ^ 4 := by ring
    have e1 : (n : ℝ) ^ 4 * n = (n : ℝ) ^ 5 := by ring
    have e2 : (n : ℝ) * (|B| * (n : ℝ) ^ 3 + 2) = |B| * (n : ℝ) ^ 4 + 2 * n := by ring
    have e3 : (n : ℝ) ^ 4 * (|B| + 4) = |B| * (n : ℝ) ^ 4 + 4 * (n : ℝ) ^ 4 := by ring
    rw [e2]
    linarith
  exact_mod_cast hmainR.trans hfin

end SublinearChoresMMS.Disposal.Dev.L32.PartX
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32
open SublinearChoresMMS.Disposal
open Finset
/-! Part X stubs used by Part Y (copied verbatim from the Blueprint). -/

end SublinearChoresMMS.Disposal.Dev.L32
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32.PartY
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.L32
open Finset

/-! ### `blockSize` bounds -/
lemma log_pos3 {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log n := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith

lemma block_le_n {n : ℕ} (hn : 3 ≤ n) : blockSize n ≤ n := by
  have h1 := log_pos3 hn
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n)
    linarith
  set s := Real.sqrt ((n : ℝ) * Real.log n) with hs
  have hs1 : 1 < s := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by nlinarith)
  have hsn : s ≤ n := by
    rw [hs, Real.sqrt_le_left (by positivity)]
    nlinarith
  have hb : (blockSize n : ℝ) = (2 : ℝ) ^ ((⌊Real.logb 2 s⌋₊ : ℕ) : ℝ) := by
    unfold blockSize
    rw [Real.rpow_natCast]
    push_cast
    rfl
  have hlog0 : 0 ≤ Real.logb 2 s := Real.logb_nonneg (by norm_num) hs1.le
  have hrp : (2 : ℝ) ^ Real.logb 2 s = s := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
  have : (blockSize n : ℝ) ≤ s := by
    rw [hb]
    calc (2 : ℝ) ^ ((⌊Real.logb 2 s⌋₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ Real.logb 2 s :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hlog0)
      _ = s := hrp
  exact_mod_cast (by linarith : (blockSize n : ℝ) ≤ n)

lemma block_pos (n : ℕ) : 0 < blockSize n := by
  unfold blockSize; positivity

end SublinearChoresMMS.Disposal.Dev.L32.PartY
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.BW.PartS
open SublinearChoresMMS.Disposal
open Finset
/-! Part S needs no Blueprint definitions. -/
/-- Quadratic form identity for a Gram matrix. -/
lemma quad_gram {κ : Type} [Fintype κ] {m : ℕ} (y : Fin m → κ → ℝ) (x : κ → ℝ) :
    ∑ j, ∑ l, x j * x l * (∑ i, y i j * y i l) = ∑ i, (∑ j, x j * y i j) ^ 2 := by
  have h : ∀ i, (∑ j, x j * y i j) ^ 2 = ∑ j, ∑ l, x j * x l * (y i j * y i l) := by
    intro i; rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [h]
  calc ∑ j, ∑ l, x j * x l * (∑ i, y i j * y i l)
      = ∑ j, ∑ i, ∑ l, x j * x l * (y i j * y i l) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Splitting off the diagonal part. -/
lemma quad_split {κ : Type} [Fintype κ] [DecidableEq κ] (U : κ → κ → ℝ) (K : ℝ) (x : κ → ℝ) :
    ∑ j, ∑ l, x j * x l * (K * (if j = l then U j j else 0) - U j l) =
      K * ∑ j, x j ^ 2 * U j j - ∑ j, ∑ l, x j * x l * U j l := by
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

/-- A frame from a finite family of vectors, discarding the zero ones. -/
lemma frame_of_vecs {κ : Type} [Fintype κ] [DecidableEq κ] (V : Submodule ℝ (κ → ℝ)) (K : ℝ)
    {m : ℕ} (y : Fin m → κ → ℝ) (hyV : ∀ i, y i ∈ V) (hne : ∃ i, y i ≠ 0)
    (hineq : ∀ c : κ → ℝ, ∑ i, (∑ j, c j * y i j) ^ 2 ≤ K * ∑ j, c j ^ 2 * ∑ i, y i j ^ 2) :
    ∃ (N : ℕ) (u : Fin N → κ → ℝ) (w : Fin N → ℝ), 0 < N ∧
      (∀ k, u k ∈ V) ∧ (∀ k, ∑ j, u k j ^ 2 = 1) ∧ (∀ k, 0 < w k) ∧
      ∀ c : κ → ℝ, ∑ k, w k * (∑ j, c j * u k j) ^ 2 ≤
        K * ∑ j, c j ^ 2 * ∑ k, w k * u k j ^ 2 := by
  classical
  let T := {i : Fin m // y i ≠ 0}
  let e := Fintype.equivFin T
  let S : Fin m → ℝ := fun i => ∑ j, y i j ^ 2
  have hSpos : ∀ i, y i ≠ 0 → 0 < S i := by
    intro i hi
    obtain ⟨j, hj⟩ : ∃ j, y i j ≠ 0 := by
      by_contra h; push Not at h; exact hi (funext h)
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨j, Finset.mem_univ _, by positivity⟩
  have hsub : ∀ F : Fin m → ℝ, (∀ i, y i = 0 → F i = 0) →
      ∑ k : Fin (Fintype.card T), F (e.symm k).1 = ∑ i, F i := by
    intro F hF
    rw [e.symm.sum_comp (fun t : T => F t.1)]
    rw [← Finset.sum_subtype (Finset.univ.filter fun i => y i ≠ 0) (by simp) F]
    exact Finset.sum_filter_of_ne fun i _ h => fun h' => h (hF i h')
  refine ⟨Fintype.card T, fun k => (Real.sqrt (S (e.symm k).1))⁻¹ • y (e.symm k).1,
    fun k => S (e.symm k).1, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hne
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  · intro k; exact V.smul_mem _ (hyV _)
  · intro k
    have hS := hSpos _ (e.symm k).2
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt hS.le,
      ← Finset.mul_sum]
    exact inv_mul_cancel₀ hS.ne'
  · intro k; exact hSpos _ (e.symm k).2
  · intro c
    have h1 : ∀ k : Fin (Fintype.card T), S (e.symm k).1 *
        (∑ j, c j * ((Real.sqrt (S (e.symm k).1))⁻¹ • y (e.symm k).1) j) ^ 2 =
        (∑ j, c j * y (e.symm k).1 j) ^ 2 := by
      intro k
      have hS := hSpos _ (e.symm k).2
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show ∑ j, c j * ((Real.sqrt (S (e.symm k).1))⁻¹ * y (e.symm k).1 j) =
        (Real.sqrt (S (e.symm k).1))⁻¹ * ∑ j, c j * y (e.symm k).1 j by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
      rw [mul_pow, inv_pow, Real.sq_sqrt hS.le, ← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul]
    have h2 : ∀ j, ∀ k : Fin (Fintype.card T), S (e.symm k).1 *
        ((Real.sqrt (S (e.symm k).1))⁻¹ • y (e.symm k).1) j ^ 2 = y (e.symm k).1 j ^ 2 := by
      intro j k
      have hS := hSpos _ (e.symm k).2
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_pow, inv_pow, Real.sq_sqrt hS.le, ← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul]
    simp only [h1, h2]
    rw [hsub (fun i => (∑ j, c j * y i j) ^ 2) (fun i hi => by simp [hi])]
    have h3 : ∀ j, ∑ k : Fin (Fintype.card T), y (e.symm k).1 j ^ 2 = ∑ i, y i j ^ 2 :=
      fun j => hsub (fun i => y i j ^ 2) (fun i hi => by simp [hi])
    simp only [h3]
    exact hineq c

/-- The dual certificate cannot exist: a PSD form `M` with `uᵀMu > K Σ M_jj u_j²` on
`V \ {0}` contradicts `card κ ≤ K dim V`. -/
lemma no_dual {κ : Type} [Fintype κ] [DecidableEq κ] (V : Submodule ℝ (κ → ℝ)) (K : ℝ)
    (hd : 0 < Module.finrank ℝ V)
    (hcard : (Fintype.card κ : ℝ) ≤ K * Module.finrank ℝ V) (M : κ → κ → ℝ)
    (h1 : ∀ x : κ → ℝ, 0 ≤ ∑ j, ∑ l, M j l * x j * x l)
    (h2 : ∀ v ∈ V, v ≠ 0 → K * ∑ j, M j j * v j ^ 2 < ∑ j, ∑ l, M j l * v j * v l) :
    False := by
  classical
  let P : Matrix κ κ ℝ := Matrix.of fun j l => (M j l + M l j) / 2
  have hQ : ∀ x : κ → ℝ, ∑ j, ∑ l, P j l * x j * x l = ∑ j, ∑ l, M j l * x j * x l := by
    intro x
    simp only [P, Matrix.of_apply, add_div, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun j l => M l j / 2 * x j * x l)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hpsd : P.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · ext j l
      simp only [P, Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
      ring
    · have := h1 x
      rw [← hQ] at this
      refine this.trans_eq ?_
      simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨m, b, hb⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hpsd
  have hPb : ∀ j l, P j l = ∑ r, b r j * b r l := by
    intro j l
    rw [hb]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
  let D : κ → ℝ := fun j => M j j
  have hD : ∀ j, D j = ∑ r, b r j ^ 2 := by
    intro j
    have := hPb j j
    simp only [P, Matrix.of_apply] at this
    simp only [D, sq]
    linarith
  have hD0 : ∀ j, 0 ≤ D j := fun j => by
    rw [hD]; exact Finset.sum_nonneg fun r _ => sq_nonneg _
  have hbz : ∀ j, D j = 0 → ∀ r, b r j = 0 := by
    intro j hj r
    rw [hD] at hj
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sq_nonneg (b r j))).mp hj r
      (Finset.mem_univ _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hQb : ∀ x : κ → ℝ, ∑ j, ∑ l, M j l * x j * x l = ∑ r, (∑ j, b r j * x j) ^ 2 := by
    intro x
    rw [← hQ]
    calc _ = ∑ j, ∑ l, x j * x l * (∑ r, b r j * b r l) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by rw [hPb]; ring
      _ = ∑ r, (∑ j, x j * b r j) ^ 2 := quad_gram b x
      _ = _ := by simp only [mul_comm (x _)]
  -- the weighting map
  let Dm : (κ → ℝ) →ₗ[ℝ] (κ → ℝ) := LinearMap.pi fun j => Real.sqrt (D j) • LinearMap.proj j
  let T : (κ → ℝ) →ₗ[ℝ] EuclideanSpace ℝ κ :=
    (WithLp.linearEquiv 2 ℝ (κ → ℝ)).symm.toLinearMap ∘ₗ Dm
  have hT : ∀ x j, T x j = Real.sqrt (D j) * x j := by
    intro x j
    simp [T, Dm]
  let TV := T ∘ₗ V.subtype
  have hinj : Function.Injective TV := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hne
    have hvj : ∀ j, D j = 0 ∨ (v : κ → ℝ) j = 0 := by
      intro j
      have := congrArg (fun z : EuclideanSpace ℝ κ => z j) hv
      simp only [TV, LinearMap.comp_apply, Submodule.subtype_apply, hT] at this
      rcases mul_eq_zero.mp this with h | h
      · left; exact le_antisymm (Real.sqrt_eq_zero'.mp h) (hD0 j)
      · right; simpa using h
    have hv0 : (v : κ → ℝ) ≠ 0 := by
      intro h; exact hne (Subtype.ext h)
    have := h2 v v.2 hv0
    rw [hQb] at this
    have e1 : ∑ r, (∑ j, b r j * (v : κ → ℝ) j) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [Finset.sum_eq_zero fun j _ => ?_]
      · simp
      · rcases hvj j with h | h
        · rw [hbz j h r, zero_mul]
        · rw [h, mul_zero]
    have e2 : ∑ j, M j j * (v : κ → ℝ) j ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases hvj j with h | h
      · rw [show M j j = D j from rfl, h, zero_mul]
      · rw [h]; ring
    rw [e1, e2, mul_zero] at this
    exact lt_irrefl _ this
  have hrank : Module.finrank ℝ (LinearMap.range TV) = Module.finrank ℝ V :=
    LinearMap.finrank_range_of_inj hinj
  let W := LinearMap.range TV
  let ob := stdOrthonormalBasis ℝ W
  have horth : Orthonormal ℝ (fun k => (ob k : EuclideanSpace ℝ κ)) :=
    ob.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hw : ∀ k, ∃ v : V, TV v = (ob k : EuclideanSpace ℝ κ) := fun k => (ob k).2
  choose vv hvv using hw
  let x : Fin (Module.finrank ℝ W) → κ → ℝ := fun k => (vv k : κ → ℝ)
  have hxw : ∀ k j, (ob k : EuclideanSpace ℝ κ) j = Real.sqrt (D j) * x k j := by
    intro k j
    rw [← hvv k]
    simp only [TV, LinearMap.comp_apply, Submodule.subtype_apply, hT, x]
  have hnorm : ∀ k, ∑ j, D j * x k j ^ 2 = 1 := by
    intro k
    have h := EuclideanSpace.real_norm_sq_eq (ob k : EuclideanSpace ℝ κ)
    rw [horth.1 k, one_pow] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hxw, mul_pow, Real.sq_sqrt (hD0 j)]
  have hx0 : ∀ k, x k ≠ 0 := by
    intro k h
    have := hnorm k
    simp [h] at this
  have hlow : ∀ k, K < ∑ r, (∑ j, b r j * x k j) ^ 2 := by
    intro k
    have := h2 (x k) (vv k).2 (hx0 k)
    rw [hQb] at this
    simpa [D, hnorm k] using this
  -- Bessel
  let c : Fin m → EuclideanSpace ℝ κ := fun r =>
    WithLp.toLp 2 (fun j => if D j = 0 then 0 else b r j / Real.sqrt (D j))
  have hcw : ∀ r k, ∑ j, b r j * x k j = inner ℝ (ob k : EuclideanSpace ℝ κ) (c r) := by
    intro r k
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [c, PiLp.toLp_apply, hxw, RCLike.inner_apply, conj_trivial]
    by_cases h : D j = 0
    · simp [h, hbz j h r]
    · have hs : Real.sqrt (D j) ≠ 0 := by
        rw [Real.sqrt_ne_zero (hD0 j)]; exact h
      simp only [h, if_false]
      field_simp
  have hcn : ∀ r, ‖c r‖ ^ 2 = ∑ j, if D j = 0 then 0 else b r j ^ 2 / D j := by
    intro r
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [c, PiLp.toLp_apply]
    split_ifs with h
    · simp
    · rw [div_pow, Real.sq_sqrt (hD0 j)]
  have hup : ∑ k, ∑ r, (∑ j, b r j * x k j) ^ 2 ≤ Fintype.card κ := by
    rw [Finset.sum_comm]
    calc ∑ r, ∑ k, (∑ j, b r j * x k j) ^ 2 ≤ ∑ r, ‖c r‖ ^ 2 := by
          refine Finset.sum_le_sum fun r _ => ?_
          have := horth.sum_inner_products_le (s := Finset.univ) (x := c r)
          simpa [hcw, Real.norm_eq_abs, sq_abs] using this
      _ = ∑ j, (if D j = 0 then 0 else 1 : ℝ) := by
          simp only [hcn]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs with h
          · simp
          · rw [← Finset.sum_div, ← hD j, div_self h]
      _ ≤ ∑ _j : κ, (1 : ℝ) := Finset.sum_le_sum fun j _ => by split_ifs <;> norm_num
      _ = Fintype.card κ := by simp
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ W))).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact ⟨⟨0, by rw [hrank]; exact hd⟩⟩
  have hlow' : K * Module.finrank ℝ V < ∑ k, ∑ r, (∑ j, b r j * x k j) ^ 2 := by
    calc K * Module.finrank ℝ V = ∑ _k : Fin (Module.finrank ℝ W), K := by
          have hr : (Module.finrank ℝ W : ℝ) = Module.finrank ℝ V := by exact_mod_cast hrank
          simp [hr, mul_comm]
      _ < _ := Finset.sum_lt_sum_of_nonempty hne fun k _ => hlow k
  linarith

/-- The matrix `B G Bᵀ` for coefficient vectors `bv`. -/
def UG {κ : Type} {d : ℕ} (bv : Fin d → κ → ℝ) (G : Fin d → Fin d → ℝ) : κ → κ → ℝ :=
  fun j l => ∑ a, ∑ b, G a b * bv a j * bv b l

lemma UG_add {κ : Type} {d : ℕ} (bv : Fin d → κ → ℝ) (G H : Fin d → Fin d → ℝ) (j l : κ) :
    UG bv (G + H) j l = UG bv G j l + UG bv H j l := by
  simp only [UG, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma UG_smul {κ : Type} {d : ℕ} (bv : Fin d → κ → ℝ) (r : ℝ) (G : Fin d → Fin d → ℝ)
    (j l : κ) : UG bv (r • G) j l = r * UG bv G j l := by
  simp only [UG, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- The linear map `G ↦ K · diag(B G Bᵀ) - B G Bᵀ`. -/
def PsiL {κ : Type} [DecidableEq κ] {d : ℕ} (K : ℝ) (bv : Fin d → κ → ℝ) :
    (Fin d → Fin d → ℝ) →ₗ[ℝ] (κ → κ → ℝ) where
  toFun G := fun j l => K * (if j = l then UG bv G j j else 0) - UG bv G j l
  map_add' G H := by
    funext j l
    simp only [Pi.add_apply, UG_add]
    split_ifs <;> ring
  map_smul' r G := by
    funext j l
    simp only [Pi.smul_apply, smul_eq_mul, UG_smul, RingHom.id_apply]
    split_ifs <;> ring

/-- Trace-one PSD symmetric coefficient matrices. -/
def KGset (d : ℕ) : Set (Fin d → Fin d → ℝ) :=
  {G | (∀ a b, G a b = G b a) ∧ (∀ x : Fin d → ℝ, 0 ≤ ∑ a, ∑ b, x a * x b * G a b) ∧
    ∑ a, G a a = 1}

lemma quad_two {d : ℕ} (G : Fin d → Fin d → ℝ) (a b : Fin d) (hab : a ≠ b) (s : ℝ) :
    ∑ c, ∑ e, ((if c = a then 1 else 0) + s * (if c = b then 1 else 0)) *
      ((if e = a then 1 else 0) + s * (if e = b then 1 else 0)) * G c e =
      G a a + s * G a b + s * G b a + s * s * G b b := by
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, one_mul, zero_mul,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  ring_nf

lemma KGset_bound {d : ℕ} {G : Fin d → Fin d → ℝ} (hG : G ∈ KGset d) (a b : Fin d) :
    |G a b| ≤ 1 := by
  classical
  obtain ⟨hs, hp, ht⟩ := hG
  have hdiag : ∀ c, 0 ≤ G c c := by
    intro c
    have := hp (fun e => if e = c then 1 else 0)
    simpa [ite_mul, Finset.sum_ite_eq'] using this
  have hdle : ∀ c, G c c ≤ 1 := by
    intro c
    rw [← ht]
    exact Finset.single_le_sum (fun e _ => hdiag e) (Finset.mem_univ c)
  by_cases hab : a = b
  · subst hab
    rw [abs_le]; constructor <;> linarith [hdiag a, hdle a]
  · have hsum : G a a + G b b ≤ 1 := by
      rw [← ht]
      calc G a a + G b b = ∑ e ∈ {a, b}, G e e := (Finset.sum_pair (f := fun e => G e e) hab).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun e _ _ => hdiag e)
    have h1 := hp (fun c => (if c = a then 1 else 0) + 1 * (if c = b then 1 else 0))
    have h2 := hp (fun c => (if c = a then 1 else 0) + (-1) * (if c = b then 1 else 0))
    rw [quad_two G a b hab] at h1 h2
    rw [hs b a] at h1 h2
    rw [abs_le]; constructor <;> nlinarith [hdiag a, hdiag b]

lemma KGset_compact (d : ℕ) : IsCompact (KGset d) := by
  have hset : KGset d = (⋂ a, ⋂ b, {G : Fin d → Fin d → ℝ | G a b = G b a}) ∩
      (⋂ x : Fin d → ℝ, {G | 0 ≤ ∑ a, ∑ b, x a * x b * G a b}) ∩
      {G | ∑ a, G a a = 1} := by
    ext G; simp [KGset, and_assoc]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · rw [hset]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_iInter fun a => isClosed_iInter fun b =>
        isClosed_eq (by fun_prop) (by fun_prop)
    · exact isClosed_iInter fun x => isClosed_le continuous_const (by fun_prop)
    · exact isClosed_eq (by fun_prop) continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun G hG => ?_⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun a => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun b => ?_
    rw [Real.norm_eq_abs]
    exact KGset_bound hG a b

lemma KGset_convex (d : ℕ) : Convex ℝ (KGset d) := by
  intro G hG H hH α β hα hβ hαβ
  obtain ⟨hs1, hp1, ht1⟩ := hG
  obtain ⟨hs2, hp2, ht2⟩ := hH
  refine ⟨fun a b => ?_, fun x => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs1 a b, hs2 a b]
  · have e : ∑ a, ∑ b, x a * x b * (α • G + β • H) a b =
        α * ∑ a, ∑ b, x a * x b * G a b + β * ∑ a, ∑ b, x a * x b * H a b := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [e]
    have := hp1 x; have := hp2 x
    positivity
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, ht1, ht2]
    linarith

/-- The PSD cone, as a set of matrices. -/
def Tset (κ : Type) [Fintype κ] : Set (κ → κ → ℝ) :=
  {N | ∀ x : κ → ℝ, 0 ≤ ∑ j, ∑ l, x j * x l * N j l}

lemma Tset_closed (κ : Type) [Fintype κ] : IsClosed (Tset κ) := by
  have : Tset κ = ⋂ x : κ → ℝ, {N | 0 ≤ ∑ j, ∑ l, x j * x l * N j l} := by
    ext N; simp [Tset]
  rw [this]
  exact isClosed_iInter fun x => isClosed_le continuous_const (by fun_prop)

lemma Tset_smul {κ : Type} [Fintype κ] {N : κ → κ → ℝ} (hN : N ∈ Tset κ) {r : ℝ}
    (hr : 0 ≤ r) : r • N ∈ Tset κ := by
  intro x
  have e : ∑ j, ∑ l, x j * x l * (r • N) j l = r * ∑ j, ∑ l, x j * x l * N j l := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e]
  exact mul_nonneg hr (hN x)

lemma Tset_convex (κ : Type) [Fintype κ] : Convex ℝ (Tset κ) := by
  intro G hG H hH α β hα hβ _ x
  have e : ∑ a, ∑ b, x a * x b * (α • G + β • H) a b =
      α * ∑ a, ∑ b, x a * x b * G a b + β * ∑ a, ∑ b, x a * x b * H a b := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e]
  have := hG x; have := hH x
  positivity

/-- Coordinate representation of a linear functional on matrices. -/
lemma rep {κ : Type} [Fintype κ] [DecidableEq κ] (f : (κ → κ → ℝ) →L[ℝ] ℝ)
    (N : κ → κ → ℝ) :
    f N = ∑ j, ∑ l, N j l * f (fun a b => if a = j ∧ b = l then 1 else 0) := by
  have hN : N = ∑ j, ∑ l, N j l • (fun a b => if a = j ∧ b = l then (1 : ℝ) else 0) := by
    funext a b
    simp [Finset.sum_apply, ite_and, Finset.sum_ite_eq']
  conv_lhs => rw [hN]
  simp [map_sum, map_smul]

lemma lin_split {κ : Type} [Fintype κ] [DecidableEq κ] (U M : κ → κ → ℝ) (K : ℝ) :
    ∑ j, ∑ l, (K * (if j = l then U j j else 0) - U j l) * M j l =
      K * ∑ j, U j j * M j j - ∑ j, ∑ l, U j l * M j l := by
  simp only [sub_mul, Finset.sum_sub_distrib, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

theorem spread {κ : Type} [Fintype κ] [DecidableEq κ] (V : Submodule ℝ (κ → ℝ)) (K : ℝ)
    (hK : 0 < K) (hd : 0 < Module.finrank ℝ V)
    (hcard : (Fintype.card κ : ℝ) ≤ K * Module.finrank ℝ V) :
    ∃ (N : ℕ) (u : Fin N → κ → ℝ) (w : Fin N → ℝ), 0 < N ∧
      (∀ k, u k ∈ V) ∧ (∀ k, ∑ j, u k j ^ 2 = 1) ∧ (∀ k, 0 < w k) ∧
      ∀ c : κ → ℝ, ∑ k, w k * (∑ j, c j * u k j) ^ 2 ≤
        K * ∑ j, c j ^ 2 * ∑ k, w k * u k j ^ 2 := by
  classical
  by_contra hne
  let fb := Module.finBasis ℝ V
  let bv : Fin (Module.finrank ℝ V) → κ → ℝ := fun a => (fb a : κ → ℝ)
  have hbvV : ∀ a, bv a ∈ V := fun a => (fb a).2
  have hli : LinearIndependent ℝ bv := fb.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  let s := PsiL K bv '' KGset (Module.finrank ℝ V)
  have hsconv : Convex ℝ s := (KGset_convex _).linear_image (PsiL K bv)
  have hscomp : IsCompact s :=
    (KGset_compact _).image (PsiL K bv).continuous_of_finiteDimensional
  have hdisj : Disjoint s (Tset κ) := by
    rw [Set.disjoint_left]
    rintro _ ⟨G, hG, rfl⟩ hT
    apply hne
    let GM : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ := G
    have hpsd : GM.PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨?_, fun x => ?_⟩
      · ext a b
        simp only [GM, Matrix.conjTranspose_apply, star_trivial]
        exact hG.1 b a
      · refine (hG.2.1 x).trans_eq ?_
        simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, Finset.mul_sum, GM]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    obtain ⟨m, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hpsd
    have hGg : ∀ a b, G a b = ∑ i, g i a * g i b := by
      intro a b
      change GM a b = _
      rw [hg]
      simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
    let y : Fin m → κ → ℝ := fun i j => ∑ a, g i a * bv a j
    have hyfun : ∀ i, y i = ∑ a, g i a • bv a := by
      intro i; funext j; simp [y, Finset.sum_apply]
    have hyV : ∀ i, y i ∈ V := by
      intro i
      rw [hyfun i]
      exact V.sum_mem fun a _ => V.smul_mem _ (hbvV a)
    have hU : ∀ j l, UG bv G j l = ∑ i, y i j * y i l := by
      intro j l
      calc UG bv G j l = ∑ a, ∑ b, ∑ i, g i a * bv a j * (g i b * bv b l) := by
            simp only [UG, hGg, Finset.sum_mul]
            exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
              Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ a, ∑ i, ∑ b, g i a * bv a j * (g i b * bv b l) :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ i, ∑ a, ∑ b, g i a * bv a j * (g i b * bv b l) := Finset.sum_comm
        _ = ∑ i, y i j * y i l := by simp only [y, Finset.sum_mul_sum]
    have hyne : ∃ i, y i ≠ 0 := by
      by_contra h
      push Not at h
      have hg0 : ∀ i a, g i a = 0 := by
        intro i
        exact Fintype.linearIndependent_iff.mp hli (g i) (by rw [← hyfun i, h i])
      have htr := hG.2.2
      simp [hGg, hg0] at htr
    refine frame_of_vecs V K y hyV hyne fun c => ?_
    have h0 := hT c
    change 0 ≤ ∑ j, ∑ l, c j * c l *
      (K * (if j = l then UG bv G j j else 0) - UG bv G j l) at h0
    rw [quad_split] at h0
    simp only [hU] at h0
    rw [quad_gram] at h0
    simp only [← sq] at h0
    linarith
  obtain ⟨f, u0, v0, hfs, huv, hft⟩ :=
    geometric_hahn_banach_compact_closed hsconv hscomp (Tset_convex κ) (Tset_closed κ) hdisj
  have hv0 : v0 < 0 := by
    have := hft 0 (fun x => by simp)
    simpa using this
  let M : κ → κ → ℝ := fun j l => f (fun a b => if a = j ∧ b = l then 1 else 0)
  have hf : ∀ N, f N = ∑ j, ∑ l, N j l * M j l := rep f
  refine no_dual V K hd hcard M ?_ ?_
  · intro x
    have hxT : (fun j l => x j * x l) ∈ Tset κ := by
      intro z
      have e : ∑ j, ∑ l, z j * z l * (x j * x l) = (∑ j, z j * x j) * (∑ l, z l * x l) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
      rw [e]
      exact mul_self_nonneg _
    have hfx : f (fun j l => x j * x l) = ∑ j, ∑ l, M j l * x j * x l := by
      rw [hf]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    by_contra hneg
    push Not at hneg
    rw [← hfx] at hneg
    have := hft _ (Tset_smul hxT (r := v0 / f (fun j l => x j * x l))
      (div_nonneg_of_nonpos hv0.le hneg.le))
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  · intro v hv hv0'
    let h := fb.repr ⟨v, hv⟩
    have hvsum : ∀ j, v j = ∑ a, h a * bv a j := by
      intro j
      have := congrArg (fun z : V => (z : κ → ℝ) j) (fb.sum_repr ⟨v, hv⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      exact this.symm
    let S := ∑ a, h a ^ 2
    have hS : 0 < S := by
      obtain ⟨a, ha⟩ : ∃ a, h a ≠ 0 := by
        by_contra hc
        push Not at hc
        apply hv0'
        funext j
        simp [hvsum j, hc]
      exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, Finset.mem_univ _, by positivity⟩
    let G : Fin (Module.finrank ℝ V) → Fin (Module.finrank ℝ V) → ℝ :=
      fun a b => h a * h b / S
    have hGK : G ∈ KGset (Module.finrank ℝ V) := by
      refine ⟨fun a b => by simp only [G]; ring, fun x => ?_, ?_⟩
      · have e : ∑ a, ∑ b, x a * x b * G a b =
            (∑ a, x a * h a) * (∑ b, x b * h b) / S := by
          rw [Finset.sum_mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun b _ => by simp only [G]; ring
        rw [e]
        exact div_nonneg (mul_self_nonneg _) hS.le
      · simp only [G]
        rw [← Finset.sum_div]
        simp only [← sq]
        exact div_self hS.ne'
    have hUG : ∀ j l, UG bv G j l = v j * v l / S := by
      intro j l
      rw [hvsum j, hvsum l, Finset.sum_mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun b _ => by simp only [G]; ring
    have hlt := hfs _ ⟨G, hGK, rfl⟩
    rw [hf] at hlt
    change ∑ j, ∑ l, (K * (if j = l then UG bv G j j else 0) - UG bv G j l) * M j l < u0
      at hlt
    rw [lin_split] at hlt
    simp only [hUG] at hlt
    have e : K * ∑ j, v j * v j / S * M j j - ∑ j, ∑ l, v j * v l / S * M j l =
        (K * ∑ j, M j j * v j ^ 2 - ∑ j, ∑ l, M j l * v j * v l) / S := by
      rw [sub_div, mul_div_assoc, Finset.sum_div, Finset.sum_div]
      congr 1
      · congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun l _ => by ring
    rw [e] at hlt
    by_contra hge
    push Not at hge
    have : 0 ≤ (K * ∑ j, M j j * v j ^ 2 - ∑ j, ∑ l, M j l * v j * v l) / S :=
      div_nonneg (by linarith) hS.le
    linarith

end SublinearChoresMMS.Disposal.Dev.BW.PartS
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.BW
open SublinearChoresMMS.Disposal
open Finset
/-! # Bansal's rounding for Appendix A.2, Steps 1–2, as a derandomized finite walk

Part S: the spread (SDP) lemma. Part T: the one-step exponential supermartingale inequality.
Part C: one step of the walk. Part W: the walk. Part A: the application to the target. -/
/-! ## Part S: Bansal's SDP lemma, as a finite frame -/
alias spread := SublinearChoresMMS.Disposal.Dev.BW.PartS.spread

/-! ## Part T: one step of the exponential supermartingale -/
/-- The potential exponent: a linear deviation plus `lam` times the remaining variance. -/
def Zf {ι : Type} [Fintype ι] (lam : ℝ) (η a ζ : ι → ℝ) : ℝ :=
  ∑ j, a j * (ζ j - η j) + lam * ∑ j, a j ^ 2 * (ζ j * (1 - ζ j))

end SublinearChoresMMS.Disposal.Dev.BW
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.BW.PartT
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.BW
open Finset
theorem step_exp {ι Ω : Type} [Fintype ι] [Fintype Ω] (K lam : ℝ) (hK : 1 ≤ K)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (η a ζ : ι → ℝ) (ha : ∀ j, |a j| ≤ 1)
    (π : Ω → ℝ) (y : Ω → ι → ℝ) (hπ0 : ∀ o, 0 ≤ π o) (hπ1 : ∑ o, π o = 1)
    (hmean : ∀ j, ∑ o, π o * y o j = 0)
    (hζ : ∀ j, 0 ≤ ζ j ∧ ζ j ≤ 1)
    (hbox : ∀ o j, 0 ≤ ζ j + y o j ∧ ζ j + y o j ≤ 1)
    (hsmall : ∀ o, ∑ j, |y o j| ≤ 1 / 2)
    (hiso : ∀ c : ι → ℝ, ∑ o, π o * (∑ j, c j * y o j) ^ 2 ≤
      K * ∑ j, c j ^ 2 * ∑ o, π o * y o j ^ 2) :
    ∑ o, π o * Real.exp (lam / (8 * K) * Zf lam η a (ζ + y o)) ≤
      Real.exp (lam / (8 * K) * Zf lam η a ζ) := by
  classical
  have hKpos : 0 < K := by linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = lam / (8 * K) := ⟨_, rfl⟩
  rw [← hα]
  have hα0 : 0 < α := by rw [hα]; positivity
  have h8 : 8 * K * α = lam := by rw [hα]; field_simp
  have hα1 : α ≤ 1 := by nlinarith
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ j, a j ^ 2 * ∑ o, π o * y o j ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact sum_nonneg fun j _ => mul_nonneg (sq_nonneg _)
      (sum_nonneg fun o _ => mul_nonneg (hπ0 o) (sq_nonneg _))
  obtain ⟨c, hc⟩ : ∃ c : ι → ℝ, c = fun j => a j ^ 2 * (1 - 2 * ζ j) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Ω → ℝ, ∀ o, L o = ∑ j, a j * y o j := ⟨_, fun _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Ω → ℝ, ∀ o, M o = ∑ j, c j * y o j := ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Ω → ℝ, ∀ o, Q o = ∑ j, a j ^ 2 * y o j ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Ω → ℝ, ∀ o, Y o = L o + lam * M o - lam * Q o :=
    ⟨_, fun _ => rfl⟩
  -- the increment of the potential exponent
  have hdec : ∀ o, Zf lam η a (ζ + y o) = Zf lam η a ζ + Y o := by
    intro o
    rw [hY, hL, hM, hQ, hc]
    simp only [Zf, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- elementary coordinate facts
  have ha2 : ∀ j, a j ^ 2 ≤ 1 := by
    intro j
    have := ha j
    have h0 := abs_nonneg (a j)
    rw [← sq_abs]; nlinarith
  have hyj : ∀ o j, |y o j| ≤ 1 / 2 := fun o j =>
    le_trans (single_le_sum (f := fun j => |y o j|) (fun j _ => abs_nonneg _) (mem_univ j))
      (hsmall o)
  have hQ0 : ∀ o, 0 ≤ Q o := fun o => by
    rw [hQ]; exact sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hQ1 : ∀ o, Q o ≤ 1 / 4 := by
    intro o
    rw [hQ]
    calc ∑ j, a j ^ 2 * y o j ^ 2 ≤ ∑ j, |y o j| * (1 / 2) := by
          refine sum_le_sum fun j _ => ?_
          have h1 := hyj o j
          have h2 := abs_nonneg (y o j)
          have h3 := ha2 j
          have h4 : y o j ^ 2 = |y o j| * |y o j| := by rw [← sq, sq_abs]
          rw [h4]
          have h5 : |y o j| * |y o j| ≤ |y o j| * (1 / 2) :=
            mul_le_mul_of_nonneg_left h1 h2
          have h6 : 0 ≤ |y o j| * |y o j| := mul_nonneg h2 h2
          nlinarith
      _ = (∑ j, |y o j|) * (1 / 2) := by rw [sum_mul]
      _ ≤ (1 / 2) * (1 / 2) := by gcongr; exact hsmall o
      _ = 1 / 4 := by norm_num
  -- |Y| ≤ 1
  have hYabs : ∀ o, |Y o| ≤ 1 := by
    intro o
    have hYe : Y o = ∑ j, a j * y o j * (1 + lam * a j * (1 - 2 * ζ j - y o j)) := by
      rw [hY, hL, hM, hQ, hc]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hYe]
    calc |∑ j, a j * y o j * (1 + lam * a j * (1 - 2 * ζ j - y o j))|
        ≤ ∑ j, |a j * y o j * (1 + lam * a j * (1 - 2 * ζ j - y o j))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, 2 * |y o j| := by
          refine sum_le_sum fun j _ => ?_
          have ht : |1 - 2 * ζ j - y o j| ≤ 1 := by
            have := hζ j; have := hbox o j
            rw [abs_le]; constructor <;> linarith
          have hw : |lam * a j * (1 - 2 * ζ j - y o j)| ≤ 1 := by
            rw [abs_mul, abs_mul, abs_of_pos hl0]
            have := ha j
            calc lam * |a j| * |1 - 2 * ζ j - y o j| ≤ 1 * 1 * 1 := by
                  gcongr
              _ = 1 := by norm_num
          have h1w : |1 + lam * a j * (1 - 2 * ζ j - y o j)| ≤ 2 := by
            calc _ ≤ |(1 : ℝ)| + |lam * a j * (1 - 2 * ζ j - y o j)| := abs_add_le _ _
              _ ≤ 1 + 1 := by rw [abs_one]; linarith
              _ = 2 := by norm_num
          rw [abs_mul, abs_mul]
          calc |a j| * |y o j| * |1 + lam * a j * (1 - 2 * ζ j - y o j)|
              ≤ 1 * |y o j| * 2 :=
                mul_le_mul (mul_le_mul_of_nonneg_right (ha j) (abs_nonneg _)) h1w
                  (abs_nonneg _) (by positivity)
            _ = 2 * |y o j| := by ring
      _ = 2 * ∑ j, |y o j| := by rw [mul_sum]
      _ ≤ 2 * (1 / 2) := by gcongr; exact hsmall o
      _ = 1 := by norm_num
  -- expectations
  have Elin : ∀ d : ι → ℝ, ∑ o, π o * ∑ j, d j * y o j = 0 := by
    intro d
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_eq_zero fun j _ => ?_
    have : ∑ o, π o * (d j * y o j) = d j * ∑ o, π o * y o j := by
      rw [mul_sum]; refine sum_congr rfl fun o _ => ?_; ring
    rw [this, hmean j, mul_zero]
  have EL : ∑ o, π o * L o = 0 := by simp only [hL]; exact Elin a
  have EM : ∑ o, π o * M o = 0 := by simp only [hM]; exact Elin c
  have EQ : ∑ o, π o * Q o = S := by
    simp only [hQ, hS, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => sum_congr rfl fun o _ => ?_
    ring
  have EY : ∑ o, π o * Y o = -(lam * S) := by
    have : ∑ o, π o * Y o =
        ∑ o, π o * L o + lam * ∑ o, π o * M o - lam * ∑ o, π o * Q o := by
      simp only [hY, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun o _ => ?_
      ring
    rw [this, EL, EM, EQ]; ring
  have EL2 : ∑ o, π o * L o ^ 2 ≤ K * S := by
    simp only [hL, hS]; exact hiso a
  have EM2 : ∑ o, π o * M o ^ 2 ≤ K * S := by
    simp only [hM]
    refine le_trans (hiso c) ?_
    rw [hS]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ?_) hKpos.le
    refine mul_le_mul_of_nonneg_right ?_
      (sum_nonneg fun o _ => mul_nonneg (hπ0 o) (sq_nonneg _))
    rw [hc]
    have h1 : (1 - 2 * ζ j) ^ 2 ≤ 1 := by
      have := hζ j; nlinarith
    have h2 := ha2 j
    have h3 : 0 ≤ a j ^ 2 := sq_nonneg _
    have h4 : 0 ≤ (1 - 2 * ζ j) ^ 2 := sq_nonneg _
    have : (a j ^ 2 * (1 - 2 * ζ j)) ^ 2 = a j ^ 2 * (a j ^ 2 * (1 - 2 * ζ j) ^ 2) := by ring
    rw [this]
    have h5 : a j ^ 2 * (1 - 2 * ζ j) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have EQ2 : ∑ o, π o * Q o ^ 2 ≤ S / 4 := by
    calc ∑ o, π o * Q o ^ 2 ≤ ∑ o, π o * (Q o / 4) := by
          refine sum_le_sum fun o _ => mul_le_mul_of_nonneg_left ?_ (hπ0 o)
          have := hQ0 o; have := hQ1 o; nlinarith
      _ = (∑ o, π o * Q o) / 4 := by
          rw [sum_div]; refine sum_congr rfl fun o _ => ?_; ring
      _ = S / 4 := by rw [EQ]
  have hlam2 : lam ^ 2 ≤ 1 := by nlinarith
  have EY2 : ∑ o, π o * Y o ^ 2 ≤ 8 * K * S := by
    calc ∑ o, π o * Y o ^ 2 ≤
          ∑ o, (2 * (π o * L o ^ 2) + 4 * (π o * M o ^ 2) + 4 * (π o * Q o ^ 2)) := by
          refine sum_le_sum fun o _ => ?_
          have hp := hπ0 o
          have hpt : Y o ^ 2 ≤ 2 * L o ^ 2 + 4 * M o ^ 2 + 4 * Q o ^ 2 := by
            rw [hY]
            have hM2 : lam ^ 2 * M o ^ 2 ≤ M o ^ 2 := by
              have := sq_nonneg (M o); nlinarith
            have hQ2 : lam ^ 2 * Q o ^ 2 ≤ Q o ^ 2 := by
              have := sq_nonneg (Q o); nlinarith
            nlinarith [sq_nonneg (L o - (lam * M o - lam * Q o)),
              sq_nonneg (lam * M o + lam * Q o)]
          nlinarith [mul_le_mul_of_nonneg_left hpt hp]
      _ = 2 * ∑ o, π o * L o ^ 2 + 4 * ∑ o, π o * M o ^ 2 + 4 * ∑ o, π o * Q o ^ 2 := by
          rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum, mul_sum]
      _ ≤ 2 * (K * S) + 4 * (K * S) + 4 * (S / 4) := by gcongr
      _ ≤ 8 * K * S := by nlinarith
  -- the exponential bound
  have hexp : ∀ o, Real.exp (α * Y o) ≤ 1 + α * Y o + (α * Y o) ^ 2 := by
    intro o
    have hx : |α * Y o| ≤ 1 := by
      rw [abs_mul, abs_of_pos hα0]
      calc α * |Y o| ≤ 1 * 1 := mul_le_mul hα1 (hYabs o) (abs_nonneg _) zero_le_one
        _ = 1 := by norm_num
    have := Real.abs_exp_sub_one_sub_id_le hx
    have := (abs_le.1 this).2
    linarith
  have hsum : ∑ o, π o * Real.exp (α * Y o) ≤ 1 := by
    calc ∑ o, π o * Real.exp (α * Y o) ≤ ∑ o, π o * (1 + α * Y o + (α * Y o) ^ 2) :=
          sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (hexp o) (hπ0 o)
      _ = ∑ o, π o + α * ∑ o, π o * Y o + α ^ 2 * ∑ o, π o * Y o ^ 2 := by
          simp only [mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun o _ => ?_
          ring
      _ ≤ 1 + α * (-(lam * S)) + α ^ 2 * (8 * K * S) := by
          rw [hπ1, EY]; gcongr
      _ = 1 + α * S * (8 * K * α - lam) := by ring
      _ = 1 := by rw [h8]; ring
  calc ∑ o, π o * Real.exp (α * Zf lam η a (ζ + y o))
      = Real.exp (α * Zf lam η a ζ) * ∑ o, π o * Real.exp (α * Y o) := by
        rw [mul_sum]
        refine sum_congr rfl fun o _ => ?_
        rw [hdec o, mul_add, Real.exp_add]; ring
    _ ≤ Real.exp (α * Zf lam η a ζ) * 1 :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = Real.exp (α * Zf lam η a ζ) := mul_one _

end SublinearChoresMMS.Disposal.Dev.BW.PartT
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.BW
open SublinearChoresMMS.Disposal
open Finset
alias step_exp := SublinearChoresMMS.Disposal.Dev.BW.PartT.step_exp

/-! ## Part C: one step of the walk -/
/-- Strictly fractional coordinates. -/
def frac {ι : Type} [Fintype ι] (ζ : ι → ℝ) : Finset ι :=
  univ.filter (fun j => 0 < ζ j ∧ ζ j < 1)

/-- Equality functionals that see some fractional coordinate. -/
def act {ι κ : Type} [Fintype ι] [Fintype κ] (g : κ → ι → ℝ) (ζ : ι → ℝ) : ℕ :=
  (univ.filter (fun l => ∃ j ∈ frac ζ, g l j ≠ 0)).card

/-- The walk may continue: the free subspace has dimension at least `|frac| / K`. -/
def Cond {ι κ : Type} [Fintype ι] [Fintype κ] (g : κ → ι → ℝ) (K : ℝ) (ζ : ι → ℝ) : Prop :=
  act g ζ + 1 < (frac ζ).card ∧
    ((frac ζ).card : ℝ) ≤ K * (((frac ζ).card : ℝ) - act g ζ - 1)

/-- The pessimistic estimator: both signs of every test vector. -/
def Phi {ι : Type} [Fintype ι] (A : Finset (ι → ℝ)) (K lam : ℝ) (η ζ : ι → ℝ) : ℝ :=
  ∑ a ∈ A, (Real.exp (lam / (8 * K) * Zf lam η a ζ) +
    Real.exp (lam / (8 * K) * Zf lam η (-a) ζ))

end SublinearChoresMMS.Disposal.Dev.BW
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.BW.PartC
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.BW
open Finset
/-- A step along `v` of length at most `γ` that stays in the box and either has length `γ`
or pushes some fractional coordinate onto the boundary. -/
lemma exists_step {ι : Type} [Fintype ι] (ζ v : ι → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hζ : ∀ j, 0 ≤ ζ j ∧ ζ j ≤ 1) (hsupp : ∀ j, v j ≠ 0 → 0 < ζ j ∧ ζ j < 1) :
    ∃ t : ℝ, 0 < t ∧ t ≤ γ ∧ (∀ j, 0 ≤ ζ j + t * v j ∧ ζ j + t * v j ≤ 1) ∧
      (t = γ ∨ ∃ j, (0 < ζ j ∧ ζ j < 1) ∧ (ζ j + t * v j = 0 ∨ ζ j + t * v j = 1)) := by
  classical
  set r : ι → ℝ := fun j => if 0 < v j then (1 - ζ j) / v j else ζ j / (-v j) with hr
  set T := univ.filter (fun j => v j ≠ 0) with hT
  have hrpos : ∀ j ∈ T, 0 < r j := by
    intro j hj
    have hv : v j ≠ 0 := (mem_filter.1 hj).2
    obtain ⟨h1, h2⟩ := hsupp j hv
    simp only [hr]
    split_ifs with h
    · exact div_pos (by linarith) h
    · exact div_pos h1 (by
        rcases lt_or_gt_of_ne hv with h' | h'
        · linarith
        · exact absurd h' h)
  -- key: any `t ∈ [0, r j]` keeps coordinate `j` in the box
  have hbox : ∀ t, 0 ≤ t → (∀ j ∈ T, t ≤ r j) → ∀ j, 0 ≤ ζ j + t * v j ∧ ζ j + t * v j ≤ 1 := by
    intro t ht0 htr j
    by_cases hv : v j = 0
    · simp [hv, hζ j]
    have hjT : j ∈ T := mem_filter.2 ⟨mem_univ _, hv⟩
    have htj := htr j hjT
    simp only [hr] at htj
    split_ifs at htj with h
    · rw [le_div_iff₀ h] at htj
      constructor <;> nlinarith [hζ j]
    · have hneg : v j < 0 := lt_of_le_of_ne (not_lt.1 h) hv
      rw [le_div_iff₀ (by linarith)] at htj
      constructor <;> nlinarith [hζ j]
  by_cases hex : ∃ j ∈ T, r j < γ
  · obtain ⟨j0, hj0T, hj0min⟩ := exists_min_image T r (by obtain ⟨j, hj, _⟩ := hex; exact ⟨j, hj⟩)
    obtain ⟨j1, hj1T, hj1⟩ := hex
    refine ⟨r j0, hrpos j0 hj0T, le_of_lt (lt_of_le_of_lt (hj0min j1 hj1T) hj1),
      hbox _ (hrpos j0 hj0T).le hj0min, Or.inr ⟨j0, hsupp j0 (mem_filter.1 hj0T).2, ?_⟩⟩
    have hv : v j0 ≠ 0 := (mem_filter.1 hj0T).2
    simp only [hr]
    split_ifs with h
    · right; field_simp; ring
    · left
      have : -v j0 ≠ 0 := neg_ne_zero.2 hv
      field_simp; ring
  · push Not at hex
    exact ⟨γ, hγ, le_rfl, hbox γ hγ.le hex, Or.inl rfl⟩

/-- Effect of such a step on `frac` and on the sum of squares. -/
lemma step_progress {ι : Type} [Fintype ι] (ζ v : ι → ℝ) (t γ : ℝ)
    (hsupp : ∀ j, v j ≠ 0 → 0 < ζ j ∧ ζ j < 1) (horth : ∑ j, ζ j * v j = 0)
    (hnorm : ∑ j, v j ^ 2 = 1)
    (ht : t = γ ∨ ∃ j, (0 < ζ j ∧ ζ j < 1) ∧ (ζ j + t * v j = 0 ∨ ζ j + t * v j = 1)) :
    frac (fun j => ζ j + t * v j) ⊆ frac ζ ∧
      ((frac (fun j => ζ j + t * v j)).card < (frac ζ).card ∨
        ∑ j, ζ j ^ 2 + γ ^ 2 ≤ ∑ j, (ζ j + t * v j) ^ 2) := by
  classical
  have hsub : frac (fun j => ζ j + t * v j) ⊆ frac ζ := by
    intro j hj
    simp only [frac, mem_filter, mem_univ, true_and] at hj ⊢
    by_cases hv : v j = 0
    · simpa [hv] using hj
    · exact hsupp j hv
  refine ⟨hsub, ?_⟩
  rcases ht with rfl | ⟨j, hj, hb⟩
  · right
    have : ∑ j, (ζ j + t * v j) ^ 2 = ∑ j, ζ j ^ 2 + 2 * t * ∑ j, ζ j * v j + t ^ 2 * ∑ j, v j ^ 2 := by
      rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl (fun j _ => by ring)
    rw [this, horth, hnorm]; linarith
  · left
    apply card_lt_card
    refine ⟨hsub, fun h => ?_⟩
    have hjm : j ∈ frac ζ := by simp [frac, hj]
    have := h hjm
    simp only [frac, mem_filter, mem_univ, true_and] at this
    rcases hb with hb | hb <;> linarith [this.1, this.2]

/-- Sums of extensions by zero from a subtype. -/
lemma sum_dite_mem {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) (G : s → ℝ) :
    ∑ j, (if h : j ∈ s then G ⟨j, h⟩ else 0) = ∑ x : s, G x := by
  classical
  rw [← sum_subset (subset_univ s) (fun j _ hj => by simp [hj])]
  rw [← sum_attach s]
  refine sum_congr rfl (fun x _ => ?_)
  simp [x.2]

theorem step_exists {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (g : κ → ι → ℝ)
    (A : Finset (ι → ℝ)) (hA : ∀ a ∈ A, ∀ j, |a j| ≤ 1) (K lam : ℝ) (hK : 1 ≤ K)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (η ζ : ι → ℝ) (hζ : ∀ j, 0 ≤ ζ j ∧ ζ j ≤ 1)
    (hc : Cond g K ζ) :
    ∃ ζ' : ι → ℝ, (∀ j, 0 ≤ ζ' j ∧ ζ' j ≤ 1) ∧
      (∀ l, ∑ j, g l j * ζ' j = ∑ j, g l j * ζ j) ∧
      Phi A K lam η ζ' ≤ Phi A K lam η ζ ∧ frac ζ' ⊆ frac ζ ∧
      ((frac ζ').card < (frac ζ).card ∨
        ∑ j, ζ j ^ 2 + 1 / (4 * (Fintype.card ι : ℝ) ^ 2) ≤ ∑ j, ζ' j ^ 2) := by
  classical
  obtain ⟨hc1, hc2⟩ := hc
  set F := frac ζ with hF
  set S := univ.filter (fun l => ∃ j ∈ frac ζ, g l j ≠ 0) with hS
  have hact : act g ζ = S.card := rfl
  -- the free subspace
  let M : Matrix (Option S) F ℝ := fun o x => Option.elim o (ζ x) (fun l => g l.1 x)
  let V : Submodule ℝ (F → ℝ) := LinearMap.ker M.mulVecLin
  have hnat : F.card ≤ Module.finrank ℝ V + S.card + 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have h2 := Submodule.finrank_le (LinearMap.range M.mulVecLin)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_coe] at h2
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
    change Module.finrank ℝ (LinearMap.range M.mulVecLin) + Module.finrank ℝ V = F.card at h1
    omega
  have hd : 0 < Module.finrank ℝ V := by rw [hact] at hc1; omega
  have hKpos : 0 < K := by linarith
  have hcard : (Fintype.card F : ℝ) ≤ K * Module.finrank ℝ V := by
    rw [Fintype.card_coe]
    have : ((F.card : ℝ) - act g ζ - 1) ≤ Module.finrank ℝ V := by
      rw [hact]
      have : (F.card : ℝ) ≤ Module.finrank ℝ V + S.card + 1 := by exact_mod_cast hnat
      linarith
    calc (F.card : ℝ) ≤ K * ((F.card : ℝ) - act g ζ - 1) := hc2
      _ ≤ K * Module.finrank ℝ V := mul_le_mul_of_nonneg_left this hKpos.le
  obtain ⟨N, u, w, hN, huV, hu1, hw, hspread⟩ := spread V K hKpos hd hcard
  have hrow : ∀ k o, ∑ x, M o x * u k x = 0 := by
    intro k o
    have := congrFun (LinearMap.mem_ker.1 (huV k)) o
    simpa [Matrix.mulVec, dotProduct] using this
  have horthF : ∀ k, ∑ x : F, ζ x * u k x = 0 := fun k => by simpa [M] using hrow k none
  have hgF : ∀ k (l : S), ∑ x : F, g l.1 x * u k x = 0 := fun k l => by simpa [M] using hrow k (some l)
  -- extension by zero
  let ue : Fin N → ι → ℝ := fun k j => if h : j ∈ F then u k ⟨j, h⟩ else 0
  have hext : ∀ k (f : ι → ℝ), ∑ j, f j * ue k j = ∑ x : F, f x * u k x := by
    intro k f
    rw [← sum_dite_mem]
    refine sum_congr rfl (fun j _ => ?_)
    by_cases h : j ∈ F <;> simp [ue, h]
  have hsupp : ∀ k j, ue k j ≠ 0 → 0 < ζ j ∧ ζ j < 1 := by
    intro k j h
    by_cases hj : j ∈ F
    · simpa [F, frac] using hj
    · simp [ue, hj] at h
  have horth : ∀ k, ∑ j, ζ j * ue k j = 0 := fun k => by rw [hext]; exact horthF k
  have hnorm : ∀ k, ∑ j, ue k j ^ 2 = 1 := by
    intro k
    rw [← hu1 k, ← sum_dite_mem]
    refine sum_congr rfl (fun j _ => ?_)
    by_cases h : j ∈ F <;> simp [ue, h]
  have hgl : ∀ l k, ∑ j, g l j * ue k j = 0 := by
    intro l k
    rw [hext]
    by_cases hl : l ∈ S
    · exact hgF k ⟨l, hl⟩
    · refine sum_eq_zero (fun x _ => ?_)
      have : g l x = 0 := by
        by_contra hne
        exact hl (mem_filter.2 ⟨mem_univ _, x.1, x.2, hne⟩)
      simp [this]
  have habs : ∀ k j, |ue k j| ≤ 1 := by
    intro k j
    rw [← sq_le_one_iff_abs_le_one]
    rw [← hnorm k]
    exact single_le_sum (f := fun j => ue k j ^ 2) (fun j _ => sq_nonneg _) (mem_univ j)
  -- directions
  let dir : Fin N × Bool → ι → ℝ := fun o j => if o.2 then ue o.1 j else -ue o.1 j
  have hdsupp : ∀ o j, dir o j ≠ 0 → 0 < ζ j ∧ ζ j < 1 := by
    intro o j h
    apply hsupp o.1 j
    intro h'; apply h; simp [dir, h']
  have hdorth : ∀ o, ∑ j, ζ j * dir o j = 0 := by
    intro o
    by_cases h : o.2 = true
    · simp only [dir, h, if_true]; exact horth o.1
    · simp only [dir, h]; simp [mul_neg, sum_neg_distrib, horth o.1]
  have hdnorm : ∀ o, ∑ j, dir o j ^ 2 = 1 := by
    intro o
    by_cases h : o.2 = true
    · simp only [dir, h, if_true]; exact hnorm o.1
    · simp only [dir, h]; simp [hnorm o.1]
  have hdg : ∀ l o, ∑ j, g l j * dir o j = 0 := by
    intro l o
    by_cases h : o.2 = true
    · simp only [dir, h, if_true]; exact hgl l o.1
    · simp only [dir, h]; simp [mul_neg, sum_neg_distrib, hgl l o.1]
  have hdabs : ∀ o j, |dir o j| ≤ 1 := by
    intro o j
    by_cases h : o.2 = true
    · simp only [dir, h, if_true]; exact habs o.1 j
    · simp only [dir, h]; simpa [abs_neg] using habs o.1 j
  -- step lengths
  have hFpos : 0 < F.card := by omega
  have hιpos : 0 < (Fintype.card ι : ℝ) := by
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.2 (by
      obtain ⟨j, _⟩ := card_pos.1 hFpos; exact ⟨j⟩)
    exact_mod_cast this
  set γ : ℝ := 1 / (2 * (Fintype.card ι : ℝ)) with hγdef
  have hγ : 0 < γ := by positivity
  have hstep := fun o => exists_step ζ (dir o) γ hγ hζ (hdsupp o)
  choose t ht0 htγ htbox htprog using hstep
  -- the distribution
  let raw : Fin N × Bool → ℝ := fun o => w o.1 / (t o * (t (o.1, true) + t (o.1, false)))
  have hraw : ∀ o, 0 < raw o := by
    intro o
    have := ht0 (o.1, true); have := ht0 (o.1, false)
    exact div_pos (hw o.1) (mul_pos (ht0 o) (by linarith))
  set Z := ∑ o, raw o with hZ
  have hZpos : 0 < Z := by
    have : Nonempty (Fin N × Bool) := ⟨(⟨0, hN⟩, true)⟩
    exact sum_pos (fun o _ => hraw o) univ_nonempty
  let π : Fin N × Bool → ℝ := fun o => raw o / Z
  let y : Fin N × Bool → ι → ℝ := fun o j => t o * dir o j
  have hπ0 : ∀ o, 0 ≤ π o := fun o => (div_pos (hraw o) hZpos).le
  have hπpos : ∀ o, 0 < π o := fun o => div_pos (hraw o) hZpos
  have hπ1 : ∑ o, π o = 1 := by
    simp only [π]; rw [← sum_div, ← hZ, div_self hZpos.ne']
  have hmean : ∀ j, ∑ o, π o * y o j = 0 := by
    intro j
    rw [Fintype.sum_prod_type]
    refine sum_eq_zero (fun k _ => ?_)
    rw [Fintype.sum_bool]
    simp only [π, y, dir, raw, if_true, Bool.false_eq_true, if_false]
    have := ht0 (k, true); have := ht0 (k, false)
    field_simp
    ring
  have hsq : ∀ h : Fin N → ℝ, ∑ o, π o * (t o ^ 2 * h o.1) = (∑ k, w k * h k) / Z := by
    intro h
    rw [Fintype.sum_prod_type, sum_div]
    refine sum_congr rfl (fun k _ => ?_)
    rw [Fintype.sum_bool]
    simp only [π, raw]
    have := ht0 (k, true); have := ht0 (k, false)
    field_simp
  have hlin : ∀ (c : ι → ℝ) o, (∑ j, c j * y o j) ^ 2 = t o ^ 2 * (∑ j, c j * ue o.1 j) ^ 2 := by
    intro c o
    have : ∑ j, c j * y o j = t o * ∑ j, c j * dir o j := by
      rw [mul_sum]; exact sum_congr rfl (fun j _ => by simp only [y]; ring)
    rw [this]
    by_cases h : o.2 = true
    · simp only [dir, h, if_true]; ring
    · simp only [dir, h]; simp only [Bool.false_eq_true, if_false, mul_neg, sum_neg_distrib]; ring
  have hcoord : ∀ o j, y o j ^ 2 = t o ^ 2 * ue o.1 j ^ 2 := by
    intro o j
    by_cases h : o.2 = true
    · simp only [y, dir, h, if_true]; ring
    · simp only [y, dir, h]; simp only [Bool.false_eq_true, if_false]; ring
  have hiso : ∀ c : ι → ℝ, ∑ o, π o * (∑ j, c j * y o j) ^ 2 ≤
      K * ∑ j, c j ^ 2 * ∑ o, π o * y o j ^ 2 := by
    intro c
    simp_rw [hlin, hcoord]
    rw [hsq (fun k => (∑ j, c j * ue k j) ^ 2)]
    have hj : ∀ j, ∑ o, π o * (t o ^ 2 * ue o.1 j ^ 2) = (∑ k, w k * ue k j ^ 2) / Z :=
      fun j => hsq (fun k => ue k j ^ 2)
    simp_rw [hj]
    simp_rw [hext]
    have hR : ∑ j, c j ^ 2 * ((∑ k, w k * ue k j ^ 2) / Z) =
        (∑ x : F, c x ^ 2 * ∑ k, w k * u k x ^ 2) / Z := by
      rw [sum_div, ← sum_dite_mem]
      refine sum_congr rfl (fun j _ => ?_)
      by_cases h : j ∈ F <;> simp [ue, h, mul_div_assoc]
    rw [hR, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hspread (fun x => c x)) hZpos.le
  have hbox : ∀ o j, 0 ≤ ζ j + y o j ∧ ζ j + y o j ≤ 1 := fun o j => htbox o j
  have hsmall : ∀ o, ∑ j, |y o j| ≤ 1 / 2 := by
    intro o
    calc ∑ j, |y o j| ≤ ∑ _j : ι, γ := by
          refine sum_le_sum (fun j _ => ?_)
          simp only [y, abs_mul, abs_of_pos (ht0 o)]
          calc t o * |dir o j| ≤ t o * 1 := mul_le_mul_of_nonneg_left (hdabs o j) (ht0 o).le
            _ ≤ γ := by linarith [htγ o]
      _ = 1 / 2 := by
          rw [sum_const, card_univ, nsmul_eq_mul, hγdef]; field_simp
  -- the supermartingale inequality for the estimator
  have hexp : ∀ a : ι → ℝ, (∀ j, |a j| ≤ 1) →
      ∑ o, π o * Real.exp (lam / (8 * K) * Zf lam η a (ζ + y o)) ≤
        Real.exp (lam / (8 * K) * Zf lam η a ζ) := fun a ha =>
    step_exp K lam hK hl0 hl1 η a ζ ha π y hπ0 hπ1 hmean hζ hbox hsmall hiso
  have hPhi : ∑ o, π o * Phi A K lam η (ζ + y o) ≤ Phi A K lam η ζ := by
    simp only [Phi, mul_sum]
    rw [sum_comm]
    refine sum_le_sum (fun a haA => ?_)
    simp only [mul_add, sum_add_distrib]
    refine add_le_add (hexp a (hA a haA)) (hexp (-a) (fun j => ?_))
    simpa [abs_neg] using hA a haA j
  obtain ⟨o, hoPhi⟩ : ∃ o, Phi A K lam η (ζ + y o) ≤ Phi A K lam η ζ := by
    by_contra hcon
    push Not at hcon
    have : Nonempty (Fin N × Bool) := ⟨(⟨0, hN⟩, true)⟩
    have hlt : ∑ o, π o * Phi A K lam η ζ < ∑ o, π o * Phi A K lam η (ζ + y o) :=
      sum_lt_sum_of_nonempty univ_nonempty
        (fun o _ => mul_lt_mul_of_pos_left (hcon o) (hπpos o))
    rw [← sum_mul, hπ1, one_mul] at hlt
    linarith
  have heq : ζ + y o = fun j => ζ j + t o * dir o j := rfl
  obtain ⟨hsub, hprog⟩ := step_progress ζ (dir o) (t o) γ (hdsupp o) (hdorth o) (hdnorm o)
    (htprog o)
  refine ⟨ζ + y o, hbox o, fun l => ?_, hoPhi, by rw [heq]; exact hsub, ?_⟩
  · have : ∑ j, g l j * (ζ + y o) j = ∑ j, g l j * ζ j + t o * ∑ j, g l j * dir o j := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl (fun j _ => by simp only [Pi.add_apply, y]; ring)
    rw [this, hdg l o, mul_zero, add_zero]
  · rw [heq]
    have hγsq : γ ^ 2 = 1 / (4 * (Fintype.card ι : ℝ) ^ 2) := by
      rw [hγdef]; field_simp; ring
    rw [← hγsq]
    exact hprog

end SublinearChoresMMS.Disposal.Dev.BW.PartC
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.BW
open SublinearChoresMMS.Disposal
open Finset
alias step_exists := SublinearChoresMMS.Disposal.Dev.BW.PartC.step_exists

end SublinearChoresMMS.Disposal.Dev.BW
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.BW.PartW
open SublinearChoresMMS.Disposal
open Finset
open SublinearChoresMMS.Disposal.Dev.BW
theorem walk {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (g : κ → ι → ℝ)
    (A : Finset (ι → ℝ)) (hA : ∀ a ∈ A, ∀ j, |a j| ≤ 1) (K lam : ℝ) (hK : 1 ≤ K)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (η ζ0 : ι → ℝ) (h0 : ∀ j, 0 ≤ ζ0 j ∧ ζ0 j ≤ 1) :
    ∃ ζ : ι → ℝ, (∀ j, 0 ≤ ζ j ∧ ζ j ≤ 1) ∧
      (∀ l, ∑ j, g l j * ζ j = ∑ j, g l j * ζ0 j) ∧
      ¬ Cond g K ζ ∧ Phi A K lam η ζ ≤ Phi A K lam η ζ0 := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn0 : 0 ≤ n := by positivity
  -- the termination measure
  let m : (ι → ℝ) → ℝ := fun ζ =>
    (4 * n ^ 2 * n + 1) * ((frac ζ).card : ℝ) + 4 * n ^ 2 * (n - ∑ j, ζ j ^ 2)
  have hS : ∀ ζ : ι → ℝ, (∀ j, 0 ≤ ζ j ∧ ζ j ≤ 1) → ∑ j, ζ j ^ 2 ≤ n := by
    intro ζ hb
    calc ∑ j, ζ j ^ 2 ≤ ∑ _j : ι, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := hb j
          nlinarith [this.1, this.2]
      _ = n := by simp [hn]
  have hm0 : ∀ ζ : ι → ℝ, (∀ j, 0 ≤ ζ j ∧ ζ j ≤ 1) → 0 ≤ m ζ := by
    intro ζ hb
    have h1 := hS ζ hb
    have : 0 ≤ 4 * n ^ 2 * (n - ∑ j, ζ j ^ 2) :=
      mul_nonneg (by positivity) (sub_nonneg.2 h1)
    have : 0 ≤ (4 * n ^ 2 * n + 1) * ((frac ζ).card : ℝ) := by positivity
    simp only [m]
    linarith
  have key : ∀ N : ℕ, ∀ ζ : ι → ℝ, (∀ j, 0 ≤ ζ j ∧ ζ j ≤ 1) →
      (∀ l, ∑ j, g l j * ζ j = ∑ j, g l j * ζ0 j) →
      Phi A K lam η ζ ≤ Phi A K lam η ζ0 → m ζ < N →
      ∃ ζ : ι → ℝ, (∀ j, 0 ≤ ζ j ∧ ζ j ≤ 1) ∧
        (∀ l, ∑ j, g l j * ζ j = ∑ j, g l j * ζ0 j) ∧
        ¬ Cond g K ζ ∧ Phi A K lam η ζ ≤ Phi A K lam η ζ0 := by
    intro N
    induction N with
    | zero =>
      intro ζ hb _ _ hlt
      have := hm0 ζ hb
      push_cast at hlt
      linarith
    | succ N ih =>
      intro ζ hb heq hphi hlt
      by_cases hc : Cond g K ζ
      · obtain ⟨ζ', hb', heq', hphi', hsub, hprog⟩ :=
          step_exists g A hA K lam hK hl0 hl1 η ζ hb hc
        have hnpos : 0 < n := by
          have h1 := hc.1
          have h2 : (frac ζ).card ≤ Fintype.card ι := Finset.card_le_univ _
          have : 0 < Fintype.card ι := by omega
          rw [hn]; exact_mod_cast this
        have hf' : ((frac ζ').card : ℝ) ≤ (frac ζ).card := by
          exact_mod_cast Finset.card_le_card hsub
        have hSz := hS ζ hb
        have hS'0 : 0 ≤ ∑ j, ζ' j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
        have ha0 : 0 ≤ 4 * n ^ 2 := by positivity
        have hC0 : 0 ≤ 4 * n ^ 2 * n + 1 := by positivity
        have hdec : m ζ' ≤ m ζ - 1 := by
          simp only [m]
          rcases hprog with h | h
          · have h1 : ((frac ζ').card : ℝ) + 1 ≤ (frac ζ).card := by exact_mod_cast h
            have e1 : 4 * n ^ 2 * (0 - n) ≤ 4 * n ^ 2 * (∑ j, ζ' j ^ 2 - ∑ j, ζ j ^ 2) :=
              mul_le_mul_of_nonneg_left (by linarith) ha0
            have e2 : 0 ≤ (4 * n ^ 2 * n + 1) *
                (((frac ζ).card : ℝ) - (frac ζ').card - 1) :=
              mul_nonneg hC0 (by linarith)
            nlinarith
          · have hone : 4 * n ^ 2 * (1 / (4 * n ^ 2)) = 1 := by
              field_simp
            have e1 : 4 * n ^ 2 * (1 / (4 * n ^ 2)) ≤
                4 * n ^ 2 * (∑ j, ζ' j ^ 2 - ∑ j, ζ j ^ 2) :=
              mul_le_mul_of_nonneg_left (by rw [← hn] at h; linarith) ha0
            have e2 : 0 ≤ (4 * n ^ 2 * n + 1) *
                (((frac ζ).card : ℝ) - (frac ζ').card) :=
              mul_nonneg hC0 (by linarith)
            nlinarith
        refine ih ζ' hb' (fun l => (heq' l).trans (heq l)) (hphi'.trans hphi) ?_
        push_cast at hlt
        linarith
      · exact ⟨ζ, hb, heq, hc, hphi⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (m ζ0)
  exact key N ζ0 h0 (fun _ => rfl) le_rfl hN

end SublinearChoresMMS.Disposal.Dev.BW.PartW
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.BW
open SublinearChoresMMS.Disposal
open Finset
/-! ## Part W: the walk -/
alias walk := SublinearChoresMMS.Disposal.Dev.BW.PartW.walk

end SublinearChoresMMS.Disposal.Dev.BW
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.BW.PartA
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.BW
open Finset
/-! ### Rows of the box with sum one -/
lemma row_pure_or_two {T : Type} [Fintype T] [DecidableEq T] (v : T → ℝ)
    (hbox : ∀ t, 0 ≤ v t ∧ v t ≤ 1) (hsum : ∑ t, v t = 1) :
    (∃ t0, ∀ u, v u = if u = t0 then 1 else 0) ∨
      2 ≤ (univ.filter (fun t => 0 < v t ∧ v t < 1)).card := by
  by_cases h0 : (univ.filter (fun t => 0 < v t ∧ v t < 1)).card = 0
  · left
    rw [card_eq_zero, filter_eq_empty_iff] at h0
    have h01 : ∀ t, v t = 0 ∨ v t = 1 := by
      intro t
      have := h0 (mem_univ t)
      rcases (hbox t).1.eq_or_lt with h | h
      · left; exact h.symm
      · right; by_contra hne; exact this ⟨h, lt_of_le_of_ne (hbox t).2 hne⟩
    have : ∃ t0, v t0 = 1 := by
      by_contra hn
      push Not at hn
      have : ∑ t, v t = 0 := sum_eq_zero (fun t _ => (h01 t).resolve_right (hn t))
      linarith
    obtain ⟨t0, ht0⟩ := this
    refine ⟨t0, fun u => ?_⟩
    by_cases hut : u = t0
    · subst hut; simp [ht0]
    · rw [if_neg hut]
      rcases h01 u with hu | hu
      · exact hu
      · exfalso
        have : v t0 + v u ≤ ∑ t, v t := by
          rw [← sum_pair (Ne.symm hut)]
          exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun t _ _ => (hbox t).1)
        linarith
  · right
    by_contra h1
    have hc1 : (univ.filter (fun t => 0 < v t ∧ v t < 1)).card = 1 := by omega
    obtain ⟨t0, ht0⟩ := card_eq_one.mp hc1
    have hmem : t0 ∈ univ.filter (fun t => 0 < v t ∧ v t < 1) := by
      rw [ht0]; exact mem_singleton_self _
    have hf0 := (mem_filter.mp hmem).2
    have hoth : ∀ u, u ≠ t0 → v u = 0 ∨ v u = 1 := by
      intro u hu
      have hnm : u ∉ univ.filter (fun t => 0 < v t ∧ v t < 1) := by
        rw [ht0]; simpa using hu
      simp only [mem_filter, mem_univ, true_and, not_and, not_lt] at hnm
      rcases (hbox u).1.eq_or_lt with h | h
      · left; exact h.symm
      · right; exact le_antisymm (hbox u).2 (hnm h)
    have hsplit : ∑ t, v t = v t0 + ∑ t ∈ univ.erase t0, v t :=
      (add_sum_erase _ _ (mem_univ t0)).symm
    by_cases hex : ∃ u, u ≠ t0 ∧ v u = 1
    · obtain ⟨u, hu, hv⟩ := hex
      have : v u ≤ ∑ t ∈ univ.erase t0, v t :=
        single_le_sum (fun t _ => (hbox t).1) (mem_erase.mpr ⟨hu, mem_univ u⟩)
      linarith
    · push Not at hex
      have : ∑ t ∈ univ.erase t0, v t = 0 :=
        sum_eq_zero (fun t ht =>
          (hoth t (ne_of_mem_erase ht)).resolve_right (hex t (ne_of_mem_erase ht)))
      linarith

/-! ### Mixed-count bound from `¬ Cond` -/
lemma mixed_bound {I T κ' : Type} [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]
    [Fintype κ'] (g : I ⊕ κ' → I × T → ℝ) (hg : ∀ i (j : I × T), g (Sum.inl i) j ≠ 0 → j.1 = i)
    (ζ : I × T → ℝ) (hbox : ∀ j, 0 ≤ ζ j ∧ ζ j ≤ 1) (hrow : ∀ i, ∑ t, ζ (i, t) = 1)
    (hk : 2 ≤ Fintype.card κ') (hc : ¬ Cond g 8 ζ) :
    ∃ S : Finset I, S.card ≤ 2 * Fintype.card κ' ∧
      ∀ i, (¬ ∃ t0, ∀ u, ζ (i, u) = if u = t0 then 1 else 0) → i ∈ S := by
  set fz : I → ℕ := fun i => (univ.filter (fun t => 0 < ζ (i, t) ∧ ζ (i, t) < 1)).card with hfz
  have hpure : ∀ i, (∃ t0, ∀ u, ζ (i, u) = if u = t0 then 1 else 0) → fz i = 0 := by
    intro i ⟨t0, ht0⟩
    simp only [hfz, card_eq_zero, filter_eq_empty_iff, mem_univ, true_implies, not_and, not_lt]
    intro t h
    rw [ht0 t] at h ⊢; split_ifs at h ⊢ <;> simp_all
  have htwo : ∀ i, 0 < fz i → 2 ≤ fz i := by
    intro i hi
    rcases row_pure_or_two (fun t => ζ (i, t)) (fun t => hbox (i, t)) (hrow i) with h | h
    · exact absurd (hpure i h) hi.ne'
    · exact h
  set S := univ.filter (fun i => 0 < fz i) with hS
  have hF : (frac ζ).card = ∑ i, fz i := by
    simp only [frac, hfz, card_filter, Fintype.sum_prod_type]
  have h2S : 2 * S.card ≤ (frac ζ).card := by
    rw [hF, card_eq_sum_ones, mul_sum, mul_one]
    calc ∑ i ∈ S, 2 ≤ ∑ i ∈ S, fz i :=
          sum_le_sum (fun i hi => htwo i (mem_filter.mp hi).2)
      _ ≤ ∑ i, fz i := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have hact : act g ζ ≤ S.card + Fintype.card κ' := by
    unfold act
    rw [card_filter, Fintype.sum_sum_type, hS, card_filter]
    gcongr with i _ r _
    · split_ifs with h1 h2 <;> try omega
      exfalso
      obtain ⟨j, hj, hgj⟩ := h1
      have hj1 := hg i j hgj
      apply h2
      apply Finset.card_pos.mpr
      refine ⟨j.2, ?_⟩
      have : j = (i, j.2) := Prod.ext hj1 rfl
      rw [this] at hj
      simpa [frac] using hj
    · rw [← card_univ, card_eq_sum_ones]
      exact sum_le_sum (fun r _ => by split_ifs <;> omega)
  refine ⟨S, ?_, ?_⟩
  · unfold Cond at hc
    by_cases h1 : act g ζ + 1 < (frac ζ).card
    · have h2 : ¬ ((frac ζ).card : ℝ) ≤ 8 * (((frac ζ).card : ℝ) - act g ζ - 1) :=
        fun h => hc ⟨h1, h⟩
      push Not at h2
      have e1 : ((2 * S.card : ℕ) : ℝ) ≤ (frac ζ).card := by exact_mod_cast h2S
      have e2 : ((act g ζ : ℕ) : ℝ) ≤ ((S.card + Fintype.card κ' : ℕ) : ℝ) := by
        exact_mod_cast hact
      have e3 : (2 : ℝ) ≤ Fintype.card κ' := by exact_mod_cast hk
      push_cast at e1 e2
      have : (S.card : ℝ) ≤ 2 * Fintype.card κ' := by linarith
      exact_mod_cast this
    · omega
  · intro i hi
    rw [hS, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rcases row_pure_or_two (fun t => ζ (i, t)) (fun t => hbox (i, t)) (hrow i) with h | h
    · exact absurd h hi
    · simp only [hfz]; omega

/-! ### The potential bounds -/
lemma exp_le_Phi {ι : Type} [Fintype ι] (A : Finset (ι → ℝ)) (lam : ℝ) (hl : 0 ≤ lam)
    (η ζ : ι → ℝ) (hζ : ∀ j, 0 ≤ ζ j ∧ ζ j ≤ 1) (a : ι → ℝ) (ha : a ∈ A) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) :
    Real.exp (lam / (8 * 8) * (σ * ∑ j, a j * (ζ j - η j))) ≤ Phi A 8 lam η ζ := by
  have hα : 0 ≤ lam / (8 * 8) := by positivity
  have hvar : 0 ≤ lam * ∑ j, a j ^ 2 * (ζ j * (1 - ζ j)) := by
    apply mul_nonneg hl
    exact sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _)
      (mul_nonneg (hζ j).1 (by linarith [(hζ j).2])))
  have hterm : Real.exp (lam / (8 * 8) * (σ * ∑ j, a j * (ζ j - η j))) ≤
      Real.exp (lam / (8 * 8) * Zf lam η a ζ) +
        Real.exp (lam / (8 * 8) * Zf lam η (-a) ζ) := by
    rcases hσ with rfl | rfl
    · have : Real.exp (lam / (8 * 8) * (1 * ∑ j, a j * (ζ j - η j))) ≤
          Real.exp (lam / (8 * 8) * Zf lam η a ζ) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hα
        unfold Zf; linarith
      linarith [Real.exp_pos (lam / (8 * 8) * Zf lam η (-a) ζ)]
    · have : Real.exp (lam / (8 * 8) * (-1 * ∑ j, a j * (ζ j - η j))) ≤
          Real.exp (lam / (8 * 8) * Zf lam η (-a) ζ) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hα
        unfold Zf
        simp only [Pi.neg_apply, neg_mul, sum_neg_distrib, neg_sq]
        linarith
      linarith [Real.exp_pos (lam / (8 * 8) * Zf lam η a ζ)]
  unfold Phi
  refine hterm.trans ?_
  exact single_le_sum (f := fun a => Real.exp (lam / (8 * 8) * Zf lam η a ζ) +
      Real.exp (lam / (8 * 8) * Zf lam η (-a) ζ))
    (fun b _ => by positivity) ha

lemma Phi_eta_le {ι : Type} [Fintype ι] (A : Finset (ι → ℝ)) (lam : ℝ) (hl : 0 ≤ lam)
    (η : ι → ℝ) (V : ℝ) (hV : ∀ a ∈ A, ∑ j, a j ^ 2 * (η j * (1 - η j)) ≤ V) :
    Phi A 8 lam η η ≤ 2 * A.card * Real.exp (lam / (8 * 8) * (lam * V)) := by
  have hα : 0 ≤ lam / (8 * 8) := by positivity
  have hZ : ∀ a ∈ A, Zf lam η a η ≤ lam * V := by
    intro a ha
    unfold Zf
    simp only [sub_self, mul_zero, sum_const_zero, zero_add]
    exact mul_le_mul_of_nonneg_left (hV a ha) hl
  have hZn : ∀ a ∈ A, Zf lam η (-a) η ≤ lam * V := by
    intro a ha
    unfold Zf
    simp only [sub_self, mul_zero, sum_const_zero, zero_add, Pi.neg_apply, neg_sq]
    exact mul_le_mul_of_nonneg_left (hV a ha) hl
  unfold Phi
  calc ∑ a ∈ A, (Real.exp (lam / (8 * 8) * Zf lam η a η) +
        Real.exp (lam / (8 * 8) * Zf lam η (-a) η))
      ≤ ∑ _a ∈ A, 2 * Real.exp (lam / (8 * 8) * (lam * V)) := by
        apply sum_le_sum
        intro a ha
        have h1 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hZ a ha) hα)
        have h2 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hZn a ha) hα)
        linarith
    _ = 2 * A.card * Real.exp (lam / (8 * 8) * (lam * V)) := by
        rw [sum_const, nsmul_eq_mul]; ring

/-! ### The application, for a general block size -/
lemma core {n m q : ℕ} (c : Cost n m) (R : Finset (Fin n)) (p : Packings n m q R)
    (φ : Coefficients n q R) (hq : 0 < q) (hnR : (0 : ℝ) < n) (hR1 : 1 ≤ R.card)
    (heta : ∀ i e, (∑ t, eta n q t * completed c p i t e) = 1 / (n : ℝ))
    (hcomp : ∀ i t e, 0 ≤ completed c p i t e ∧ completed c p i t e ≤ 1 / (q : ℝ))
    (hetasum : ∑ t, eta n q t = 1) (hη0 : ∀ t, 0 ≤ eta n q t)
    (hΓ1 : 1 ≤ profiles c p) (hΛq : Real.log (2 * (profiles c p : ℝ)) ≤ 3 / 2 * q) :
    ∃ ζ : Coefficients n q R,
      Simplex ζ ∧
      (∀ j ∈ R, (∑ i, ∑ t, ζ i t * fractionalCost c j (completed c p i t)) =
        ((n - R.card : ℕ) : ℝ) * propShare c j) ∧
      mixedCount ζ ≤ 2 * (R.card + 1) ∧
      (∀ e, |∑ i, ∑ t, (ζ i t - eta n q t) * completed c p i t e| ≤
        300 / 2 * Real.sqrt (Real.log (2 * (profiles c p : ℝ)) / q)) ∧
      (∑ i, ∑ t, φ i t * ζ i t) = ∑ i, ∑ t, φ i t * eta n q t := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcardN : Fintype.card (Ordinary R) = n - R.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
  have hNn : (Fintype.card (Ordinary R) : ℝ) ≤ n := by
    rw [hcardN]; exact_mod_cast Nat.sub_le n R.card
  have hη1 : ∀ t, eta n q t ≤ 1 := by
    intro t
    rw [← hetasum]
    exact single_le_sum (f := fun t => eta n q t) (fun t _ => hη0 t) (mem_univ t)
  have hAΓ : ∀ A : Finset (Ordinary R × Fin (n / q) → ℝ), A.card ≤ profiles c p →
      2 * (A.card : ℝ) ≤ Real.exp (Real.log (2 * (profiles c p : ℝ))) := by
    intro A hA
    have : (1 : ℝ) ≤ profiles c p := by exact_mod_cast hΓ1
    rw [Real.exp_log (by linarith)]
    have : (A.card : ℝ) ≤ profiles c p := by exact_mod_cast hA
    linarith
  have hΓpos : (1 : ℝ) < 2 * (profiles c p : ℝ) := by
    have : (1 : ℝ) ≤ profiles c p := by exact_mod_cast hΓ1
    linarith
  generalize hΛdef : Real.log (2 * (profiles c p : ℝ)) = Λ at hΛq hAΓ ⊢
  have hΛpos : 0 < Λ := by rw [← hΛdef]; exact Real.log_pos hΓpos
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (Λ / q) := ⟨_, rfl⟩
  rw [← hsdef]
  have hs2 : s ^ 2 = Λ / q := by rw [hsdef]; exact Real.sq_sqrt (div_nonneg hΛpos.le hqR.le)
  have hspos : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr (div_pos hΛpos hqR)
  have hΛs : Λ = q * s ^ 2 := by rw [hs2]; field_simp
  have hs2le : s ^ 2 ≤ 3 / 2 := by
    rw [hs2, div_le_iff₀ hqR]; linarith
  have hs2' : s ≤ 2 := by nlinarith
  obtain ⟨lam, hlamdef⟩ : ∃ lam, lam = s / 2 := ⟨_, rfl⟩
  have hl0 : 0 < lam := by rw [hlamdef]; positivity
  have hl1 : lam ≤ 1 := by rw [hlamdef]; linarith
  -- the functionals
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : Ordinary R ⊕ ((↥R) ⊕ Unit) → Ordinary R × Fin (n / q) → ℝ,
      (∀ i j, g (Sum.inl i) j = if j.1 = i then 1 else 0) ∧
      (∀ (r : ↥R) j, g (Sum.inr (Sum.inl r)) j = fractionalCost c r.val (completed c p j.1 j.2)) ∧
      (∀ j, g (Sum.inr (Sum.inr ())) j = φ j.1 j.2) :=
    ⟨fun l j => Sum.elim (fun i => if j.1 = i then (1 : ℝ) else 0)
      (Sum.elim (fun r : ↥R => fractionalCost c r.val (completed c p j.1 j.2))
        (fun _ => φ j.1 j.2)) l, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  -- the test vectors
  obtain ⟨A, hAmem, hAin, hAcard⟩ : ∃ A : Finset (Ordinary R × Fin (n / q) → ℝ),
      (∀ a ∈ A, ∃ e, a = fun it => (q : ℝ) * completed c p it.1 it.2 e) ∧
      (∀ e, (fun it : Ordinary R × Fin (n / q) => (q : ℝ) * completed c p it.1 it.2 e) ∈ A) ∧
      A.card ≤ profiles c p := by
    refine ⟨(univ.image (fun e : Fin m => fun (i : Ordinary R) (t : Fin (n / q)) =>
      completed c p i t e)).image (fun f => fun it : Ordinary R × Fin (n / q) =>
        (q : ℝ) * f it.1 it.2), ?_, ?_, ?_⟩
    · intro a ha
      simp only [mem_image, mem_univ, true_and] at ha
      obtain ⟨f, ⟨e, rfl⟩, rfl⟩ := ha
      exact ⟨e, rfl⟩
    · intro e
      simp only [mem_image, mem_univ, true_and]
      exact ⟨_, ⟨e, rfl⟩, rfl⟩
    · exact card_image_le
  have hA : ∀ a ∈ A, ∀ j, |a j| ≤ 1 := by
    intro a ha j
    obtain ⟨e, rfl⟩ := hAmem a ha
    obtain ⟨h0, h1⟩ := hcomp j.1 j.2 e
    have : (q : ℝ) * completed c p j.1 j.2 e ≤ 1 := by
      calc (q : ℝ) * completed c p j.1 j.2 e ≤ q * (1 / q) :=
            mul_le_mul_of_nonneg_left h1 hqR.le
        _ = 1 := by field_simp
    rw [abs_le]; constructor <;> nlinarith
  -- run the walk from η
  obtain ⟨ηι, hηι⟩ : ∃ ηι : Ordinary R × Fin (n / q) → ℝ, ηι = fun j => eta n q j.2 :=
    ⟨_, rfl⟩
  obtain ⟨ζ, hbox, heq, hncond, hPhi⟩ :=
    walk g A hA 8 lam (by norm_num) hl0 hl1 ηι ηι (fun j => by rw [hηι]; exact ⟨hη0 j.2, hη1 j.2⟩)
  have hsum : ∀ (l : Ordinary R ⊕ ((↥R) ⊕ Unit)),
      ∑ i, ∑ t, g l (i, t) * ζ (i, t) = ∑ i, ∑ t, g l (i, t) * eta n q t := by
    intro l
    have := heq l
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at this
    rw [hηι] at this
    exact this
  have hrow : ∀ i, ∑ t, ζ (i, t) = 1 := by
    intro i
    have h := hsum (Sum.inl i)
    simp only [hg1] at h
    rw [sum_eq_single i, sum_eq_single i] at h
    · simpa [hetasum] using h
    all_goals first
      | (intro b _ hb; simp [hb])
      | (intro h; exact absurd (mem_univ _) h)
  refine ⟨fun i t => ζ (i, t), ⟨fun i t => (hbox (i, t)).1, hrow⟩, ?_, ?_, ?_, ?_⟩
  · -- reserved equations
    intro j hj
    have h := hsum (Sum.inr (Sum.inl ⟨j, hj⟩))
    simp only [hg2] at h
    have hη : ∀ i : Ordinary R, ∑ t, fractionalCost c j (completed c p i t) * eta n q t =
        propShare c j := by
      intro i
      unfold fractionalCost
      simp_rw [sum_mul]
      rw [sum_comm]
      have : ∀ e, ∑ t, c j e * completed c p i t e * eta n q t = c j e * (1 / n) := by
        intro e
        rw [← heta i e, mul_sum]
        exact sum_congr rfl (fun t _ => by ring)
      simp_rw [this]
      unfold propShare cost ChoresEFX.cost
      rw [sum_div]
      exact sum_congr rfl (fun e _ => by ring)
    simp only [hη, sum_const, card_univ, hcardN, nsmul_eq_mul] at h
    rw [← h]
    exact sum_congr rfl (fun i _ => sum_congr rfl (fun t _ => by ring))
  · -- mixed count
    have hk : 2 ≤ Fintype.card ((↥R) ⊕ Unit) := by
      rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_unit]; omega
    obtain ⟨S, hS, hSmem⟩ := mixed_bound g
      (fun i j h => by rw [hg1] at h; by_contra hne; exact h (if_neg hne)) ζ hbox hrow hk hncond
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_unit] at hS
    classical
    unfold mixedCount
    refine le_trans (card_le_card ?_) hS
    intro i hi
    rw [mem_filter] at hi
    exact hSmem i hi.2
  · -- discrepancy
    intro e
    have ha := hAin e
    obtain ⟨a, hadef⟩ : ∃ a : Ordinary R × Fin (n / q) → ℝ,
        a = fun it => (q : ℝ) * completed c p it.1 it.2 e := ⟨_, rfl⟩
    rw [← hadef] at ha
    obtain ⟨D, hD⟩ : ∃ D, D = ∑ i, ∑ t, (ζ (i, t) - eta n q t) * completed c p i t e :=
      ⟨_, rfl⟩
    rw [← hD]
    have haD : ∑ j, a j * (ζ j - ηι j) = q * D := by
      rw [Fintype.sum_prod_type, hD, mul_sum, hadef, hηι]
      exact sum_congr rfl (fun i _ => by rw [mul_sum]; exact sum_congr rfl (fun t _ => by ring))
    have hV : ∀ a' ∈ A, ∑ j, a' j ^ 2 * (ηι j * (1 - ηι j)) ≤ (q : ℝ) := by
      intro a' ha'
      obtain ⟨e', rfl⟩ := hAmem a' ha'
      rw [Fintype.sum_prod_type, hηι]
      calc ∑ i, ∑ t, ((q : ℝ) * completed c p i t e') ^ 2 * (eta n q t * (1 - eta n q t))
          ≤ ∑ i : Ordinary R, ∑ t, (q : ℝ) * (eta n q t * completed c p i t e') := by
            apply sum_le_sum; intro i _; apply sum_le_sum; intro t _
            obtain ⟨h0, h1⟩ := hcomp i t e'
            have hx1 : (q : ℝ) * completed c p i t e' ≤ 1 := by
              calc (q : ℝ) * completed c p i t e' ≤ q * (1 / q) :=
                    mul_le_mul_of_nonneg_left h1 hqR.le
                _ = 1 := by field_simp
            have hx0 : 0 ≤ (q : ℝ) * completed c p i t e' := mul_nonneg hqR.le h0
            have he0 := hη0 t
            have he1 := hη1 t
            have : ((q : ℝ) * completed c p i t e') ^ 2 * (eta n q t * (1 - eta n q t)) ≤
                ((q : ℝ) * completed c p i t e') * eta n q t := by
              have hy : ((q : ℝ) * completed c p i t e') * (1 - eta n q t) ≤ 1 := by
                nlinarith
              have hz : 0 ≤ ((q : ℝ) * completed c p i t e') * eta n q t := mul_nonneg hx0 he0
              calc ((q : ℝ) * completed c p i t e') ^ 2 * (eta n q t * (1 - eta n q t))
                  = (((q : ℝ) * completed c p i t e') * eta n q t) *
                      (((q : ℝ) * completed c p i t e') * (1 - eta n q t)) := by ring
                _ ≤ (((q : ℝ) * completed c p i t e') * eta n q t) * 1 :=
                    mul_le_mul_of_nonneg_left hy hz
                _ = _ := by ring
            linarith
        _ = ∑ _i : Ordinary R, (q : ℝ) * (1 / n) := by
            refine sum_congr rfl (fun i _ => ?_)
            rw [← mul_sum, heta i e']
        _ ≤ (q : ℝ) := by
            rw [sum_const, card_univ, nsmul_eq_mul]
            rw [show (Fintype.card (Ordinary R) : ℝ) * ((q : ℝ) * (1 / n)) =
              q * ((Fintype.card (Ordinary R) : ℝ) / n) by ring]
            have : (Fintype.card (Ordinary R) : ℝ) / n ≤ 1 := by
              rw [div_le_one hnR]; exact hNn
            nlinarith
    have hP0 := Phi_eta_le A lam hl0.le ηι q hV
    have hΓexp : 2 * (A.card : ℝ) ≤ Real.exp Λ := hAΓ A hAcard
    have hbound : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → σ * D ≤ 150 * s := by
      intro σ hσ
      have h1 := exp_le_Phi A lam hl0.le ηι ζ hbox a ha σ hσ
      have h2 : Real.exp (lam / (8 * 8) * (σ * (q * D))) ≤
          Real.exp (Λ + lam / (8 * 8) * (lam * q)) := by
        rw [Real.exp_add, ← haD]
        calc _ ≤ Phi A 8 lam ηι ζ := h1
          _ ≤ Phi A 8 lam ηι ηι := hPhi
          _ ≤ 2 * A.card * Real.exp (lam / (8 * 8) * (lam * q)) := hP0
          _ ≤ Real.exp Λ * Real.exp (lam / (8 * 8) * (lam * q)) :=
              mul_le_mul_of_nonneg_right hΓexp (Real.exp_pos _).le
      have h3 := Real.exp_le_exp.mp h2
      rw [hΛs, hlamdef] at h3
      rw [hlamdef] at hl0
      -- h3 : s/2/64 * (σ * (q*D)) ≤ q s^2 + s/2/64 * (s/2 * q)
      have hqs : 0 < q * s := mul_pos hqR hspos
      have key : (q * s) * (σ * D) ≤ (q * s) * (150 * s) := by
        nlinarith
      exact le_of_mul_le_mul_left key hqs
    have hup := hbound 1 (Or.inl rfl)
    have hlo := hbound (-1) (Or.inr rfl)
    rw [abs_le]
    constructor <;> [skip; skip] <;> norm_num at hup hlo ⊢ <;> linarith
  · -- the φ equation
    have h := hsum (Sum.inr (Sum.inr ()))
    simp only [hg3] at h
    rw [← h]

/-! ### The application -/
theorem lemma_3_2_steps_1_2_dev (B : ℝ) (hB : 0 < B) :
    ∃ C₄ : ℝ, 0 < C₄ ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ (m : ℕ) (c : Cost n m),
        Normalized c → blockSize n ≤ m → blockSize n ∣ m →
        ∀ R : Finset (Fin n), 1 ≤ R.card → R.card < n →
          4 * Real.log n ≤ (blockSize n : ℝ) →
          ∀ p : Packings n m (blockSize n) R,
            (∀ i, ValidPacking c i.val (p i)) →
            (∀ i, (segments (p i) : ℝ) ≤ B * (n / blockSize n : ℕ) ^ 3) →
            ∀ φ : Coefficients n (blockSize n) R,
              ∃ ζ : Coefficients n (blockSize n) R,
                Simplex ζ ∧
                (∀ j ∈ R, (∑ i, ∑ t, ζ i t * fractionalCost c j (completed c p i t)) =
                  ((n - R.card : ℕ) : ℝ) * propShare c j) ∧
                mixedCount ζ ≤ 2 * (R.card + 1) ∧
                (∀ e, |∑ i, ∑ t, (ζ i t - eta n (blockSize n) t) * completed c p i t e| ≤
                  C₄ / 2 * Real.sqrt (Real.log (2 * (profiles c p : ℝ)) / blockSize n)) ∧
                (∑ i, ∑ t, φ i t * ζ i t) = ∑ i, ∑ t, φ i t * eta n (blockSize n) t := by
  obtain ⟨n₂, hprof⟩ := Dev.L32.PartX.profiles_le B
  refine ⟨300, by norm_num, max n₂ 3, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn m c hc hqm hdiv R hR1 hRn hlog p hp hseg φ
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnn₂ : n₂ ≤ n := le_trans (le_max_left _ _) hn
  have hq := Dev.L32.PartY.block_pos n
  have hqn := Dev.L32.PartY.block_le_n hn3
  obtain ⟨heta, -, hcomp⟩ := Dev.L32.PartX.completed_facts hq hqn hqm hdiv c hc R hRn p hp
  have hΓ := hprof n hnn₂ m (blockSize n) c hq hqn hdiv R p hseg
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnR : (0 : ℝ) < n := by linarith
  have hqR : (0 : ℝ) < blockSize n := by exact_mod_cast hq
  have hlogn : 0 < Real.log n := lt_trans one_pos (Dev.L32.PartY.log_pos3 hn3)
  have hη0 : ∀ t, 0 ≤ eta n (blockSize n) t := fun t =>
    le_trans (div_nonneg hqR.le hnR.le) (Dev.L32.PartX.eta_bounds hq hqn t).1
  have hΓ1 : 1 ≤ profiles c p := by
    unfold profiles
    apply card_pos.mpr
    have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    exact univ_nonempty.image _
  have hΛn : Real.log (2 * (profiles c p : ℝ)) ≤ 6 * Real.log n := by
    have hΓr : (profiles c p : ℝ) ≤ (n : ℝ) ^ 5 := by exact_mod_cast hΓ
    have hΓ1r : (1 : ℝ) ≤ profiles c p := by exact_mod_cast hΓ1
    have h2 : 2 * (profiles c p : ℝ) ≤ (n : ℝ) ^ 6 := by
      have : (0 : ℝ) ≤ (n : ℝ) ^ 5 := by positivity
      nlinarith
    calc Real.log (2 * (profiles c p : ℝ)) ≤ Real.log ((n : ℝ) ^ 6) :=
          Real.log_le_log (by linarith) h2
      _ = 6 * Real.log n := by rw [Real.log_pow]; norm_num
  have := core c R p φ hq hnR hR1 heta hcomp (Dev.L32.PartX.eta_sum hq hqn) hη0 hΓ1
    (by linarith)
  exact this

end SublinearChoresMMS.Disposal.Dev.BW.PartA
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.BW
open SublinearChoresMMS.Disposal
open Finset
/-! ## Part A: the application -/
alias lemma_3_2_steps_1_2_dev := SublinearChoresMMS.Disposal.Dev.BW.PartA.lemma_3_2_steps_1_2_dev

end SublinearChoresMMS.Disposal.Dev.BW
end
end

section
noncomputable section
open SublinearChoresMMS
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev
open SublinearChoresMMS.Disposal.Dev.BW
open SublinearChoresMMS.Disposal
open Finset
theorem solution (B : ℝ) (hB : 0 < B) :
    ∃ C₄ : ℝ, 0 < C₄ ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ (m : ℕ) (c : Cost n m),
        Normalized c → blockSize n ≤ m → blockSize n ∣ m →
        ∀ R : Finset (Fin n), 1 ≤ R.card → R.card < n →
          4 * Real.log n ≤ (blockSize n : ℝ) →
          ∀ p : Packings n m (blockSize n) R,
            (∀ i, ValidPacking c i.val (p i)) →
            (∀ i, (segments (p i) : ℝ) ≤ B * (n / blockSize n : ℕ) ^ 3) →
            ∀ φ : Coefficients n (blockSize n) R,
              ∃ ζ : Coefficients n (blockSize n) R,
                Simplex ζ ∧
                (∀ j ∈ R, (∑ i, ∑ t, ζ i t * fractionalCost c j (completed c p i t)) =
                  ((n - R.card : ℕ) : ℝ) * propShare c j) ∧
                mixedCount ζ ≤ 2 * (R.card + 1) ∧
                (∀ e, |∑ i, ∑ t, (ζ i t - eta n (blockSize n) t) * completed c p i t e| ≤
                  C₄ / 2 * Real.sqrt (Real.log (2 * (profiles c p : ℝ)) / blockSize n)) ∧
                (∑ i, ∑ t, φ i t * ζ i t) = ∑ i, ∑ t, φ i t * eta n (blockSize n) t := by
  exact SublinearChoresMMS.Disposal.Dev.BW.lemma_3_2_steps_1_2_dev B hB
end
end
