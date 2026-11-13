-- Prove2me | solution 1 for SublinearChoresMMS.Disposal.lemma_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T10:16:25.558968+00:00
-- url     : https://prove2.me/submissions/469cc0ca-f8fc-45f7-b27c-441957d114a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Slots
import Definitions.Def_SublinearChoresMMS_Disposal_Prepared
import Theorems.Thm_SublinearChoresMMS_Disposal_lemma_3_2_steps_1_2
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

end SublinearChoresMMS.Disposal.Dev.L32.PartX
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32
open SublinearChoresMMS.Disposal
open Finset
alias eta_sum := SublinearChoresMMS.Disposal.Dev.L32.PartX.eta_sum

end SublinearChoresMMS.Disposal.Dev.L32
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32.PartX
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.L33
open Finset
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

end SublinearChoresMMS.Disposal.Dev.L32.PartX
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32
open SublinearChoresMMS.Disposal
open Finset
alias eta_bounds := SublinearChoresMMS.Disposal.Dev.L32.PartX.eta_bounds

end SublinearChoresMMS.Disposal.Dev.L32
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32.PartX
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.L33
open Finset
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

end SublinearChoresMMS.Disposal.Dev.L32.PartX
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32
open SublinearChoresMMS.Disposal
open Finset

end SublinearChoresMMS.Disposal.Dev.L32
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32.PartX
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.L33
open Finset
variable {n m q : ℕ}
/-! ### Completed bundles -/
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

end SublinearChoresMMS.Disposal.Dev.L32.PartX
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32.PartX
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.L33
open Finset
/-! ### Counting profiles -/
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

end SublinearChoresMMS.Disposal.Dev.L32.PartX
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32.PartX
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.L33
open Finset
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

end SublinearChoresMMS.Disposal.Dev.L32.PartX
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32.PartX
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.L33
open Finset
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
/-! ## Part X: the prepared bundles -/
alias profiles_le := SublinearChoresMMS.Disposal.Dev.L32.PartX.profiles_le

alias completed_facts := SublinearChoresMMS.Disposal.Dev.L32.PartX.completed_facts

end SublinearChoresMMS.Disposal.Dev.L32
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32.PartY
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.L32
open Finset
/-! Part X stubs used by Part Y (copied verbatim from the Blueprint). -/
theorem hull_law {α β : Type} [Fintype α] [Fintype β] (S : Set (α → β → ℝ)) (hS : IsCompact S)
    (η : α → β → ℝ)
    (h : ∀ φ : α → β → ℝ, ∃ ζ ∈ S, (∑ a, ∑ b, φ a b * ζ a b) = ∑ a, ∑ b, φ a b * η a b) :
    ∃ P : FiniteLaw (α → β → ℝ), (∀ a b, P.mean (fun v => v a b) = η a b) ∧
      ∀ k : Fin P.size, 0 < P.weight k → P.atom k ∈ S := by
  classical
  obtain ⟨s₀, hs₀, -⟩ := h 0
  let N := Module.finrank ℝ (α → β → ℝ)
  let F : (Fin (N+1) → ℝ) × (Fin (N+1) → (α → β → ℝ)) → (α → β → ℝ) :=
    fun p => ∑ j, p.1 j • p.2 j
  let D := stdSimplex ℝ (Fin (N+1)) ×ˢ Set.pi Set.univ (fun _ : Fin (N+1) => S)
  have hDc : IsCompact D := IsCompact.prod (isCompact_stdSimplex ℝ _) (isCompact_univ_pi fun _ => hS)
  have hFc : Continuous F := by fun_prop
  have hK : F '' D = convexHull ℝ S := by
    apply subset_antisymm
    · rintro _ ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
      exact (convex_convexHull ℝ S).sum_mem (fun j _ => hw.1 j) hw.2
        (fun j _ => subset_convexHull ℝ S (hz j (Set.mem_univ _)))
    · intro x hx
      obtain ⟨ι, _, z, w, hzS, hai, hw, hw1, hxs⟩ := eq_pos_convex_span_of_mem_convexHull hx
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
        (by
          have h1 := hai.card_le_finrank_succ
          have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
          show Fintype.card ι ≤ Fintype.card (Fin (N+1))
          rw [Fintype.card_fin]
          omega)
      let w' : Fin (N+1) → ℝ := fun j => ∑ i, if e i = j then w i else 0
      let z' : Fin (N+1) → (α → β → ℝ) := fun j => if h : ∃ i, e i = j then z h.choose else s₀
      have hz' : ∀ i, z' (e i) = z i := by
        intro i
        have h : ∃ i', e i' = e i := ⟨i, rfl⟩
        simp only [z', dif_pos h]
        rw [e.injective h.choose_spec]
      refine ⟨(w', z'), ⟨⟨fun j => show 0 ≤ ∑ i, (if e i = j then w i else 0) from
        Finset.sum_nonneg (fun i _ => ?_), ?_⟩, ?_⟩, ?_⟩
      · split_ifs
        · exact (hw i).le
        · exact le_rfl
      · simp only [w']
        rw [Finset.sum_comm]
        simp [hw1]
      · intro j _
        simp only [z']
        split_ifs with h
        · exact hzS ⟨_, rfl⟩
        · exact hs₀
      · simp only [F, w']
        simp_rw [Finset.sum_smul]
        rw [Finset.sum_comm]
        simp [ite_smul, hz', hxs]
  have hη : η ∈ convexHull ℝ S := by
    by_contra hne
    rw [← hK] at hne
    obtain ⟨f, u, hfu, huη⟩ := geometric_hahn_banach_closed_point
      (hK ▸ convex_convexHull ℝ S) (hDc.image hFc).isClosed hne
    let φ : α → β → ℝ := fun a b => f (Pi.single a (Pi.single b 1))
    have hf : ∀ v, f v = ∑ a, ∑ b, φ a b * v a b := by
      intro v
      have hv : v = ∑ a, ∑ b, v a b • (Pi.single a (Pi.single b 1) : α → β → ℝ) := by
        funext a' b'
        simp [Finset.sum_apply, Pi.single_apply, ite_apply, Finset.sum_ite_eq]
      conv_lhs => rw [hv]
      simp [map_sum, map_smul, φ, mul_comm]
    obtain ⟨ζ, hζS, hζ⟩ := h φ
    have h1 := hfu ζ (hK ▸ subset_convexHull ℝ S hζS)
    rw [hf, hζ, ← hf] at h1
    linarith
  obtain ⟨ι, _, w, z, hw, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hη
  let L : OAI.CliqueFreeIndependence.Lottery.Law (α → β → ℝ) :=
    (Finset.univ : Finset ι).toList.map (fun i => (w i, z i))
  have hexp : ∀ g, OAI.CliqueFreeIndependence.Lottery.expect L g = ∑ i, w i * g (z i) := by
    intro g
    simp [OAI.CliqueFreeIndependence.Lottery.expect, L, List.map_map, Function.comp_def,
      Finset.sum_map_toList]
  refine ⟨⟨L, ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · intro p hp
    simp only [L, List.mem_map] at hp
    obtain ⟨i, -, rfl⟩ := hp
    exact hw i
  · unfold OAI.CliqueFreeIndependence.Lottery.total
    rw [hexp]
    simpa using hw1
  · intro a b
    show OAI.CliqueFreeIndependence.Lottery.expect L _ = _
    rw [hexp, ← hsum]
    simp [Finset.sum_apply]
  · intro k _
    show L[k.val].2 ∈ S
    simp only [L, List.getElem_map]
    exact hz _

end SublinearChoresMMS.Disposal.Dev.L32.PartY
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32
open SublinearChoresMMS.Disposal
open Finset
/-! ## Part Y: separation and assembly -/

end SublinearChoresMMS.Disposal.Dev.L32
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32.PartY
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev.L32
open Finset
lemma isClosed_pure {n q : ℕ} {R : Finset (Fin n)} (i : Ordinary R) :
    IsClosed {v : Coefficients n q R | Pure v i} := by
  have : {v : Coefficients n q R | Pure v i} =
      ⋃ t : Fin (n / q), ⋂ u : Fin (n / q), {v | v i u = if u = t then 1 else 0} := by
    ext v; simp [Pure]
  rw [this]
  exact isClosed_iUnion_of_finite fun t => isClosed_iInter fun u =>
    isClosed_eq (by fun_prop) continuous_const

lemma isClosed_mixed {n q : ℕ} {R : Finset (Fin n)} (M : ℕ) :
    IsClosed {v : Coefficients n q R | mixedCount v ≤ M} := by
  classical
  have : {v : Coefficients n q R | mixedCount v ≤ M}ᶜ =
      ⋃ T : {T : Finset (Ordinary R) // M < T.card}, ⋂ i ∈ T.1, {v | ¬Pure v i} := by
    ext v
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro hv
      refine ⟨⟨Finset.univ.filter (fun i => ¬Pure v i), ?_⟩, ?_⟩
      · unfold mixedCount at hv; convert hv
      · intro i hi; simpa using hi
    · rintro ⟨⟨T, hT⟩, hTv⟩
      unfold mixedCount
      refine lt_of_lt_of_le hT (Finset.card_le_card ?_)
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      convert hTv i hi
  rw [← isOpen_compl_iff, this]
  exact isOpen_iUnion fun T => isOpen_biInter_finset fun i _ => (isClosed_pure i).isOpen_compl

theorem isCompact_coordinated {n m q : ℕ} (c : Cost n m) {R : Finset (Fin n)}
    (p : Packings n m q R) (M : ℕ) :
    IsCompact {v : Coefficients n q R | Coordinated c p v ∧ mixedCount v ≤ M} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have : {v : Coefficients n q R | Coordinated c p v ∧ mixedCount v ≤ M} =
        ((⋂ i, ⋂ t, {v : Coefficients n q R | 0 ≤ v i t}) ∩
          (⋂ i, {v : Coefficients n q R | ∑ t, v i t = 1})) ∩
        (⋂ e, {v | ordinaryFraction c p v e ≤ 1}) ∩
        (⋂ j ∈ R, {v | (∑ i, ∑ t, v i t * fractionalCost c j (completed c p i t)) =
          ((n - R.card : ℕ) : ℝ) * propShare c j}) ∩
        {v | mixedCount v ≤ M} := by
      ext v
      simp only [Coordinated, Simplex, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      tauto
    rw [this]
    refine (((IsClosed.inter ?_ ?_).inter ?_).inter ?_).inter (isClosed_mixed M)
    · exact isClosed_iInter fun i => isClosed_iInter fun t =>
        isClosed_le continuous_const (by fun_prop)
    · exact isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_iInter fun e => isClosed_le (by unfold ordinaryFraction; fun_prop)
        continuous_const
    · exact isClosed_biInter fun j _ => isClosed_eq (by fun_prop) continuous_const
  · refine (Metric.isBounded_Icc (0 : Coefficients n q R) 1).subset ?_
    rintro v ⟨⟨⟨h0, h1⟩, -⟩, -⟩
    refine ⟨fun i t => h0 i t, fun i t => ?_⟩
    show v i t ≤ 1
    rw [← h1 i]
    exact Finset.single_le_sum (fun u _ => h0 i u) (Finset.mem_univ t)

end SublinearChoresMMS.Disposal.Dev.L32.PartY
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32
open SublinearChoresMMS.Disposal
open Finset

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

theorem lemma_3_2 (B : ℝ) (hB : 0 < B) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ (m : ℕ) (c : Cost n m),
        Normalized c → blockSize n ≤ m → blockSize n ∣ m →
        ∀ R : Finset (Fin n), 1 ≤ R.card → R.card < n →
          4 * Real.log n ≤ (blockSize n : ℝ) →
          C₂ * n * Real.sqrt (Real.log n / blockSize n) ≤ (R.card : ℝ) →
          ∀ p : Packings n m (blockSize n) R,
            (∀ i, ValidPacking c i.val (p i)) →
            (∀ i, (segments (p i) : ℝ) ≤ B * (n / blockSize n : ℕ) ^ 3) →
            (profiles c p ≤ n ^ 5) ∧
            ((∑ t : Fin (n / blockSize n), eta n (blockSize n) t) = 1) ∧
            (∀ t, (blockSize n : ℝ) / n ≤ eta n (blockSize n) t ∧
              eta n (blockSize n) t ≤ 2 * blockSize n / n) ∧
            (∀ i e, (∑ t, eta n (blockSize n) t * completed c p i t e) = 1 / (n : ℝ)) ∧
            (∀ i t, fractionalCost c i.val (completed c p i t) ≤ 1) ∧
            (∀ i t e, 0 ≤ completed c p i t e ∧ completed c p i t e ≤ 1 / (blockSize n : ℝ)) ∧
            ∃ P : FiniteLaw (Coefficients n (blockSize n) R),
              (∀ i t, P.mean (fun v => v i t) = eta n (blockSize n) t) ∧
              ∀ a : Fin P.size, 0 < P.weight a →
                Coordinated c p (P.atom a) ∧ mixedCount (P.atom a) ≤ 2 * (R.card + 1) := by
  obtain ⟨C₄, hC₄, n₁, -, hsteps⟩ := lemma_3_2_steps_1_2 B hB
  obtain ⟨n₂, hprof⟩ := profiles_le B
  refine ⟨C₄ * Real.sqrt 6 / 2 + 1, by positivity, max (max n₁ n₂) 3,
    le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn m c hc hqm hdiv R hR1 hRn hlog hC₂ p hp hseg
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnn₁ : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnn₂ : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hq := block_pos n
  have hqn := block_le_n hn3
  obtain ⟨heta, hfc, hcomp⟩ := completed_facts hq hqn hqm hdiv c hc R hRn p hp
  have hΓ := hprof n hnn₂ m (blockSize n) c hq hqn hdiv R p hseg
  refine ⟨hΓ, eta_sum hq hqn, fun t => eta_bounds hq hqn t, heta, hfc, hcomp, ?_⟩
  refine Exists.imp (fun P hP => ⟨fun i t => hP.1 i t, fun a ha => hP.2 a ha⟩) (hull_law
    {v : Coefficients n (blockSize n) R | Coordinated c p v ∧ mixedCount v ≤ 2 * (R.card + 1)}
    (isCompact_coordinated c p _) (fun _ t => eta n (blockSize n) t) ?_)
  intro φ
  obtain ⟨ζ, hsim, hres, hmix, hdev, hφ⟩ :=
    hsteps n hnn₁ m c hc hqm hdiv R hR1 hRn hlog p hp hseg φ
  refine ⟨ζ, ⟨⟨hsim, ?_, hres⟩, hmix⟩, hφ⟩
  intro e
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 0 < Real.log n := lt_trans one_pos (log_pos3 hn3)
  have hqpos : (0 : ℝ) < blockSize n := by exact_mod_cast hq
  have hL : Real.log (2 * (profiles c p : ℝ)) ≤ 6 * Real.log n := by
    rcases Nat.eq_zero_or_pos (profiles c p) with h0 | h0
    · simp only [h0, Nat.cast_zero, mul_zero, Real.log_zero]
      positivity
    · have hΓr : (profiles c p : ℝ) ≤ (n : ℝ) ^ 5 := by exact_mod_cast hΓ
      have h2 : 2 * (profiles c p : ℝ) ≤ (n : ℝ) ^ 6 := by
        have : (0 : ℝ) ≤ (n : ℝ) ^ 5 := by positivity
        nlinarith
      have hpos : (0 : ℝ) < 2 * (profiles c p : ℝ) := by
        have : (0 : ℝ) < profiles c p := by exact_mod_cast h0
        linarith
      calc Real.log (2 * (profiles c p : ℝ)) ≤ Real.log ((n : ℝ) ^ 6) :=
            Real.log_le_log hpos h2
        _ = 6 * Real.log n := by rw [Real.log_pow]; norm_num
  set s := Real.sqrt (Real.log n / blockSize n) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt (Real.log (2 * (profiles c p : ℝ)) / blockSize n) ≤ Real.sqrt 6 * s := by
    rw [hs, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right hL hqpos.le
  have hD : C₄ / 2 * Real.sqrt (Real.log (2 * (profiles c p : ℝ)) / blockSize n) ≤
      (C₄ * Real.sqrt 6 / 2 + 1) * s := by
    have := mul_le_mul_of_nonneg_left hsqrt (by linarith : (0 : ℝ) ≤ C₄ / 2)
    nlinarith
  have hdev' := le_trans (le_abs_self _) (le_trans (hdev e) hD)
  have hsplit : ordinaryFraction c p ζ e =
      (∑ i, ∑ t, (ζ i t - eta n (blockSize n) t) * completed c p i t e) +
        ∑ _i : Ordinary R, (1 / (n : ℝ)) := by
    unfold ordinaryFraction
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← heta i e, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have hcard : (Fintype.card (Ordinary R) : ℝ) = n - R.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin,
      Nat.cast_sub hRn.le]
  rw [hsplit, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hkey : (∑ i, ∑ t, (ζ i t - eta n (blockSize n) t) * completed c p i t e) * n ≤ R.card := by
    have := mul_le_mul_of_nonneg_right hdev' hnpos.le
    nlinarith
  have hle : (∑ i, ∑ t, (ζ i t - eta n (blockSize n) t) * completed c p i t e) ≤
      (R.card : ℝ) / n := by
    rw [le_div_iff₀ hnpos]; exact hkey
  have : ((n : ℝ) - R.card) * (1 / n) = 1 - (R.card : ℝ) / n := by
    field_simp
  rw [this]
  linarith

end SublinearChoresMMS.Disposal.Dev.L32.PartY
end
end

section
noncomputable section
namespace SublinearChoresMMS.Disposal.Dev.L32
open SublinearChoresMMS.Disposal
open Finset
alias lemma_3_2 := SublinearChoresMMS.Disposal.Dev.L32.PartY.lemma_3_2

end SublinearChoresMMS.Disposal.Dev.L32
end
end

section
noncomputable section
open SublinearChoresMMS
open SublinearChoresMMS.Disposal
open SublinearChoresMMS.Disposal.Dev
open SublinearChoresMMS.Disposal.Dev.L32
open SublinearChoresMMS.Disposal
open Finset
theorem solution (B : ℝ) (hB : 0 < B) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ (m : ℕ) (c : Cost n m),
        Normalized c → blockSize n ≤ m → blockSize n ∣ m →
        ∀ R : Finset (Fin n), 1 ≤ R.card → R.card < n →
          4 * Real.log n ≤ (blockSize n : ℝ) →
          C₂ * n * Real.sqrt (Real.log n / blockSize n) ≤ (R.card : ℝ) →
          ∀ p : Packings n m (blockSize n) R,
            (∀ i, ValidPacking c i.val (p i)) →
            (∀ i, (segments (p i) : ℝ) ≤ B * (n / blockSize n : ℕ) ^ 3) →
            (profiles c p ≤ n ^ 5) ∧
            ((∑ t : Fin (n / blockSize n), eta n (blockSize n) t) = 1) ∧
            (∀ t, (blockSize n : ℝ) / n ≤ eta n (blockSize n) t ∧
              eta n (blockSize n) t ≤ 2 * blockSize n / n) ∧
            (∀ i e, (∑ t, eta n (blockSize n) t * completed c p i t e) = 1 / (n : ℝ)) ∧
            (∀ i t, fractionalCost c i.val (completed c p i t) ≤ 1) ∧
            (∀ i t e, 0 ≤ completed c p i t e ∧ completed c p i t e ≤ 1 / (blockSize n : ℝ)) ∧
            ∃ P : FiniteLaw (Coefficients n (blockSize n) R),
              (∀ i t, P.mean (fun v => v i t) = eta n (blockSize n) t) ∧
              ∀ a : Fin P.size, 0 < P.weight a →
                Coordinated c p (P.atom a) ∧ mixedCount (P.atom a) ≤ 2 * (R.card + 1) := by
  exact SublinearChoresMMS.Disposal.Dev.L32.lemma_3_2 B hB
end
end
