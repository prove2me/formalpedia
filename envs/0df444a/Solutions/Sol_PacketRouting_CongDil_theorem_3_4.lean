-- Prove2me | solution 1 for PacketRouting.CongDil.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T08:08:54.679254+00:00
-- url     : https://prove2.me/submissions/84ec0ecf-2395-46fd-90d3-f763917af674

import Mathlib
import Definitions.Def_PacketRouting_CongDil_Network
import Definitions.Def_PacketRouting_CongDil_Timetable

-- BEGIN PRProof/SharedBasics.lean

-- END PRProof/SharedBasics.lean

-- BEGIN PRProof/IntegerScales.lean

namespace PacketRouting.CongDil.PRFresh

def scaleExponent (h l : ℕ) : ℕ := h / 2 ^ l

def blockScale (h l : ℕ) : ℕ := 2 ^ scaleExponent h l

def delayScale (h l : ℕ) : ℕ := 2 ^ (scaleExponent h l / 4)

lemma scaleExponent_zero (h : ℕ) : scaleExponent h 0 = h := by
  simp [scaleExponent]

lemma scaleExponent_succ (h l : ℕ) :
    scaleExponent h (l + 1) = scaleExponent h l / 2 := by
  simp [scaleExponent, pow_succ, Nat.div_div_eq_div_mul]

lemma scaleExponent_antitone (h : ℕ) : Antitone (scaleExponent h) := by
  apply antitone_nat_of_succ_le
  intro l
  rw [scaleExponent_succ]
  exact Nat.div_le_self _ _

lemma blockScale_pos (h l : ℕ) : 0 < blockScale h l := by
  unfold blockScale
  positivity

lemma delayScale_pos (h l : ℕ) : 0 < delayScale h l := by
  unfold delayScale
  positivity

lemma blockScale_child_dvd (h l : ℕ) : blockScale h (l + 1) ∣ blockScale h l := by
  apply pow_dvd_pow
  exact scaleExponent_antitone h (Nat.le_succ l)

lemma exists_terminal_scale {H h : ℕ} (hH : 0 < H) (hh : H ≤ h) :
    ∃ L : ℕ, H ≤ scaleExponent h L ∧ scaleExponent h L < 2 * H := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    by_cases hs : h < 2 * H
    · exact ⟨0, by simpa [scaleExponent] using hh, by simpa [scaleExponent] using hs⟩
    · have hhalf : H ≤ h / 2 := by omega
      have hlt : h / 2 < h := by omega
      obtain ⟨L, hlo, hhi⟩ := ih (h / 2) hlt hhalf
      refine ⟨L + 1, ?_, ?_⟩
      · simpa [scaleExponent, pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm] using hlo
      · simpa [scaleExponent, pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm] using hhi

lemma terminal_depth_two {H h L : ℕ} (_hH : 0 < H) (hh : 8 * H ≤ h)
    (hend : scaleExponent h L < 2 * H) : 2 ≤ L := by
  by_contra hn
  interval_cases L <;> simp [scaleExponent] at hend <;> omega

end PacketRouting.CongDil.PRFresh

-- END PRProof/IntegerScales.lean

-- BEGIN PRProof/ScaleDepth.lean

namespace PacketRouting.CongDil.PRFresh

lemma twice_child_exponent_le (h l : ℕ) :
    2 * scaleExponent h (l + 1) ≤ scaleExponent h l := by
  rw [scaleExponent_succ]
  exact Nat.mul_div_le _ _

lemma exponent_depth_bound {h i j : ℕ} (hij : i ≤ j) :
    2 ^ (j - i) * scaleExponent h j ≤ scaleExponent h i := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have he : j + 1 - i = (j - i) + 1 := by omega
    calc
      2 ^ (j + 1 - i) * scaleExponent h (j + 1) =
          2 ^ (j - i) * (2 * scaleExponent h (j + 1)) := by rw [he, pow_succ]; ring
      _ ≤ 2 ^ (j - i) * scaleExponent h j := Nat.mul_le_mul_left _ (twice_child_exponent_le h j)
      _ ≤ scaleExponent h i := ih

lemma slot_exponent_margin {h L H l : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) :
    8 * (L - l + 1) ≤ scaleExponent h l := by
  have hp : L - l + 1 ≤ 2 ^ (L - l) := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have he := exponent_depth_bound (h := h) hl
  have hm := Nat.mul_le_mul_left (2 ^ (L - l)) hend
  nlinarith

lemma delay_slots_fit {h L H l : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) :
    (L - l + 1) + 1 + scaleExponent h l / 4 ≤ scaleExponent h l := by
  have he := slot_exponent_margin hH hend hl
  omega

lemma slot_period_dvd_half {h L H l : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) :
    2 ^ (L - l + 1) ∣ 2 ^ (scaleExponent h l - 1) := by
  apply pow_dvd_pow
  have he := slot_exponent_margin hH hend hl
  omega

end PacketRouting.CongDil.PRFresh

-- END PRProof/ScaleDepth.lean

-- BEGIN PRProof/PrefixDelay.lean

namespace PacketRouting.CongDil.PRFresh

/-- Prefix count for first-x / last-(W-x) waiting positions. -/
def prefixDelay (x a b : ℕ) : ℕ := min x a + (b - x)

lemma prefixDelay_zero (x : ℕ) : prefixDelay x 0 0 = 0 := by
  simp [prefixDelay]

lemma prefixDelay_full {x W : ℕ} (hx : x ≤ W) : prefixDelay x W W = W := by
  unfold prefixDelay
  omega

lemma prefixDelay_middle {x W : ℕ} (hx : x ≤ W) : prefixDelay x W 0 = x := by
  unfold prefixDelay
  omega

lemma prefixDelay_mono {x a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    prefixDelay x a b ≤ prefixDelay x a' b' := by
  unfold prefixDelay
  omega

lemma prefixDelay_le {x W a b : ℕ} (hx : x ≤ W) (ha : a ≤ W) (hb : b ≤ W) :
    prefixDelay x a b ≤ W := by
  have h := prefixDelay_mono (x := x) ha hb
  rw [prefixDelay_full hx] at h
  exact h

lemma prefixDelay_step {x a b a' b' : ℕ}
    (ha : a ≤ a') (ha' : a' ≤ a + 1)
    (hb : b ≤ b') (hb' : b' ≤ b + 1)
    (hdis : a' = a ∨ b' = b) :
    prefixDelay x a b ≤ prefixDelay x a' b' ∧
      prefixDelay x a' b' ≤ prefixDelay x a b + 1 := by
  unfold prefixDelay
  rcases hdis with h | h <;> omega

lemma prefixDelay_choice_injective {W : ℕ} :
    Function.Injective (fun x : Fin (W + 1) => prefixDelay x.val W 0) := by
  intro x y h
  change prefixDelay x.val W 0 = prefixDelay y.val W 0 at h
  have hx : x.val ≤ W := by omega
  have hy : y.val ≤ W := by omega
  rw [prefixDelay_middle hx, prefixDelay_middle hy] at h
  exact Fin.ext h

end PacketRouting.CongDil.PRFresh

-- END PRProof/PrefixDelay.lean

-- BEGIN PRProof/PositionCounts.lean

namespace PacketRouting.CongDil.PRFresh

/-- Number of selected signed positions up to a crossing position. -/
def positionCount (S : Finset ℤ) (q : ℤ) : ℕ :=
  (S.filter (fun j => j ≤ q)).card

lemma positionCount_le (S : Finset ℤ) (q : ℤ) : positionCount S q ≤ S.card :=
  Finset.card_filter_le _ _

lemma positionCount_mono (S : Finset ℤ) : Monotone (positionCount S) := by
  intro q r h
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, hj.2.trans h⟩

lemma positionCount_before {S : Finset ℤ} {q : ℤ} (h : ∀ j ∈ S, q < j) :
    positionCount S q = 0 := by
  unfold positionCount
  have he : S.filter (fun j => j ≤ q) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    simp only [Finset.mem_filter] at hj
    exact (not_lt_of_ge hj.2) (h j hj.1)
  rw [he]
  rfl

lemma positionCount_after {S : Finset ℤ} {q : ℤ} (h : ∀ j ∈ S, j ≤ q) :
    positionCount S q = S.card := by
  unfold positionCount
  rw [Finset.filter_eq_self.mpr h]

lemma positionCount_step (S : Finset ℤ) (q : ℤ) :
    positionCount S (q + 1) = positionCount S q + if q + 1 ∈ S then 1 else 0 := by
  by_cases h : q + 1 ∈ S
  · have he : S.filter (fun j => j ≤ q + 1) =
        insert (q + 1) (S.filter (fun j => j ≤ q)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · intro hj
        by_cases heq : j = q + 1
        · exact Or.inl heq
        · exact Or.inr ⟨hj.1, by omega⟩
      · rintro (rfl | hj)
        · exact ⟨h, le_rfl⟩
        · exact ⟨hj.1, by omega⟩
    have hn : q + 1 ∉ S.filter (fun j => j ≤ q) := by simp
    simp only [positionCount, he, Finset.card_insert_of_notMem hn, if_pos h]
  · have he : S.filter (fun j => j ≤ q + 1) = S.filter (fun j => j ≤ q) := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · intro hj
        refine ⟨hj.1, ?_⟩
        by_contra hn
        have heq : j = q + 1 := by omega
        subst j
        exact h hj.1
      · intro hj
        exact ⟨hj.1, by omega⟩
    simp only [positionCount, he, if_neg h, Nat.add_zero]

lemma positionCount_step_le (S : Finset ℤ) (q : ℤ) :
    positionCount S (q + 1) ≤ positionCount S q + 1 := by
  rw [positionCount_step]
  split_ifs <;> omega

lemma positionCount_step_eq {S : Finset ℤ} {q : ℤ} (h : q + 1 ∉ S) :
    positionCount S (q + 1) = positionCount S q := by
  simp [positionCount_step, h]

lemma positionCount_disjoint_step {S T : Finset ℤ} (h : Disjoint S T) (q : ℤ) :
    positionCount S (q + 1) = positionCount S q ∨
      positionCount T (q + 1) = positionCount T q := by
  by_cases hs : q + 1 ∈ S
  · right
    exact positionCount_step_eq (fun ht => Finset.disjoint_left.mp h hs ht)
  · exact Or.inl (positionCount_step_eq hs)

end PacketRouting.CongDil.PRFresh

-- END PRProof/PositionCounts.lean

-- BEGIN PRProof/WaitBlock.lean

namespace PacketRouting.CongDil.PRFresh

structure WaitBlock (W : ℕ) where
  first : Finset ℤ
  last : Finset ℤ
  card_first : first.card = W
  card_last : last.card = W
  disjoint : Disjoint first last

namespace WaitBlock

variable {W : ℕ}

def support (B : WaitBlock W) : Finset ℤ := B.first ∪ B.last

def delay (B : WaitBlock W) (x : ℕ) (q : ℤ) : ℕ :=
  prefixDelay x (positionCount B.first q) (positionCount B.last q)

lemma delay_le (B : WaitBlock W) {x : ℕ} (hx : x ≤ W) (q : ℤ) :
    B.delay x q ≤ W := by
  apply prefixDelay_le hx
  · simpa [B.card_first] using positionCount_le B.first q
  · simpa [B.card_last] using positionCount_le B.last q

lemma delay_mono (B : WaitBlock W) (x : ℕ) : Monotone (B.delay x) := by
  intro q r h
  exact prefixDelay_mono (positionCount_mono B.first h) (positionCount_mono B.last h)

lemma delay_step (B : WaitBlock W) (x : ℕ) (q : ℤ) :
    B.delay x q ≤ B.delay x (q + 1) ∧ B.delay x (q + 1) ≤ B.delay x q + 1 := by
  exact prefixDelay_step
    (positionCount_mono B.first (by omega)) (positionCount_step_le B.first q)
    (positionCount_mono B.last (by omega)) (positionCount_step_le B.last q)
    (positionCount_disjoint_step B.disjoint q)

lemma delay_step_eq (B : WaitBlock W) (x : ℕ) (q : ℤ)
    (h : q + 1 ∉ B.support) : B.delay x (q + 1) = B.delay x q := by
  have hf : q + 1 ∉ B.first := fun hf => h (Finset.mem_union_left _ hf)
  have hl : q + 1 ∉ B.last := fun hl => h (Finset.mem_union_right _ hl)
  unfold delay
  rw [positionCount_step_eq hf, positionCount_step_eq hl]

lemma delay_before (B : WaitBlock W) (x : ℕ) (q : ℤ)
    (hf : ∀ j ∈ B.first, q < j) (hl : ∀ j ∈ B.last, q < j) : B.delay x q = 0 := by
  unfold delay
  rw [positionCount_before hf, positionCount_before hl, prefixDelay_zero]

lemma delay_after (B : WaitBlock W) {x : ℕ} (hx : x ≤ W) (q : ℤ)
    (hf : ∀ j ∈ B.first, j ≤ q) (hl : ∀ j ∈ B.last, j ≤ q) : B.delay x q = W := by
  unfold delay
  rw [positionCount_after hf, positionCount_after hl, B.card_first, B.card_last]
  exact prefixDelay_full hx

lemma delay_middle (B : WaitBlock W) {x : ℕ} (hx : x ≤ W) (q : ℤ)
    (hf : ∀ j ∈ B.first, j ≤ q) (hl : ∀ j ∈ B.last, q < j) : B.delay x q = x := by
  unfold delay
  rw [positionCount_after hf, positionCount_before hl, B.card_first]
  exact prefixDelay_middle hx

end WaitBlock
end PacketRouting.CongDil.PRFresh

-- END PRProof/WaitBlock.lean

-- BEGIN PRProof/ArithmeticSlots.lean

namespace PacketRouting.CongDil.PRFresh

def arithmeticSlots (a : ℤ) (s W : ℕ) : Finset ℤ :=
  (Finset.range W).image (fun i : ℕ => a + (s : ℤ) * i)

lemma mem_arithmeticSlots {a z : ℤ} {s W : ℕ} : z ∈ arithmeticSlots a s W ↔
    ∃ i : ℕ, i < W ∧ a + (s : ℤ) * i = z := by
  simp [arithmeticSlots]

lemma arithmeticSlots_card (a : ℤ) {s : ℕ} (hs : 0 < s) (W : ℕ) :
    (arithmeticSlots a s W).card = W := by
  unfold arithmeticSlots
  rw [Finset.card_image_of_injective]
  · exact Finset.card_range W
  · intro i j he
    have hs' : (0 : ℤ) < s := by exact_mod_cast hs
    have hi : (i : ℤ) = j := by nlinarith
    exact_mod_cast hi

lemma arithmeticSlots_bounds {a z : ℤ} {s W : ℕ} (hs : 0 < s)
    (hz : z ∈ arithmeticSlots a s W) : a ≤ z ∧ z < a + (s : ℤ) * W := by
  obtain ⟨i, hi, rfl⟩ := mem_arithmeticSlots.mp hz
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  have hi' : (i : ℤ) < W := by exact_mod_cast hi
  constructor <;> nlinarith

lemma arithmeticSlots_disjoint (a : ℤ) {s W M : ℕ} (hs : 0 < s) (hWM : 2 * W ≤ M) :
    Disjoint (arithmeticSlots a s W)
      (arithmeticSlots (a + (s : ℤ) * (M - W : ℕ)) s W) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have h1 := (arithmeticSlots_bounds hs hz).2
  have h2 := (arithmeticSlots_bounds hs hz').1
  have hMW : W ≤ M - W := by omega
  have hMW' : (W : ℤ) ≤ (M - W : ℕ) := by exact_mod_cast hMW
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  nlinarith

def progressionBlock (a : ℤ) (s W M : ℕ) (hs : 0 < s) (hWM : 2 * W ≤ M) : WaitBlock W where
  first := arithmeticSlots a s W
  last := arithmeticSlots (a + (s : ℤ) * (M - W : ℕ)) s W
  card_first := arithmeticSlots_card a hs W
  card_last := arithmeticSlots_card _ hs W
  disjoint := arithmeticSlots_disjoint a hs hWM

lemma progressionBlock_middle {a q : ℤ} {s W M x : ℕ} (hs : 0 < s)
    (hWM : 2 * W ≤ M) (hx : x ≤ W)
    (hlo : a + (s : ℤ) * W ≤ q)
    (hhi : q < a + (s : ℤ) * (M - W : ℕ)) :
    (progressionBlock a s W M hs hWM).delay x q = x := by
  apply WaitBlock.delay_middle _ hx q
  · intro j hj
    exact (arithmeticSlots_bounds hs hj).2.le.trans hlo
  · intro j hj
    exact hhi.trans_le (arithmeticSlots_bounds (W := W) hs hj).1

end PacketRouting.CongDil.PRFresh

-- END PRProof/ArithmeticSlots.lean

-- BEGIN PRProof/CenteredBlocks.lean

namespace PacketRouting.CongDil.PRFresh

def centeredIndex (m q : ℕ) : ℕ := (q + m / 2) / m

def centeredStart (m b : ℕ) : ℤ := (m : ℤ) * b - (m / 2 : ℕ)

lemma centeredIndex_bounds {m q : ℕ} (hm : 0 < m) :
    centeredStart m (centeredIndex m q) ≤ (q : ℤ) ∧
      (q : ℤ) < centeredStart m (centeredIndex m q) + m := by
  have he := Nat.mod_add_div (q + m / 2) m
  have hr := Nat.mod_lt (q + m / 2) hm
  have he' : ((q + m / 2) % m : ℕ) + (m : ℤ) * ((q + m / 2) / m : ℕ) =
      (q : ℤ) + (m / 2 : ℕ) := by exact_mod_cast he
  have hr' : (((q + m / 2) % m : ℕ) : ℤ) < m := by exact_mod_cast hr
  unfold centeredStart centeredIndex
  constructor <;> omega

lemma centeredIndex_lt {m q D : ℕ} (hm : 0 < m) (hq : q ≤ D) :
    centeredIndex m q < D / m + 2 := by
  have hh := Nat.div_le_self m 2
  have he := Nat.div_le_div_right (c := m) (show q + m / 2 ≤ D + m by omega)
  rw [Nat.add_div_right D hm] at he
  unfold centeredIndex
  omega

lemma centeredBlock_unique {m q b : ℕ} (hm : 0 < m)
    (hl : centeredStart m b ≤ (q : ℤ))
    (hu : (q : ℤ) < centeredStart m b + m) : b = centeredIndex m q := by
  have hb := centeredIndex_bounds (q := q) hm
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  unfold centeredStart at hl hu hb
  have he : (b : ℤ) = centeredIndex m q := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hs : (b : ℤ) + 1 ≤ centeredIndex m q := by omega
      nlinarith
    · have hs : (centeredIndex m q : ℤ) + 1 ≤ b := by omega
      nlinarith
  exact_mod_cast he

lemma centeredBlocks_disjoint {m b c : ℕ} (hm : 0 < m) (hbc : b ≠ c) :
    Disjoint (Set.Ico (centeredStart m b) (centeredStart m b + m))
      (Set.Ico (centeredStart m c) (centeredStart m c + m)) := by
  apply Set.disjoint_left.mpr
  intro q hq hq'
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  unfold centeredStart at hq hq'
  rcases lt_or_gt_of_ne hbc with h | h
  · have hs : (b : ℤ) + 1 ≤ c := by exact_mod_cast h
    nlinarith [hq.1, hq.2, hq'.1, hq'.2]
  · have hs : (c : ℤ) + 1 ≤ b := by exact_mod_cast h
    nlinarith [hq.1, hq.2, hq'.1, hq'.2]

end PacketRouting.CongDil.PRFresh

-- END PRProof/CenteredBlocks.lean

-- BEGIN PRProof/SlotIntervals.lean

namespace PacketRouting.CongDil.PRFresh

lemma arithmeticSlots_prefix_subset (a : ℤ) (s : ℕ) {W M : ℕ} (h : W ≤ M) :
    arithmeticSlots a s W ⊆ arithmeticSlots a s M := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := mem_arithmeticSlots.mp hz
  exact mem_arithmeticSlots.mpr ⟨i, hi.trans_le h, rfl⟩

lemma arithmeticSlots_suffix_subset (a : ℤ) (s : ℕ) {W M : ℕ} (h : W ≤ M) :
    arithmeticSlots (a + (s : ℤ) * (M - W : ℕ)) s W ⊆ arithmeticSlots a s M := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := mem_arithmeticSlots.mp hz
  refine mem_arithmeticSlots.mpr ⟨M - W + i, by omega, ?_⟩
  push_cast
  ring

lemma progressionBlock_support_subset (a : ℤ) {s W M : ℕ} (hs : 0 < s)
    (hWM : 2 * W ≤ M) :
    (progressionBlock a s W M hs hWM).support ⊆ arithmeticSlots a s M := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact arithmeticSlots_prefix_subset a s (by omega) hz
  · exact arithmeticSlots_suffix_subset a s (by omega) hz

lemma centeredSlots_bounds {m r M b : ℕ} (hr : 0 < r) (hm : m = r * M)
    {z : ℤ} (hz : z ∈ arithmeticSlots (centeredStart m b + (r / 2 : ℕ)) r M) :
    centeredStart m b ≤ z ∧ z < centeredStart m b + m := by
  obtain ⟨i, hi, rfl⟩ := mem_arithmeticSlots.mp hz
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  have hi' : (i : ℤ) + 1 ≤ M := by exact_mod_cast hi
  have hh : (r / 2 : ℕ) < r := by omega
  have hh' : ((r / 2 : ℕ) : ℤ) < r := by exact_mod_cast hh
  have hm' : (m : ℤ) = (r : ℤ) * M := by exact_mod_cast hm
  constructor <;> nlinarith

lemma centeredSlots_disjoint {m r M b c : ℕ} (hm : 0 < m) (hr : 0 < r)
    (he : m = r * M) (hbc : b ≠ c) :
    Disjoint (arithmeticSlots (centeredStart m b + (r / 2 : ℕ)) r M)
      (arithmeticSlots (centeredStart m c + (r / 2 : ℕ)) r M) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  exact Set.disjoint_left.mp (centeredBlocks_disjoint hm hbc)
    (centeredSlots_bounds hr he hz) (centeredSlots_bounds hr he hz')

end PacketRouting.CongDil.PRFresh

-- END PRProof/SlotIntervals.lean

-- BEGIN PRProof/DyadicOwnership.lean

namespace PacketRouting.CongDil.PRFresh

def OwnsPosition (q : ℕ) (z : ℤ) : Prop := ∃ k : ℤ, z = (2 : ℤ) ^ q * (2 * k + 1)

lemma ownsPosition_zero (q : ℕ) : ¬ OwnsPosition q 0 := by
  rintro ⟨k, hk⟩
  have hp : (2 : ℤ) ^ q ≠ 0 := by positivity
  have ho : 2 * k + 1 = 0 := (mul_eq_zero.mp hk.symm).resolve_left hp
  omega

lemma ownsPosition_unique {i j : ℕ} {z : ℤ}
    (hi : OwnsPosition i z) (hj : OwnsPosition j z) : i = j := by
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  have hlt : ∀ i j : ℕ, ∀ a b : ℤ, i < j →
      (2 : ℤ) ^ i * (2 * a + 1) ≠ (2 : ℤ) ^ j * (2 * b + 1) := by
    intro i j a b hij he
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ j by omega)
    have hp : (2 : ℤ) ^ i ≠ 0 := by positivity
    have hc : 2 * a + 1 = 2 * ((2 : ℤ) ^ d * (2 * b + 1)) := by
      apply mul_left_cancel₀ hp
      calc
        (2 : ℤ) ^ i * (2 * a + 1) = (2 : ℤ) ^ (i + 1 + d) * (2 * b + 1) := he
        _ = (2 : ℤ) ^ i * (2 * ((2 : ℤ) ^ d * (2 * b + 1))) := by
          rw [pow_add, pow_add]
          ring
    omega
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (hlt i j a b h (ha.symm.trans hb))
  · exact h
  · exact False.elim (hlt j i b a h (hb.symm.trans ha))

lemma ownsPosition_period {q : ℕ} {z : ℤ} (h : OwnsPosition q z) (k : ℤ) :
    OwnsPosition q (z + (2 : ℤ) ^ (q + 1) * k) := by
  obtain ⟨a, rfl⟩ := h
  refine ⟨a + k, ?_⟩
  rw [pow_succ]
  ring

end PacketRouting.CongDil.PRFresh

-- END PRProof/DyadicOwnership.lean

-- BEGIN PRProof/HierarchyBlocks.lean

namespace PacketRouting.CongDil.PRFresh

def slotPeriod (L l : ℕ) : ℕ := 2 ^ (L - l + 1)
def slotsPerBlock (h L l : ℕ) : ℕ := 2 ^ (scaleExponent h l - (L - l + 1))

lemma scale_eq_period_mul {h L H l : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) :
    blockScale h l = slotPeriod L l * slotsPerBlock h L l := by
  have he := slot_exponent_margin hH hend hl
  unfold blockScale slotPeriod slotsPerBlock
  rw [← pow_add]
  congr 1
  omega

lemma two_delays_le_slots {h L H l : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) :
    2 * delayScale h l ≤ slotsPerBlock h L l := by
  have he := delay_slots_fit hH hend hl
  unfold delayScale slotsPerBlock
  calc
    2 * 2 ^ (scaleExponent h l / 4) = 2 ^ (scaleExponent h l / 4 + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (scaleExponent h l - (L - l + 1)) := Nat.pow_le_pow_right (by omega) (by omega)

lemma slot_period_dvd_block_half {h L H l : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) :
    slotPeriod L l ∣ blockScale h l / 2 := by
  have he := slot_exponent_margin hH hend hl
  have hp : 1 ≤ scaleExponent h l := by omega
  have hdiv : blockScale h l / 2 = 2 ^ (scaleExponent h l - 1) := by
    simpa [blockScale] using (Nat.pow_div (x := 2) hp (by omega))
  rw [hdiv]
  exact slot_period_dvd_half hH hend hl

noncomputable def hierarchyBlock (h L H l b : ℕ) (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) : WaitBlock (delayScale h l) :=
  progressionBlock
    (centeredStart (blockScale h l) b + (slotPeriod L l / 2 : ℕ))
    (slotPeriod L l) (delayScale h l) (slotsPerBlock h L l)
    (by unfold slotPeriod; positivity) (two_delays_le_slots hH hend hl)

lemma hierarchyBlock_inside {h L H l b : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) {z : ℤ}
    (hz : z ∈ (hierarchyBlock h L H l b hH hend hl).support) :
    centeredStart (blockScale h l) b ≤ z ∧
      z < centeredStart (blockScale h l) b + blockScale h l := by
  have hs := progressionBlock_support_subset
    (centeredStart (blockScale h l) b + (slotPeriod L l / 2 : ℕ))
    (show 0 < slotPeriod L l by unfold slotPeriod; positivity)
    (two_delays_le_slots hH hend hl) hz
  exact centeredSlots_bounds (by unfold slotPeriod; positivity)
    (scale_eq_period_mul hH hend hl) hs

lemma hierarchyBlock_same_level_disjoint {h L H l b c : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) (hbc : b ≠ c) :
    Disjoint (hierarchyBlock h L H l b hH hend hl).support
      (hierarchyBlock h L H l c hH hend hl).support := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  exact Set.disjoint_left.mp (centeredBlocks_disjoint (blockScale_pos h l) hbc)
    (hierarchyBlock_inside hH hend hl hz) (hierarchyBlock_inside hH hend hl hz')

end PacketRouting.CongDil.PRFresh

-- END PRProof/HierarchyBlocks.lean

-- BEGIN PRProof/HierarchyOwnership.lean

namespace PacketRouting.CongDil.PRFresh

lemma centeredSlots_owned {m M b q : ℕ}
    (hm : m = 2 ^ (q + 1) * M) (hd : 2 ^ (q + 1) ∣ m / 2)
    {z : ℤ} (hz : z ∈ arithmeticSlots
      (centeredStart m b + (2 ^ (q + 1) / 2 : ℕ)) (2 ^ (q + 1)) M) :
    OwnsPosition q z := by
  obtain ⟨i, _, rfl⟩ := mem_arithmeticSlots.mp hz
  obtain ⟨a, ha⟩ := hd
  have hh : 2 ^ (q + 1) / 2 = 2 ^ q := by
    simpa using (Nat.pow_div (x := 2) (m := q + 1) (n := 1) (by omega) (by omega))
  refine ⟨(M : ℤ) * b - a + i, ?_⟩
  unfold centeredStart
  rw [hh, ha, hm]
  push_cast
  rw [pow_succ]
  ring

lemma hierarchyBlock_owned {h L H l b : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) {z : ℤ}
    (hz : z ∈ (hierarchyBlock h L H l b hH hend hl).support) :
    OwnsPosition (L - l) z := by
  have hs := progressionBlock_support_subset
    (centeredStart (blockScale h l) b + (slotPeriod L l / 2 : ℕ))
    (show 0 < slotPeriod L l by unfold slotPeriod; positivity)
    (two_delays_le_slots hH hend hl) hz
  exact centeredSlots_owned (scale_eq_period_mul hH hend hl)
    (slot_period_dvd_block_half hH hend hl) hs

lemma hierarchyBlock_other_level_disjoint {h L H l j b c : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) (hj : j ≤ L) (hne : l ≠ j) :
    Disjoint (hierarchyBlock h L H l b hH hend hl).support
      (hierarchyBlock h L H j c hH hend hj).support := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have he := ownsPosition_unique (hierarchyBlock_owned hH hend hl hz)
    (hierarchyBlock_owned hH hend hj hz')
  omega

end PacketRouting.CongDil.PRFresh

-- END PRProof/HierarchyOwnership.lean

-- BEGIN PRProof/HierarchyDelay.lean

namespace PacketRouting.CongDil.PRFresh

lemma hierarchyBlock_before {h L H l b : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) (x : ℕ) {q : ℤ}
    (hq : q < centeredStart (blockScale h l) b) :
    (hierarchyBlock h L H l b hH hend hl).delay x q = 0 := by
  apply WaitBlock.delay_before
  · intro z hz
    exact hq.trans_le (hierarchyBlock_inside hH hend hl (Finset.mem_union_left _ hz)).1
  · intro z hz
    exact hq.trans_le (hierarchyBlock_inside hH hend hl (Finset.mem_union_right _ hz)).1

lemma hierarchyBlock_after {h L H l b : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) {x : ℕ} (hx : x ≤ delayScale h l)
    {q : ℤ} (hq : centeredStart (blockScale h l) b + blockScale h l ≤ q) :
    (hierarchyBlock h L H l b hH hend hl).delay x q = delayScale h l := by
  apply WaitBlock.delay_after _ hx
  · intro z hz
    exact (hierarchyBlock_inside hH hend hl (Finset.mem_union_left _ hz)).2.le.trans hq
  · intro z hz
    exact (hierarchyBlock_inside hH hend hl (Finset.mem_union_right _ hz)).2.le.trans hq

lemma hierarchyBlock_earlier {h L H l b q : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) {x : ℕ} (hx : x ≤ delayScale h l)
    (hb : b < centeredIndex (blockScale h l) q) :
    (hierarchyBlock h L H l b hH hend hl).delay x q = delayScale h l := by
  apply hierarchyBlock_after hH hend hl hx
  have hi := (centeredIndex_bounds (q := q) (blockScale_pos h l)).1
  have hb' : (b : ℤ) + 1 ≤ centeredIndex (blockScale h l) q := by exact_mod_cast hb
  have hp : (0 : ℤ) < blockScale h l := by exact_mod_cast blockScale_pos h l
  unfold centeredStart at hi ⊢
  nlinarith

lemma hierarchyBlock_later {h L H l b q : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) (x : ℕ)
    (hb : centeredIndex (blockScale h l) q < b) :
    (hierarchyBlock h L H l b hH hend hl).delay x q = 0 := by
  apply hierarchyBlock_before hH hend hl x
  have hi := (centeredIndex_bounds (q := q) (blockScale_pos h l)).2
  have hb' : (centeredIndex (blockScale h l) q : ℤ) + 1 ≤ b := by exact_mod_cast hb
  have hp : (0 : ℤ) < blockScale h l := by exact_mod_cast blockScale_pos h l
  unfold centeredStart at hi ⊢
  nlinarith

def hierarchyMargin (h L l : ℕ) : ℕ := slotPeriod L l * (delayScale h l + 1)

lemma hierarchyBlock_middle {h L H l b : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) {x : ℕ} (hx : x ≤ delayScale h l)
    {q : ℤ}
    (hlo : centeredStart (blockScale h l) b + hierarchyMargin h L l ≤ q)
    (hhi : q ≤ centeredStart (blockScale h l) b + blockScale h l - hierarchyMargin h L l) :
    (hierarchyBlock h L H l b hH hend hl).delay x q = x := by
  apply progressionBlock_middle _ _ hx
  · have hs := Nat.div_le_self (slotPeriod L l) 2
    have hs' : ((slotPeriod L l / 2 : ℕ) : ℤ) ≤ slotPeriod L l := by exact_mod_cast hs
    unfold hierarchyMargin at hlo
    push_cast at hlo
    nlinarith
  · have he := scale_eq_period_mul hH hend hl
    have he' : (blockScale h l : ℤ) = (slotPeriod L l : ℤ) * slotsPerBlock h L l := by exact_mod_cast he
    have hW := two_delays_le_slots hH hend hl
    have hsub : ((slotsPerBlock h L l - delayScale h l : ℕ) : ℤ) =
        (slotsPerBlock h L l : ℤ) - delayScale h l := by omega
    have hs : (0 : ℤ) < slotPeriod L l := by unfold slotPeriod; positivity
    unfold hierarchyMargin at hhi
    push_cast at hhi
    rw [hsub]
    nlinarith

end PacketRouting.CongDil.PRFresh

-- END PRProof/HierarchyDelay.lean

-- BEGIN PRProof/WaitFamily.lean

namespace PacketRouting.CongDil.PRFresh

lemma sum_delay_step {J : Type*} [Fintype J] {W : J → ℕ}
    (B : (j : J) → WaitBlock (W j)) (x : J → ℕ)
    (hd : Pairwise (fun i j => Disjoint (B i).support (B j).support)) (q : ℤ) :
    (∑ j, (B j).delay (x j) q) ≤ ∑ j, (B j).delay (x j) (q + 1) ∧
    (∑ j, (B j).delay (x j) (q + 1)) ≤ (∑ j, (B j).delay (x j) q) + 1 := by
  classical
  constructor
  · exact Finset.sum_le_sum (fun j _ => ((B j).delay_step (x j) q).1)
  · by_cases he : ∃ i, q + 1 ∈ (B i).support
    · obtain ⟨i, hi⟩ := he
      let delta := (B i).delay (x i) (q + 1) - (B i).delay (x i) q
      have hdi : delta ≤ 1 := by
        have h := (B i).delay_step (x i) q
        omega
      have hformula (j : J) : (B j).delay (x j) (q + 1) =
          (B j).delay (x j) q + if j = i then delta else 0 := by
        by_cases hj : j = i
        · subst j
          have h := ((B i).delay_step (x i) q).1
          simp only [ite_true]
          dsimp only [delta]
          omega
        · have hnot : q + 1 ∉ (B j).support := by
            intro hjmem
            exact Finset.disjoint_left.mp (hd hj) hjmem hi
          rw [(B j).delay_step_eq (x j) q hnot, if_neg hj, Nat.add_zero]
      simp_rw [hformula]
      rw [Finset.sum_add_distrib]
      simpa using Nat.add_le_add_left hdi (∑ j, (B j).delay (x j) q)
    · have hformula (j : J) : (B j).delay (x j) (q + 1) = (B j).delay (x j) q :=
        (B j).delay_step_eq (x j) q (fun h => he ⟨j, h⟩)
      simp_rw [hformula]
      omega

end PacketRouting.CongDil.PRFresh

-- END PRProof/WaitFamily.lean

-- BEGIN PRProof/FamilyClock.lean

namespace PacketRouting.CongDil.PRFresh

noncomputable def familyTimetable {P E J : Type*} [Fintype J]
    (path : P → List E) {W : J → ℕ} (B : (j : J) → WaitBlock (W j))
    (root : P → ℕ) (x : P → J → ℕ) : Timetable path where
  time := fun p k => k.val + 1 + root p + ∑ j, (B j).delay (x p j) (k.val + 1 : ℕ)
  one_le_time := by intros; omega
  strictMono_time := by
    intro p k l hkl
    have hs : (∑ j, (B j).delay (x p j) (k.val + 1 : ℕ)) ≤
        ∑ j, (B j).delay (x p j) (l.val + 1 : ℕ) := by
      apply Finset.sum_le_sum
      intro j _
      exact (B j).delay_mono (x p j) (by exact_mod_cast Nat.add_le_add_right hkl.le 1)
    dsimp only
    omega

lemma familyTimetable_gap {P E J : Type*} [Fintype J]
    {path : P → List E} {W : J → ℕ} (B : (j : J) → WaitBlock (W j))
    (hd : Pairwise (fun i j => Disjoint (B i).support (B j).support))
    (root : P → ℕ) (x : P → J → ℕ) (p : P) (k : ℕ)
    (hk : k + 1 < (path p).length) :
    (familyTimetable path B root x).time p ⟨k + 1, hk⟩ ≤
      (familyTimetable path B root x).time p ⟨k, Nat.lt_of_succ_lt hk⟩ + 2 := by
  have hs := (sum_delay_step B (x p) hd (k + 1 : ℕ)).2
  simp only [Nat.cast_add, Nat.cast_one] at hs
  change k + 1 + 1 + root p + (∑ j, (B j).delay (x p j) ((k + 1 + 1 : ℕ) : ℤ)) ≤ _
  simp only [familyTimetable, Nat.cast_add, Nat.cast_one]
  omega

lemma familyTimetable_length {P E J : Type*} [Fintype J]
    {path : P → List E} {W : J → ℕ} (B : (j : J) → WaitBlock (W j))
    (root : P → ℕ) (x : P → J → ℕ) {d R : ℕ} (hd : DilationLE path d)
    (hr : ∀ p, root p ≤ R) (hx : ∀ p j, x p j ≤ W j) :
    (familyTimetable path B root x).LengthLE (d + R + ∑ j, W j) := by
  intro p k
  have hs : (∑ j, (B j).delay (x p j) (k.val + 1 : ℕ)) ≤ ∑ j, W j :=
    Finset.sum_le_sum (fun j _ => (B j).delay_le (hx p j) _)
  have hp := hd p
  have hroot := hr p
  change k.val + 1 + root p + (∑ j, (B j).delay (x p j) (k.val + 1 : ℕ)) ≤ _
  omega

end PacketRouting.CongDil.PRFresh

-- END PRProof/FamilyClock.lean

-- BEGIN PRProof/HierarchyFamily.lean

namespace PacketRouting.CongDil.PRFresh

abbrev HierarchyIndex (h L : ℕ) :=
  Σ l : Fin L, Fin (2 ^ h / blockScale h (l.val + 1) + 2)

def hierarchyWidth (h L : ℕ) (j : HierarchyIndex h L) : ℕ := delayScale h (j.1.val + 1)

noncomputable def hierarchyWait (h L H : ℕ) (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (j : HierarchyIndex h L) : WaitBlock (hierarchyWidth h L j) :=
  hierarchyBlock h L H (j.1.val + 1) j.2.val hH hend (by have := j.1.isLt; omega)

lemma hierarchyWait_pairwise {h L H : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) :
    Pairwise (fun i j : HierarchyIndex h L =>
      Disjoint (hierarchyWait h L H hH hend i).support (hierarchyWait h L H hH hend j).support) := by
  intro i j hij
  by_cases he : i.1 = j.1
  · rcases i with ⟨l, b⟩
    rcases j with ⟨l', c⟩
    dsimp only at he
    subst l'
    have hbc : b.val ≠ c.val := by
      intro hbc
      have : b = c := Fin.ext hbc
      subst c
      exact hij rfl
    exact hierarchyBlock_same_level_disjoint hH hend (by have := l.isLt; omega) hbc
  · exact hierarchyBlock_other_level_disjoint hH hend
      (by have := i.1.isLt; omega) (by have := j.1.isLt; omega)
      (by intro hv; apply he; apply Fin.ext; omega)

noncomputable def selectedHierarchyIndex (h L q : ℕ) (hq : q ≤ 2 ^ h) (l : Fin L) :
    HierarchyIndex h L :=
  ⟨l, ⟨centeredIndex (blockScale h (l.val + 1)) q,
    centeredIndex_lt (blockScale_pos h (l.val + 1)) hq⟩⟩

lemma hierarchy_delay_sum_depends {h L H q : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hq : q ≤ 2 ^ h)
    (x y : HierarchyIndex h L → ℕ)
    (hx : ∀ j, x j ≤ hierarchyWidth h L j) (hy : ∀ j, y j ≤ hierarchyWidth h L j)
    (he : ∀ l, x (selectedHierarchyIndex h L q hq l) = y (selectedHierarchyIndex h L q hq l)) :
    (∑ j, (hierarchyWait h L H hH hend j).delay (x j) q) =
      ∑ j, (hierarchyWait h L H hH hend j).delay (y j) q := by
  apply Finset.sum_congr rfl
  intro j _
  rcases j with ⟨l, b⟩
  have hl : l.val + 1 ≤ L := by have := l.isLt; omega
  rcases lt_trichotomy b.val (centeredIndex (blockScale h (l.val + 1)) q) with hb | hb | hb
  · change (hierarchyBlock h L H (l.val + 1) b.val hH hend hl).delay (x ⟨l, b⟩) (q : ℤ) =
        (hierarchyBlock h L H (l.val + 1) b.val hH hend hl).delay (y ⟨l, b⟩) (q : ℤ)
    rw [hierarchyBlock_earlier hH hend hl (hx ⟨l, b⟩) hb,
      hierarchyBlock_earlier hH hend hl (hy ⟨l, b⟩) hb]
  · have hj : (⟨l, b⟩ : HierarchyIndex h L) = selectedHierarchyIndex h L q hq l := by
      congr 1
      exact Fin.ext hb
    rw [hj, he l]
  · change (hierarchyBlock h L H (l.val + 1) b.val hH hend hl).delay (x ⟨l, b⟩) (q : ℤ) =
        (hierarchyBlock h L H (l.val + 1) b.val hH hend hl).delay (y ⟨l, b⟩) (q : ℤ)
    rw [hierarchyBlock_later hH hend hl (x ⟨l, b⟩) hb,
      hierarchyBlock_later hH hend hl (y ⟨l, b⟩) hb]

end PacketRouting.CongDil.PRFresh

-- END PRProof/HierarchyFamily.lean

-- BEGIN PRProof/GeometricBudgets.lean

namespace PacketRouting.CongDil.PRFresh

lemma sum_descending_nat (f : ℕ → ℕ) (N : ℕ)
    (h : ∀ i < N, 2 * f (i + 1) ≤ f i) :
    (∑ i ∈ Finset.range N, f (i + 1)) + f N ≤ f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hp := ih (fun i hi => h i (by omega))
    have hn := h N (by omega)
    rw [Finset.sum_range_succ]
    omega

lemma sum_ascending_nat (f : ℕ → ℕ) (N : ℕ)
    (h : ∀ i < N, 2 * f i ≤ f (i + 1)) :
    (∑ i ∈ Finset.range N, f i) + f 0 ≤ f N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hp := ih (fun i hi => h i (by omega))
    have hn := h N (by omega)
    rw [Finset.sum_range_succ]
    omega

lemma sum_ascending_real (f : ℕ → ℝ) (N : ℕ)
    (h : ∀ i < N, 2 * f i ≤ f (i + 1)) :
    (∑ i ∈ Finset.range N, f i) + f 0 ≤ f N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hp := ih (fun i hi => h i (by omega))
    have hn := h N (by omega)
    rw [Finset.sum_range_succ]
    linarith

lemma sum_descending_real (f : ℕ → ℝ) (N : ℕ)
    (h : ∀ i < N, 2 * f (i + 1) ≤ f i) :
    (∑ i ∈ Finset.range N, f (i + 1)) + f N ≤ f 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hp := ih (fun i hi => h i (by omega))
    have hn := h N (by omega)
    rw [Finset.sum_range_succ]
    linarith

end PacketRouting.CongDil.PRFresh

-- END PRProof/GeometricBudgets.lean

-- BEGIN PRProof/ScaleBudgets.lean

namespace PacketRouting.CongDil.PRFresh

def waitMass (h l : ℕ) : ℕ := (2 ^ h / blockScale h l) * delayScale h l

lemma waitMass_eq (h l : ℕ) :
    waitMass h l = 2 ^ (h - scaleExponent h l + scaleExponent h l / 4) := by
  have he : scaleExponent h l ≤ h := Nat.div_le_self _ _
  unfold waitMass blockScale delayScale
  rw [Nat.pow_div he (by omega), ← pow_add]

lemma delayScale_half {h l : ℕ} (hh : 8 ≤ scaleExponent h l) :
    2 * delayScale h (l + 1) ≤ delayScale h l := by
  unfold delayScale
  rw [scaleExponent_succ]
  calc
    2 * 2 ^ (scaleExponent h l / 2 / 4) = 2 ^ (scaleExponent h l / 2 / 4 + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (scaleExponent h l / 4) := Nat.pow_le_pow_right (by omega) (by omega)

lemma waitMass_double {h l : ℕ} (hh : 8 ≤ scaleExponent h l) :
    2 * waitMass h l ≤ waitMass h (l + 1) := by
  rw [waitMass_eq, waitMass_eq, scaleExponent_succ]
  have he : scaleExponent h l ≤ h := Nat.div_le_self _ _
  calc
    2 * 2 ^ (h - scaleExponent h l + scaleExponent h l / 4) =
        2 ^ (h - scaleExponent h l + scaleExponent h l / 4 + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (h - scaleExponent h l / 2 + scaleExponent h l / 2 / 4) := Nat.pow_le_pow_right (by omega) (by omega)

lemma waitMass_le_half {h l : ℕ} (hh : 2 ≤ scaleExponent h l) :
    2 * waitMass h l ≤ 2 ^ h := by
  rw [waitMass_eq]
  have he : scaleExponent h l ≤ h := Nat.div_le_self _ _
  calc
    2 * 2 ^ (h - scaleExponent h l + scaleExponent h l / 4) =
        2 ^ (h - scaleExponent h l + scaleExponent h l / 4 + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ h := Nat.pow_le_pow_right (by omega) (by omega)

lemma sum_shift_nat (f : ℕ → ℕ) (N : ℕ) :
    (∑ i ∈ Finset.range N, f (i + 1)) + f 0 = (∑ i ∈ Finset.range N, f i) + f N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, Finset.sum_range_succ]; omega

lemma hierarchy_wait_budget {h L H : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) :
    (∑ l ∈ Finset.range L, (2 ^ h / blockScale h (l + 1) + 2) * delayScale h (l + 1)) ≤ 3 * 2 ^ h := by
  have hex (l : ℕ) (hl : l ≤ L) : 8 ≤ scaleExponent h l :=
    hH.trans (hend.trans (scaleExponent_antitone h hl))
  have ha := sum_ascending_nat (waitMass h) L (fun i hi => waitMass_double (hex i hi.le))
  have hs := sum_shift_nat (waitMass h) L
  have hb := waitMass_le_half (show 2 ≤ scaleExponent h L by have := hex L le_rfl; omega)
  have hmass : (∑ i ∈ Finset.range L, waitMass h (i + 1)) ≤ 2 ^ h := by omega
  have hw := sum_descending_nat (delayScale h) L (fun i hi => delayScale_half (hex i hi.le))
  have hw0 : delayScale h 0 ≤ 2 ^ h := by
    unfold delayScale
    rw [scaleExponent_zero]
    exact Nat.pow_le_pow_right (by omega) (Nat.div_le_self h 4)
  have hwait : (∑ i ∈ Finset.range L, delayScale h (i + 1)) ≤ 2 ^ h := by omega
  have he : (∑ l ∈ Finset.range L, (2 ^ h / blockScale h (l + 1) + 2) * delayScale h (l + 1)) =
      (∑ l ∈ Finset.range L, waitMass h (l + 1)) +
        2 * (∑ l ∈ Finset.range L, delayScale h (l + 1)) := by
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, waitMass]
  rw [he]
  omega

end PacketRouting.CongDil.PRFresh

-- END PRProof/ScaleBudgets.lean

-- BEGIN PRProof/RoutingClock.lean

namespace PacketRouting.CongDil.PRFresh

abbrev RoutingCoordinate (h L : ℕ) := Option (HierarchyIndex h L)

def routingWidth (h L : ℕ) : RoutingCoordinate h L → ℕ
  | none => 2 ^ h
  | some j => hierarchyWidth h L j

abbrev RoutingAssignment (h L : ℕ) := (j : RoutingCoordinate h L) → Fin (routingWidth h L j)

noncomputable def routingTimetable {P E : Type*} (path : P → List E)
    (h L H : ℕ) (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (ω : P → RoutingAssignment h L) : Timetable path :=
  familyTimetable path (hierarchyWait h L H hH hend)
    (fun p => (ω p none).val + 1) (fun p j => (ω p (some j)).val + 1)

lemma hierarchyWidth_sum {h L H : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) :
    (∑ j : HierarchyIndex h L, hierarchyWidth h L j) ≤ 3 * 2 ^ h := by
  change (∑ j : Σ l : Fin L, Fin (2 ^ h / blockScale h (l.val + 1) + 2),
    delayScale h (j.1.val + 1)) ≤ _
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (∑ l : Fin L, (2 ^ h / blockScale h (l.val + 1) + 2) * delayScale h (l.val + 1)) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun l => (2 ^ h / blockScale h (l + 1) + 2) * delayScale h (l + 1))]
  exact hierarchy_wait_budget hH hend

lemma routingTimetable_length {P E : Type*} {path : P → List E}
    {h L H : ℕ} (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (hd : DilationLE path (2 ^ h)) (ω : P → RoutingAssignment h L) :
    (routingTimetable path h L H hH hend ω).LengthLE (5 * 2 ^ h) := by
  have hr (p : P) : (ω p none).val + 1 ≤ 2 ^ h := by
    have hp := (ω p none).isLt
    change (ω p none).val < 2 ^ h at hp
    omega
  have hx (p : P) (j : HierarchyIndex h L) : (ω p (some j)).val + 1 ≤ hierarchyWidth h L j := by
    have := (ω p (some j)).isLt
    exact Nat.succ_le_of_lt this
  have hb := familyTimetable_length (hierarchyWait h L H hH hend)
    (fun p => (ω p none).val + 1) (fun p j => (ω p (some j)).val + 1) hd hr hx
  have hs := hierarchyWidth_sum hH hend
  intro p k
  have he := hb p k
  change (familyTimetable path (hierarchyWait h L H hH hend)
    (fun p => (ω p none).val + 1) (fun p j => (ω p (some j)).val + 1)).time p k ≤ _
  omega

lemma routingTimetable_gap {P E : Type*} {path : P → List E}
    {h L H : ℕ} (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (ω : P → RoutingAssignment h L) (p : P) (k : ℕ) (hk : k + 1 < (path p).length) :
    (routingTimetable path h L H hH hend ω).time p ⟨k + 1, hk⟩ ≤
      (routingTimetable path h L H hH hend ω).time p ⟨k, Nat.lt_of_succ_lt hk⟩ + 2 :=
  familyTimetable_gap (hierarchyWait h L H hH hend) (hierarchyWait_pairwise hH hend)
    (fun p => (ω p none).val + 1) (fun p j => (ω p (some j)).val + 1) p k hk

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingClock.lean

-- BEGIN PRProof/FiniteLaw.lean

noncomputable section
open scoped BigOperators
namespace PacketRouting.CongDil.PRFresh

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

structure FiniteLaw (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1

namespace FiniteLaw

def mean (P : FiniteLaw ι) (f : ι → ℝ) : ℝ := ∑ i, P.weight i * f i

theorem mean_const (P : FiniteLaw ι) (c : ℝ) : P.mean (fun _ => c) = c := by
  rw [mean, ← Finset.sum_mul, P.total, one_mul]

theorem mean_add (P : FiniteLaw ι) (f g : ι → ℝ) :
    P.mean (fun i => f i + g i) = P.mean f + P.mean g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]

theorem mean_sub (P : FiniteLaw ι) (f g : ι → ℝ) :
    P.mean (fun i => f i - g i) = P.mean f - P.mean g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mul (P : FiniteLaw ι) (c : ℝ) (f : ι → ℝ) :
    P.mean (fun i => c * f i) = c * P.mean f := by
  simp only [mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mean_mono (P : FiniteLaw ι) {f g : ι → ℝ} (h : ∀ i, f i ≤ g i) :
    P.mean f ≤ P.mean g :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (P.nonneg i)

theorem mean_nonneg (P : FiniteLaw ι) {f : ι → ℝ} (h : ∀ i, 0 ≤ f i) :
    0 ≤ P.mean f := by
  simpa only [P.mean_const] using P.mean_mono h

def prod (P : FiniteLaw ι) (Q : FiniteLaw κ) : FiniteLaw (ι × κ) where
  weight z := P.weight z.1 * Q.weight z.2
  nonneg z := mul_nonneg (P.nonneg z.1) (Q.nonneg z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, Q.total, mul_one, P.total]

theorem mean_prod (P : FiniteLaw ι) (Q : FiniteLaw κ) (f : ι × κ → ℝ) :
    (P.prod Q).mean f = P.mean (fun i => Q.mean (fun j => f (i,j))) := by
  simp only [mean, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/FiniteLaw.lean

-- BEGIN PRProof/FiniteProbability.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

def prob (P : FiniteLaw Ω) (A : Ω → Prop) : ℝ := by
  classical
  exact P.mean (fun x => if A x then 1 else 0)

theorem prob_nonneg (P : FiniteLaw Ω) (A : Ω → Prop) : 0 ≤ P.prob A := by
  classical
  apply P.mean_nonneg
  intro x
  split_ifs <;> norm_num

theorem prob_mono (P : FiniteLaw Ω) {A B : Ω → Prop} (h : ∀x, A x → B x) :
    P.prob A ≤ P.prob B := by
  classical
  apply P.mean_mono
  intro x
  by_cases ha : A x
  · simp [ha,h x ha]
  · simp [ha]
    split_ifs <;> norm_num

theorem prob_true (P : FiniteLaw Ω) : P.prob (fun _ => True) = 1 := by
  classical
  simp [prob,P.mean_const]

theorem prob_false (P : FiniteLaw Ω) : P.prob (fun _ => False) = 0 := by
  classical
  simp [prob,P.mean_const]

theorem prob_le_one (P : FiniteLaw Ω) (A : Ω → Prop) : P.prob A ≤ 1 := by
  simpa only [P.prob_true] using P.prob_mono (A := A) (B := fun _ => True) (by simp)

theorem prob_split (P : FiniteLaw Ω) (A B : Ω → Prop) :
    P.prob A = P.prob (fun x => A x ∧ B x) + P.prob (fun x => A x ∧ ¬B x) := by
  classical
  rw [prob,prob,prob,←P.mean_add]
  congr 1
  funext x
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha,hb]

theorem exists_of_prob_pos (P : FiniteLaw Ω) {A : Ω → Prop} (h : 0 < P.prob A) : ∃x,A x := by
  classical
  by_contra hn
  have he : A = fun _ => False := by
    funext x
    exact propext ⟨fun hx => hn ⟨x,hx⟩,False.elim⟩
  rw [he,P.prob_false] at h
  exact lt_irrefl 0 h

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/FiniteProbability.lean

-- BEGIN PRProof/ProductLaw.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have h : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
    simp [h]

def pi {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*} [∀j,Fintype (α j)]
    (P : ∀j,FiniteLaw (α j)) : FiniteLaw (∀j,α j) where
  weight s := ∏j,(P j).weight (s j)
  nonneg s := Finset.prod_nonneg fun j _ => (P j).nonneg (s j)
  total := by
    classical
    rw [←Fintype.prod_sum]
    simp only [FiniteLaw.total,Finset.prod_const_one]

theorem mean_pi_prod {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*} [∀j,Fintype (α j)]
    (P : ∀j,FiniteLaw (α j)) (f : ∀j,α j → ℝ) :
    (pi P).mean (fun s => ∏j,f j (s j)) = ∏j,(P j).mean (f j) := by
  classical
  simp only [mean,pi,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j a => (P j).weight a*f j a)).symm

theorem mean_pi_eval {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*} [∀j,Fintype (α j)]
    (P : ∀j,FiniteLaw (α j)) (i : J) (f : α i → ℝ) :
    (pi P).mean (fun s => f (s i)) = (P i).mean f := by
  classical
  let g : ∀j,α j → ℝ := fun j a => if h : j=i then f (h ▸ a) else 1
  have h := mean_pi_prod P g
  have he (s : ∀j,α j) : (∏j,g j (s j)) = f (s i) := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro b _ hbi
      simp [g,hbi]
    · simp
  have hf : (∏j,(P j).mean (g j)) = (P i).mean f := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro b _ hbi
      simp [g,hbi,mean_const]
    · simp
  simpa only [he,hf] using h

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/ProductLaw.lean

-- BEGIN PRProof/ProductSplit.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*} [∀j,Fintype (α j)]

def joinAssignment (S : Finset J) (u : ∀j : {j // j∈S},α j)
    (v : ∀j : {j // j∉S},α j) (j : J) : α j :=
  if h : j∈S then u ⟨j,h⟩ else v ⟨j,h⟩

theorem mean_pi_split (P : ∀j,FiniteLaw (α j)) (S : Finset J) (f : (∀j,α j) → ℝ) :
    (pi P).mean f = (pi (fun j : {j // j∈S} => P j)).mean (fun u =>
      (pi (fun j : {j // j∉S} => P j)).mean (fun v => f (joinAssignment S u v))) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun j => j∈S) α
  unfold mean pi
  have he := e.symm.sum_comp (fun s : ∀j,α j => (∏j,(P j).weight (s j))*f s)
  rw [←he,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hp := Fintype.prod_subtype_mul_prod_subtype (fun j => j∈S)
    (fun j => (P j).weight (e.symm (u,v) j))
  have ha (j : {j // j∈S}) : e.symm (u,v) j = u j := by simp [e]
  have hb (j : {j // j∉S}) : e.symm (u,v) j = v j := by simp [e,j.property]
  simp_rw [ha,hb] at hp
  change (∏j,(P j).weight (e.symm (u,v) j))*f (e.symm (u,v)) =
    (∏j : {j // j∈S},(P j).weight (u j))*
      ((∏j : {j // j∉S},(P j).weight (v j))*f (joinAssignment S u v))
  rw [←hp,mul_assoc]
  have hi := congrArg (fun h : Fintype {j // j∈S} => @Finset.univ {j // j∈S} h)
    (Subsingleton.elim (Subtype.fintype (fun j => j∈S)) (Finset.Subtype.fintype S))
  rw [hi]
  rfl

def CoordinateDepends (f : (∀j,α j) → ℝ) (S : Finset J) : Prop :=
  ∀u v, (∀j∈S,u j=v j) → f u=f v

theorem mean_pi_independent (P : ∀j,FiniteLaw (α j)) (S T : Finset J)
    (hST : Disjoint S T) (f g : (∀j,α j) → ℝ)
    (hf : CoordinateDepends f S) (hg : CoordinateDepends g T)
    [∀j,Nonempty (α j)] :
    (pi P).mean (fun s => f s*g s) = (pi P).mean f*(pi P).mean g := by
  classical
  let base : ∀j,α j := fun _ => Classical.choice inferInstance
  let f' := fun u => f (joinAssignment S u (fun j => base j))
  let g' := fun v => g (joinAssignment S (fun j => base j) v)
  have hF u v : f (joinAssignment S u v)=f' u := by
    apply hf
    intro j hj
    simp [joinAssignment,hj]
  have hG u v : g (joinAssignment S u v)=g' v := by
    apply hg
    intro j hj
    have hjs : j∉S := fun h => Finset.disjoint_left.mp hST h hj
    simp [joinAssignment,hjs]
  rw [mean_pi_split P S,mean_pi_split P S f,mean_pi_split P S g]
  simp_rw [hF,hG,mean_mul,mean_const]
  rw [show (fun u => f' u * (pi (fun j : {j // j∉S} => P j)).mean g') =
      (fun u => (pi (fun j : {j // j∉S} => P j)).mean g' * f' u) by funext u; ring,
    mean_mul]
  ring

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/ProductSplit.lean

-- BEGIN PRProof/Resampling.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*} [∀j,Fintype (α j)]

def replaceCoordinates (S : Finset J) (u v : ∀j,α j) (j : J) : α j :=
  if j∈S then u j else v j

theorem mean_pi_restrict (P : ∀j,FiniteLaw (α j)) (S : Finset J)
    (f : (∀j : {j // j∈S},α j) → ℝ) :
    (pi P).mean (fun u => f (fun j => u j)) =
      (pi (fun j : {j // j∈S} => P j)).mean f := by
  rw [mean_pi_split P S]
  have he (u : ∀j : {j // j∈S},α j) (v : ∀j : {j // j∉S},α j) : (fun j : {j // j∈S} => joinAssignment S u v j)=u := by
    funext j
    simp [joinAssignment]
  simp_rw [he,mean_const]

theorem mean_pi_replace (P : ∀j,FiniteLaw (α j)) (S : Finset J) (f : (∀j,α j) → ℝ) :
    (pi P).mean (fun u => (pi P).mean (fun v => f (replaceCoordinates S u v))) =
      (pi P).mean f := by
  rw [mean_pi_split P S f]
  have he (u v : ∀j,α j) : replaceCoordinates S u v =
      joinAssignment S (fun j => u j) (fun j => v j) := by
    funext j
    simp [replaceCoordinates,joinAssignment]
  simp_rw [he]
  have hv (u : ∀j,α j) : (pi P).mean (fun v => f (joinAssignment S (fun j => u j) (fun j => v j))) =
      (pi (fun j : {j // j∉S} => P j)).mean
        (fun v => f (joinAssignment S (fun j => u j) v)) := by
    rw [mean_pi_split P S]
    have he2 (a : ∀j : {j // j∈S},α j) (b : ∀j : {j // j∉S},α j) : (fun j : {j // j∉S} => joinAssignment S a b j)=b := by
      funext j
      simp [joinAssignment,j.property]
    simp_rw [he2,mean_const]
  simp_rw [hv]
  exact mean_pi_restrict P S (fun u => (pi (fun j : {j // j∉S} => P j)).mean
    (fun v => f (joinAssignment S u v)))

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/Resampling.lean

-- BEGIN PRProof/ConditionalMean.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*} [∀j,Fintype (α j)]

def conditionalMean (P : ∀j,FiniteLaw (α j)) (S : Finset J) (base : ∀j,α j)
    (f : (∀j,α j) → ℝ) : ℝ :=
  (pi P).mean (fun ω => f (replaceCoordinates S base ω))

theorem conditionalMean_empty (P : ∀j,FiniteLaw (α j)) (base : ∀j,α j)
    (f : (∀j,α j) → ℝ) : conditionalMean P ∅ base f=(pi P).mean f := by
  have he (ω : ∀j,α j) : replaceCoordinates ∅ base ω=ω := by
    funext j
    simp [replaceCoordinates]
  simp only [conditionalMean,he]

theorem conditionalMean_univ (P : ∀j,FiniteLaw (α j)) (base : ∀j,α j)
    (f : (∀j,α j) → ℝ) : conditionalMean P univ base f=f base := by
  have he (ω : ∀j,α j) : replaceCoordinates univ base ω=base := by
    funext j
    simp [replaceCoordinates]
  simp only [conditionalMean,he,mean_const]

theorem conditionalMean_const (P : ∀j,FiniteLaw (α j)) (S : Finset J) (base : ∀j,α j)
    (c : ℝ) : conditionalMean P S base (fun _ => c)=c := (pi P).mean_const c

theorem conditionalMean_mono (P : ∀j,FiniteLaw (α j)) (S : Finset J) (base : ∀j,α j)
    {f g : (∀j,α j) → ℝ} (h : ∀ω,f ω≤g ω) :
    conditionalMean P S base f ≤ conditionalMean P S base g := (pi P).mean_mono (fun ω => h (replaceCoordinates S base ω))

theorem conditionalMean_tower (P : ∀j,FiniteLaw (α j)) (S T : Finset J)
    (hST : Disjoint S T) (base : ∀j,α j) (f : (∀j,α j) → ℝ) :
    (pi P).mean (fun u => conditionalMean P (S∪T) (replaceCoordinates T u base) f) =
      conditionalMean P S base f := by
  have he (u v : ∀j,α j) :
      replaceCoordinates (S∪T) (replaceCoordinates T u base) v =
      replaceCoordinates S base (replaceCoordinates T u v) := by
    funext j
    by_cases hs : j∈S
    · have ht : j∉T := fun h => Finset.disjoint_left.mp hST hs h
      simp [replaceCoordinates,hs,ht]
    · by_cases ht : j∈T <;> simp [replaceCoordinates,hs,ht]
  unfold conditionalMean
  calc
    _ = (pi P).mean (fun u => (pi P).mean (fun v =>
        f (replaceCoordinates S base (replaceCoordinates T u v)))) := by
      congr 1
      funext u
      congr 1
      funext v
      exact congrArg f (he u v)
    _ = _ := mean_pi_replace P T (fun ω => f (replaceCoordinates S base ω))

theorem conditionalMean_agree (P : ∀j,FiniteLaw (α j)) (S : Finset J)
    (u v : ∀j,α j) (h : ∀j∈S,u j=v j) (f : (∀j,α j) → ℝ) :
    conditionalMean P S u f=conditionalMean P S v f := by
  unfold conditionalMean
  congr 1
  funext ω
  congr 1
  funext j
  by_cases hj : j∈S <;> simp [replaceCoordinates,hj,h j]

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/ConditionalMean.lean

-- BEGIN PRProof/UniformAtoms.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem uniform_prob_card (A : Ω → Prop) [DecidablePred A] :
    (uniform Ω).prob A = (Fintype.card {ω // A ω}:ℝ)/(Fintype.card Ω) := by
  classical
  unfold prob mean uniform
  simp only [mul_ite,mul_one,mul_zero,←Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Fintype.card_subtype]
  rfl

theorem uniform_atom_lower {A : Ω → Prop} (h : 0<(uniform Ω).prob A) :
    (Fintype.card Ω:ℝ)⁻¹ ≤ (uniform Ω).prob A := by
  classical
  obtain ⟨ω,hω⟩ := (uniform Ω).exists_of_prob_pos h
  let : Nonempty {ω // A ω} := ⟨⟨ω,hω⟩⟩
  rw [uniform_prob_card]
  have hc : (1:ℝ)≤Fintype.card {ω // A ω} := by exact_mod_cast Fintype.card_pos
  have hd : (0:ℝ)<Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  simpa only [one_div] using div_le_div_of_nonneg_right hc hd.le

theorem uniform_fiber_upper {B : Type*} (f : Ω → B) (hf : Function.Injective f) (b : B) :
    (uniform Ω).prob (fun ω => f ω=b) ≤ (Fintype.card Ω:ℝ)⁻¹ := by
  classical
  rw [uniform_prob_card]
  have hi : Subsingleton {ω // f ω=b} := ⟨fun x y => Subtype.ext (hf (x.property.trans y.property.symm))⟩
  let := hi
  have hc : (Fintype.card {ω // f ω=b}:ℝ)≤1 := by exact_mod_cast (Fintype.card_le_one_iff_subsingleton.mpr hi)
  have hd : (0:ℝ)≤Fintype.card Ω := Nat.cast_nonneg _
  simpa only [one_div] using div_le_div_of_nonneg_right hc hd

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/UniformAtoms.lean

-- BEGIN PRProof/UniformProduct.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*}
  [∀j,Fintype (α j)] [∀j,Nonempty (α j)]

theorem pi_uniform : pi (fun j => uniform (α j)) = uniform (∀j,α j) := by
  have he (P Q : FiniteLaw (∀j,α j)) (h : P.weight=Q.weight) : P=Q := by
    cases P
    cases Q
    cases h
    rfl
  apply he
  funext s
  simp only [pi,uniform,Fintype.card_pi,Nat.cast_prod,Finset.prod_inv_distrib]

theorem uniform_restrict (S : Finset J) (f : (∀j : {j // j∈S},α j) → ℝ) :
    (uniform (∀j,α j)).mean (fun u => f (fun j => u j)) =
      (uniform (∀j : {j // j∈S},α j)).mean f := by
  rw [←pi_uniform,mean_pi_restrict,pi_uniform]

theorem uniform_match_probability (S : Finset J) (base : ∀j,α j) :
    (uniform (∀j,α j)).prob (fun ω => ∀j∈S,ω j=base j) =
      (Fintype.card (∀j : {j // j∈S},α j):ℝ)⁻¹ := by
  classical
  have he (ω : ∀j,α j) : (∀j∈S,ω j=base j) ↔ (fun j : {j // j∈S} => ω j)=(fun j : {j // j∈S} => base j) := by
    constructor
    · intro h; funext j; exact h j j.property
    · intro h j hj; exact congrFun h ⟨j,hj⟩
  unfold prob
  simp_rw [he]
  rw [uniform_restrict S (fun u => if u=(fun j : {j // j∈S} => base j) then (1:ℝ) else 0)]
  have h : (uniform (∀j : {j // j∈S},α j)).prob
      (fun ω => ω=(fun j : {j // j∈S} => base j)) =
      (Fintype.card (∀j : {j // j∈S},α j):ℝ)⁻¹ := by
    rw [uniform_prob_card]
    simp
  unfold prob at h
  convert h using 1
  congr 1
  funext u
  split_ifs <;> rfl

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/UniformProduct.lean

-- BEGIN PRProof/Avoidance.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {Ω I : Type*} [Fintype Ω] [DecidableEq I]

def avoid (A : I → Ω → Prop) (S : Finset I) (ω : Ω) : Prop := ∀i∈S,¬A i ω

omit [Fintype Ω] [DecidableEq I] in
theorem avoid_empty (A : I → Ω → Prop) : avoid A ∅ = fun _ => True := by
  funext ω
  simp [avoid]

omit [Fintype Ω] in
theorem avoid_insert (A : I → Ω → Prop) (S : Finset I) (i : I) :
    avoid A (insert i S) = fun ω => avoid A S ω ∧ ¬A i ω := by
  funext ω
  simp [avoid,and_comm]

omit [DecidableEq I] in
theorem prob_avoid_mono (P : FiniteLaw Ω) (A : I → Ω → Prop) {S T : Finset I}
    (h : S ⊆ T) : P.prob (avoid A T) ≤ P.prob (avoid A S) :=
  P.prob_mono fun _ hw i hi => hw i (h hi)

theorem prob_avoid_insert (P : FiniteLaw Ω) (A : I → Ω → Prop) (S : Finset I) (i : I) :
    P.prob (avoid A (insert i S)) = P.prob (avoid A S) -
      P.prob (fun ω => avoid A S ω ∧ A i ω) := by
  rw [avoid_insert]
  have h := P.prob_split (avoid A S) (A i)
  linarith

theorem avoid_lower (P : FiniteLaw Ω) (A : I → Ω → Prop) (x : I → ℝ)
    (S : Finset I) (hx : ∀i, x i < 1)
    (hb : ∀T ⊆ S, ∀i∈S, i∉T →
      P.prob (fun ω => avoid A T ω ∧ A i ω) ≤ x i*P.prob (avoid A T)) :
    (∏ i ∈ S, (1 - x i)) ≤ P.prob (avoid A S) := by
  induction S using Finset.induction with
  | empty => simp [avoid_empty,P.prob_true]
  | @insert i S hi ih =>
    have hS := ih (fun T hT j hj hjT => hb T (hT.trans (subset_insert _ _)) j (mem_insert_of_mem hj) hjT)
    have hI := hb S (subset_insert _ _) i (mem_insert_self _ _) hi
    rw [Finset.prod_insert hi,prob_avoid_insert]
    have hmul := mul_le_mul_of_nonneg_left hS (le_of_lt (sub_pos.mpr (hx i)))
    nlinarith

theorem avoid_relative_lower (P : FiniteLaw Ω) (A : I → Ω → Prop) (x : I → ℝ)
    (R T : Finset I) (hx : ∀i, x i < 1) (hdis : Disjoint R T)
    (hb : ∀U ⊆ T, ∀i∈T, i∉U →
      P.prob (fun ω => avoid A (R∪U) ω ∧ A i ω) ≤ x i*P.prob (avoid A (R∪U))) :
    P.prob (avoid A R)*(∏ i ∈ T, (1 - x i)) ≤ P.prob (avoid A (R∪T)) := by
  induction T using Finset.induction with
  | empty => simp
  | @insert i T hi ih =>
    have hdisT : Disjoint R T := hdis.mono_right (subset_insert _ _)
    have hT := ih hdisT (fun U hU j hj hjU =>
      hb U (hU.trans (subset_insert _ _)) j (mem_insert_of_mem hj) hjU)
    have hI := hb T (subset_insert _ _) i (mem_insert_self _ _) hi
    have he : R∪insert i T = insert i (R∪T) := by ext j; simp
    rw [Finset.prod_insert hi,he,prob_avoid_insert]
    have hmul := mul_le_mul_of_nonneg_left hT (le_of_lt (sub_pos.mpr (hx i)))
    nlinarith

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/Avoidance.lean

-- BEGIN PRProof/LocalLemma.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {Ω I : Type*} [Fintype Ω] [DecidableEq I]

theorem local_lemma_conditional (P : FiniteLaw Ω) (A : I → Ω → Prop)
    (N : I → Finset I) (x : I → ℝ) (hx0 : ∀i,0≤x i) (hx1 : ∀i,x i<1)
    (hp : ∀i,P.prob (A i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hind : ∀i R, i∉R → Disjoint R (N i) →
      P.prob (fun ω => avoid A R ω ∧ A i ω) = P.prob (avoid A R)*P.prob (A i)) :
    ∀S : Finset I, ∀i, i∉S →
      P.prob (fun ω => avoid A S ω ∧ A i ω) ≤ x i*P.prob (avoid A S) := by
  intro S
  induction S using Finset.strongInductionOn
  rename_i S ih
  intro i hi
  let R := S \ N i
  let T := S ∩ N i
  have hR : R ⊆ S := sdiff_subset
  have hT : T ⊆ S := inter_subset_left
  have hTN : T ⊆ N i := inter_subset_right
  have hRT : R∪T=S := by ext j; simp [R,T]; tauto
  have hdis : Disjoint R T := by
    apply Finset.disjoint_left.mpr
    intro j hjR hjT
    exact (mem_sdiff.mp hjR).2 (mem_inter.mp hjT).2
  have hRN : Disjoint R (N i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hN
    exact (mem_sdiff.mp hj).2 hN
  have hiR : i∉R := fun h => hi (hR h)
  have hlower : P.prob (avoid A R)*(∏ j ∈ T, (1 - x j)) ≤ P.prob (avoid A S) := by
    rw [←hRT]
    apply P.avoid_relative_lower A x R T hx1 hdis
    intro U hU j hj hjU
    have hsub : R∪U ⊆ S := union_subset hR (hU.trans hT)
    have hjR : j∉R := fun h => Finset.disjoint_left.mp hdis h hj
    have hjRU : j∉R∪U := by simp [hjR,hjU]
    have hproper : R∪U ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
      intro he
      exact hjRU (he.symm ▸ hT hj)⟩
    exact ih _ hproper j hjRU
  have hprod : (∏ j ∈ N i, (1 - x j)) ≤ ∏ j ∈ T, (1 - x j) := by
    apply Finset.prod_le_prod_of_subset_of_le_one hTN
    · intro j _
      exact sub_nonneg.mpr (le_of_lt (hx1 j))
    · intro j _ _
      exact sub_le_self _ (hx0 j)
  have hnum : P.prob (fun ω => avoid A S ω ∧ A i ω) ≤
      P.prob (avoid A R)*P.prob (A i) := by
    rw [←hind i R hiR hRN]
    apply P.prob_mono
    intro ω h
    exact ⟨fun j hj => h.1 j (hR hj),h.2⟩
  have hpi := (hp i).trans (mul_le_mul_of_nonneg_left hprod (hx0 i))
  have hmul := mul_le_mul_of_nonneg_left hpi (P.prob_nonneg (avoid A R))
  have hmul2 := mul_le_mul_of_nonneg_left hlower (hx0 i)
  nlinarith
theorem local_lemma_positive (P : FiniteLaw Ω) (A : I → Ω → Prop)
    (N : I → Finset I) (x : I → ℝ) (hx0 : ∀i,0≤x i) (hx1 : ∀i,x i<1)
    (hp : ∀i,P.prob (A i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hind : ∀i R, i∉R → Disjoint R (N i) →
      P.prob (fun ω => avoid A R ω ∧ A i ω) = P.prob (avoid A R)*P.prob (A i))
    (S : Finset I) : 0 < P.prob (avoid A S) := by
  have h := P.avoid_lower A x S hx1 (fun T _ i _ hi =>
    P.local_lemma_conditional A N x hx0 hx1 hp hind T i hi)
  exact (Finset.prod_pos (fun i _ => sub_pos.mpr (hx1 i))).trans_le h

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/LocalLemma.lean

-- BEGIN PRProof/SymmetricLocalLemma.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {Ω I : Type*} [Fintype Ω] [DecidableEq I]

theorem symmetric_local_lemma (P : FiniteLaw Ω) (A : I → Ω → Prop)
    (N : I → Finset I) (d : ℕ) (p : ℝ)
    (hdeg : ∀i,(N i).card≤d) (hp : ∀i,P.prob (A i)≤p)
    (hsmall : 4*p*((d:ℝ)+1)≤1)
    (hind : ∀i R, i∉R → Disjoint R (N i) →
      P.prob (fun ω => avoid A R ω ∧ A i ω) = P.prob (avoid A R)*P.prob (A i))
    (S : Finset I) : ∃ω,avoid A S ω := by
  let x : ℝ := 1/(2*((d:ℝ)+1))
  have hd : 0<(d:ℝ)+1 := by positivity
  have hx0 : 0<x := by dsimp [x]; positivity
  have hxhalf : x≤1/2 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hx1 : x<1 := by linarith
  have hdx : (d:ℝ)*x≤1/2 := by
    dsimp [x]
    rw [←mul_div_assoc, mul_one]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hprod (i : I) : 1/2 ≤ ∏_j∈N i,(1-x) := by
    rw [Finset.prod_const]
    have hn := one_add_mul_le_pow (a := -x) (by linarith : -2≤-x) (N i).card
    have hcard : ((N i).card:ℝ)≤d := by exact_mod_cast hdeg i
    have hmul := mul_le_mul_of_nonneg_right hcard hx0.le
    have hn' : 1-((N i).card:ℝ)*x ≤ (1-x)^(N i).card := by
      simpa only [mul_neg, ←sub_eq_add_neg] using hn
    nlinarith [hn']
  have hpx : p≤x/2 := by
    dsimp [x]
    rw [div_div]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  apply P.exists_of_prob_pos
  apply P.local_lemma_positive A N (fun _ => x) (fun _ => hx0.le) (fun _ => hx1) _ hind S
  intro i
  have h := mul_le_mul_of_nonneg_left (hprod i) hx0.le
  exact (hp i).trans (hpx.trans (by nlinarith))

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/SymmetricLocalLemma.lean

-- BEGIN PRProof/SupportLocalLemma.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*}
  [∀j,Fintype (α j)] [∀j,Nonempty (α j)]

def EventDepends (A : (∀j,α j) → Prop) (S : Finset J) : Prop :=
  ∀u v, (∀j∈S,u j=v j) → (A u ↔ A v)

theorem prob_pi_independent (P : ∀j,FiniteLaw (α j)) (S T : Finset J)
    (hST : Disjoint S T) (A B : (∀j,α j) → Prop)
    (hA : EventDepends A S) (hB : EventDepends B T) :
    (pi P).prob (fun ω => A ω ∧ B ω) = (pi P).prob A*(pi P).prob B := by
  classical
  have h := mean_pi_independent P S T hST
    (fun ω => if A ω then (1:ℝ) else 0) (fun ω => if B ω then (1:ℝ) else 0)
    (by intro u v huv; dsimp only; rw [hA u v huv]) (by intro u v huv; dsimp only; rw [hB u v huv])
  have he : (fun ω => (if A ω then (1:ℝ) else 0)*(if B ω then (1:ℝ) else 0)) =
      fun ω => if A ω ∧ B ω then (1:ℝ) else 0 := by
    funext ω
    by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha,hb]
  rw [he] at h
  unfold prob
  convert h using 1
  congr 1
  funext ω
  split_ifs <;> rfl

omit [Fintype J] [∀j,Fintype (α j)] [∀j,Nonempty (α j)] in
theorem eventDepends_avoid {I : Type*} [DecidableEq I]
    (A : I → (∀j,α j) → Prop) (S : I → Finset J) (R : Finset I)
    (hA : ∀i,EventDepends (A i) (S i)) : EventDepends (avoid A R) (R.biUnion S) := by
  intro u v huv
  have he (i : I) (hi : i∈R) : A i u ↔ A i v := hA i u v (fun j hj =>
    huv j (mem_biUnion.mpr ⟨i,hi,hj⟩))
  constructor
  · intro h i hi hv
    exact h i hi ((he i hi).mpr hv)
  · intro h i hi hu
    exact h i hi ((he i hi).mp hu)

theorem support_local_lemma {I : Type*} [Fintype I] [DecidableEq I]
    (P : ∀j,FiniteLaw (α j)) (A : I → (∀j,α j) → Prop) (S : I → Finset J)
    (hA : ∀i,EventDepends (A i) (S i)) (d : ℕ) (p : ℝ)
    (hdeg : ∀i,(univ.filter (fun k => k≠i ∧ ¬Disjoint (S i) (S k))).card≤d)
    (hp : ∀i,(pi P).prob (A i)≤p) (hsmall : 4*p*((d:ℝ)+1)≤1) :
    ∃ω,∀i,¬A i ω := by
  classical
  let N (i : I) := univ.filter (fun k => k≠i ∧ ¬Disjoint (S i) (S k))
  have hind (i : I) (R : Finset I) (hi : i∉R) (hR : Disjoint R (N i)) :
      (pi P).prob (fun ω => avoid A R ω ∧ A i ω) =
        (pi P).prob (avoid A R)*(pi P).prob (A i) := by
    have hs : Disjoint (R.biUnion S) (S i) := by
      apply Finset.disjoint_left.mpr
      intro j hj hji
      obtain ⟨k,hk,hjk⟩ := mem_biUnion.mp hj
      have hki : k≠i := by intro he; subst k; exact hi hk
      have hkn : k∉N i := fun hn => Finset.disjoint_left.mp hR hk hn
      have hd : Disjoint (S i) (S k) := by
        by_contra hn
        exact hkn (mem_filter.mpr ⟨mem_univ _,hki,hn⟩)
      exact Finset.disjoint_left.mp hd hji hjk
    exact prob_pi_independent P _ _ hs _ _ (eventDepends_avoid A S R hA) (hA i)
  obtain ⟨ω,hω⟩ := (pi P).symmetric_local_lemma A N d p hdeg hp hsmall hind univ
  exact ⟨ω,fun i => hω i (mem_univ i)⟩

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/SupportLocalLemma.lean

-- BEGIN PRProof/CoordinateAtoms.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*}
  [∀j,Fintype (α j)] [∀j,Nonempty (α j)]

theorem uniform_coordinate_fiber {B : Type*} (f : (∀j,α j) → B) (i : J) (b : B)
    (hf : ∀u v, (∀j,j≠i → u j=v j) → f u=f v → u=v) :
    (uniform (∀j,α j)).prob (fun ω => f ω=b) ≤ (Fintype.card (α i):ℝ)⁻¹ := by
  classical
  let R := ∀j : {j // j≠i},α j
  let proj (u : {ω : ∀j,α j // f ω=b}) : R := fun j => u.val j
  have hinj : Function.Injective proj := by
    intro u v h
    apply Subtype.ext
    apply hf u.val v.val
    · intro j hj
      exact congrFun h ⟨j,hj⟩
    · exact u.property.trans v.property.symm
  have hc : (Fintype.card {ω : ∀j,α j // f ω=b}:ℝ)≤Fintype.card R := by
    exact_mod_cast Fintype.card_le_of_injective proj hinj
  have he : Fintype.card (∀j,α j)=Fintype.card (α i)*Fintype.card R := by
    simpa [R,Fintype.card_prod] using Fintype.card_congr (Equiv.piSplitAt i α)
  have hpos : (0:ℝ)<Fintype.card (∀j,α j) := by exact_mod_cast Fintype.card_pos
  have hi : (Fintype.card (α i):ℝ)≠0 := by exact_mod_cast (ne_of_gt (Fintype.card_pos (α := α i)))
  have hr : (Fintype.card R:ℝ)≠0 := by exact_mod_cast (ne_of_gt (Fintype.card_pos (α := R)))
  rw [uniform_prob_card]
  apply (div_le_div_of_nonneg_right hc hpos.le).trans_eq
  rw [he,Nat.cast_mul]
  field_simp

theorem uniform_support_atom_lower (A : (∀j,α j) → Prop) (S : Finset J)
    (hA : EventDepends A S) (hpos : 0<(uniform (∀j,α j)).prob A) :
    (Fintype.card (∀j : {j // j∈S},α j):ℝ)⁻¹ ≤ (uniform (∀j,α j)).prob A := by
  obtain ⟨base,hbase⟩ := (uniform (∀j,α j)).exists_of_prob_pos hpos
  rw [←uniform_match_probability S base]
  apply prob_mono
  intro ω hω
  exact (hA ω base hω).mpr hbase

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/CoordinateAtoms.lean

-- BEGIN PRProof/ConditionalSupport.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*}
  [∀j,Fintype (α j)]

theorem conditionalMean_sum {I : Type*} [Fintype I] (P : ∀j,FiniteLaw (α j))
    (S : Finset J) (base : ∀j,α j) (f : I → (∀j,α j) → ℝ) :
    conditionalMean P S base (fun ω => ∑i,f i ω) = ∑i,conditionalMean P S base (f i) := by
  simp only [conditionalMean,mean,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem conditionalMean_depends (P : ∀j,FiniteLaw (α j)) (S T : Finset J)
    (f : (∀j,α j) → ℝ) (hf : CoordinateDepends f T) :
    CoordinateDepends (fun base => conditionalMean P S base f) (S∩T) := by
  intro u v huv
  change (pi P).mean (fun ω => f (replaceCoordinates S u ω)) =
    (pi P).mean (fun ω => f (replaceCoordinates S v ω))
  apply congrArg ((pi P).mean)
  funext ω
  apply hf
  intro j hj
  by_cases hs : j∈S
  · simp only [replaceCoordinates,if_pos hs]
    exact huv j (mem_inter.mpr ⟨hs,hj⟩)
  · simp [replaceCoordinates,hs]

omit [Fintype J] [∀j,Fintype (α j)] in
theorem eventDepends_replace (A : (∀j,α j) → Prop) (S T : Finset J)
    (base : ∀j,α j) (hA : EventDepends A T) :
    EventDepends (fun ω => A (replaceCoordinates S base ω)) (T\S) := by
  intro u v huv
  apply hA
  intro j hj
  by_cases hs : j∈S
  · simp [replaceCoordinates,hs]
  · simp only [replaceCoordinates,if_neg hs]
    exact huv j (mem_sdiff.mpr ⟨hj,hs⟩)

theorem conditional_indicator_nonneg (P : ∀j,FiniteLaw (α j)) (S : Finset J)
    (base : ∀j,α j) (A : (∀j,α j) → Prop) [DecidablePred A] :
    0≤conditionalMean P S base (fun ω => if A ω then 1 else 0) := by
  apply (pi P).mean_nonneg
  intro ω
  dsimp only
  split_ifs <;> norm_num

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/ConditionalSupport.lean

-- BEGIN PRProof/RoutingSupport.lean
noncomputable section
namespace PacketRouting.CongDil.PRFresh

def routingLevel {h L : ℕ} : RoutingCoordinate h L → ℕ
  | none => 0
  | some j => j.1.val + 1

lemma routingWidth_pos (h L : ℕ) (j : RoutingCoordinate h L) :
    0 < routingWidth h L j := by
  cases j with
  | none => exact pow_pos (by decide) _
  | some j => exact delayScale_pos h (j.1.val + 1)

instance routingAlphabetNonempty (h L : ℕ) (j : RoutingCoordinate h L) :
    Nonempty (Fin (routingWidth h L j)) := ⟨⟨0, routingWidth_pos h L j⟩⟩

def routingSelected {h L q : ℕ} (hq : q ≤ 2 ^ h) : Finset (RoutingCoordinate h L) :=
  insert none (Finset.univ.image (fun l : Fin L => some (selectedHierarchyIndex h L q hq l)))

lemma routingTime_depends {P E : Type*} {path : P → List E} {h L H : ℕ}
    (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L) (hd : DilationLE path (2 ^ h))
    (p : P) (k : Fin (path p).length) (ω ν : P → RoutingAssignment h L)
    (he : ∀j ∈ routingSelected (le_trans (Nat.succ_le_of_lt k.isLt) (hd p)), ω p j = ν p j) :
    (routingTimetable path h L H hH hend ω).time p k =
      (routingTimetable path h L H hH hend ν).time p k := by
  have hr := he none (Finset.mem_insert_self _ _)
  have hs := hierarchy_delay_sum_depends hH hend
    (le_trans (Nat.succ_le_of_lt k.isLt) (hd p))
    (fun j => (ω p (some j)).val + 1) (fun j => (ν p (some j)).val + 1)
    (fun j => Nat.succ_le_of_lt (ω p (some j)).isLt)
    (fun j => Nat.succ_le_of_lt (ν p (some j)).isLt)
    (fun l => congrArg (fun z => z.val + 1) (he _ (by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩)))
  simp only [routingTimetable, familyTimetable]
  rw [hr, hs]

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingSupport.lean

-- BEGIN PRProof/FiberLabels.lean

namespace PacketRouting.CongDil.PRFresh

lemma exists_fiber_labels {I K : Type*} [Fintype I] [DecidableEq K] (key : I → K) {B : ℕ}
    (hB : 0 < B)
    (hcard : ∀ k, Fintype.card {i // key i = k} ≤ B) :
    ∃ label : I → Fin B, ∀ i j, key i = key j → label i = label j → i = j := by
  classical
  let f (k : K) (i : I) : Fin B :=
    if h : key i = k then
      ⟨(Fintype.equivFin {i // key i = k} ⟨i, h⟩).val,
        lt_of_lt_of_le (Fintype.equivFin {i // key i = k} ⟨i, h⟩).isLt (hcard k)⟩
    else ⟨0, hB⟩
  have hf (k : K) (i j : I) (hi : key i = k) (hj : key j = k)
      (he : f k i = f k j) : i = j := by
    have hv := congrArg Fin.val he
    simp only [f, dif_pos hi, dif_pos hj] at hv
    have heq : Fintype.equivFin {i // key i = k} ⟨i, hi⟩ =
        Fintype.equivFin {i // key i = k} ⟨j, hj⟩ := Fin.ext hv
    exact congrArg Subtype.val ((Fintype.equivFin _).injective heq)
  refine ⟨fun i => f (key i) i, ?_⟩
  intro i j hk he
  change f (key i) i = f (key j) j at he
  rw [← hk] at he
  exact hf (key i) i j rfl hk.symm he

end PacketRouting.CongDil.PRFresh

-- END PRProof/FiberLabels.lean

-- BEGIN PRProof/QueueBound.lean

namespace PacketRouting.CongDil.PRFresh

lemma queueSize_le_gap {P E : Type*} [Fintype P] {path : P → List E}
    (τ : Timetable path) (hv : τ.Valid) (G : ℕ)
    (hgap : ∀ p k (h : k + 1 < (path p).length),
      τ.time p ⟨k + 1, h⟩ ≤ τ.time p ⟨k, Nat.lt_of_succ_lt h⟩ + G)
    (g : E) (t : ℕ) : τ.queueSize g t ≤ G := by
  classical
  let S : Finset (Σ p : P, Fin (path p).length) := Finset.univ.filter (fun x =>
    (path x.1).get x.2 = g ∧ τ.time x.1 x.2 ≤ t ∧
      ∃ h : x.2.val + 1 < (path x.1).length, t < τ.time x.1 ⟨x.2.val + 1, h⟩)
  change S.card ≤ G
  have hm : Set.MapsTo (fun x : Σ p : P, Fin (path p).length => τ.time x.1 x.2)
      S (Finset.Ico (t + 1 - G) (t + 1)) := by
    intro x hx
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨_, ht, hh, hnext⟩ := hx
    have hg := hgap x.1 x.2.val hh
    change τ.time x.1 ⟨x.2.val + 1, hh⟩ ≤ τ.time x.1 x.2 + G at hg
    simp only [Finset.mem_coe, Finset.mem_Ico]
    constructor <;> omega
  have hi : (S : Set (Σ p : P, Fin (path p).length)).InjOn
      (fun x => τ.time x.1 x.2) := by
    intro x hx y hy he
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have hxy := hv x.1 y.1 x.2 y.2 (hx.1.trans hy.1.symm) he
    rcases x with ⟨p, k⟩
    rcases y with ⟨q, l⟩
    dsimp only at hxy
    obtain ⟨rfl, hk⟩ := hxy
    have : k = l := Fin.ext hk
    subst l
    rfl
  have hc := Finset.card_le_card_of_injOn _ hm hi
  have hb : (Finset.Ico (t + 1 - G) (t + 1)).card ≤ G := by
    rw [Nat.card_Ico]
    omega
  exact hc.trans hb

end PacketRouting.CongDil.PRFresh

-- END PRProof/QueueBound.lean

-- BEGIN PRProof/Serialization.lean

namespace PacketRouting.CongDil.PRFresh

noncomputable def crossingLoad {P E : Type*} [Fintype P] {path : P → List E}
    (τ : Timetable path) (g : E) (t : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : Σ p : P, Fin (path p).length =>
    (path x.1).get x.2 = g ∧ τ.time x.1 x.2 = t)).card

lemma serialize_timetable {P E : Type*} [Fintype P] {path : P → List E}
    (τ : Timetable path) {B L : ℕ} (hB : 0 < B)
    (hload : ∀ g t, crossingLoad τ g t ≤ B) (hL : τ.LengthLE L)
    (hgap : ∀ p k (h : k + 1 < (path p).length),
      τ.time p ⟨k + 1, h⟩ ≤ τ.time p ⟨k, Nat.lt_of_succ_lt h⟩ + 2) :
    ∃ σ : Timetable path, σ.Valid ∧ σ.LengthLE (B * (L + 1)) ∧
      ∀ g t, σ.queueSize g t ≤ 3 * B := by
  classical
  let key (x : Σ p : P, Fin (path p).length) := ((path x.1).get x.2, τ.time x.1 x.2)
  have hc (k : E × ℕ) : Fintype.card {x // key x = k} ≤ B := by
    rcases k with ⟨g, t⟩
    simpa only [Fintype.card_subtype, key, Prod.mk.injEq, crossingLoad] using hload g t
  obtain ⟨label, hlabel⟩ := exists_fiber_labels key hB hc
  let σ : Timetable path := {
    time := fun p k => B * τ.time p k + (label ⟨p, k⟩).val + 1
    one_le_time := by intros; omega
    strictMono_time := by
      intro p k l hkl
      have h := τ.strictMono_time p hkl
      have hm := Nat.mul_le_mul_left B (show τ.time p k + 1 ≤ τ.time p l by omega)
      have hk := (label ⟨p, k⟩).isLt
      dsimp only
      nlinarith }
  have hv : σ.Valid := by
    intro p q k l he ht
    change B * τ.time p k + (label ⟨p, k⟩).val + 1 =
      B * τ.time q l + (label ⟨q, l⟩).val + 1 at ht
    have hk := (label ⟨p, k⟩).isLt
    have hl := (label ⟨q, l⟩).isLt
    have ht0 : τ.time p k = τ.time q l := by
      rcases lt_trichotomy (τ.time p k) (τ.time q l) with h | h | h
      · have hm := Nat.mul_le_mul_left B (show τ.time p k + 1 ≤ τ.time q l by omega)
        nlinarith
      · exact h
      · have hm := Nat.mul_le_mul_left B (show τ.time q l + 1 ≤ τ.time p k by omega)
        nlinarith
    have hr : label ⟨p, k⟩ = label ⟨q, l⟩ := by
      apply Fin.ext
      rw [ht0] at ht
      omega
    have hx : (⟨p, k⟩ : Σ p : P, Fin (path p).length) = ⟨q, l⟩ :=
      hlabel _ _ (Prod.ext he ht0) hr
    cases hx
    exact ⟨rfl, rfl⟩
  have hlen : σ.LengthLE (B * (L + 1)) := by
    intro p k
    have hm := Nat.mul_le_mul_left B (hL p k)
    have hk := (label ⟨p, k⟩).isLt
    change B * τ.time p k + (label ⟨p, k⟩).val + 1 ≤ _
    nlinarith
  have hgap' : ∀ p k (h : k + 1 < (path p).length),
      σ.time p ⟨k + 1, h⟩ ≤ σ.time p ⟨k, Nat.lt_of_succ_lt h⟩ + 3 * B := by
    intro p k h
    have hm := Nat.mul_le_mul_left B (hgap p k h)
    have hk := (label ⟨p, ⟨k + 1, h⟩⟩).isLt
    change B * τ.time p ⟨k + 1, h⟩ + (label ⟨p, ⟨k + 1, h⟩⟩).val + 1 ≤ _
    dsimp only [σ]
    nlinarith
  exact ⟨σ, hv, hlen, fun g t => queueSize_le_gap σ hv (3 * B) hgap' g t⟩

end PacketRouting.CongDil.PRFresh

-- END PRProof/Serialization.lean

-- BEGIN PRProof/CoarseBasics.lean

namespace PacketRouting.CongDil.PRFresh

lemma crossingLoad_le_congestion {P E : Type*} [Fintype P] {path : P → List E}
    (hn : ∀ p, (path p).Nodup) (τ : Timetable path) {c : ℕ}
    (hc : CongestionLE path c) (g : E) (t : ℕ) : crossingLoad τ g t ≤ c := by
  classical
  let S : Finset (Σ p : P, Fin (path p).length) := Finset.univ.filter (fun x =>
    (path x.1).get x.2 = g ∧ τ.time x.1 x.2 = t)
  let T : Finset P := Finset.univ.filter (fun p => g ∈ path p)
  have hm : Set.MapsTo Sigma.fst (S : Set (Σ p : P, Fin (path p).length)) (T : Set P) := by
    intro x hx
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [T, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hx.1]
    exact List.get_mem _ _
  have hi : (S : Set (Σ p : P, Fin (path p).length)).InjOn Sigma.fst := by
    intro x hx y hy he
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    rcases x with ⟨p, k⟩
    rcases y with ⟨q, l⟩
    dsimp only at he hx hy
    subst q
    have hk : k = l := (hn p).injective_get (hx.1.trans hy.1.symm)
    subst l
    rfl
  exact (Finset.card_le_card_of_injOn Sigma.fst hm hi).trans (hc g)

def noWaitTimetable {P E : Type*} (path : P → List E) : Timetable path where
  time := fun _ k => k.val + 1
  one_le_time := by intros; omega
  strictMono_time := by intro p i j h; exact Nat.add_lt_add_right h 1

lemma noWaitTimetable_length {P E : Type*} {path : P → List E} {d : ℕ}
    (hd : DilationLE path d) : (noWaitTimetable path).LengthLE d := by
  intro p k
  have h := hd p
  change k.val + 1 ≤ d
  omega

lemma bounded_congestion_schedule {P E : Type*} [Fintype P] {path : P → List E}
    (hn : ∀ p, (path p).Nodup) {c d B : ℕ} (hc : CongestionLE path c)
    (hd : DilationLE path d) (hB : 0 < B) (hcB : c ≤ B) :
    ∃ τ : Timetable path, τ.Valid ∧ τ.LengthLE (B * (d + 1)) ∧
      ∀ g t, τ.queueSize g t ≤ 3 * B := by
  apply serialize_timetable (noWaitTimetable path) hB
  · intro g t
    exact (crossingLoad_le_congestion hn _ hc g t).trans hcB
  · exact noWaitTimetable_length hd
  · intro p k h
    change k + 1 + 1 ≤ k + 1 + 2
    omega

end PacketRouting.CongDil.PRFresh

-- END PRProof/CoarseBasics.lean

-- BEGIN PRProof/CrossingEvents.lean
noncomputable section
namespace PacketRouting.CongDil.PRFresh

abbrev Crossing {P E : Type*} (path : P → List E) := Σ p : P, Fin (path p).length

def crossingEdge {P E : Type*} (path : P → List E) (x : Crossing path) : E :=
  (path x.1).get x.2

lemma crossing_packet_injective {P E : Type*} {path : P → List E}
    (hn : ∀p,(path p).Nodup) (g : E) :
    Set.InjOn Sigma.fst {x : Crossing path | crossingEdge path x=g} := by
  intro x hx y hy he
  rcases x with ⟨p,k⟩
  rcases y with ⟨q,l⟩
  dsimp only at he
  subst q
  have hk : k=l := (hn p).injective_get (hx.trans hy.symm)
  subst l
  rfl

noncomputable def usedEdges {P E : Type*} [Fintype P] (path : P → List E) : Finset E := by
  classical
  exact Finset.univ.image (crossingEdge path)

lemma crossing_mem_usedEdges {P E : Type*} [Fintype P] (path : P → List E)
    (x : Crossing path) : crossingEdge path x ∈ usedEdges path := by
  classical
  exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩

lemma crossingLoad_zero_of_unused {P E : Type*} [Fintype P] {path : P → List E}
    (τ : Timetable path) {g : E} (hg : g ∉ usedEdges path) (t : ℕ) :
    crossingLoad τ g t=0 := by
  classical
  unfold crossingLoad
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have he := (Finset.mem_filter.mp hx).2.1
  apply hg
  rw [←he]
  exact crossing_mem_usedEdges path x

lemma crossingLoad_zero_after_length {P E : Type*} [Fintype P] {path : P → List E}
    (τ : Timetable path) {N : ℕ} (hN : τ.LengthLE N) (g : E) {t : ℕ} (ht : N<t) :
    crossingLoad τ g t=0 := by
  classical
  unfold crossingLoad
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have he := (Finset.mem_filter.mp hx).2.2
  have hb := hN x.1 x.2
  omega

end PacketRouting.CongDil.PRFresh

-- END PRProof/CrossingEvents.lean

-- BEGIN PRProof/RoutingEvents.lean
noncomputable section
namespace PacketRouting.CongDil.PRFresh

abbrev FlatRoutingAssignment (P : Type*) (h L : ℕ) :=
  (j : P × RoutingCoordinate h L) → Fin (routingWidth h L j.2)

def arrivalSupport {P E : Type*} [DecidableEq P] {path : P → List E}
    {h L : ℕ} (hd : DilationLE path (2^h)) (x : Crossing path) :
    Finset (P × RoutingCoordinate h L) :=
  (routingSelected (L := L) (le_trans (Nat.succ_le_of_lt x.2.isLt) (hd x.1))).image
    (fun j => (x.1,j))

lemma arrival_depends {P E : Type*} [DecidableEq P] {path : P → List E}
    {h L H : ℕ} (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (hd : DilationLE path (2^h)) (x : Crossing path) (t : ℕ) :
    FiniteLaw.EventDepends
      (fun ω : FlatRoutingAssignment P h L =>
        (routingTimetable path h L H hH hend (fun p j => ω (p,j))).time x.1 x.2=t)
      (arrivalSupport hd x) := by
  intro ω ν he
  have ht := routingTime_depends hH hend hd x.1 x.2
    (fun p j => ω (p,j)) (fun p j => ν (p,j)) (fun j hj =>
      he (x.1,j) (Finset.mem_image.mpr ⟨j,hj,rfl⟩))
  change _ = t ↔ _ = t
  rw [ht]

lemma arrivalSupport_packet {P E : Type*} [DecidableEq P] {path : P → List E}
    {h L : ℕ} (hd : DilationLE path (2^h)) (x : Crossing path)
    {j : P × RoutingCoordinate h L} (hj : j∈arrivalSupport hd x) : j.1=x.1 := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
  rfl

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingEvents.lean

-- BEGIN PRProof/ConditionalAtoms.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*}
  [∀j,Fintype (α j)] [∀j,Nonempty (α j)]

def conditionalProb (S : Finset J) (base : ∀j,α j) (A : (∀j,α j) → Prop) : ℝ :=
  (uniform (∀j,α j)).prob (fun ω => A (replaceCoordinates S base ω))

theorem conditionalProb_fiber {B : Type*} (S : Finset J) (base : ∀j,α j)
    (f : (∀j,α j) → B) (i : J) (hi : i∉S) (b : B)
    (hf : ∀u v, (∀j,j≠i → u j=v j) → f u=f v → u=v) :
    conditionalProb S base (fun ω => f ω=b) ≤ (Fintype.card (α i):ℝ)⁻¹ := by
  apply uniform_coordinate_fiber (fun ω => f (replaceCoordinates S base ω)) i b
  intro u v huv he
  have hr : replaceCoordinates S base u=replaceCoordinates S base v := by
    apply hf _ _ _ he
    intro j hj
    by_cases hs : j∈S <;> simp [replaceCoordinates,hs,huv j hj]
  funext j
  by_cases hj : j=i
  · subst j
    simpa only [replaceCoordinates,if_neg hi] using congrFun hr i
  · exact huv j hj

theorem conditionalProb_atom (S T : Finset J) (base : ∀j,α j)
    (A : (∀j,α j) → Prop) (hA : EventDepends A T)
    (hp : 0<conditionalProb S base A) :
    (Fintype.card (∀j : {j // j∈T\S},α j):ℝ)⁻¹ ≤ conditionalProb S base A := by
  exact uniform_support_atom_lower _ (T\S) (eventDepends_replace A S T base hA) hp

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/ConditionalAtoms.lean

-- BEGIN PRProof/PositiveMean.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem weight_mul_le_mean (P : FiniteLaw Ω) (f : Ω → ℝ) (hf : ∀ω,0≤f ω) (ω : Ω) :
    P.weight ω*f ω ≤ P.mean f := by
  classical
  exact Finset.single_le_sum (fun x _ => mul_nonneg (P.nonneg x) (hf x)) (mem_univ ω)

theorem eq_zero_of_mean_eq_zero (P : FiniteLaw Ω) (hP : ∀ω,0<P.weight ω)
    (f : Ω → ℝ) (hf : ∀ω,0≤f ω) (h : P.mean f=0) : ∀ω,f ω=0 := by
  intro ω
  have hm := P.weight_mul_le_mean f hf ω
  rw [h] at hm
  have hz : f ω≤0 := by nlinarith [hP ω]
  exact le_antisymm hz (hf ω)

theorem uniform_mean_zero [Nonempty Ω] (f : Ω → ℝ) (hf : ∀ω,0≤f ω)
    (h : (uniform Ω).mean f=0) : ∀ω,f ω=0 := by
  apply (uniform Ω).eq_zero_of_mean_eq_zero _ f hf h
  intro ω
  change 0<(Fintype.card Ω:ℝ)⁻¹
  exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

theorem positive_support_card {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → ℝ) {a γ : ℝ} (_ha : 0<a) (hf : ∀i,0≤f i)
    (hpos : ∀i,0<f i → a≤f i) (hsum : (∑i,f i)≤γ) :
    ((univ.filter (fun i => 0<f i)).card:ℝ)*a ≤ γ := by
  classical
  have h : (∑i∈univ.filter (fun i => 0<f i),a) ≤ ∑i,f i := by
    calc
      _ ≤ ∑i∈univ.filter (fun i => 0<f i),f i := sum_le_sum (fun i hi => hpos i (mem_filter.mp hi).2)
      _ ≤ ∑i,f i := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => hf i)
  simpa only [sum_const,nsmul_eq_mul] using h.trans hsum

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/PositiveMean.lean

-- BEGIN PRProof/LevelConditioning.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*}
  [∀j,Fintype (α j)] [∀j,Nonempty (α j)]

theorem conditionalProb_eq_mean (S : Finset J) (base : ∀j,α j)
    (A : (∀j,α j) → Prop) [DecidablePred A] :
    conditionalProb S base A = conditionalMean (fun j => uniform (α j)) S base
      (fun ω => if A ω then 1 else 0) := by
  unfold conditionalProb conditionalMean prob
  rw [pi_uniform]
  congr 1
  funext ω
  dsimp only
  split_ifs <;> rfl

theorem conditionalProb_tower (S T : Finset J) (hST : Disjoint S T)
    (base : ∀j,α j) (A : (∀j,α j) → Prop) :
    (uniform (∀j,α j)).mean (fun u => conditionalProb (S∪T) (replaceCoordinates T u base) A) =
      conditionalProb S base A := by
  classical
  simp_rw [conditionalProb_eq_mean]
  rw [←pi_uniform]
  exact conditionalMean_tower _ S T hST base _

theorem conditionalProb_nonneg (S : Finset J) (base : ∀j,α j) (A : (∀j,α j) → Prop) :
    0≤conditionalProb S base A := (uniform (∀j,α j)).prob_nonneg _

theorem conditionalProb_zero_refine (S T : Finset J) (hST : Disjoint S T)
    (base : ∀j,α j) (A : (∀j,α j) → Prop) (hz : conditionalProb S base A=0)
    (u : ∀j,α j) : conditionalProb (S∪T) (replaceCoordinates T u base) A=0 := by
  apply uniform_mean_zero (fun u => conditionalProb (S∪T) (replaceCoordinates T u base) A)
    (fun u => conditionalProb_nonneg _ _ _) _ u
  rw [conditionalProb_tower S T hST,hz]

def beforeLevel (level : J → ℕ) (n : ℕ) : Finset J := univ.filter (fun j => level j<n)
def atLevel (level : J → ℕ) (n : ℕ) : Finset J := univ.filter (fun j => level j=n)

theorem beforeLevel_succ (level : J → ℕ) (n : ℕ) :
    beforeLevel level (n+1)=beforeLevel level n ∪ atLevel level n := by
  ext j
  simp only [beforeLevel,atLevel,mem_filter,mem_univ,true_and,mem_union]
  omega

omit [DecidableEq J] in
theorem before_at_disjoint (level : J → ℕ) (n : ℕ) :
    Disjoint (beforeLevel level n) (atLevel level n) := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  have h1 := (mem_filter.mp hj).2
  have h2 := (mem_filter.mp hk).2
  omega

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/LevelConditioning.lean

-- BEGIN PRProof/CoordinateLevels.lean
noncomputable section
namespace PacketRouting.CongDil.PRFresh

lemma routingSelected_level_injective {h L q : ℕ} (hq : q≤2^h) :
    Set.InjOn (@routingLevel h L) (routingSelected (L := L) hq) := by
  classical
  intro i hi j hj he
  simp only [routingSelected, Finset.mem_coe, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and] at hi hj
  rcases hi with rfl | ⟨l,rfl⟩ <;> rcases hj with rfl | ⟨k,rfl⟩
  · rfl
  · simp only [routingLevel, selectedHierarchyIndex] at he
    omega
  · simp only [routingLevel, selectedHierarchyIndex] at he
    omega
  · have hlk : l=k := by
      apply Fin.ext
      simpa only [routingLevel,selectedHierarchyIndex,Nat.add_right_cancel_iff] using he
    subst k
    rfl

noncomputable def selectedAtLevel {h L q : ℕ} (hq : q≤2^h) (n : ℕ) (hn : n≤L) :
    RoutingCoordinate h L :=
  if hz : n=0 then none else some (selectedHierarchyIndex h L q hq ⟨n-1,by omega⟩)

lemma selectedAtLevel_mem {h L q n : ℕ} (hq : q≤2^h) (hn : n≤L) :
    selectedAtLevel hq n hn ∈ routingSelected (L := L) hq := by
  classical
  unfold selectedAtLevel
  split_ifs with hz
  · exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩

lemma selectedAtLevel_level {h L q n : ℕ} (hq : q≤2^h) (hn : n≤L) :
    routingLevel (selectedAtLevel hq n hn)=n := by
  unfold selectedAtLevel
  split_ifs with hz
  · exact hz.symm
  · simp only [routingLevel,selectedHierarchyIndex]
    omega

lemma arrival_current_support {P E : Type*} [Fintype P] [DecidableEq P]
    {path : P → List E} {h L n : ℕ} (hd : DilationLE path (2^h)) (hn : n≤L)
    (x : Crossing path) :
    FiniteLaw.atLevel (fun j : P × RoutingCoordinate h L => routingLevel j.2) n ∩
      arrivalSupport hd x ⊆
      {(x.1,selectedAtLevel (le_trans (Nat.succ_le_of_lt x.2.isLt) (hd x.1)) n hn)} := by
  classical
  intro j hj
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hj).2
  apply Finset.mem_singleton.mpr
  congr 1
  apply routingSelected_level_injective _ hi (selectedAtLevel_mem _ hn)
  have he := (Finset.mem_filter.mp (Finset.mem_inter.mp hj).1).2
  simpa only [selectedAtLevel_level] using he

end PacketRouting.CongDil.PRFresh

-- END PRProof/CoordinateLevels.lean

-- BEGIN PRProof/LoadIdentity.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

lemma crossingLoad_cast {P E : Type*} [Fintype P] [DecidableEq E] {path : P → List E}
    (τ : Timetable path) (g : E) (t : ℕ) :
    (crossingLoad τ g t : ℝ) = ∑x : Crossing path,
      if crossingEdge path x=g ∧ τ.time x.1 x.2=t then (1:ℝ) else 0 := by
  classical
  simp only [crossingLoad,crossingEdge]
  rw [←Finset.sum_boole]
  apply sum_congr rfl
  intro x _
  split_ifs with he
  · exact (if_pos he).symm
  · exact (if_neg he).symm

lemma edgeCrossings_card {P E : Type*} [Fintype P] [DecidableEq E] {path : P → List E}
    (hn : ∀p,(path p).Nodup) {c : ℕ} (hc : CongestionLE path c) (g : E) :
    (univ.filter (fun x : Crossing path => crossingEdge path x=g)).card ≤ c := by
  classical
  apply le_trans (Finset.card_le_card_of_injOn Sigma.fst ?_ ?_) (hc g)
  · intro x hx
    simp only [Finset.mem_coe,mem_filter,mem_univ,true_and] at hx ⊢
    rw [←hx]
    exact List.get_mem _ _
  · intro x hx y hy he
    exact crossing_packet_injective hn g (mem_filter.mp hx).2 (mem_filter.mp hy).2 he

lemma conditional_crossingLoad {P E : Type*} [Fintype P] [DecidableEq P]
    {path : P → List E} {h L H : ℕ} (hH : 8≤H) (hend : H ≤ scaleExponent h L)
    (past : Finset (P × RoutingCoordinate h L)) (base : FlatRoutingAssignment P h L)
    (g : E) (t : ℕ) :
    FiniteLaw.conditionalMean (fun j : P × RoutingCoordinate h L =>
      FiniteLaw.uniform (Fin (routingWidth h L j.2))) past base
      (fun ω => (crossingLoad (routingTimetable path h L H hH hend
        (fun p j => ω (p,j))) g t : ℝ)) =
    ∑x : Crossing path, FiniteLaw.conditionalProb past base
      (fun ω : FlatRoutingAssignment P h L => crossingEdge path x=g ∧
        (routingTimetable path h L H hH hend (fun p j => ω (p,j))).time x.1 x.2=t) := by
  classical
  simp_rw [crossingLoad_cast]
  rw [FiniteLaw.conditionalMean_sum]
  apply sum_congr rfl
  intro x _
  exact (FiniteLaw.conditionalProb_eq_mean past base (fun ω : FlatRoutingAssignment P h L => crossingEdge path x=g ∧
    (routingTimetable path h L H hH hend (fun p j => ω (p,j))).time x.1 x.2=t)).symm

end PacketRouting.CongDil.PRFresh

-- END PRProof/LoadIdentity.lean

-- BEGIN PRProof/SingleCoordinate.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*}
  [∀j,Fintype (α j)] [∀j,Nonempty (α j)]

omit [∀j,Nonempty (α j)] in
/-- After fixing the past, a function with only one newly revealed support
coordinate is genuinely a function of that single choice. -/
theorem conditional_single_coordinate (P : ∀j,FiniteLaw (α j))
    (past current support : Finset J) (base : ∀j,α j)
    (f : (∀j,α j) → ℝ) (hf : CoordinateDepends f support)
    (i : J) (hs : current ∩ support ⊆ {i})
    (u v : ∀j,α j) (hi : u i=v i) :
    conditionalMean P (past∪current) (replaceCoordinates current u base) f =
      conditionalMean P (past∪current) (replaceCoordinates current v base) f := by
  apply conditionalMean_depends P (past∪current) support f hf
  intro j hj
  by_cases hc : j∈current
  · have hji : j=i := mem_singleton.mp (hs (mem_inter.mpr ⟨hc,(mem_inter.mp hj).2⟩))
    subst j
    simp only [replaceCoordinates,if_pos hc,hi]
  · simp only [replaceCoordinates,if_neg hc]

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/SingleCoordinate.lean

-- BEGIN PRProof/SupportDegree.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
variable {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]

theorem support_degree_bound (S : I → Finset J) (a b : ℕ)
    (hsize : ∀i,(S i).card≤a)
    (hocc : ∀j,(univ.filter (fun i => j∈S i)).card≤b) (i : I) :
    (univ.filter (fun k => k≠i ∧ ¬Disjoint (S i) (S k))).card ≤ a*b := by
  classical
  have hsub : univ.filter (fun k => k≠i ∧ ¬Disjoint (S i) (S k)) ⊆
      (S i).biUnion (fun j => univ.filter (fun k => j∈S k)) := by
    intro k hk
    have hn := (mem_filter.mp hk).2.2
    obtain ⟨j,hji,hjk⟩ := Finset.not_disjoint_iff.mp hn
    exact mem_biUnion.mpr ⟨j,hji,mem_filter.mpr ⟨mem_univ _,hjk⟩⟩
  calc
    _ ≤ ((S i).biUnion (fun j => univ.filter (fun k => j∈S k))).card := card_le_card hsub
    _ ≤ ∑j∈S i,(univ.filter (fun k => j∈S k)).card := card_biUnion_le
    _ ≤ ∑_j∈S i,b := sum_le_sum (fun j _ => hocc j)
    _ = (S i).card*b := by simp
    _ ≤ a*b := Nat.mul_le_mul_right b (hsize i)

end PacketRouting.CongDil.PRFresh

-- END PRProof/SupportDegree.lean

-- BEGIN PRProof/BoundedMGF.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

theorem exp_small_quadratic {z : ℝ} (hz : 0≤z) (hz1 : z≤1) :
    Real.exp z ≤ 1+z+z^2 := by
  have h := Real.exp_bound' (n := 2) hz hz1 (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  nlinarith [sq_nonneg z]

theorem exp_chord {δ t z : ℝ} (hδ : 0<δ) (_ht : 0≤t) (hz : 0≤z) (hzδ : z≤δ) :
    Real.exp (t*z) ≤ 1+(Real.exp (t*δ)-1)*(z/δ) := by
  have hzdiv : 0≤z/δ := div_nonneg hz hδ.le
  have hzdiv1 : z/δ≤1 := (div_le_one hδ).mpr hzδ
  have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (t*δ))
    (sub_nonneg.mpr hzdiv1) hzdiv (by ring : 1-z/δ+z/δ=1)
  have he : (1-z/δ)*(0:ℝ)+(z/δ)*(t*δ)=t*z := by field_simp; ring
  simp only [smul_eq_mul,Real.exp_zero] at h
  rw [he] at h
  nlinarith

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem mean_exp_le (P : FiniteLaw Ω) (Z : Ω → ℝ) {δ t : ℝ}
    (hδ : 0<δ) (ht : 0≤t) (htδ : t*δ≤1) (hZ : ∀ω,0≤Z ω ∧ Z ω≤δ) :
    P.mean (fun ω => Real.exp (t*Z ω)) ≤ Real.exp ((t+t^2*δ)*P.mean Z) := by
  have hc := P.mean_mono (fun ω => exp_chord hδ ht (hZ ω).1 (hZ ω).2)
  have he : P.mean (fun ω => 1+(Real.exp (t*δ)-1)*(Z ω/δ)) =
      1+(Real.exp (t*δ)-1)/δ*P.mean Z := by
    have hf : (fun ω => 1+(Real.exp (t*δ)-1)*(Z ω/δ)) =
        fun ω => 1+((Real.exp (t*δ)-1)/δ)*Z ω := by funext ω; ring
    rw [hf,P.mean_add,P.mean_const,P.mean_mul]
  rw [he] at hc
  have hs := exp_small_quadratic (mul_nonneg ht hδ.le) htδ
  have hcoef : (Real.exp (t*δ)-1)/δ ≤ t+t^2*δ := by
    apply (div_le_iff₀ hδ).mpr
    nlinarith
  have hm := P.mean_nonneg (fun ω => (hZ ω).1)
  have hm2 := mul_le_mul_of_nonneg_right hcoef hm
  exact hc.trans ((by linarith : 1+(Real.exp (t*δ)-1)/δ*P.mean Z ≤
    1+(t+t^2*δ)*P.mean Z).trans (by simpa [add_comm] using Real.add_one_le_exp ((t+t^2*δ)*P.mean Z)))

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/BoundedMGF.lean

-- BEGIN PRProof/FiniteChernoff.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*} [∀j,Fintype (α j)]

theorem sum_mgf (P : ∀j,FiniteLaw (α j)) (Z : ∀j,α j → ℝ) {δ t : ℝ}
    (hδ : 0<δ) (ht : 0≤t) (htδ : t*δ≤1) (hZ : ∀j ω,0≤Z j ω ∧ Z j ω≤δ) :
    (pi P).mean (fun ω => Real.exp (t*∑j,Z j (ω j))) ≤
      Real.exp ((t+t^2*δ)*∑j,(P j).mean (Z j)) := by
  have he (ω : ∀j,α j) : Real.exp (t*∑j,Z j (ω j)) = ∏j,Real.exp (t*Z j (ω j)) := by
    rw [Finset.mul_sum,Real.exp_sum]
  simp_rw [he]
  rw [mean_pi_prod P (fun j a => Real.exp (t*Z j a))]
  have h := Finset.prod_le_prod (s := Finset.univ)
    (fun j _ => (P j).mean_nonneg (fun ω => (Real.exp_pos _).le))
    (fun j _ => (P j).mean_exp_le (Z j) hδ ht htδ (hZ j))
  simpa only [←Real.exp_sum,←Finset.mul_sum] using h

theorem exponential_markov {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (Z : Ω → ℝ)
    {t b : ℝ} (ht : 0≤t) :
    P.prob (fun ω => b<Z ω) ≤ Real.exp (-t*b)*P.mean (fun ω => Real.exp (t*Z ω)) := by
  classical
  rw [←P.mean_mul]
  apply P.mean_mono
  intro ω
  split_ifs with h
  · rw [←Real.exp_add]
    have hz : 0≤-t*b+t*Z ω := by nlinarith
    simpa using Real.exp_le_exp.mpr hz
  · positivity

theorem bounded_sum_tail (P : ∀j,FiniteLaw (α j)) (Z : ∀j,α j → ℝ)
    {δ γ η : ℝ} (hδ : 0<δ) (hγ : 1≤γ) (hη : 0<η) (hη1 : η≤1)
    (hZ : ∀j ω,0≤Z j ω ∧ Z j ω≤δ)
    (hmean : (∑j,(P j).mean (Z j))≤γ) :
    (pi P).prob (fun ω => γ+η<∑j,Z j (ω j)) ≤ Real.exp (-(η^2)/(4*δ*γ)) := by
  have hγ0 : 0<γ := by linarith
  let t := η/(2*δ*γ)
  have ht : 0<t := by dsimp [t]; positivity
  have htδ : t*δ≤1 := by
    have he : t*δ=η/(2*γ) := by dsimp [t]; field_simp
    rw [he]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hm := sum_mgf P Z hδ ht.le htδ hZ
  have hc : 0≤t+t^2*δ := by positivity
  have hm' := hm.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmean hc))
  have hmk := exponential_markov (pi P) (fun ω => ∑j,Z j (ω j)) (b := γ+η) ht.le
  have hmul := mul_le_mul_of_nonneg_left hm' (Real.exp_pos (-t*(γ+η))).le
  apply (hmk.trans hmul).trans_eq
  rw [←Real.exp_add]
  congr 1
  dsimp [t]
  field_simp
  ring

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/FiniteChernoff.lean

-- BEGIN PRProof/LoadRefinement.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
  {α : J → Type*} [∀j,Fintype (α j)] [∀j,Nonempty (α j)]

theorem refine_load (P : ∀j,FiniteLaw (α j)) (Z : I → ∀j,α j → ℝ)
    (S : I → Finset J) (a b : ℕ) {δ γ η : ℝ}
    (hδ : 0<δ) (hγ : 1≤γ) (hη : 0<η) (hη1 : η≤1)
    (hZ : ∀i j ω,0≤Z i j ω ∧ Z i j ω≤δ)
    (hout : ∀i j,j∉S i → ∀ω,Z i j ω=0)
    (hmean : ∀i,(∑j,(P j).mean (Z i j))≤γ)
    (hsize : ∀i,(S i).card≤a)
    (hocc : ∀j,(univ.filter (fun i => j∈S i)).card≤b)
    (hsmall : 4*Real.exp (-(η^2)/(4*δ*γ))*((a*b:ℕ)+1)≤1) :
    ∃ω : ∀j,α j, ∀i,(∑j,Z i j (ω j))≤γ+η := by
  classical
  let A (i : I) (ω : ∀j,α j) : Prop := γ+η<∑j,Z i j (ω j)
  have hA (i : I) : EventDepends (A i) (S i) := by
    intro u v huv
    have he : (∑j,Z i j (u j))=∑j,Z i j (v j) := by
      apply sum_congr rfl
      intro j _
      by_cases hj : j∈S i
      · rw [huv j hj]
      · rw [hout i j hj,hout i j hj]
    simp only [A,he]
  have hp (i : I) : (pi P).prob (A i)≤Real.exp (-(η^2)/(4*δ*γ)) :=
    bounded_sum_tail P (Z i) hδ hγ hη hη1 (hZ i) (hmean i)
  obtain ⟨ω,hω⟩ := support_local_lemma P A S hA (a*b) _
    (support_degree_bound S a b hsize hocc) hp (by exact_mod_cast hsmall)
  exact ⟨ω,fun i => le_of_not_gt (hω i)⟩

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/LoadRefinement.lean

-- BEGIN PRProof/ConditionalRefinement.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
  {α : J → Type*} [∀j,Fintype (α j)] [∀j,Nonempty (α j)]

omit [∀j,Nonempty (α j)] in
theorem mean_pi_sum (P : ∀j,FiniteLaw (α j)) (Z : ∀j,α j → ℝ) :
    (pi P).mean (fun ω => ∑j,Z j (ω j)) = ∑j,(P j).mean (Z j) := by
  calc
    _ = ∑j,(pi P).mean (fun ω => Z j (ω j)) := by
      simp only [mean,Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_congr rfl (fun j _ => mean_pi_eval P j (Z j))

theorem refine_conditioned_load (P : ∀j,FiniteLaw (α j)) (past current : Finset J)
    (hdis : Disjoint past current) (base : ∀j,α j) (load : I → (∀j,α j) → ℝ)
    (Z : I → ∀j,α j → ℝ) (S : I → Finset J) (a b : ℕ) {δ γ η : ℝ}
    (hδ : 0<δ) (hγ : 1≤γ) (hη : 0<η) (hη1 : η≤1)
    (he : ∀i ω, conditionalMean P (past∪current) (replaceCoordinates current ω base) (load i) =
      ∑j,Z i j (ω j))
    (hZ : ∀i j ω,0≤Z i j ω ∧ Z i j ω≤δ)
    (hout : ∀i j,j∉S i → ∀ω,Z i j ω=0)
    (hmean : ∀i,conditionalMean P past base (load i)≤γ)
    (hsize : ∀i,(S i).card≤a)
    (hocc : ∀j,(univ.filter (fun i => j∈S i)).card≤b)
    (hsmall : 4*Real.exp (-(η^2)/(4*δ*γ))*((a*b:ℕ)+1)≤1) :
    ∃ν : ∀j,α j, (∀j∈past,ν j=base j) ∧
      ∀i,conditionalMean P (past∪current) ν (load i)≤γ+η := by
  have hm (i : I) : (∑j,(P j).mean (Z i j))≤γ := by
    rw [←mean_pi_sum]
    have ht := conditionalMean_tower P past current hdis base (load i)
    simp_rw [he i] at ht
    rw [ht]
    exact hmean i
  obtain ⟨ω,hω⟩ := refine_load P Z S a b hδ hγ hη hη1 hZ hout hm hsize hocc hsmall
  refine ⟨replaceCoordinates current ω base,?_,?_⟩
  · intro j hj
    have hc : j∉current := fun h => Finset.disjoint_left.mp hdis hj h
    simp [replaceCoordinates,hc]
  · intro i
    rw [he]
    exact hω i

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/ConditionalRefinement.lean

-- BEGIN PRProof/InjectiveLoad.lean
noncomputable section
namespace PacketRouting.CongDil.PRFresh
open Finset

/-- Group a finite family by its actual coordinate. Injectivity on the active family
ensures each grouped summand has the same bound as a single summand. -/
def groupedLoad {X J : Type*} [Fintype X] [DecidableEq J]
    (active : Finset X) (coord : X → J) {α : J → Type*}
    (f : (x : X) → α (coord x) → ℝ) (j : J) (z : α j) : ℝ :=
  ∑ x ∈ active, if h : coord x = j then f x (h.symm ▸ z) else 0

lemma groupedLoad_bounds {X J : Type*} [Fintype X] [DecidableEq X] [DecidableEq J]
    (active : Finset X) (coord : X → J) {α : J → Type*}
    (f : (x : X) → α (coord x) → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hinj : Set.InjOn coord active) (hf : ∀x∈active,∀z,0≤f x z ∧ f x z≤δ)
    (j : J) (z : α j) : 0 ≤ groupedLoad active coord f j z ∧
      groupedLoad active coord f j z ≤ δ := by
  classical
  by_cases he : ∃x∈active,coord x=j
  · obtain ⟨x,hx,hxj⟩ := he
    have heq : groupedLoad active coord f j z = f x (hxj.symm ▸ z) := by
      unfold groupedLoad
      rw [Finset.sum_eq_single x]
      · simp only [dif_pos hxj]
      · intro y hy hyx
        have hyj : coord y ≠ j := by
          intro hyj
          exact hyx (hinj hy hx (hyj.trans hxj.symm))
        simp only [dif_neg hyj]
      · exact fun hn => (hn hx).elim
    rw [heq]
    exact hf x hx _
  · have heq : groupedLoad active coord f j z = 0 := by
      unfold groupedLoad
      apply Finset.sum_eq_zero
      intro x hx
      have hxj : coord x ≠ j := fun h => he ⟨x,hx,h⟩
      simp only [dif_neg hxj]
    rw [heq]
    exact ⟨le_rfl,hδ⟩

lemma groupedLoad_sum {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (active : Finset X) (coord : X → J) {α : J → Type*}
    (f : (x : X) → α (coord x) → ℝ) (ω : ∀j,α j) :
    (∑j,groupedLoad active coord f j (ω j)) = ∑x∈active,f x (ω (coord x)) := by
  classical
  unfold groupedLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

lemma groupedLoad_zero {X J : Type*} [Fintype X] [DecidableEq J]
    (active : Finset X) (coord : X → J) {α : J → Type*}
    (f : (x : X) → α (coord x) → ℝ) (j : J) (hj : j ∉ active.image coord)
    (z : α j) : groupedLoad active coord f j z = 0 := by
  classical
  unfold groupedLoad
  apply Finset.sum_eq_zero
  intro x hx
  have hn : coord x ≠ j := fun he => hj (Finset.mem_image.mpr ⟨x,hx,he⟩)
  simp only [dif_neg hn]

end PacketRouting.CongDil.PRFresh

-- END PRProof/InjectiveLoad.lean

-- BEGIN PRProof/ConditionalDecomposition.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X] [DecidableEq X]
  {α : J → Type*} [∀j,Fintype (α j)] [∀j,Nonempty (α j)]

def revealedContribution (past current : Finset J) (base : ∀j,α j)
    (A : X → (∀j,α j) → Prop) (coord : X → J) (x : X) (z : α (coord x)) : ℝ :=
  conditionalProb (past∪current)
    (replaceCoordinates current (Function.update base (coord x) z) base) (A x)

theorem conditional_prob_single (past current support : Finset J) (base : ∀j,α j)
    (A : (∀j,α j) → Prop) (hA : EventDepends A support) (i : J)
    (hs : current∩support ⊆ {i}) (ω : ∀j,α j) :
    conditionalProb (past∪current) (replaceCoordinates current ω base) A =
      conditionalProb (past∪current)
        (replaceCoordinates current (Function.update base i (ω i)) base) A := by
  classical
  simp_rw [conditionalProb_eq_mean]
  have hf : CoordinateDepends (fun ω => if A ω then (1:ℝ) else 0) support := by
    intro u v huv
    have he := hA u v huv
    simp only [he]
  exact conditional_single_coordinate _ past current support base _ hf i hs ω
    (Function.update base i (ω i)) (by simp)

omit [DecidableEq X] in
theorem conditional_load_decomposition (past current : Finset J) (hdis : Disjoint past current)
    (base : ∀j,α j) (A : X → (∀j,α j) → Prop) (support : X → Finset J)
    (hA : ∀x,EventDepends (A x) (support x)) (coord : X → J)
    (hs : ∀x,current∩support x ⊆ {coord x}) (ω : ∀j,α j) :
    (∑x,conditionalProb (past∪current) (replaceCoordinates current ω base) (A x)) =
      ∑j,groupedLoad (univ.filter (fun x => 0<conditionalProb past base (A x))) coord
        (revealedContribution past current base A coord) j (ω j) := by
  classical
  rw [groupedLoad_sum]
  symm
  calc
    _ = ∑x∈univ.filter (fun x => 0<conditionalProb past base (A x)),
        conditionalProb (past∪current) (replaceCoordinates current ω base) (A x) := by
      apply sum_congr rfl
      intro x _
      exact (conditional_prob_single past current (support x) base (A x) (hA x)
        (coord x) (hs x) ω).symm
    _ = _ := by
      apply sum_subset (filter_subset _ _)
      intro x _ hx
      have hz : conditionalProb past base (A x)=0 := by
        have hn : ¬0<conditionalProb past base (A x) := by simpa using hx
        exact le_antisymm (le_of_not_gt hn) (conditionalProb_nonneg _ _ _)
      exact conditionalProb_zero_refine past current hdis base (A x) hz ω

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/ConditionalDecomposition.lean

-- BEGIN PRProof/RoutingEventData.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

abbrev RoutingEvent {P E : Type*} [Fintype P] (path : P → List E) (h : ℕ) :=
  {g : E // g∈usedEdges path} × Fin (5*2^h+1)

def routingEventKey {P E : Type*} [Fintype P] {path : P → List E} {h : ℕ}
    (i : RoutingEvent path h) : E × ℕ := (i.1.val,i.2.val)

lemma routingEventKey_injective {P E : Type*} [Fintype P] {path : P → List E} {h : ℕ} :
    Function.Injective (@routingEventKey P E _ path h) := by
  intro i j he
  exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

def routeArrival {P E : Type*} [Fintype P] {path : P → List E} {h L H : ℕ}
    (hH : 8≤H) (hend : H ≤ scaleExponent h L) (i : RoutingEvent path h)
    (x : Crossing path) (ω : FlatRoutingAssignment P h L) : Prop :=
  crossingEdge path x=i.1.val ∧
    (routingTimetable path h L H hH hend (fun p j => ω (p,j))).time x.1 x.2=i.2.val

def routingPast {P : Type*} [Fintype P] {h L : ℕ} (n : ℕ) : Finset (P × RoutingCoordinate h L) :=
  FiniteLaw.beforeLevel (fun j => routingLevel j.2) n

def routingCurrent {P : Type*} [Fintype P] {h L : ℕ} (n : ℕ) : Finset (P × RoutingCoordinate h L) :=
  FiniteLaw.atLevel (fun j => routingLevel j.2) n

noncomputable def routingActive {P E : Type*} [Fintype P] [DecidableEq P] {path : P → List E} {h L H : ℕ}
    (hH : 8≤H) (hend : H ≤ scaleExponent h L) (n : ℕ)
    (base : FlatRoutingAssignment P h L) (i : RoutingEvent path h) : Finset (Crossing path) := by
  classical
  exact univ.filter (fun x => 0<FiniteLaw.conditionalProb (routingPast n) base (routeArrival hH hend i x))

def crossingCoordinate {P E : Type*} {path : P → List E} {h L : ℕ}
    (hd : DilationLE path (2^h)) (n : ℕ) (hn : n≤L) (x : Crossing path) :
    P × RoutingCoordinate h L :=
  (x.1,selectedAtLevel ((Nat.succ_le_of_lt x.2.isLt).trans (hd x.1)) n hn)

lemma routeArrival_depends {P E : Type*} [Fintype P] [DecidableEq P] {path : P → List E}
    {h L H : ℕ} (hH : 8≤H) (hend : H ≤ scaleExponent h L) (hd : DilationLE path (2^h))
    (i : RoutingEvent path h) (x : Crossing path) :
    FiniteLaw.EventDepends (routeArrival hH hend i x) (arrivalSupport hd x) := by
  intro u v huv
  exact and_congr_right (fun _ => arrival_depends hH hend hd x i.2.val u v huv)

lemma routingActive_edge {P E : Type*} [Fintype P] [DecidableEq P] {path : P → List E} {h L H : ℕ}
    (hH : 8≤H) (hend : H ≤ scaleExponent h L) (n : ℕ)
    (base : FlatRoutingAssignment P h L) (i : RoutingEvent path h) {x : Crossing path}
    (hx : x∈routingActive hH hend n base i) : crossingEdge path x=i.1.val := by
  classical
  have hp := (mem_filter.mp hx).2
  obtain ⟨ω,hω⟩ := FiniteLaw.exists_of_prob_pos _ hp
  exact hω.1

lemma crossingCoordinate_inj_active {P E : Type*} [Fintype P] [DecidableEq P] {path : P → List E}
    {h L H n : ℕ} (hH : 8≤H) (hend : H ≤ scaleExponent h L)
    (hd : DilationLE path (2^h)) (hn : n≤L) (hnodup : ∀p,(path p).Nodup)
    (base : FlatRoutingAssignment P h L) (i : RoutingEvent path h) :
    Set.InjOn (crossingCoordinate hd n hn) (routingActive hH hend n base i) := by
  intro x hx y hy he
  exact crossing_packet_injective hnodup i.1.val
    (routingActive_edge hH hend n base i hx) (routingActive_edge hH hend n base i hy)
    (congrArg Prod.fst he)

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingEventData.lean

-- BEGIN PRProof/SupportCard.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

lemma support_alphabet_card {J : Type*} [DecidableEq J] (S : Finset J)
    (width : J → ℕ) (level : J → ℕ) (W : ℕ → ℕ) (T : Finset ℕ)
    (hinj : Set.InjOn level S) (hwidth : ∀j∈S,width j=W (level j))
    (hrange : ∀j∈S,level j∈T) (hW : ∀i∈T,1≤W i) :
    Fintype.card (∀j : {j // j∈S},Fin (width j)) ≤ ∏i∈T,W i := by
  classical
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [←prod_subtype S (fun _ => Iff.rfl) width]
  calc
    _ = ∏j∈S,W (level j) := prod_congr rfl hwidth
    _ = ∏i∈S.image level,W i := (prod_image hinj).symm
    _ ≤ _ := prod_le_prod_of_subset_of_one_le
      (by intro i hi; obtain ⟨j,hj,rfl⟩ := mem_image.mp hi; exact hrange j hj)
      (fun _ _ => Nat.zero_le _) (fun i hi _ => hW i hi)

end PacketRouting.CongDil.PRFresh

-- END PRProof/SupportCard.lean

-- BEGIN PRProof/TailBudgets.lean

namespace PacketRouting.CongDil.PRFresh

lemma sum_descending_head_nat (f : ℕ → ℕ) (N : ℕ)
    (h : ∀ i < N, 2 * f (i + 1) ≤ f i) :
    (∑ i ∈ Finset.range N, f i) ≤ 2 * f 0 := by
  have hd := sum_descending_nat f N h
  have hs := sum_shift_nat f N
  omega

lemma sum_exponent_tail (h start N : ℕ) :
    (∑ i ∈ Finset.range N, scaleExponent h (start + i)) ≤ 2 * scaleExponent h start := by
  simpa using sum_descending_head_nat (fun i => scaleExponent h (start + i)) N
    (fun i _ => by simpa [Nat.add_assoc] using twice_child_exponent_le h (start + i))

lemma sum_alphabet_exponents (h start N : ℕ) :
    (∑ i ∈ Finset.range N, scaleExponent h (start + i) / 4) ≤ scaleExponent h start / 2 := by
  have hp := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range N) =>
    Nat.mul_div_le (scaleExponent h (start + i)) 4)
  rw [← Finset.mul_sum] at hp
  have he := sum_exponent_tail h start N
  omega

lemma prod_delay_tail (h start N : ℕ) :
    (∏ i ∈ Finset.range N, delayScale h (start + i)) ≤ 2 ^ (scaleExponent h start / 2) := by
  unfold delayScale
  rw [Finset.prod_pow_eq_pow_sum]
  exact Nat.pow_le_pow_right (by omega) (sum_alphabet_exponents h start N)

lemma prod_delay_tail_le_block (h start N : ℕ) :
    (∏ i ∈ Finset.range N, delayScale h (start + i)) ≤ blockScale h start := by
  exact (prod_delay_tail h start N).trans
    (Nat.pow_le_pow_right (by omega) (Nat.div_le_self _ _))

lemma sum_delay_tail {h L H start N : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hN : start + N ≤ L + 1) :
    (∑ i ∈ Finset.range N, delayScale h (start + i)) ≤ 2 * delayScale h start := by
  have hex (i : ℕ) (hi : i < N) : 8 ≤ scaleExponent h (start + i) :=
    hH.trans (hend.trans (scaleExponent_antitone h (by omega)))
  simpa using sum_descending_head_nat (fun i => delayScale h (start + i)) N
    (fun i hi => by simpa [Nat.add_assoc] using delayScale_half (hex i hi))

lemma final_two_alphabets {h L H : ℕ} (hL : 2 ≤ L)
    (hend : scaleExponent h L < 2 * H) :
    delayScale h (L - 1) * delayScale h L ≤ 2 ^ (2 * H) := by
  have he : scaleExponent h L = scaleExponent h (L - 1) / 2 := by
    have hidx : L = (L - 1) + 1 := by omega
    conv_lhs => rw [hidx]
    exact scaleExponent_succ h (L - 1)
  unfold delayScale
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by omega)
  omega

end PacketRouting.CongDil.PRFresh

-- END PRProof/TailBudgets.lean

-- BEGIN PRProof/RemainingAlphabet.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

lemma routingSelected_level_le {h L q : ℕ} (hq : q≤2^h)
    {j : RoutingCoordinate h L} (hj : j∈routingSelected (L := L) hq) : routingLevel j≤L := by
  simp only [routingSelected,mem_insert,mem_image,mem_univ,true_and] at hj
  rcases hj with rfl | ⟨l,rfl⟩
  · exact Nat.zero_le _
  · change l.val+1≤L
    exact Nat.succ_le_of_lt l.isLt

lemma remaining_alphabet_card {P E : Type*} [Fintype P] [DecidableEq P]
    {path : P → List E} {h L n : ℕ} (hd : DilationLE path (2^h)) (hn : 1≤n)
    (x : Crossing path) :
    Fintype.card (∀j : {j : P × RoutingCoordinate h L //
      j∈arrivalSupport hd x \ FiniteLaw.beforeLevel (fun j => routingLevel j.2) n},
      Fin (routingWidth h L j.1.2)) ≤ blockScale h n := by
  classical
  let S : Finset (P × RoutingCoordinate h L) := arrivalSupport hd x \ FiniteLaw.beforeLevel (fun j => routingLevel j.2) n
  have hm {j : P × RoutingCoordinate h L} (hj : j∈S) :
      j.1=x.1 ∧ j.2∈routingSelected (L := L)
        (le_trans (Nat.succ_le_of_lt x.2.isLt) (hd x.1)) ∧ n≤routingLevel j.2 := by
    have hja := (mem_sdiff.mp hj).1
    obtain ⟨a,ha,he⟩ := mem_image.mp hja
    have hlev : n≤routingLevel j.2 := by
      have hnot := (mem_sdiff.mp hj).2
      simpa only [FiniteLaw.beforeLevel,mem_filter,mem_univ,true_and,not_lt] using hnot
    exact ⟨by rw [←he],by simpa only [←he] using ha,hlev⟩
  have hb := support_alphabet_card S (fun j => routingWidth h L j.2)
    (fun j => routingLevel j.2) (delayScale h) (Ico n (L+1))
    (by
      intro a ha b hb he
      apply Prod.ext
      · exact (hm ha).1.trans (hm hb).1.symm
      · exact routingSelected_level_injective _ (hm ha).2.1 (hm hb).2.1 he)
    (by
      intro j hj
      cases he : j.2 with
      | none => have hh := (hm hj).2.2; simp only [he,routingLevel] at hh; omega
      | some a => rfl)
    (by
      intro j hj
      exact mem_Ico.mpr ⟨(hm hj).2.2,Nat.lt_succ_of_le (routingSelected_level_le _ (hm hj).2.1)⟩)
    (fun i _ => Nat.succ_le_of_lt (delayScale_pos h i))
  apply hb.trans
  rw [Finset.prod_Ico_eq_prod_range]
  simpa only [Nat.add_comm] using prod_delay_tail_le_block h n (L+1-n)

end PacketRouting.CongDil.PRFresh

-- END PRProof/RemainingAlphabet.lean

-- BEGIN PRProof/ConditionalCounting.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
  {α : J → Type*} [∀j,Fintype (α j)] [∀j,Nonempty (α j)]

theorem conditional_positive_count (past : Finset J) (base : ∀j,α j)
    (A : I → (∀j,α j) → Prop) (support : I → Finset J)
    (hA : ∀i,EventDepends (A i) (support i)) {m : ℕ} (hm : 0 < m) {γ : ℝ}
    (hc : ∀i,Fintype.card (∀j : {j // j ∈ support i \ past},α j) ≤ m)
    (hmean : (∑i,conditionalProb past base (A i))≤γ) :
    ((univ.filter (fun i => 0<conditionalProb past base (A i))).card:ℝ) ≤ γ*m := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hp (i : I) (hi : 0<conditionalProb past base (A i)) :
      (m:ℝ)⁻¹ ≤ conditionalProb past base (A i) := by
    have ha := conditionalProb_atom past (support i) base (A i) (hA i) hi
    apply le_trans _ ha
    apply inv_anti₀
    · exact_mod_cast Fintype.card_pos (α := ∀j : {j // j ∈ support i \ past},α j)
    · exact_mod_cast hc i
  have hs := positive_support_card (fun i => conditionalProb past base (A i))
    (inv_pos.mpr hmR) (fun i => conditionalProb_nonneg _ _ _) hp hmean
  have hh := mul_le_mul_of_nonneg_right hs hmR.le
  simpa only [mul_assoc,inv_mul_cancel₀ hmR.ne',mul_one] using hh

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/ConditionalCounting.lean

-- BEGIN PRProof/RoutingActiveSize.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

lemma routingActive_card {P E : Type*} [Fintype P] [DecidableEq P]
    {path : P → List E} {h L H n : ℕ} (hH : 8≤H) (hend : H ≤ scaleExponent h L)
    (hd : DilationLE path (2^h)) (hnodup : ∀p,(path p).Nodup)
    (hc : CongestionLE path (2^h)) (base : FlatRoutingAssignment P h L)
    (i : RoutingEvent path h) {γ : ℝ} (hγ : γ≤2)
    (hmean : (∑x,FiniteLaw.conditionalProb (routingPast n) base (routeArrival hH hend i x))≤γ) :
    (routingActive hH hend n base i).card ≤ 2*blockScale h n := by
  classical
  by_cases hn : n=0
  · subst n
    have hs : routingActive hH hend 0 base i ⊆ univ.filter
        (fun x : Crossing path => crossingEdge path x=i.1.val) := by
      intro x hx
      exact mem_filter.mpr ⟨mem_univ _,routingActive_edge hH hend 0 base i hx⟩
    have hh := (card_le_card hs).trans (edgeCrossings_card hnodup hc i.1.val)
    simp only [blockScale,scaleExponent_zero]
    omega
  · have hn1 : 1≤n := by omega
    have hh : ((routingActive hH hend n base i).card:ℝ) ≤ γ*(blockScale h n:ℝ) := by
      unfold routingActive
      exact FiniteLaw.conditional_positive_count
        (α := fun j : P × RoutingCoordinate h L => Fin (routingWidth h L j.2))
        (routingPast n) base (routeArrival hH hend i) (arrivalSupport (L := L) hd)
        (routeArrival_depends hH hend hd i) (blockScale_pos h n)
        (fun x => remaining_alphabet_card (L := L) hd hn1 x) hmean
    have hm : (0:ℝ)≤blockScale h n := by positivity
    have hfinal : ((routingActive hH hend n base i).card:ℝ)≤2*(blockScale h n:ℝ) :=
      hh.trans (mul_le_mul_of_nonneg_right hγ hm)
    exact_mod_cast hfinal

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingActiveSize.lean

-- BEGIN PRProof/MidpointSeparation.lean

namespace PacketRouting.CongDil.PRFresh

lemma halfGrid_separated {r : ℤ} (hr : 0 < r) (i j : ℤ) :
    r ≤ |(2 * r * i) - (2 * r * j + r)| := by
  by_cases h : i ≤ j
  · have hs : 2 * r * i - (2 * r * j + r) ≤ -r := by nlinarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hs : j + 1 ≤ i := by omega
    have hp : r ≤ 2 * r * i - (2 * r * j + r) := by nlinarith
    rw [abs_of_nonneg (by linarith)]
    exact hp

lemma not_near_both_halfGrids {r q : ℤ} (hr : 0 < r) (i j : ℤ)
    (h1 : 2 * |q - 2 * r * i| < r) :
    r ≤ 2 * |q - (2 * r * j + r)| := by
  have hsep := halfGrid_separated hr i j
  have htri : |2 * r * i - (2 * r * j + r)| ≤
      |q - 2 * r * i| + |q - (2 * r * j + r)| := by
    calc
      |2 * r * i - (2 * r * j + r)| =
          |(2 * r * i - q) + (q - (2 * r * j + r))| := by congr 1; ring
      _ ≤ |2 * r * i - q| + |q - (2 * r * j + r)| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (2 * r * i) q]
  omega

lemma either_far_from_halfGrids {r q : ℤ} (hr : 0 < r) :
    (∀ i : ℤ, r ≤ 2 * |q - 2 * r * i|) ∨
      (∀ j : ℤ, r ≤ 2 * |q - (2 * r * j + r)|) := by
  by_cases h : ∀ i : ℤ, r ≤ 2 * |q - 2 * r * i|
  · exact Or.inl h
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Or.inr (fun j => not_near_both_halfGrids hr i j hi)

end PacketRouting.CongDil.PRFresh

-- END PRProof/MidpointSeparation.lean

-- BEGIN PRProof/TwoScaleInterior.lean

namespace PacketRouting.CongDil.PRFresh

lemma two_scale_interior {m n a b q : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hme : m = 2 * (m / 2)) (hne : n = 2 * (n / 2)) (hdiv : n ∣ m / 2)
    (ha : 4 * a ≤ n) (hb : 4 * b ≤ n) :
    (centeredStart m (centeredIndex m q) + a ≤ (q : ℤ) ∧
      (q : ℤ) ≤ centeredStart m (centeredIndex m q) + m - a) ∨
    (centeredStart n (centeredIndex n q) + b ≤ (q : ℤ) ∧
      (q : ℤ) ≤ centeredStart n (centeredIndex n q) + n - b) := by
  have hr : (0 : ℤ) < (n / 2 : ℕ) := by omega
  obtain ⟨c, hc⟩ := hdiv
  have hc' : ((m / 2 : ℕ) : ℤ) = (n : ℤ) * c := by exact_mod_cast hc
  have hm' : (m : ℤ) = 2 * (m / 2 : ℕ) := by exact_mod_cast hme
  have hn' : (n : ℤ) = 2 * (n / 2 : ℕ) := by exact_mod_cast hne
  have ham : (4 : ℤ) * a ≤ n := by exact_mod_cast ha
  have hbm : (4 : ℤ) * b ≤ n := by exact_mod_cast hb
  have hqi := centeredIndex_bounds (q := q) hm
  have hqj := centeredIndex_bounds (q := q) hn
  rcases either_far_from_halfGrids (q := (q : ℤ)) hr with h | h
  · left
    have hl := h ((2 : ℤ) * c * centeredIndex m q - c)
    have hu := h ((2 : ℤ) * c * centeredIndex m q + c)
    have hel : 2 * (n / 2 : ℕ) * ((2 : ℤ) * c * centeredIndex m q - c) =
        centeredStart m (centeredIndex m q) := by
          unfold centeredStart
          rw [hm', hc', hn']
          ring
    have heu : 2 * (n / 2 : ℕ) * ((2 : ℤ) * c * centeredIndex m q + c) =
        centeredStart m (centeredIndex m q) + m := by
          unfold centeredStart
          rw [hm', hc', hn']
          ring
    rw [hel, abs_of_nonneg (by omega)] at hl
    rw [heu, abs_of_nonpos (by omega)] at hu
    constructor <;> omega
  · right
    have hl := h ((centeredIndex n q : ℤ) - 1)
    have hu := h (centeredIndex n q)
    have hel : 2 * (n / 2 : ℕ) * ((centeredIndex n q : ℤ) - 1) + (n / 2 : ℕ) =
        centeredStart n (centeredIndex n q) := by
          unfold centeredStart
          rw [hn']
          ring
    have heu : 2 * (n / 2 : ℕ) * (centeredIndex n q : ℤ) + (n / 2 : ℕ) =
        centeredStart n (centeredIndex n q) + n := by
          unfold centeredStart
          rw [hn']
          ring
    rw [hel, abs_of_nonneg (by omega)] at hl
    rw [heu, abs_of_nonpos (by omega)] at hu
    constructor <;> omega

end PacketRouting.CongDil.PRFresh

-- END PRProof/TwoScaleInterior.lean

-- BEGIN PRProof/InteriorMargins.lean

namespace PacketRouting.CongDil.PRFresh

lemma hierarchyMargin_le_pow (h L l : ℕ) :
    hierarchyMargin h L l ≤ 2 ^ ((L - l + 1) + scaleExponent h l / 4 + 1) := by
  have hw := delayScale_pos h l
  unfold hierarchyMargin slotPeriod delayScale at *
  calc
    2 ^ (L - l + 1) * (2 ^ (scaleExponent h l / 4) + 1) ≤
        2 ^ (L - l + 1) * (2 * 2 ^ (scaleExponent h l / 4)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by rw [pow_add, pow_add]; ring

lemma four_margin_le_child {h L H l : ℕ} (hH : 64 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) :
    4 * hierarchyMargin h L l ≤ blockScale h (l + 1) := by
  have he := slot_exponent_margin (show 8 ≤ H by omega) hend hl
  have heH : 64 ≤ scaleExponent h l := hH.trans (hend.trans (scaleExponent_antitone h hl))
  have hb := Nat.mul_le_mul_left 4 (hierarchyMargin_le_pow h L l)
  calc
    4 * hierarchyMargin h L l ≤ 4 * 2 ^ ((L - l + 1) + scaleExponent h l / 4 + 1) := hb
    _ = 2 ^ ((L - l + 1) + scaleExponent h l / 4 + 3) := by
      have hi : (L - l + 1) + scaleExponent h l / 4 + 3 =
          ((L - l + 1) + scaleExponent h l / 4 + 1) + 2 := by omega
      rw [hi, pow_add]
      ring
    _ ≤ blockScale h (l + 1) := by
      unfold blockScale
      rw [scaleExponent_succ]
      exact Nat.pow_le_pow_right (by omega) (by omega)

lemma blockScale_even {h l : ℕ} (he : 1 ≤ scaleExponent h l) :
    blockScale h l = 2 * (blockScale h l / 2) := by
  have hd : 2 ∣ blockScale h l := by
    unfold blockScale
    simpa only [pow_one] using (pow_dvd_pow (a := 2) he)
  exact (Nat.mul_div_cancel' hd).symm

lemma child_dvd_half {h l : ℕ} (he : 2 ≤ scaleExponent h l) :
    blockScale h (l + 1) ∣ blockScale h l / 2 := by
  have hdiv : blockScale h l / 2 = 2 ^ (scaleExponent h l - 1) := by
    simpa [blockScale] using (Nat.pow_div (x := 2) (m := scaleExponent h l) (n := 1) (by omega) (by omega))
  rw [hdiv]
  unfold blockScale
  rw [scaleExponent_succ]
  exact pow_dvd_pow 2 (by omega)

lemma hierarchy_two_interiors {h L H l q : ℕ} (hH : 64 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l + 2 ≤ L) :
    (centeredStart (blockScale h (l + 1)) (centeredIndex (blockScale h (l + 1)) q) +
        hierarchyMargin h L (l + 1) ≤ (q : ℤ) ∧
      (q : ℤ) ≤ centeredStart (blockScale h (l + 1)) (centeredIndex (blockScale h (l + 1)) q) +
        blockScale h (l + 1) - hierarchyMargin h L (l + 1)) ∨
    (centeredStart (blockScale h (l + 2)) (centeredIndex (blockScale h (l + 2)) q) +
        hierarchyMargin h L (l + 2) ≤ (q : ℤ) ∧
      (q : ℤ) ≤ centeredStart (blockScale h (l + 2)) (centeredIndex (blockScale h (l + 2)) q) +
        blockScale h (l + 2) - hierarchyMargin h L (l + 2)) := by
  have he1 : 64 ≤ scaleExponent h (l + 1) := hH.trans (hend.trans (scaleExponent_antitone h (by omega)))
  have he2 : 64 ≤ scaleExponent h (l + 2) := hH.trans (hend.trans (scaleExponent_antitone h hl))
  apply two_scale_interior (blockScale_pos h (l + 1)) (blockScale_pos h (l + 2))
    (blockScale_even (by omega)) (blockScale_even (by omega))
  · simpa [Nat.add_assoc] using child_dvd_half (show 2 ≤ scaleExponent h (l + 1) by omega)
  · simpa [Nat.add_assoc] using four_margin_le_child hH hend (show l + 1 ≤ L by omega)
  · exact (four_margin_le_child hH hend hl).trans
      (Nat.pow_le_pow_right (by omega) (scaleExponent_antitone h (Nat.le_succ (l + 2))))

end PacketRouting.CongDil.PRFresh

-- END PRProof/InteriorMargins.lean

-- BEGIN PRProof/MiddleInjectivity.lean

namespace PacketRouting.CongDil.PRFresh

lemma delay_sum_update_middle {J : Type*} [Fintype J] [DecidableEq J] {W : J → ℕ}
    (B : (j : J) → WaitBlock (W j)) (x : J → ℕ) (i : J) (q : ℤ)
    (hm : ∀ v ≤ W i, (B i).delay v q = v) {v : ℕ} (hv : v ≤ W i) :
    (∑ j, (B j).delay (Function.update x i v j) q) =
      v + ∑ j ∈ Finset.univ \ {i}, (B j).delay (x j) q := by
  have he : (fun j => (B j).delay (Function.update x i v j) q) =
      Function.update (fun j => (B j).delay (x j) q) i v := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, hm v hv]
    · simp only [Function.update_of_ne hj]
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ i)]

lemma delay_sum_middle_injective {J : Type*} [Fintype J] [DecidableEq J] {W : J → ℕ}
    (B : (j : J) → WaitBlock (W j)) (x : J → ℕ) (i : J) (q : ℤ)
    (hm : ∀ v ≤ W i, (B i).delay v q = v) (base : ℕ) :
    Function.Injective (fun v : Fin (W i) => base + ∑ j,
      (B j).delay (Function.update x i (v.val + 1) j) q) := by
  intro v w he
  change base + (∑ j, (B j).delay (Function.update x i (v.val + 1) j) q) =
    base + (∑ j, (B j).delay (Function.update x i (w.val + 1) j) q) at he
  rw [delay_sum_update_middle B x i q hm (by have := v.isLt; omega),
    delay_sum_update_middle B x i q hm (by have := w.isLt; omega)] at he
  apply Fin.ext
  omega

lemma exists_selected_middle {h L H l q : ℕ} (hH : 64 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l + 2 ≤ L) (hq : q ≤ 2 ^ h) :
    ∃ j : HierarchyIndex h L,
      (j.1.val + 1 = l + 1 ∨ j.1.val + 1 = l + 2) ∧
      (∀ v ≤ hierarchyWidth h L j, (hierarchyWait h L H (by omega) hend j).delay v q = v) := by
  have h8 : 8 ≤ H := by omega
  rcases hierarchy_two_interiors hH hend hl (q := q) with hmid | hmid
  · let a : Fin L := ⟨l, by omega⟩
    refine ⟨selectedHierarchyIndex h L q hq a, Or.inl rfl, ?_⟩
    intro v hv
    exact hierarchyBlock_middle h8 hend (by omega) hv hmid.1 hmid.2
  · let a : Fin L := ⟨l + 1, by omega⟩
    refine ⟨selectedHierarchyIndex h L q hq a, Or.inr rfl, ?_⟩
    intro v hv
    exact hierarchyBlock_middle h8 hend (by omega) hv hmid.1 hmid.2

end PacketRouting.CongDil.PRFresh

-- END PRProof/MiddleInjectivity.lean

-- BEGIN PRProof/RoutingSmoothing.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

lemma routing_middle_fiber {P E : Type*} [DecidableEq P] {path : P → List E}
    {h L H : ℕ} (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (p : P) (k : Fin (path p).length) (i : HierarchyIndex h L)
    (hm : ∀v≤hierarchyWidth h L i,
      (hierarchyWait h L H hH hend i).delay v (k.val+1:ℕ)=v)
    (u v : FlatRoutingAssignment P h L)
    (huv : ∀j,j≠(p,some i) → u j=v j)
    (he : (routingTimetable path h L H hH hend (fun p j => u (p,j))).time p k =
      (routingTimetable path h L H hH hend (fun p j => v (p,j))).time p k) : u=v := by
  classical
  have hr : u (p,none)=v (p,none) := huv _ (by simp)
  have hs : (∑j∈univ.erase i,(hierarchyWait h L H hH hend j).delay
      ((u (p,some j)).val+1) (k.val+1:ℕ)) =
      ∑j∈univ.erase i,(hierarchyWait h L H hH hend j).delay
      ((v (p,some j)).val+1) (k.val+1:ℕ) := by
    apply sum_congr rfl
    intro j hj
    have hjn : j≠i := (mem_erase.mp hj).1
    rw [huv (p,some j) (by simpa using hjn)]
  have hu := sum_erase_add (s := univ)
    (fun j => (hierarchyWait h L H hH hend j).delay ((u (p,some j)).val+1) (k.val+1:ℕ))
    (mem_univ i)
  have hv := sum_erase_add (s := univ)
    (fun j => (hierarchyWait h L H hH hend j).delay ((v (p,some j)).val+1) (k.val+1:ℕ))
    (mem_univ i)
  simp only [routingTimetable,familyTimetable] at he
  rw [←hu,←hv,hm _ (Nat.succ_le_of_lt (u (p,some i)).isLt),
    hm _ (Nat.succ_le_of_lt (v (p,some i)).isLt),hr,hs] at he
  have hi : u (p,some i)=v (p,some i) := Fin.ext (by omega)
  funext j
  by_cases hj : j=(p,some i)
  · subst j; exact hi
  · exact huv j hj

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingSmoothing.lean

-- BEGIN PRProof/RealScaleBounds.lean

namespace PacketRouting.CongDil.PRFresh

lemma blockScale_rpow (h l : ℕ) (r : ℝ) :
    (blockScale h l : ℝ) ^ r = (2 : ℝ) ^ ((scaleExponent h l : ℝ) * r) := by
  simp only [blockScale, Nat.cast_pow, Nat.cast_ofNat]
  exact (Real.rpow_natCast_mul (by norm_num) (scaleExponent h l) r).symm

lemma delayScale_antitone (h : ℕ) : Antitone (delayScale h) := by
  intro i j hij
  exact Nat.pow_le_pow_right (by omega) (Nat.div_le_div_right (scaleExponent_antitone h hij))

lemma two_step_delay_lower (h l : ℕ) :
    (blockScale h l : ℝ) ^ (1 / 16 : ℝ) ≤ 2 * (delayScale h (l + 2) : ℝ) := by
  have he : scaleExponent h (l + 2) / 4 = scaleExponent h l / 16 := by
    rw [show l + 2 = (l + 1) + 1 by omega, scaleExponent_succ, scaleExponent_succ,
      Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  have hf : scaleExponent h l ≤ 16 * (scaleExponent h l / 16 + 1) := by omega
  have hf' : (scaleExponent h l : ℝ) ≤ 16 * ((scaleExponent h l / 16 : ℕ) + 1 : ℝ) := by exact_mod_cast hf
  rw [blockScale_rpow]
  calc
    (2 : ℝ) ^ ((scaleExponent h l : ℝ) * (1 / 16 : ℝ)) ≤
        (2 : ℝ) ^ ((scaleExponent h l / 16 : ℕ) + 1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2 * (delayScale h (l + 2) : ℝ) := by
      simp only [delayScale, he, Nat.cast_pow, Nat.cast_ofNat]
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one]
      ring

lemma future_delay_lower {h l u : ℕ} (hu : u = l + 1 ∨ u = l + 2) :
    (blockScale h l : ℝ) ^ (1 / 16 : ℝ) ≤ 2 * (delayScale h u : ℝ) := by
  rcases hu with rfl | rfl
  · have hm : (delayScale h (l + 2) : ℝ) ≤ delayScale h (l + 1) := by
      exact_mod_cast delayScale_antitone h (show l + 1 ≤ l + 2 by omega)
    exact (two_step_delay_lower h l).trans (by linarith)
  · exact two_step_delay_lower h l

noncomputable def scaleError (h l : ℕ) : ℝ := (blockScale h l : ℝ) ^ (-1 / 64 : ℝ)

lemma scaleError_pos (h l : ℕ) : 0 < scaleError h l := by
  apply Real.rpow_pos_of_pos
  exact_mod_cast blockScale_pos h l

lemma scaleError_le_one (h l : ℕ) : scaleError h l ≤ 1 := by
  rw [scaleError, blockScale_rpow]
  have he : (scaleExponent h l : ℝ) * (-1 / 64 : ℝ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by norm_num)
  simpa using Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) he

lemma scaleError_double {h l : ℕ} (hh : 128 ≤ scaleExponent h l) :
    2 * scaleError h l ≤ scaleError h (l + 1) := by
  have hd : scaleExponent h l / 2 + 64 ≤ scaleExponent h l := by omega
  have hd' : ((scaleExponent h l / 2 : ℕ) : ℝ) + 64 ≤ scaleExponent h l := by exact_mod_cast hd
  rw [scaleError, scaleError, blockScale_rpow, blockScale_rpow, scaleExponent_succ]
  calc
    2 * (2 : ℝ) ^ ((scaleExponent h l : ℝ) * (-1 / 64 : ℝ)) =
        (2 : ℝ) ^ (1 + (scaleExponent h l : ℝ) * (-1 / 64 : ℝ)) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]
    _ ≤ (2 : ℝ) ^ (((scaleExponent h l / 2 : ℕ) : ℝ) * (-1 / 64 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

lemma scaleError_sum_le_one {h L H : ℕ} (hH : 128 ≤ H)
    (hend : H ≤ scaleExponent h L) : (∑ l ∈ Finset.range L, scaleError h l) ≤ 1 := by
  have hb := sum_ascending_real (scaleError h) L (fun i hi => scaleError_double
    (hH.trans (hend.trans (scaleExponent_antitone h hi.le))))
  have hp := scaleError_pos h 0
  have hl := scaleError_le_one h L
  linarith

end PacketRouting.CongDil.PRFresh

-- END PRProof/RealScaleBounds.lean

-- BEGIN PRProof/ConditionalSmoothing.lean
noncomputable section
namespace PacketRouting.CongDil.PRFresh

lemma conditional_time_bound {P E : Type*} [Fintype P] [DecidableEq P]
    {path : P → List E} {h L H n : ℕ} (hH : 64≤H)
    (hend : H ≤ scaleExponent h L) (hn : n+2≤L)
    (hd : DilationLE path (2^h)) (base : FlatRoutingAssignment P h L)
    (p : P) (k : Fin (path p).length) (t : ℕ) :
    FiniteLaw.conditionalProb
      (FiniteLaw.beforeLevel (fun j : P × RoutingCoordinate h L => routingLevel j.2) (n+1))
      base (fun ω : FlatRoutingAssignment P h L =>
        (routingTimetable path h L H (by omega) hend (fun p j => ω (p,j))).time p k=t) ≤
      2*(blockScale h n : ℝ)^(-(1/16:ℝ)) := by
  classical
  have hq : k.val+1≤2^h := (Nat.succ_le_of_lt k.isLt).trans (hd p)
  obtain ⟨j,hj,hm⟩ := exists_selected_middle hH hend hn hq
  have hnot : (p,some j) ∉ FiniteLaw.beforeLevel
      (fun j : P × RoutingCoordinate h L => routingLevel j.2) (n+1) := by
    intro hc
    have hh := (Finset.mem_filter.mp hc).2
    change j.1.val+1<n+1 at hh
    rcases hj with hj | hj <;> omega
  have hb := FiniteLaw.conditionalProb_fiber
    (FiniteLaw.beforeLevel (fun j : P × RoutingCoordinate h L => routingLevel j.2) (n+1))
    base (fun ω : FlatRoutingAssignment P h L =>
      (routingTimetable path h L H (by omega) hend (fun p j => ω (p,j))).time p k)
    (p,some j) hnot t (routing_middle_fiber (by omega) hend p k j hm)
  have hcard : Fintype.card (Fin (routingWidth h L (p,some j).2)) = hierarchyWidth h L j := Fintype.card_fin _
  rw [hcard] at hb
  apply hb.trans
  have hw : (0:ℝ)<hierarchyWidth h L j := by exact_mod_cast delayScale_pos h (j.1.val+1)
  have hm0 : (0:ℝ)<blockScale h n := by exact_mod_cast blockScale_pos h n
  have hp : (0:ℝ)<(blockScale h n : ℝ)^(1/16:ℝ) := Real.rpow_pos_of_pos hm0 _
  have hl := future_delay_lower (h := h) hj
  change (blockScale h n : ℝ)^(1/16:ℝ) ≤ 2*(hierarchyWidth h L j:ℝ) at hl
  rw [Real.rpow_neg hm0.le]
  have hdv : 1/(hierarchyWidth h L j:ℝ) ≤ 2/(blockScale h n:ℝ)^(1/16:ℝ) :=
    (div_le_div_iff₀ hw hp).mpr (by simpa using hl)
  simpa only [one_div,div_eq_mul_inv,one_mul] using hdv

end PacketRouting.CongDil.PRFresh

-- END PRProof/ConditionalSmoothing.lean

-- BEGIN PRProof/EventRefinement.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J X I : Type*} [Fintype J] [DecidableEq J] [Fintype X] [DecidableEq X]
  [Fintype I] [DecidableEq I] {α : J → Type*} [∀j,Fintype (α j)] [∀j,Nonempty (α j)]

theorem refine_events (past current : Finset J) (hdis : Disjoint past current)
    (base : ∀j,α j) (A : I → X → (∀j,α j) → Prop) (support : I → X → Finset J)
    (hA : ∀i x,EventDepends (A i x) (support i x)) (coord : I → X → J)
    (hs : ∀i x,current∩support i x ⊆ {coord i x})
    (active : I → Finset X) (hactive : ∀i,active i=univ.filter (fun x => 0<conditionalProb past base (A i x)))
    (hinj : ∀i,Set.InjOn (coord i) (active i)) (a b : ℕ) {δ γ η : ℝ}
    (hδ : 0<δ) (hγ : 1≤γ) (hη : 0<η) (hη1 : η≤1)
    (hbound : ∀i x ω,conditionalProb (past∪current) (replaceCoordinates current ω base) (A i x)≤δ)
    (hmean : ∀i,(∑x,conditionalProb past base (A i x))≤γ)
    (hsize : ∀i,(active i).card≤a)
    (hocc : ∀j,(univ.filter (fun i => j∈(active i).image (coord i))).card≤b)
    (hsmall : 4*Real.exp (-(η^2)/(4*δ*γ))*((a*b:ℕ)+1)≤1) :
    ∃ν : ∀j,α j, (∀j∈past,ν j=base j) ∧
      ∀i,(∑x,conditionalProb (past∪current) ν (A i x))≤γ+η := by
  classical
  let load (i : I) (ω : ∀j,α j) : ℝ := ∑x,if A i x ω then 1 else 0
  let Z (i : I) := groupedLoad (active i) (coord i)
    (revealedContribution past current base (A i) (coord i))
  have hload (S : Finset J) (ν : ∀j,α j) (i : I) :
      conditionalMean (fun j => uniform (α j)) S ν (load i)=∑x,conditionalProb S ν (A i x) := by
    unfold load
    rw [conditionalMean_sum]
    apply sum_congr rfl
    intro x _
    exact (conditionalProb_eq_mean S ν (A i x)).symm
  obtain ⟨ν,hν,hv⟩ := refine_conditioned_load (fun j => uniform (α j)) past current hdis base load Z
    (fun i => (active i).image (coord i)) a b hδ hγ hη hη1
    (by
      intro i ω
      rw [hload]
      dsimp only [Z]
      rw [hactive]
      exact conditional_load_decomposition past current hdis base (A i) (support i) (hA i) (coord i) (hs i) ω)
    (by
      intro i j z
      exact groupedLoad_bounds (active i) (coord i) _ hδ.le (hinj i)
        (fun x _ z => ⟨conditionalProb_nonneg _ _ _,hbound i x _⟩) j z)
    (fun i j hj z => groupedLoad_zero _ _ _ j hj z)
    (fun i => by rw [hload]; exact hmean i)
    (fun i => (card_image_le).trans (hsize i)) hocc hsmall
  refine ⟨ν,hν,fun i => ?_⟩
  have hv_i := hv i
  rw [hload] at hv_i
  exact hv_i

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/EventRefinement.lean

-- BEGIN PRProof/PolynomialTail.lean
noncomputable section
open Filter Topology
namespace PacketRouting.CongDil.PRFresh

theorem polynomial_stretched_exp_zero (d : ℕ) {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    Tendsto (fun x : ℝ => x^d*Real.exp (-b*x^a)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((d:ℝ)/a) b hb).comp
    (tendsto_rpow_atTop ha)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  dsimp only [Function.comp_def]
  rw [←Real.rpow_mul hx.le]
  have he : a*((d:ℝ)/a)=d := by field_simp
  rw [he,Real.rpow_natCast]

theorem exists_dyadic_tail_threshold (d H0 : ℕ) (C a b : ℝ) (ha : 0<a) (hb : 0<b) :
    ∃H : ℕ,H0≤H ∧ ∀h : ℕ,H≤h →
      C*((2:ℝ)^h)^d*Real.exp (-b*((2:ℝ)^h)^a) ≤ 1 := by
  have hpow : Tendsto (fun h : ℕ => (2:ℝ)^h) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h := ((polynomial_stretched_exp_zero d ha hb).const_mul C).comp hpow
  simp only [mul_zero] at h
  have he : ∀ᶠh : ℕ in atTop, C*((2:ℝ)^h)^d*Real.exp (-b*((2:ℝ)^h)^a) ≤ 1 := by
    have hx := h.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
    filter_upwards [hx] with n hn
    dsimp only [Function.comp_def] at hn
    nlinarith only [hn]
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  exact ⟨max H0 N,le_max_left _ _,fun n hn => hN n ((le_max_right _ _).trans hn)⟩

end PacketRouting.CongDil.PRFresh

-- END PRProof/PolynomialTail.lean

-- BEGIN PRProof/RefinementConstants.lean
noncomputable section
namespace PacketRouting.CongDil.PRFresh

lemma refinement_exponent {m γ : ℝ} (hm : 0 < m) (hγ : 0 < γ) (hγ2 : γ ≤ 2) :
    m ^ (1 / 32 : ℝ) / 16 ≤
      (m ^ (-(1 / 64 : ℝ))) ^ 2 / (4 * (2 * m ^ (-(1 / 16 : ℝ))) * γ) := by
  have hd : 0 < 4 * (2 * m ^ (-(1 / 16 : ℝ))) * γ := by positivity
  apply (le_div_iff₀ hd).mpr
  have he : m ^ (1 / 32 : ℝ) * m ^ (-(1 / 16 : ℝ)) =
      (m ^ (-(1 / 64 : ℝ))) ^ 2 := by
    rw [←Real.rpow_add hm, ←Real.rpow_natCast, ←Real.rpow_mul hm.le]
    norm_num
  have hp : 0 ≤ m ^ (1 / 32 : ℝ) * m ^ (-(1 / 16 : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hγ2 hp]

lemma exists_refinement_threshold : ∃H : ℕ,64≤H ∧ ∀h : ℕ,H≤h →
    ∀γ : ℝ, 1≤γ → γ≤2 →
    4 * Real.exp (-(((2:ℝ)^h)^(-(1/64:ℝ)))^2 /
      (4*(2*((2:ℝ)^h)^(-(1/16:ℝ)))*γ)) * (18*((2:ℝ)^h)^3+1) ≤ 1 := by
  obtain ⟨H,hH,hh⟩ := exists_dyadic_tail_threshold 3 64 76 (1/32) (1/16)
    (by norm_num) (by norm_num)
  refine ⟨H,hH,?_⟩
  intro h hHh γ hγ hγ2
  have hm : 0 < (2:ℝ)^h := by positivity
  have hm1 : 1 ≤ (2:ℝ)^h := one_le_pow₀ (by norm_num)
  have he := refinement_exponent hm (by linarith : 0<γ) hγ2
  have hex : Real.exp (-(((2:ℝ)^h)^(-(1/64:ℝ)))^2 /
      (4*(2*((2:ℝ)^h)^(-(1/16:ℝ)))*γ)) ≤
      Real.exp (-(1/16)*((2:ℝ)^h)^(1/32:ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht := hh h hHh
  have hx := Real.exp_pos (-(1/16)*((2:ℝ)^h)^(1/32:ℝ))
  have hc : 1 ≤ ((2:ℝ)^h)^3 := one_le_pow₀ hm1
  nlinarith [mul_le_mul_of_nonneg_right hex (by positivity : 0 ≤ 18*((2:ℝ)^h)^3+1)]

end PacketRouting.CongDil.PRFresh

-- END PRProof/RefinementConstants.lean

-- BEGIN PRProof/RoutingRefinement.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

lemma refine_routing_events {P E : Type*} [Fintype P] [DecidableEq P]
    {path : P → List E} {h L H n : ℕ} (hH : 64≤H) (hend : H ≤ scaleExponent h L)
    (hn : n+2≤L) (hd : DilationLE path (2^h)) (hc : CongestionLE path (2^h))
    (hnodup : ∀p,(path p).Nodup) (base : FlatRoutingAssignment P h L)
    {γ : ℝ} (hγ : 1≤γ) (hγ2 : γ≤2)
    (hmean : ∀i : RoutingEvent path h,
      (∑x,FiniteLaw.conditionalProb (routingPast n) base (routeArrival (by omega) hend i x))≤γ)
    (hocc : ∀j : P × RoutingCoordinate h L,
      (univ.filter (fun i : RoutingEvent path h => j∈(routingActive (by omega) hend n base i).image
        (crossingCoordinate hd n (by omega)))).card ≤ 9*(blockScale h n)^2)
    (hsmall : 4*Real.exp (-(scaleError h n)^2 /
      (4*(2*(blockScale h n:ℝ)^(-(1/16:ℝ)))*γ)) *
      (((2*blockScale h n)*(9*(blockScale h n)^2):ℕ)+1) ≤ 1) :
    ∃ν : FlatRoutingAssignment P h L, ∀i : RoutingEvent path h,
      (∑x,FiniteLaw.conditionalProb (routingPast (n+1)) ν
        (routeArrival (by omega) hend i x))≤γ+scaleError h n := by
  classical
  have h8 : 8≤H := by omega
  have hnL : n≤L := by omega
  have hsuc : routingPast (P := P) (h := h) (L := L) (n+1) = routingPast n ∪ routingCurrent n :=
    FiniteLaw.beforeLevel_succ _ n
  obtain ⟨ν,_,hv⟩ := FiniteLaw.refine_events (routingPast n) (routingCurrent n)
    (FiniteLaw.before_at_disjoint _ n) base (routeArrival h8 hend)
    (fun _ => arrivalSupport hd) (fun i => routeArrival_depends h8 hend hd i)
    (fun _ => crossingCoordinate hd n hnL)
    (fun _ x => arrival_current_support hd hnL x)
    (routingActive h8 hend n base) (fun _ => rfl)
    (fun i => crossingCoordinate_inj_active h8 hend hd hnL hnodup base i)
    (2*blockScale h n) (9*(blockScale h n)^2)
    (by
      have hm : (0:ℝ)<blockScale h n := by exact_mod_cast blockScale_pos h n
      positivity) hγ (scaleError_pos h n) (scaleError_le_one h n)
    (by
      intro i x ω
      rw [←hsuc]
      have hm : FiniteLaw.conditionalProb (routingPast (n+1))
          (FiniteLaw.replaceCoordinates (routingCurrent n) ω base) (routeArrival h8 hend i x) ≤
          FiniteLaw.conditionalProb (routingPast (n+1))
          (FiniteLaw.replaceCoordinates (routingCurrent n) ω base)
          (fun ν : FlatRoutingAssignment P h L =>
            (routingTimetable path h L H h8 hend (fun p j => ν (p,j))).time x.1 x.2=i.2.val) := by
        apply FiniteLaw.prob_mono
        intro ν hν
        exact hν.2
      exact hm.trans (conditional_time_bound hH hend hn hd _ x.1 x.2 i.2.val))
    hmean (fun i => routingActive_card h8 hend hd hnodup hc base i hγ2 (hmean i)) hocc hsmall
  refine ⟨ν,fun i => ?_⟩
  rw [hsuc]
  exact hv i

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingRefinement.lean

-- BEGIN PRProof/HierarchyDrift.lean

namespace PacketRouting.CongDil.PRFresh

lemma hierarchy_level_drift {h L H l q : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hl : l ≤ L) (hq : q ≤ 2 ^ h)
    (x y : Fin (2 ^ h / blockScale h l + 2) → ℕ)
    (hx : ∀ b, x b ≤ delayScale h l) (hy : ∀ b, y b ≤ delayScale h l) :
    (∑ b, (hierarchyBlock h L H l b.val hH hend hl).delay (x b) q) ≤
      (∑ b, (hierarchyBlock h L H l b.val hH hend hl).delay (y b) q) + delayScale h l := by
  classical
  let k : Fin (2 ^ h / blockScale h l + 2) :=
    ⟨centeredIndex (blockScale h l) q, centeredIndex_lt (blockScale_pos h l) hq⟩
  have hp (b : Fin (2 ^ h / blockScale h l + 2)) :
      (hierarchyBlock h L H l b.val hH hend hl).delay (x b) q ≤
      (hierarchyBlock h L H l b.val hH hend hl).delay (y b) q + if b = k then delayScale h l else 0 := by
    by_cases he : b = k
    · rw [if_pos he]
      have hb := (hierarchyBlock h L H l b.val hH hend hl).delay_le (hx b) (q : ℤ)
      omega
    · simp only [if_neg he, Nat.add_zero]
      have hv : b.val ≠ centeredIndex (blockScale h l) q := by
        intro hv
        apply he
        exact Fin.ext hv
      rcases lt_or_gt_of_ne hv with hb | hb
      · rw [hierarchyBlock_earlier hH hend hl (hx b) hb,
          hierarchyBlock_earlier hH hend hl (hy b) hb]
      · rw [hierarchyBlock_later hH hend hl (x b) hb,
          hierarchyBlock_later hH hend hl (y b) hb]
  have hs := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hp b)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hs

lemma hierarchy_total_drift {h L H q start : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hq : q ≤ 2 ^ h)
    (x y : HierarchyIndex h L → ℕ)
    (hx : ∀ j, x j ≤ hierarchyWidth h L j) (hy : ∀ j, y j ≤ hierarchyWidth h L j)
    (hfix : ∀ j, j.1.val + 1 < start → x j = y j) :
    (∑ j, (hierarchyWait h L H hH hend j).delay (x j) q) ≤
      (∑ j, (hierarchyWait h L H hH hend j).delay (y j) q) +
        ∑ l : Fin L, if start ≤ l.val + 1 then delayScale h (l.val + 1) else 0 := by
  classical
  rw [Fintype.sum_sigma, Fintype.sum_sigma, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l _
  by_cases he : start ≤ l.val + 1
  · rw [if_pos he]
    exact hierarchy_level_drift hH hend (by have := l.isLt; omega) hq
      (fun b => x ⟨l, b⟩) (fun b => y ⟨l, b⟩)
      (fun b => hx ⟨l, b⟩) (fun b => hy ⟨l, b⟩)
  · simp only [if_neg he, Nat.add_zero]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro b _
    rw [hfix ⟨l, b⟩ (by change l.val + 1 < start; omega)]

end PacketRouting.CongDil.PRFresh

-- END PRProof/HierarchyDrift.lean

-- BEGIN PRProof/TailReindex.lean

namespace PacketRouting.CongDil.PRFresh

lemma sum_range_level_tail (f : ℕ → ℕ) {start : ℕ} (hs : 1 ≤ start) (L : ℕ) :
    (∑ i ∈ Finset.range L, if start ≤ i + 1 then f (i + 1) else 0) =
      ∑ i ∈ Finset.range (L + 1 - start), f (start + i) := by
  induction L with
  | zero =>
    have he : 0 + 1 - start = 0 := by omega
    simp [he]
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : start ≤ L + 1
    · have he : L + 1 + 1 - start = (L + 1 - start) + 1 := by omega
      have hi : start + (L + 1 - start) = L + 1 := by omega
      rw [if_pos h, he, Finset.sum_range_succ, hi]
    · have he : L + 1 - start = 0 := by omega
      have he' : L + 1 + 1 - start = 0 := by omega
      simp only [if_neg h, he, he', Finset.range_zero, Finset.sum_empty, Nat.add_zero]

lemma sum_fin_level_tail_le {h L H start : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hs : 1 ≤ start) (hsL : start ≤ L) :
    (∑ l : Fin L, if start ≤ l.val + 1 then delayScale h (l.val + 1) else 0) ≤
      2 * delayScale h start := by
  rw [Fin.sum_univ_eq_sum_range (fun l => if start ≤ l + 1 then delayScale h (l + 1) else 0)]
  rw [sum_range_level_tail _ hs]
  exact sum_delay_tail hH hend (by omega)

end PacketRouting.CongDil.PRFresh

-- END PRProof/TailReindex.lean

-- BEGIN PRProof/RoutingDrift.lean

namespace PacketRouting.CongDil.PRFresh

lemma routingTimetable_drift {P E : Type*} {path : P → List E}
    {h L H start : ℕ} (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (hd : DilationLE path (2 ^ h)) (hs : 1 ≤ start) (hsL : start ≤ L)
    (ω ν : P → RoutingAssignment h L) (p : P) (k : Fin (path p).length)
    (hr : ω p none = ν p none)
    (hfix : ∀ j : HierarchyIndex h L, j.1.val + 1 < start → ω p (some j) = ν p (some j)) :
    (routingTimetable path h L H hH hend ω).time p k ≤
      (routingTimetable path h L H hH hend ν).time p k + 2 * delayScale h start := by
  have hq : k.val + 1 ≤ 2 ^ h := by have hp := hd p; omega
  have hx (j : HierarchyIndex h L) : (ω p (some j)).val + 1 ≤ hierarchyWidth h L j :=
    Nat.succ_le_of_lt (ω p (some j)).isLt
  have hy (j : HierarchyIndex h L) : (ν p (some j)).val + 1 ≤ hierarchyWidth h L j :=
    Nat.succ_le_of_lt (ν p (some j)).isLt
  have he := hierarchy_total_drift (start := start) hH hend hq
    (fun j => (ω p (some j)).val + 1) (fun j => (ν p (some j)).val + 1) hx hy
    (fun j hj => by rw [hfix j hj])
  have hb := sum_fin_level_tail_le hH hend hs hsL
  change k.val + 1 + ((ω p none).val + 1) +
      (∑ j, (hierarchyWait h L H hH hend j).delay ((ω p (some j)).val + 1) (k.val + 1 : ℕ)) ≤
    k.val + 1 + ((ν p none).val + 1) +
      (∑ j, (hierarchyWait h L H hH hend j).delay ((ν p (some j)).val + 1) (k.val + 1 : ℕ)) + _
  rw [hr]
  omega

lemma delayScale_le_block (h l : ℕ) : delayScale h l ≤ blockScale h l := by
  exact Nat.pow_le_pow_right (by omega) (Nat.div_le_self _ _)

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingDrift.lean

-- BEGIN PRProof/GapLipschitz.lean

namespace PacketRouting.CongDil.PRFresh

lemma timetable_time_le_of_index_le {P E : Type*} {path : P → List E}
    (τ : Timetable path) (G : ℕ)
    (hgap : ∀ p k (h : k + 1 < (path p).length),
      τ.time p ⟨k + 1, h⟩ ≤ τ.time p ⟨k, Nat.lt_of_succ_lt h⟩ + G)
    (p : P) (i j : Fin (path p).length) (hij : i.val ≤ j.val) :
    τ.time p j ≤ τ.time p i + G * (j.val - i.val) := by
  have aux : ∀ r : ℕ, ∀ hr : i.val + r < (path p).length,
      τ.time p ⟨i.val + r, hr⟩ ≤ τ.time p i + G * r := by
    intro r
    induction r with
    | zero => intro hr; simp
    | succ r ih =>
      intro hr
      have hr' : i.val + r < (path p).length := by omega
      have hp := ih hr'
      have hg := hgap p (i.val + r) (by omega)
      change τ.time p ⟨i.val + r + 1, _⟩ ≤ τ.time p ⟨i.val + r, hr'⟩ + G at hg
      have hidx : (⟨i.val + r + 1, by omega⟩ : Fin (path p).length) = ⟨i.val + (r + 1), hr⟩ := by
        apply Fin.ext
        change i.val + r + 1 = i.val + (r + 1)
        omega
      rw [hidx] at hg
      calc
        τ.time p ⟨i.val + (r + 1), hr⟩ ≤ τ.time p i + G * r + G :=
          hg.trans (Nat.add_le_add_right hp G)
        _ = τ.time p i + G * (r + 1) := by ring

  have hj : i.val + (j.val - i.val) < (path p).length := by omega
  have he := aux (j.val - i.val) hj
  have hidx : (⟨i.val + (j.val - i.val), hj⟩ : Fin (path p).length) = j := by
    apply Fin.ext
    change i.val + (j.val - i.val) = j.val
    omega
  rw [hidx] at he
  exact he

lemma timetable_time_le_nearby {P E : Type*} {path : P → List E}
    (τ : Timetable path) (G : ℕ)
    (hgap : ∀ p k (h : k + 1 < (path p).length),
      τ.time p ⟨k + 1, h⟩ ≤ τ.time p ⟨k, Nat.lt_of_succ_lt h⟩ + G)
    (p : P) (i j : Fin (path p).length) (m : ℕ) (hij : i.val ≤ j.val + m) :
    τ.time p i ≤ τ.time p j + G * m := by
  by_cases he : i.val ≤ j.val
  · exact (τ.strictMono_time p).monotone he |>.trans (Nat.le_add_right _ _)
  · have hji : j.val ≤ i.val := by omega
    have ht := timetable_time_le_of_index_le τ G hgap p j i hji
    have hm := Nat.mul_le_mul_left G (show i.val - j.val ≤ m by omega)
    omega

end PacketRouting.CongDil.PRFresh

-- END PRProof/GapLipschitz.lean

-- BEGIN PRProof/RoutingWindow.lean

namespace PacketRouting.CongDil.PRFresh

noncomputable def blockTimeWindow {P E : Type*} {path : P → List E}
    (τ : Timetable path) (p : P) (anchor : Fin (path p).length) (m : ℕ) : Finset ℕ :=
  Finset.Icc (τ.time p anchor - 4 * m) (τ.time p anchor + 4 * m)

lemma blockTimeWindow_card {P E : Type*} {path : P → List E}
    (τ : Timetable path) (p : P) (anchor : Fin (path p).length) {m : ℕ} (hm : 0 < m) :
    (blockTimeWindow τ p anchor m).card ≤ 9 * m := by
  unfold blockTimeWindow
  rw [Nat.card_Icc]
  omega

lemma routingTime_mem_block_window {P E : Type*} {path : P → List E}
    {h L H start : ℕ} (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (hd : DilationLE path (2 ^ h)) (hs : 1 ≤ start) (hsL : start ≤ L)
    (ω ν : P → RoutingAssignment h L) (p : P) (k anchor : Fin (path p).length)
    (hr : ω p none = ν p none)
    (hfix : ∀ j : HierarchyIndex h L, j.1.val + 1 < start → ω p (some j) = ν p (some j))
    (hb : centeredIndex (blockScale h start) (k.val + 1) =
      centeredIndex (blockScale h start) (anchor.val + 1)) :
    (routingTimetable path h L H hH hend ω).time p k ∈
      blockTimeWindow (routingTimetable path h L H hH hend ν) p anchor (blockScale h start) := by
  have hk := centeredIndex_bounds (q := k.val + 1) (blockScale_pos h start)
  have ha := centeredIndex_bounds (q := anchor.val + 1) (blockScale_pos h start)
  rw [hb] at hk
  have hka : k.val ≤ anchor.val + blockScale h start := by omega
  have hak : anchor.val ≤ k.val + blockScale h start := by omega
  have htka := timetable_time_le_nearby (routingTimetable path h L H hH hend ν) 2
    (routingTimetable_gap hH hend ν) p k anchor (blockScale h start) hka
  have htak := timetable_time_le_nearby (routingTimetable path h L H hH hend ν) 2
    (routingTimetable_gap hH hend ν) p anchor k (blockScale h start) hak
  have hxy := routingTimetable_drift hH hend hd hs hsL ω ν p k hr hfix
  have hyx := routingTimetable_drift hH hend hd hs hsL ν ω p k hr.symm (fun j hj => (hfix j hj).symm)
  have hW := delayScale_le_block h start
  simp only [blockTimeWindow, Finset.mem_Icc]
  constructor <;> omega

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingWindow.lean

-- BEGIN PRProof/BlockPositions.lean

namespace PacketRouting.CongDil.PRFresh

def blockPositions (n m b : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun k => centeredIndex m (k.val + 1) = b)

lemma blockPositions_card (n : ℕ) {m : ℕ} (hm : 0 < m) (b : ℕ) :
    (blockPositions n m b).card ≤ m := by
  let T : Finset ℤ := Finset.Ico (centeredStart m b) (centeredStart m b + m)
  have ht : T.card = m := by
    unfold T
    rw [Int.card_Ico]
    simp
  have hf : Set.MapsTo (fun k : Fin n => ((k.val + 1 : ℕ) : ℤ))
      (blockPositions n m b : Set (Fin n)) (T : Set ℤ) := by
    intro k hk
    simp only [blockPositions, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hb := centeredIndex_bounds (q := k.val + 1) hm
    rw [hk] at hb
    simpa only [T, Finset.mem_coe, Finset.mem_Ico] using hb
  have hi : (blockPositions n m b : Set (Fin n)).InjOn (fun k : Fin n => ((k.val + 1 : ℕ) : ℤ)) := by
    intro i _ j _ he
    change ((i.val + 1 : ℕ) : ℤ) = ((j.val + 1 : ℕ) : ℤ) at he
    apply Fin.ext
    omega
  have hc := Finset.card_le_card_of_injOn _ hf hi
  rw [ht] at hc
  exact hc

noncomputable def blockEvents {E : Type*} (path : List E) (m b : ℕ) (times : Finset ℕ) : Finset (E × ℕ) := by
  classical
  exact ((blockPositions path.length m b) ×ˢ times).image (fun kt => (path.get kt.1, kt.2))

lemma blockEvents_card {E : Type*} (path : List E) {m : ℕ} (hm : 0 < m)
    (b : ℕ) (times : Finset ℕ) : (blockEvents path m b times).card ≤ m * times.card := by
  classical
  have he : (blockEvents path m b times).card ≤ ((blockPositions path.length m b) ×ˢ times).card :=
    Finset.card_image_le
  rw [Finset.card_product] at he
  exact he.trans (Nat.mul_le_mul_right times.card (blockPositions_card path.length hm b))

lemma mem_blockEvents {E : Type*} (path : List E) (m b : ℕ) (times : Finset ℕ)
    (k : Fin path.length) (hk : centeredIndex m (k.val + 1) = b) {t : ℕ} (ht : t ∈ times) :
    (path.get k, t) ∈ blockEvents path m b times := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(k, t), ?_, rfl⟩
  simp only [Finset.mem_product, blockPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hk, ht⟩

end PacketRouting.CongDil.PRFresh

-- END PRProof/BlockPositions.lean

-- BEGIN PRProof/RoutingEnvelope.lean

namespace PacketRouting.CongDil.PRFresh

noncomputable def blockEnvelope {P E : Type*} (path : P → List E)
    (h L H : ℕ) (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (ν : P → RoutingAssignment h L) (p : P) (j : HierarchyIndex h L) : Finset (E × ℕ) := by
  classical
  let m := blockScale h (j.1.val + 1)
  exact if ha : ∃ k : Fin (path p).length, centeredIndex m (k.val + 1) = j.2.val then
    blockEvents (path p) m j.2.val
      (blockTimeWindow (routingTimetable path h L H hH hend ν) p (Classical.choose ha) m)
    else ∅

lemma blockEnvelope_card {P E : Type*} {path : P → List E}
    {h L H : ℕ} (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (ν : P → RoutingAssignment h L) (p : P) (j : HierarchyIndex h L) :
    (blockEnvelope path h L H hH hend ν p j).card ≤ 9 * (blockScale h (j.1.val + 1)) ^ 2 := by
  classical
  unfold blockEnvelope
  dsimp only
  split_ifs with ha
  · have hm := blockScale_pos h (j.1.val + 1)
    have he := blockEvents_card (path p) hm j.2.val
      (blockTimeWindow (routingTimetable path h L H hH hend ν) p (Classical.choose ha) (blockScale h (j.1.val + 1)))
    have ht := blockTimeWindow_card (routingTimetable path h L H hH hend ν) p (Classical.choose ha) hm
    have hmul := Nat.mul_le_mul_left (blockScale h (j.1.val + 1)) ht
    nlinarith
  · simp

lemma mem_blockEnvelope {P E : Type*} {path : P → List E}
    {h L H : ℕ} (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (hd : DilationLE path (2 ^ h)) (ω ν : P → RoutingAssignment h L)
    (p : P) (j : HierarchyIndex h L) (k : Fin (path p).length)
    (hk : centeredIndex (blockScale h (j.1.val + 1)) (k.val + 1) = j.2.val)
    (hr : ω p none = ν p none)
    (hfix : ∀ i : HierarchyIndex h L, i.1.val + 1 < j.1.val + 1 → ω p (some i) = ν p (some i)) :
    ((path p).get k, (routingTimetable path h L H hH hend ω).time p k) ∈
      blockEnvelope path h L H hH hend ν p j := by
  classical
  have ha : ∃ a : Fin (path p).length,
      centeredIndex (blockScale h (j.1.val + 1)) (a.val + 1) = j.2.val := ⟨k, hk⟩
  unfold blockEnvelope
  dsimp only
  rw [dif_pos ha]
  apply mem_blockEvents _ _ _ _ k hk
  apply routingTime_mem_block_window hH hend hd (by omega) (by have := j.1.isLt; omega)
    ω ν p k (Classical.choose ha) hr hfix
  exact hk.trans (Classical.choose_spec ha).symm

noncomputable def rootEnvelope {E : Type*} (path : List E) (D : ℕ) : Finset (E × ℕ) := by
  classical
  exact ((Finset.univ : Finset (Fin path.length)) ×ˢ Finset.Icc 1 (5 * D)).image
    (fun kt => (path.get kt.1, kt.2))

lemma rootEnvelope_card {E : Type*} (path : List E) {D : ℕ} (hd : path.length ≤ D) :
    (rootEnvelope path D).card ≤ 9 * D ^ 2 := by
  classical
  have he : (rootEnvelope path D).card ≤
      ((Finset.univ : Finset (Fin path.length)) ×ˢ Finset.Icc 1 (5 * D)).card := Finset.card_image_le
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.card_Icc, Nat.add_sub_cancel] at he
  have hmul := Nat.mul_le_mul_right (5 * D) hd
  nlinarith

lemma mem_rootEnvelope {P E : Type*} {path : P → List E}
    {h L H : ℕ} (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (hd : DilationLE path (2 ^ h)) (ω : P → RoutingAssignment h L)
    (p : P) (k : Fin (path p).length) :
    ((path p).get k, (routingTimetable path h L H hH hend ω).time p k) ∈ rootEnvelope (path p) (2 ^ h) := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(k, (routingTimetable path h L H hH hend ω).time p k), ?_, rfl⟩
  simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_Icc]
  exact ⟨(routingTimetable path h L H hH hend ω).one_le_time p k,
    routingTimetable_length hH hend hd ω p k⟩

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingEnvelope.lean

-- BEGIN PRProof/RoutingEnvelopeLevel.lean

namespace PacketRouting.CongDil.PRFresh

noncomputable def routingEnvelope {P E : Type*} (path : P → List E)
    (h L H : ℕ) (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (ν : P → RoutingAssignment h L) (p : P) : RoutingCoordinate h L → Finset (E × ℕ)
  | none => rootEnvelope (path p) (2 ^ h)
  | some j => blockEnvelope path h L H hH hend ν p j

lemma routingEnvelope_card {P E : Type*} {path : P → List E}
    {h L H : ℕ} (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (hd : DilationLE path (2 ^ h)) (ν : P → RoutingAssignment h L)
    (p : P) (j : RoutingCoordinate h L) :
    (routingEnvelope path h L H hH hend ν p j).card ≤ 9 * (blockScale h (routingLevel j)) ^ 2 := by
  cases j with
  | none => simpa only [routingEnvelope, routingLevel, blockScale, scaleExponent_zero] using rootEnvelope_card (path p) (hd p)
  | some j => exact blockEnvelope_card hH hend ν p j

lemma selected_block_index {h L q : ℕ} (hq : q ≤ 2 ^ h) (j : HierarchyIndex h L)
    (hj : some j ∈ routingSelected hq) :
    centeredIndex (blockScale h (j.1.val + 1)) q = j.2.val := by
  classical
  have hi : some j ∈ Finset.univ.image (fun l : Fin L => some (selectedHierarchyIndex h L q hq l)) :=
    (Finset.mem_insert.mp hj).resolve_left (by simp)
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hi
  have he' : selectedHierarchyIndex h L q hq l = j := Option.some.inj he
  rw [← he']
  rfl

lemma mem_routingEnvelope {P E : Type*} {path : P → List E}
    {h L H : ℕ} (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (hd : DilationLE path (2 ^ h)) (ω ν : P → RoutingAssignment h L)
    (p : P) (k : Fin (path p).length) (j : RoutingCoordinate h L)
    (hj : j ∈ routingSelected ((Nat.succ_le_of_lt k.isLt).trans (hd p)))
    (hfix : ∀ i : RoutingCoordinate h L, routingLevel i < routingLevel j → ω p i = ν p i) :
    ((path p).get k, (routingTimetable path h L H hH hend ω).time p k) ∈
      routingEnvelope path h L H hH hend ν p j := by
  cases j with
  | none => exact mem_rootEnvelope hH hend hd ω p k
  | some j =>
    apply mem_blockEnvelope hH hend hd ω ν p j k (selected_block_index _ j hj)
    · exact hfix none (by simp [routingLevel])
    · intro i hi
      exact hfix (some i) hi

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingEnvelopeLevel.lean

-- BEGIN PRProof/RoutingIncidence.lean

noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

lemma active_event_mem_envelope {P E : Type*} [Fintype P] [DecidableEq P]
    {path : P → List E} {h L H n : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hd : DilationLE path (2^h)) (hn : n ≤ L)
    (base : FlatRoutingAssignment P h L) (i : RoutingEvent path h)
    (x : Crossing path) (hx : x ∈ routingActive hH hend n base i) :
    routingEventKey i ∈ routingEnvelope path h L H hH hend (fun p j => base (p,j))
      (crossingCoordinate hd n hn x).1 (crossingCoordinate hd n hn x).2 := by
  classical
  have hp := (mem_filter.mp hx).2
  obtain ⟨ω,hω⟩ := FiniteLaw.exists_of_prob_pos _ hp
  let u := FiniteLaw.replaceCoordinates (routingPast n) base ω
  have hu : routeArrival hH hend i x u := hω
  have he := mem_routingEnvelope hH hend hd (fun p j => u (p,j))
    (fun p j => base (p,j)) x.1 x.2
    (selectedAtLevel ((Nat.succ_le_of_lt x.2.isLt).trans (hd x.1)) n hn)
    (selectedAtLevel_mem _ hn) (by
      intro j hj
      have hjn : routingLevel j < n := by simpa only [selectedAtLevel_level] using hj
      have hm : (x.1,j) ∈ routingPast (P := P) (h := h) (L := L) n := by
        simp only [routingPast, FiniteLaw.beforeLevel, mem_filter, mem_univ, true_and]
        exact hjn
      simp only [u, FiniteLaw.replaceCoordinates, if_pos hm])
  change crossingEdge path x = i.1.val ∧ _ at hu
  change ((path x.1).get x.2, _) ∈ _ at he
  change (i.1.val,i.2.val) ∈ _
  rw [show (path x.1).get x.2=i.1.val from hu.1, hu.2] at he
  exact he

lemma routing_incidence_bound {P E : Type*} [Fintype P] [DecidableEq P]
    {path : P → List E} {h L H n : ℕ} (hH : 8 ≤ H)
    (hend : H ≤ scaleExponent h L) (hd : DilationLE path (2^h)) (hn : n ≤ L)
    (base : FlatRoutingAssignment P h L) (j : P × RoutingCoordinate h L) :
    (univ.filter (fun i : RoutingEvent path h =>
      j ∈ (routingActive hH hend n base i).image (crossingCoordinate hd n hn))).card
      ≤ 9 * (blockScale h n)^2 := by
  classical
  let S := univ.filter (fun i : RoutingEvent path h =>
    j ∈ (routingActive hH hend n base i).image (crossingCoordinate hd n hn))
  by_cases hs : S.Nonempty
  · have hlevel : routingLevel j.2 = n := by
      obtain ⟨i,hi⟩ := hs
      obtain ⟨x,_,he⟩ := mem_image.mp (mem_filter.mp hi).2
      rw [←he]
      exact selectedAtLevel_level _ hn
    have hm : Set.MapsTo routingEventKey (S : Set (RoutingEvent path h))
        ((routingEnvelope path h L H hH hend (fun p j => base (p,j)) j.1 j.2) : Set (E × ℕ)) := by
      intro i hi
      obtain ⟨x,hx,he⟩ := mem_image.mp (mem_filter.mp hi).2
      have hh := active_event_mem_envelope hH hend hd hn base i x hx
      rw [he] at hh
      exact hh
    have hc := Finset.card_le_card_of_injOn routingEventKey hm routingEventKey_injective.injOn
    have hb := routingEnvelope_card hH hend hd (fun p j => base (p,j)) j.1 j.2
    rw [hlevel] at hb
    exact hc.trans hb
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change S.card ≤ _
    rw [he]
    simp

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingIncidence.lean

-- BEGIN PRProof/RoutingIteration.lean

namespace PacketRouting.CongDil.PRFresh

noncomputable def routingGamma (h n : ℕ) : ℝ :=
  1 + ∑ l ∈ Finset.range n, scaleError h l

lemma routingGamma_zero (h : ℕ) : routingGamma h 0 = 1 := by
  simp [routingGamma]

lemma routingGamma_succ (h n : ℕ) :
    routingGamma h (n + 1) = routingGamma h n + scaleError h n := by
  simp only [routingGamma, Finset.sum_range_succ]
  ring

lemma routingGamma_bounds {h L H n : ℕ} (hH : 128 ≤ H)
    (hend : H ≤ scaleExponent h L) (hn : n ≤ L) :
    1 ≤ routingGamma h n ∧ routingGamma h n ≤ 2 := by
  have hp : 0 ≤ ∑ l ∈ Finset.range n, scaleError h l :=
    Finset.sum_nonneg (fun l _ => (scaleError_pos h l).le)
  have hs : (∑ l ∈ Finset.range n, scaleError h l) ≤
      ∑ l ∈ Finset.range L, scaleError h l :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      (fun l _ _ => (scaleError_pos h l).le)
  have ht := scaleError_sum_le_one hH hend
  unfold routingGamma
  constructor <;> linarith

 theorem routing_iteration {Ω I : Type*} {h L H : ℕ}
    (hH : 128 ≤ H) (hend : H ≤ scaleExponent h L)
    (M : ℕ → Ω → I → ℝ) (base : Ω)
    (hbase : ∀ i, M 0 base i ≤ 1)
    (hstep : ∀ n, n + 1 ≤ L - 1 → ∀ ω,
      (∀ i, M n ω i ≤ routingGamma h n) →
      ∃ ν, ∀ i, M (n + 1) ν i ≤ routingGamma h n + scaleError h n) :
    ∃ ν, ∀ i, M (L - 1) ν i ≤ 2 := by
  have aux : ∀ n, n ≤ L - 1 → ∃ ν, ∀ i, M n ν i ≤ routingGamma h n := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨base, fun i => by simpa only [routingGamma_zero] using hbase i⟩
    | succ n ih =>
      intro hn
      obtain ⟨ω,hω⟩ := ih (by omega)
      obtain ⟨ν,hν⟩ := hstep n hn ω hω
      exact ⟨ν, fun i => by simpa only [routingGamma_succ] using hν i⟩
  obtain ⟨ν,hν⟩ := aux (L - 1) le_rfl
  exact ⟨ν, fun i => (hν i).trans (routingGamma_bounds hH hend (by omega)).2⟩

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingIteration.lean

-- BEGIN PRProof/RoutingInjectivity.lean

namespace PacketRouting.CongDil.PRFresh

lemma routing_root_fiber {P E : Type*} {path : P → List E}
    {h L H : ℕ} (hH : 8 ≤ H) (hend : H ≤ scaleExponent h L)
    (p : P) (k : Fin (path p).length) (u v : FlatRoutingAssignment P h L)
    (huv : ∀ j, j ≠ (p, none) → u j = v j)
    (he : (routingTimetable path h L H hH hend (fun p j => u (p, j))).time p k =
      (routingTimetable path h L H hH hend (fun p j => v (p, j))).time p k) : u = v := by
  classical
  have hs : (∑ j, (hierarchyWait h L H hH hend j).delay ((u (p, some j)).val + 1) (k.val + 1 : ℕ)) =
      ∑ j, (hierarchyWait h L H hH hend j).delay ((v (p, some j)).val + 1) (k.val + 1 : ℕ) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [huv (p, some j) (by simp)]
  simp only [routingTimetable, familyTimetable] at he
  rw [hs] at he
  have hr : u (p, none) = v (p, none) := Fin.ext (by omega)
  funext j
  by_cases hj : j = (p, none)
  · subst j
    exact hr
  · exact huv j hj

end PacketRouting.CongDil.PRFresh

-- END PRProof/RoutingInjectivity.lean

-- BEGIN PRProof/InitialLoad.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

lemma initial_load_bound {P E : Type*} [Fintype P] [DecidableEq P]
    {path : P → List E} {h L H : ℕ} (hH : 8≤H) (hend : H ≤ scaleExponent h L)
    (hn : ∀p,(path p).Nodup) (hc : CongestionLE path (2^h))
    (base : FlatRoutingAssignment P h L) (g : E) (t : ℕ) :
    (∑x : Crossing path, FiniteLaw.conditionalProb ∅ base
      (fun ω : FlatRoutingAssignment P h L => crossingEdge path x=g ∧
        (routingTimetable path h L H hH hend (fun p j => ω (p,j))).time x.1 x.2=t)) ≤ 1 := by
  classical
  let f (x : Crossing path) := FiniteLaw.conditionalProb ∅ base
      (fun ω : FlatRoutingAssignment P h L => crossingEdge path x=g ∧
        (routingTimetable path h L H hH hend (fun p j => ω (p,j))).time x.1 x.2=t)
  have hzero (x : Crossing path) (hx : crossingEdge path x ≠ g) : f x=0 := by
    simp only [f,FiniteLaw.conditionalProb,hx,false_and]
    exact FiniteLaw.prob_false _
  have hb (x : Crossing path) : f x ≤ ((2^h:ℕ):ℝ)⁻¹ := by
    have ht := FiniteLaw.conditionalProb_fiber (∅ : Finset (P × RoutingCoordinate h L)) base
      (fun ω : FlatRoutingAssignment P h L =>
        (routingTimetable path h L H hH hend (fun p j => ω (p,j))).time x.1 x.2)
      (x.1,none) (by simp) t (routing_root_fiber hH hend x.1 x.2)
    have hm : f x ≤ FiniteLaw.conditionalProb ∅ base
      (fun ω : FlatRoutingAssignment P h L =>
        (routingTimetable path h L H hH hend (fun p j => ω (p,j))).time x.1 x.2=t) := by
      apply FiniteLaw.prob_mono
      intro ω hω
      exact hω.2
    apply hm.trans
    have hcard : Fintype.card (Fin (routingWidth h L (x.1,none).2))=2^h := Fintype.card_fin _
    rwa [hcard] at ht
  have hcR : ((univ.filter (fun x : Crossing path => crossingEdge path x=g)).card:ℝ)≤(2^h:ℕ) := by
    exact_mod_cast edgeCrossings_card hn hc g
  have hD : (0:ℝ)<(2^h:ℕ) := by positivity
  change (∑x,f x)≤1
  calc
    _ = ∑x∈univ.filter (fun x : Crossing path => crossingEdge path x=g),f x := by
      symm
      apply sum_subset (filter_subset _ _)
      intro x _ hx
      exact hzero x (by simpa using hx)
    _ ≤ ∑x∈univ.filter (fun x : Crossing path => crossingEdge path x=g),((2^h:ℕ):ℝ)⁻¹ :=
      sum_le_sum (fun x _ => hb x)
    _ ≤ 1 := by
      simp only [sum_const,nsmul_eq_mul]
      calc
        _ ≤ ((2^h:ℕ):ℝ)*((2^h:ℕ):ℝ)⁻¹ := mul_le_mul_of_nonneg_right hcR (inv_nonneg.mpr hD.le)
        _ = 1 := mul_inv_cancel₀ hD.ne'

end PacketRouting.CongDil.PRFresh

-- END PRProof/InitialLoad.lean

-- BEGIN PRProof/RealizedAtoms.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh
namespace FiniteLaw
variable {J : Type*} [Fintype J] [DecidableEq J] {α : J → Type*}
  [∀j,Fintype (α j)] [∀j,Nonempty (α j)]

theorem conditionalProb_positive_of (S : Finset J) (base ν : ∀j,α j)
    (hν : ∀j∈S,ν j=base j) (A : (∀j,α j) → Prop) (hA : A ν) :
    0<conditionalProb S base A := by
  classical
  have he : replaceCoordinates S base ν=ν := by
    funext j
    by_cases hj : j∈S
    · simp [replaceCoordinates,hj,hν j hj]
    · simp [replaceCoordinates,hj]
  have hm := (uniform (∀j,α j)).weight_mul_le_mean
    (fun ω => if A (replaceCoordinates S base ω) then (1:ℝ) else 0)
    (fun ω => by split_ifs <;> norm_num) ν
  simp only [he,if_pos hA,mul_one] at hm
  have hp : 0<(uniform (∀j,α j)).weight ν := by
    change 0<(Fintype.card (∀j,α j):ℝ)⁻¹
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  exact hp.trans_le hm

theorem realized_indicator_le (S T : Finset J) (base ν : ∀j,α j)
    (hν : ∀j∈S,ν j=base j) (A : (∀j,α j) → Prop) [DecidablePred A]
    (hA : EventDepends A T) {B : ℝ} (hB : 0≤B)
    (hcard : (Fintype.card (∀j : {j // j∈T\S},α j):ℝ)≤B) :
    (if A ν then (1:ℝ) else 0) ≤ B*conditionalProb S base A := by
  by_cases ha : A ν
  · rw [if_pos ha]
    have hp := conditionalProb_positive_of S base ν hν A ha
    have hl := conditionalProb_atom S T base A hA hp
    have hc : (0:ℝ)<Fintype.card (∀j : {j // j∈T\S},α j) := by exact_mod_cast Fintype.card_pos
    have hn := mul_le_mul_of_nonneg_left hl hc.le
    have he : (Fintype.card (∀j : {j // j∈T\S},α j):ℝ)*
        (Fintype.card (∀j : {j // j∈T\S},α j):ℝ)⁻¹=1 := mul_inv_cancel₀ hc.ne'
    rw [he] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right hcard hp.le)
  · rw [if_neg ha]
    exact mul_nonneg hB (conditionalProb_nonneg S base A)

end FiniteLaw
end PacketRouting.CongDil.PRFresh

-- END PRProof/RealizedAtoms.lean

-- BEGIN PRProof/FinalLoad.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

lemma penultimate_scale_bound {h L H : ℕ} (hL : 2≤L) (hend : scaleExponent h L<2*H) :
    blockScale h (L-1) ≤ 2^(4*H) := by
  have he := scaleExponent_succ h (L-1)
  have hi : L-1+1=L := by omega
  rw [hi] at he
  unfold blockScale
  exact Nat.pow_le_pow_right (by omega) (by omega)

lemma final_load_bound {P E : Type*} [Fintype P] [DecidableEq P]
    {path : P → List E} {h L H : ℕ} (hH : 8≤H) (hend : H ≤ scaleExponent h L)
    (hsmall : scaleExponent h L<2*H) (hL : 2≤L) (hd : DilationLE path (2^h))
    (base : FlatRoutingAssignment P h L)
    (hmean : ∀g t,(∑x : Crossing path,FiniteLaw.conditionalProb
      (FiniteLaw.beforeLevel (fun j : P × RoutingCoordinate h L => routingLevel j.2) (L-1)) base
      (fun ω : FlatRoutingAssignment P h L => crossingEdge path x=g ∧
        (routingTimetable path h L H hH hend (fun p j => ω (p,j))).time x.1 x.2=t))≤2) :
    ∀g t,crossingLoad (routingTimetable path h L H hH hend (fun p j => base (p,j))) g t ≤ 2*2^(4*H) := by
  classical
  intro g t
  let S := FiniteLaw.beforeLevel (fun j : P × RoutingCoordinate h L => routingLevel j.2) (L-1)
  have hb (x : Crossing path) := FiniteLaw.realized_indicator_le S (arrivalSupport hd x) base base
    (fun _ _ => rfl)
    (fun ω : FlatRoutingAssignment P h L => crossingEdge path x=g ∧
      (routingTimetable path h L H hH hend (fun p j => ω (p,j))).time x.1 x.2=t)
    (by
      intro u v huv
      have he := arrival_depends hH hend hd x t u v huv
      exact and_congr_right (fun _ => he))
    (show (0:ℝ)≤(2^(4*H):ℕ) by positivity)
    (by
      have hc := (remaining_alphabet_card (L := L) hd (by omega : 1≤L-1) x).trans (penultimate_scale_bound hL hsmall)
      exact_mod_cast hc)
  have hs := sum_le_sum (fun x (_ : x∈univ) => hb x)
  rw [←crossingLoad_cast,←Finset.mul_sum] at hs
  have hh := mul_le_mul_of_nonneg_left (hmean g t) (show (0:ℝ)≤(2^(4*H):ℕ) by positivity)
  have hout := hs.trans hh
  exact_mod_cast (show (crossingLoad (routingTimetable path h L H hH hend (fun p j => base (p,j))) g t:ℝ)≤
    (2*2^(4*H):ℕ) by simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_comm] using hout)

end PacketRouting.CongDil.PRFresh

-- END PRProof/FinalLoad.lean

-- BEGIN PRProof/EventExtension.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

lemma extend_event_mean {P E : Type*} [Fintype P] [DecidableEq P]
    {path : P → List E} {h L H n : ℕ} (hH : 8≤H) (hend : H ≤ scaleExponent h L)
    (hd : DilationLE path (2^h)) (base : FlatRoutingAssignment P h L) {γ : ℝ} (hγ : 0≤γ)
    (hm : ∀i : RoutingEvent path h,
      (∑x,FiniteLaw.conditionalProb (routingPast n) base (routeArrival hH hend i x))≤γ) :
    ∀g t,(∑x : Crossing path,FiniteLaw.conditionalProb (routingPast n) base
      (fun ω : FlatRoutingAssignment P h L => crossingEdge path x=g ∧
        (routingTimetable path h L H hH hend (fun p j => ω (p,j))).time x.1 x.2=t))≤γ := by
  classical
  intro g t
  by_cases hg : g∈usedEdges path
  · by_cases ht : t≤5*2^h
    · exact hm (⟨g,hg⟩,⟨t,by omega⟩)
    · rw [←conditional_crossingLoad hH hend (routingPast n) base g t]
      have he : (fun ω : FlatRoutingAssignment P h L =>
          (crossingLoad (routingTimetable path h L H hH hend (fun p j => ω (p,j))) g t:ℝ)) =
          fun _ => 0 := by
        funext ω
        rw [crossingLoad_zero_after_length _ (routingTimetable_length hH hend hd _) g (by omega)]
        simp
      rw [he,FiniteLaw.conditionalMean_const]
      exact hγ
  · rw [←conditional_crossingLoad hH hend (routingPast n) base g t]
    have he : (fun ω : FlatRoutingAssignment P h L =>
        (crossingLoad (routingTimetable path h L H hH hend (fun p j => ω (p,j))) g t:ℝ)) =
        fun _ => 0 := by
      funext ω
      rw [crossingLoad_zero_of_unused _ hg t]
      simp
    rw [he,FiniteLaw.conditionalMean_const]
    exact hγ

end PacketRouting.CongDil.PRFresh

-- END PRProof/EventExtension.lean

-- BEGIN PRProof/LargeCoarse.lean
noncomputable section
open Finset
namespace PacketRouting.CongDil.PRFresh

lemma large_coarse_schedule (H : ℕ) (hH : 128≤H)
    (hthreshold : ∀e : ℕ,H≤e → ∀γ : ℝ,1≤γ → γ≤2 →
      4*Real.exp (-(((2:ℝ)^e)^(-(1/64:ℝ)))^2 /
        (4*(2*((2:ℝ)^e)^(-(1/16:ℝ)))*γ))*(18*((2:ℝ)^e)^3+1)≤1)
    {P E : Type*} [Fintype P] (path : P → List E) (hnodup : ∀p,(path p).Nodup)
    (h : ℕ) (hh : 8*H≤h) (hc : CongestionLE path (2^h)) (hd : DilationLE path (2^h)) :
    ∃τ : Timetable path, τ.LengthLE (5*2^h) ∧
      (∀g t,crossingLoad τ g t≤2*2^(4*H)) ∧
      (∀p k (hk : k+1<(path p).length),
        τ.time p ⟨k+1,hk⟩≤τ.time p ⟨k,Nat.lt_of_succ_lt hk⟩+2) := by
  classical
  obtain ⟨L,hend,hend2⟩ := exists_terminal_scale (by omega : 0<H) (by omega : H≤h)
  have hL : 2≤L := terminal_depth_two (by omega) hh hend2
  have h8 : 8≤H := by omega
  let base : FlatRoutingAssignment P h L := fun j => ⟨0,routingWidth_pos h L j.2⟩
  let M (n : ℕ) (ω : FlatRoutingAssignment P h L) (i : RoutingEvent path h) : ℝ :=
    ∑x,FiniteLaw.conditionalProb (routingPast n) ω (routeArrival h8 hend i x)
  obtain ⟨ν,hν⟩ := routing_iteration hH hend M base
    (by
      intro i
      dsimp only [M]
      have hz : routingPast (P := P) (h := h) (L := L) 0 = ∅ := by
        ext j
        simp [routingPast,FiniteLaw.beforeLevel]
      rw [hz]
      exact initial_load_bound h8 hend hnodup hc base i.1.val i.2.val)
    (by
      intro n hn ω hω
      have hn2 : n+2≤L := by omega
      have hg := routingGamma_bounds hH hend (show n≤L by omega)
      apply refine_routing_events (by omega) hend hn2 hd hc hnodup ω hg.1 hg.2 hω
        (routing_incidence_bound h8 hend hd (by omega) ω)
      have he : H ≤ scaleExponent h n := hend.trans (scaleExponent_antitone h (by omega))
      have ht := hthreshold (scaleExponent h n) he (routingGamma h n) hg.1 hg.2
      convert ht using 1
      simp only [scaleError,blockScale,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      congr 1 <;> ring)
  let τ := routingTimetable path h L H h8 hend (fun p j => ν (p,j))
  refine ⟨τ,routingTimetable_length h8 hend hd _,?_,routingTimetable_gap h8 hend _⟩
  apply final_load_bound h8 hend hend2 hL hd ν
  exact extend_event_mean h8 hend hd ν (by norm_num) hν

end PacketRouting.CongDil.PRFresh

-- END PRProof/LargeCoarse.lean

-- BEGIN PRProof/NativeAssembly.lean

namespace PacketRouting.CongDil.PRFresh

lemma native_from_coarse (H B : ℕ) (hB : 0 < B)
    (hlarge : ∀ (P E : Type) [Fintype P] (path : P → List E),
      (∀ p, (path p).Nodup) → ∀ h : ℕ, 8 * H ≤ h →
      CongestionLE path (2 ^ h) → DilationLE path (2 ^ h) →
      ∃ τ : Timetable path, τ.LengthLE (5 * 2 ^ h) ∧
        (∀ g t, crossingLoad τ g t ≤ B) ∧
        (∀ p k (hk : k + 1 < (path p).length),
          τ.time p ⟨k + 1, hk⟩ ≤ τ.time p ⟨k, Nat.lt_of_succ_lt hk⟩ + 2)) :
    ∃ K Q : ℕ, ∀ (V E P : Type) [Fintype P] (src tgt : E → V) (path : P → List E),
      (∀ p, IsEdgeSimplePath src tgt (path p)) →
      ∀ c d : ℕ, CongestionLE path c → DilationLE path d →
      ∃ τ : Timetable path, τ.Valid ∧ τ.LengthLE (K * (c + d)) ∧
        ∀ (g : E) (t : ℕ), τ.queueSize g t ≤ Q := by
  let Bs := 2 ^ (8 * H)
  have hBs : 0 < Bs := by dsimp [Bs]; positivity
  refine ⟨12 * (B + Bs + 1), 3 * (B + Bs), ?_⟩
  intro V E P _ src tgt path hn c d hc hd
  by_cases hz : c + d = 0
  · have hlen (p : P) : (path p).length = 0 := by have hp := hd p; omega
    let τ := noWaitTimetable path
    have hv : τ.Valid := by
      intro p q k l _ _
      have hp := hlen p
      have hk := k.isLt
      omega
    have hg : ∀ p k (hk : k + 1 < (path p).length),
        τ.time p ⟨k + 1, hk⟩ ≤ τ.time p ⟨k, Nat.lt_of_succ_lt hk⟩ + 1 := by
      intro p k hk
      have hp := hlen p
      omega
    refine ⟨τ, hv, ?_, ?_⟩
    · intro p k
      have hp := hlen p
      have hk := k.isLt
      omega
    · intro g t
      exact (queueSize_le_gap τ hv 1 hg g t).trans (by omega)
  · let h := Nat.log2 (c + d) + 1
    have hN : 0 < c + d := by omega
    have hD : c + d < 2 ^ h := (Nat.log2_lt hz).mp (by dsimp [h]; omega)
    have hD' : 2 ^ h ≤ 2 * (c + d) := by
      have hp := Nat.log2_self_le hz
      dsimp [h]
      rw [pow_succ]
      nlinarith
    have hcD : CongestionLE path (2 ^ h) := fun g => (hc g).trans (by omega)
    have hdD : DilationLE path (2 ^ h) := fun p => (hd p).trans (by omega)
    by_cases hh : 8 * H ≤ h
    · obtain ⟨τ, hτL, hτload, hτgap⟩ := hlarge P E path (fun p => (hn p).2) h hh hcD hdD
      obtain ⟨σ, hv, hL, hQ⟩ := serialize_timetable τ hB hτload hτL hτgap
      refine ⟨σ, hv, ?_, ?_⟩
      · intro p k
        have hk := hL p k
        nlinarith
      · intro g t
        exact (hQ g t).trans (by omega)
    · have hcBs : c ≤ Bs := by
        have hp : 2 ^ h ≤ 2 ^ (8 * H) := Nat.pow_le_pow_right (by omega) (by omega)
        dsimp [Bs]
        omega
      obtain ⟨τ, hv, hL, hQ⟩ := bounded_congestion_schedule (fun p => (hn p).2) hc hd hBs hcBs
      refine ⟨τ, hv, ?_, ?_⟩
      · intro p k
        have hk := hL p k
        nlinarith
      · intro g t
        exact (hQ g t).trans (by omega)

end PacketRouting.CongDil.PRFresh

-- END PRProof/NativeAssembly.lean

-- BEGIN PRProof/NativeConclusion.lean

namespace PacketRouting.CongDil.PRFresh

theorem native_theorem_3_4 :
    ∃ K Q : ℕ, ∀ (V E P : Type) [Fintype P] (src tgt : E → V) (path : P → List E),
      (∀ p, IsEdgeSimplePath src tgt (path p)) →
      ∀ c d : ℕ, CongestionLE path c → DilationLE path d →
      ∃ τ : Timetable path, τ.Valid ∧ τ.LengthLE (K * (c + d)) ∧
        ∀ (g : E) (t : ℕ), τ.queueSize g t ≤ Q := by
  classical
  obtain ⟨H0,hH0,hthreshold⟩ := exists_refinement_threshold
  let H := max 128 H0
  have h128 : 128≤H := le_max_left _ _
  have h0 : H0≤H := le_max_right _ _
  apply native_from_coarse H (2*2^(4*H)) (by positivity)
  intro P E _ path hnodup h hh hc hd
  exact large_coarse_schedule H h128
    (fun e he γ hγ hγ2 => hthreshold e (h0.trans he) γ hγ hγ2)
    path hnodup h hh hc hd

end PacketRouting.CongDil.PRFresh

-- END PRProof/NativeConclusion.lean

-- BEGIN Canonical.lean

namespace PacketRouting.CongDil

/-- Theorem 3.4 (Leighton–Maggs–Rao, p. 11): there are absolute constants `K` and `Q` such that
for every directed network, every finite set of packets with edge-simple paths of congestion at
most `c` and dilation at most `d`, there is a schedule of length at most `K (c + d)` in which at
most one packet traverses each edge at each step and every edge queue holds at most `Q` packets
at every step. -/
theorem theorem_3_4 :
    ∃ K Q : ℕ, ∀ (V E P : Type) [Fintype P] (src tgt : E → V) (path : P → List E),
      (∀ p, IsEdgeSimplePath src tgt (path p)) →
      ∀ c d : ℕ, CongestionLE path c → DilationLE path d →
      ∃ τ : Timetable path, τ.Valid ∧ τ.LengthLE (K * (c + d)) ∧
        ∀ (g : E) (t : ℕ), τ.queueSize g t ≤ Q := by
  exact PRFresh.native_theorem_3_4

end PacketRouting.CongDil

-- END Canonical.lean

open PacketRouting.CongDil

theorem solution :
    ∃ K Q : ℕ, ∀ (V E P : Type) [Fintype P] (src tgt : E → V) (path : P → List E),
      (∀ p, IsEdgeSimplePath src tgt (path p)) →
      ∀ c d : ℕ, CongestionLE path c → DilationLE path d →
      ∃ τ : Timetable path, τ.Valid ∧ τ.LengthLE (K * (c + d)) ∧
        ∀ (g : E) (t : ℕ), τ.queueSize g t ≤ Q := by
  exact PacketRouting.CongDil.theorem_3_4
