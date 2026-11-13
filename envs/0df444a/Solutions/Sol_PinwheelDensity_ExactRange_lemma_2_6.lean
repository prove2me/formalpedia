-- Prove2me | solution 1 for PinwheelDensity.ExactRange.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:50:01.170296+00:00
-- url     : https://prove2.me/submissions/9a294bed-5a0d-4a23-a9ce-b7a761bd99f6

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_coreP

section
set_option autoImplicit false
open Classical

namespace PinwheelDensity.ExactRange.Dev.CountAux

/-- Number of elements of `S` in the half-open interval `[a, b)`. -/
noncomputable def cnt (S : Set ℤ) (a b : ℤ) : ℕ := ((Finset.Ico a b).filter (· ∈ S)).card

lemma cnt_mono_int {S : Set ℤ} {a b a' b' : ℤ} (h1 : a' ≤ a) (h2 : b ≤ b') :
    cnt S a b ≤ cnt S a' b' := by
  unfold cnt
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
  exact ⟨⟨by omega, by omega⟩, hx.2⟩

lemma cnt_le_len (S : Set ℤ) (a b : ℤ) : cnt S a b ≤ (b - a).toNat := by
  unfold cnt
  calc _ ≤ (Finset.Ico a b).card := Finset.card_filter_le _ _
    _ = (b - a).toNat := Int.card_Ico a b

lemma cnt_split {S : Set ℤ} {a c b : ℤ} (h1 : a ≤ c) (h2 : c ≤ b) :
    cnt S a b ≤ cnt S a c + cnt S c b := by
  unfold cnt
  calc _ ≤ ((Finset.Ico a c).filter (· ∈ S) ∪ (Finset.Ico c b).filter (· ∈ S)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union] at hx ⊢
        by_cases hxc : x < c
        · exact Or.inl ⟨⟨hx.1.1, hxc⟩, hx.2⟩
        · exact Or.inr ⟨⟨by omega, hx.1.2⟩, hx.2⟩
    _ ≤ _ := Finset.card_union_le _ _

lemma window_bound {X : Set ℤ} {c N : ℕ} (hN : 0 < N) (hX : ∀ t, cnt X t (t + N) ≤ c) :
    ∀ q : ℕ, ∀ r : ℕ, r ≤ N → ∀ a b : ℤ, b - a ≤ (N : ℤ) * q + r →
      cnt X a b ≤ c * q + min c r := by
  intro q
  induction q with
  | zero =>
    intro r hr a b hab
    have hb : b ≤ a + N := by push_cast at hab; omega
    have h1 : cnt X a b ≤ c := le_trans (cnt_mono_int le_rfl hb) (hX a)
    have h2 : cnt X a b ≤ r := le_trans (cnt_le_len _ _ _) (by omega)
    simp only [Nat.mul_zero, Nat.zero_add]
    omega
  | succ q ih =>
    intro r hr a b hab
    have hNq : (N : ℤ) * ((q + 1 : ℕ) : ℤ) = N * q + N := by push_cast; ring
    rw [hNq] at hab
    by_cases hb : b ≤ a + N
    · have h1 : cnt X a b ≤ c := le_trans (cnt_mono_int le_rfl hb) (hX a)
      have : c ≤ c * (q + 1) := by nlinarith
      omega
    · have h1 := cnt_split (S := X) (a := a) (c := a + N) (b := b) (by omega) (by omega)
      have h2 := ih r hr (a + N) b (by omega)
      have h3 := hX a
      have : c * (q + 1) = c * q + c := by ring
      omega

lemma len_le_cnt {S : Set ℤ} {a b : ℤ} (l : List ℤ) (hl : l.Pairwise (· < ·))
    (h : ∀ x ∈ l, x ∈ S ∧ a ≤ x ∧ x < b) : l.length ≤ cnt S a b := by
  have hnd : l.Nodup := hl.imp (fun h => ne_of_lt h)
  rw [← List.toFinset_card_of_nodup hnd]
  unfold cnt
  apply Finset.card_le_card
  intro x hx
  rw [List.mem_toFinset] at hx
  simp only [Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨(h x hx).2.1, (h x hx).2.2⟩, (h x hx).1⟩

lemma cnt_ge_four {S : Set ℤ} {a b x1 x2 x3 x4 : ℤ} (h12 : x1 < x2) (h23 : x2 < x3)
    (h34 : x3 < x4) (m1 : x1 ∈ S) (m2 : x2 ∈ S) (m3 : x3 ∈ S) (m4 : x4 ∈ S)
    (ha : a ≤ x1) (hb : x4 < b) : 4 ≤ cnt S a b := by
  have := len_le_cnt (S := S) (a := a) (b := b) [x1, x2, x3, x4] (by simp; omega)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨‹_›, by omega, by omega⟩)
  simpa using this

lemma cnt_ge_five {S : Set ℤ} {a b x1 x2 x3 x4 x5 : ℤ} (h12 : x1 < x2) (h23 : x2 < x3)
    (h34 : x3 < x4) (h45 : x4 < x5) (m1 : x1 ∈ S) (m2 : x2 ∈ S) (m3 : x3 ∈ S) (m4 : x4 ∈ S)
    (m5 : x5 ∈ S) (ha : a ≤ x1) (hb : x5 < b) : 5 ≤ cnt S a b := by
  have := len_le_cnt (S := S) (a := a) (b := b) [x1, x2, x3, x4, x5] (by simp; omega)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨‹_›, by omega, by omega⟩)
  simpa using this

lemma cnt_add_le {U T X : Set ℤ} (hU : U ⊆ X) (hT : T ⊆ X) (hd : Disjoint U T) (a b : ℤ) :
    cnt U a b + cnt T a b ≤ cnt X a b := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union] at hx ⊢
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, hU h2⟩
    · exact ⟨h1, hT h2⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter] at hx hx'
    exact Set.disjoint_left.mp hd hx.2 hx'.2

/-- Interleaving, gap one: between any two elements of `U` lies an element of `T`. -/
lemma interleave1_list (U T : Set ℤ)
    (hsep : ∀ y ∈ U, ∀ y' ∈ U, y < y' → ∃ t ∈ T, y < t ∧ t < y') :
    ∀ l : List ℤ, l.Pairwise (· < ·) → (∀ x ∈ l, x ∈ U) →
      ∃ G : Finset ℤ, (∀ g ∈ G, g ∈ T ∧ (∃ x ∈ l, x < g) ∧ (∃ x ∈ l, g < x)) ∧
        l.length ≤ G.card + 1 := by
  intro l
  induction l with
  | nil => intro _ _; exact ⟨∅, by simp, by simp⟩
  | cons e rest ih =>
    intro hl hU
    cases rest with
    | nil => exact ⟨∅, by simp, by simp⟩
    | cons e' rest' =>
      have hl' := List.pairwise_cons.mp hl
      have hee : e < e' := hl'.1 e' (by simp)
      obtain ⟨G', hG', hlen⟩ := ih hl'.2 (fun x hx => hU x (by simp [hx]))
      obtain ⟨t, htT, het, het'⟩ := hsep e (hU e (by simp)) e' (hU e' (by simp)) hee
      have hlt : ∀ g ∈ G', t < g := by
        intro g hg
        obtain ⟨_, ⟨x, hx, hxg⟩, _⟩ := hG' g hg
        have : e' ≤ x := by
          simp at hx
          rcases hx with rfl | hx
          · exact le_refl _
          · exact le_of_lt ((List.pairwise_cons.mp hl'.2).1 x hx)
        omega
      have htn : t ∉ G' := fun h => lt_irrefl _ (hlt t h)
      refine ⟨insert t G', ?_, ?_⟩
      · intro g hg
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact ⟨htT, ⟨e, by simp, het⟩, ⟨e', by simp, het'⟩⟩
        · obtain ⟨h1, ⟨x, hx, hxg⟩, ⟨x', hx', hxg'⟩⟩ := hG' g hg
          exact ⟨h1, ⟨x, by simp at hx ⊢; tauto, hxg⟩, ⟨x', by simp at hx' ⊢; tauto, hxg'⟩⟩
      · rw [Finset.card_insert_of_notMem htn]
        simp only [List.length_cons] at hlen ⊢
        omega

/-- Interleaving, gap two: between `y` and `y'` lies an element of `T` as soon as an element of
`U` lies strictly between them. -/
lemma interleave2_list (U T : Set ℤ)
    (hsep : ∀ y ∈ U, ∀ z ∈ U, ∀ y' ∈ U, y < z → z < y' → ∃ t ∈ T, y < t ∧ t < y') :
    ∀ n : ℕ, ∀ l : List ℤ, l.length = n → l.Pairwise (· < ·) → (∀ x ∈ l, x ∈ U) →
      ∃ G : Finset ℤ, (∀ g ∈ G, g ∈ T ∧ (∃ x ∈ l, x < g) ∧ (∃ x ∈ l, g < x)) ∧
        l.length ≤ 2 * G.card + 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hn hl hU
    match l, hn, hl, hU with
    | [], _, _, _ => exact ⟨∅, by simp, by simp⟩
    | [_], _, _, _ => exact ⟨∅, by simp, by simp⟩
    | [_, _], _, _, _ => exact ⟨∅, by simp, by simp⟩
    | e0 :: e1 :: e2 :: rest, hn, hl, hU =>
      have hl1 := List.pairwise_cons.mp hl
      have hl2 := List.pairwise_cons.mp hl1.2
      have h01 : e0 < e1 := hl1.1 e1 (by simp)
      have h12 : e1 < e2 := hl2.1 e2 (by simp)
      have hl3 := List.pairwise_cons.mp hl2.2
      obtain ⟨G', hG', hlen⟩ := ih (rest.length + 1) (by simp at hn; omega) (e2 :: rest) rfl hl2.2
        (fun x hx => hU x (by simp at hx ⊢; tauto))
      obtain ⟨t, htT, het, het'⟩ := hsep e0 (hU e0 (by simp)) e1 (hU e1 (by simp)) e2
        (hU e2 (by simp)) h01 h12
      have hlt : ∀ g ∈ G', t < g := by
        intro g hg
        obtain ⟨_, ⟨x, hx, hxg⟩, _⟩ := hG' g hg
        have : e2 ≤ x := by
          simp at hx
          rcases hx with rfl | hx
          · exact le_refl _
          · exact le_of_lt (hl3.1 x hx)
        omega
      have htn : t ∉ G' := fun h => lt_irrefl _ (hlt t h)
      refine ⟨insert t G', ?_, ?_⟩
      · intro g hg
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact ⟨htT, ⟨e0, by simp, het⟩, ⟨e2, by simp, het'⟩⟩
        · obtain ⟨h1, ⟨x, hx, hxg⟩, ⟨x', hx', hxg'⟩⟩ := hG' g hg
          exact ⟨h1, ⟨x, by simp at hx ⊢; tauto, hxg⟩, ⟨x', by simp at hx' ⊢; tauto, hxg'⟩⟩
      · rw [Finset.card_insert_of_notMem htn]
        simp only [List.length_cons] at hlen ⊢
        omega

/-- The elements of `T` produced by interleaving lie in the interval. -/
lemma cnt_of_list {U T : Set ℤ} (a b : ℤ) (k : ℕ)
    (H : ∀ l : List ℤ, l.Pairwise (· < ·) → (∀ x ∈ l, x ∈ U) →
      ∃ G : Finset ℤ, (∀ g ∈ G, g ∈ T ∧ (∃ x ∈ l, x < g) ∧ (∃ x ∈ l, g < x)) ∧
        l.length ≤ k * G.card + k) :
    cnt U a b ≤ k * cnt T a b + k := by
  set F := (Finset.Ico a b).filter (· ∈ U) with hF
  have hs := Finset.sortedLT_sort F
  obtain ⟨G, hG, hlen⟩ := H (F.sort (fun x y => x ≤ y)) hs.pairwise
    (fun x hx => by
      rw [Finset.mem_sort] at hx
      exact (Finset.mem_filter.mp hx).2)
  rw [Finset.length_sort] at hlen
  have hGc : G.card ≤ cnt T a b := by
    unfold cnt
    apply Finset.card_le_card
    intro g hg
    obtain ⟨hgT, ⟨x, hx, hxg⟩, ⟨x', hx', hxg'⟩⟩ := hG g hg
    rw [Finset.mem_sort, hF, Finset.mem_filter, Finset.mem_Ico] at hx hx'
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨by omega, by omega⟩, hgT⟩
  have : cnt U a b = F.card := rfl
  rw [this]
  nlinarith

lemma interleave_cnt1 {U T : Set ℤ}
    (hsep : ∀ y ∈ U, ∀ y' ∈ U, y < y' → ∃ t ∈ T, y < t ∧ t < y') (a b : ℤ) :
    cnt U a b ≤ cnt T a b + 1 := by
  have := cnt_of_list (U := U) (T := T) a b 1 (by
    intro l hl hU
    obtain ⟨G, h1, h2⟩ := interleave1_list U T hsep l hl hU
    exact ⟨G, h1, by omega⟩)
  omega

lemma interleave_cnt2 {U T : Set ℤ}
    (hsep : ∀ y ∈ U, ∀ z ∈ U, ∀ y' ∈ U, y < z → z < y' → ∃ t ∈ T, y < t ∧ t < y')
    (a b : ℤ) : cnt U a b ≤ 2 * cnt T a b + 2 :=
  cnt_of_list (U := U) (T := T) a b 2 (fun l hl hU =>
    interleave2_list U T hsep l.length l rfl hl hU)

lemma amp1 {U T X : Set ℤ} (hsep : ∀ y ∈ U, ∀ y' ∈ U, y < y' → ∃ t ∈ T, y < t ∧ t < y')
    (hU : U ⊆ X) (hT : T ⊆ X) (hd : Disjoint U T) (a b : ℤ) :
    2 * cnt U a b ≤ cnt X a b + 1 := by
  have h1 := interleave_cnt1 hsep a b
  have h2 := cnt_add_le hU hT hd a b
  omega

lemma amp2 {U T X : Set ℤ}
    (hsep : ∀ y ∈ U, ∀ z ∈ U, ∀ y' ∈ U, y < z → z < y' → ∃ t ∈ T, y < t ∧ t < y')
    (hU : U ⊆ X) (hT : T ⊆ X) (hd : Disjoint U T) (a b : ℤ) :
    3 * cnt U a b ≤ 2 * cnt X a b + 2 := by
  have h1 := interleave_cnt2 hsep a b
  have h2 := cnt_add_le hU hT hd a b
  omega

/-- The gap lemma: consecutive elements `p < p'` of `T` around `[y, y']`. -/
lemma gap {T : Set ℤ} {a : ℤ} (hT : ∀ t : ℤ, ∃ x ∈ T, t ≤ x ∧ x < t + a) {y y' : ℤ}
    (hy : y ∉ T) (hy' : y' ∉ T) (hno : ∀ t ∈ T, ¬ (y < t ∧ t < y')) (hyy : y ≤ y') :
    ∃ p ∈ T, ∃ p' ∈ T, p < y ∧ y' < p' ∧ p' - p ≤ a := by
  obtain ⟨x, hxT, hx1, hx2⟩ := hT (y - a + 1)
  have hxy : x < y := by
    rcases lt_or_eq_of_le (show x ≤ y by omega) with h | h
    · exact h
    · exact absurd (h ▸ hxT) hy
  set P := (Finset.Ico (y - a) y).filter (· ∈ T) with hP
  have hPne : P.Nonempty := ⟨x, by simp [hP]; exact ⟨⟨by omega, hxy⟩, hxT⟩⟩
  set p := P.max' hPne with hp
  have hpP : p ∈ P := Finset.max'_mem _ _
  have hpP' := hpP
  rw [hP, Finset.mem_filter, Finset.mem_Ico] at hpP'
  have hxp : x ≤ p := Finset.le_max' _ _ (by simp [hP]; exact ⟨⟨by omega, hxy⟩, hxT⟩)
  obtain ⟨x', hx'T, hx'1, hx'2⟩ := hT (y' + 1)
  set P' := (Finset.Ioc y' (y' + a)).filter (· ∈ T) with hP'
  have hP'ne : P'.Nonempty := ⟨x', by simp [hP']; exact ⟨⟨by omega, by omega⟩, hx'T⟩⟩
  set p' := P'.min' hP'ne with hp'
  have hp'P : p' ∈ P' := Finset.min'_mem _ _
  have hp'P' := hp'P
  rw [hP', Finset.mem_filter, Finset.mem_Ioc] at hp'P'
  have hnone : ∀ t ∈ T, ¬ (p < t ∧ t < p') := by
    rintro t htT ⟨h1, h2⟩
    by_cases hty : t < y
    · have : t ∈ P := by
        rw [hP, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨by omega, hty⟩, htT⟩
      have := Finset.le_max' P t this
      omega
    · by_cases hty' : t ≤ y'
      · rcases lt_or_eq_of_le (show y ≤ t by omega) with h | h
        · rcases lt_or_eq_of_le hty' with h' | h'
          · exact hno t htT ⟨h, h'⟩
          · exact hy' (h' ▸ htT)
        · exact hy (h ▸ htT)
      · have : t ∈ P' := by
          rw [hP', Finset.mem_filter, Finset.mem_Ioc]
          exact ⟨⟨by omega, by omega⟩, htT⟩
        have := Finset.min'_le P' t this
        omega
  refine ⟨p, hpP'.2, p', hp'P'.2, by omega, by omega, ?_⟩
  obtain ⟨z, hzT, hz1, hz2⟩ := hT (p + 1)
  have : p' ≤ z := by
    by_contra hcon
    exact hnone z hzT ⟨by omega, by omega⟩
  omega


lemma window_family (S : ℕ → Set ℤ) (J : Finset ℕ)
    (hdis : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (S j) (S k)) (N : ℕ) (t : ℤ)
    (hhit : ∀ j ∈ J, ∃ x ∈ S j, t ≤ x ∧ x < t + N) :
    J.card + cnt {z | ∀ j ∈ J, z ∉ S j} t (t + N) ≤ N := by
  set X : Set ℤ := {z | ∀ j ∈ J, z ∉ S j} with hXdef
  let f : ℕ → ℤ := fun j => if h : j ∈ J then (hhit j h).choose else 0
  have hf : ∀ j ∈ J, f j ∈ S j ∧ t ≤ f j ∧ f j < t + N := by
    intro j hj
    simp only [f, dif_pos hj]
    exact (hhit j hj).choose_spec
  have hcard : J.card ≤ ((Finset.Ico t (t + N)).filter (fun z => ¬ z ∈ X)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro j hj
      have hj' : j ∈ J := hj
      obtain ⟨h1, h2, h3⟩ := hf j hj'
      simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq]
      exact ⟨⟨h2, h3⟩, fun hx => hx j hj' h1⟩
    · intro j hj k hk hjk
      have hj' : j ∈ J := hj
      have hk' : k ∈ J := hk
      by_contra hne
      have := Set.disjoint_left.mp (hdis j hj' k hk' hne) (hf j hj').1
      apply this
      rw [hjk]
      exact (hf k hk').1
  have hsum : ((Finset.Ico t (t + (N : ℤ))).filter (· ∈ X)).card +
      ((Finset.Ico t (t + (N : ℤ))).filter (fun z => ¬ z ∈ X)).card =
      (Finset.Ico t (t + (N : ℤ))).card := Finset.card_filter_add_card_filter_not _
  have hc : (Finset.Ico t (t + (N : ℤ))).card = N := by
    rw [Int.card_Ico]; omega
  have hcnt : cnt X t (t + (N : ℤ)) =
      ((Finset.Ico t (t + (N : ℤ))).filter (· ∈ X)).card := by
    unfold cnt
    congr
  omega

/-- Abstract form of Lemma 2.6. `SB` is the second task of period `m`. -/
theorem abstractQ (m : ℕ) (X SA SB SC SF : Set ℤ)
    (hX : ∀ t, cnt X t (t + ((m : ℤ) + 1)) ≤ 4)
    (hA : SA ⊆ X) (hB : SB ⊆ X \ SA) (hC : SC ⊆ (X \ SA) \ SB)
    (hF : SF ⊆ ((X \ SA) \ SB) \ SC)
    (hitA : ∀ t : ℤ, ∃ x ∈ SA, t ≤ x ∧ x < t + (m : ℤ))
    (hitB : ∀ t : ℤ, ∃ x ∈ SB, t ≤ x ∧ x < t + (m : ℤ))
    (hitC : ∀ t : ℤ, ∃ x ∈ SC, t ≤ x ∧ x < t + (2 * (m : ℤ) + 2))
    (hitF : ∀ t : ℤ, ∃ x ∈ SF, t ≤ x ∧ x < t + (3 * (m : ℤ) + 2))
    (f : ℤ) (hfV : f ∈ ((X \ SA) \ SB) \ SC) (hfF : f ∉ SF) : False := by
  have hX' : ∀ t, cnt X t (t + ((m + 1 : ℕ) : ℤ)) ≤ 4 := by
    intro t; push_cast; exact hX t
  have bd := window_bound (Nat.succ_pos m) hX'
  set Y := X \ SA with hY
  set W := Y \ SB with hW
  set V := W \ SC with hV
  have hYX : Y ⊆ X := Set.diff_subset
  have hWY : W ⊆ Y := Set.diff_subset
  have hVW : V ⊆ W := Set.diff_subset
  -- Step 2
  have s2 : ∀ y ∈ Y, ∀ z ∈ Y, ∀ y' ∈ Y, y < z → z < y' → ∃ t ∈ SA, y < t ∧ t < y' := by
    intro y hy z hz y' hy' h1 h2
    by_contra hcon
    push_neg at hcon
    obtain ⟨p, hp, p', hp', e1, e2, e3⟩ := gap hitA hy.2 hy'.2
      (fun t ht ⟨a, b⟩ => absurd (hcon t ht a) (not_le.mpr b)) (by omega)
    have h4 := cnt_ge_five (S := X) (a := p) (b := p' + 1) e1 h1 h2 e2 (hA hp) (hYX hy) (hYX hz)
      (hYX hy') (hA hp') le_rfl (by omega)
    have h5 := bd 1 0 (by omega) p (p' + 1) (by push_cast; omega)
    omega
  have a2 : ∀ a b, 3 * cnt Y a b ≤ 2 * cnt X a b + 2 := fun a b =>
    amp2 s2 hYX hA Set.disjoint_sdiff_left a b
  -- Step 3
  have s3 : ∀ w ∈ W, ∀ w' ∈ W, w < w' → ∃ t ∈ SB, w < t ∧ t < w' := by
    intro y hy y' hy' hlt
    by_contra hcon
    push_neg at hcon
    obtain ⟨p, hp, p', hp', e1, e2, e3⟩ := gap hitB hy.2 hy'.2
      (fun t ht ⟨a, b⟩ => absurd (hcon t ht a) (not_le.mpr b)) hlt.le
    have h4 := cnt_ge_four (S := Y) (a := p) (b := p' + 1) e1 hlt e2 (hB hp) (hWY hy) (hWY hy')
      (hB hp') le_rfl (by omega)
    have h5 := a2 p (p' + 1)
    have h6 := bd 1 0 (by omega) p (p' + 1) (by push_cast; omega)
    omega
  have a1 : ∀ a b, 2 * cnt W a b ≤ cnt Y a b + 1 := fun a b =>
    amp1 s3 hWY (fun x hx => (hB hx)) Set.disjoint_sdiff_left a b
  -- Step 4
  have s4 : ∀ w ∈ V, ∀ w' ∈ V, w < w' → ∃ t ∈ SC, w < t ∧ t < w' := by
    intro y hy y' hy' hlt
    by_contra hcon
    push_neg at hcon
    obtain ⟨p, hp, p', hp', e1, e2, e3⟩ := gap hitC hy.2 hy'.2
      (fun t ht ⟨a, b⟩ => absurd (hcon t ht a) (not_le.mpr b)) hlt.le
    have h4 := cnt_ge_four (S := W) (a := p) (b := p' + 1) e1 hlt e2 (hC hp) (hVW hy) (hVW hy')
      (hC hp') le_rfl (by omega)
    have h5 := a1 p (p' + 1)
    have h55 := a2 p (p' + 1)
    have h6 := bd 2 1 (by omega) p (p' + 1) (by push_cast; omega)
    omega
  -- Step 5
  obtain ⟨v, hv, v', hv', h1, h2, h3⟩ := gap hitF hfF hfF (fun t _ ⟨a, b⟩ => by omega) le_rfl
  have hvV := hF hv
  have hv'V := hF hv'
  obtain ⟨c, hc, hc1, hc2⟩ := s4 v hvV f hfV h1
  obtain ⟨c', hc', hc1', hc2'⟩ := s4 f hfV v' hv'V h2
  have h4 := cnt_ge_five (S := W) (a := v) (b := v' + 1) hc1 hc2 hc1' hc2' hvV.1 (hC hc)
    hfV.1 (hC hc') hv'V.1 le_rfl (by omega)
  have h5 := a1 v (v' + 1)
  have h55 := a2 v (v' + 1)
  have h6 := bd 3 0 (by omega) v (v' + 1) (by push_cast; omega)
  omega

end PinwheelDensity.ExactRange.Dev.CountAux
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.SchedAux

open PinwheelDensity.ExactRange

/-- The execution sets indexed by natural numbers (empty out of range). -/
def fam {A : List ℕ} (σ : ZSchedule A) (j : ℕ) : Set ℤ :=
  if h : j < A.length then σ.days ⟨j, h⟩ else ∅

lemma fam_disjoint {A : List ℕ} (σ : ZSchedule A) {j k : ℕ} (hj : j < A.length)
    (hk : k < A.length) (hne : j ≠ k) : Disjoint (fam σ j) (fam σ k) := by
  simp only [fam, dif_pos hj, dif_pos hk]
  exact σ.disjoint (fun h => hne (by simpa using congrArg Fin.val h))

lemma fam_hit {A : List ℕ} (σ : ZSchedule A) {j : ℕ} (hj : j < A.length) (a : ℕ)
    (ha : A[j] = a) (t : ℤ) : ∃ x ∈ fam σ j, t ≤ x ∧ x < t + (a : ℤ) := by
  obtain ⟨x, hx1, hx2⟩ := σ.hits ⟨j, hj⟩ t
  refine ⟨x, ?_, ?_⟩
  · simp only [fam, dif_pos hj]; exact hx1
  · have : A.get ⟨j, hj⟩ = a := by simpa using ha
    rw [this] at hx2
    simpa using hx2

lemma fam_free {A : List ℕ} (σ : ZSchedule A) {d : ℤ} (hd : σ.IsFreeDay d) (j : ℕ) :
    d ∉ fam σ j := by
  by_cases hj : j < A.length
  · simp only [fam, dif_pos hj]; exact hd ⟨j, hj⟩
  · simp [fam, hj]

lemma fam_hit' {A : List ℕ} (σ : ZSchedule A) {j a : ℕ} (h : A[j]? = some a) (b : ℤ)
    (hab : (a : ℤ) = b) (t : ℤ) : ∃ x ∈ fam σ j, t ≤ x ∧ x < t + b := by
  obtain ⟨hj, ha⟩ := List.getElem?_eq_some_iff.mp h
  obtain ⟨x, hx, h1, h2⟩ := fam_hit σ hj a ha t
  exact ⟨x, hx, h1, by omega⟩

/-- A window of length `M * s` contains a point `p + M * (c + s * j)`. -/
lemma exists_win (t M p c s : ℤ) (hM : 0 < M) (hs : 0 < s) :
    ∃ j : ℤ, t ≤ p + M * (c + s * j) ∧ p + M * (c + s * j) < t + M * s := by
  have hL : 0 < M * s := mul_pos hM hs
  set r := p + M * c with hr
  refine ⟨-((r - t) / (M * s)), ?_, ?_⟩
  · have e : p + M * (c + s * (-((r - t) / (M * s)))) = t + (r - t) % (M * s) := by
      rw [Int.emod_def, hr]; ring
    rw [e]
    have := Int.emod_nonneg (r - t) hL.ne'
    omega
  · have e : p + M * (c + s * (-((r - t) / (M * s)))) = t + (r - t) % (M * s) := by
      rw [Int.emod_def, hr]; ring
    rw [e]
    have := Int.emod_lt_of_pos (r - t) hL
    omega

lemma pos_blk (M p k : ℤ) (hM : 0 < M) (hp0 : 0 ≤ p) (hp : p < M) :
    (p + M * k) % M = p ∧ (p + M * k) / M = k := by
  constructor
  · rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt hp0 hp
  · rw [Int.add_mul_ediv_left _ _ hM.ne', Int.ediv_eq_zero_of_lt hp0 hp]; simp

end PinwheelDensity.ExactRange.Dev.SchedAux
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.L26

open PinwheelDensity.ExactRange CountAux SchedAux

lemma coreQ_length (m : ℕ) (hm : 4 ≤ m) : (coreQ m).length = m + 1 := by
  simp [coreQ]; omega

lemma coreQ_get? (m : ℕ) (hm : 4 ≤ m) (j : ℕ) : (coreQ m)[j]? =
    if j = 0 then some m else if j = 1 then some m else if j ≤ m - 2 then some (m + 1)
    else if j = m - 1 then some (2 * m + 2) else if j = m then some (3 * m + 2) else none := by
  have : coreQ m = m :: m :: (List.replicate (m - 3) (m + 1) ++ [2 * m + 2, 3 * m + 2]) := by
    simp [coreQ]
  rw [this]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j' with rfl | hj'
    · simp
    · obtain ⟨i, rfl⟩ : ∃ i, j' = i + 1 := ⟨j' - 1, by omega⟩
      rw [List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_append]
      simp only [List.length_replicate, List.getElem?_replicate]
      by_cases h : i < m - 3
      · simp [h]
        omega
      · obtain ⟨k, rfl⟩ : ∃ k, i = m - 3 + k := ⟨i - (m - 3), by omega⟩
        simp only [h, if_false, Nat.add_sub_cancel_left]
        rcases k with _ | _ | k
        all_goals (simp; try (split_ifs <;> first | rfl | (exfalso; omega)))

theorem noFreeQ (m : ℕ) (hm : 4 ≤ m) (σ : ZSchedule (coreQ m)) (d : ℤ) (hd : σ.IsFreeDay d) :
    False := by
  have hlen := coreQ_length m hm
  set S := fam σ with hS
  have hdis : ∀ j k, j ≤ m → k ≤ m → j ≠ k → Disjoint (S j) (S k) :=
    fun j k hj hk hne => fam_disjoint σ (by omega) (by omega) hne
  have hit : ∀ (j a : ℕ) (b : ℤ), (coreQ m)[j]? = some a → (a : ℤ) = b →
      ∀ t, ∃ x ∈ S j, t ≤ x ∧ x < t + b := fun j a b h hab t => fam_hit' σ h b hab t
  set J := Finset.Icc 2 (m - 2) with hJ
  set X : Set ℤ := {z | ∀ j ∈ J, z ∉ S j} with hXdef
  have hXw : ∀ t, CountAux.cnt X t (t + ((m : ℤ) + 1)) ≤ 4 := by
    intro t
    have : J.card + CountAux.cnt X t (t + ((m + 1 : ℕ) : ℤ)) ≤ m + 1 :=
      window_family S J (fun j hj k hk hne => hdis j k
      (by simp [hJ] at hj; omega) (by simp [hJ] at hk; omega) hne) (m + 1) t (fun j hj => by
        have hj' : 2 ≤ j ∧ j ≤ m - 2 := Finset.mem_Icc.mp hj
        exact hit j (m + 1) _ (by
          rw [coreQ_get? m hm, if_neg (by omega), if_neg (by omega), if_pos hj'.2]) rfl t)
    have hc : J.card = m - 3 := by simp [hJ]; omega
    push_cast at this
    omega
  have mk : ∀ k, k ≤ m → ¬ (2 ≤ k ∧ k ≤ m - 2) → ∀ z ∈ S k, z ∈ X := by
    intro k hk hkJ z hz j hj hzj
    have hj' : 2 ≤ j ∧ j ≤ m - 2 := Finset.mem_Icc.mp hj
    exact Set.disjoint_left.mp (hdis k j hk (by omega) (by rintro rfl; exact hkJ hj')) hz hzj
  have nd : ∀ k l z, k ≤ m → l ≤ m → k ≠ l → z ∈ S k → z ∉ S l :=
    fun k l z hk hl hne hz => Set.disjoint_left.mp (hdis k l hk hl hne) hz
  refine abstractQ m X (S 0) (S 1) (S (m - 1)) (S m) hXw
    (mk 0 (by omega) (by omega))
    (fun z hz => ⟨mk _ (by omega) (by omega) z hz, nd _ _ z (by omega) (by omega) (by omega) hz⟩)
    (fun z hz => ⟨⟨mk _ (by omega) (by omega) z hz, nd _ _ z (by omega) (by omega) (by omega) hz⟩,
      nd _ _ z (by omega) (by omega) (by omega) hz⟩)
    (fun z hz => ⟨⟨⟨mk _ (by omega) (by omega) z hz,
        nd _ _ z (by omega) (by omega) (by omega) hz⟩,
      nd _ _ z (by omega) (by omega) (by omega) hz⟩,
      nd _ _ z (by omega) (by omega) (by omega) hz⟩)
    (hit 0 m _ (by rw [coreQ_get? m hm]; simp) rfl)
    (hit 1 m _ (by rw [coreQ_get? m hm]; simp) rfl)
    (hit (m - 1) (2 * m + 2) _ (by
      rw [coreQ_get? m hm, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl])
      (by omega))
    (hit m (3 * m + 2) _ (by
      rw [coreQ_get? m hm, if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos rfl]) (by omega))
    d ⟨⟨⟨fun j _ => fam_free σ hd j, fam_free σ hd 0⟩, fam_free σ hd 1⟩, fam_free σ hd (m - 1)⟩
    (fam_free σ hd m)

/-- The task served on day `x`: blocks of `m` days `A, A', B₁, …, B_{m-3}, D`, the slot `D`
serving `C` and `F` in alternate blocks. -/
def taskQ (m : ℕ) (x : ℤ) : ℕ :=
  if x % (m : ℤ) = 0 then 0
  else if x % (m : ℤ) = 1 then 1
  else if x % (m : ℤ) ≤ (m : ℤ) - 2 then (x % (m : ℤ)).toNat
  else if (x / (m : ℤ)) % 2 = 1 then m else m - 1

lemma taskQ_val (m : ℕ) (hm : 4 ≤ m) (p c : ℤ) (hp0 : 0 ≤ p) (hp : p < (m : ℤ)) :
    taskQ m (p + (m : ℤ) * c) =
      if p = 0 then 0 else if p = 1 then 1 else if p ≤ (m : ℤ) - 2 then p.toNat
      else if c % 2 = 1 then m else m - 1 := by
  obtain ⟨h1, h2⟩ := pos_blk (m : ℤ) p c (by omega) hp0 hp
  unfold taskQ
  rw [h1, h2]

lemma get_of (m : ℕ) (i : Fin (coreQ m).length) (a : ℕ) (h : (coreQ m)[i.1]? = some a) :
    (coreQ m).get i = a := by
  obtain ⟨_, h2⟩ := List.getElem?_eq_some_iff.mp h
  simpa using h2

theorem zsched_Q (m : ℕ) (hm : 4 ≤ m) : ZSchedulable (coreQ m) := by
  refine ⟨{ days := fun i => {x | taskQ m x = i.1}
            disjoint := fun i j hij => Set.disjoint_left.mpr
              (fun x hx hx' => hij (Fin.ext (hx.symm.trans hx')))
            hits := ?_ }⟩
  intro i t
  have hi : i.1 < m + 1 := by have := i.2; have := coreQ_length m hm; omega
  have hM : (0 : ℤ) < (m : ℤ) := by omega
  by_cases h0 : i.1 = 0
  · rw [get_of m i m (by rw [coreQ_get? m hm, if_pos h0])]
    obtain ⟨j, h1, h2⟩ := exists_win t (m : ℤ) 0 0 1 hM one_pos
    refine ⟨_, ?_, h1, ?_⟩
    · show taskQ m _ = _
      rw [taskQ_val m hm 0 (0 + 1 * j) le_rfl hM]
      split_ifs <;> omega
    · omega
  by_cases h1' : i.1 = 1
  · rw [get_of m i m (by rw [coreQ_get? m hm, if_neg h0, if_pos h1'])]
    obtain ⟨j, h1, h2⟩ := exists_win t (m : ℤ) 1 0 1 hM one_pos
    refine ⟨_, ?_, h1, ?_⟩
    · show taskQ m _ = _
      rw [taskQ_val m hm 1 (0 + 1 * j) (by omega) (by omega)]
      split_ifs <;> omega
    · omega
  by_cases hB : i.1 ≤ m - 2
  · rw [get_of m i (m + 1) (by rw [coreQ_get? m hm, if_neg h0, if_neg h1', if_pos hB])]
    obtain ⟨j, h1, h2⟩ := exists_win t (m : ℤ) (i.1 : ℤ) 0 1 hM one_pos
    refine ⟨_, ?_, h1, ?_⟩
    · show taskQ m _ = _
      rw [taskQ_val m hm (i.1 : ℤ) (0 + 1 * j) (by omega) (by omega)]
      split_ifs <;> omega
    · push_cast; omega
  by_cases hC : i.1 = m - 1
  · rw [get_of m i (2 * m + 2) (by
      rw [coreQ_get? m hm, if_neg h0, if_neg h1', if_neg hB, if_pos hC])]
    obtain ⟨j, h1, h2⟩ := exists_win t (m : ℤ) ((m : ℤ) - 1) 0 2 hM two_pos
    refine ⟨_, ?_, h1, ?_⟩
    · show taskQ m _ = _
      rw [taskQ_val m hm ((m : ℤ) - 1) (0 + 2 * j) (by omega) (by omega)]
      split_ifs <;> omega
    · push_cast; omega
  · have hF : i.1 = m := by omega
    rw [get_of m i (3 * m + 2) (by
      rw [coreQ_get? m hm, if_neg h0, if_neg h1', if_neg hB, if_neg hC, if_pos hF])]
    obtain ⟨j, h1, h2⟩ := exists_win t (m : ℤ) ((m : ℤ) - 1) 1 2 hM two_pos
    refine ⟨_, ?_, h1, ?_⟩
    · show taskQ m _ = _
      rw [taskQ_val m hm ((m : ℤ) - 1) (1 + 2 * j) (by omega) (by omega)]
      split_ifs <;> omega
    · push_cast; omega

theorem lemma_2_6_core (m : ℕ) (hm : 4 ≤ m) :
    NoScheduleWithFreeDay (coreQ m) ∧ ZSchedulable (coreQ m) ∧ Saturated (coreQ m) := by
  have h1 : NoScheduleWithFreeDay (coreQ m) := fun σ d hd => noFreeQ m hm σ d hd
  have h2 := zsched_Q m hm
  exact ⟨h1, h2, h2, h1⟩

end PinwheelDensity.ExactRange.Dev.L26

namespace PinwheelDensity.ExactRange

theorem chk_lemma_2_6 (m : ℕ) (hm : 4 ≤ m) :
    NoScheduleWithFreeDay (coreQ m) ∧ ZSchedulable (coreQ m) ∧ Saturated (coreQ m) :=
  Dev.L26.lemma_2_6_core m hm

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_lemma_2_6 := @PinwheelDensity.ExactRange.chk_lemma_2_6
