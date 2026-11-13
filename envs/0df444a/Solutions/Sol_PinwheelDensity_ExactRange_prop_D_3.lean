-- Prove2me | solution 1 for PinwheelDensity.ExactRange.prop_D_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:01:10.896908+00:00
-- url     : https://prove2.me/submissions/3fc052a9-dc7b-4a23-b297-4bce341a0890
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_cellOf
import Definitions.Def_PinwheelDensity_ExactRange_checkRun
import Theorems.Thm_pinwheel_conjecture
import Theorems.Thm_PinwheelDensity_ExactRange_lemma_A_1

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.FoldAux

open PinwheelDensity.ExactRange

/-- `toQ` as a plain `List.map` (the coercion in the definition elaborates through a monad lift). -/
theorem toQ_eq (A : List ℕ) : toQ A = A.map (fun a : ℕ => ((a : ℕ) : ℚ)) := by
  induction A with
  | nil => rfl
  | cons a l ih =>
    have : toQ (a :: l) = (a : ℚ) :: toQ l := by simp [toQ]
    rw [this, ih]; rfl

/-! ### Counting executions -/

theorem cnt_succ (s : ℕ → Option ℕ) (i t w : ℕ) :
    cnt s i t (w + 1) = cnt s i t w + if s (t + w) = some i then 1 else 0 := by
  unfold cnt
  rw [List.range_succ, List.filter_append]
  by_cases h : s (t + w) = some i <;> simp [h]

theorem cnt_add (s : ℕ → Option ℕ) (i t a b : ℕ) :
    cnt s i t (a + b) = cnt s i t a + cnt s i (t + a) b := by
  induction b with
  | zero => simp [cnt]
  | succ b ih =>
    rw [← add_assoc, cnt_succ, cnt_succ, ih, add_assoc, add_assoc]

theorem cnt_mono_of_imp (s s' : ℕ → Option ℕ) (i i' t w : ℕ)
    (h : ∀ k, k < w → s (t + k) = some i → s' (t + k) = some i') :
    cnt s i t w ≤ cnt s' i' t w := by
  induction w with
  | zero => simp [cnt]
  | succ w ih =>
    rw [cnt_succ, cnt_succ]
    have := ih (fun k hk => h k (by omega))
    by_cases h1 : s (t + w) = some i
    · have h2 := h w (by omega) h1
      simp [h1, h2]; omega
    · simp only [h1, if_false]
      split_ifs <;> omega

theorem serves_mono {s : ℕ → Option ℕ} {i : ℕ} {a a' : ℚ} (ha : 0 < a) (haa : a ≤ a')
    (h : Serves s i a) : Serves s i a' := by
  intro t w
  refine le_trans (Nat.floor_le_floor ?_) (h t w)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) ha haa

/-! ### Lemma A.2 / A.3: relabeling, deletion, monotonicity -/

/-- Relabeling, deletion and monotonicity at once (Lemmas A.2 and A.3): if every entry `B[j]`
of `B` is at least the entry `A[σ j]` of a schedulable list `A`, for an index map `σ` that is
injective on the positions of `B`, then `B` is schedulable. -/
theorem RatSchedulable.of_embed {A B : List ℚ} (σ : ℕ → ℕ)
    (hinj : ∀ j k, j < B.length → k < B.length → σ j = σ k → j = k)
    (hle : ∀ j (hj : j < B.length), ∃ a, A[σ j]? = some a ∧ a ≤ B[j])
    (hA : RatSchedulable A) : RatSchedulable B := by
  classical
  obtain ⟨hpos, s, hs⟩ := hA
  have hσ : ∀ j (hj : j < B.length), ∃ h : σ j < A.length, A[σ j] ≤ B[j] := by
    intro j hj
    obtain ⟨a, ha, hab⟩ := hle j hj
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp ha
    exact ⟨h, hab⟩
  have hApos : ∀ j (hj : j < B.length), 0 < A[σ j]'(hσ j hj).1 :=
    fun j hj => hpos _ (List.getElem_mem _)
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
    exact lt_of_lt_of_le (hApos j hj) (hσ j hj).2
  · let s' : ℕ → Option ℕ := fun t =>
      match s t with
      | none => none
      | some k => if h : ∃ j, j < B.length ∧ σ j = k then some (Classical.choose h) else none
    refine ⟨s', fun j hj => ?_⟩
    have h1 : Serves s (σ j) B[j] :=
      serves_mono (hApos j hj) (hσ j hj).2 (hs (σ j) (hσ j hj).1)
    intro t w
    refine le_trans (h1 t w) (cnt_mono_of_imp s s' _ _ t w fun k _ hk => ?_)
    have hex : ∃ j', j' < B.length ∧ σ j' = σ j := ⟨j, hj, rfl⟩
    have hc := Classical.choose_spec hex
    have := hinj _ _ hc.1 hj hc.2
    simp only [s', hk, dif_pos hex]
    rw [this]

theorem perm_index {α : Type} {A B : List α} (h : A.Perm B) :
    ∃ σ : ℕ → ℕ, (∀ j, j < B.length → σ j < A.length ∧ A[σ j]? = B[j]?) ∧
      ∀ j k, j < B.length → k < B.length → σ j = σ k → j = k := by
  induction h with
  | nil => exact ⟨id, by simp, by simp⟩
  | cons x _ ih =>
    obtain ⟨σ, h1, h2⟩ := ih
    refine ⟨fun j => if j = 0 then 0 else σ (j - 1) + 1, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero => simp
      | succ j =>
        have := h1 j (by simpa using hj)
        simp only [List.length_cons] at hj ⊢
        simp [this.2]; omega
    · intro j k hj hk hjk
      simp only [List.length_cons] at hj hk
      cases j <;> cases k <;> simp at hjk ⊢
      exact h2 _ _ (by omega) (by omega) hjk
  | swap x y l =>
    refine ⟨fun j => if j = 0 then 1 else if j = 1 then 0 else j, ?_, ?_⟩
    · intro j hj
      simp only [List.length_cons] at hj ⊢
      rcases j with _ | _ | j <;> simp
      omega
    · intro j k hj hk hjk
      simp only at hjk
      split_ifs at hjk <;> omega
  | trans _ _ ih1 ih2 =>
    obtain ⟨σ1, a1, b1⟩ := ih1
    obtain ⟨σ2, a2, b2⟩ := ih2
    refine ⟨fun j => σ1 (σ2 j), ?_, ?_⟩
    · intro j hj
      obtain ⟨c1, c2⟩ := a2 j hj
      obtain ⟨d1, d2⟩ := a1 (σ2 j) c1
      exact ⟨d1, d2.trans c2⟩
    · intro j k hj hk h
      exact b2 j k hj hk (b1 _ _ (a2 j hj).1 (a2 k hk).1 h)

/-- Lemma A.2: schedulability is invariant under permutations. -/
theorem RatSchedulable.perm {A B : List ℚ} (h : A.Perm B) (hA : RatSchedulable A) :
    RatSchedulable B := by
  obtain ⟨σ, h1, h2⟩ := perm_index h
  refine RatSchedulable.of_embed σ h2 (fun j hj => ?_) hA
  obtain ⟨c1, c2⟩ := h1 j hj
  exact ⟨B[j], by rw [c2]; simp [hj], le_refl _⟩

/-! ### Lemma A.4: the pair fold -/

/-! ### Lemma A.5: sorting is monotone -/

/-! ### Lemma A.6: folding preserves order -/

/-! ### Corollary A.7: domination certificates -/

end PinwheelDensity.ExactRange.Dev.FoldAux
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.LC3

open PinwheelDensity.ExactRange PinwheelDensity.ExactRange.Dev.FoldAux

/-- The schedule defined by a cyclic word. -/
def sch (w : List ℕ) : ℕ → Option ℕ := fun t => w[t % w.length]?

/-- The extended occurrence function `T(j) = t_{j mod n} + ⌊j/n⌋ N`. -/
def TT (w : List ℕ) (i j : ℕ) : ℕ :=
  (occurrences w i).getD (j % (occurrences w i).length) 0 +
    (j / (occurrences w i).length) * w.length

theorem mem_occ (w : List ℕ) (i x : ℕ) :
    x ∈ occurrences w i ↔ x < w.length ∧ w[x]? = some i := by
  simp [occurrences, List.mem_filter, List.mem_range]

theorem occ_pw (w : List ℕ) (i : ℕ) : (occurrences w i).Pairwise (· < ·) := by
  unfold occurrences
  exact List.Pairwise.filter _ (List.pairwise_lt_range)

theorem occ_lt (w : List ℕ) (i k : ℕ) (hk : k < (occurrences w i).length) :
    (occurrences w i).getD k 0 < w.length := by
  rw [List.getD_eq_getElem _ _ hk]
  exact ((mem_occ w i _).1 (List.getElem_mem hk)).1

theorem occ_mono (w : List ℕ) (i a b : ℕ) (hab : a < b) (hb : b < (occurrences w i).length) :
    (occurrences w i).getD a 0 < (occurrences w i).getD b 0 := by
  have ha : a < (occurrences w i).length := by omega
  rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]
  exact List.pairwise_iff_getElem.1 (occ_pw w i) a b ha hb hab

theorem TT_strict (w : List ℕ) (i : ℕ) (hn : 0 < (occurrences w i).length) {j k : ℕ}
    (hjk : j < k) : TT w i j < TT w i k := by
  unfold TT
  set n := (occurrences w i).length with hn'
  have h1 := occ_lt w i (j % n) (Nat.mod_lt _ hn)
  have h2 := occ_lt w i (k % n) (Nat.mod_lt _ hn)
  rcases Nat.lt_or_ge (j / n) (k / n) with h | h
  · have : (j / n + 1) * w.length ≤ (k / n) * w.length := Nat.mul_le_mul_right _ h
    nlinarith
  · have hjn : j / n = k / n := by
      have : j / n ≤ k / n := Nat.div_le_div_right hjk.le
      omega
    have hm : j % n < k % n := by
      have e1 := Nat.mod_add_div j n
      have e2 := Nat.mod_add_div k n
      rw [hjn] at e1
      have : n * (k / n) = n * (k / n) := rfl
      nlinarith
    have := occ_mono w i _ _ hm (Nat.mod_lt _ hn)
    rw [hjn]; omega

theorem TT_add (w : List ℕ) (i : ℕ) (hn : 0 < (occurrences w i).length) (j : ℕ) :
    TT w i (j + (occurrences w i).length) = TT w i j + w.length := by
  unfold TT
  set n := (occurrences w i).length
  rw [Nat.add_mod_right, Nat.add_div_right _ hn]
  ring

theorem TT_ext (w : List ℕ) (i k : ℕ) (hk : k < 2 * (occurrences w i).length)
    (hn : 0 < (occurrences w i).length) : TT w i k = extOcc w i k := by
  unfold TT extOcc
  simp only
  set n := (occurrences w i).length
  by_cases h : k < n
  · rw [if_pos h, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]; simp
  · rw [if_neg h]
    have : k = (k - n) + n := by omega
    have e : TT w i k = TT w i (k - n) + w.length := by
      conv_lhs => rw [this]
      exact TT_add w i hn _
    unfold TT at e
    rw [e, Nat.mod_eq_of_lt (by omega : k - n < n), Nat.div_eq_of_lt (by omega : k - n < n)]
    simp

theorem sch_iff (w : List ℕ) (i : ℕ) (hN : 0 < w.length) (x : ℕ) :
    sch w x = some i ↔ ∃ j, TT w i j = x ∧ 0 < (occurrences w i).length := by
  constructor
  · intro h
    have hx : x % w.length ∈ occurrences w i :=
      (mem_occ w i _).2 ⟨Nat.mod_lt _ hN, h⟩
    obtain ⟨m, hm, hmx⟩ := List.mem_iff_getElem.1 hx
    have hn : 0 < (occurrences w i).length := by omega
    refine ⟨m + (x / w.length) * (occurrences w i).length, ?_, hn⟩
    unfold TT
    set n := (occurrences w i).length
    have e1 : (m + x / w.length * n) % n = m := by
      rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hm
    have e2 : (m + x / w.length * n) / n = x / w.length := by
      rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hm]; simp
    rw [e1, e2, List.getD_eq_getElem _ _ hm, hmx]
    rw [mul_comm]; exact Nat.mod_add_div x w.length
  · rintro ⟨j, rfl, hn⟩
    have h1 := occ_lt w i (j % (occurrences w i).length) (Nat.mod_lt _ hn)
    have hmem : (occurrences w i).getD (j % (occurrences w i).length) 0 ∈ occurrences w i := by
      rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hn)]; exact List.getElem_mem _
    have := ((mem_occ w i _).1 hmem).2
    unfold sch TT
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
    exact this


/-- The prefix count `F x`. -/
theorem F_spec (w : List ℕ) (i : ℕ) (hN : 0 < w.length) (hn : 0 < (occurrences w i).length)
    (x : ℕ) :
    x ≤ TT w i (cnt (sch w) i 0 x) ∧
      (0 < cnt (sch w) i 0 x → TT w i (cnt (sch w) i 0 x - 1) < x) := by
  induction x with
  | zero => simp [cnt]
  | succ x ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [cnt_succ]
    simp only [zero_add]
    by_cases h : sch w x = some i
    · obtain ⟨j, hj, -⟩ := (sch_iff w i hN x).1 h
      rw [if_pos h]
      have hjF : j = cnt (sch w) i 0 x := by
        have a1 : j ≤ cnt (sch w) i 0 x := by
          by_contra hc
          have := TT_strict w i hn (not_le.1 hc)
          omega
        have a2 : cnt (sch w) i 0 x ≤ j := by
          by_cases hz : 0 < cnt (sch w) i 0 x
          · by_contra hc
            have hle : j ≤ cnt (sch w) i 0 x - 1 := by omega
            have := h2 hz
            rcases hle.eq_or_lt with e | e
            · rw [e] at hj; omega
            · have := TT_strict w i hn e; omega
          · omega
        omega
      subst hjF
      refine ⟨?_, fun _ => ?_⟩
      · have := TT_strict w i hn (show cnt (sch w) i 0 x < cnt (sch w) i 0 x + 1 by omega); omega
      · simp only [Nat.add_sub_cancel]; omega
    · rw [if_neg h]
      refine ⟨?_, fun hp => ?_⟩
      · have : TT w i (cnt (sch w) i 0 x) ≠ x := by
          intro he; exact h ((sch_iff w i hN x).2 ⟨_, he, hn⟩)
        simp only [add_zero]
        omega
      · simp only [add_zero] at hp ⊢; have := h2 hp; omega


theorem gap_ext (w : List ℕ) (i p q : ℕ) (hn : 0 < (occurrences w i).length)
    (hNq : w.length * q ≤ (occurrences w i).length * p)
    (H : ∀ j k, j < k → k < 2 * (occurrences w i).length →
      (((TT w i k : ℕ) : ℤ) - (TT w i j : ℕ) - 1) * (q : ℤ) < ((k : ℤ) - j) * (p : ℤ)) :
    ∀ k j, j < k →
      (((TT w i k : ℕ) : ℤ) - (TT w i j : ℕ) - 1) * (q : ℤ) < ((k : ℤ) - j) * (p : ℤ) := by
  set n := (occurrences w i).length with hn'
  have hNq' : ((w.length : ℕ) : ℤ) * q ≤ (n : ℤ) * p := by exact_mod_cast hNq
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hjk
    by_cases hj : n ≤ j
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + n := ⟨j - n, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + n := ⟨k - n, by omega⟩
      have := ih k' (by omega) j' (by omega)
      rw [TT_add w i hn, TT_add w i hn]
      push_cast
      linarith
    · by_cases hk : k < 2 * n
      · exact H j k hjk hk
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + n := ⟨k - n, by omega⟩
        have := ih k' (by omega) j (by omega)
        rw [TT_add w i hn]
        push_cast
        nlinarith

theorem serves_of_gap (w : List ℕ) (i p q : ℕ) (hq : 0 < q) (hg : gapTest w i p q = true)
    (t W : ℕ) : ⌊(W : ℚ) / ((p : ℚ) / q)⌋₊ ≤ cnt (sch w) i t W := by
  unfold gapTest at hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hg
  obtain ⟨⟨hn1, hNq⟩, H⟩ := hg
  have hn : 0 < (occurrences w i).length := hn1
  have hN : 0 < w.length := by
    have := occ_lt w i 0 hn
    omega
  have hp : 0 < p := by
    by_contra hp
    have : p = 0 := by omega
    subst this
    have : 0 < w.length * q := Nat.mul_pos hN hq
    omega
  have H' : ∀ j k, j < k → k < 2 * (occurrences w i).length →
      (((TT w i k : ℕ) : ℤ) - (TT w i j : ℕ) - 1) * (q : ℤ) < ((k : ℤ) - j) * (p : ℤ) := by
    intro j k hjk hk
    have := H k hk j hjk
    rw [TT_ext w i k hk hn, TT_ext w i j (by omega) hn]
    exact this
  have G := gap_ext w i p q hn hNq H'
  -- shift
  have hshift : cnt (sch w) i t W = cnt (sch w) i (t + w.length) W := by
    unfold cnt
    congr 1
    apply List.filter_congr
    intro k _
    have : t + w.length + k = (t + k) + w.length := by ring
    have e : sch w (t + w.length + k) = sch w (t + k) := by
      unfold sch
      rw [this, Nat.add_mod_right]
    simp only [e]
  rw [hshift]
  set u := t + w.length with hu
  have hadd := cnt_add (sch w) i 0 u W
  simp only [zero_add] at hadd
  obtain ⟨hF1, hF2⟩ := F_spec w i hN hn u
  obtain ⟨hK1, hK2⟩ := F_spec w i hN hn (u + W)
  have hFpos : 0 < cnt (sch w) i 0 u := by
    by_contra hz
    have h0 : cnt (sch w) i 0 u = 0 := by omega
    rw [h0] at hF1
    have := occ_lt w i 0 hn
    simp only [TT, Nat.zero_mod, Nat.zero_div, zero_mul, add_zero] at hF1
    omega
  have hj := hF2 hFpos
  set Fu := cnt (sch w) i 0 u
  set Fk := cnt (sch w) i 0 (u + W)
  set c := cnt (sch w) i u W
  have hGG := G Fk (Fu - 1) (by omega)
  have e1 : ((Fk : ℤ) - ((Fu - 1 : ℕ) : ℤ)) = (c : ℤ) + 1 := by
    have : Fu - 1 + 1 = Fu := by omega
    omega
  rw [e1] at hGG
  have h3 : (W : ℤ) ≤ ((TT w i Fk : ℕ) : ℤ) - (TT w i (Fu - 1) : ℕ) - 1 := by omega
  have h4 : (W : ℤ) * q < ((c : ℤ) + 1) * p := by
    have : (W : ℤ) * q ≤ (((TT w i Fk : ℕ) : ℤ) - (TT w i (Fu - 1) : ℕ) - 1) * q :=
      mul_le_mul_of_nonneg_right h3 (by exact_mod_cast hq.le)
    linarith
  have h5 : W * q < (c + 1) * p := by exact_mod_cast h4
  have h6 : (W : ℚ) / ((p : ℚ) / q) < (c : ℚ) + 1 := by
    have hpq : (0 : ℚ) < p := by exact_mod_cast hp
    have hqq : (0 : ℚ) < q := by exact_mod_cast hq
    rw [div_div_eq_mul_div, div_lt_iff₀ hpq]
    exact_mod_cast h5
  have h7 : ⌊(W : ℚ) / ((p : ℚ) / q)⌋₊ < c + 1 := by
    rw [Nat.floor_lt (by positivity)]
    exact_mod_cast h6
  omega

end PinwheelDensity.ExactRange.Dev.LC3
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.LD3

open PinwheelDensity.ExactRange

/-! ### Lemma D.1: τ̂, span, κ -/

theorem foldr_max_ge (L : List ℕ) (x : ℕ) (hx : x ∈ L) : x ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem foldr_max_le (L : List ℕ) (M : ℕ) (h : ∀ x ∈ L, x ≤ M) : L.foldr max 0 ≤ M := by
  induction L with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldr_cons]
    exact max_le (h y (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem foldr_max_add (L : List ℕ) (hL : L ≠ []) (N : ℕ) :
    (L.map (· + N)).foldr max 0 = L.foldr max 0 + N := by
  induction L with
  | nil => simp at hL
  | cons y l ih =>
    cases l with
    | nil => simp
    | cons z l' =>
      simp only [List.map_cons, List.foldr_cons] at ih ⊢
      rw [ih (by simp)]
      omega

variable (τ : List ℕ) (N : ℕ)

theorem tauHat_lt (hlt : ∀ x ∈ τ, x < N) (hf : 0 < τ.length) (j : ℕ) :
    τ.getD (j % τ.length) 0 < N := by
  rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hf)]
  exact hlt _ (List.getElem_mem _)

theorem tauHat_add_f (hf : 0 < τ.length) (j : ℕ) :
    tauHat τ N (j + τ.length) = tauHat τ N j + N := by
  unfold tauHat
  rw [Nat.add_mod_right, Nat.add_div_right _ hf]
  ring

theorem tauHat_add_mul (hf : 0 < τ.length) (j q : ℕ) :
    tauHat τ N (j + q * τ.length) = tauHat τ N j + q * N := by
  induction q with
  | zero => simp
  | succ q ih =>
    have : j + (q + 1) * τ.length = (j + q * τ.length) + τ.length := by ring
    rw [this, tauHat_add_f τ N hf, ih]; ring

theorem tauHat_strict (hτ : τ.Pairwise (· < ·)) (hlt : ∀ x ∈ τ, x < N) (hf : 0 < τ.length)
    {j k : ℕ} (hjk : j < k) : tauHat τ N j < tauHat τ N k := by
  unfold tauHat
  set n := τ.length with hn'
  have h1 := tauHat_lt τ N hlt hf j
  have h2 := tauHat_lt τ N hlt hf k
  rcases Nat.lt_or_ge (j / n) (k / n) with h | h
  · have : (j / n + 1) * N ≤ (k / n) * N := Nat.mul_le_mul_right _ h
    nlinarith
  · have hjn : j / n = k / n := by
      have : j / n ≤ k / n := Nat.div_le_div_right hjk.le
      omega
    have hm : j % n < k % n := by
      have e1 := Nat.mod_add_div j n
      have e2 := Nat.mod_add_div k n
      rw [hjn] at e1
      nlinarith
    have : τ.getD (j % n) 0 < τ.getD (k % n) 0 := by
      rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hf), List.getD_eq_getElem _ _ (Nat.mod_lt _ hf)]
      exact List.pairwise_iff_getElem.1 hτ _ _ _ _ hm
    rw [hjn]; omega

theorem tauHat_mono (hτ : τ.Pairwise (· < ·)) (hlt : ∀ x ∈ τ, x < N) (hf : 0 < τ.length)
    {j k : ℕ} (hjk : j ≤ k) : tauHat τ N j ≤ tauHat τ N k := by
  rcases hjk.eq_or_lt with h | h
  · rw [h]
  · exact (tauHat_strict τ N hτ hlt hf h).le

theorem len_le_N (hτ : τ.Pairwise (· < ·)) (hlt : ∀ x ∈ τ, x < N) : τ.length ≤ N := by
  have hnd : τ.Nodup := hτ.imp (fun h => h.ne)
  have h1 : τ.toFinset.card = τ.length := List.toFinset_card_of_nodup hnd
  have h2 : τ.toFinset ⊆ Finset.range N := by
    intro x hx; simpa using hlt x (List.mem_toFinset.1 hx)
  have := Finset.card_le_card h2
  simp at this
  omega

theorem span_ge (hτ : τ.Pairwise (· < ·)) (hlt : ∀ x ∈ τ, x < N) (hf : 0 < τ.length)
    (b j : ℕ) : tauHat τ N (j + b) ≤ tauHat τ N j + span τ N b := by
  set f := τ.length with hf'
  have hj : j = j % f + (j / f) * f := by
    rw [mul_comm]; exact (Nat.mod_add_div j f).symm
  have e1 : tauHat τ N j = tauHat τ N (j % f) + (j / f) * N := by
    conv_lhs => rw [hj]
    exact tauHat_add_mul τ N hf _ _
  have e2 : tauHat τ N (j + b) = tauHat τ N (j % f + b) + (j / f) * N := by
    have : j + b = (j % f + b) + (j / f) * f := by omega
    rw [this]; exact tauHat_add_mul τ N hf _ _
  have hmem : tauHat τ N (j % f + b) - tauHat τ N (j % f) ∈
      (List.range f).map fun j => tauHat τ N (j + b) - tauHat τ N j :=
    List.mem_map.2 ⟨j % f, List.mem_range.2 (Nat.mod_lt _ hf), rfl⟩
  have h3 := foldr_max_ge _ _ hmem
  have h4 := tauHat_mono τ N hτ hlt hf (Nat.le_add_right (j % f) b)
  have : span τ N b = ((List.range f).map fun j => tauHat τ N (j + b) - tauHat τ N j).foldr max 0 :=
    rfl
  omega

theorem span_zero (hf : 0 < τ.length) : span τ N 0 = 0 := by
  unfold span
  have : ((List.range τ.length).map fun j => tauHat τ N (j + 0) - tauHat τ N j) =
      (List.range τ.length).map fun _ => 0 := by
    apply List.map_congr_left; intro j _; simp
  rw [this]
  generalize τ.length = n
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.foldr_append] at ih ⊢; simp_all

theorem span_mono (hτ : τ.Pairwise (· < ·)) (hlt : ∀ x ∈ τ, x < N) (hf : 0 < τ.length)
    {b b' : ℕ} (h : b ≤ b') : span τ N b ≤ span τ N b' := by
  unfold span
  apply foldr_max_le
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have := tauHat_mono τ N hτ hlt hf (show j + b ≤ j + b' by omega)
  refine le_trans ?_ (foldr_max_ge _ _ (List.mem_map.2 ⟨j, hj, rfl⟩))
  omega

theorem span_add_f (hτ : τ.Pairwise (· < ·)) (hlt : ∀ x ∈ τ, x < N) (hf : 0 < τ.length)
    (b : ℕ) : span τ N (b + τ.length) = span τ N b + N := by
  unfold span
  have hne : List.range τ.length ≠ [] := by
    rw [Ne, List.range_eq_nil]; omega
  have : ((List.range τ.length).map fun j => tauHat τ N (j + (b + τ.length)) - tauHat τ N j) =
      (((List.range τ.length).map fun j => tauHat τ N (j + b) - tauHat τ N j).map (· + N)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j _
    have h1 : tauHat τ N (j + (b + τ.length)) = tauHat τ N (j + b) + N := by
      rw [← add_assoc]; exact tauHat_add_f τ N hf _
    have h2 := tauHat_mono τ N hτ hlt hf (Nat.le_add_right j b)
    simp only [Function.comp]
    omega
  rw [this, foldr_max_add _ (by simpa using hne)]

/-! ### κ -/

theorem filt_len (P : ℕ → Prop) [DecidablePred P] (hP : ∀ x y, x ≤ y → P y → P x) :
    ∀ a, ((List.range a).filter (fun x => decide (P x))).length ≤ a ∧
      ∀ x < a, (P x ↔ x < ((List.range a).filter (fun x => decide (P x))).length) := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [List.range_succ, List.filter_append]
    set c := ((List.range a).filter (fun x => decide (P x))).length with hc
    by_cases hPa : P a
    · have hall : ∀ x < a, P x := fun x hx => hP x a hx.le hPa
      have hca : c = a := by
        apply le_antisymm h1
        by_contra hlt
        have := (h2 c (by omega)).1 (hall c (by omega))
        omega
      simp only [List.filter_cons, hPa, decide_true, if_true, List.filter_nil, List.length_append,
        List.length_singleton]
      refine ⟨by omega, fun x hx => ?_⟩
      constructor
      · intro _; omega
      · intro _
        rcases Nat.lt_or_ge x a with h | h
        · exact hall x h
        · have : x = a := by omega
          subst this; exact hPa
    · simp only [List.filter_cons, hPa, decide_false, List.filter_nil, List.length_append]
      simp only [Bool.false_eq_true, if_false, List.length_nil, add_zero]
      refine ⟨by omega, fun x hx => ?_⟩
      rcases Nat.lt_or_ge x a with h | h
      · exact h2 x h
      · have : x = a := by omega
        subst this
        constructor
        · intro h; exact absurd h hPa
        · intro h; omega

variable {τ N}

theorem kappa_spec (hτ : τ.Pairwise (· < ·)) (hlt : ∀ x ∈ τ, x < N) (hf : 0 < τ.length)
    (a : ℕ) : kappa τ N a ≤ a ∧ ∀ x < a, (span τ N (x + 1) ≤ a ↔ x < kappa τ N a) := by
  have := filt_len (fun x => span τ N (x + 1) ≤ a)
    (fun x y hxy hy => le_trans (span_mono τ N hτ hlt hf (by omega)) hy) a
  exact this

theorem kappa_span (hτ : τ.Pairwise (· < ·)) (hlt : ∀ x ∈ τ, x < N) (hf : 0 < τ.length)
    (a : ℕ) : span τ N (kappa τ N a) ≤ a := by
  obtain ⟨h1, h2⟩ := kappa_spec hτ hlt hf a
  rcases Nat.eq_zero_or_pos (kappa τ N a) with h | h
  · rw [h, span_zero τ N hf]; omega
  · have := (h2 (kappa τ N a - 1) (by omega)).2 (by omega)
    have e : kappa τ N a - 1 + 1 = kappa τ N a := by omega
    rwa [e] at this

theorem kappa_mono (hτ : τ.Pairwise (· < ·)) (hlt : ∀ x ∈ τ, x < N) (hf : 0 < τ.length)
    {a a' : ℕ} (h : a ≤ a') : kappa τ N a ≤ kappa τ N a' := by
  obtain ⟨h1, -⟩ := kappa_spec hτ hlt hf a
  obtain ⟨-, h2'⟩ := kappa_spec hτ hlt hf a'
  rcases Nat.eq_zero_or_pos (kappa τ N a) with h0 | h0
  · omega
  · have hs := kappa_span hτ hlt hf a
    have := (h2' (kappa τ N a - 1) (by omega)).1
      (by
        have e : kappa τ N a - 1 + 1 = kappa τ N a := by omega
        rw [e]; omega)
    omega

theorem kappa_add_N (hτ : τ.Pairwise (· < ·)) (hlt : ∀ x ∈ τ, x < N) (hf : 0 < τ.length)
    (a : ℕ) : kappa τ N a + τ.length ≤ kappa τ N (a + N) := by
  obtain ⟨h1, -⟩ := kappa_spec hτ hlt hf a
  obtain ⟨-, h2'⟩ := kappa_spec hτ hlt hf (a + N)
  have hfN := len_le_N τ N hτ hlt
  have hs := kappa_span hτ hlt hf a
  have := (h2' (kappa τ N a + τ.length - 1) (by omega)).1
    (by
      have e : kappa τ N a + τ.length - 1 + 1 = kappa τ N a + τ.length := by omega
      rw [e, span_add_f τ N hτ hlt hf]; omega)
  omega

theorem kappa_add_mul (hτ : τ.Pairwise (· < ·)) (hlt : ∀ x ∈ τ, x < N) (hf : 0 < τ.length)
    (a k : ℕ) : kappa τ N a + k * τ.length ≤ kappa τ N (a + k * N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := kappa_add_N hτ hlt hf (a + k * N)
    have e : a + (k + 1) * N = a + k * N + N := by ring
    rw [e]
    nlinarith

/-! ### ρ* -/

theorem foldr_ge_init (L : List ℕ) (h : ℕ → ℚ) (init : ℚ) :
    init ≤ L.foldr (fun i acc => max acc (h i)) init := by
  induction L with
  | nil => simp
  | cons y l ih => simp only [List.foldr_cons]; exact le_trans ih (le_max_left _ _)

theorem foldr_ge_mem (L : List ℕ) (h : ℕ → ℚ) (init : ℚ) (i : ℕ) (hi : i ∈ L) :
    h i ≤ L.foldr (fun i acc => max acc (h i)) init := by
  induction L with
  | nil => simp at hi
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hi with e | e
    · subst e; exact le_max_right _ _
    · exact le_trans (ih e) (le_max_left _ _)

theorem ratio_bound (hτ : τ.Pairwise (· < ·)) (hlt : ∀ x ∈ τ, x < N) (hf : 0 < τ.length)
    (aStar : ℕ) (hk : 1 ≤ kappa τ N aStar) (a : ℕ) (ha : aStar ≤ a) :
    1 ≤ kappa τ N a ∧ (a : ℚ) ≤ rhoStar τ N aStar * (kappa τ N a : ℚ) := by
  have hNpos : 0 < N := lt_of_lt_of_le hf (len_le_N τ N hτ hlt)
  set R := rhoStar τ N aStar with hR
  have hNf : (N : ℚ) / τ.length ≤ R := foldr_ge_init _ _ _
  have hfq : (0 : ℚ) < τ.length := by exact_mod_cast hf
  have hNR : (N : ℚ) ≤ R * τ.length := by
    rw [div_le_iff₀ hfq] at hNf; exact hNf
  have hR0 : 0 ≤ R := le_trans (by positivity) hNf
  have ha'' : a = (aStar + (a - aStar) % N) + (a - aStar) / N * N := by
    have h1 := Nat.mod_add_div (a - aStar) N
    have h2 := Nat.mul_comm N ((a - aStar) / N)
    omega
  have hiN : (a - aStar) % N < N := Nat.mod_lt _ hNpos
  generalize (a - aStar) % N = i at ha'' hiN
  generalize (a - aStar) / N = k at ha''
  have ha' := ha''
  have hmono := kappa_mono hτ hlt hf (show aStar ≤ aStar + i by omega)
  have hk1 : 1 ≤ kappa τ N (aStar + i) := le_trans hk hmono
  have hadd := kappa_add_mul hτ hlt hf (aStar + i) k
  rw [← ha'] at hadd
  refine ⟨by nlinarith [Nat.zero_le (k * τ.length)], ?_⟩
  have hmem : i ∈ List.range N := List.mem_range.2 hiN
  have h1 := foldr_ge_mem (List.range N)
    (fun i => ((aStar + i : ℕ) : ℚ) / (kappa τ N (aStar + i) : ℚ)) ((N : ℚ) / (τ.length : ℚ)) i hmem
  have hkq : (0 : ℚ) < kappa τ N (aStar + i) := by exact_mod_cast hk1
  have h2 : ((aStar + i : ℕ) : ℚ) ≤ R * kappa τ N (aStar + i) := by
    have : ((aStar + i : ℕ) : ℚ) / (kappa τ N (aStar + i) : ℚ) ≤ R := h1
    rwa [div_le_iff₀ hkq] at this
  have hadd' : (kappa τ N (aStar + i) : ℚ) + k * τ.length ≤ kappa τ N a := by exact_mod_cast hadd
  have e : (a : ℚ) = ((aStar + i : ℕ) : ℚ) + k * N := by
    rw [ha']; push_cast; ring
  rw [e]
  have h3 : (k : ℚ) * N ≤ k * (R * τ.length) := mul_le_mul_of_nonneg_left hNR (by positivity)
  nlinarith

end PinwheelDensity.ExactRange.Dev.LD3
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.LD3

open PinwheelDensity.ExactRange PinwheelDensity.ExactRange.Dev.LC3

theorem freePos_mem (w : List ℕ) (k x : ℕ) :
    x ∈ freePositions w k ↔ x < w.length ∧ ∃ a, w[x]? = some a ∧ k ≤ a := by
  unfold freePositions
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    cases hx : w[x]? with
    | none => rw [hx] at h2; simp at h2
    | some a => rw [hx] at h2; exact ⟨a, rfl, by simpa using h2⟩
  · rintro ⟨h1, a, ha, hk⟩
    refine ⟨h1, ?_⟩
    rw [ha]; simpa using hk

theorem freePos_pw (w : List ℕ) (k : ℕ) : (freePositions w k).Pairwise (· < ·) := by
  unfold freePositions
  exact List.Pairwise.filter _ (List.pairwise_lt_range)

theorem freePos_lt (w : List ℕ) (k : ℕ) : ∀ x ∈ freePositions w k, x < w.length := fun x hx =>
  ((freePos_mem w k x).1 hx).1

/-- The schedule obtained by running `k + g j` on the `j`-th free day. -/
noncomputable def comb (w : List ℕ) (k : ℕ) (g : ℕ → ℕ) (t : ℕ) : Option ℕ :=
  open Classical in
  if h : ∃ j, tauHat (freePositions w k) w.length j = t then
    some (k + g (Classical.choose h)) else sch w t

theorem sch_free (w : List ℕ) (k j : ℕ) (hN : 0 < w.length) (hf : 0 < (freePositions w k).length) :
    ∃ a, sch w (tauHat (freePositions w k) w.length j) = some a ∧ k ≤ a := by
  set τ := freePositions w k
  have hlt := freePos_lt w k
  have h1 := tauHat_lt τ w.length hlt hf j
  have hmem : τ.getD (j % τ.length) 0 ∈ τ := by
    rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hf)]; exact List.getElem_mem _
  obtain ⟨-, a, ha, hk⟩ := (freePos_mem w k _).1 hmem
  refine ⟨a, ?_, hk⟩
  unfold sch tauHat
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
  exact ha

theorem comb_word (w : List ℕ) (k : ℕ) (g : ℕ → ℕ) (hN : 0 < w.length)
    (hf : 0 < (freePositions w k).length) (t i : ℕ) (h : sch w t = some i) (hi : i < k) :
    comb w k g t = some i := by
  unfold comb
  rw [dif_neg]
  · exact h
  · rintro ⟨j, hj⟩
    obtain ⟨a, ha, hk⟩ := sch_free w k j hN hf
    rw [hj, h] at ha
    cases ha
    omega

theorem comb_free (w : List ℕ) (k : ℕ) (g : ℕ → ℕ) (hf : 0 < (freePositions w k).length) (j : ℕ) :
    comb w k g (tauHat (freePositions w k) w.length j) = some (k + g j) := by
  unfold comb
  have hex : ∃ j', tauHat (freePositions w k) w.length j' = tauHat (freePositions w k) w.length j :=
    ⟨j, rfl⟩
  rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  have : Classical.choose hex = j := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := tauHat_strict (freePositions w k) w.length (freePos_pw w k) (freePos_lt w k) hf h
      omega
    · have := tauHat_strict (freePositions w k) w.length (freePos_pw w k) (freePos_lt w k) hf h
      omega
  rw [this]

/-- Lemma D.2 (free-slot compression), window form. -/
theorem compress (w : List ℕ) (k : ℕ) (hN : 0 < w.length) (hf : 0 < (freePositions w k).length)
    (T1 : List ℕ) (hκ : ∀ a ∈ T1, 1 ≤ kappa (freePositions w k) w.length a) (g : ℕ → ℕ)
    (hg : ∀ m (hm : m < T1.length), ∀ n, ∃ j, n ≤ j ∧
      j < n + kappa (freePositions w k) w.length T1[m] ∧ g j = m)
    (m : ℕ) (hm : m < T1.length) (t : ℕ) :
    ∃ d, t ≤ d ∧ d < t + T1[m] ∧ comb w k g d = some (k + m) := by
  set τ := freePositions w k with hτdef
  set N := w.length with hNdef
  have hτ := freePos_pw w k
  have hlt := freePos_lt w k
  set a := T1[m] with ha
  have hκa : 1 ≤ kappa τ N a := hκ a (List.getElem_mem hm)
  have hsp : span τ N (kappa τ N a) ≤ a := kappa_span hτ hlt hf a
  have hex : ∃ j, t ≤ tauHat τ N j := by
    refine ⟨t * τ.length, ?_⟩
    have := tauHat_add_mul τ N hf 0 t
    simp only [zero_add] at this
    rw [this]
    nlinarith
  set j0 := Nat.find hex with hj0
  have hj0s : t ≤ tauHat τ N j0 := Nat.find_spec hex
  obtain ⟨j, hj1, hj2, hj3⟩ := hg m hm j0
  refine ⟨tauHat τ N j, ?_, ?_, ?_⟩
  · exact le_trans hj0s (tauHat_mono τ N hτ hlt hf hj1)
  · set κ := kappa τ N a with hκdef
    have hfN := len_le_N τ N hτ hlt
    rcases Nat.eq_zero_or_pos j0 with h0 | h0
    · have hb := span_ge τ N hτ hlt hf κ (τ.length - 1)
      have e : τ.length - 1 + κ = (κ - 1) + τ.length := by omega
      rw [e, tauHat_add_f τ N hf] at hb
      have hl : tauHat τ N (τ.length - 1) < N := by
        have := tauHat_lt τ N hlt hf (τ.length - 1)
        have e2 : tauHat τ N (τ.length - 1) = τ.getD ((τ.length - 1) % τ.length) 0 := by
          unfold tauHat
          rw [Nat.div_eq_of_lt (by omega)]; simp
        omega
      have hm1 := tauHat_mono τ N hτ hlt hf (show j ≤ κ - 1 by omega)
      omega
    · have hmin : ¬ t ≤ tauHat τ N (j0 - 1) := Nat.find_min hex (by omega)
      have hb := span_ge τ N hτ hlt hf κ (j0 - 1)
      have hm1 := tauHat_mono τ N hτ hlt hf (show j ≤ j0 - 1 + κ by omega)
      omega
  · have := comb_free w k g hf j
    rw [hj3] at this
    exact this

end PinwheelDensity.ExactRange.Dev.LD3
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.LD3

open PinwheelDensity.ExactRange PinwheelDensity.ExactRange.Dev.LC3
  PinwheelDensity.ExactRange.Dev.FoldAux

theorem density_append (A B : List ℕ) : density (A ++ B) = density A + density B := by
  simp [density]

theorem density_cons (b : ℕ) (T : List ℕ) : density (b :: T) = 1 / (b : ℚ) + density T := by
  simp [density]

theorem density_eq (A : List ℕ) : density A = (A.map (fun a : ℕ => (1 : ℚ) / (a : ℚ))).sum := by
  induction A with
  | nil => simp [density]
  | cons b l ih => rw [density_cons, ih]; simp

theorem density_perm {A B : List ℕ} (h : A.Perm B) : density A = density B := by
  rw [density_eq, density_eq]; exact (h.map (fun a : ℕ => (1 : ℚ) / (a : ℚ))).sum_eq

theorem density_nonneg (A : List ℕ) : 0 ≤ density A := by
  induction A with
  | nil => simp [density]
  | cons b l ih => rw [density_cons]; positivity

theorem one_div_le_density {a : ℕ} {T : List ℕ} (ha : a ∈ T) : (1 : ℚ) / a ≤ density T := by
  induction T with
  | nil => simp at ha
  | cons b l ih =>
    rw [density_cons]
    rcases List.mem_cons.1 ha with h | h
    · subst h; linarith [density_nonneg l]
    · have : (0 : ℚ) ≤ 1 / (b : ℚ) := by positivity
      linarith [ih h]

theorem ceil_le_of {ε : ℚ} (hε : 0 < ε) {a : ℕ} (ha : 1 ≤ a) (h : (1 : ℚ) / a ≤ ε) :
    ⌈1 / ε⌉₊ ≤ a := by
  have ha0 : (0 : ℚ) < a := by exact_mod_cast ha
  rw [div_le_iff₀ ha0] at h
  apply Nat.ceil_le.2
  rw [div_le_iff₀ hε]
  linarith

theorem wordServes_serves {w : List ℕ} {r : List ℚ} (h : wordServes w r = true) :
    0 < w.length ∧ ∀ i (hi : i < r.length), 0 < r[i] ∧ Serves (sch w) i r[i] := by
  unfold wordServes at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hN, h⟩ := h
  refine ⟨hN, fun i hi => ?_⟩
  have := h i hi
  simp only [List.getElem?_eq_getElem hi, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨hpos, hg⟩ := this
  refine ⟨hpos, fun t W => ?_⟩
  have hnum : ((r[i].num.toNat : ℕ) : ℚ) = (r[i].num : ℚ) := by
    have : 0 ≤ r[i].num := Rat.num_nonneg.2 hpos.le
    exact_mod_cast Int.toNat_of_nonneg this
  have := serves_of_gap w i r[i].num.toNat r[i].den r[i].den_pos hg t W
  rw [hnum, Rat.num_div_den] at this
  exact this

theorem sched_of_serves {w : List ℕ} {r : List ℚ} (h : wordServes w r = true) :
    RatSchedulable r :=
  ⟨fun a ha => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    exact ((wordServes_serves h).2 i hi).1, sch w, fun i hi => ((wordServes_serves h).2 i hi).2⟩

/-- The main case: the tail `T1` lies above `a*`. -/
theorem absorb_main (w S s T1 : List ℕ) (k : ℕ) (hk : S.length + s.length = k) (ρ : ℚ) (aStar : ℕ)
    (hwS : wordServes w (toQ (S ++ s)) = true) (hf : 1 ≤ (freePositions w k).length)
    (hκ : 1 ≤ kappa (freePositions w k) w.length aStar) (hρ0 : 0 < ρ)
    (hρ : ρ * rhoStar (freePositions w k) w.length aStar ≤ 5 / 6)
    (hSs : ∀ a ∈ S ++ s, 1 ≤ a) (hT1pos : ∀ a ∈ T1, 1 ≤ a) (hT1a : ∀ a ∈ T1, aStar ≤ a)
    (hdens : density T1 ≤ ρ) : RatSchedulable (toQ (S ++ s ++ T1)) := by
  classical
  obtain ⟨hN, hser⟩ := wordServes_serves hwS
  set τ := freePositions w k with hτdef
  have hτ := freePos_pw w k
  have hlt := freePos_lt w k
  have hf' : 0 < τ.length := hf
  have hlen : (S ++ s).length = k := by simp [hk]
  have hpos : ∀ a ∈ S ++ s ++ T1, 1 ≤ a := by
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hSs a h
    · exact hT1pos a h
  have hposQ : ∀ a ∈ toQ (S ++ s ++ T1), 0 < a := by
    intro a ha
    rw [toQ_eq] at ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    have := hpos b hb
    exact_mod_cast this
  have hsched : RatSchedulable (toQ (S ++ s)) := sched_of_serves hwS
  by_cases h0 : T1 = []
  · subst h0
    simpa using hsched
  · obtain ⟨a1, ha1⟩ := List.exists_mem_of_ne_nil T1 h0
    have hbound : ∀ a ∈ T1, 1 ≤ kappa τ w.length a ∧
        (a : ℚ) ≤ rhoStar τ w.length aStar * (kappa τ w.length a : ℚ) := fun a ha =>
      ratio_bound hτ hlt hf' aStar hκ a (hT1a a ha)
    have hR0 : 0 ≤ rhoStar τ w.length aStar := by
      unfold rhoStar
      refine le_trans ?_ (foldr_ge_init _ _ _)
      positivity
    have hTlen : 1 ≤ T1.length := List.length_pos_iff.2 (List.ne_nil_of_mem ha1)
    have hsum : ∑ i : Fin T1.length,
        (1 : ℚ) / ((fun i : Fin T1.length => kappa τ w.length T1[i]) i : ℕ) ≤ 5 / 6 := by
      have h1 : ∀ i : Fin T1.length, (1 : ℚ) / (kappa τ w.length T1[i] : ℕ) ≤
          rhoStar τ w.length aStar * ((1 : ℚ) / (T1[i] : ℕ)) := by
        intro i
        obtain ⟨hk1, hk2⟩ := hbound T1[i] (List.getElem_mem i.2)
        have hkq : (0 : ℚ) < kappa τ w.length T1[i] := by exact_mod_cast hk1
        have haq : (0 : ℚ) < T1[i] := by
          have := hT1pos _ (List.getElem_mem i.2); exact_mod_cast this
        rw [mul_one_div, div_le_div_iff₀ hkq haq]
        linarith
      calc ∑ i : Fin T1.length, (1 : ℚ) / ((fun i : Fin T1.length => kappa τ w.length T1[i]) i : ℕ)
          ≤ ∑ i : Fin T1.length, rhoStar τ w.length aStar * ((1 : ℚ) / (T1[i] : ℕ)) :=
            Finset.sum_le_sum fun i _ => h1 i
        _ = rhoStar τ w.length aStar * density T1 := by
            rw [← Finset.mul_sum]
            congr 1
            rw [density_eq]; exact Fin.sum_univ_fun_getElem T1 (fun a : ℕ => (1 : ℚ) / (a : ℚ))
        _ ≤ rhoStar τ w.length aStar * ρ := mul_le_mul_of_nonneg_left hdens hR0
        _ ≤ 5 / 6 := by linarith
    obtain ⟨schedule, hsch⟩ := pinwheel_conjecture T1.length hTlen
      (fun i : Fin T1.length => kappa τ w.length T1[i])
      (fun i => (hbound _ (List.getElem_mem i.2)).1) hsum
    set g : ℕ → ℕ := fun n => (schedule n).val with hg
    have hgw : ∀ m (hm : m < T1.length), ∀ n, ∃ j, n ≤ j ∧
        j < n + kappa τ w.length T1[m] ∧ g j = m := by
      intro m hm n
      obtain ⟨j, h1, h2, h3⟩ := hsch ⟨m, hm⟩ n
      exact ⟨j, h1, h2, by simp [hg, h3]⟩
    have hcomp := compress w k hN hf' T1 (fun a ha => (hbound a ha).1) g hgw
    have hA1 := lemma_A_1
    refine ⟨hposQ, comb w k g, fun i hi => ?_⟩
    by_cases hik : i < k
    · have hiA : i < (toQ (S ++ s)).length := by simp only [toQ_eq, List.length_map]; omega
      obtain ⟨-, hs⟩ := hser i hiA
      have e : (toQ (S ++ s ++ T1))[i] = (toQ (S ++ s))[i] := by
        simp only [toQ_eq, List.getElem_map]
        rw [List.getElem_append_left (by omega)]
      rw [e]
      intro t W
      refine le_trans (hs t W) (cnt_mono_of_imp _ _ _ _ _ _ fun d _ hd => ?_)
      exact comb_word w k g hN hf' (t + d) i hd hik
    · obtain ⟨m, rfl⟩ : ∃ m, i = k + m := ⟨i - k, by omega⟩
      have hm : m < T1.length := by
        simp only [toQ_eq, List.length_map, List.length_append] at hi; omega
      have e : (toQ (S ++ s ++ T1))[k + m] = ((T1[m] : ℕ) : ℚ) := by
        simp only [toQ_eq, List.getElem_map]
        rw [List.getElem_append_right (by omega)]
        have h2 : k + m - (S.length + s.length) = m := by omega
        simp [h2]
      rw [e]
      exact (hA1.1 (comb w k g) (k + m) T1[m] (hT1pos _ (List.getElem_mem hm))).2
        (fun t => hcomp m hm t)

theorem perm_sorted (T : List ℕ) (a0 : ℕ) :
    ((T.filter (fun x => decide (x < a0))).insertionSort (· ≤ ·) ++
      T.filter (fun x => !decide (x < a0))).Perm T := by
  refine List.Perm.trans (List.Perm.append_right _ (List.perm_insertionSort _ _)) ?_
  exact List.filter_append_perm (fun x => decide (x < a0)) T

end PinwheelDensity.ExactRange.Dev.LD3

namespace PinwheelDensity.ExactRange

open Dev.LD3 Dev.LC3 Dev.FoldAux in
theorem chk_prop_D_3 (B : ℚ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (S : List ℕ) (hS : ∀ a ∈ S, 1 ≤ a)
    (δ : ℚ) (hδ : δ = B - density S) (hδpos : 0 < δ) (l a₀ lStar : ℕ)
    (hlStar : lStar = max l ⌈1 / δ⌉₊)
    (hcases : ∀ s : List ℕ, s.Pairwise (· ≤ ·) → (∀ x ∈ s, lStar ≤ x ∧ x < a₀) → density s ≤ δ →
      ∃ w : List ℕ, absorbCaseOK δ S s w a₀ = true)
    (T : List ℕ) (hT : ∀ a ∈ T, 1 ≤ a ∧ l ≤ a) (hdens : density (S ++ T) ≤ B) :
    Schedulable (S ++ T) := by
  classical
  have hdT : density T ≤ δ := by
    have := density_append S T; linarith
  have hTpos : ∀ a ∈ T, 1 ≤ a := fun a ha => (hT a ha).1
  have hlS : ∀ a ∈ T, lStar ≤ a := by
    intro a ha
    rw [hlStar]
    refine max_le (hT a ha).2 (ceil_le_of hδpos (hTpos a ha) ?_)
    exact le_trans (one_div_le_density ha) hdT
  set s := (T.filter (fun x => decide (x < a₀))).insertionSort (· ≤ ·) with hs
  set T1 := T.filter (fun x => !decide (x < a₀)) with hT1
  have hperm : (s ++ T1).Perm T := perm_sorted T a₀
  have hsmem : ∀ x ∈ s, x ∈ T ∧ x < a₀ := by
    intro x hx
    have : x ∈ T.filter (fun x => decide (x < a₀)) := (List.perm_insertionSort _ _).subset hx
    simpa using this
  have hT1mem : ∀ x ∈ T1, x ∈ T ∧ a₀ ≤ x := by
    intro x hx
    have := List.mem_filter.1 hx
    simpa using this
  have hdsplit : density T = density s + density T1 := by
    rw [← density_perm hperm, density_append]
  have hds : density s ≤ δ := by
    have := density_nonneg T1; linarith
  have hsorted : s.Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
  obtain ⟨w, hw⟩ := hcases s hsorted (fun x hx => ⟨hlS x (hsmem x hx).1, (hsmem x hx).2⟩) hds
  have hSs : ∀ a ∈ S ++ s, 1 ≤ a := by
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hS a h
    · exact hTpos a (hsmem a h).1
  have hposQ : ∀ a ∈ S ++ T, 1 ≤ a := by
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hS a h
    · exact hTpos a h
  have hperm' : (toQ (S ++ s ++ T1)).Perm (toQ (S ++ T)) := by
    have : (S ++ s ++ T1).Perm (S ++ T) := by
      rw [List.append_assoc]; exact List.Perm.append_left S hperm
    rw [toQ_eq, toQ_eq]; exact this.map _
  have hfin : RatSchedulable (toQ (S ++ s ++ T1)) → Schedulable (S ++ T) := fun h =>
    ((lemma_A_1.2.1 (S ++ T) hposQ).1 (RatSchedulable.perm hperm' h))
  apply hfin
  have hwS : wordServes w (toQ (S ++ s)) = true := by
    unfold absorbCaseOK at hw
    simp only [Bool.and_eq_true] at hw
    exact hw.1
  have hd1 : density T1 ≤ δ - density s := by linarith
  have hT1pos : ∀ a ∈ T1, 1 ≤ a := fun a ha => hTpos a (hT1mem a ha).1
  by_cases hT1e : T1 = []
  · rw [hT1e]
    simpa using sched_of_serves hwS
  · obtain ⟨a1, ha1⟩ := List.exists_mem_of_ne_nil T1 hT1e
    unfold absorbCaseOK at hw
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hw
    obtain ⟨-, hw2⟩ := hw
    rcases hw2 with h0 | ⟨⟨⟨hρ0, hf⟩, hκ⟩, hρ⟩
    · exfalso
      have := one_div_le_density ha1
      have hpos : (0 : ℚ) < 1 / (a1 : ℚ) := by
        have : (0 : ℚ) < a1 := by exact_mod_cast hT1pos a1 ha1
        positivity
      linarith
    · refine absorb_main w S s T1 (S.length + s.length) rfl (δ - density s)
        (max a₀ ⌈1 / (δ - density s)⌉₊) hwS hf hκ hρ0 hρ hSs hT1pos (fun a ha => ?_) hd1
      refine max_le_iff.2 ⟨(hT1mem a ha).2, ceil_le_of hρ0 (hT1pos a ha) ?_⟩
      exact le_trans (one_div_le_density ha) hd1

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_prop_D_3 := @PinwheelDensity.ExactRange.chk_prop_D_3
