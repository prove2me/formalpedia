-- Prove2me | solution 1 for TSPHeuristics.Insertion.lemma_1_sum_le_half_clog_add_one_mul_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T22:49:29.396265+00:00
-- url     : https://prove2.me/submissions/b5746265-273c-4c9c-9ee0-0d2f3da05e1d

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_TSPModel
import Definitions.Def_TSPHeuristics_Insertion_InsertionMethod

open Classical

namespace TSPHeuristics.Insertion

open TSPHeuristics.Shared

/-- path sum from x through L to y -/
def PS {n : ℕ} (d : Fin n → Fin n → ℝ) (x : Fin n) (L : List (Fin n)) (y : Fin n) : ℝ :=
  (List.zipWith d (x :: L) (L ++ [y])).sum

lemma PS_nil {n : ℕ} (d : Fin n → Fin n → ℝ) (x y : Fin n) : PS d x [] y = d x y := by
  simp [PS]

lemma PS_cons {n : ℕ} (d : Fin n → Fin n → ℝ) (x h y : Fin n) (L : List (Fin n)) :
    PS d x (h :: L) y = d x h + PS d h L y := by
  simp [PS]

lemma cycle_cons {n : ℕ} (d : Fin n → Fin n → ℝ) (x : Fin n) (L : List (Fin n)) :
    cycleLength d (x :: L) = PS d x L x := by
  simp [cycleLength, PS]

lemma PS_detour {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (x b y : Fin n)
    (M : List (Fin n)) : PS d x M y ≤ d x b + PS d b M y := by
  rcases M with _ | ⟨h, M'⟩
  · simp only [PS_nil]; exact hd.triangle x b y
  · rw [PS_cons, PS_cons]; linarith [hd.triangle x b h]

lemma PS_sublist {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) {L M : List (Fin n)}
    (h : L.Sublist M) : ∀ x y, PS d x L y ≤ PS d x M y := by
  induction h with
  | slnil => intro x y; exact le_rfl
  | cons b h ih =>
    intro x y
    rw [PS_cons]
    exact (ih x y).trans (PS_detour d hd x b y _)
  | cons_cons b h ih =>
    intro x y
    rw [PS_cons, PS_cons]; linarith [ih b y]

lemma PS_end {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (L : List (Fin n)) :
    ∀ x y z, PS d x L y ≤ PS d x L z + d z y := by
  induction L with
  | nil => intro x y z; simp only [PS_nil]; exact hd.triangle x z y
  | cons h L ih => intro x y z; rw [PS_cons, PS_cons]; linarith [ih h y z]

lemma cycle_sublist {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (L W : List (Fin n))
    (h : L.Sublist W) (hL : L ≠ []) : cycleLength d L ≤ cycleLength d W := by
  rcases W with _ | ⟨w, W'⟩
  · exact absurd (List.sublist_nil.mp h) hL
  rcases List.sublist_cons_iff.mp h with h1 | ⟨r, rfl, hr⟩
  · rcases L with _ | ⟨y, r⟩
    · exact absurd rfl hL
    rw [cycle_cons, cycle_cons]
    have e1 := PS_end d hd r y y w
    have e2 := PS_sublist d hd h1 w w
    rw [PS_cons] at e2
    linarith [hd.symm w y]
  · rw [cycle_cons, cycle_cons]
    exact PS_sublist d hd hr w w

lemma zipWith_ofFn_sum {n : ℕ} (d : Fin n → Fin n → ℝ) (f g : Fin n → Fin n) :
    (List.zipWith d (List.ofFn f) (List.ofFn g)).sum = ∑ i, d (f i) (g i) := by
  have : List.zipWith d (List.ofFn f) (List.ofFn g) = List.ofFn (fun i => d (f i) (g i)) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2; simp
  rw [this, List.sum_ofFn]

lemma cycle_ofFn {n : ℕ} (d : Fin n → Fin n → ℝ) (τ : Equiv.Perm (Fin n)) :
    cycleLength d (List.ofFn τ) = tourLength d τ := by
  unfold cycleLength tourLength
  have hr : (List.ofFn τ).rotate 1 = List.ofFn (fun i => τ (finRotate n i)) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.getElem_rotate]
      simp only [List.getElem_ofFn, List.length_ofFn]
      congr 1
      obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by simp at h2; omega⟩
      apply Fin.ext
      rw [finRotate_succ_apply, Fin.val_add_one]
      simp at h2
      split_ifs with hh
      · have : i = N := by
          have := congrArg Fin.val hh; simpa using this
        subst this; simp
      · have : i ≠ N := by
          intro h; apply hh; apply Fin.ext; simp [h]
        simp; omega
  rw [hr, zipWith_ofFn_sum]

lemma exists_opt_tour {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ) :
    ∃ τ : Equiv.Perm (Fin n), optimal d = cycleLength d (List.ofFn τ) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨τ, -, hτ⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Equiv.Perm (Fin n)))
    (tourLength d)
  exact ⟨τ, by rw [cycle_ofFn]; exact hτ⟩

lemma optimal_nonneg {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) :
    0 ≤ optimal d := by
  unfold optimal
  apply Finset.le_inf'
  intro τ _
  unfold tourLength
  exact Finset.sum_nonneg (fun k _ => hd.nonneg _ _)

lemma zip_le {α : Type*} (g g' : α → α → ℝ) :
    ∀ (L L' : List α), (∀ i (h1 : i < L.length) (h2 : i < L'.length), g L[i] L'[i] ≤ g' L[i] L'[i]) →
    (List.zipWith g L L').sum ≤ (List.zipWith g' L L').sum := by
  intro L
  induction L with
  | nil => intro L' _; simp
  | cons x L ih =>
    intro L' h
    rcases L' with _ | ⟨y, L'⟩
    · simp
    · simp only [List.zipWith_cons_cons, List.sum_cons]
      have h0 := h 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at h0
      have := ih L' (fun i h1 h2 => by
        have := h (i+1) (by simp; omega) (by simp; omega)
        simpa using this)
      linarith

lemma zip_add {α : Type*} (f g : α → ℝ) :
    ∀ (L L' : List α), L.length = L'.length →
    (List.zipWith (fun p q => f p + g q) L L').sum = (L.map f).sum + (L'.map g).sum := by
  intro L
  induction L with
  | nil => intro L' h; rcases L' with _ | _ <;> simp_all
  | cons x L ih =>
    intro L' h
    rcases L' with _ | ⟨y, L'⟩
    · simp at h
    · simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons]
      rw [ih L' (by simpa using h)]; ring

/-- Key block inequality. -/
lemma block_core {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (l : Fin n → ℝ)
    (ha : ∀ p q, p ≠ q → min (l p) (l q) ≤ d p q) (hl0 : ∀ p, 0 ≤ l p)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ i j : Fin n, i ≤ j → l (σ j) ≤ l (σ i))
    (V : ℕ → ℝ) (hV : ∀ i (h : i < n), V i = l (σ ⟨i, h⟩))
    (k M : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) (hM2 : M ≤ 2 * k) (hMn : M ≤ n) (hM : 2 ≤ M) :
    2 * ∑ i ∈ Finset.Ico k M, V i ≤ optimal d := by
  obtain ⟨τ, hτ⟩ := exists_opt_tour hn d
  set W := List.ofFn τ with hW
  have hWnd : W.Nodup := List.nodup_ofFn.mpr τ.injective
  have hWmem : ∀ p, p ∈ W := fun p => List.mem_ofFn.mpr ⟨τ.symm p, by simp⟩
  let r : Fin n → ℕ := fun p => (σ.symm p).val
  set L := W.filter (fun p => decide (r p < M)) with hL
  have hLsub : L.Sublist W := List.filter_sublist
  have hLnd : L.Nodup := hWnd.filter _
  have hLmem : ∀ p, p ∈ L ↔ r p < M := by
    intro p; rw [hL, List.mem_filter]; simp [hWmem p]
  set θ := V (k - 1) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ, hV (k-1) (by omega)]; exact hl0 _
  have hlp : ∀ p, l p = V (r p) := by
    intro p; rw [hV (r p) (σ.symm p).isLt]; simp [r]
  have hbig : ∀ p, r p < k → θ ≤ l p := by
    intro p hp
    rw [hθ, hV (k-1) (by omega)]
    have := hσ (σ.symm p) ⟨k-1, by omega⟩ (by simp only [Fin.le_def]; simp only [r] at hp; omega)
    simpa using this
  have hsmall : ∀ p, k ≤ r p → l p ≤ θ := by
    intro p hp
    rw [hθ, hV (k-1) (by omega)]
    have := hσ ⟨k-1, by omega⟩ (σ.symm p) (by simp only [Fin.le_def]; simp only [r] at hp; omega)
    simpa using this
  let φ : Fin n → ℝ := fun p => if r p < k then θ / 2 else l p - θ / 2
  have hedge : ∀ p q, p ≠ q → r p < M → r q < M → φ p + φ q ≤ d p q := by
    intro p q hpq _ _
    refine le_trans ?_ (ha p q hpq)
    apply le_min
    · simp only [φ]
      split_ifs with h1 h2 h2
      · linarith [hbig p h1]
      · linarith [hsmall q (by omega), hbig p h1]
      · linarith [hbig q h2, hsmall p (by omega)]
      · linarith [hsmall q (by omega)]
    · simp only [φ]
      split_ifs with h1 h2 h2
      · linarith [hbig q h2]
      · linarith [hsmall q (by omega), hbig p h1]
      · linarith [hsmall p (by omega), hbig q h2]
      · linarith [hsmall p (by omega)]
  -- length ≥ 2
  have hlen : 2 ≤ L.length := by
    have hx : σ ⟨0, by omega⟩ ∈ L := by rw [hLmem]; simp [r]; omega
    have hy : σ ⟨1, by omega⟩ ∈ L := by rw [hLmem]; simp [r]; omega
    have hxy : σ ⟨0, by omega⟩ ≠ σ ⟨1, by omega⟩ := by
      intro h; have := congrArg Fin.val (σ.injective h); simp at this
    rw [← List.toFinset_card_of_nodup hLnd]
    have : ({σ ⟨0, by omega⟩, σ ⟨1, by omega⟩} : Finset (Fin n)) ⊆ L.toFinset := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [List.mem_toFinset]; rcases hz with rfl | rfl <;> assumption
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair hxy] at h2
    exact h2
  -- edge sum bound
  have hzip : (List.zipWith (fun p q => φ p + φ q) L (L.rotate 1)).sum ≤ cycleLength d L := by
    unfold cycleLength
    apply zip_le
    intro i h1 h2
    rw [List.getElem_rotate]
    apply hedge
    · rw [Ne, hLnd.getElem_inj_iff]
      by_cases hi : i + 1 < L.length
      · rw [Nat.mod_eq_of_lt hi]; omega
      · have : i + 1 = L.length := by omega
        rw [this, Nat.mod_self]; omega
    · exact (hLmem _).mp (List.getElem_mem _)
    · exact (hLmem _).mp (List.getElem_mem _)
  have hcyc : cycleLength d L ≤ optimal d := by
    rw [hτ]
    apply cycle_sublist d hd L W hLsub
    intro h; rw [h] at hlen; simp at hlen
  rw [zip_add φ φ L (L.rotate 1) (by simp)] at hzip
  have hrot : ((L.rotate 1).map φ).sum = (L.map φ).sum :=
    ((List.rotate_perm L 1).map φ).sum_eq
  rw [hrot] at hzip
  -- compute (L.map φ).sum
  have hsum : (L.map φ).sum = ∑ i ∈ Finset.range n,
      (if i < M then (if i < k then θ / 2 else V i - θ / 2) else 0) := by
    rw [← List.sum_toFinset φ hLnd]
    have hts : L.toFinset = Finset.univ.filter (fun p => r p < M) := by
      ext p; simp [hLmem p]
    rw [hts, Finset.sum_filter, ← Equiv.sum_comp σ]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hri : r (σ i) = i.val := by simp [r]
    simp only [φ, hri]
    rw [hlp (σ i), hri]
  have hsplit : ∑ i ∈ Finset.range n,
      (if i < M then (if i < k then θ / 2 else V i - θ / 2) else 0)
      = (k : ℝ) * (θ / 2) + ∑ i ∈ Finset.Ico k M, V i - ((M - k : ℕ) : ℝ) * (θ / 2) := by
    rw [← Finset.sum_range_add_sum_Ico _ hMn, ← Finset.sum_range_add_sum_Ico _ hkM]
    have e1 : ∑ i ∈ Finset.Ico M n, (if i < M then (if i < k then θ / 2 else V i - θ / 2) else 0)
        = 0 := by
      apply Finset.sum_eq_zero; intro i hi; simp at hi; rw [if_neg (by omega)]
    have e2 : ∑ i ∈ Finset.range k, (if i < M then (if i < k then θ / 2 else V i - θ / 2) else 0)
        = (k : ℝ) * (θ / 2) := by
      rw [Finset.sum_congr rfl (g := fun _ => θ / 2)]
      · simp
      · intro i hi; simp at hi; rw [if_pos (by omega), if_pos hi]
    have e3 : ∑ i ∈ Finset.Ico k M, (if i < M then (if i < k then θ / 2 else V i - θ / 2) else 0)
        = ∑ i ∈ Finset.Ico k M, (V i - θ / 2) := by
      apply Finset.sum_congr rfl; intro i hi; simp at hi; rw [if_pos (by omega), if_neg (by omega)]
    rw [e1, e2, e3, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, add_zero]
    ring
  have hcast : ((M - k : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega : M - k ≤ k)
  rw [hsum, hsplit] at hzip
  nlinarith

theorem lemma1_nonneg {n : ℕ} (hn : 1 ≤ n)
    (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (l : Fin n → ℝ)
    (ha : ∀ p q, p ≠ q → min (l p) (l q) ≤ d p q)
    (hb : ∀ p, l p ≤ optimal d / 2) (hl0 : ∀ p, 0 ≤ l p) :
    ∑ p, l p ≤ (1 / 2) * ((Nat.clog 2 n : ℝ) + 1) * optimal d := by
  have hO := optimal_nonneg hn d hd
  set σ := Tuple.sort (fun p => -l p) with hσdef
  have hσ : ∀ i j : Fin n, i ≤ j → l (σ j) ≤ l (σ i) := by
    intro i j hij
    have := Tuple.monotone_sort (fun p => -l p) hij
    simp only [Function.comp] at this
    linarith
  let V : ℕ → ℝ := fun i => if h : i < n then l (σ ⟨i, h⟩) else 0
  have hV : ∀ i (h : i < n), V i = l (σ ⟨i, h⟩) := by intro i h; simp [V, h]
  have htot : ∑ p, l p = ∑ i ∈ Finset.range n, V i := by
    rw [← Equiv.sum_comp σ, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl; intro i _; rw [hV i.val i.isLt]
  have key : ∀ j : ℕ, ∑ i ∈ Finset.range (min (2 ^ j) n), V i ≤ ((j : ℝ) + 1) * (optimal d / 2) := by
    intro j
    induction j with
    | zero =>
      have : min (2 ^ 0) n = 1 := by simp; omega
      rw [this, Finset.sum_range_one, hV 0 (by omega)]
      simp; exact hb _
    | succ j ih =>
      have hab : min (2 ^ j) n ≤ min (2 ^ (j+1)) n := by
        apply min_le_min_right; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← Finset.sum_range_add_sum_Ico _ hab]
      by_cases hc : n ≤ 2 ^ j
      · have e1 : min (2 ^ j) n = n := min_eq_right hc
        have e2 : min (2 ^ (j+1)) n = n := min_eq_right (by rw [pow_succ]; omega)
        rw [e1, e2, Finset.Ico_self, Finset.sum_empty]
        rw [e1] at ih
        push_cast; nlinarith
      · push_neg at hc
        have e1 : min (2 ^ j) n = 2 ^ j := min_eq_left hc.le
        rw [e1] at ih ⊢
        have hpos : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        have hb2 := block_core hn d hd l ha hl0 σ hσ V hV (2 ^ j) (min (2 ^ (j+1)) n) hpos
          (by rw [pow_succ]; omega) (by rw [pow_succ]; omega) (min_le_right _ _)
          (by rw [pow_succ]; omega)
        push_cast; linarith
  have hc := key (Nat.clog 2 n)
  rw [min_eq_right (Nat.le_pow_clog (by norm_num) n)] at hc
  rw [htot]; linarith

theorem lemma1_core {n : ℕ} (hn : 1 ≤ n)
    (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (l : Fin n → ℝ)
    (ha : ∀ p q, p ≠ q → min (l p) (l q) ≤ d p q)
    (hb : ∀ p, l p ≤ optimal d / 2) :
    ∑ p, l p ≤ (1 / 2) * ((Nat.clog 2 n : ℝ) + 1) * optimal d := by
  have hO := optimal_nonneg hn d hd
  have h := lemma1_nonneg hn d hd (fun p => max (l p) 0)
    (by
      intro p q hpq
      have h1 := ha p q hpq
      rw [← max_min_distrib_right]
      exact max_le h1 (hd.nonneg p q))
    (fun p => max_le (hb p) (by linarith)) (fun p => le_max_right _ _)
  refine le_trans ?_ h
  exact Finset.sum_le_sum (fun p _ => le_max_left _ _)

end TSPHeuristics.Insertion

open TSPHeuristics.Insertion


theorem solution {n : ℕ} (hn : 1 ≤ n)
    (d : Fin n → Fin n → ℝ) (hd : TSPHeuristics.Shared.IsTSPDist d) (l : Fin n → ℝ)
    (ha : ∀ p q, p ≠ q → min (l p) (l q) ≤ d p q)
    (hb : ∀ p, l p ≤ TSPHeuristics.Shared.optimal d / 2) :
    ∑ p, l p ≤ (1 / 2) * ((Nat.clog 2 n : ℝ) + 1) * TSPHeuristics.Shared.optimal d := by
  exact lemma1_core hn d hd l ha hb
