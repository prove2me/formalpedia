-- Prove2me | solution 1 for TSPHeuristics.Insertion.insert_le_clog_add_one_mul_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T22:52:20.662926+00:00
-- url     : https://prove2.me/submissions/25009634-58c4-445b-ae2e-4926a7920897

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

lemma PS_append {n : ℕ} (d : Fin n → Fin n → ℝ) (L1 : List (Fin n)) :
    ∀ (x z y : Fin n) (L2 : List (Fin n)), PS d x (L1 ++ z :: L2) y = PS d x L1 z + PS d z L2 y := by
  induction L1 with
  | nil => intro x z y L2; simp [PS_cons, PS_nil]
  | cons h L ih => intro x z y L2; rw [List.cons_append, PS_cons, PS_cons, ih]; ring

lemma cycle_swap {n : ℕ} (d : Fin n → Fin n → ℝ) (A B : List (Fin n)) :
    cycleLength d (A ++ B) = cycleLength d (B ++ A) := by
  rcases A with _ | ⟨x, A'⟩
  · simp
  rcases B with _ | ⟨z, B'⟩
  · simp
  rw [List.cons_append, List.cons_append, cycle_cons, cycle_cons, PS_append, PS_append]
  ring

lemma PS_le {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (k j : Fin n) (B : List (Fin n)) :
    PS d k B j ≤ d k j + PS d j B j := by
  rcases B with _ | ⟨h, B'⟩
  · simp [PS_nil, hd.diag]
  · rw [PS_cons, PS_cons]; linarith [hd.triangle k j h]

lemma insertIdx_split {α : Type*} (A B : List α) (j k : α) :
    (A ++ j :: B).insertIdx (A.length + 1) k = A ++ j :: k :: B := by
  induction A with
  | nil => simp
  | cons x A ih => simp [List.insertIdx_succ_cons, ih]

lemma lemma2_core {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d)
    (T : List (Fin n)) (k j : Fin n) (hj : j ∈ T) :
    insCost d T k ≤ 2 * d k j := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hj
  unfold insCost
  have hmem : A.length + 1 ∈ Finset.range ((A ++ j :: B).length + 1) := by
    simp
  have h1 := Finset.inf'_le (fun pos => cycleLength d ((A ++ j :: B).insertIdx pos k)
    - cycleLength d (A ++ j :: B)) hmem
  rw [insertIdx_split] at h1
  have e1 : cycleLength d (A ++ j :: k :: B) = d j k + PS d k (B ++ A) j := by
    rw [cycle_swap, List.cons_append, List.cons_append, cycle_cons, PS_cons]
  have e2 : cycleLength d (A ++ j :: B) = PS d j (B ++ A) j := by
    rw [cycle_swap, List.cons_append, cycle_cons]
  have := PS_le d hd k j (B ++ A)
  rw [hd.symm j k] at e1
  linarith

theorem insertion_cost_eq {n : ℕ} (d : Fin n → Fin n → ℝ) (T : List (Fin n)) (k : Fin n)
    (T' : List (Fin n)) (h : IsInsertion d T k T') :
    insCost d T k = cycleLength d T' - cycleLength d T := by
  obtain ⟨_, pos, hpos, rfl, hmin⟩ := h
  unfold insCost
  apply le_antisymm
  · exact Finset.inf'_le (fun pos => cycleLength d (T.insertIdx pos k) - cycleLength d T)
      (Finset.mem_range.mpr (by omega))
  · apply Finset.le_inf'
    intro p hp
    exact sub_le_sub_right (hmin p (by simpa [Nat.lt_succ_iff] using hp)) _

theorem eq37_core {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    cycleLength d (T n) = ∑ i ∈ Finset.Ico 1 n, insCost d (T i) (a i) := by
  have key : ∀ m, 1 ≤ m → m ≤ n → cycleLength d (T m) = ∑ i ∈ Finset.Ico 1 m, insCost d (T i) (a i) := by
    intro m hm1 hmn
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0; rw [hrun.1]; simp [cycleLength, hd.diag]
      · rw [Finset.sum_Ico_succ_top hpos, ← ih hpos (by omega),
          insertion_cost_eq d _ _ _ (hrun.2 m hpos (by omega))]
        ring
  exact key n hn le_rfl

lemma run_mem {n : ℕ} (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n)
    (hrun : IsInsertionRun d T a) :
    ∀ j, 1 ≤ j → j ≤ n → ∀ x, x ∈ T j ↔ ∃ i < j, a i = x := by
  intro j hj hjn
  induction j with
  | zero => omega
  | succ j ih =>
    intro x
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; rw [hrun.1]; simp [eq_comm]
    · obtain ⟨_, pos, hpos', hT, _⟩ := hrun.2 j hpos (by omega)
      rw [hT, List.mem_insertIdx hpos', ih hpos (by omega)]
      constructor
      · rintro (h | ⟨i, hi, rfl⟩)
        · exact ⟨j, by omega, h.symm⟩
        · exact ⟨i, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact Or.inr ⟨i, h, rfl⟩
        · exact Or.inl (by rw [h])

lemma run_mem_iff {n : ℕ} (d : Fin n → Fin n → ℝ) (T : ℕ → List (Fin n)) (a : ℕ → Fin n)
    (hrun : IsInsertionRun d T a) :
    ∀ j, 1 ≤ j → j ≤ n → ∀ i, i < n → (a i ∈ T j ↔ i < j) := by
  intro j hj hjn i hi
  rw [run_mem d T a hrun j hj hjn]
  constructor
  · rintro ⟨i', hi', he⟩
    by_contra hij
    have h1 : 1 ≤ i := by omega
    have hnot := (hrun.2 i h1 hi).1
    apply hnot
    rw [run_mem d T a hrun i h1 hi.le]
    exact ⟨i', by omega, he⟩
  · intro h; exact ⟨i, h, rfl⟩

lemma pair_le {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ) (hd : IsTSPDist d) (x y : Fin n) :
    2 * d x y ≤ optimal d := by
  by_cases hxy : x = y
  · subst hxy; rw [hd.diag]; linarith [optimal_nonneg hn d hd]
  obtain ⟨τ, hτ⟩ := exists_opt_tour hn d
  set W := List.ofFn τ with hW
  have hWnd : W.Nodup := List.nodup_ofFn.mpr τ.injective
  have hWmem : ∀ p, p ∈ W := fun p => List.mem_ofFn.mpr ⟨τ.symm p, by simp⟩
  set L := W.filter (fun z => decide (z = x ∨ z = y)) with hL
  have hLsub : L.Sublist W := List.filter_sublist
  have hLnd : L.Nodup := hWnd.filter _
  have hLmem : ∀ p, p ∈ L ↔ (p = x ∨ p = y) := by
    intro p; rw [hL, List.mem_filter]; simp [hWmem p]
  have hts : L.toFinset = {x, y} := by
    ext p; simp [hLmem p]
  have hlen : L.length = 2 := by
    rw [← List.toFinset_card_of_nodup hLnd, hts, Finset.card_pair hxy]
  obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hlen
  have hc : cycleLength d L ≤ optimal d := by
    rw [hτ]; apply cycle_sublist d hd L W hLsub; rw [huv]; simp
  have hcl : cycleLength d L = d u v + d v u := by
    rw [huv]; simp [cycleLength]
  have hu := (hLmem u).mp (by rw [huv]; simp)
  have hv := (hLmem v).mp (by rw [huv]; simp)
  have hne : u ≠ v := by
    intro h; rw [huv, h] at hLnd; simp at hLnd
  rw [hcl] at hc
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl hne
  · linarith [hd.symm u v]
  · linarith [hd.symm u v]
  · exact absurd rfl hne

theorem goal_core {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    cycleLength d (T n) ≤ ((Nat.clog 2 n : ℝ) + 1) * optimal d := by
  have hO := optimal_nonneg hn d hd
  let c : ℕ → ℝ := fun i => if 1 ≤ i then insCost d (T i) (a i) else 0
  let A : Fin n → Fin n := fun i => a i.val
  have hA : Function.Injective A := by
    have key : ∀ i j : ℕ, i < j → j < n → a i ≠ a j := by
      intro i j hij hjn h
      have h1 : a i ∈ T j := (run_mem_iff d T a hrun j (by omega) hjn.le i (by omega)).mpr hij
      rw [h] at h1
      exact (hrun.2 j (by omega) hjn).1 h1
    intro i j h
    simp only [A] at h
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact absurd h (key _ _ hlt j.isLt)
    · exact Fin.ext heq
    · exact absurd h.symm (key _ _ hgt i.isLt)
  let e : Fin n ≃ Fin n := Equiv.ofBijective A hA.bijective_of_finite
  have he : ∀ i, e i = a i.val := fun i => rfl
  let l : Fin n → ℝ := fun p => c (e.symm p).val / 2
  have hl : ∀ i : Fin n, l (a i.val) = c i.val / 2 := by
    intro i; simp only [l]; rw [← he, Equiv.symm_apply_apply]
  have hcost : ∀ j, 1 ≤ j → j < n → ∀ i, i < j → c j ≤ 2 * d (a j) (a i) := by
    intro j hj hjn i hij
    simp only [c, if_pos hj]
    exact lemma2_core d hd (T j) (a j) (a i)
      ((run_mem_iff d T a hrun j hj hjn.le i (by omega)).mpr hij)
  have ha : ∀ p q, p ≠ q → min (l p) (l q) ≤ d p q := by
    intro p q hpq
    obtain ⟨i, rfl⟩ := e.surjective p
    obtain ⟨j, rfl⟩ := e.surjective q
    rw [he, he, hl, hl]
    have hij : i.val ≠ j.val := by intro h; apply hpq; rw [Fin.ext h]
    rcases lt_or_gt_of_ne hij with h | h
    · have := hcost j.val (by omega) j.isLt i.val h
      rw [hd.symm] at this
      exact (min_le_right _ _).trans (by linarith)
    · have := hcost i.val (by omega) i.isLt j.val h
      exact (min_le_left _ _).trans (by linarith)
  have hb : ∀ p, l p ≤ optimal d / 2 := by
    intro p
    obtain ⟨i, rfl⟩ := e.surjective p
    rw [he, hl]
    by_cases hi : 1 ≤ i.val
    · have := hcost i.val hi i.isLt 0 (by omega)
      have := pair_le hn d hd (a i.val) (a 0)
      linarith
    · simp only [c, if_neg hi]; linarith
  have hL1 := lemma1_core hn d hd l ha hb
  have hsum : ∑ p, l p = (∑ i ∈ Finset.Ico 1 n, insCost d (T i) (a i)) / 2 := by
    rw [← Equiv.sum_comp e]
    simp only [he, hl]
    rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun i => c i) n, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [c, if_neg (by omega : ¬ 1 ≤ 0), zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi; simp at hi; rw [if_pos hi.1]
  rw [eq37_core hn d hd T a hrun]
  rw [hsum] at hL1
  linarith

end TSPHeuristics.Insertion

open TSPHeuristics.Insertion


theorem solution {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : IsInsertionRun d T a) :
    TSPHeuristics.Shared.cycleLength d (T n) ≤ ((Nat.clog 2 n : ℝ) + 1) * TSPHeuristics.Shared.optimal d := by
  exact goal_core hn d hd T a hrun
