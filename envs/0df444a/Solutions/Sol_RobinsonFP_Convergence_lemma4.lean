-- Prove2me | solution 1 for RobinsonFP.Convergence.lemma4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:44:15.112748+00:00
-- url     : https://prove2.me/submissions/0cb55c61-a3a2-4977-a95a-1b5658bdd66a

import Mathlib
import Definitions.Def_RobinsonFP_Convergence_VectorSystem

open Filter Topology

namespace RobinsonFP.Convergence

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem rb_le_vmax [Nonempty ι] (w : ι → ℝ) (i : ι) : w i ≤ vmax w :=
  Finset.le_sup' w (Finset.mem_univ i)

theorem rb_vmax_le [Nonempty ι] {w : ι → ℝ} {c : ℝ} (h : ∀ i, w i ≤ c) : vmax w ≤ c :=
  Finset.sup'_le _ _ (fun i _ => h i)

theorem rb_vmin_le [Nonempty ι] (w : ι → ℝ) (i : ι) : vmin w ≤ w i :=
  Finset.inf'_le w (Finset.mem_univ i)

theorem rb_le_vmin [Nonempty ι] {w : ι → ℝ} {c : ℝ} (h : ∀ i, c ≤ w i) : c ≤ vmin w :=
  Finset.le_inf' _ _ (fun i _ => h i)

theorem rb_exists_eq_vmax [Nonempty ι] (w : ι → ℝ) : ∃ i, w i = vmax w := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) w
  exact ⟨i, hi.symm⟩

theorem rb_exists_eq_vmin [Nonempty ι] (w : ι → ℝ) : ∃ i, w i = vmin w := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι)) w
  exact ⟨i, hi.symm⟩

theorem rb_vmax_neg [Nonempty ι] (w : ι → ℝ) : vmax (fun i => - w i) = - vmin w := by
  apply le_antisymm
  · apply rb_vmax_le
    intro i
    have := rb_vmin_le w i
    linarith
  · obtain ⟨i, hi⟩ := rb_exists_eq_vmin w
    have := rb_le_vmax (fun i => - w i) i
    linarith

theorem rb_vmin_neg [Nonempty ι] (w : ι → ℝ) : vmin (fun i => - w i) = - vmax w := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := rb_exists_eq_vmax w
    have := rb_vmin_le (fun i => - w i) i
    linarith
  · apply rb_le_vmin
    intro i
    have := rb_le_vmax w i
    linarith

theorem rb_gap_step [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) (t : ℕ) :
    vmax (V t) - vmin (U t) ≤ vmax (V (t + 1)) - vmin (U (t + 1)) := by
  obtain ⟨i, j, hi, hj, hU, hV⟩ := h.2 t
  have e1 : V (t + 1) i = V t i + A i j := by simpa using congrFun hV i
  have e2 : U (t + 1) j = U t j + A i j := by simpa using congrFun hU j
  have h1 := rb_le_vmax (V (t + 1)) i
  have h2 := rb_vmin_le (U (t + 1)) j
  linarith

theorem rb_gap_mono [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) :
    Monotone (fun t => vmax (V t) - vmin (U t)) :=
  monotone_nat_of_le_succ (fun t => rb_gap_step h t)

theorem rb_gap_nonneg [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) (t : ℕ) :
    0 ≤ vmax (V t) - vmin (U t) := by
  have := rb_gap_mono h (Nat.zero_le t)
  have h0 : vmax (V 0) - vmin (U 0) = 0 := by rw [h.1]; ring
  simp only at this
  linarith
theorem rb_U_lip [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) {a : ℝ} (ha : ∀ i j, |A i j| ≤ a)
    (j : κ) (t₂ d : ℕ) : |U (t₂ + d) j - U t₂ j| ≤ a * d := by
  induction d with
  | zero => simp
  | succ d ih =>
    obtain ⟨i, j', _, _, hU, _⟩ := h.2 (t₂ + d)
    have e : U (t₂ + (d + 1)) j = U (t₂ + d) j + A i j := by
      have := congrFun hU j
      simpa [← add_assoc] using this
    have h1 := abs_le.mp ih
    have h2 := abs_le.mp (ha i j)
    rw [abs_le]
    push_cast
    constructor <;> nlinarith

theorem rb_V_lip [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) {a : ℝ} (ha : ∀ i j, |A i j| ≤ a)
    (i : ι) (t₂ d : ℕ) : |V (t₂ + d) i - V t₂ i| ≤ a * d := by
  induction d with
  | zero => simp
  | succ d ih =>
    obtain ⟨i', j, _, _, _, hV⟩ := h.2 (t₂ + d)
    have e : V (t₂ + (d + 1)) i = V (t₂ + d) i + A i j := by
      have := congrFun hV i
      simpa [← add_assoc] using this
    have h1 := abs_le.mp ih
    have h2 := abs_le.mp (ha i j)
    rw [abs_le]
    push_cast
    constructor <;> nlinarith

theorem rb_lemma2 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (a : ℝ) (ha : ∀ i j, |A i j| ≤ a)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s t : ℕ)
    (hrow : ∀ i, RowEligible V i s (s + t)) (hcol : ∀ j, ColEligible U j s (s + t)) :
    vmax (U (s + t)) - vmin (U (s + t)) ≤ 2 * a * t ∧
      vmax (V (s + t)) - vmin (V (s + t)) ≤ 2 * a * t := by
  have ha0 : 0 ≤ a :=
    le_trans (abs_nonneg _) (ha (Classical.arbitrary ι) (Classical.arbitrary κ))
  constructor
  · obtain ⟨j, hj⟩ := rb_exists_eq_vmax (U (s + t))
    obtain ⟨t₂, h1, h2, h3⟩ := hcol j
    obtain ⟨d, hd⟩ : ∃ d, s + t = t₂ + d := ⟨s + t - t₂, by omega⟩
    have hdt : (d : ℝ) ≤ t := by exact_mod_cast (by omega : d ≤ t)
    have had : a * d ≤ a * t := mul_le_mul_of_nonneg_left hdt ha0
    have hlj := abs_le.mp (rb_U_lip hUV ha j t₂ d)
    have key : ∀ k, U (s + t) j - 2 * a * t ≤ U (s + t) k := by
      intro k
      have hk := abs_le.mp (rb_U_lip hUV ha k t₂ d)
      have hmin := rb_vmin_le (U t₂) k
      rw [hd]
      linarith
    have := rb_le_vmin key
    linarith
  · obtain ⟨i, hi⟩ := rb_exists_eq_vmin (V (s + t))
    obtain ⟨t₁, h1, h2, h3⟩ := hrow i
    obtain ⟨d, hd⟩ : ∃ d, s + t = t₁ + d := ⟨s + t - t₁, by omega⟩
    have hdt : (d : ℝ) ≤ t := by exact_mod_cast (by omega : d ≤ t)
    have had : a * d ≤ a * t := mul_le_mul_of_nonneg_left hdt ha0
    have hli := abs_le.mp (rb_V_lip hUV ha i t₁ d)
    have key : ∀ k, V (s + t) k ≤ V (s + t) i + 2 * a * t := by
      intro k
      have hk := abs_le.mp (rb_V_lip hUV ha k t₁ d)
      have hmax := rb_le_vmax (V t₁) k
      rw [hd]
      linarith
    have := rb_vmax_le key
    linarith
theorem rb_vmin_V_le_vmax_U [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) (T : ℕ) :
    vmin (V T) ≤ vmax (U T) := by
  choose i j hi hj hU hV using h.2
  have hUf : ∀ t l, U t l = U 0 l + ∑ τ ∈ Finset.range t, A (i τ) l := by
    intro t l
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.sum_range_succ]
      have := congrFun (hU t) l
      simp at this
      linarith
  have hVf : ∀ t l, V t l = V 0 l + ∑ σ ∈ Finset.range t, A l (j σ) := by
    intro t l
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.sum_range_succ]
      have := congrFun (hV t) l
      simp at this
      linarith
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · obtain ⟨i0, h0⟩ := rb_exists_eq_vmax (V 0)
    have j0 : κ := Classical.arbitrary κ
    exact (rb_vmin_le _ i0).trans (h0.le.trans (h.1.symm.le.trans
      ((rb_vmin_le _ j0).trans (rb_le_vmax _ j0))))
  · have e1 : (T : ℝ) * vmin (V T) ≤ ∑ τ ∈ Finset.range T, V T (i τ) := by
      calc (T : ℝ) * vmin (V T) = ∑ τ ∈ Finset.range T, vmin (V T) := by simp
        _ ≤ _ := Finset.sum_le_sum fun τ _ => rb_vmin_le _ _
    have e2 : ∑ σ ∈ Finset.range T, U T (j σ) ≤ (T : ℝ) * vmax (U T) := by
      calc ∑ σ ∈ Finset.range T, U T (j σ) ≤ ∑ σ ∈ Finset.range T, vmax (U T) :=
            Finset.sum_le_sum fun σ _ => rb_le_vmax _ _
        _ = _ := by simp
    have e3 : ∑ τ ∈ Finset.range T, V 0 (i τ) ≤ (T : ℝ) * vmax (V 0) := by
      calc ∑ τ ∈ Finset.range T, V 0 (i τ) ≤ ∑ τ ∈ Finset.range T, vmax (V 0) :=
            Finset.sum_le_sum fun τ _ => rb_le_vmax _ _
        _ = _ := by simp
    have e4 : (T : ℝ) * vmin (U 0) ≤ ∑ σ ∈ Finset.range T, U 0 (j σ) := by
      calc (T : ℝ) * vmin (U 0) = ∑ σ ∈ Finset.range T, vmin (U 0) := by simp
        _ ≤ _ := Finset.sum_le_sum fun σ _ => rb_vmin_le _ _
    have e5 : ∑ τ ∈ Finset.range T, V T (i τ) = ∑ τ ∈ Finset.range T, V 0 (i τ)
        + ∑ τ ∈ Finset.range T, ∑ σ ∈ Finset.range T, A (i τ) (j σ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun τ _ => hVf T (i τ))
    have e6 : ∑ σ ∈ Finset.range T, U T (j σ) = ∑ σ ∈ Finset.range T, U 0 (j σ)
        + ∑ σ ∈ Finset.range T, ∑ τ ∈ Finset.range T, A (i τ) (j σ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun σ _ => hUf T (j σ))
    have e7 : ∑ σ ∈ Finset.range T, ∑ τ ∈ Finset.range T, A (i τ) (j σ)
        = ∑ τ ∈ Finset.range T, ∑ σ ∈ Finset.range T, A (i τ) (j σ) := Finset.sum_comm
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    have h1 : (T : ℝ) * vmin (U 0) = T * vmax (V 0) := by rw [h.1]
    have : (T : ℝ) * vmin (V T) ≤ (T : ℝ) * vmax (U T) := by linarith
    exact le_of_mul_le_mul_left this hTpos

theorem rb_lemma3 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (a : ℝ) (ha : ∀ i j, |A i j| ≤ a)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s t : ℕ)
    (hrow : ∀ i, RowEligible V i s (s + t)) (hcol : ∀ j, ColEligible U j s (s + t)) :
    vmax (V (s + t)) - vmin (U (s + t)) ≤ 4 * a * t := by
  obtain ⟨h1, h2⟩ := rb_lemma2 A a ha U V hUV s t hrow hcol
  have := rb_vmin_V_le_vmax_U hUV (s + t)
  linarith
def rbSeq {α : Type*} (orig : ℕ → α) (nxt : α → α) (T : ℕ) : ℕ → α
  | 0 => orig 0
  | n + 1 => if n < T then orig (n + 1) else nxt (rbSeq orig nxt T n)

theorem rbSeq_orig {α : Type*} (orig : ℕ → α) (nxt : α → α) (T : ℕ) :
    ∀ n, n ≤ T → rbSeq orig nxt T n = orig n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    show (if n < T then orig (n + 1) else nxt (rbSeq orig nxt T n)) = orig (n + 1)
    rw [if_pos (by omega)]

theorem rb_extend {ι' κ' : Type*} [Fintype ι'] [Fintype κ'] [Nonempty ι'] [Nonempty κ']
    (A : Matrix ι' κ' ℝ) (U₀ : ℕ → κ' → ℝ) (V₀ : ℕ → ι' → ℝ) (T : ℕ)
    (h0 : vmin (U₀ 0) = vmax (V₀ 0))
    (hstep : ∀ τ, τ < T → ∃ i j, V₀ τ i = vmax (V₀ τ) ∧ U₀ τ j = vmin (U₀ τ) ∧
        U₀ (τ + 1) = U₀ τ + A i ∧ V₀ (τ + 1) = V₀ τ + fun k => A k j) :
    ∃ (U' : ℕ → κ' → ℝ) (V' : ℕ → ι' → ℝ), IsVectorSystem A U' V' ∧
      ∀ τ, τ ≤ T → U' τ = U₀ τ ∧ V' τ = V₀ τ := by
  have hex : ∀ st : (κ' → ℝ) × (ι' → ℝ), ∃ nx : (κ' → ℝ) × (ι' → ℝ), ∃ i j,
      st.2 i = vmax st.2 ∧ st.1 j = vmin st.1 ∧ nx.1 = st.1 + A i ∧
      nx.2 = st.2 + fun k => A k j := by
    intro st
    obtain ⟨i, hi⟩ := rb_exists_eq_vmax st.2
    obtain ⟨j, hj⟩ := rb_exists_eq_vmin st.1
    exact ⟨(st.1 + A i, st.2 + fun k => A k j), i, j, hi, hj, rfl, rfl⟩
  choose nxt hnxt using hex
  have hΦ := rbSeq_orig (fun τ => (U₀ τ, V₀ τ)) nxt T
  refine ⟨fun τ => (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ).1,
    fun τ => (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ).2, ⟨?_, ?_⟩, ?_⟩
  · show vmin ((rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T 0).1) =
      vmax ((rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T 0).2)
    rw [hΦ 0 (Nat.zero_le _)]
    exact h0
  · intro τ
    by_cases hτ : τ < T
    · obtain ⟨i, j, h1, h2, h3, h4⟩ := hstep τ hτ
      refine ⟨i, j, ?_, ?_, ?_, ?_⟩
      · show (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ).2 i = vmax (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ).2
        rw [hΦ τ hτ.le]; exact h1
      · show (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ).1 j = vmin (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ).1
        rw [hΦ τ hτ.le]; exact h2
      · show (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T (τ + 1)).1 =
          (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ).1 + A i
        rw [hΦ τ hτ.le, hΦ (τ + 1) hτ]; exact h3
      · show (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T (τ + 1)).2 =
          (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ).2 + fun k => A k j
        rw [hΦ τ hτ.le, hΦ (τ + 1) hτ]; exact h4
    · have e : rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T (τ + 1)
          = nxt (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ) := by
        show (if τ < T then (U₀ (τ + 1), V₀ (τ + 1))
          else nxt (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ)) = _
        rw [if_neg hτ]
      obtain ⟨i, j, h1, h2, h3, h4⟩ := hnxt (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ)
      refine ⟨i, j, h1, h2, ?_, ?_⟩
      · show (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T (τ + 1)).1 =
          (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ).1 + A i
        rw [e]; exact h3
      · show (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T (τ + 1)).2 =
          (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ).2 + fun k => A k j
        rw [e]; exact h4
  · intro τ hτ
    show (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ).1 = U₀ τ ∧
      (rbSeq (fun τ => (U₀ τ, V₀ τ)) nxt T τ).2 = V₀ τ
    rw [hΦ τ hτ]
    exact ⟨rfl, rfl⟩

theorem rb_vmax_sub [Nonempty ι] [DecidableEq ι] (w : ι → ℝ) (k : ι) (c : ℝ)
    (hk : w k < vmax w) [Nonempty {i // i ≠ k}] :
    vmax (fun i : {i // i ≠ k} => w i.1 + c) = vmax w + c := by
  apply le_antisymm
  · apply rb_vmax_le
    intro i
    have := rb_le_vmax w i.1
    linarith
  · obtain ⟨i0, hi0⟩ := rb_exists_eq_vmax w
    have hne : i0 ≠ k := by
      intro h
      rw [h] at hi0
      linarith
    have := rb_le_vmax (fun i : {i // i ≠ k} => w i.1 + c) ⟨i0, hne⟩
    simp only at this
    linarith

theorem rb_transfer_row [DecidableEq ι] [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ}
    {U : ℕ → κ → ℝ} {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) (s T : ℕ) (k : ι)
    [Nonempty {i // i ≠ k}]
    (hk : ∀ τ, τ ≤ T → V (s + τ) k < vmax (V (s + τ))) :
    ∃ (U' : ℕ → κ → ℝ) (V' : ℕ → {i // i ≠ k} → ℝ),
      IsVectorSystem (A.submatrix Subtype.val id) U' V' ∧
      ∀ τ, τ ≤ T → vmax (V' τ) - vmin (U' τ) =
        (vmax (V (s + τ)) - vmin (U (s + τ))) - (vmax (V s) - vmin (U s)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = vmin (U s) - vmax (V s) := ⟨_, rfl⟩
  have hvm : ∀ τ, τ ≤ T →
      vmax (fun i : {i // i ≠ k} => V (s + τ) i.1 + c) = vmax (V (s + τ)) + c :=
    fun τ hτ => rb_vmax_sub (V (s + τ)) k c (hk τ hτ)
  obtain ⟨U', V', hsys, hev⟩ := rb_extend (A.submatrix Subtype.val id)
    (fun τ => U (s + τ)) (fun τ (i : {i // i ≠ k}) => V (s + τ) i.1 + c) T
    (by
      show vmin (U (s + 0)) = vmax (fun i : {i // i ≠ k} => V (s + 0) i.1 + c)
      rw [hvm 0 (Nat.zero_le _), add_zero, hc]
      ring)
    (by
      intro τ hτ
      obtain ⟨i, j, hi, hj, hU, hV⟩ := h.2 (s + τ)
      have hik : i ≠ k := by
        intro hh
        have := hk τ hτ.le
        rw [hh] at hi
        linarith
      refine ⟨⟨i, hik⟩, j, ?_, ?_, ?_, ?_⟩
      · show V (s + τ) i + c = vmax (fun i : {i // i ≠ k} => V (s + τ) i.1 + c)
        rw [hvm τ hτ.le, hi]
      · exact hj
      · show U (s + (τ + 1)) = U (s + τ) + A i
        exact hU
      · funext l
        have := congrFun hV l.1
        simp only [Pi.add_apply] at this ⊢
        show V (s + (τ + 1)) l.1 + c = V (s + τ) l.1 + c + A l.1 j
        rw [show s + (τ + 1) = s + τ + 1 from rfl, this]
        ring)
  refine ⟨U', V', hsys, ?_⟩
  intro τ hτ
  obtain ⟨e1, e2⟩ := hev τ hτ
  rw [e1, e2]
  show vmax (fun i : {i // i ≠ k} => V (s + τ) i.1 + c) - vmin (U (s + τ)) = _
  rw [hvm τ hτ, hc]
  ring

def rbDual (A : Matrix ι κ ℝ) : Matrix κ ι ℝ := fun j i => - A i j

theorem rb_dual_system [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ} {U : ℕ → κ → ℝ}
    {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) :
    IsVectorSystem (rbDual A) (fun t i => - V t i) (fun t j => - U t j) := by
  refine ⟨?_, fun t => ?_⟩
  · show vmin (fun i => - V 0 i) = vmax (fun j => - U 0 j)
    rw [rb_vmin_neg, rb_vmax_neg, h.1]
  · obtain ⟨i, j, hi, hj, hU, hV⟩ := h.2 t
    refine ⟨j, i, ?_, ?_, ?_, ?_⟩
    · show -U t j = vmax (fun j => -U t j)
      rw [rb_vmax_neg, hj]
    · show -V t i = vmin (fun i => -V t i)
      rw [rb_vmin_neg, hi]
    · funext l
      have := congrFun hV l
      simp only [Pi.add_apply] at this
      show -V (t + 1) l = -V t l + -A l j
      rw [this]; ring
    · funext l
      have := congrFun hU l
      simp only [Pi.add_apply] at this
      show -U (t + 1) l = -U t l + -A i l
      rw [this]; ring

theorem rb_transfer_col [DecidableEq κ] [Nonempty ι] [Nonempty κ] {A : Matrix ι κ ℝ}
    {U : ℕ → κ → ℝ} {V : ℕ → ι → ℝ} (h : IsVectorSystem A U V) (s T : ℕ) (k : κ)
    [Nonempty {j // j ≠ k}]
    (hk : ∀ τ, τ ≤ T → vmin (U (s + τ)) < U (s + τ) k) :
    ∃ (U' : ℕ → {j // j ≠ k} → ℝ) (V' : ℕ → ι → ℝ),
      IsVectorSystem (A.submatrix id Subtype.val) U' V' ∧
      ∀ τ, τ ≤ T → vmax (V' τ) - vmin (U' τ) =
        (vmax (V (s + τ)) - vmin (U (s + τ))) - (vmax (V s) - vmin (U s)) := by
  have hd := rb_dual_system h
  obtain ⟨Ud, Vd, hsys, hgap⟩ := rb_transfer_row (A := rbDual A) hd s T k
    (by
      intro τ hτ
      have := hk τ hτ
      show -U (s + τ) k < vmax (fun j => -U (s + τ) j)
      rw [rb_vmax_neg]
      linarith)
  have hsys2 := rb_dual_system hsys
  have hm : rbDual ((rbDual A).submatrix (Subtype.val : {j // j ≠ k} → κ) id)
      = A.submatrix id (Subtype.val : {j // j ≠ k} → κ) := by
    ext i j
    simp [rbDual, Matrix.submatrix]
  rw [hm] at hsys2
  refine ⟨fun t j => - Vd t j, fun t i => - Ud t i, hsys2, ?_⟩
  intro τ hτ
  have g := hgap τ hτ
  show vmax (fun i => - Ud τ i) - vmin (fun j => - Vd τ j) = _
  rw [rb_vmax_neg, rb_vmin_neg]
  rw [rb_vmax_neg, rb_vmin_neg, rb_vmax_neg, rb_vmin_neg] at g
  linarith
theorem rb_eq3 [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
    (ε : ℝ) (hε : 0 < ε) (tstar : ℕ)
    (hrowIH : ∀ k : ι, ∀ (_ : Nonempty {i // i ≠ k}) (U' : ℕ → κ → ℝ)
      (V' : ℕ → {i // i ≠ k} → ℝ),
      IsVectorSystem (A.submatrix Subtype.val id) U' V' →
        ∀ t : ℕ, tstar ≤ t → vmax (V' t) - vmin (U' t) < ε / 2 * t)
    (hcolIH : ∀ k : κ, ∀ (_ : Nonempty {j // j ≠ k}) (U' : ℕ → {j // j ≠ k} → ℝ)
      (V' : ℕ → ι → ℝ),
      IsVectorSystem (A.submatrix id Subtype.val) U' V' →
        ∀ t : ℕ, tstar ≤ t → vmax (V' t) - vmin (U' t) < ε / 2 * t)
    (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ) (hUV : IsVectorSystem A U V) (s : ℕ)
    (hnot : (∃ i, ¬ RowEligible V i s (s + tstar)) ∨ (∃ j, ¬ ColEligible U j s (s + tstar))) :
    vmax (V (s + tstar)) - vmin (U (s + tstar)) <
      vmax (V s) - vmin (U s) + ε / 2 * tstar := by
  rcases hnot with ⟨i, hi⟩ | ⟨j, hj⟩
  · have hk : ∀ τ, τ ≤ tstar → V (s + τ) i < vmax (V (s + τ)) := by
      intro τ hτ
      refine lt_of_le_of_ne (rb_le_vmax _ _) ?_
      intro heq
      exact hi ⟨s + τ, by omega, by omega, heq⟩
    obtain ⟨i0, hi0⟩ := rb_exists_eq_vmax (V s)
    have hne : Nonempty {i' // i' ≠ i} := ⟨⟨i0, fun h => by
      have := hk 0 (Nat.zero_le _)
      rw [add_zero, ← h, hi0] at this
      exact lt_irrefl _ this⟩⟩
    obtain ⟨U', V', hsys, hgap⟩ := rb_transfer_row hUV s tstar i hk
    have h1 := hgap tstar le_rfl
    have h2 := hrowIH i hne U' V' hsys tstar le_rfl
    linarith
  · have hk : ∀ τ, τ ≤ tstar → vmin (U (s + τ)) < U (s + τ) j := by
      intro τ hτ
      refine lt_of_le_of_ne (rb_vmin_le _ _) ?_
      intro heq
      exact hj ⟨s + τ, by omega, by omega, heq.symm⟩
    obtain ⟨j0, hj0⟩ := rb_exists_eq_vmin (U s)
    have hne : Nonempty {j' // j' ≠ j} := ⟨⟨j0, fun h => by
      have := hk 0 (Nat.zero_le _)
      rw [add_zero, ← h, hj0] at this
      exact lt_irrefl _ this⟩⟩
    obtain ⟨U', V', hsys, hgap⟩ := rb_transfer_col hUV s tstar j hk
    have h1 := hgap tstar le_rfl
    have h2 := hcolIH j hne U' V' hsys tstar le_rfl
    linarith
universe u v

theorem rb_lemma4_aux : ∀ (n : ℕ) (α : Type u) (β : Type v) [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β], Fintype.card α + Fintype.card β ≤ n →
    ∀ (A : Matrix α β ℝ) (ε : ℝ), 0 < ε → ∃ t₀ : ℕ, ∀ (U : ℕ → β → ℝ) (V : ℕ → α → ℝ),
      IsVectorSystem A U V → ∀ t : ℕ, t₀ ≤ t → vmax (V t) - vmin (U t) < ε * t := by
  intro n
  induction n with
  | zero =>
    intro α β _ _ _ _ hcard
    exfalso
    have h1 := Fintype.card_pos (α := α)
    omega
  | succ n ih =>
    intro α β _ _ _ _ hcard A ε hε
    classical
    have hrow : ∀ k : α, ∃ t₀ : ℕ, ∀ (_ : Nonempty {i // i ≠ k}) (U' : ℕ → β → ℝ)
        (V' : ℕ → {i // i ≠ k} → ℝ), IsVectorSystem (A.submatrix Subtype.val id) U' V' →
        ∀ t : ℕ, t₀ ≤ t → vmax (V' t) - vmin (U' t) < ε / 2 * t := by
      intro k
      by_cases hne : Nonempty {i // i ≠ k}
      · have hlt : Fintype.card {i // i ≠ k} < Fintype.card α :=
          Fintype.card_subtype_lt (p := fun i => i ≠ k) (x := k) (by simp)
        obtain ⟨t₀, ht⟩ := ih {i // i ≠ k} β (by omega) (A.submatrix Subtype.val id) (ε / 2)
          (by positivity)
        exact ⟨t₀, fun _ U' V' hs t htt => ht U' V' hs t htt⟩
      · exact ⟨0, fun h => absurd h hne⟩
    have hcol : ∀ k : β, ∃ t₀ : ℕ, ∀ (_ : Nonempty {j // j ≠ k}) (U' : ℕ → {j // j ≠ k} → ℝ)
        (V' : ℕ → α → ℝ), IsVectorSystem (A.submatrix id Subtype.val) U' V' →
        ∀ t : ℕ, t₀ ≤ t → vmax (V' t) - vmin (U' t) < ε / 2 * t := by
      intro k
      by_cases hne : Nonempty {j // j ≠ k}
      · have hlt : Fintype.card {j // j ≠ k} < Fintype.card β :=
          Fintype.card_subtype_lt (p := fun j => j ≠ k) (x := k) (by simp)
        obtain ⟨t₀, ht⟩ := ih α {j // j ≠ k} (by omega) (A.submatrix id Subtype.val) (ε / 2)
          (by positivity)
        exact ⟨t₀, fun _ U' V' hs t htt => ht U' V' hs t htt⟩
      · exact ⟨0, fun h => absurd h hne⟩
    choose tr htr using hrow
    choose tc htc using hcol
    obtain ⟨T, hT⟩ : ∃ T : ℕ, T = 1 + ∑ k, tr k + ∑ k, tc k := ⟨_, rfl⟩
    have hTr : ∀ k, tr k ≤ T := fun k => by
      have := Finset.single_le_sum (f := tr) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      omega
    have hTc : ∀ k, tc k ≤ T := fun k => by
      have := Finset.single_le_sum (f := tc) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      omega
    have hT1 : 1 ≤ T := by omega
    obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = ∑ i, ∑ j, |A i j| := ⟨_, rfl⟩
    have ha : ∀ i j, |A i j| ≤ a := by
      intro i j
      rw [ha_def]
      calc |A i j| ≤ ∑ j', |A i j'| :=
            Finset.single_le_sum (f := fun j' => |A i j'|) (fun _ _ => abs_nonneg _)
              (Finset.mem_univ j)
        _ ≤ ∑ i', ∑ j', |A i' j'| :=
            Finset.single_le_sum (f := fun i' => ∑ j', |A i' j'|)
              (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)
    have ha0 : 0 ≤ a :=
      le_trans (abs_nonneg _) (ha (Classical.arbitrary α) (Classical.arbitrary β))
    have hTr' : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    have hstep : ∀ (U : ℕ → β → ℝ) (V : ℕ → α → ℝ), IsVectorSystem A U V → ∀ s : ℕ,
        vmax (V (s + T)) - vmin (U (s + T)) ≤ 4 * a * T ∨
        vmax (V (s + T)) - vmin (U (s + T)) < vmax (V s) - vmin (U s) + ε / 2 * T := by
      intro U V hUV s
      by_cases hnot : (∃ i, ¬ RowEligible V i s (s + T)) ∨ (∃ j, ¬ ColEligible U j s (s + T))
      · right
        exact rb_eq3 A ε hε T
          (fun k hne U' V' hs t ht => htr k hne U' V' hs t (le_trans (hTr k) ht))
          (fun k hne U' V' hs t ht => htc k hne U' V' hs t (le_trans (hTc k) ht))
          U V hUV s hnot
      · left
        have hr : ∀ i, RowEligible V i s (s + T) := fun i => by
          by_contra hc
          exact hnot (Or.inl ⟨i, hc⟩)
        have hc : ∀ j, ColEligible U j s (s + T) := fun j => by
          by_contra hc
          exact hnot (Or.inr ⟨j, hc⟩)
        exact rb_lemma3 A a ha U V hUV s T hr hc
    refine ⟨⌈(8 * a + ε) * T / ε⌉₊ + 1, ?_⟩
    intro U V hUV t ht
    have hmono := rb_gap_mono hUV
    have h0 : vmax (V 0) - vmin (U 0) = 0 := by rw [hUV.1]; ring
    have iter : ∀ n : ℕ, vmax (V (n * T)) - vmin (U (n * T)) ≤ 4 * a * T + n * (ε / 2 * T) := by
      intro n
      induction n with
      | zero =>
        simp only [zero_mul, Nat.cast_zero]
        rw [h0]
        nlinarith
      | succ n ihn =>
        have e : (n + 1) * T = n * T + T := by ring
        rw [e]
        have hs := hstep U V hUV (n * T)
        have hnn : (0 : ℝ) ≤ (n : ℝ) * (ε / 2 * T) := by positivity
        push_cast
        rcases hs with hs | hs
        · nlinarith
        · nlinarith
    have hTpos : 0 < T := hT1
    have hlt : t < (t / T + 1) * T := by
      have := Nat.lt_mul_div_succ t hTpos
      nlinarith
    set n := t / T with hn
    have h1 := iter (n + 1)
    have h2 : vmax (V t) - vmin (U t) ≤ vmax (V ((n + 1) * T)) - vmin (U ((n + 1) * T)) :=
      hmono hlt.le
    have h3 : (((n + 1) * T : ℕ) : ℝ) ≤ ((t + T : ℕ) : ℝ) := by
      have hnt : n * T ≤ t := Nat.div_mul_le_self t T
      have e : (n + 1) * T = n * T + T := by ring
      exact_mod_cast (by rw [e]; omega : (n + 1) * T ≤ t + T)
    have hx : (8 * a + ε) * T / ε ≤ ⌈(8 * a + ε) * T / ε⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hε] at hx
    have htr' : ((⌈(8 * a + ε) * T / ε⌉₊ + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast ht
    push_cast at h3 htr'
    push_cast at h1
    have hn1 : ((n : ℝ) + 1) * T ≤ t + T := by
      have := h3
      push_cast at this
      linarith
    nlinarith

theorem rb_lemma4 [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t₀ : ℕ, ∀ (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ), IsVectorSystem A U V →
      ∀ t : ℕ, t₀ ≤ t → vmax (V t) - vmin (U t) < ε * t :=
  rb_lemma4_aux _ ι κ le_rfl A ε hε

end RobinsonFP.Convergence

open RobinsonFP.Convergence


variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem solution [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t₀ : ℕ, ∀ (U : ℕ → κ → ℝ) (V : ℕ → ι → ℝ), IsVectorSystem A U V →
      ∀ t : ℕ, t₀ ≤ t → vmax (V t) - vmin (U t) < ε * t := by
  exact rb_lemma4 A ε hε
