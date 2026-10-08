-- Prove2me | solution 1 for RobinsonFP.Convergence.eq3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:39:45.20944+00:00
-- url     : https://prove2.me/submissions/0eb3462a-7960-4115-8ced-cc1cf7724215

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

end RobinsonFP.Convergence

open RobinsonFP.Convergence


variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem solution [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ] (A : Matrix ι κ ℝ)
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
  exact rb_eq3 A ε hε tstar hrowIH hcolIH U V hUV s hnot
