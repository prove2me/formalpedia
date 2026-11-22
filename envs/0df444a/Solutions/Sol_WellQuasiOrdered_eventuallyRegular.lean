-- Prove2me | solution 1 for WellQuasiOrdered.eventuallyRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:06.130226+00:00
-- url     : https://prove2.me/submissions/88051d54-553a-4a1c-9901-fd84a37adae0

module
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Order.WellFoundedSet
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
section
@[expose] public section
open Set Preorder
noncomputable section
namespace Preorder
end Preorder
private theorem key_reformulation {Q : Type*} (r : Q → Q → Prop) (f : ℕ → Q)
    (hcon : ∀ n, ∃ i, {j : ℕ | r (f (i + n)) (f (j + n))}.Finite) :
    ∀ m : ℕ, ∃ i, m ≤ i ∧ {j : ℕ | r (f i) (f j)}.Finite := by
  intro m
  obtain ⟨i, hfin⟩ := hcon m
  refine ⟨i + m, by omega, ?_⟩
  have hsplit : {j : ℕ | r (f (i + m)) (f j)}
      = {j : ℕ | j < m ∧ r (f (i + m)) (f j)}
        ∪ (fun k => k + m) '' {k : ℕ | r (f (i + m)) (f (k + m))} := by
    ext j
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hj
      rcases lt_or_ge j m with h | h
      · exact Or.inl ⟨h, hj⟩
      · exact Or.inr ⟨j - m, by simpa [Nat.sub_add_cancel h] using hj, Nat.sub_add_cancel h⟩
    · rintro (⟨_, hj⟩ | ⟨k, hk, rfl⟩)
      · exact hj
      · exact hk
  rw [hsplit]
  exact Set.Finite.union ((Set.finite_Iio m).subset fun j ⟨hj, _⟩ => hj) (hfin.image _)
private theorem exists_bad_seq {Q : Type*} (r : Q → Q → Prop) (f : ℕ → Q)
    (key : ∀ m : ℕ, ∃ i, m ≤ i ∧ {j : ℕ | r (f i) (f j)}.Finite) :
    ∃ idx : ℕ → ℕ, StrictMono idx ∧ ∀ m n, m < n → ¬ r (f (idx m)) (f (idx n)) := by
  let S := {p : ℕ × ℕ // ∀ j, r (f p.1) (f j) → j ≤ p.2}
  have succ_step : ∀ p : S, ∃ q : S, p.1.1 < q.1.1 ∧ p.1.2 < q.1.1 := by
    rintro ⟨⟨i, B⟩, hB⟩
    obtain ⟨i', hi'_ge, hfin'⟩ := key (max (i + 1) (B + 1))
    obtain ⟨B', hB'⟩ := hfin'.bddAbove
    refine ⟨⟨(i', max B' i'), fun j hj => le_trans (hB' hj) (le_max_left _ _)⟩, ?_, ?_⟩
    · change i < i'; have h := le_trans (le_max_left (i + 1) (B + 1)) hi'_ge; omega
    · change B < i'; have h := le_trans (le_max_right (i + 1) (B + 1)) hi'_ge; omega
  obtain ⟨i₀, _, hfin₀⟩ := key 0
  obtain ⟨B₀, hB₀⟩ := hfin₀.bddAbove
  let p0 : S := ⟨(i₀, B₀), hB₀⟩
  let nextOf : S → S := fun p => (succ_step p).choose
  let seq : ℕ → S := fun k => Nat.rec p0 (fun _ q => nextOf q) k
  have hseq_succ : ∀ k, seq (k + 1) = nextOf (seq k) := fun k => rfl
  have hstep : ∀ p : S, p.1.1 < (nextOf p).1.1 ∧ p.1.2 < (nextOf p).1.1 :=
    fun p => (succ_step p).choose_spec
  set idx : ℕ → ℕ := fun k => (seq k).1.1 with hidx
  set bd : ℕ → ℕ := fun k => (seq k).1.2 with hbd
  have hidx_lt : ∀ k, idx k < idx (k + 1) := fun k => by
    change (seq k).1.1 < (seq (k + 1)).1.1
    rw [hseq_succ k]; exact (hstep (seq k)).1
  have hbd_lt_idx : ∀ k, bd k < idx (k + 1) := fun k => by
    change (seq k).1.2 < (seq (k + 1)).1.1
    rw [hseq_succ k]; exact (hstep (seq k)).2
  have hidx_mono : StrictMono idx := strictMono_nat_of_lt_succ hidx_lt
  refine ⟨idx, hidx_mono, ?_⟩
  intro m n hmn hle
  have hbound := (seq m).2
  have h1 : idx n ≤ bd m := hbound (idx n) hle
  have h2 : bd m < idx (m + 1) := hbd_lt_idx m
  have h3 : idx (m + 1) ≤ idx n := hidx_mono.le_iff_le.mpr hmn
  omega
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Set Preorder
noncomputable section
namespace WellQuasiOrdered
theorem _root_.solution {Q : Type*} (r : Q → Q → Prop)
    (hwqo : WellQuasiOrdered r) (f : ℕ → Q) :
    ∃ n : ℕ, IsRegularSeq r fun i => f (i + n) := by
  by_contra hcon
  push Not at hcon
  simp only [IsRegularSeq, not_forall, Set.not_infinite] at hcon
  obtain ⟨idx, _, hbad⟩ := exists_bad_seq r f (key_reformulation r f hcon)
  obtain ⟨m, n, hmn, hrel⟩ := hwqo fun k => f (idx k)
  exact hbad m n hmn hrel
end WellQuasiOrdered
