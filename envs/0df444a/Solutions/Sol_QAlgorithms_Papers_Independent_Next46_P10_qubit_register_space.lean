-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P10.qubit_register_space
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:09:23.246827+00:00
-- url     : https://prove2.me/submissions/0063484f-4eb4-43a5-9fa3-fbb36238268c

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P10
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Next46.P10

attribute [local instance] Classical.propDecidable

namespace G62Q

theorem clog_succ (n : ℕ) (hn : 1 ≤ n) : Nat.clog 2 (n + 1) = Nat.log 2 n + 1 := by
  have h1 := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num)]; omega
  · by_contra h
    push Not at h
    have : Nat.clog 2 (n + 1) ≤ Nat.log 2 n := by omega
    rw [Nat.clog_le_iff_le_pow (by norm_num)] at this
    omega

theorem clog_half (n : ℕ) (hn : 2 ≤ n) : Nat.clog 2 (n / 2 + 1) = Nat.log 2 n := by
  have h1 := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  have hL : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  obtain ⟨L, hL'⟩ : ∃ L, Nat.log 2 n = L + 1 := ⟨Nat.log 2 n - 1, by omega⟩
  rw [hL'] at h1 h2 ⊢
  rw [pow_succ] at h1 h2
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num), pow_succ]; omega
  · by_contra h
    push Not at h
    have : Nat.clog 2 (n / 2 + 1) ≤ L := by omega
    rw [Nat.clog_le_iff_le_pow (by norm_num)] at this
    omega

theorem natToBits_inj {m a b : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : natToBits m a = natToBits m b) : a = b := by
  unfold natToBits at h
  have := congrArg Fin.val ((bitsEquivFin m).symm.injective h)
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

theorem append_inj {a b : ℕ} {x x' : Fin a → Bool} {y y' : Fin b → Bool}
    (h : Fin.append x y = Fin.append x' y') : x = x' ∧ y = y' := by
  constructor
  · funext i; have := congrFun h (Fin.castAdd b i); simpa using this
  · funext i; have := congrFun h (Fin.natAdd a i); simpa using this


theorem pbc_sum {n : ℕ} (p : Qubits n) (k : ℕ) :
    prefixBottomCount p k = ∑ i : Fin n, if i.val < k ∧ p i = true then 1 else 0 := by
  unfold prefixBottomCount; rw [Finset.card_filter]

theorem wt_sum {n : ℕ} (p : Qubits n) :
    hammingWeight p = ∑ i : Fin n, if p i = true then 1 else 0 := by
  unfold hammingWeight; rw [Finset.card_filter]

theorem pbc_ge {n : ℕ} (p : Qubits n) (k : ℕ) (hk : n ≤ k) : prefixBottomCount p k = hammingWeight p := by
  rw [pbc_sum, wt_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : i.val < k := lt_of_lt_of_le i.isLt hk
  simp [this]

theorem bval (b : Bool) : (if b = true then 1 else 0 : ℕ) = b.toNat := by cases b <;> rfl

theorem pbc_snoc {n : ℕ} (p : Qubits n) (b : Bool) (k : ℕ) :
    prefixBottomCount (Fin.snoc (α := fun _ => Bool) p b) k =
      prefixBottomCount p k + (if n < k ∧ b = true then 1 else 0) := by
  rw [pbc_sum, pbc_sum, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem wt_snoc {n : ℕ} (p : Qubits n) (b : Bool) :
    hammingWeight (Fin.snoc (α := fun _ => Bool) p b) = hammingWeight p + b.toNat := by
  rw [wt_sum, wt_sum, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, bval]

theorem tab_snoc {n : ℕ} (p : Qubits n) (b : Bool) :
    IsTableauWord (Fin.snoc (α := fun _ => Bool) p b) ↔
      IsTableauWord p ∧ 2 * (hammingWeight p + b.toNat) ≤ n + 1 := by
  constructor
  · intro h
    refine ⟨fun k => ?_, ?_⟩
    · have := h (Fin.castSucc k)
      rw [pbc_snoc] at this
      simp only [Fin.coe_castSucc] at this
      have hk := k.isLt
      rw [if_neg (by omega), add_zero] at this
      exact this
    · have := h (Fin.last (n + 1))
      rw [pbc_snoc, pbc_ge p _ (by simp)] at this
      simp only [Fin.val_last] at this
      cases b <;> simp_all
  · rintro ⟨h1, h2⟩ k
    rw [pbc_snoc]
    by_cases hk : k.val ≤ n
    · rw [if_neg (by omega), add_zero]
      exact h1 ⟨k.val, by omega⟩
    · have hk' : k.val = n + 1 := by omega
      rw [hk', pbc_ge p _ (by omega)]
      cases b <;> simp_all

theorem tab_wt {n : ℕ} (p : Qubits n) (h : IsTableauWord p) : 2 * hammingWeight p ≤ n := by
  have := h (Fin.last n)
  rwa [Fin.val_last, pbc_ge p _ le_rfl] at this


def F (n : ℕ) : ℕ := ∑ p : Qubits n, if IsTableauWord p then n - 2 * hammingWeight p + 1 else 0

theorem F_succ (n : ℕ) : F (n + 1) = 2 * F n := by
  unfold F
  rw [← (Fin.snocEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have e : ∀ b : Bool, (Fin.snocEquiv (fun _ => Bool)) (b, p) = Fin.snoc (α := fun _ => Bool) p b :=
    fun b => rfl
  simp only [e, tab_snoc, wt_snoc]
  by_cases hp : IsTableauWord p
  · have hw := tab_wt p hp
    simp only [hp, true_and, Bool.toNat_true, Bool.toNat_false, add_zero]
    rw [if_pos trivial]
    by_cases h2 : 2 * (hammingWeight p + 1) ≤ n + 1
    · rw [if_pos h2, if_pos (by omega)]; omega
    · rw [if_neg h2, if_pos (by omega)]; omega
  · simp [hp]

theorem F_zero : F 0 = 1 := by
  unfold F
  rw [Fintype.sum_unique]
  have : ∀ p : Qubits 0, IsTableauWord p := by
    intro p k
    rw [pbc_ge _ _ (Nat.zero_le _)]
    simp [hammingWeight]
  rw [if_pos (this _)]
  simp [hammingWeight]

theorem F_eq (n : ℕ) : F n = 2 ^ n := by
  induction n with
  | zero => exact F_zero
  | succ n ih => rw [F_succ, ih, pow_succ]; ring

theorem cnt (N c : ℕ) (hc : c ≤ N) : (∑ s : Fin N, if s.val < c then 1 else 0) = c := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < c then 1 else 0) N, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  have : (Finset.range N).filter (fun i => i < c) = Finset.range c := by
    ext i; simp; omega
  rw [this, Finset.card_range]

theorem card_label (n : ℕ) : Fintype.card (QubitSchurLabel n) = 2 ^ n := by
  rw [← F_eq, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  unfold F
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hp : IsTableauWord p
  · simp only [hp, true_and, if_true]
    exact cnt _ _ (by omega)
  · simp [hp]


theorem first_false {n : ℕ} (p : Qubits (n + 1)) (hp : IsTableauWord p) : p 0 = false := by
  have h1 := hp ⟨1, by omega⟩
  simp only at h1
  have h0 : prefixBottomCount p 1 = 0 := by omega
  unfold prefixBottomCount at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  have := h0 (Finset.mem_univ 0)
  simpa using this

theorem seq_inj {m : ℕ} (p q : Qubits (m + 2)) (hp : IsTableauWord p) (hq : IsTableauWord q)
    (hw : hammingWeight p = hammingWeight q) (hs : seqWord p = seqWord q) : p = q := by
  have hcs : ∀ i : Fin (m + 1), p (Fin.castSucc i) = q (Fin.castSucc i) := by
    intro i
    rcases i with ⟨i, hi⟩
    cases i with
    | zero =>
      have h1 := first_false p hp
      have h2 := first_false q hq
      exact h1.trans h2.symm
    | succ j =>
      have := congrFun hs ⟨j, by simp [seqSize]; omega⟩
      simp only [seqWord] at this
      rw [dif_pos (by omega), dif_pos (by omega)] at this
      exact this
  have hl : p (Fin.last (m + 1)) = q (Fin.last (m + 1)) := by
    have eP : ∀ r : Qubits (m + 2), hammingWeight r = (∑ i : Fin (m + 1),
        (if r (Fin.castSucc i) = true then 1 else 0)) + (if r (Fin.last (m + 1)) = true then 1 else 0) := by
      intro r; rw [wt_sum, Fin.sum_univ_castSucc]
    rw [eP p, eP q] at hw
    simp only [hcs] at hw
    have : (if p (Fin.last (m + 1)) = true then 1 else 0 : ℕ) =
        if q (Fin.last (m + 1)) = true then 1 else 0 := by omega
    revert this
    cases p (Fin.last (m + 1)) <;> cases q (Fin.last (m + 1)) <;> simp
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hl
  · exact hcs j

end G62Q

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    seqSize n = n - 2 ∧
    parSize n = Nat.clog 2 (n / 2 + 1) ∧
    statSize n = Nat.clog 2 (n + 1) ∧
    (∀ m : ℕ, m ≤ n / 2 →
      Fintype.card (TwoRowTableau n m) ≤ 2 ^ seqSize n) ∧
    (∀ a : QubitSchurLabel n,
      hammingWeight a.val.1 < 2 ^ parSize n ∧
      a.val.2.val < 2 ^ statSize n) ∧
    Function.Injective (@labelEncoding n) ∧
    Fintype.card (QubitSchurLabel n) = 2 ^ n ∧
    totalSize n = n + 2 * Nat.log 2 n - 1 ∧
    ancillaSize n = 2 * Nat.log 2 n - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hpar : ∀ w : ℕ, 2 * w ≤ k + 2 → w < 2 ^ parSize (k + 2) := by
    intro w hw
    have := Nat.le_pow_clog (by norm_num : 1 < 2) ((k + 2) / 2 + 1)
    unfold parSize; omega
  have hstat : ∀ s : ℕ, s < k + 2 + 1 → s < 2 ^ statSize (k + 2) := by
    intro s hs
    have := Nat.le_pow_clog (by norm_num : 1 < 2) (k + 2 + 1)
    unfold statSize; omega
  have hL1 := G62Q.clog_half (k + 2) (by omega)
  have hL2 := G62Q.clog_succ (k + 2) (by omega)
  have hL : 1 ≤ Nat.log 2 (k + 2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have htot : totalSize (k + 2) = k + 2 + 2 * Nat.log 2 (k + 2) - 1 := by
    unfold totalSize seqSize parSize statSize
    rw [hL1, hL2]; omega
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, G62Q.card_label _, htot, ?_⟩
  · intro m _
    have h := Fintype.card_le_of_injective (fun t : TwoRowTableau (k + 2) m => seqWord t.val)
      (fun a b hab => Subtype.ext (G62Q.seq_inj a.val b.val a.2.1 b.2.1 (a.2.2.trans b.2.2.symm) hab))
    simpa [Qubits] using h
  · intro a
    exact ⟨hpar _ (G62Q.tab_wt _ a.2.1), hstat _ a.val.2.isLt⟩
  · intro a b hab
    obtain ⟨h1, h23⟩ := G62Q.append_inj hab
    obtain ⟨h2, h3⟩ := G62Q.append_inj h23
    have hw := G62Q.natToBits_inj (hpar _ (G62Q.tab_wt _ a.2.1)) (hpar _ (G62Q.tab_wt _ b.2.1)) h2
    have hs := G62Q.natToBits_inj (hstat _ a.val.2.isLt) (hstat _ b.val.2.isLt) h3
    apply Subtype.ext
    exact Prod.ext (G62Q.seq_inj _ _ a.2.1 b.2.1 hw h1) (Fin.ext hs)
  · unfold ancillaSize; rw [htot]; omega
