-- Prove2me | solution 1 for RealPinwheel.FiveSixths.periodic_unfolding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:51:38.783491+00:00
-- url     : https://prove2.me/submissions/3fefa4aa-9ad4-4e84-934e-b2708029df19

import Definitions.Def_RealPinwheel_FiveSixths_Transformations

open RealPinwheel.FiveSixths

private lemma residue_offset (q : ℕ) (hq : 0 < q) (c r : ℕ) (hr : r < q) :
    ∃ s < q, (c + s) % q = r := by
  have hc := Nat.mod_lt c hq
  by_cases h : c % q ≤ r
  · refine ⟨r - c % q, by omega, ?_⟩
    rw [Nat.add_mod]
    have he : c % q + (r - c % q) % q = r := by
      rw [Nat.mod_eq_of_lt (show r - c % q < q by omega)]
      omega
    rw [he, Nat.mod_eq_of_lt hr]
  · refine ⟨q + r - c % q, by omega, ?_⟩
    rw [Nat.add_mod]
    have he : c % q + (q + r - c % q) % q = q + r := by
      rw [Nat.mod_eq_of_lt (show q + r - c % q < q by omega)]
      omega
    rw [he, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hr]

private lemma windowCount_count {n : ℕ} (S : ℕ → Fin n) (i : Fin n) (m h : ℕ) :
    windowCount S i m h = Nat.count (fun t => S (m + t) = i) h := by
  rw [Nat.count_eq_card_filter_range]
  rfl

private lemma prefix_window {n : ℕ} (S : ℕ → Fin n) (i : Fin n) (m h : ℕ) :
    Nat.count (fun t => S t = i) (m + h) =
      Nat.count (fun t => S t = i) m + windowCount S i m h := by
  rw [Nat.count_add, windowCount_count]

private lemma rank_window {n : ℕ} (S : ℕ → Fin n) (i : Fin n) (m H k : ℕ)
    (hk : k < windowCount S i m H) :
    ∃ t < H, S (m + t) = i ∧
      Nat.count (fun t => S t = i) (m + t) = Nat.count (fun t => S t = i) m + k := by
  let p := fun t => S (m + t) = i
  have hk' : k < Nat.count p H := by simpa [p, windowCount_count] using hk
  have hf : ∀ h : (Set.ofPred p).Finite, k < h.toFinset.card :=
    fun h => hk'.trans_le (Nat.count_le_card h H)
  refine ⟨Nat.nth p k, Nat.nth_lt_of_lt_count hk', Nat.nth_mem k hf, ?_⟩
  rw [Nat.count_add, Nat.count_nth hf]

private lemma split_window {n : ℕ} (S : ℕ → Fin n) (j : Fin n)
    (q : ℕ) (hq : 0 < q) (r : Fin q) (m H ell : ℕ)
    (hC : q * ell ≤ windowCount S j m H) :
    ell ≤ ((Finset.range H).filter fun t => S (m + t) = j ∧
      Nat.count (fun t => S t = j) (m + t) % q = r.val).card := by
  obtain ⟨s, hs, hsr⟩ := residue_offset q hq (Nat.count (fun t => S t = j) m) r.val r.isLt
  have hw (k : Fin ell) : ∃ t < H, S (m + t) = j ∧
      Nat.count (fun t => S t = j) (m + t) =
        Nat.count (fun t => S t = j) m + (s + q * k.val) := by
    apply rank_window
    have hk := k.isLt
    have hh : s + q * k.val < q * ell := by nlinarith
    omega
  choose f hf using hw
  have hinj : Function.Injective f := by
    intro k l he
    have hk := (hf k).2.2
    have hl := (hf l).2.2
    rw [he] at hk
    have hv : k.val = l.val := by nlinarith
    exact Fin.ext hv
  have hc := Finset.card_le_card_of_injOn f (s := Finset.univ)
    (t := (Finset.range H).filter fun t => S (m + t) = j ∧
      Nat.count (fun t => S t = j) (m + t) % q = r.val)
    (by
      intro k _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨(hf k).1, (hf k).2.1, ?_⟩
      rw [(hf k).2.2, ← Nat.add_assoc, Nat.add_mul_mod_self_left, hsr])
    (hinj.injOn)
  simpa using hc

private lemma unfolded_nodup {n : ℕ} (a : Fin n → ℝ) (j : Fin n) (q : ℕ) :
    (unfoldedLabels a j q).Nodup := by
  classical
  rw [unfoldedLabels, List.nodup_mergeSort, unfoldingLabels, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (List.nodup_finRange n).filter _ |>.map Sum.inl_injective
  · exact (List.nodup_finRange q).map Sum.inr_injective
  · intro x hx y hy
    simp only [List.mem_map] at hx hy
    rcases hx with ⟨u, _, rfl⟩
    rcases hy with ⟨v, _, rfl⟩
    exact Sum.inl_ne_inr

private lemma unfolded_mem {n : ℕ} (a : Fin n → ℝ) (j : Fin n) (q : ℕ)
    (x : Fin n ⊕ Fin q) :
    x ∈ unfoldedLabels a j q ↔ (∀ k, x = Sum.inl k → k ≠ j) := by
  classical
  cases x <;> simp [unfoldedLabels, List.mem_mergeSort, unfoldingLabels]

private noncomputable def splitSchedule {n : ℕ} (a : Fin n → ℝ) (S : ℕ → Fin n)
    (j : Fin n) (q : ℕ) (hq : 0 < q) : ℕ → Fin (unfoldedLabels a j q).length := by
  classical
  intro t
  let x : Fin n ⊕ Fin q := if S t = j then
    Sum.inr ⟨Nat.count (fun t => S t = j) t % q, Nat.mod_lt _ hq⟩ else Sum.inl (S t)
  have hx : x ∈ unfoldedLabels a j q := by
    rw [unfolded_mem]
    intro k hk
    dsimp [x] at hk
    split_ifs at hk with ht <;> simp_all
  exact Classical.choose (List.mem_iff_get.mp hx)

private lemma splitSchedule_label {n : ℕ} (a : Fin n → ℝ) (S : ℕ → Fin n)
    (j : Fin n) (q : ℕ) (hq : 0 < q) (t : ℕ) :
    (unfoldedLabels a j q).get (splitSchedule a S j q hq t) =
      if S t = j then Sum.inr ⟨Nat.count (fun t => S t = j) t % q, Nat.mod_lt _ hq⟩
      else Sum.inl (S t) := by
  classical
  dsimp only [splitSchedule]
  exact @Classical.choose_spec (Fin (unfoldedLabels a j q).length)
    (fun i => (unfoldedLabels a j q).get i =
      if S t = j then Sum.inr ⟨Nat.count (fun t => S t = j) t % q, Nat.mod_lt _ hq⟩
      else Sum.inl (S t)) _

private lemma splitSchedule_valid {n : ℕ} (a : Fin n → ℝ) (S : ℕ → Fin n)
    (hS : Valid a S) (j : Fin n) (q : ℕ) (hq : 0 < q) :
    Valid (unfoldedPeriods a j q) (splitSchedule a S j q hq) := by
  classical
  intro i ell hell m
  have hmem := (unfoldedLabels a j q).get_mem i
  have hinj := fun {u v} => (unfolded_nodup a j q).get_inj_iff (i := u) (j := v)
  cases hi : (unfoldedLabels a j q).get i with
  | inl k =>
    have hkj : k ≠ j := (unfolded_mem a j q _).mp (hi ▸ hmem) k rfl
    have hp : unfoldedPeriods a j q i = a k := by
      change unfoldingPeriod a j q ((unfoldedLabels a j q).get i) = _
      rw [hi]
      rfl
    rw [hp]
    apply (hS k ell hell m).trans
    apply Finset.card_mono
    intro t ht
    simp only [Finset.mem_filter] at ht ⊢
    refine ⟨ht.1, ?_⟩
    apply hinj.mp
    rw [splitSchedule_label, ht.2, if_neg hkj, hi]
  | inr r =>
    have hp : unfoldedPeriods a j q i = (q : ℝ) * a j := by
      change unfoldingPeriod a j q ((unfoldedLabels a j q).get i) = _
      rw [hi]
      rfl
    rw [hp]
    have hc := hS j (q * ell) (Nat.mul_pos hq hell) m
    have he : ((q * ell : ℕ) : ℝ) * a j =
        (ell : ℝ) * ((q : ℝ) * a j) := by push_cast; ring
    rw [he] at hc
    apply (split_window S j q hq r m _ ell hc).trans
    apply Finset.card_mono
    intro t ht
    simp only [Finset.mem_filter] at ht ⊢
    refine ⟨ht.1, ?_⟩
    apply hinj.mp
    rw [splitSchedule_label, if_pos ht.2.1, hi]
    congr 1
    exact Fin.ext ht.2.2

private lemma periodic_prefix {n : ℕ} (S : ℕ → Fin n) (L : ℕ)
    (hper : ∀ t, S (t + L) = S t) (j : Fin n) (t : ℕ) :
    Nat.count (fun t => S t = j) (t + L) =
      Nat.count (fun t => S t = j) t + Nat.count (fun t => S t = j) L := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show t + 1 + L = (t + L) + 1 by omega]
    rw [Nat.count_succ, Nat.count_succ, ih, hper]
    omega

private lemma periodic_prefix_mul {n : ℕ} (S : ℕ → Fin n) (L : ℕ)
    (hper : ∀ t, S (t + L) = S t) (j : Fin n) (t q : ℕ) :
    Nat.count (fun t => S t = j) (t + q * L) =
      Nat.count (fun t => S t = j) t + q * Nat.count (fun t => S t = j) L := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, periodic_prefix S L hper j, ih]
    ring

private lemma periodic_mul {n : ℕ} (S : ℕ → Fin n) (L : ℕ)
    (hper : ∀ t, S (t + L) = S t) (t q : ℕ) : S (t + q * L) = S t := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, ← Nat.add_assoc, hper, ih]

private lemma splitSchedule_periodic {n : ℕ} (a : Fin n → ℝ) (S : ℕ → Fin n)
    (j : Fin n) (q : ℕ) (hq : 0 < q) (L : ℕ)
    (hper : ∀ t, S (t + L) = S t) :
    ∀ t, splitSchedule a S j q hq (t + q * L) = splitSchedule a S j q hq t := by
  intro t
  apply (unfolded_nodup a j q).get_inj_iff.mp
  rw [splitSchedule_label, splitSchedule_label, periodic_mul S L hper t q]
  split_ifs
  · congr 2
    simp only [periodic_prefix_mul S L hper j, Nat.add_mul_mod_self_left]
  · rfl

theorem solution {n : ℕ} (A : Instance n) (S : ℕ → Fin n) (hS : Valid A.period S)
    (j : Fin n) (L : ℕ) (hL : 0 < L) (hper : ∀ t, S (t + L) = S t) :
    ∃ T : ℕ → Fin (unfoldedLabels A.period j 2).length,
      Valid (unfoldedPeriods A.period j 2) T ∧ Periodic T (2 * L) := by
  exact ⟨splitSchedule A.period S j 2 (by omega),
    splitSchedule_valid A.period S hS j 2 (by omega),
    Nat.mul_pos (by omega) hL, splitSchedule_periodic A.period S j 2 (by omega) L hper⟩
