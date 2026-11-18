-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.auxiliary_upper_game
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:33:20.127826+00:00
-- url     : https://prove2.me/submissions/bbdd286f-e9db-4364-b32c-1e7b745781aa

import Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_test_efficient
import Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_student_uniform
import Definitions.Def_StudentTeacher976_Adaptivity_Auxiliary
open QAdvFew.PoQOracle
set_option autoImplicit false
namespace StudentTeacher976.Adaptivity

private theorem readComponent_encoded (u v : Word) :
    readComponent (u.flatMap (fun b => [true, b]) ++ [false, false] ++ v) = some (u, v) := by
  induction u with
  | nil => simp [readComponent]
  | cons b u ih =>
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ih ⊢
    simpa [readComponent] using congrArg (fun o => o.map (fun p : Word × Word => (b :: p.1, p.2))) ih

private theorem readComponent_sound (s u v : Word) (h : readComponent s = some (u, v)) :
    s = u.flatMap (fun b => [true, b]) ++ [false, false] ++ v := by
  induction s using readComponent.induct generalizing u v with
  | case1 rest =>
    simp only [readComponent, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | case2 b rest ih =>
    simp only [readComponent, Option.map_eq_some_iff] at h
    obtain ⟨⟨u', v'⟩, huv, heq⟩ := h
    cases heq
    simp [ih _ _ huv]
  | case3 s => simp_all [readComponent]

private theorem decodeTupleFuel_sound (fuel : ℕ) (s : Word) (Y : List Word)
    (h : decodeTupleFuel fuel s = some Y) : tup Y = s := by
  induction fuel generalizing s Y with
  | zero =>
    cases s with
    | nil =>
      have : Y = [] := by simpa [decodeTupleFuel] using h.symm
      subst Y
      rfl
    | cons b s => simp [decodeTupleFuel] at h
  | succ fuel ih =>
    cases s with
    | nil =>
      have : Y = [] := by simpa [decodeTupleFuel] using h.symm
      subst Y
      rfl
    | cons b s =>
      simp only [decodeTupleFuel, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨u, v⟩, huv, Y', hY', rfl⟩ := h
      have hs := readComponent_sound (b :: s) u v huv
      simp only [tup, List.flatMap_cons]
      rw [← ih v Y' hY'] at hs
      simpa [tup, List.append_assoc] using hs.symm

private theorem decodeTupleFuel_encoded (Y : List Word) (fuel : ℕ) (hf : Y.length ≤ fuel) :
    decodeTupleFuel fuel (tup Y) = some Y := by
  induction Y generalizing fuel with
  | nil => simp [tup, decodeTupleFuel]
  | cons u Y ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hnon : tup (u :: Y) ≠ [] := by
        simp [tup, List.flatMap_cons]
      have heq : tup (u :: Y) = u.flatMap (fun b => [true, b]) ++ [false, false] ++ tup Y := by
        simp [tup, List.append_assoc]
      rw [heq]
      cases hword : u.flatMap (fun b => [true, b]) ++ [false, false] ++ tup Y with
      | nil => exact (hnon (heq.trans hword)).elim
      | cons b s =>
        rw [decodeTupleFuel, ← hword, readComponent_encoded]
        simp [ih fuel (by simpa using hf)]

private theorem tup_length (Y : List Word) : (tup Y).length = 2 * (Y.map List.length).sum + 2 * Y.length := by
  induction Y with
  | nil => simp [tup]
  | cons u Y ih =>
    have hbits : (u.flatMap fun b => [true, b]).length = 2 * u.length := by
      induction u with
      | nil => simp
      | cons b u ih => simp [ih]; omega
    simp only [tup, List.flatMap_cons, List.length_append, hbits, List.length_cons,
      List.length_nil, List.map_cons, List.sum_cons]
    change 2 * u.length + (1 + (1 + 0)) + (tup Y).length = _
    rw [ih]
    ring

 theorem decodeTuple_encoded (Y : List Word) : decodeTuple (tup Y) = some Y :=
  decodeTupleFuel_encoded Y _ (by rw [tup_length]; omega)

 theorem decodeTuple_sound (s : Word) (Y : List Word) (h : decodeTuple s = some Y) : tup Y = s :=
  decodeTupleFuel_sound s.length s Y h

private theorem poly_eval_mono (p : Polynomial ℕ) {n m : ℕ} (h : n ≤ m) :
    p.eval n ≤ p.eval m := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

private theorem block_shape (r : ℕ → ℕ) (x : Word) (X : List Word)
    (h : blockInput r x = some X) :
    TupleShape (x.length / resource r x.length) (resource r x.length) X ∧
      0 < resource r x.length ∧ resource r x.length ≤ x.length := by
  unfold blockInput at h
  dsimp only at h
  split at h
  · rename_i hp
    simp only [Option.some.injEq] at h
    subst X
    obtain ⟨hm, hk, hmod⟩ := hp
    have hmul : x.length / resource r x.length * resource r x.length = x.length :=
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
    refine ⟨⟨by simp [decodeBlocks], ?_⟩, hk,
      Nat.le_of_dvd hm (Nat.dvd_of_mod_eq_zero hmod)⟩
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    have hjlt := List.mem_range.mp hj
    have hbound := Nat.mul_le_mul_left (x.length / resource r x.length) (Nat.succ_le_of_lt hjlt)
    rw [hmul, Nat.mul_succ, Nat.mul_comm (x.length / resource r x.length) j] at hbound
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    omega
  · simp at h

private theorem tuple_total {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (X : List Word) : ∃ Y, TupleRelation W X Y := by
  classical
  let select : Word → Word := fun a =>
    if h : ∃ w, ValidWitness W a w then h.choose
    else List.replicate (W.length.eval a.length) false
  have hselect : ∀ a, (select a).length = W.length.eval a.length ∧
      ((∃ w, ValidWitness W a w) → ValidWitness W a (select a)) := by
    intro a
    dsimp [select]
    split
    · rename_i h
      exact ⟨h.choose_spec.1, fun _ => h.choose_spec⟩
    · rename_i hnot
      refine ⟨by simp, fun h => (hnot h).elim⟩
  refine ⟨X.map select, by simp, ?_, ?_⟩
  · intro j hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      List.getD_eq_getElem _ _ hj]
    exact (hselect _).1
  · intro j hj hw
    rw [List.getD_eq_getElem (X.map select) [] (by simpa using hj), List.getElem_map]
    rw [List.getD_eq_getElem _ _ hj] at *
    exact (hselect _).2 hw

 theorem auxiliary_total {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (x : Word) : ∃ y, auxiliaryRelation W r x y := by
  unfold auxiliaryRelation
  cases h : blockInput r x with
  | none => exact ⟨[], rfl⟩
  | some X =>
    obtain ⟨Y, hY⟩ := tuple_total W X
    exact ⟨tup Y, Y, rfl, hY⟩

private theorem tuple_encoding_bound {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (x : Word) (X Y : List Word) (hx : blockInput r x = some X)
    (hY : Y.length = X.length ∧ ∀ j < X.length,
      (Y.getD j []).length = W.length.eval (X.getD j []).length) :
    (tup Y).length ≤ (2 * Polynomial.X * (W.length + 1) : Polynomial ℕ).eval x.length := by
  obtain ⟨hX, hkpos, hkle⟩ := block_shape r x X hx
  have hbound : ∀ a ∈ Y, a.length ≤ W.length.eval x.length := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    have hjX : j < X.length := by simpa [hY.1] using hj
    have hlen := hY.2 j hjX
    rw [List.getD_eq_getElem _ _ hj] at hlen
    rw [hlen]
    apply poly_eval_mono
    have hmem : X.getD j [] ∈ X := by
      rw [List.getD_eq_getElem _ _ hjX]
      exact List.getElem_mem _
    rw [hX.2 _ hmem]
    exact Nat.div_le_self _ _
  have hsum : (Y.map List.length).sum ≤ Y.length * W.length.eval x.length := by
    calc
      (Y.map List.length).sum ≤ (Y.map fun _ => W.length.eval x.length).sum :=
        List.sum_le_sum (by intro a ha; exact hbound a ha)
      _ = Y.length * W.length.eval x.length := by simp
  have hYlen : Y.length ≤ x.length := by rw [hY.1, hX.1]; exact hkle
  rw [tup_length]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_X,
    Polynomial.eval_one]
  nlinarith

 theorem auxiliary_bounded {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) : ∃ b : Polynomial ℕ, ∀ x y,
      auxiliaryRelation W r x y → y.length ≤ b.eval x.length := by
  refine ⟨2 * Polynomial.X * (W.length + 1), ?_⟩
  intro x y hrel
  unfold auxiliaryRelation at hrel
  cases hx : blockInput r x with
  | none => simp [hx] at hrel; subst y; simp
  | some X =>
    simp only [hx] at hrel
    obtain ⟨Y, rfl, hY⟩ := hrel
    exact tuple_encoding_bound W r x X Y hx ⟨hY.1, hY.2.1⟩

private theorem certificate_encode {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (x a w : Word) (j : ℕ) (hj : j < x.length)
    (hwlen : w.length = W.length.eval a.length)
    (ha : a.length ≤ x.length) :
    ∃ z : Word, z.length = x.length + W.length.eval x.length ∧
      rawIndex x z = j ∧ rawWitness W x a z = w := by
  let certPrefix := List.replicate j true ++ List.replicate (x.length - j) false
  let certSuffix := w ++ List.replicate (W.length.eval x.length - w.length) false
  have hplen : certPrefix.length = x.length := by simp [certPrefix]; omega
  have hwidth : w.length ≤ W.length.eval x.length := by
    rw [hwlen]
    exact poly_eval_mono W.length ha
  have hcertSuffix : certSuffix.length = W.length.eval x.length := by simp [certSuffix]; omega
  refine ⟨certPrefix ++ certSuffix, by simp [hplen, hcertSuffix], ?_, ?_⟩
  · unfold rawIndex
    rw [List.take_append_of_le_length (by omega), ← hplen, List.take_length]
    have htake : certPrefix.takeWhile id = List.replicate j true := by
      dsimp [certPrefix]
      rw [List.takeWhile_append_of_pos]
      · simp
      · intro b hb
        have : b = true := (List.mem_replicate.mp hb).2
        simp [this]
    rw [htake]
    simp
  · unfold rawWitness
    rw [← hplen, List.drop_left]
    dsimp [certSuffix]
    rw [← hwlen, List.take_left]

 theorem auxiliary_represents {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (x y : Word) :
    auxiliaryRelation W r x y ↔ ∀ z : Word,
      z.length = x.length + W.length.eval x.length → auxiliaryTest W r x y z := by
  classical
  unfold auxiliaryRelation auxiliaryTest
  cases hx : blockInput r x with
  | none =>
    constructor
    · intro hy z hz; exact hy
    · intro hall
      exact hall (List.replicate (x.length + W.length.eval x.length) false) (by simp)
  | some X =>
    obtain ⟨hX, hkpos, hkle⟩ := block_shape r x X hx
    constructor
    · rintro ⟨Y, rfl, hY⟩ z hz
      rw [decodeTuple_encoded]
      refine ⟨hY.1, hY.2.1, ?_⟩
      intro hj hw
      exact hY.2.2 _ hj ⟨_, hw⟩
    · intro hall
      have hzero := hall (List.replicate (x.length + W.length.eval x.length) false) (by simp)
      cases hy : decodeTuple y with
      | none => simp [hy] at hzero
      | some Y =>
        simp only [hy] at hzero
        refine ⟨Y, (decodeTuple_sound y Y hy).symm, hzero.1, hzero.2.1, ?_⟩
        intro j hj hw
        obtain ⟨w, hw⟩ := hw
        have hjm : j < x.length := by rw [hX.1] at hj; omega
        have hmem : X.getD j [] ∈ X := by
          rw [List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem _
        have ha : (X.getD j []).length ≤ x.length := by
          rw [hX.2 _ hmem]
          exact Nat.div_le_self _ _
        obtain ⟨z, hzlen, hzidx, hzword⟩ := certificate_encode W x (X.getD j []) w j hjm hw.1 ha
        have htest := hall z hzlen
        rw [hy] at htest
        have h := htest.2.2
        rw [hzidx] at h
        apply h hj
        rw [hzword]
        exact hw

private theorem candidate_spec {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (x : Word) (X : List Word) (H : List (List Word)) :
    (auxiliaryCandidate W x X H).length = X.length ∧
      ∀ j < X.length,
        ((auxiliaryCandidate W x X H).getD j []).length = W.length.eval (X.getD j []).length ∧
        (∀ z ∈ H.flatten, ValidWitness W (X.getD j []) (rawWitness W x (X.getD j []) z) →
          ValidWitness W (X.getD j []) ((auxiliaryCandidate W x X H).getD j [])) := by
  classical
  constructor
  · simp [auxiliaryCandidate]
  · intro j hj
    rw [List.getD_eq_getElem (auxiliaryCandidate W x X H) [] (by simpa [auxiliaryCandidate] using hj),
      List.getD_eq_getElem X [] hj]
    simp only [auxiliaryCandidate, List.getElem_map]
    cases hf : ((H.flatten.map fun z => rawWitness W x X[j] z).find?
        fun w => decide (ValidWitness W X[j] w)) with
    | none =>
      simp only [Option.getD_none, List.length_replicate, true_and]
      intro z hz hv
      have hn := List.find?_eq_none.mp hf _ (List.mem_map.mpr ⟨z, hz, rfl⟩)
      simp [hv] at hn
    | some w =>
      have hw : ValidWitness W X[j] w := by simpa using List.find?_some hf
      simp only [Option.getD_some]
      exact ⟨hw.1, fun _ _ _ => hw⟩

 theorem auxiliary_student_wins_semantic {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (x : Word) (H : List (List Word))
    (hH : HistoryShape (resource (fun m => r m + 1) x.length) 1
      (x.length + W.length.eval x.length) H) :
    ∃ t, t < resource (fun m => r m + 1) x.length ∧
      auxiliaryTest W r x ((auxiliaryStudent W r x t (H.take t)).getD 0 [])
        ((H.getD t []).getD 0 []) := by
  classical
  let k := resource r x.length
  have hbudget : resource (fun m => r m + 1) x.length = k + 1 := rfl
  cases hx : blockInput r x with
  | none =>
    refine ⟨0, by rw [hbudget]; omega, ?_⟩
    simp [auxiliaryStudent, hbudget, auxiliaryTest, hx]
  | some X =>
    obtain ⟨hX, hkpos, hkle⟩ := block_shape r x X hx
    by_contra! hfail
    have hbad : ∀ t : Fin (k + 1),
        rawIndex x ((H.getD t.val []).getD 0 []) < X.length ∧
        ValidWitness W (X.getD (rawIndex x ((H.getD t.val []).getD 0 [])) [])
          (rawWitness W x (X.getD (rawIndex x ((H.getD t.val []).getD 0 [])) []) ((H.getD t.val []).getD 0 [])) ∧
        ¬ ValidWitness W (X.getD (rawIndex x ((H.getD t.val []).getD 0 [])) [])
          ((auxiliaryCandidate W x X (H.take t.val)).getD (rawIndex x ((H.getD t.val []).getD 0 [])) []) := by
      intro t
      have ht : t.val < resource (fun m => r m + 1) x.length := by simpa [hbudget] using t.isLt
      have h := hfail t.val ht
      have hc := candidate_spec W x X (H.take t.val)
      simp only [auxiliaryStudent, if_pos ht, hx, List.getD_cons_zero,
        auxiliaryTest, hx, decodeTuple_encoded] at h
      have hshape : ∀ j < X.length,
          ((auxiliaryCandidate W x X (H.take t.val)).getD j []).length = W.length.eval (X.getD j []).length :=
        fun j hj => (hc.2 j hj).1
      simp only [hc.1, hshape, true_and] at h
      push_neg at h
      exact h hshape
    let index : Fin (k + 1) → Fin k := fun t => ⟨rawIndex x ((H.getD t.val []).getD 0 []),
      by simpa [hX.1] using (hbad t).1⟩
    have hdistinct : ∀ a b : Fin (k + 1), a.val < b.val → index a ≠ index b := by
      intro a b hab heq
      have heqval : (index a).val = (index b).val := congrArg Fin.val heq
      have hmem : (H.getD a.val []).getD 0 [] ∈ (H.take b.val).flatten := by
        have haH : a.val < H.length := by rw [hH.1, hbudget]; exact a.isLt
        have hB : H.getD a.val [] ∈ H.take b.val := by
          rw [List.getD_eq_getElem H [] haH]
          have hm := List.getElem_mem (l := H.take b.val) (n := a.val) (by simp [hH.1, hbudget]; omega)
          simpa using hm
        have hBlen := (hH.2 _ (List.mem_of_mem_take hB)).1
        refine List.mem_flatten.mpr ⟨_, hB, ?_⟩
        rw [List.getD_eq_getElem (H.getD a.val []) [] (by omega)]
        exact List.getElem_mem _
      apply (hbad b).2.2
      apply (candidate_spec W x X (H.take b.val)).2 _ (hbad b).1 |>.2 _ hmem
      have hva := (hbad a).2.1
      change rawIndex x ((H.getD a.val []).getD 0 []) = rawIndex x ((H.getD b.val []).getD 0 []) at heqval
      rwa [heqval] at hva
    have hinj : Function.Injective index := by
      intro a b heq
      rcases lt_trichotomy a.val b.val with h | h | h
      · exact (hdistinct a b h heq).elim
      · exact Fin.ext h
      · exact (hdistinct b a h heq.symm).elim
    have hcard := Fintype.card_le_of_injective index hinj
    simp only [Fintype.card_fin] at hcard
    omega

 theorem auxiliary_student_shape {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (P : RefutablePresentation i (auxiliaryRelation W r)) :
    StudentShape P (fun m => r m + 1) (fun _ => 1) (auxiliaryStudent W r) := by
  classical
  constructor
  · refine ⟨2 * Polynomial.X * (W.length + 1), ?_⟩
    intro x t H ht hH
    rw [auxiliaryStudent, if_pos ht]
    constructor
    · rfl
    · intro y hy
      simp only [List.mem_singleton] at hy
      subst y
      cases hx : blockInput r x with
      | none => simp
      | some X =>
        have hc := candidate_spec W x X H
        exact tuple_encoding_bound W r x X (auxiliaryCandidate W x X H) hx
          ⟨hc.1, fun j hj => (hc.2 j hj).1⟩
  · intro x t H ht
    simp [auxiliaryStudent, Nat.not_lt.mpr ht]

end StudentTeacher976.Adaptivity

open StudentTeacher976.Adaptivity

theorem solution (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (hr : AdmissibleRounds r) :
    auxiliaryRelation W r ∈ ST i (fun m => r m + 1) (fun _ => 1) := by
  obtain ⟨b, hb⟩ := auxiliary_bounded W r
  let P : RefutablePresentation i (auxiliaryRelation W r) :=
    { answerBound := b
      refutationLength := Polynomial.X + W.length
      test := auxiliaryTest W r
      efficient := auxiliary_test_efficient i L W r hr
      total := auxiliary_total W r
      bounded := hb
      represents := by
        intro x y
        simpa using auxiliary_represents W r x y }
  refine ⟨P, auxiliaryStudent W r, auxiliary_student_uniform i L W r hr,
    auxiliary_student_shape W r P, ?_⟩
  intro x H hH
  have hH' : HistoryShape (resource (fun m => r m + 1) x.length) 1
      (x.length + W.length.eval x.length) H := by
    simpa [P, resource] using hH
  obtain ⟨t, ht, htest⟩ := auxiliary_student_wins_semantic W r x H hH'
  exact ⟨t, ht, 0, by simp [resource], htest⟩
