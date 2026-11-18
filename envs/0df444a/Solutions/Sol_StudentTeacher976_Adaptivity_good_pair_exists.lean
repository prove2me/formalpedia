-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.good_pair_exists
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:06:24.014443+00:00
-- url     : https://prove2.me/submissions/71358438-5abe-45f9-9f0e-057b5701fb96

import Definitions.Def_StudentTeacher976_Adaptivity_Teacher

open StudentTeacher976.Adaptivity

set_option autoImplicit false

namespace StudentTeacher976.Adaptivity

private theorem words_spec (n : ℕ) (w : Word) : w ∈ wordsOfLength n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [wordsOfLength, List.length_eq_zero_iff]
  | succ n ih =>
    cases w with
    | nil => simp [wordsOfLength]
    | cons b w =>
      cases b <;> simp [wordsOfLength, ih]

private theorem leastWitness_spec {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    {x : Word} (hx : ∃ y, ValidWitness W x y) :
    ∃ y, leastWitness W x = some y ∧ ValidWitness W x y := by
  classical
  obtain ⟨y, hylen, hy⟩ := hx
  have hex : ∃ y ∈ wordsOfLength (W.length.eval x.length), W.test x y :=
    ⟨y, (words_spec _ _).mpr hylen, hy⟩
  have hn : (leastWitness W x).isSome := by
    simpa [leastWitness, List.find?_isSome] using hex
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hn
  refine ⟨z, hz, ?_⟩
  have hmem := List.mem_of_find?_eq_some (show _ = some z from hz)
  have htest := List.find?_some (show _ = some z from hz)
  exact ⟨(words_spec _ _).mp hmem, of_decide_eq_true htest⟩

private theorem teacher_spec {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    {n k : ℕ} {X : List Word} (hX : TupleShape n k X)
    {B : List (List Word)} {z : TupleReply} (hz : teacher W X B = some z) :
    ReplyShape W n k z ∧ ∀ Y ∈ B, ¬ TupleTest W X Y z := by
  classical
  unfold teacher at hz
  obtain ⟨j, hj, hrest⟩ := Option.bind_eq_some_iff.mp hz
  have hjprop := List.find?_some hj
  have hjmem := List.mem_of_find?_eq_some hj
  have hjlt : j < X.length := List.mem_range.mp hjmem
  have hjp : (∃ w, ValidWitness W (X.getD j []) w) ∧
      ¬ ∃ Y ∈ B, ValidWitness W (X.getD j []) (Y.getD j []) := by
    simpa using hjprop
  obtain ⟨w, hw, hvalid⟩ := leastWitness_spec W hjp.1
  simp only [hw, Option.map_some, Option.some.injEq] at hrest
  subst z
  have hlen : ∀ j < X.length, (X.getD j []).length = n := by
    intro j hj
    apply hX.2
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  constructor
  · refine ⟨by simpa [hX.1] using hjlt, ?_, ?_⟩
    · simp [TupleShape, hX.1]
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
      have halt := List.mem_range.mp ha
      by_cases h : a = j
      · subst a
        rw [if_pos rfl]
        exact hvalid.1.trans (congrArg (fun l => W.length.eval l) (hlen j hjlt))
      · simp only [if_neg h, List.length_replicate, hlen a halt]
  · intro Y hY htest
    apply hjp.2
    refine ⟨Y, hY, htest.2.2 hjlt ?_⟩
    simpa [List.getD_map, hjlt] using hvalid

private theorem trace_le {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (f : TupleStudent) (q : ℕ) (X : List Word) (t : ℕ) :
    (fixedTrace W f q X t).length ≤ t := by
  induction t with
  | zero => simp [fixedTrace]
  | succ t ih =>
    simp only [fixedTrace]
    split
    · omega
    · split <;> simp_all <;> omega

private theorem trace_spec {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (f : TupleStudent) (q n k : ℕ) (X : List Word) (hX : TupleShape n k X) (t : ℕ) :
    (∀ z ∈ fixedTrace W f q X t, ReplyShape W n k z) ∧
    ∀ s, s < (fixedTrace W f q X t).length →
      teacher W X (normalize W f X s
        (((fixedTrace W f q X t).take s).map fun z => List.replicate q z)) =
        some ((fixedTrace W f q X t).getD s (0, [])) := by
  classical
  induction t with
  | zero => simp [fixedTrace]
  | succ t ih =>
    rw [fixedTrace]
    split
    · exact ih
    · rename_i hfull
      have hlen : (fixedTrace W f q X t).length = t := by
        have := trace_le W f q X t
        omega
      split
      · exact ih
      · rename_i z hz
        constructor
        · intro z' hz'
          rcases List.mem_append.mp hz' with h | h
          · exact ih.1 z' h
          · have heq : z' = z := by simpa using h
            subst z'
            exact (teacher_spec W hX hz).1
        · intro s hs
          have hsle : s ≤ t := by simpa [hlen] using hs
          by_cases hst : s < t
          · rw [List.take_append_of_le_length (by omega), List.getD_append _ _ _ _ (by omega)]
            exact ih.2 s (by omega)
          · have heq : s = t := by omega
            subst s
            rw [List.take_append_of_le_length (by omega), List.getD_append_right _ _ _ _ (by omega)]
            have htake : (fixedTrace W f q X t).take t = fixedTrace W f q X t :=
              List.take_of_length_le (by omega)
            rw [htake]
            simpa [hlen] using hz

private theorem trace_short {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (f : TupleStudent) (n k q : ℕ) (X : List Word) (hX : TupleShape n k X)
    (hfshape : TupleStudentShape W n k q f)
    (hwin : TupleStudentWins W n k q (normalize W f)) :
    (fixedTrace W f q X k).length < k := by
  classical
  have hle := trace_le W f q X k
  by_contra! hnot
  have hlen : (fixedTrace W f q X k).length = k := by omega
  let Z := fixedTrace W f q X k
  let H := Z.map fun z => List.replicate q z
  have hspec := trace_spec W f q n k X hX k
  have hshape : TupleHistoryShape W n k q k H := by
    refine ⟨by simp [H, Z, hlen], ?_⟩
    intro B hB
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hB
    refine ⟨by simp, ?_⟩
    intro z' hz'
    have : z' = z := (List.mem_replicate.mp hz').2
    subst z'
    exact hspec.1 z hz
  obtain ⟨t, ht, j, hj, htest⟩ := hwin X H hX hshape
  have hpast : (Z.take t).map (fun z => List.replicate q z) = H.take t := by
    simp [H, List.map_take]
  have hteach := hspec.2 t (by omega)
  have hteacher := (teacher_spec W hX hteach).2
  have hpastshape : TupleHistoryShape W n k q t (H.take t) := by
    refine ⟨by simp [H, Z, hlen, Nat.min_eq_left (Nat.le_of_lt ht)], ?_⟩
    intro B hB
    exact hshape.2 B (List.mem_of_mem_take hB)
  have hflen : (normalize W f X t (H.take t)).length = q := by
    simpa [normalize] using (hfshape.1 X t (H.take t) hX ht hpastshape).1
  have hmem : (normalize W f X t (H.take t)).getD j [] ∈
      normalize W f X t (H.take t) := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hget : H.getD t [] = List.replicate q (Z.getD t (0, [])) := by
    have htz : t < Z.length := by simpa [Z, hlen] using ht
    rw [List.getD_eq_getElem _ _ (by simpa [H] using htz)]
    rw [List.getD_eq_getElem Z (0, []) htz]
    simp [H]
  have hreply : (H.getD t []).getD j (0, []) = Z.getD t (0, []) := by
    rw [hget, List.getD_replicate _ hj]
  apply hteacher ((normalize W f X t (H.take t)).getD j [])
  · simpa only [← hpast] using hmem
  · simpa only [hreply, ← hpast] using htest

end StudentTeacher976.Adaptivity

 theorem solution (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (n k : ℕ) (hsize : k = resource r (n * k))
    (f : TupleStudent) (hf : UniformTupleStudent i f)
    (hshape : TupleStudentShape W n k (resource q (n * k)) f)
    (hsolve : TupleStudentWins W n k (resource q (n * k)) (normalize W f))
    (V : Finset Word) (hV : ∀ x ∈ V, x ∈ positiveInputs W n) (hcard : V.card = k) :
    ∃ x ∈ V, GoodPair W n k (resource q (n * k)) f (V.erase x) x := by
  classical
  let X := V.sort (· ≤ ·)
  have hX : TupleShape n k X := by
    refine ⟨by simp [X, hcard], ?_⟩
    intro x hx
    exact (hV x (by simpa [X] using hx)).1
  let Z := fixedTrace W f (resource q (n * k)) X k
  let B : Finset Word := (Z.map fun z => X.getD z.1 []).toFinset
  have hshort : Z.length < k := trace_short W f n k _ X hX hshape hsolve
  have hBcard : B.card < V.card := by
    calc
      B.card ≤ (Z.map fun z => X.getD z.1 []).length := List.toFinset_card_le _
      _ = Z.length := by simp
      _ < V.card := by omega
  obtain ⟨x, hxV, hxB⟩ := Finset.exists_mem_notMem_of_card_lt_card hBcard
  refine ⟨x, hxV, ?_⟩
  have hinput : orderedInput (V.erase x) x = X := by
    simp [orderedInput, Finset.insert_erase hxV, X]
  refine ⟨by simp [Finset.card_erase_of_mem hxV, hcard], ?_, hV x hxV,
    Finset.notMem_erase x V, ?_⟩
  · intro y hy
    exact hV y (Finset.mem_of_mem_erase hy)
  · intro z hz heq
    rw [hinput] at hz heq
    apply hxB
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨z, hz, heq⟩)
