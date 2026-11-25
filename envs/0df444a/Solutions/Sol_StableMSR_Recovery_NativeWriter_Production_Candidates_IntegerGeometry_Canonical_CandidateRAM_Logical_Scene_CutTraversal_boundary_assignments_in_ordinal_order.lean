-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.boundary_assignments_in_ordinal_order
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T13:03:30.13471+00:00
-- url     : https://prove2.me/submissions/130060c6-9a71-4cd4-b406-7f10094efc26

import Definitions.Def_StableMSR_EligibleSeparatorRows
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Basic

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open StableMSR.Recovery.SingleCircuit StableMSR.Recovery.TightLanguage
set_option autoImplicit false

/-- Decode the ordinal by the right-to-left remainder and quotient operations of
the entry program. The Boolean table identifies permitted word slots. -/
private def readAssignment (base : ℕ) (word : ℕ → ℕ) (permitted : ℕ → ℕ → Bool) :
    List ℕ → ℕ → Option Assignment
  | [], _ => some []
  | v :: back, q =>
      if permitted v (q % base) then
        (readAssignment base word permitted back (q / base)).map
          (fun a => a ++ [(v, word (q % base))])
      else none

private lemma rangeBlocks (rows base : ℕ) :
    List.range (rows * base) =
      (List.range rows).flatMap (fun i => (List.range base).map (i * base + ·)) := by
  induction rows with
  | zero => simp
  | succ rows ih =>
    rw [Nat.succ_mul, List.range_add, List.range_succ, List.flatMap_append, ← ih]
    simp

private lemma appendMenu (d : Instance) (cut : List ℕ) (v : ℕ) :
    assignments d (cut ++ [v]) = (assignments d cut).flatMap
      (fun a => (d.menu v).map (fun x => a ++ [(v, x)])) := by
  induction cut with
  | nil => simp [assignments, List.map_eq_flatMap]
  | cons u us ih =>
    simp only [List.cons_append, assignments, ih, List.flatMap_assoc, List.map_flatMap,
      List.flatMap_map, List.map_map, Function.comp_def, List.cons_append]

private lemma appendDecoded {α β γ : Type*} (l : List α) (f : α → Option β) (g : β → List γ) :
    (l.filterMap f).flatMap g = l.flatMap (fun i => ((f i).map g).getD []) := by
  induction l with
  | nil => rfl
  | cons i is ih => cases h : f i <;> simp [h, ih]

/-- Scanning the ordinals in increasing order and rejecting forbidden digits
returns exactly the recursive list of boundary assignments, in order and with
the same multiplicities. The rightmost boundary vertex takes the least significant digit. -/
private theorem assignment_ordinal_order (d : Instance) (cut : List ℕ) (base : ℕ)
    (word : ℕ → ℕ) (permitted : ℕ → ℕ → Bool) (hb : 0 < base)
    (menus : ∀ v ∈ cut, d.menu v = (List.range base).filterMap
      (fun i => if permitted v i then some (word i) else none)) :
    (List.range (base ^ cut.length)).filterMap
      (readAssignment base word permitted cut.reverse) = assignments d cut := by
  induction cut using List.reverseRecOn with
  | nil => simp [readAssignment, assignments]
  | append_singleton cut v ih =>
    have old := ih (fun u hu => menus u (List.mem_append_left _ hu))
    have last := menus v (by simp)
    simp only [List.length_append, List.length_singleton, pow_succ, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    rw [rangeBlocks, List.filterMap_flatMap, appendMenu, ← old, appendDecoded]
    apply List.flatMap_congr
    intro q _
    rw [List.filterMap_map]
    let f := readAssignment base word permitted cut.reverse
    change (List.range base).filterMap (fun j => readAssignment base word permitted
      (v :: cut.reverse) (q*base+j)) = ((f q).map _).getD []
    have digit : ∀ j ∈ List.range base, readAssignment base word permitted
        (v :: cut.reverse) (q*base+j) =
        if permitted v j then (f q).map (fun a => a ++ [(v, word j)]) else none := by
      intro j hj
      have h := List.mem_range.mp hj
      have div : (q*base+j)/base=q := by
        rw [Nat.mul_comm q base, Nat.mul_add_div hb, Nat.div_eq_of_lt h, Nat.add_zero]
      simp [readAssignment, Nat.mul_add_mod_of_lt h, div, f]
    rw [List.filterMap_congr digit]
    cases f q with
    | none => simp
    | some a =>
      simp only [Option.map_some, Option.getD_some]
      rw [last, List.map_filterMap]
      apply List.filterMap_congr
      intro j _
      cases permitted v j <;> simp

open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open SeparatorLevels

private lemma wordCount (n h : ℕ) : (SingleCodes.words n h).length = sizes n h := by
  have rect (H R : ℕ) (f : ℕ → ℕ → ℕ) :
      ((List.range H).flatMap fun i => (List.range R).map (f i)).length = H*R := by
    induction H with
    | zero => simp
    | succ H ih => simp [List.range_succ, List.flatMap_append, ih, Nat.succ_mul]
  exact rect (h+1) (n^(2*(h+1))) (SingleCodes.encode h)

private lemma listFromSlots (xs : List ℕ) :
    (List.range xs.length).map (fun i => xs[i]?.getD 0) = xs := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂; simp [List.getElem?_eq_getElem h₂]

/-- The actual base register, word array, and vertex feasibility bits in any state
preserving the regional tables yield the reference menu product. -/
private theorem assignment_order_from_regional_tables (x : World) (s : Store) (r h w : ℕ)
    (u v z a : State) (hn : 0 < x.n) (prep : Prepared x.n r h w u)
    (geometry : Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h u v)
    (menus : Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h v z)
    (preserved : Between z a) (cut : List ℕ) (bounded : ∀ p ∈ cut, p < x.n) :
    let base := (a.reg 70).toNat
    let word := fun i => (a.heap ((a.reg 76).toNat+i)).toNat
    let permitted := fun p i => decide (1 ≤ a.heap ((a.reg 81).toNat+(p*base+i)))
    (List.range (base^cut.length)).filterMap (readAssignment base word permitted cut.reverse) =
      assignments (integerData x.n x.mem s.imem r h) cut := by
  let M := sizes x.n h
  let layout := offsets x.n M
  let W := WindowProfiles.piece x (r/x.n) (r%x.n)
  obtain ⟨_,_,_,_,_,_,_,_,baseReg,_,_,ptrs,_,_,_⟩ := prep
  have ctrl (j : ℕ) (hj : 64 ≤ j ∧ j ≤ 81) : a.reg j = u.reg j :=
    (preserved.control j (.inr (.inr hj))).trans ((menus.controls j (by omega)).trans
      (geometry.controls j (by omega)))
  have baseEq : (a.reg 70).toNat = M := by
    rw [ctrl 70 (by decide), baseReg]; rfl
  have wordPtr : (a.reg 76).toNat = cursorAt layout 5 := by
    rw [ctrl 76 (by decide), show u.reg 76 = _ from ptrs ⟨5,by decide⟩]; rfl
  have bitsPtr : (a.reg 81).toNat = cursorAt layout 10 := by
    rw [ctrl 81 (by decide), show u.reg 81 = _ from ptrs ⟨10,by decide⟩]; rfl
  dsimp only
  rw [baseEq, wordPtr, bitsPtr]
  have positive : 0 < M := by dsimp [M, sizes]; positivity
  apply assignment_ordinal_order _ cut M _ _ positive
  intro p hp
  have small := bounded p hp
  let vertex : Fin x.n := ⟨p, small⟩
  let words := SingleCodes.words x.n h
  let valid := fun c => Bits.feasible (Bits.win s.imem W vertex)
    (Bits.blocks s.imem (Bits.win s.imem W vertex) h c)
  have len : words.length = M := wordCount _ _
  have menuEq : (integerData x.n x.mem s.imem r h).menu p = words.filter valid := by
    simp [integerData, arrange, Bits.normalized, Bits.lookup, small, Bits.menus, words, valid, vertex, W]
    rfl
  rw [menuEq]
  have listed : (List.range M).map (fun j => words[j]?.getD 0) = words := by
    rw [← len]; exact listFromSlots _
  calc
    words.filter valid = (List.range M).filterMap
        (fun j => if valid (words[j]?.getD 0) then some (words[j]?.getD 0) else none) := by
      conv_lhs => rw [← listed]
      rw [← List.filterMap_eq_filter, List.filterMap_map]
      rfl
    _ = _ := by
      apply List.filterMap_congr
      intro j hj
      have hj := List.mem_range.mp hj
      have slot : p*M+j < x.n*M := by
        calc p*M+j < p*M+M := Nat.add_lt_add_left hj _
             _ = (p+1)*M := (Nat.succ_mul _ _).symm
             _ ≤ _ := Nat.mul_le_mul_right _ small
      have endWords : cursorAt layout 5+M ≤ cursorAt layout 11 := by
        simp [layout,cursorAt,offsets]; omega
      have endBits : cursorAt layout 10+x.n*M ≤ cursorAt layout 11 := by
        simp [layout,cursorAt,offsets]; omega
      have safe : cursorAt layout 11 ≤ (z.reg 8).toNat := by have := menus.cursor; dsimp [layout,M]; omega
      have wc := (preserved.tables (cursorAt layout 5+j) (by omega)).trans (menus.words j hj)
      have fe := (preserved.tables (cursorAt layout 10+(p*M+j)) (by omega)).trans
        (menus.tables vertex j hj).2.2.2.2
      change a.heap (cursorAt layout 5+j) = ((words[j]?.getD 0 : ℕ):ℤ) at wc
      change a.heap (cursorAt layout 10+(p*M+j)) = (if valid (words[j]?.getD 0) then 1 else 0) at fe
      rw [wc, fe]
      cases valid (words[j]?.getD 0) <;> simp


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option maxHeartbeats 4100000
set_option maxRecDepth 35000
set_option autoImplicit false
open Scene.CutTraversal Scene.SeparatorLevels TightLanguage
theorem solution (x : World) (s : Store) (r h w : ℕ)
    (u v z a : Logical.State) (hn : 0 < x.n) (prep : Prepared x.n r h w u)
    (geometry : Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h u v)
    (menus : Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h v z)
    (preserved : Between z a) (cut : List ℕ) (bounded : ∀ p ∈ cut, p < x.n) :
    let base := (a.reg 70).toNat
    let word := fun i => (a.heap ((a.reg 76).toNat+i)).toNat
    let permitted := fun p i => decide (1 ≤ a.heap ((a.reg 81).toNat+(p*base+i)))
    (List.range (base^cut.length)).filterMap ((cut.reverse.foldr (fun v (k : ℕ → Option Assignment) q =>
        if permitted v (q%base) then (k (q/base)).map (fun t => t++[(v,word (q%base))]) else none)
        (fun _ => some []))) =
      assignments (integerData x.n x.mem s.imem r h) cut := by
  have decode (base : ℕ) (word : ℕ → ℕ) (p : ℕ → ℕ → Bool) (back : List ℕ) :
      back.foldr (fun v (k : ℕ → Option Assignment) q =>
        if p v (q%base) then (k (q/base)).map (fun t => t++[(v,word (q%base))]) else none)
        (fun _ => some []) = readAssignment base word p back := by
    induction back with
    | nil => rfl
    | cons v back ih => rw [List.foldr_cons, ih]; rfl
  dsimp only
  rw [decode (a.reg 70).toNat (fun i => (a.heap ((a.reg 76).toNat+i)).toNat)
    (fun p i => decide (1 ≤ a.heap ((a.reg 81).toNat+(p*(a.reg 70).toNat+i)))) cut.reverse]
  exact assignment_order_from_regional_tables x s r h w u v z a hn prep geometry menus preserved cut bounded

#print axioms solution
