-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.ComponentProgram.component_traversal_program
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T20:11:13.741427+00:00
-- url     : https://prove2.me/submissions/4749df2f-80a7-40e7-b8d1-fedce42ebf96

import Definitions.Def_StableMSR_ComponentGraphMemory
import Theorems.Thm_StableMSR_Recovery_Compiler_compiler_execution_exact
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler
namespace StableMSR.Recovery.Compiler
lemma compile_deterministic (cmd : Cmd) (result : ℕ) :
    DeterministicProgram (compile cmd result) :=
  (compiler_execution_exact cmd result).1
lemma compile_halts {n : ℕ} {d : Point n → Point n → ℝ}
    {cmd : Cmd} {s t : Store} {cost : ℕ} (h : Executes d cmd s t cost)
    (ω : ℕ → ℝ) (w result : ℕ) :
    (MinSumFPT.step (compile cmd result) d ω)^[cost+1] (s.state 0 w) =
      t.haltedState cmd.size (w+cost+1) result :=
  (compiler_execution_exact cmd result).2 n d s t cost h ω w
@[simp] lemma compileAt_length (pc : ℕ) (cmd : Cmd) :
    (compileAt pc cmd).length = cmd.size := by
  induction cmd generalizing pc <;> simp_all [compileAt, Cmd.size] <;> omega
end StableMSR.Recovery.Compiler
set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.TupleWriter

/- Store a register at the output pointer and advance that pointer. -/
def writeOne (out r : ℕ) (s : Store) : Store :=
  { s with
    imem := Function.update s.imem (s.ptrs out) (s.ptrs r)
    ptrs := Function.update s.ptrs out (s.ptrs out+1) }

def writeRegs (out : ℕ) : List ℕ → Cmd
  | [] => .skip
  | r::rs => .seq (.atom (.integerStore out r))
      (.seq (.atom (.pointerInc out)) (writeRegs out rs))

@[simp] lemma writeRegs_size (out : ℕ) (rs : List ℕ) :
    (writeRegs out rs).size = 2*rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [writeRegs,Cmd.size,List.length_cons,ih]; omega

def writeStore (out : ℕ) : List ℕ → Store → Store
  | [], s => s
  | r::rs, s => writeStore out rs (writeOne out r s)

/- Consecutive integer-memory writes, in stream order. -/
def writeMemory (base : ℤ) (values : List ℤ) (mem : ℤ → ℤ) : ℤ → ℤ :=
  match values with
  | [] => mem
  | v::vs => writeMemory (base+1) vs (Function.update mem base v)

@[simp] theorem writeMemory_nil (a : ℤ) (mem : ℤ → ℤ) : writeMemory a [] mem = mem := rfl

lemma writeMemory_append (a : ℤ) (xs ys : List ℤ) (mem : ℤ → ℤ) :
    writeMemory a (xs++ys) mem =
      writeMemory (a+(xs.length : ℤ)) ys (writeMemory a xs mem) := by
  induction xs generalizing a mem with
  | nil => simp [writeMemory]
  | cons x xs ih =>
    simp only [List.cons_append,writeMemory,List.length_cons]
    rw [ih]
    congr 1
    push_cast
    ring

lemma writeMemory_before (a x : ℤ) (values : List ℤ) (mem : ℤ → ℤ) (hx : x < a) :
    writeMemory a values mem x = mem x := by
  induction values generalizing a mem with
  | nil => rfl
  | cons v vs ih =>
    rw [writeMemory,ih (a+1) (Function.update mem a v) (by omega)]
    simp [show x ≠ a by omega]

lemma writeMemory_after (a x : ℤ) (values : List ℤ) (mem : ℤ → ℤ)
    (hx : a+(values.length : ℤ) ≤ x) :
    writeMemory a values mem x = mem x := by
  induction values generalizing a mem with
  | nil => rfl
  | cons v vs ih =>
    have hlen : ((v::vs).length : ℤ) = vs.length + 1 := by simp
    rw [writeMemory,ih (a+1) (Function.update mem a v) (by omega)]
    simp [show x ≠ a by have := Int.natCast_nonneg vs.length; omega]

lemma writeMemory_get (a : ℤ) (values : List ℤ) (mem : ℤ → ℤ)
    (i : ℕ) (hi : i < values.length) :
    writeMemory a values mem (a+(i : ℤ)) = values[i] := by
  induction values generalizing a mem i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero =>
      simp only [Nat.cast_zero,add_zero,List.getElem_cons_zero,writeMemory]
      rw [writeMemory_before (a+1) a vs (Function.update mem a v) (by omega)]
      simp
    | succ i =>
      have hi' : i < vs.length := by simpa using hi
      have he : a+((i+1 : ℕ) : ℤ) = (a+1)+(i : ℤ) := by push_cast; ring
      rw [writeMemory,he,ih (a+1) (Function.update mem a v) i hi']
      rfl

lemma writeRegs_exec {n : ℕ} (d : Point n → Point n → ℝ)
    (out : ℕ) (rs : List ℕ) (s : Store) :
    Executes d (writeRegs out rs) s (writeStore out rs s) (2*rs.length) := by
  induction rs generalizing s with
  | nil => exact Executes.skip s
  | cons r rs ih =>
    have he := Executes.seq (Executes.atom (.integerStore out r) s)
      (Executes.seq (Executes.atom (.pointerInc out) ((Op.integerStore out r).eval d s))
        (ih (writeOne out r s)))
    simpa only [writeRegs,writeStore,List.length_cons,
      show 2*(rs.length+1) = 1+(1+2*rs.length) by omega] using he

@[simp] lemma writeOne_ptr_out (out r : ℕ) (s : Store) :
    (writeOne out r s).ptrs out = s.ptrs out+1 := by simp [writeOne]
lemma writeOne_ptr_ne (out r j : ℕ) (s : Store) (hj : j ≠ out) :
    (writeOne out r s).ptrs j = s.ptrs j := by simp [writeOne,hj]

lemma writeStore_ptr_out (out : ℕ) (rs : List ℕ) (s : Store) :
    (writeStore out rs s).ptrs out = s.ptrs out+(rs.length : ℤ) := by
  induction rs generalizing s with
  | nil => simp [writeStore]
  | cons r rs ih =>
    simp only [writeStore,ih,writeOne_ptr_out,List.length_cons,Nat.cast_add,Nat.cast_one]
    ring
lemma writeStore_ptr_ne (out j : ℕ) (rs : List ℕ) (s : Store) (hj : j ≠ out) :
    (writeStore out rs s).ptrs j = s.ptrs j := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => rw [writeStore,ih,writeOne_ptr_ne out r j s hj]

lemma writeStore_frame (out : ℕ) (rs : List ℕ) (s : Store) :
    (writeStore out rs s).regs = s.regs ∧
    (writeStore out rs s).mem = s.mem ∧
    (writeStore out rs s).queries = s.queries ∧
    (writeStore out rs s).tapePos = s.tapePos ∧
    (writeStore out rs s).output = s.output := by
  induction rs generalizing s with
  | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | cons r rs ih => exact ih (writeOne out r s)

lemma writeStore_memory (out : ℕ) (rs : List ℕ) (s : Store) (hf : out ∉ rs) :
    (writeStore out rs s).imem = writeMemory (s.ptrs out) (rs.map s.ptrs) s.imem := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    have hr : r ≠ out := by simp only [List.mem_cons,not_or] at hf; exact Ne.symm hf.1
    have hrs : out ∉ rs := by simp only [List.mem_cons,not_or] at hf; exact hf.2
    rw [writeStore,ih (writeOne out r s) hrs]
    have hm : rs.map (writeOne out r s).ptrs = rs.map s.ptrs := by
      apply List.map_congr_left
      intro j hj
      exact writeOne_ptr_ne out r j s (fun he => hrs (he ▸ hj))
    simp only [hm,writeOne_ptr_out,List.map_cons,writeMemory]
    rfl

/- A fixed-width output record: header followed by the digit registers. -/
def writerRegs (w : ℕ) : List ℕ := (w+2)::((List.range w).map (·+1))
def writer (w : ℕ) : Cmd := writeRegs (w+1) (writerRegs w)
def writerEval (w : ℕ) (s : Store) : Store := writeStore (w+1) (writerRegs w) s

@[simp] lemma writerRegs_length (w : ℕ) : (writerRegs w).length = w+1 := by simp [writerRegs]
@[simp] lemma writer_size (w : ℕ) : (writer w).size = 2*(w+1) := by
  simp [writer]
lemma writerRegs_fresh (w : ℕ) : w+1 ∉ writerRegs w := by
  simp only [writerRegs,List.mem_cons,List.mem_map,List.mem_range]
  rintro (he | ⟨i,hi,he⟩) <;> omega
lemma writer_exec {n : ℕ} (d : Point n → Point n → ℝ) (w : ℕ) (s : Store) :
    Executes d (writer w) s (writerEval w s) (2*(w+1)) := by
  simpa [writer,writerEval] using writeRegs_exec d (w+1) (writerRegs w) s
lemma writer_ptr_out (w : ℕ) (s : Store) :
    (writerEval w s).ptrs (w+1) = s.ptrs (w+1)+(w+1 : ℕ) := by
  simp [writerEval,writeStore_ptr_out]
lemma writer_ptr_ne (w j : ℕ) (s : Store) (hj : j ≠ w+1) :
    (writerEval w s).ptrs j = s.ptrs j := writeStore_ptr_ne (w+1) j (writerRegs w) s hj
lemma writer_frame (w : ℕ) (s : Store) :
    (writerEval w s).regs = s.regs ∧ (writerEval w s).mem = s.mem ∧
    (writerEval w s).queries = s.queries ∧ (writerEval w s).tapePos = s.tapePos ∧
    (writerEval w s).output = s.output := writeStore_frame (w+1) (writerRegs w) s
lemma writer_memory (w : ℕ) (s : Store) :
    (writerEval w s).imem =
      writeMemory (s.ptrs (w+1)) ((writerRegs w).map s.ptrs) s.imem :=
  writeStore_memory (w+1) (writerRegs w) s (writerRegs_fresh w)

lemma writer_header (w : ℕ) (s : Store) (hw : s.ptrs (w+2) = (w : ℤ)) :
    (writerEval w s).imem (s.ptrs (w+1)) = (w : ℤ) := by
  rw [writer_memory]
  have h := writeMemory_get (s.ptrs (w+1)) ((writerRegs w).map s.ptrs) s.imem 0 (by simp)
  simpa [writerRegs,hw] using h

lemma writer_digit (w : ℕ) (s : Store) (i : ℕ) (hi : i < w) :
    (writerEval w s).imem (s.ptrs (w+1)+1+(i : ℤ)) = s.ptrs (i+1) := by
  rw [writer_memory]
  have h := writeMemory_get (s.ptrs (w+1)) ((writerRegs w).map s.ptrs) s.imem (i+1) (by simp; omega)
  simpa [writerRegs,List.getElem_map,List.getElem_range,hi,add_assoc,add_comm,add_left_comm] using h

lemma writer_before (w : ℕ) (s : Store) (x : ℤ) (hx : x < s.ptrs (w+1)) :
    (writerEval w s).imem x = s.imem x := by
  rw [writer_memory]
  exact writeMemory_before _ _ _ _ hx

lemma writer_after (w : ℕ) (s : Store) (x : ℤ)
    (hx : s.ptrs (w+1)+(w+1 : ℕ) ≤ x) :
    (writerEval w s).imem x = s.imem x := by
  rw [writer_memory]
  apply writeMemory_after
  simpa using hx

end StableMSR.Recovery.Compiler.TupleWriter

set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.BitmapFill

open TupleWriter

/- One iteration of an integer-array fill. -/
def fillBody (out value : ℕ) : Cmd :=
  .seq (.atom (.integerStore out value)) (.atom (.pointerInc out))

/- A fixed program whose input stop pointer determines the fill length. -/
def fillCmd (out stop value : ℕ) : Cmd :=
  .whileDo (.pointerLE out stop) (fillBody out value)

@[simp] lemma fillBody_size (out value : ℕ) : (fillBody out value).size = 2 := rfl

@[simp] lemma fillCmd_size (out stop value : ℕ) : (fillCmd out stop value).size = 5 := rfl

/- Mathematical effect of filling `q` consecutive cells. -/
def fillEval (out value q : ℕ) (s : Store) : Store :=
  writeStore out (List.replicate q value) s

@[simp] lemma fillEval_zero (out value : ℕ) (s : Store) :
    fillEval out value 0 s = s := rfl

lemma fillEval_succ (out value q : ℕ) (s : Store) :
    fillEval out value (q+1) s = fillEval out value q (writeOne out value s) := by
  simp only [fillEval,List.replicate_succ,writeStore]

lemma fillBody_exec {n : ℕ} (d : Point n → Point n → ℝ)
    (out value : ℕ) (s : Store) :
    Executes d (fillBody out value) s (writeOne out value s) 2 := by
  exact Executes.seq (Executes.atom (.integerStore out value) s)
    (Executes.atom (.pointerInc out) ((.integerStore out value : Op).eval d s))

/- Exact execution cost includes the final unsuccessful loop test. -/
lemma fill_exec {n : ℕ} (d : Point n → Point n → ℝ)
    (out stop value q : ℕ) (s : Store) (hne : out ≠ stop)
    (hstop : s.ptrs stop = s.ptrs out + (q : ℤ) - 1) :
    Executes d (fillCmd out stop value) s (fillEval out value q s) (4*q+2) := by
  induction q generalizing s with
  | zero =>
    apply Executes.while_false
    simp only [Cond.test]
    simp only [Nat.cast_zero] at hstop
    omega
  | succ q ih =>
    have hguard : (Cond.pointerLE out stop).test s := by
      simp only [Cond.test]
      simp only [Nat.cast_add,Nat.cast_one] at hstop
      omega
    have hnext : (writeOne out value s).ptrs stop =
        (writeOne out value s).ptrs out + (q : ℤ) - 1 := by
      rw [writeOne_ptr_ne out value stop s (Ne.symm hne),writeOne_ptr_out]
      simp only [Nat.cast_add,Nat.cast_one] at hstop
      omega
    have hex := Executes.while_true hguard (fillBody_exec d out value s)
      (ih (writeOne out value s) hnext)
    simpa only [fillCmd,fillEval_succ,show 1+2+1+(4*q+2) = 4*(q+1)+2 by omega]
      using hex

lemma fill_ptr_out (out value q : ℕ) (s : Store) :
    (fillEval out value q s).ptrs out = s.ptrs out + (q : ℤ) := by
  simpa only [fillEval,List.length_replicate] using
    writeStore_ptr_out out (List.replicate q value) s

lemma fill_ptr_ne (out value q j : ℕ) (s : Store) (hj : j ≠ out) :
    (fillEval out value q s).ptrs j = s.ptrs j :=
  writeStore_ptr_ne out j (List.replicate q value) s hj

lemma fill_frame (out value q : ℕ) (s : Store) :
    (fillEval out value q s).regs = s.regs ∧
    (fillEval out value q s).mem = s.mem ∧
    (fillEval out value q s).queries = s.queries ∧
    (fillEval out value q s).tapePos = s.tapePos ∧
    (fillEval out value q s).output = s.output :=
  writeStore_frame out (List.replicate q value) s

lemma fill_memory (out value q : ℕ) (s : Store) (hne : out ≠ value) :
    (fillEval out value q s).imem =
      writeMemory (s.ptrs out) (List.replicate q (s.ptrs value)) s.imem := by
  have hf : out ∉ List.replicate q value := by simp [hne]
  simpa only [fillEval,List.map_replicate] using
    writeStore_memory out (List.replicate q value) s hf

lemma fill_memory_get (out value q i : ℕ) (s : Store)
    (hne : out ≠ value) (hi : i < q) :
    (fillEval out value q s).imem (s.ptrs out + (i : ℤ)) = s.ptrs value := by
  rw [fill_memory out value q s hne]
  have hi' : i < (List.replicate q (s.ptrs value)).length := by simpa using hi
  rw [writeMemory_get _ _ _ i hi']
  simp

lemma fill_memory_before (out value q : ℕ) (s : Store) (x : ℤ)
    (hne : out ≠ value) (hx : x < s.ptrs out) :
    (fillEval out value q s).imem x = s.imem x := by
  rw [fill_memory out value q s hne]
  exact writeMemory_before _ _ _ _ hx

lemma fill_memory_after (out value q : ℕ) (s : Store) (x : ℤ)
    (hne : out ≠ value) (hx : s.ptrs out + (q : ℤ) ≤ x) :
    (fillEval out value q s).imem x = s.imem x := by
  rw [fill_memory out value q s hne]
  apply writeMemory_after
  simpa only [List.length_replicate] using hx

end StableMSR.Recovery.Compiler.BitmapFill


namespace StableMSR.Recovery.Havens

variable {V : Type} [DecidableEq V]

noncomputable def componentWithin (G : SimpleGraph V) (U : Finset V) (u : V) : Finset V :=
  by classical exact U.filter (fun v => ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∈ U)

lemma mem_componentWithin {G : SimpleGraph V} {U : Finset V} {u v : V} :
    v ∈ componentWithin G U u ↔ v ∈ U ∧ ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∈ U := by
  classical
  simp only [componentWithin, Finset.mem_filter]

lemma componentWithin_subset (G : SimpleGraph V) (U : Finset V) (u : V) :
    componentWithin G U u ⊆ U := by
  intro v hv
  exact (mem_componentWithin.mp hv).1

lemma self_mem_componentWithin {G : SimpleGraph V} {U : Finset V} {u : V} (hu : u ∈ U) :
    u ∈ componentWithin G U u := by
  refine mem_componentWithin.mpr ⟨hu, .nil, ?_⟩
  simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using fun z (hz : z = u) => hz ▸ hu

lemma componentWithin_closed {G : SimpleGraph V} {U : Finset V} {u x y : V}
    (hx : x ∈ componentWithin G U u) (hxy : G.Adj x y) (hy : y ∈ U) :
    y ∈ componentWithin G U u := by
  obtain ⟨_, p, hp⟩ := mem_componentWithin.mp hx
  refine mem_componentWithin.mpr ⟨hy, p.concat hxy, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_concat] at hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hp z hz
  · simpa only [List.mem_singleton] using (show z = y from List.mem_singleton.mp hz) ▸ hy

lemma mem_of_walk_closed {G : SimpleGraph V} {C D : Finset V}
    (hclosed : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ D → y ∈ C)
    {u v : V} (p : G.Walk u v) (hu : u ∈ C)
    (hp : ∀ z ∈ p.support, z ∈ D) : v ∈ C := by
  induction p with
  | nil => exact hu
  | @cons u v w huv p ih =>
    apply ih (hclosed u hu v huv (hp v (by simp)))
    intro z hz
    exact hp z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hz)

end StableMSR.Recovery.Havens

set_option autoImplicit false
namespace StableMSR.Recovery.ComponentTraversal
variable {V : Type} [Fintype V] [DecidableEq V]

/- An inflationary finite-set map stabilizes once the remaining cardinality
room has been exhausted. No monotonicity across unrelated inputs is needed. -/
theorem inflationary_stabilizes_of_card_le (f : Finset V → Finset V)
    (hf : ∀ S, S ⊆ f S) (r : ℕ) (S : Finset V)
    (hroom : Fintype.card V ≤ S.card + r) :
    f (f^[r] S) = f^[r] S := by
  induction r generalizing S with
  | zero =>
    have hc : (f S).card ≤ S.card := (Finset.card_le_univ _).trans (by omega)
    exact (Finset.eq_of_subset_of_card_le (hf S) hc).symm
  | succ r ih =>
    by_cases hfix : f S = S
    · rw [Function.iterate_fixed hfix (r+1),hfix]
    · have hc : S.card < (f S).card := by
        by_contra hn
        exact hfix (Finset.eq_of_subset_of_card_le (hf S) (by omega)).symm
      have hnext : Fintype.card V ≤ (f S).card + r := by omega
      simpa only [Function.iterate_succ_apply] using ih (f S) hnext

/- Every inflationary iteration on subsets of an n-element set has reached a
fixed point after n applications, including the empty ground-set case. -/
theorem inflationary_stabilizes (f : Finset V → Finset V)
    (hf : ∀ S, S ⊆ f S) (S : Finset V) :
    f (f^[Fintype.card V] S) = f^[Fintype.card V] S :=
  inflationary_stabilizes_of_card_le f hf (Fintype.card V) S (by omega)

end StableMSR.Recovery.ComponentTraversal


namespace StableMSR.Recovery.ComponentTraversal

variable {V : Type} [DecidableEq V]

/- Process one directed edge, marking its permitted target when its source is marked. -/
def relax (allowed R : Finset V) (e : V × V) : Finset V :=
  if e.1 ∈ R ∧ e.2 ∈ allowed then insert e.2 R else R

/- One complete sweep of the explicit directed edge list. -/
def pass (allowed : Finset V) (es : List (V × V)) (R : Finset V) : Finset V :=
  es.foldl (relax allowed) R

/- At most one sweep per vertex suffices, independently of the edge ordering. -/
def traverse [Fintype V] (allowed : Finset V) (es : List (V × V))
    (seed : V) : Finset V :=
  (pass allowed es)^[Fintype.card V] {seed}

theorem relax_inflationary (allowed R : Finset V) (e : V × V) :
    R ⊆ relax allowed R e := by
  simp only [relax]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem pass_inflationary (allowed : Finset V) (es : List (V × V))
    (R : Finset V) : R ⊆ pass allowed es R := by
  induction es generalizing R with
  | nil => exact Finset.Subset.refl _
  | cons e es ih =>
    exact (relax_inflationary allowed R e).trans (ih (relax allowed R e))

theorem relax_subset {allowed R C : Finset V} {e : V × V}
    (hR : R ⊆ C) (hclosed : e.1 ∈ C → e.2 ∈ allowed → e.2 ∈ C) :
    relax allowed R e ⊆ C := by
  simp only [relax]
  split
  · rename_i h
    exact Finset.insert_subset (hclosed (hR h.1) h.2) hR
  · exact hR

theorem pass_subset {allowed R C : Finset V} {es : List (V × V)}
    (hR : R ⊆ C)
    (hclosed : ∀ e ∈ es, e.1 ∈ C → e.2 ∈ allowed → e.2 ∈ C) :
    pass allowed es R ⊆ C := by
  induction es generalizing R with
  | nil => exact hR
  | cons e es ih =>
    apply ih (relax_subset hR (hclosed e (by simp)))
    intro e' he'
    exact hclosed e' (by simp [he'])

theorem edge_target_mem_pass {allowed R : Finset V} {es : List (V × V)}
    {u v : V} (he : (u, v) ∈ es) (hu : u ∈ R) (hv : v ∈ allowed) :
    v ∈ pass allowed es R := by
  induction es generalizing R with
  | nil => simp at he
  | cons e es ih =>
    rcases List.mem_cons.mp he with h | h
    · subst e
      apply pass_inflationary allowed es (relax allowed R (u, v))
      simp [relax, hu, hv]
    · exact ih h ((relax_inflationary allowed R e) hu)

theorem pass_fixed_edge_closed {allowed R : Finset V} {es : List (V × V)}
    (hfixed : pass allowed es R = R) {u v : V}
    (he : (u, v) ∈ es) (hu : u ∈ R) (hv : v ∈ allowed) : v ∈ R := by
  rw [← hfixed]
  exact edge_target_mem_pass he hu hv

theorem seed_mem_iterate (allowed : Finset V) (es : List (V × V))
    (seed : V) (n : ℕ) : seed ∈ (pass allowed es)^[n] {seed} := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact pass_inflationary allowed es _ ih

theorem iterate_subset_componentWithin (G : SimpleGraph V) (allowed : Finset V)
    (es : List (V × V)) (seed : V) (hseed : seed ∈ allowed)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (n : ℕ) :
    (pass allowed es)^[n] {seed} ⊆ Havens.componentWithin G allowed seed := by
  induction n with
  | zero =>
    exact Finset.singleton_subset_iff.mpr (Havens.self_mem_componentWithin hseed)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    apply pass_subset ih
    intro e he hu hv
    exact Havens.componentWithin_closed hu (hsound e he) hv

theorem traverse_fixed [Fintype V] (allowed : Finset V)
    (es : List (V × V)) (seed : V) :
    pass allowed es (traverse allowed es seed) = traverse allowed es seed := by
  exact inflationary_stabilizes (pass allowed es) (pass_inflationary allowed es) {seed}

theorem seed_mem_traverse [Fintype V] (allowed : Finset V)
    (es : List (V × V)) (seed : V) : seed ∈ traverse allowed es seed :=
  seed_mem_iterate allowed es seed _

theorem traverse_closed [Fintype V] (G : SimpleGraph V) (allowed : Finset V)
    (es : List (V × V)) (seed : V)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es)
    {u v : V} (hu : u ∈ traverse allowed es seed) (hxy : G.Adj u v)
    (hv : v ∈ allowed) : v ∈ traverse allowed es seed :=
  pass_fixed_edge_closed (traverse_fixed allowed es seed) (hcomplete u v hxy) hu hv

/- Repeated sweeps of any sound and complete directed edge list compute the
entire induced component, even when edges are duplicated or arbitrarily ordered. -/
theorem traverse_eq_componentWithin [Fintype V] (G : SimpleGraph V)
    (allowed : Finset V) (es : List (V × V)) (seed : V)
    (hseed : seed ∈ allowed)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) :
    traverse allowed es seed = Havens.componentWithin G allowed seed := by
  apply Finset.Subset.antisymm
  · exact iterate_subset_componentWithin G allowed es seed hseed hsound _
  · intro v hv
    obtain ⟨_, p, hp⟩ := Havens.mem_componentWithin.mp hv
    exact Havens.mem_of_walk_closed
      (fun _ hx _ hxy hy => traverse_closed G allowed es seed hcomplete hx hxy hy)
      p (seed_mem_traverse allowed es seed) hp

theorem traverse_subset_allowed [Fintype V] (allowed : Finset V)
    (es : List (V × V)) (seed : V) (hseed : seed ∈ allowed) :
    traverse allowed es seed ⊆ allowed := by
  have hiter : ∀ n, (pass allowed es)^[n] {seed} ⊆ allowed := by
    intro n
    induction n with
    | zero => exact Finset.singleton_subset_iff.mpr hseed
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact pass_subset ih (fun _ _ _ hv => hv)
  exact hiter _

/- Direct logical reachability specification for the executable marking routine. -/
theorem mem_traverse_iff [Fintype V] (G : SimpleGraph V)
    (allowed : Finset V) (es : List (V × V)) (seed v : V)
    (hseed : seed ∈ allowed)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) :
    v ∈ traverse allowed es seed ↔
      ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∈ allowed := by
  rw [traverse_eq_componentWithin G allowed es seed hseed hsound hcomplete,
    Havens.mem_componentWithin]
  constructor
  · exact And.right
  · intro h
    exact ⟨h.choose_spec v h.choose.end_mem_support, h⟩

end StableMSR.Recovery.ComponentTraversal



namespace StableMSR.Recovery.ComponentMemory

/- Integer memory address of a vertex in a contiguous bitmap. -/
/- Exact zero/one encoding of a finite set in integer memory. -/
/- One actual memory update, with integer endpoints supplied by the edge array. -/
def markMemory (allowedBase reachedBase u v : ℤ) (mem : ℤ → ℤ) : ℤ → ℤ :=
  if 0 < mem (reachedBase + u) ∧ 0 < mem (allowedBase + v) then
    Function.update mem (reachedBase + v) 1
  else mem

/- The memory effect of one complete scan of the directed edge array. -/
def memoryPass {n : ℕ} (allowedBase reachedBase : ℤ)
    (es : List (Fin n × Fin n)) (mem : ℤ → ℤ) : ℤ → ℤ :=
  es.foldl (fun m e => markMemory allowedBase reachedBase e.1.val e.2.val m) mem

/- Read-only bitmap cells are separate from all writable reached cells. -/
@[simp] theorem address_eq_iff {n : ℕ} (base : ℤ) (u v : Fin n) :
    address base u = address base v ↔ u = v := by
  constructor
  · intro h
    apply Fin.ext
    have h' : (u.val : ℤ) = (v.val : ℤ) := by simpa [address] using h
    exact_mod_cast h'
  · rintro rfl
    rfl

 theorem markMemory_frame (allowedBase reachedBase u v : ℤ)
    (mem : ℤ → ℤ) (x : ℤ) (hx : x ≠ reachedBase + v) :
    markMemory allowedBase reachedBase u v mem x = mem x := by
  simp only [markMemory]
  split
  · exact Function.update_of_ne hx _ _
  · rfl

 theorem markMemory_bitmap {n : ℕ} {mem : ℤ → ℤ}
    {allowedBase reachedBase : ℤ} {A R : Finset (Fin n)}
    (hA : Bitmap mem allowedBase A) (hR : Bitmap mem reachedBase R)
    (e : Fin n × Fin n) :
    Bitmap (markMemory allowedBase reachedBase e.1.val e.2.val mem) reachedBase
      (ComponentTraversal.relax A R e) := by
  intro x
  have hsource := hR e.1
  have htarget := hA e.2
  dsimp [address] at hsource htarget
  by_cases hu : e.1 ∈ R <;> by_cases hv : e.2 ∈ A
  · simp only [hu, hv, if_true] at hsource htarget
    simp only [markMemory, hsource, htarget, zero_lt_one, and_self, if_true,
      ComponentTraversal.relax, hu, hv, and_self, if_true]
    by_cases hx : x = e.2
    · subst x
      simp [address]
    · have haddr : address reachedBase x ≠ reachedBase + (e.2.val : ℤ) := by
        change address reachedBase x ≠ address reachedBase e.2
        exact fun h => hx ((address_eq_iff reachedBase x e.2).mp h)
      rw [Function.update_of_ne haddr]
      simpa [hx] using hR x
  · simp [markMemory, hsource, htarget, hu, hv, ComponentTraversal.relax, hR x]
  · simp [markMemory, hsource, htarget, hu, hv, ComponentTraversal.relax, hR x]
  · simp [markMemory, hsource, htarget, hu, hv, ComponentTraversal.relax, hR x]

 theorem markMemory_preserves_bitmap {n : ℕ} {mem : ℤ → ℤ}
    {allowedBase reachedBase : ℤ} {A : Finset (Fin n)}
    (hsep : Separate (n := n) allowedBase reachedBase)
    (hA : Bitmap mem allowedBase A) (e : Fin n × Fin n) :
    Bitmap (markMemory allowedBase reachedBase e.1.val e.2.val mem) allowedBase A := by
  intro x
  rw [markMemory_frame allowedBase reachedBase _ _ mem _ (hsep x e.2)]
  exact hA x

 theorem memoryPass_refines {n : ℕ} {mem : ℤ → ℤ}
    {allowedBase reachedBase : ℤ} {A R : Finset (Fin n)}
    (hsep : Separate (n := n) allowedBase reachedBase)
    (hA : Bitmap mem allowedBase A) (hR : Bitmap mem reachedBase R)
    (es : List (Fin n × Fin n)) :
    Bitmap (memoryPass allowedBase reachedBase es mem) allowedBase A ∧
    Bitmap (memoryPass allowedBase reachedBase es mem) reachedBase
      (ComponentTraversal.pass A es R) := by
  induction es generalizing mem R with
  | nil => exact ⟨hA, hR⟩
  | cons e es ih =>
    exact ih (markMemory_preserves_bitmap hsep hA e) (markMemory_bitmap hA hR e)

 theorem memoryPass_frame {n : ℕ} (allowedBase reachedBase : ℤ)
    (es : List (Fin n × Fin n)) (mem : ℤ → ℤ) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address reachedBase v) :
    memoryPass allowedBase reachedBase es mem x = mem x := by
  induction es generalizing mem with
  | nil => rfl
  | cons e es ih =>
    change memoryPass allowedBase reachedBase es
      (markMemory allowedBase reachedBase e.1.val e.2.val mem) x = mem x
    rw [ih]
    exact markMemory_frame _ _ _ _ _ _ (hx e.2)

 theorem memoryPass_iterate_refines {n : ℕ} {mem : ℤ → ℤ}
    {allowedBase reachedBase : ℤ} {A R : Finset (Fin n)}
    (hsep : Separate (n := n) allowedBase reachedBase)
    (hA : Bitmap mem allowedBase A) (hR : Bitmap mem reachedBase R)
    (es : List (Fin n × Fin n)) (q : ℕ) :
    Bitmap ((memoryPass allowedBase reachedBase es)^[q] mem) allowedBase A ∧
    Bitmap ((memoryPass allowedBase reachedBase es)^[q] mem) reachedBase
      ((ComponentTraversal.pass A es)^[q] R) := by
  induction q with
  | zero => exact ⟨hA, hR⟩
  | succ q ih =>
    simp only [Function.iterate_succ_apply']
    exact memoryPass_refines hsep ih.1 ih.2 es

 theorem memoryPass_iterate_frame {n : ℕ} (allowedBase reachedBase : ℤ)
    (es : List (Fin n × Fin n)) (mem : ℤ → ℤ) (q : ℕ) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address reachedBase v) :
    (memoryPass allowedBase reachedBase es)^[q] mem x = mem x := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply', memoryPass_frame _ _ _ _ _ hx, ih]

/- Two integer endpoint cells per directed edge, indexed from zero. -/
/- Edge endpoint cells are outside the writable reached bitmap. -/
 theorem memoryPass_iterate_preserves_edges {n : ℕ} {mem : ℤ → ℤ}
    (allowedBase reachedBase edgeBase : ℤ) (es : List (Fin n × Fin n))
    (hsep : EdgesSeparate edgeBase reachedBase es)
    (hencode : EdgeEncoding mem edgeBase es) (q : ℕ) :
    EdgeEncoding ((memoryPass allowedBase reachedBase es)^[q] mem) edgeBase es := by
  intro j hj
  rw [memoryPass_iterate_frame _ _ _ _ _ _ (fun v => (hsep j hj v).1),
      memoryPass_iterate_frame _ _ _ _ _ _ (fun v => (hsep j hj v).2)]
  exact hencode j hj


/- Concatenating edge scans composes their memory effects. -/
theorem memoryPass_append {n : ℕ} (allowedBase reachedBase : ℤ)
    (xs ys : List (Fin n × Fin n)) (mem : ℤ → ℤ) :
    memoryPass allowedBase reachedBase (xs ++ ys) mem =
      memoryPass allowedBase reachedBase ys
        (memoryPass allowedBase reachedBase xs mem) := by
  exact List.foldl_append

/- Every finite partial scan preserves the endpoint array. -/
theorem memoryPass_preserves_edges {n : ℕ} {mem : ℤ → ℤ}
    (allowedBase reachedBase edgeBase : ℤ) (xs es : List (Fin n × Fin n))
    (hsep : EdgesSeparate edgeBase reachedBase es)
    (hencode : EdgeEncoding mem edgeBase es) :
    EdgeEncoding (memoryPass allowedBase reachedBase xs mem) edgeBase es := by
  intro j hj
  rw [memoryPass_frame _ _ _ _ _ (fun v => (hsep j hj v).1),
      memoryPass_frame _ _ _ _ _ (fun v => (hsep j hj v).2)]
  exact hencode j hj

/- A vertex-sized number of scans produces exactly the desired component bitmap. -/
theorem memoryPass_iterate_component {n : ℕ} {mem : ℤ → ℤ}
    {allowedBase reachedBase : ℤ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (es : List (Fin n × Fin n)) (seed : Fin n)
    (hsep : Separate (n := n) allowedBase reachedBase)
    (hA : Bitmap mem allowedBase A) (hR : Bitmap mem reachedBase {seed})
    (hseed : seed ∈ A) (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) :
    Bitmap ((memoryPass allowedBase reachedBase es)^[n] mem) allowedBase A ∧
    Bitmap ((memoryPass allowedBase reachedBase es)^[n] mem) reachedBase
      (Havens.componentWithin G A seed) := by
  have h := memoryPass_iterate_refines hsep hA hR es n
  refine ⟨h.1, ?_⟩
  have heq : (ComponentTraversal.pass A es)^[n] {seed} =
      Havens.componentWithin G A seed := by
    simpa [ComponentTraversal.traverse] using
      ComponentTraversal.traverse_eq_componentWithin G A es seed hseed hsound hcomplete
  simpa only [heq] using h.2

/- Direct readback: a final positive flag is equivalent to an allowed graph walk. -/
theorem memoryPass_iterate_positive_iff {n : ℕ} {mem : ℤ → ℤ}
    {allowedBase reachedBase : ℤ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (es : List (Fin n × Fin n)) (seed v : Fin n)
    (hsep : Separate (n := n) allowedBase reachedBase)
    (hA : Bitmap mem allowedBase A) (hR : Bitmap mem reachedBase {seed})
    (hseed : seed ∈ A) (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) :
    0 < (memoryPass allowedBase reachedBase es)^[n] mem (address reachedBase v) ↔
      ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∈ A := by
  have h := (memoryPass_iterate_component G A es seed hsep hA hR
    hseed hsound hcomplete).2 v
  rw [h]
  have hp : (0 : ℤ) < (if v ∈ Havens.componentWithin G A seed then 1 else 0) ↔
      v ∈ Havens.componentWithin G A seed := by
    by_cases hv : v ∈ Havens.componentWithin G A seed <;> simp [hv]
  rw [hp, Havens.mem_componentWithin]
  constructor
  · exact And.right
  · intro hwalk
    exact ⟨hwalk.choose_spec v hwalk.choose.end_mem_support, hwalk⟩

end StableMSR.Recovery.ComponentMemory




open scoped Classical
namespace StableMSR.Recovery.Compiler.ComponentMachine

/- The graph bases and dimensions occupy registers 2--6; registers 7--14
are scratch. The command reads an ordinary directed edge list and two bitmaps. -/
def setPtr (s : Store) (i : ℕ) (z : ℤ) : Store :=
  { s with ptrs := Function.update s.ptrs i z }

def incPtr (s : Store) (i : ℕ) : Store := setPtr s i (s.ptrs i+1)

def opsCmd : List Op → Cmd
  | [] => .skip
  | op :: ops => .seq (.atom op) (opsCmd ops)

noncomputable def evalOps {N : ℕ} (d : Point N → Point N → ℝ) : List Op → Store → Store
  | [], s => s
  | op :: ops, s => evalOps d ops (op.eval d s)

lemma ops_exec {N : ℕ} (d : Point N → Point N → ℝ) (ops : List Op) (s : Store) :
    Executes d (opsCmd ops) s (evalOps d ops s) ops.length := by
  induction ops generalizing s with
  | nil => exact Executes.skip s
  | cons op ops ih =>
    simpa [opsCmd, evalOps, Nat.add_comm] using
      Executes.seq (Executes.atom op s) (ih (op.eval d s))

def nop : Cmd := .atom (.pointerCopy 0 0)
def pad2 : Cmd := .seq nop nop
def pad4 : Cmd := .seq pad2 pad2

lemma nop_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d nop s s 1 := by
  simpa [nop, Op.eval, Function.update_eq_self] using Executes.atom (Op.pointerCopy 0 0) s
lemma pad2_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d pad2 s s 2 := Executes.seq (nop_exec d s) (nop_exec d s)
lemma pad4_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d pad4 s s 4 := Executes.seq (pad2_exec d s) (pad2_exec d s)

/- Padding balances all three cases, including every branch and jump. -/
def markCmd : Cmd :=
  .ite (.pointerLE 13 0) pad4
    (.ite (.pointerLE 14 0) pad2 (.atom (.integerStore 11 1)))

noncomputable def markEval (s : Store) : Store :=
  if s.ptrs 13 ≤ s.ptrs 0 then s else
  if s.ptrs 14 ≤ s.ptrs 0 then s else
  { s with imem := Function.update s.imem (s.ptrs 11) (s.ptrs 1) }

lemma mark_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d markCmd s (markEval s) 5 := by
  by_cases h13 : s.ptrs 13 ≤ s.ptrs 0
  · simpa [markCmd, markEval, h13] using
      Executes.ite_true (c := Cond.pointerLE 13 0)
        (no := Cmd.ite (.pointerLE 14 0) pad2 (.atom (.integerStore 11 1)))
        h13 (pad4_exec d s)
  · by_cases h14 : s.ptrs 14 ≤ s.ptrs 0
    · simpa [markCmd, markEval, h13, h14] using
        Executes.ite_false (c := Cond.pointerLE 13 0) (yes := pad4) h13
          (Executes.ite_true (c := Cond.pointerLE 14 0)
            (no := Cmd.atom (.integerStore 11 1)) h14 (pad2_exec d s))
    · simpa [markCmd, markEval, h13, h14, Op.eval] using
        Executes.ite_false (c := Cond.pointerLE 13 0) (yes := pad4) h13
          (Executes.ite_false (c := Cond.pointerLE 14 0) (yes := pad2) h14
            (Executes.atom (.integerStore 11 1) s))

def edgeOps : List Op :=
  [.integerLoad 10 7, .pointerInc 7, .integerLoad 11 7, .pointerInc 7,
   .pointerAdd 10 4 10, .pointerAdd 12 3 11, .pointerAdd 11 4 11,
   .integerLoad 13 10, .integerLoad 14 12]

def edgeCmd : Cmd := .seq (opsCmd edgeOps) (.seq markCmd (.atom (.pointerInc 8)))

noncomputable def edgeInput (s : Store) : Store :=
  let a := s.imem (s.ptrs 7)
  let b := s.imem (s.ptrs 7+1)
  let t := setPtr (setPtr (setPtr (setPtr s 7 (s.ptrs 7+2))
    10 (s.ptrs 4+a)) 12 (s.ptrs 3+b)) 11 (s.ptrs 4+b)
  setPtr (setPtr t 13 (s.imem (s.ptrs 4+a))) 14 (s.imem (s.ptrs 3+b))

noncomputable def edgeStep (s : Store) : Store := incPtr (markEval (edgeInput s)) 8

lemma edgeInput_eq {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    evalOps d edgeOps s = edgeInput s := by
  simp [evalOps, edgeOps, Op.eval, edgeInput, setPtr, Function.update_comm,
    Function.update_idem, add_assoc]

lemma edge_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d edgeCmd s (edgeStep s) 15 := by
  have hp : Executes d (opsCmd edgeOps) s (edgeInput s) 9 := by
    have h := ops_exec d edgeOps s
    rw [edgeInput_eq] at h
    exact h
  exact Executes.seq hp (Executes.seq (mark_exec d _) (Executes.atom (.pointerInc 8) _))

lemma mark_ptrs (s : Store) : (markEval s).ptrs = s.ptrs := by
  simp only [markEval]; split <;> (try split) <;> rfl

lemma edge_ptr_frame (s : Store) (j : ℕ)
    (hj : j ≠ 7 ∧ j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j ≠ 12 ∧ j ≠ 13 ∧ j ≠ 14) :
    (edgeStep s).ptrs j = s.ptrs j := by
  rcases hj with ⟨h7,h8,h10,h11,h12,h13,h14⟩
  simp [edgeStep, incPtr, setPtr, mark_ptrs, edgeInput,
    h7,h8,h10,h11,h12,h13,h14]

lemma edge_index (s : Store) : (edgeStep s).ptrs 8 = s.ptrs 8+1 := by
  simp [edgeStep, incPtr, setPtr, mark_ptrs, edgeInput]
lemma edge_cursor (s : Store) : (edgeStep s).ptrs 7 = s.ptrs 7+2 := by
  simp [edgeStep, incPtr, setPtr, mark_ptrs, edgeInput]

lemma iterate_preserves {α : Type*} (f : Store → Store) (F : Store → α)
    (h : ∀ s, F (f s) = F s) (q : ℕ) (s : Store) : F (f^[q] s) = F s := by
  induction q with
  | zero => rfl
  | succ q ih => rw [Function.iterate_succ_apply',h,ih]

lemma iterate_additive (f : Store → Store) (F : Store → ℤ) (a : ℤ)
    (h : ∀ s, F (f s) = F s+a) (q : ℕ) (s : Store) :
    F (f^[q] s) = F s+(q:ℤ)*a := by
  induction q with
  | zero => simp
  | succ q ih => rw [Function.iterate_succ_apply',h,ih]; push_cast; ring

lemma fixed_loop_exec {N : ℕ} (d : Point N → Point N → ℝ)
    (body : Cmd) (f : Store → Store) (i b cost : ℕ) (bound : ℤ)
    (he : ∀ s, s.ptrs b = bound → Executes d body s (f s) cost)
    (hi : ∀ s, (f s).ptrs i = s.ptrs i+1)
    (hbframe : ∀ s, (f s).ptrs b = s.ptrs b)
    (q : ℕ) (s : Store) (hb : s.ptrs b = bound)
    (hstop : s.ptrs i+(q:ℤ)-1 = bound) :
    Executes d (.whileDo (.pointerLE i b) body) s (f^[q] s) ((cost+2)*q+2) := by
  induction q generalizing s with
  | zero =>
    apply Executes.while_false
    simp only [Cond.test]
    omega
  | succ q ih =>
    have ht : (Cond.pointerLE i b).test s := by simp only [Cond.test]; omega
    have hrest := ih (f s) (by rw [hbframe,hb]) (by rw [hi]; push_cast at hstop; omega)
    have hrun := Executes.while_true ht (he s hb) hrest
    convert hrun using 1
    · exact Function.iterate_succ_apply f q s
    · simp only [Nat.mul_succ]; omega

def passSetupCmd : Cmd := opsCmd [.pointerCopy 7 2, .pointerConst 8 1]
def passSetup (s : Store) : Store := setPtr (setPtr s 7 (s.ptrs 2)) 8 1

def passCmd : Cmd := .seq passSetupCmd (.whileDo (.pointerLE 8 5) edgeCmd)
noncomputable def passEval (m : ℕ) (s : Store) : Store := edgeStep^[m] (passSetup s)

lemma pass_exec {N : ℕ} (d : Point N → Point N → ℝ) (m : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) :
    Executes d passCmd s (passEval m s) (17*m+4) := by
  have hs : Executes d passSetupCmd s (passSetup s) 2 := by
    simpa [passSetupCmd, evalOps, Op.eval, passSetup, setPtr] using
      ops_exec d [.pointerCopy 7 2, .pointerConst 8 1] s
  have hl := fixed_loop_exec d edgeCmd edgeStep 8 5 15 m
    (fun t _ => edge_exec d t) edge_index
    (fun t => edge_ptr_frame t 5 (by norm_num)) m (passSetup s)
    (by simpa [passSetup,setPtr] using hm) (by simp [passSetup,setPtr])
  convert Executes.seq hs hl using 1 <;> try rfl
  omega

lemma pass_ptr_frame (m : ℕ) (s : Store) (j : ℕ)
    (hj : j ≠ 7 ∧ j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j ≠ 12 ∧ j ≠ 13 ∧ j ≠ 14) :
    (passEval m s).ptrs j = s.ptrs j := by
  unfold passEval
  rw [iterate_preserves _ (fun t => t.ptrs j) (fun t => edge_ptr_frame t j hj)]
  simp [passSetup,setPtr,hj.1,hj.2.1]

lemma pass_cursor (m : ℕ) (s : Store) :
    (passEval m s).ptrs 7 = s.ptrs 2+2*(m:ℤ) := by
  unfold passEval
  rw [iterate_additive _ (fun t => t.ptrs 7) 2 edge_cursor]
  simp [passSetup,setPtr,mul_comm]

lemma pass_index (m : ℕ) (s : Store) : (passEval m s).ptrs 8 = (m:ℤ)+1 := by
  unfold passEval
  rw [iterate_additive _ (fun t => t.ptrs 8) 1 edge_index]
  simp [passSetup,setPtr,add_comm]

noncomputable def passStep (m : ℕ) (s : Store) : Store := incPtr (passEval m s) 9

def setupCmd : Cmd := opsCmd [.pointerConst 0 0, .pointerConst 1 1, .pointerConst 9 1]
def setup (s : Store) : Store := setPtr (setPtr (setPtr s 0 0) 1 1) 9 1

def block : Cmd := .seq setupCmd
  (.whileDo (.pointerLE 9 6) (.seq passCmd (.atom (.pointerInc 9))))
noncomputable def blockEval (m q : ℕ) (s : Store) : Store := (passStep m)^[q] (setup s)

lemma passStep_ptr_frame (m : ℕ) (s : Store) (j : ℕ)
    (hj : j < 7 ∨ 14 < j) : (passStep m s).ptrs j = s.ptrs j := by
  have h9 : j ≠ 9 := by omega
  simp only [passStep,incPtr,setPtr,Function.update_of_ne h9]
  apply pass_ptr_frame
  omega

lemma block_exec {N : ℕ} (d : Point N → Point N → ℝ) (m q : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 6 = (q:ℤ)) :
    Executes d block s (blockEval m q s) (q*(17*m+7)+5) := by
  have hs : Executes d setupCmd s (setup s) 3 := by
    simpa [setupCmd,evalOps,Op.eval,setup,setPtr] using
      ops_exec d [.pointerConst 0 0, .pointerConst 1 1, .pointerConst 9 1] s
  have hbody (t : Store) (ht : t.ptrs 5 = (m:ℤ)) :
      Executes d (.seq passCmd (.atom (.pointerInc 9))) t (passStep m t) (17*m+5) := by
    simpa [passStep,incPtr,setPtr,Op.eval,Nat.add_assoc] using
      Executes.seq (pass_exec d m t ht) (Executes.atom (.pointerInc 9) (passEval m t))
  have h5 (r : ℕ) : ((passStep m)^[r] (setup s)).ptrs 5 = (m:ℤ) := by
    rw [iterate_preserves _ (fun t => t.ptrs 5) (fun t => passStep_ptr_frame m t 5 (by omega))]
    simpa [setup,setPtr] using hm
  -- Induction carries the edge-count input as well as the outer-loop bound.
  have loop : ∀ (r : ℕ) (t : Store), t.ptrs 5 = (m:ℤ) → t.ptrs 6 = (q:ℤ) →
      t.ptrs 9+(r:ℤ)-1 = (q:ℤ) →
      Executes d (.whileDo (.pointerLE 9 6) (.seq passCmd (.atom (.pointerInc 9))))
        t ((passStep m)^[r] t) ((17*m+7)*r+2) := by
    intro r
    induction r with
    | zero =>
      intro t ht5 ht6 ht9
      apply Executes.while_false
      simp only [Cond.test]
      omega
    | succ r ih =>
      intro t ht5 ht6 ht9
      have hg : (Cond.pointerLE 9 6).test t := by simp only [Cond.test]; omega
      have ht9' : (passStep m t).ptrs 9 = t.ptrs 9+1 := by
        simp [passStep,incPtr,setPtr,pass_ptr_frame m t 9 (by norm_num)]
      have hr := ih (passStep m t)
        (by rw [passStep_ptr_frame m t 5 (by omega),ht5])
        (by rw [passStep_ptr_frame m t 6 (by omega),ht6])
        (by rw [ht9']; push_cast at ht9; omega)
      have hh := Executes.while_true hg (hbody t ht5) hr
      convert hh using 1
      · exact Function.iterate_succ_apply (passStep m) r t
      · simp only [Nat.mul_succ]; omega
  have hl := loop q (setup s) (by simpa [setup,setPtr] using hm)
    (by simpa [setup,setPtr] using hq) (by simp [setup,setPtr])
  convert Executes.seq hs hl using 1 <;> try rfl
  ring

lemma block_ptr_frame (m q : ℕ) (s : Store) (j : ℕ)
    (hj : 2 ≤ j ∧ j ≤ 6 ∨ 14 < j) : (blockEval m q s).ptrs j = s.ptrs j := by
  unfold blockEval
  rw [iterate_preserves _ (fun t => t.ptrs j)
    (fun t => passStep_ptr_frame m t j (by omega))]
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  have h9 : j ≠ 9 := by omega
  simp [setup,setPtr,h0,h1,h9]

/- Graph traversal changes integer scratch and reached flags only. -/
def DataFrame (s t : Store) : Prop :=
  t.regs = s.regs ∧ t.mem = s.mem ∧ t.queries = s.queries ∧
    t.tapePos = s.tapePos ∧ t.output = s.output

lemma DataFrame.refl (s : Store) : DataFrame s s := ⟨rfl,rfl,rfl,rfl,rfl⟩
lemma DataFrame.trans {s t u : Store} (h : DataFrame s t) (k : DataFrame t u) :
    DataFrame s u := ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
      k.2.2.2.1.trans h.2.2.2.1,k.2.2.2.2.trans h.2.2.2.2⟩

lemma setPtr_frame (s : Store) (i : ℕ) (z : ℤ) : DataFrame s (setPtr s i z) :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩
lemma incPtr_frame (s : Store) (i : ℕ) : DataFrame s (incPtr s i) :=
  setPtr_frame s i _
lemma edge_frame (s : Store) : DataFrame s (edgeStep s) := by
  unfold edgeStep incPtr setPtr markEval
  split <;> (try split) <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma iterate_frame (f : Store → Store) (h : ∀ t, DataFrame t (f t))
    (q : ℕ) (s : Store) : DataFrame s (f^[q] s) := by
  induction q with
  | zero => exact DataFrame.refl s
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (h _)

lemma pass_frame (m : ℕ) (s : Store) : DataFrame s (passEval m s) :=
  (show DataFrame s (passSetup s) from ⟨rfl,rfl,rfl,rfl,rfl⟩).trans
    (iterate_frame edgeStep edge_frame m (passSetup s))

lemma passStep_frame (m : ℕ) (s : Store) : DataFrame s (passStep m s) :=
  (pass_frame m s).trans (incPtr_frame _ 9)

lemma block_frame (m q : ℕ) (s : Store) : DataFrame s (blockEval m q s) :=
  (show DataFrame s (setup s) from ⟨rfl,rfl,rfl,rfl,rfl⟩).trans
    (iterate_frame (passStep m) (passStep_frame m) q (setup s))

lemma block_constants (m q : ℕ) (s : Store) :
    (blockEval m q s).ptrs 0 = 0 ∧ (blockEval m q s).ptrs 1 = 1 := by
  constructor
  · unfold blockEval
    rw [iterate_preserves _ (fun t => t.ptrs 0)
      (fun t => passStep_ptr_frame m t 0 (by omega))]
    simp [setup,setPtr]
  · unfold blockEval
    rw [iterate_preserves _ (fun t => t.ptrs 1)
      (fun t => passStep_ptr_frame m t 1 (by omega))]
    simp [setup,setPtr]

noncomputable def program : MinSumFPT.Program := compile block 0

lemma block_size : block.size = 33 := by decide
lemma program_length : program.length = 34 := by
  simp [program,compile,compileAt_length,block_size]

theorem kernel_machine_execution {N : ℕ} (d : Point N → Point N → ℝ)
    (m q : ℕ) (s : Store) (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 6 = (q:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[q*(17*m+7)+6] (s.state 0 work) =
      (blockEval m q s).haltedState 33 (work+(q*(17*m+7)+6)) 0 := by
  simpa [program,block_size,Nat.add_assoc] using compile_halts (block_exec d m q s hm hq) ω work 0

theorem kernel_cubic_bound (n m : ℕ) (hm : m ≤ n^2) :
    n*(17*m+7)+6 ≤ 30*(n+1)^3 := by
  have hmul := Nat.mul_le_mul_left n hm
  nlinarith

/- A single finite graph-scanning program, with uniform source size and an
exact charged run on every edge-list dimension and requested pass count. -/
theorem kernel_uniform :
    program.length = 34 ∧ DeterministicProgram program ∧
    ∀ (N : ℕ) (d : Point N → Point N → ℝ) (m q : ℕ) (s : Store),
      s.ptrs 5 = (m:ℤ) → s.ptrs 6 = (q:ℤ) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      (MinSumFPT.step program d ω)^[q*(17*m+7)+6] (s.state 0 work) =
        (blockEval m q s).haltedState 33 (work+(q*(17*m+7)+6)) 0 := by
  exact ⟨program_length,compile_deterministic block 0,
    fun _ d m q s hm hq ω work => kernel_machine_execution d m q s hm hq ω work⟩

end StableMSR.Recovery.Compiler.ComponentMachine



namespace StableMSR.Recovery.Compiler.ComponentMachine
open StableMSR.Recovery.ComponentMemory

/- The actual read/branch/store step has precisely the abstract marking effect. -/
theorem edgeStep_imem (s : Store) (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1) :
    (edgeStep s).imem =
      markMemory (s.ptrs 3) (s.ptrs 4) (s.imem (s.ptrs 7))
        (s.imem (s.ptrs 7 + 1)) s.imem := by
  simp [edgeStep, incPtr, setPtr, markEval, edgeInput, markMemory, h0, h1]
  split <;> (try split) <;> simp_all <;> omega

 theorem edge_low (s : Store) (j : ℕ) (hj : j < 7) :
    (edgeStep s).ptrs j = s.ptrs j :=
  edge_ptr_frame s j (by omega)

 theorem encoding_tail {n : ℕ} {mem : ℤ → ℤ} {base : ℤ}
    {e : Fin n × Fin n} {es : List (Fin n × Fin n)}
    (h : EdgeEncoding mem base (e :: es)) : EdgeEncoding mem (base + 2) es := by
  intro j hj
  have h' := h (j + 1) (by simpa using Nat.succ_lt_succ hj)
  simpa [List.getElem_cons_succ, Nat.cast_add, Nat.cast_one,
    mul_add, add_assoc, add_comm, add_left_comm] using h'

 theorem separation_tail {n : ℕ} {base reachedBase : ℤ}
    {e : Fin n × Fin n} {es : List (Fin n × Fin n)}
    (h : EdgesSeparate base reachedBase (e :: es)) :
    EdgesSeparate (base + 2) reachedBase es := by
  intro j hj v
  have h' := h (j + 1) (by simpa using Nat.succ_lt_succ hj) v
  simpa [Nat.cast_add, Nat.cast_one, mul_add, add_assoc, add_comm, add_left_comm] using h'

/- Sequentially executing the edge step follows the input list exactly, while
writes to the reached bitmap leave all future endpoint reads unchanged. -/
theorem edgeSteps_imem {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1)
    (hencode : EdgeEncoding s.imem (s.ptrs 7) es)
    (hsep : EdgesSeparate (s.ptrs 7) (s.ptrs 4) es) :
    (edgeStep^[es.length] s).imem =
      memoryPass (s.ptrs 3) (s.ptrs 4) es s.imem := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    have hh := hencode 0 (by simp)
    simp only [Nat.cast_zero, mul_zero, add_zero, List.getElem_cons_zero] at hh
    have hm : (edgeStep s).imem =
        markMemory (s.ptrs 3) (s.ptrs 4) e.1.val e.2.val s.imem := by
      simpa only [hh.1, hh.2] using edgeStep_imem s h0 h1
    have he : EdgeEncoding (edgeStep s).imem (s.ptrs 7) (e :: es) := by
      rw [hm]
      exact memoryPass_preserves_edges (s.ptrs 3) (s.ptrs 4) (s.ptrs 7)
        [e] (e :: es) hsep hencode
    have htail : EdgeEncoding (edgeStep s).imem ((edgeStep s).ptrs 7) es := by
      rw [edge_cursor]
      exact encoding_tail he
    have htailsep : EdgesSeparate ((edgeStep s).ptrs 7) ((edgeStep s).ptrs 4) es := by
      rw [edge_cursor, edge_low s 4 (by omega)]
      exact separation_tail hsep
    rw [List.length_cons, Function.iterate_succ_apply]
    rw [ih (edgeStep s) (by rw [edge_low s 0 (by omega), h0])
      (by rw [edge_low s 1 (by omega), h1]) htail htailsep]
    rw [edge_low s 3 (by omega), edge_low s 4 (by omega), hm]
    rfl

/- A complete interpreter scan refines the finite-set scan's memory fold. -/
theorem passEval_imem {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1)
    (hencode : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) :
    (passEval es.length s).imem =
      memoryPass (s.ptrs 3) (s.ptrs 4) es s.imem := by
  apply edgeSteps_imem es (passSetup s)
    (by simpa [passSetup, setPtr] using h0)
    (by simpa [passSetup, setPtr] using h1)
    (by simpa [passSetup, setPtr] using hencode)
    (by simpa [passSetup, setPtr] using hsep)

 theorem passStep_imem {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1)
    (hencode : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) :
    (passStep es.length s).imem =
      memoryPass (s.ptrs 3) (s.ptrs 4) es s.imem :=
  passEval_imem es s h0 h1 hencode hsep

 theorem passSteps_imem {n : ℕ} (es : List (Fin n × Fin n)) (q : ℕ) (s : Store)
    (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1)
    (hencode : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) :
    ((passStep es.length)^[q] s).imem =
      (memoryPass (s.ptrs 3) (s.ptrs 4) es)^[q] s.imem := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih =>
    have hf (j : ℕ) (hj : j < 7) :
        (passStep es.length s).ptrs j = s.ptrs j :=
      passStep_ptr_frame es.length s j (Or.inl hj)
    have hm := passStep_imem es s h0 h1 hencode hsep
    have he : EdgeEncoding (passStep es.length s).imem
        ((passStep es.length s).ptrs 2) es := by
      rw [hf 2 (by omega), hm]
      exact memoryPass_preserves_edges (s.ptrs 3) (s.ptrs 4) (s.ptrs 2) es es hsep hencode
    have hs : EdgesSeparate ((passStep es.length s).ptrs 2)
        ((passStep es.length s).ptrs 4) es := by
      rwa [hf 2 (by omega), hf 4 (by omega)]
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    rw [ih (passStep es.length s) (by rw [hf 0 (by omega), h0])
      (by rw [hf 1 (by omega), h1]) he hs]
    rw [hf 3 (by omega), hf 4 (by omega), hm]

/- The complete actual interpreter block implements exactly the repeated
memory scans. Constant-register initialization is internal to the block. -/
theorem blockEval_imem {n : ℕ} (es : List (Fin n × Fin n)) (q : ℕ) (s : Store)
    (hencode : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) :
    (blockEval es.length q s).imem =
      (memoryPass (s.ptrs 3) (s.ptrs 4) es)^[q] s.imem := by
  apply passSteps_imem es q (setup s)
    (by simp [setup, setPtr]) (by simp [setup, setPtr])
    (by simpa [setup, setPtr] using hencode)
    (by simpa [setup, setPtr] using hsep)


/- Exact graph-component meaning of the actual block's reached bitmap. -/
theorem blockEval_component {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (hencode : EdgeEncoding s.imem (s.ptrs 2) es)
    (hedges : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hA : Bitmap s.imem (s.ptrs 3) A) (hR : Bitmap s.imem (s.ptrs 4) {seed})
    (hseed : seed ∈ A) (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) :
    Bitmap (blockEval es.length n s).imem (s.ptrs 3) A ∧
    Bitmap (blockEval es.length n s).imem (s.ptrs 4)
      (Havens.componentWithin G A seed) := by
  rw [blockEval_imem es n s hencode hedges]
  exact memoryPass_iterate_component G A es seed hsep hA hR hseed hsound hcomplete

/- The actual block preserves every integer cell outside the reached bitmap. -/
theorem blockEval_imem_frame {n : ℕ} (es : List (Fin n × Fin n)) (q : ℕ) (s : Store)
    (hencode : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (blockEval es.length q s).imem x = s.imem x := by
  rw [blockEval_imem es q s hencode hsep]
  exact memoryPass_iterate_frame _ _ _ _ _ _ hx

end StableMSR.Recovery.Compiler.ComponentMachine




set_option autoImplicit false

namespace StableMSR.Recovery.Compiler.ComponentInit

open BitmapFill TupleWriter ComponentMemory

/- Initialize constants and the inclusive bounds of the reached bitmap. -/
def prepCmd : Cmd :=
  .seq (.atom (.pointerConst 0 0))
    (.seq (.atom (.pointerConst 1 1))
      (.seq (.atom (.pointerCopy 15 4))
        (.seq (.atom (.pointerAdd 16 4 6)) (.atom (.pointerDec 16)))))

def prepEval (s : Store) : Store :=
  { s with ptrs := (Function.update
      (Function.update (Function.update (Function.update s.ptrs 0 0) 1 1) 15 (s.ptrs 4))
      16 (s.ptrs 4 + s.ptrs 6 - 1)) }

/- Mark the seed after zero-filling all reached cells. -/
def seedCmd : Cmd :=
  .seq (.atom (.pointerAdd 15 4 17)) (.atom (.integerStore 15 1))

def seedEval (s : Store) : Store :=
  { s with
    ptrs := Function.update s.ptrs 15 (s.ptrs 4 + s.ptrs 17)
    imem := Function.update s.imem (s.ptrs 4 + s.ptrs 17) (s.ptrs 1) }

/- Fixed initialization code; the vertex count is read from pointer register 6. -/
def initCmd : Cmd := .seq prepCmd (.seq (fillCmd 15 16 0) seedCmd)

def initEval (q : ℕ) (s : Store) : Store :=
  seedEval (fillEval 15 0 q (prepEval s))

@[simp] lemma initCmd_size : initCmd.size = 12 := rfl

lemma prep_exec {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    Executes d prepCmd s (prepEval s) 5 := by
  have h := Executes.seq (Executes.atom (.pointerConst 0 0) (d := d) s)
    (Executes.seq (Executes.atom (.pointerConst 1 1) (d := d) _)
      (Executes.seq (Executes.atom (.pointerCopy 15 4) (d := d) _)
        (Executes.seq (Executes.atom (.pointerAdd 16 4 6) (d := d) _)
          (Executes.atom (.pointerDec 16) (d := d) _))))
  simpa [prepCmd,prepEval,Op.eval,Function.update_idem] using h

lemma seed_exec {n : ℕ} (d : Point n → Point n → ℝ) (s : Store) :
    Executes d seedCmd s (seedEval s) 2 := by
  have h := Executes.seq (Executes.atom (.pointerAdd 15 4 17) (d := d) s)
    (Executes.atom (.integerStore 15 1) (d := d) _)
  simpa [seedCmd,seedEval,Op.eval] using h

lemma init_exec {n : ℕ} (d : Point n → Point n → ℝ)
    (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    Executes d initCmd s (initEval q s) (4*q+9) := by
  have hstop : (prepEval s).ptrs 16 = (prepEval s).ptrs 15 + (q : ℤ) - 1 := by
    simp [prepEval,hcount]
  have hf := fill_exec d 15 16 0 q (prepEval s) (by decide) hstop
  have h := Executes.seq (prep_exec d s)
    (Executes.seq hf (seed_exec d (fillEval 15 0 q (prepEval s))))
  simpa only [initCmd,initEval,show 5+(4*q+2+2)=4*q+9 by omega] using h

lemma init_ptr_ne (q j : ℕ) (s : Store)
    (h0 : j ≠ 0) (h1 : j ≠ 1) (h15 : j ≠ 15) (h16 : j ≠ 16) :
    (initEval q s).ptrs j = s.ptrs j := by
  simp only [initEval,seedEval,Function.update_of_ne h15]
  rw [fill_ptr_ne 15 0 q j (prepEval s) h15]
  simp [prepEval,h0,h1,h15,h16]

@[simp] lemma init_ptr_zero (q : ℕ) (s : Store) : (initEval q s).ptrs 0 = 0 := by
  simp only [initEval,seedEval,Function.update_of_ne (show (0 : ℕ) ≠ 15 by decide)]
  rw [fill_ptr_ne 15 0 q 0 (prepEval s) (by decide)]
  simp [prepEval]

@[simp] lemma init_ptr_one (q : ℕ) (s : Store) : (initEval q s).ptrs 1 = 1 := by
  simp only [initEval,seedEval,Function.update_of_ne (show (1 : ℕ) ≠ 15 by decide)]
  rw [fill_ptr_ne 15 0 q 1 (prepEval s) (by decide)]
  simp [prepEval]

lemma init_frame (q : ℕ) (s : Store) :
    (initEval q s).regs = s.regs ∧
    (initEval q s).mem = s.mem ∧
    (initEval q s).queries = s.queries ∧
    (initEval q s).tapePos = s.tapePos ∧
    (initEval q s).output = s.output :=
  fill_frame 15 0 q (prepEval s)

lemma init_memory (q : ℕ) (s : Store) :
    (initEval q s).imem =
      Function.update (writeMemory (s.ptrs 4) (List.replicate q (0 : ℤ)) s.imem)
        (s.ptrs 4 + s.ptrs 17) 1 := by
  simp only [initEval,seedEval]
  rw [fill_memory 15 0 q (prepEval s) (by decide),
    fill_ptr_ne 15 0 q 4 (prepEval s) (by decide),
    fill_ptr_ne 15 0 q 17 (prepEval s) (by decide),
    fill_ptr_ne 15 0 q 1 (prepEval s) (by decide)]
  simp [prepEval]

lemma init_bitmap {n : ℕ} (s : Store) (seed : Fin n)
    (hseed : s.ptrs 17 = (seed.val : ℤ)) :
    Bitmap (initEval n s).imem (s.ptrs 4) {seed} := by
  intro v
  rw [init_memory,hseed]
  by_cases hv : v = seed
  · subst v
    simp [address]
  · have haddr : address (s.ptrs 4) v ≠ s.ptrs 4 + (seed.val : ℤ) := by
      change address (s.ptrs 4) v ≠ address (s.ptrs 4) seed
      exact fun h => hv ((address_eq_iff _ _ _).mp h)
    rw [Function.update_of_ne haddr]
    have hi : v.val < (List.replicate n (0 : ℤ)).length := by simpa using v.isLt
    rw [address,writeMemory_get _ _ _ v.val hi]
    simp [hv]

lemma init_memory_frame {n : ℕ} (s : Store) (seed : Fin n)
    (hseed : s.ptrs 17 = (seed.val : ℤ)) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (initEval n s).imem x = s.imem x := by
  have hs : x ≠ s.ptrs 4 + (seed.val : ℤ) := hx seed
  rw [init_memory,hseed,Function.update_of_ne hs]
  by_cases hlo : x < s.ptrs 4
  · exact writeMemory_before _ _ _ _ hlo
  · have hhi : s.ptrs 4 + (n : ℤ) ≤ x := by
      by_contra hbad
      have hnonneg : 0 ≤ x - s.ptrs 4 := by omega
      have hlt : (x - s.ptrs 4).toNat < n := by omega
      let v : Fin n := ⟨(x - s.ptrs 4).toNat,hlt⟩
      have he : x = address (s.ptrs 4) v := by
        dsimp [address,v]
        omega
      exact hx v he
    apply writeMemory_after
    simpa only [List.length_replicate] using hhi

lemma init_preserves_bitmap {n : ℕ} (s : Store) (seed : Fin n)
    (hseed : s.ptrs 17 = (seed.val : ℤ)) (base : ℤ) (A : Finset (Fin n))
    (hsep : Separate (n := n) base (s.ptrs 4)) (hA : Bitmap s.imem base A) :
    Bitmap (initEval n s).imem base A := by
  intro v
  rw [init_memory_frame s seed hseed _ (fun w => hsep v w)]
  exact hA v

lemma init_preserves_edges {n : ℕ} (s : Store) (seed : Fin n)
    (hseed : s.ptrs 17 = (seed.val : ℤ)) (edgeBase : ℤ)
    (es : List (Fin n × Fin n))
    (hsep : EdgesSeparate edgeBase (s.ptrs 4) es)
    (hedges : EdgeEncoding s.imem edgeBase es) :
    EdgeEncoding (initEval n s).imem edgeBase es := by
  intro j hj
  rw [init_memory_frame s seed hseed _ (fun v => (hsep j hj v).1),
    init_memory_frame s seed hseed _ (fun v => (hsep j hj v).2)]
  exact hedges j hj

end StableMSR.Recovery.Compiler.ComponentInit



open scoped Classical

namespace StableMSR.Recovery.Compiler.ComponentProgram
open ComponentInit ComponentMachine ComponentMemory

/- Erase the writable bitmap, mark the supplied seed, then perform one edge
sweep per vertex. This syntax is independent of all graph dimensions. -/
def fullCmd : Cmd := .seq initCmd block
noncomputable def fullEval (n m : ℕ) (s : Store) : Store :=
  blockEval m n (initEval n s)
noncomputable def program : MinSumFPT.Program := compile fullCmd 0

lemma fullCmd_size : fullCmd.size = 45 := by decide
lemma program_length : program.length = 46 := by
  simp [program,compile,compileAt_length,fullCmd_size]

lemma init_input_ptr (n : ℕ) (s : Store) (j : ℕ)
    (hj : 2 ≤ j ∧ j ≤ 6 ∨ j = 17) : (initEval n s).ptrs j = s.ptrs j :=
  init_ptr_ne n j s (by omega) (by omega) (by omega) (by omega)

lemma full_exec {N : ℕ} (d : Point N → Point N → ℝ) (n m : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ)) :
    Executes d fullCmd s (fullEval n m s) (n*(17*m+11)+14) := by
  have h := Executes.seq (init_exec d n s hn)
    (block_exec d m n (initEval n s)
      (by rw [init_input_ptr n s 5 (by omega),hm])
      (by rw [init_input_ptr n s 6 (by omega),hn]))
  convert h using 1 <;> try rfl
  ring

lemma full_machine_execution {N : ℕ} (d : Point N → Point N → ℝ)
    (n m : ℕ) (s : Store) (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[n*(17*m+11)+15] (s.state 0 work) =
      (fullEval n m s).haltedState 45 (work+(n*(17*m+11)+15)) 0 := by
  simpa [program,fullCmd_size,Nat.add_assoc] using
    compile_halts (full_exec d n m s hm hn) ω work 0

lemma fullEval_frame (n m : ℕ) (s : Store) : DataFrame s (fullEval n m s) :=
  (show DataFrame s (initEval n s) from init_frame n s).trans
    (block_frame m n (initEval n s))

lemma fullEval_ptr_frame (n m : ℕ) (s : Store) (j : ℕ)
    (hj : 2 ≤ j ∧ j ≤ 6 ∨ j = 17) : (fullEval n m s).ptrs j = s.ptrs j := by
  unfold fullEval
  rw [block_ptr_frame m n (initEval n s) j (by omega)]
  exact init_input_ptr n s j hj

lemma fullEval_imem {n : ℕ} (A : Finset (Fin n)) (es : List (Fin n × Fin n))
    (seed : Fin n) (s : Store) (hin : GraphInput s A es seed) :
    (fullEval n es.length s).imem =
      (memoryPass (s.ptrs 3) (s.ptrs 4) es)^[n] (initEval n s).imem := by
  rcases hin with ⟨hm,hn,hseed,hA,he,hsep,hesep⟩
  have he' : EdgeEncoding (initEval n s).imem ((initEval n s).ptrs 2) es := by
    rw [init_input_ptr n s 2 (by omega)]
    exact init_preserves_edges s seed hseed _ es hesep he
  have hs' : EdgesSeparate ((initEval n s).ptrs 2) ((initEval n s).ptrs 4) es := by
    rwa [init_input_ptr n s 2 (by omega),init_input_ptr n s 4 (by omega)]
  unfold fullEval
  rw [blockEval_imem es n (initEval n s) he' hs',
    init_input_ptr n s 3 (by omega),init_input_ptr n s 4 (by omega)]

lemma fullEval_component {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (hin : GraphInput s A es seed) (hseed : seed ∈ A)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    Bitmap (fullEval n es.length s).imem (s.ptrs 3) A ∧
    Bitmap (fullEval n es.length s).imem (s.ptrs 4) (Havens.componentWithin G A seed) := by
  rw [fullEval_imem A es seed s hin]
  rcases hin with ⟨hm,hn,hs,hA,he,hsep,hesep⟩
  exact memoryPass_iterate_component G A es seed hsep
    (init_preserves_bitmap s seed hs _ A hsep hA) (init_bitmap s seed hs)
    hseed hsound hcomplete

lemma fullEval_positive_iff {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (hin : GraphInput s A es seed) (hseed : seed ∈ A)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) (v : Fin n) :
    0 < (fullEval n es.length s).imem (address (s.ptrs 4) v) ↔
      ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∈ A := by
  rw [fullEval_imem A es seed s hin]
  rcases hin with ⟨hm,hn,hs,hA,he,hsep,hesep⟩
  exact memoryPass_iterate_positive_iff G A es seed v hsep
    (init_preserves_bitmap s seed hs _ A hsep hA) (init_bitmap s seed hs)
    hseed hsound hcomplete

lemma fullEval_imem_frame {n : ℕ} (A : Finset (Fin n)) (es : List (Fin n × Fin n))
    (seed : Fin n) (s : Store) (hin : GraphInput s A es seed) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (fullEval n es.length s).imem x = s.imem x := by
  rw [fullEval_imem A es seed s hin, memoryPass_iterate_frame _ _ _ _ _ _ hx]
  exact init_memory_frame s seed hin.2.2.1 x hx

/- A public readback statement using only ordinary graph walks. -/
lemma fullEval_walk_bitmap {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (hin : GraphInput s A es seed) (hseed : seed ∈ A)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) (v : Fin n) :
    (fullEval n es.length s).imem (address (s.ptrs 4) v) =
      if (∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∈ A) then 1 else 0 := by
  have he : v ∈ Havens.componentWithin G A seed ↔
      ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∈ A := by
    rw [Havens.mem_componentWithin]
    constructor
    · exact And.right
    · intro hp
      exact ⟨hp.choose_spec v hp.choose.end_mem_support,hp⟩
  simpa only [he] using
    (fullEval_component G A es seed s hin hseed hsound hcomplete).2 v

/- With at most one listed arc per ordered vertex pair, the complete run is
at most 43 n³ charged steps; a supplied seed implies n is positive. -/
theorem component_program_cubic_bound (n m : ℕ) (seed : Fin n) (hm : m ≤ n^2) :
    n*(17*m+11)+15 ≤ 43*n^3 := by
  have hn : 1 ≤ n := by have := seed.isLt; omega
  have hmul := Nat.mul_le_mul_left n hm
  have hn2 : n ≤ n^2 := by nlinarith
  have hn3 : n^2 ≤ n^3 := by nlinarith
  nlinarith


/- One fixed deterministic program initializes its own reached bitmap from
ordinary graph input and returns exactly the allowed component, with every
instruction, branch, initialization step, and halt included in the charge. -/
end StableMSR.Recovery.Compiler.ComponentProgram

open StableMSR.Recovery.ComponentMemory StableMSR.Recovery.Compiler.ComponentProgram
theorem solution :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 46 ∧
    ∀ (n : ℕ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (A : Finset (Fin n)) (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store),
      GraphInput s A es seed → seed ∈ A →
      (∀ e ∈ es, G.Adj e.1 e.2) →
      (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let result := (MinSumFPT.step P d ω)^[n*(17*es.length+11)+15] (s.state 0 work)
      result.halted = true ∧ result.work = work+(n*(17*es.length+11)+15) ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      result.cfg.mem = s.mem ∧ result.cfg.regs = s.regs ∧
      (∀ v : Fin n, result.imem (address (s.ptrs 4) v) =
        if (∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∈ A) then 1 else 0) ∧
      (∀ v : Fin n, 0 < result.imem (address (s.ptrs 4) v) ↔
        ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∈ A) ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ address (s.ptrs 4) v) → result.imem x = s.imem x) ∧
      (∀ j : ℕ, (2 ≤ j ∧ j ≤ 6 ∨ j = 17) → result.cfg.ptrs j = s.ptrs j) := by
  refine ⟨program,compile_deterministic fullCmd 0,program_length,?_⟩
  intro n d G A es seed s hin hseed hsound hcomplete ω work
  dsimp only
  rw [full_machine_execution d n es.length s hin.1 hin.2.1 ω work]
  have hf := fullEval_frame n es.length s
  exact ⟨rfl,rfl,hf.2.2.1,hf.2.2.2.1,hf.2.1,hf.1,
    fullEval_walk_bitmap G A es seed s hin hseed hsound hcomplete,
    fullEval_positive_iff G A es seed s hin hseed hsound hcomplete,
    fullEval_imem_frame A es seed s hin,
    fullEval_ptr_frame n es.length s⟩

