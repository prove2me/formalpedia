-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.StateCatalogAllocated.self_allocating_state_catalog_program
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-17T10:44:24.084888+00:00
-- url     : https://prove2.me/submissions/fd10bf2b-6b77-4195-9461-c2915093e53f

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
namespace StableMSR.Recovery.BoundaryMemory
open ComponentMemory

/- A graph's external neighborhood of a specified vertex set. -/
noncomputable def externalBoundary {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => v ∉ C ∧ ∃ u ∈ C, G.Adj u v)

@[simp] theorem mem_externalBoundary {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (v : Fin n) :
    v ∈ externalBoundary G C ↔ v ∉ C ∧ ∃ u ∈ C, G.Adj u v := by
  classical
  simp [externalBoundary]

/- Pure processing of one directed arc for an immutable source set. -/
def boundaryRelax {n : ℕ} (C B : Finset (Fin n)) (e : Fin n × Fin n) : Finset (Fin n) :=
  if e.1 ∈ C ∧ e.2 ∉ C then insert e.2 B else B

/- One finite-set scan suffices because membership in the source set never changes. -/
def boundarySetPass {n : ℕ} (C : Finset (Fin n))
    (es : List (Fin n × Fin n)) (B : Finset (Fin n)) : Finset (Fin n) :=
  es.foldl (boundaryRelax C) B

 theorem mem_boundarySetPass {n : ℕ} (C : Finset (Fin n))
    (es : List (Fin n × Fin n)) (B : Finset (Fin n)) (v : Fin n) :
    v ∈ boundarySetPass C es B ↔
      v ∈ B ∨ (v ∉ C ∧ ∃ u, (u, v) ∈ es ∧ u ∈ C) := by
  induction es generalizing B with
  | nil => simp [boundarySetPass]
  | cons e es ih =>
    change v ∈ boundarySetPass C es (boundaryRelax C B e) ↔ _
    rw [ih]
    rcases e with ⟨u, w⟩
    by_cases h : u ∈ C ∧ w ∉ C
    · simp only [boundaryRelax, h, if_true, Finset.mem_insert, List.mem_cons,
        Prod.mk.injEq]
      aesop
    · simp only [boundaryRelax, h, if_false, List.mem_cons, Prod.mk.injEq]
      aesop

/- No ordering or uniqueness condition is imposed on the directed edge list. -/
theorem boundarySetPass_eq {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) :
    boundarySetPass C es ∅ = externalBoundary G C := by
  ext v
  rw [mem_boundarySetPass, mem_externalBoundary]
  simp only [Finset.notMem_empty, false_or]
  constructor
  · rintro ⟨hv, u, he, hu⟩
    exact ⟨hv, u, hu, hsound (u, v) he⟩
  · rintro ⟨hv, u, hu, huv⟩
    exact ⟨hv, u, hcomplete u v huv, hu⟩

/- Memory effect of one boundary-marking interpreter step. -/
def boundaryMark (Cbase Bbase u v : ℤ) (mem : ℤ → ℤ) : ℤ → ℤ :=
  if 0 < mem (Cbase + u) ∧ mem (Cbase + v) ≤ 0 then
    Function.update mem (Bbase + v) 1
  else mem

/- Memory effect of one full directed-edge scan. -/
def boundaryPass {n : ℕ} (Cbase Bbase : ℤ)
    (es : List (Fin n × Fin n)) (mem : ℤ → ℤ) : ℤ → ℤ :=
  es.foldl (fun m e => boundaryMark Cbase Bbase e.1.val e.2.val m) mem

 theorem boundaryMark_frame (Cbase Bbase u v : ℤ) (mem : ℤ → ℤ)
    (x : ℤ) (hx : x ≠ Bbase + v) :
    boundaryMark Cbase Bbase u v mem x = mem x := by
  simp only [boundaryMark]
  split
  · exact Function.update_of_ne hx _ _
  · rfl

 theorem boundaryMark_bitmap {n : ℕ} {mem : ℤ → ℤ}
    {Cbase Bbase : ℤ} {C B : Finset (Fin n)}
    (hC : Bitmap mem Cbase C) (hB : Bitmap mem Bbase B)
    (e : Fin n × Fin n) :
    Bitmap (boundaryMark Cbase Bbase e.1.val e.2.val mem) Bbase
      (boundaryRelax C B e) := by
  intro x
  have hsource := hC e.1
  have htarget := hC e.2
  dsimp [address] at hsource htarget
  by_cases hu : e.1 ∈ C <;> by_cases hv : e.2 ∈ C
  · simp [boundaryMark, hsource, htarget, hu, hv, boundaryRelax, hB x]
  · simp only [hu, hv, if_true, if_false] at hsource htarget
    simp only [boundaryMark, hsource, htarget, zero_lt_one, le_refl, and_self, if_true,
      boundaryRelax, hu, hv, not_false_eq_true, and_self, if_true]
    by_cases hx : x = e.2
    · subst x
      simp [address]
    · have haddr : address Bbase x ≠ Bbase + (e.2.val : ℤ) := by
        change address Bbase x ≠ address Bbase e.2
        exact fun h => hx ((address_eq_iff Bbase x e.2).mp h)
      rw [Function.update_of_ne haddr]
      simpa [hx] using hB x
  · simp [boundaryMark, hsource, htarget, hu, hv, boundaryRelax, hB x]
  · simp [boundaryMark, hsource, htarget, hu, hv, boundaryRelax, hB x]

 theorem boundaryMark_preserves_bitmap {n : ℕ} {mem : ℤ → ℤ}
    {Cbase Bbase : ℤ} {C : Finset (Fin n)}
    (hsep : Separate (n := n) Cbase Bbase)
    (hC : Bitmap mem Cbase C) (e : Fin n × Fin n) :
    Bitmap (boundaryMark Cbase Bbase e.1.val e.2.val mem) Cbase C := by
  intro x
  rw [boundaryMark_frame Cbase Bbase _ _ mem _ (hsep x e.2)]
  exact hC x

 theorem boundaryPass_refines {n : ℕ} {mem : ℤ → ℤ}
    {Cbase Bbase : ℤ} {C B : Finset (Fin n)}
    (hsep : Separate (n := n) Cbase Bbase)
    (hC : Bitmap mem Cbase C) (hB : Bitmap mem Bbase B)
    (es : List (Fin n × Fin n)) :
    Bitmap (boundaryPass Cbase Bbase es mem) Cbase C ∧
    Bitmap (boundaryPass Cbase Bbase es mem) Bbase (boundarySetPass C es B) := by
  induction es generalizing mem B with
  | nil => exact ⟨hC, hB⟩
  | cons e es ih =>
    exact ih (boundaryMark_preserves_bitmap hsep hC e) (boundaryMark_bitmap hC hB e)

 theorem boundaryPass_frame {n : ℕ} (Cbase Bbase : ℤ)
    (es : List (Fin n × Fin n)) (mem : ℤ → ℤ) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address Bbase v) :
    boundaryPass Cbase Bbase es mem x = mem x := by
  induction es generalizing mem with
  | nil => rfl
  | cons e es ih =>
    change boundaryPass Cbase Bbase es
      (boundaryMark Cbase Bbase e.1.val e.2.val mem) x = mem x
    rw [ih]
    exact boundaryMark_frame _ _ _ _ _ _ (hx e.2)

 theorem boundaryPass_preserves_edges {n : ℕ} {mem : ℤ → ℤ}
    (Cbase Bbase edgeBase : ℤ) (xs es : List (Fin n × Fin n))
    (hsep : EdgesSeparate edgeBase Bbase es)
    (hencode : EdgeEncoding mem edgeBase es) :
    EdgeEncoding (boundaryPass Cbase Bbase xs mem) edgeBase es := by
  intro j hj
  rw [boundaryPass_frame _ _ _ _ _ (fun v => (hsep j hj v).1),
      boundaryPass_frame _ _ _ _ _ (fun v => (hsep j hj v).2)]
  exact hencode j hj

/- One pass from the empty output bitmap computes the exact external boundary. -/
theorem boundaryPass_boundary {n : ℕ} {mem : ℤ → ℤ} {Cbase Bbase : ℤ}
    (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) (es : List (Fin n × Fin n))
    (hsep : Separate (n := n) Cbase Bbase)
    (hC : Bitmap mem Cbase C) (hB : Bitmap (n := n) mem Bbase ∅)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) :
    Bitmap (boundaryPass Cbase Bbase es mem) Cbase C ∧
    Bitmap (boundaryPass Cbase Bbase es mem) Bbase (externalBoundary G C) := by
  simpa only [boundarySetPass_eq G C es hsound hcomplete] using
    boundaryPass_refines hsep hC hB es

/- Exact positive-flag readback, without a set-valued output oracle. -/
theorem boundaryPass_positive_iff {n : ℕ} {mem : ℤ → ℤ} {Cbase Bbase : ℤ}
    (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) (es : List (Fin n × Fin n))
    (hsep : Separate (n := n) Cbase Bbase)
    (hC : Bitmap mem Cbase C) (hB : Bitmap (n := n) mem Bbase ∅)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) (v : Fin n) :
    0 < boundaryPass Cbase Bbase es mem (address Bbase v) ↔
      v ∉ C ∧ ∃ u ∈ C, G.Adj u v := by
  rw [(boundaryPass_boundary G C es hsep hC hB hsound hcomplete).2 v]
  by_cases hv : v ∈ externalBoundary G C
  · simpa only [hv, if_true, zero_lt_one, true_iff] using
      (mem_externalBoundary G C v).mp hv
  · simp only [hv, if_false, lt_self_iff_false, false_iff]
    exact fun h => hv ((mem_externalBoundary G C v).mpr h)

end StableMSR.Recovery.BoundaryMemory



open scoped Classical
namespace StableMSR.Recovery.Compiler.BoundaryMachine
open ComponentMachine

/- Mark the target outside C when the source lies in C. Padding charges five
steps in all cases, including every conditional branch. -/
def markCmd : Cmd :=
  .ite (.pointerLE 13 0) pad4
    (.ite (.pointerLE 14 0) (.seq (.atom (.integerStore 11 1)) nop) nop)

noncomputable def markEval (s : Store) : Store :=
  if s.ptrs 13 ≤ s.ptrs 0 then s else
  if s.ptrs 14 ≤ s.ptrs 0 then
    { s with imem := Function.update s.imem (s.ptrs 11) (s.ptrs 1) }
  else s

lemma mark_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d markCmd s (markEval s) 5 := by
  by_cases h13 : s.ptrs 13 ≤ s.ptrs 0
  · simpa [markCmd, markEval, h13] using
      Executes.ite_true (c := Cond.pointerLE 13 0)
        (no := Cmd.ite (.pointerLE 14 0) (.seq (.atom (.integerStore 11 1)) nop) nop)
        h13 (pad4_exec d s)
  · by_cases h14 : s.ptrs 14 ≤ s.ptrs 0
    · simpa [markCmd, markEval, h13, h14, Op.eval] using
        Executes.ite_false (c := Cond.pointerLE 13 0) (yes := pad4) h13
          (Executes.ite_true (c := Cond.pointerLE 14 0) (no := nop) h14
            (Executes.seq (Executes.atom (.integerStore 11 1) s)
              (nop_exec d (Op.eval d (.integerStore 11 1) s))))
    · simpa [markCmd, markEval, h13, h14] using
        Executes.ite_false (c := Cond.pointerLE 13 0) (yes := pad4) h13
          (Executes.ite_false (c := Cond.pointerLE 14 0)
            (yes := Cmd.seq (.atom (.integerStore 11 1)) nop) h14 (nop_exec d s))

def edgeOps : List Op :=
  [.integerLoad 10 7, .pointerInc 7, .integerLoad 11 7, .pointerInc 7,
   .pointerAdd 10 3 10, .pointerAdd 12 3 11, .pointerAdd 11 4 11,
   .integerLoad 13 10, .integerLoad 14 12]

def edgeCmd : Cmd := .seq (opsCmd edgeOps) (.seq markCmd (.atom (.pointerInc 8)))

noncomputable def edgeInput (s : Store) : Store :=
  let a := s.imem (s.ptrs 7)
  let b := s.imem (s.ptrs 7+1)
  let t := setPtr (setPtr (setPtr (setPtr s 7 (s.ptrs 7+2))
    10 (s.ptrs 3+a)) 12 (s.ptrs 3+b)) 11 (s.ptrs 4+b)
  setPtr (setPtr t 13 (s.imem (s.ptrs 3+a))) 14 (s.imem (s.ptrs 3+b))

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

lemma edge_frame (s : Store) : DataFrame s (edgeStep s) := by
  unfold edgeStep incPtr setPtr markEval
  split <;> (try split) <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma pass_frame (m : ℕ) (s : Store) : DataFrame s (passEval m s) :=
  (show DataFrame s (passSetup s) from ⟨rfl,rfl,rfl,rfl,rfl⟩).trans
    (iterate_frame edgeStep edge_frame m (passSetup s))

lemma pass_size : passCmd.size = 26 := by decide

end StableMSR.Recovery.Compiler.BoundaryMachine


namespace StableMSR.Recovery.Compiler.BoundaryMachine
open StableMSR.Recovery.ComponentMemory
open StableMSR.Recovery.BoundaryMemory
open ComponentMachine

/- The actual read/branch/store step has precisely the abstract marking effect. -/
theorem edgeStep_imem (s : Store) (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1) :
    (edgeStep s).imem =
      boundaryMark (s.ptrs 3) (s.ptrs 4) (s.imem (s.ptrs 7))
        (s.imem (s.ptrs 7 + 1)) s.imem := by
  simp [edgeStep, incPtr, setPtr, markEval, edgeInput, boundaryMark, h0, h1]
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
      boundaryPass (s.ptrs 3) (s.ptrs 4) es s.imem := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    have hh := hencode 0 (by simp)
    simp only [Nat.cast_zero, mul_zero, add_zero, List.getElem_cons_zero] at hh
    have hm : (edgeStep s).imem =
        boundaryMark (s.ptrs 3) (s.ptrs 4) e.1.val e.2.val s.imem := by
      simpa only [hh.1, hh.2] using edgeStep_imem s h0 h1
    have he : EdgeEncoding (edgeStep s).imem (s.ptrs 7) (e :: es) := by
      rw [hm]
      exact boundaryPass_preserves_edges (s.ptrs 3) (s.ptrs 4) (s.ptrs 7)
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
      boundaryPass (s.ptrs 3) (s.ptrs 4) es s.imem := by
  apply edgeSteps_imem es (passSetup s)
    (by simpa [passSetup, setPtr] using h0)
    (by simpa [passSetup, setPtr] using h1)
    (by simpa [passSetup, setPtr] using hencode)
    (by simpa [passSetup, setPtr] using hsep)


/- The interpreter scan computes the exact external-boundary bitmap from a
zeroed output, and preserves the input component bitmap. -/
theorem passEval_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store)
    (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1)
    (hencode : EdgeEncoding s.imem (s.ptrs 2) es)
    (hedges : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hC : Bitmap s.imem (s.ptrs 3) C) (hB : Bitmap (n := n) s.imem (s.ptrs 4) ∅)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u, v) ∈ es) :
    Bitmap (passEval es.length s).imem (s.ptrs 3) C ∧
    Bitmap (passEval es.length s).imem (s.ptrs 4) (externalBoundary G C) := by
  rw [passEval_imem es s h0 h1 hencode hedges]
  exact boundaryPass_boundary G C es hsep hC hB hsound hcomplete

/- Every integer cell outside the writable output bitmap is unchanged. -/
theorem passEval_imem_frame {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (h0 : s.ptrs 0 = 0) (h1 : s.ptrs 1 = 1)
    (hencode : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (passEval es.length s).imem x = s.imem x := by
  rw [passEval_imem es s h0 h1 hencode hsep]
  exact boundaryPass_frame _ _ _ _ _ hx

end StableMSR.Recovery.Compiler.BoundaryMachine



open scoped Classical
namespace StableMSR.Recovery.Compiler.BoundaryProgram
open ComponentInit ComponentMachine BitmapFill ComponentMemory BoundaryMemory

/- Clear the output bitmap and initialize the zero/one constants. -/
def clearCmd : Cmd := .seq prepCmd (fillCmd 15 16 0)
def clearEval (n : ℕ) (s : Store) : Store := fillEval 15 0 n (prepEval s)

lemma clear_exec {N : ℕ} (d : Point N → Point N → ℝ) (n : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) :
    Executes d clearCmd s (clearEval n s) (4*n+7) := by
  have hs : (prepEval s).ptrs 16 = (prepEval s).ptrs 15+(n:ℤ)-1 := by
    simp [prepEval,hn]
  have h := Executes.seq (prep_exec d s)
    (fill_exec d 15 16 0 n (prepEval s) (by decide) hs)
  convert h using 1 <;> try rfl
  omega

lemma clear_ptr_ne (n : ℕ) (s : Store) (j : ℕ)
    (h0 : j ≠ 0) (h1 : j ≠ 1) (h15 : j ≠ 15) (h16 : j ≠ 16) :
    (clearEval n s).ptrs j = s.ptrs j := by
  unfold clearEval
  rw [fill_ptr_ne 15 0 n j (prepEval s) h15]
  simp [prepEval,h0,h1,h15,h16]

lemma clear_constants (n : ℕ) (s : Store) :
    (clearEval n s).ptrs 0 = 0 ∧ (clearEval n s).ptrs 1 = 1 := by
  constructor
  · unfold clearEval
    rw [fill_ptr_ne 15 0 n 0 (prepEval s) (by decide)]
    simp [prepEval]
  · unfold clearEval
    rw [fill_ptr_ne 15 0 n 1 (prepEval s) (by decide)]
    simp [prepEval]

lemma clear_frame (n : ℕ) (s : Store) : DataFrame s (clearEval n s) :=
  fill_frame 15 0 n (prepEval s)

lemma clear_memory (n : ℕ) (s : Store) :
    (clearEval n s).imem =
      TupleWriter.writeMemory (s.ptrs 4) (List.replicate n (0:ℤ)) s.imem := by
  unfold clearEval
  rw [fill_memory 15 0 n (prepEval s) (by decide)]
  simp [prepEval]

lemma clear_bitmap (n : ℕ) (s : Store) :
    Bitmap (n := n) (clearEval n s).imem (s.ptrs 4) ∅ := by
  intro v
  rw [clear_memory]
  have hi : v.val < (List.replicate n (0:ℤ)).length := by simpa using v.isLt
  rw [address,TupleWriter.writeMemory_get _ _ _ v.val hi]
  simp

lemma clear_memory_frame (n : ℕ) (s : Store) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (clearEval n s).imem x = s.imem x := by
  rw [clear_memory]
  by_cases hlo : x < s.ptrs 4
  · exact TupleWriter.writeMemory_before _ _ _ _ hlo
  · have hhi : s.ptrs 4 + (n:ℤ) ≤ x := by
      by_contra hbad
      have hnonneg : 0 ≤ x-s.ptrs 4 := by omega
      have hlt : (x-s.ptrs 4).toNat < n := by omega
      let v : Fin n := ⟨(x-s.ptrs 4).toNat,hlt⟩
      have he : x = address (s.ptrs 4) v := by dsimp [address,v]; omega
      exact hx v he
    apply TupleWriter.writeMemory_after
    simpa only [List.length_replicate] using hhi

lemma clear_preserves_bitmap {n : ℕ} (s : Store) (base : ℤ) (C : Finset (Fin n))
    (hsep : Separate (n := n) base (s.ptrs 4)) (hC : Bitmap s.imem base C) :
    Bitmap (clearEval n s).imem base C := by
  intro v
  rw [clear_memory_frame n s _ (fun w => hsep v w)]
  exact hC v

lemma clear_preserves_edges {n : ℕ} (s : Store) (edgeBase : ℤ)
    (es : List (Fin n × Fin n)) (hsep : EdgesSeparate edgeBase (s.ptrs 4) es)
    (he : EdgeEncoding s.imem edgeBase es) :
    EdgeEncoding (clearEval n s).imem edgeBase es := by
  intro j hj
  rw [clear_memory_frame n s _ (fun v => (hsep j hj v).1),
    clear_memory_frame n s _ (fun v => (hsep j hj v).2)]
  exact he j hj

def fullCmd : Cmd := .seq clearCmd BoundaryMachine.passCmd
noncomputable def fullEval (n m : ℕ) (s : Store) : Store :=
  BoundaryMachine.passEval m (clearEval n s)
noncomputable def program : MinSumFPT.Program := compile fullCmd 0

lemma fullCmd_size : fullCmd.size = 36 := by decide
lemma program_length : program.length = 37 := by
  simp [program,compile,compileAt_length,fullCmd_size]

lemma full_exec {N : ℕ} (d : Point N → Point N → ℝ) (n m : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ)) :
    Executes d fullCmd s (fullEval n m s) (4*n+17*m+11) := by
  have h := Executes.seq (clear_exec d n s hn)
    (BoundaryMachine.pass_exec d m (clearEval n s)
      (by rw [clear_ptr_ne n s 5 (by decide) (by decide) (by decide) (by decide),hm]))
  convert h using 1 <;> try rfl
  omega

lemma full_machine_execution {N : ℕ} (d : Point N → Point N → ℝ)
    (n m : ℕ) (s : Store) (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[4*n+17*m+12] (s.state 0 work) =
      (fullEval n m s).haltedState 36 (work+(4*n+17*m+12)) 0 := by
  simpa [program,fullCmd_size,Nat.add_assoc] using
    compile_halts (full_exec d n m s hm hn) ω work 0

lemma fullEval_frame (n m : ℕ) (s : Store) : DataFrame s (fullEval n m s) :=
  (clear_frame n s).trans (BoundaryMachine.pass_frame m (clearEval n s))

lemma fullEval_ptr_frame (n m : ℕ) (s : Store) (j : ℕ)
    (hj : 2 ≤ j ∧ j ≤ 6 ∨ 16 < j) : (fullEval n m s).ptrs j = s.ptrs j := by
  unfold fullEval
  rw [BoundaryMachine.pass_ptr_frame m (clearEval n s) j (by omega)]
  exact clear_ptr_ne n s j (by omega) (by omega) (by omega) (by omega)

lemma fullEval_imem {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) :
    (fullEval n es.length s).imem =
      boundaryPass (s.ptrs 3) (s.ptrs 4) es (clearEval n s).imem := by
  have hp (j : ℕ) (h2 : 2 ≤ j) (h6 : j ≤ 6) :
      (clearEval n s).ptrs j = s.ptrs j :=
    clear_ptr_ne n s j (by omega) (by omega) (by omega) (by omega)
  have he' : EdgeEncoding (clearEval n s).imem ((clearEval n s).ptrs 2) es := by
    rw [hp 2 (by omega) (by omega)]
    exact clear_preserves_edges s _ es hesep he
  have hs' : EdgesSeparate ((clearEval n s).ptrs 2) ((clearEval n s).ptrs 4) es := by
    rwa [hp 2 (by omega) (by omega),hp 4 (by omega) (by omega)]
  unfold fullEval
  rw [BoundaryMachine.passEval_imem es (clearEval n s)
      (clear_constants n s).1 (clear_constants n s).2 he' hs',
    hp 3 (by omega) (by omega),hp 4 (by omega) (by omega)]

lemma fullEval_boundary {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n))
    (es : List (Fin n × Fin n)) (s : Store)
    (hC : Bitmap s.imem (s.ptrs 3) C)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    Bitmap (fullEval n es.length s).imem (s.ptrs 3) C ∧
    Bitmap (fullEval n es.length s).imem (s.ptrs 4) (externalBoundary G C) := by
  rw [fullEval_imem es s he hesep]
  exact boundaryPass_boundary G C es hsep
    (clear_preserves_bitmap s _ C hsep hC) (clear_bitmap n s) hsound hcomplete

lemma fullEval_imem_frame {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (fullEval n es.length s).imem x = s.imem x := by
  rw [fullEval_imem es s he hesep,boundaryPass_frame _ _ _ _ _ hx]
  exact clear_memory_frame n s x hx

lemma fullEval_boundary_bitmap {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store)
    (hC : Bitmap s.imem (s.ptrs 3) C)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) (v : Fin n) :
    (fullEval n es.length s).imem (address (s.ptrs 4) v) =
      if v ∉ C ∧ (∃ u ∈ C, G.Adj u v) then 1 else 0 := by
  simpa only [mem_externalBoundary] using
    (fullEval_boundary G C es s hC he hsep hesep hsound hcomplete).2 v

/- One dimension-independent finite program clears its output and computes
the exact external neighborhood in 4n+17m+12 charged instructions. -/
theorem boundary_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 37 ∧
    ∀ (n : ℕ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (C : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store),
      s.ptrs 5 = (es.length:ℤ) → s.ptrs 6 = (n:ℤ) →
      Bitmap s.imem (s.ptrs 3) C → EdgeEncoding s.imem (s.ptrs 2) es →
      Separate (n := n) (s.ptrs 3) (s.ptrs 4) →
      EdgesSeparate (s.ptrs 2) (s.ptrs 4) es →
      (∀ e ∈ es, G.Adj e.1 e.2) → (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      let result := (MinSumFPT.step P d ω)^[4*n+17*es.length+12] (s.state 0 work)
      result.halted = true ∧ result.work = work+(4*n+17*es.length+12) ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos ∧
      result.cfg.mem = s.mem ∧ result.cfg.regs = s.regs ∧
      (∀ v : Fin n, result.imem (address (s.ptrs 4) v) =
        if v ∉ C ∧ (∃ u ∈ C, G.Adj u v) then 1 else 0) ∧
      (∀ x : ℤ, (∀ v : Fin n, x ≠ address (s.ptrs 4) v) → result.imem x = s.imem x) ∧
      (∀ j : ℕ, 2 ≤ j → j ≤ 6 → result.cfg.ptrs j = s.ptrs j) := by
  refine ⟨program,compile_deterministic fullCmd 0,program_length,?_⟩
  intro n d G C es s hm hn hC he hsep hesep hsound hcomplete ω work
  dsimp only
  rw [full_machine_execution d n es.length s hm hn ω work]
  have hf := fullEval_frame n es.length s
  refine ⟨rfl,rfl,hf.2.2.1,hf.2.2.2.1,hf.2.1,hf.1,
    fullEval_boundary_bitmap G C es s hC he hsep hesep hsound hcomplete,
    fullEval_imem_frame es s he hesep,?_⟩
  intro j h2 h6
  exact fullEval_ptr_frame n es.length s j (Or.inl ⟨h2,h6⟩)

end StableMSR.Recovery.Compiler.BoundaryProgram


set_option autoImplicit false

namespace StableMSR.Recovery.Compiler.ArrayEquality

open ComponentMachine

def prepOps : List Op :=
  [.pointerConst 0 0, .pointerConst 18 1, .pointerCopy 20 6, .pointerDec 20]

def prepEval (s : Store) : Store :=
  setPtr (setPtr (setPtr s 0 0) 18 1) 20 (s.ptrs 6 - 1)

/- Two integer comparisons, with equal cost on equality and both strict orders. -/
def compareCmd : Cmd :=
  .ite (.pointerLE 21 22)
    (.ite (.pointerLE 22 21) pad2 (.atom (.pointerConst 18 0)))
    (.seq (.atom (.pointerConst 18 0)) nop)

def compareEval (s : Store) : Store :=
  if s.ptrs 21 = s.ptrs 22 then s else setPtr s 18 0

def body : Cmd :=
  .seq (opsCmd [.pointerAdd 23 3 20, .integerLoad 21 23,
    .pointerAdd 23 4 20, .integerLoad 22 23])
    (.seq compareCmd (.atom (.pointerDec 20)))

def inputEval (s : Store) : Store :=
  setPtr (setPtr (setPtr s 21 (s.imem (s.ptrs 3+s.ptrs 20)))
    23 (s.ptrs 4+s.ptrs 20)) 22 (s.imem (s.ptrs 4+s.ptrs 20))

def step (s : Store) : Store :=
  let t := compareEval (inputEval s)
  setPtr t 20 (t.ptrs 20-1)

def run : ℕ → Store → Store
  | 0, s => s
  | q+1, s => run q (step s)

def loop : Cmd := .whileDo (.pointerLE 0 20) body

def equalityCmd : Cmd := .seq (opsCmd prepOps) loop

def equalityEval (q : ℕ) (s : Store) : Store := run q (prepEval s)

@[simp] lemma equalityCmd_size : equalityCmd.size = 21 := rfl

lemma prep_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d (opsCmd prepOps) s (prepEval s) 4 := by
  simpa [prepOps,evalOps,prepEval,Op.eval,setPtr,Function.update_idem] using
    ops_exec d prepOps s

lemma compare_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d compareCmd s (compareEval s) 4 := by
  by_cases hle : s.ptrs 21 ≤ s.ptrs 22
  · by_cases hrev : s.ptrs 22 ≤ s.ptrs 21
    · have he := le_antisymm hle hrev
      simpa [compareCmd,compareEval,he] using
        Executes.ite_true (c := Cond.pointerLE 21 22)
          (no := Cmd.seq (.atom (.pointerConst 18 0)) nop) hle
          (Executes.ite_true (c := Cond.pointerLE 22 21)
            (no := Cmd.atom (.pointerConst 18 0)) hrev (pad2_exec d s))
    · have he : s.ptrs 21 ≠ s.ptrs 22 := by omega
      simpa [compareCmd,compareEval,he,Op.eval,setPtr] using
        Executes.ite_true (c := Cond.pointerLE 21 22)
          (no := Cmd.seq (.atom (.pointerConst 18 0)) nop) hle
          (Executes.ite_false (c := Cond.pointerLE 22 21) (yes := pad2) hrev
            (Executes.atom (.pointerConst 18 0) (d := d) s))
  · have he : s.ptrs 21 ≠ s.ptrs 22 := by omega
    have hp := Executes.seq (Executes.atom (.pointerConst 18 0) (d := d) s)
      (nop_exec d _)
    simpa [compareCmd,compareEval,he,Op.eval,setPtr] using
      Executes.ite_false (c := Cond.pointerLE 21 22)
        (yes := Cmd.ite (.pointerLE 22 21) pad2 (.atom (.pointerConst 18 0))) hle hp

lemma body_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d body s (step s) 9 := by
  have hi : Executes d (opsCmd [.pointerAdd 23 3 20, .integerLoad 21 23,
      .pointerAdd 23 4 20, .integerLoad 22 23]) s (inputEval s) 4 := by
    simpa [evalOps,Op.eval,inputEval,setPtr,Function.update_comm,Function.update_idem] using
      ops_exec d [.pointerAdd 23 3 20, .integerLoad 21 23,
        .pointerAdd 23 4 20, .integerLoad 22 23] s
  exact Executes.seq hi (Executes.seq (compare_exec d _)
    (Executes.atom (.pointerDec 20) _))

lemma step_ptr_frame (s : Store) (j : ℕ) (h18 : j ≠ 18) (h20 : j ≠ 20)
    (h21 : j ≠ 21) (h22 : j ≠ 22) (h23 : j ≠ 23) :
    (step s).ptrs j = s.ptrs j := by
  simp only [step,compareEval]
  split <;> simp [setPtr,inputEval,h18,h20,h21,h22,h23]

lemma step_index (s : Store) : (step s).ptrs 20 = s.ptrs 20-1 := by
  simp only [step,compareEval]
  split <;> simp [setPtr,inputEval]

lemma step_flag (s : Store) :
    (step s).ptrs 18 =
      if s.imem (s.ptrs 3+s.ptrs 20) = s.imem (s.ptrs 4+s.ptrs 20)
      then s.ptrs 18 else 0 := by
  simp only [step,compareEval]
  split <;> simp_all [setPtr,inputEval]

lemma step_frame (s : Store) :
    (step s).regs = s.regs ∧ (step s).mem = s.mem ∧ (step s).imem = s.imem ∧
    (step s).queries = s.queries ∧ (step s).tapePos = s.tapePos ∧
    (step s).output = s.output := by
  simp only [step,compareEval]
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

lemma run_ptr_frame (q : ℕ) (s : Store) (j : ℕ) (h18 : j ≠ 18) (h20 : j ≠ 20)
    (h21 : j ≠ 21) (h22 : j ≠ 22) (h23 : j ≠ 23) :
    (run q s).ptrs j = s.ptrs j := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih => rw [run,ih,step_ptr_frame s j h18 h20 h21 h22 h23]

lemma run_frame (q : ℕ) (s : Store) :
    (run q s).regs = s.regs ∧ (run q s).mem = s.mem ∧ (run q s).imem = s.imem ∧
    (run q s).queries = s.queries ∧ (run q s).tapePos = s.tapePos ∧
    (run q s).output = s.output := by
  induction q generalizing s with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  | succ q ih =>
    rcases ih (step s) with ⟨h1,h2,h3,h4,h5,h6⟩
    rcases step_frame s with ⟨g1,g2,g3,g4,g5,g6⟩
    exact ⟨h1.trans g1,h2.trans g2,h3.trans g3,h4.trans g4,h5.trans g5,h6.trans g6⟩

lemma loop_exec {N : ℕ} (d : Point N → Point N → ℝ)
    (q : ℕ) (s : Store) (hzero : s.ptrs 0 = 0)
    (hindex : s.ptrs 20 = (q : ℤ)-1) :
    Executes d loop s (run q s) (11*q+2) := by
  induction q generalizing s with
  | zero =>
    apply Executes.while_false
    simp only [Cond.test,hzero,hindex,Nat.cast_zero]
    omega
  | succ q ih =>
    have hg : (Cond.pointerLE 0 20).test s := by
      simp only [Cond.test,hzero,hindex,Nat.cast_add,Nat.cast_one]
      omega
    have hz : (step s).ptrs 0 = 0 := by
      rw [step_ptr_frame s 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hzero
    have hi : (step s).ptrs 20 = (q : ℤ)-1 := by
      rw [step_index,hindex]
      push_cast
      omega
    have he := Executes.while_true hg (body_exec d s) (ih (step s) hz hi)
    simpa only [loop,run,show 1+9+1+(11*q+2)=11*(q+1)+2 by omega] using he

lemma equality_exec {N : ℕ} (d : Point N → Point N → ℝ)
    (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    Executes d equalityCmd s (equalityEval q s) (11*q+6) := by
  have hz : (prepEval s).ptrs 0 = 0 := by simp [prepEval,setPtr]
  have hi : (prepEval s).ptrs 20 = (q : ℤ)-1 := by simp [prepEval,setPtr,hcount]
  have h := Executes.seq (prep_exec d s) (loop_exec d q (prepEval s) hz hi)
  simpa only [equalityCmd,equalityEval,show 4+(11*q+2)=11*q+6 by omega] using h

lemma equality_ptr_frame (q : ℕ) (s : Store) (j : ℕ)
    (h0 : j ≠ 0) (h18 : j ≠ 18) (h20 : j ≠ 20)
    (h21 : j ≠ 21) (h22 : j ≠ 22) (h23 : j ≠ 23) :
    (equalityEval q s).ptrs j = s.ptrs j := by
  rw [equalityEval,run_ptr_frame q (prepEval s) j h18 h20 h21 h22 h23]
  simp [prepEval,setPtr,h0,h18,h20]

lemma equality_frame (q : ℕ) (s : Store) :
    (equalityEval q s).regs = s.regs ∧ (equalityEval q s).mem = s.mem ∧
    (equalityEval q s).imem = s.imem ∧ (equalityEval q s).queries = s.queries ∧
    (equalityEval q s).tapePos = s.tapePos ∧ (equalityEval q s).output = s.output :=
  run_frame q (prepEval s)

end StableMSR.Recovery.Compiler.ArrayEquality


set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Compiler.ArrayEquality

open ComponentMachine

def PrefixEqual (mem : ℤ → ℤ) (A B : ℤ) (q : ℕ) : Prop :=
  ∀ i : ℕ, i < q → mem (A+(i : ℤ)) = mem (B+(i : ℤ))

lemma prefixEqual_succ (mem : ℤ → ℤ) (A B : ℤ) (q : ℕ) :
    PrefixEqual mem A B (q+1) ↔
      PrefixEqual mem A B q ∧ mem (A+(q : ℤ)) = mem (B+(q : ℤ)) := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega),h q (by omega)⟩
  · rintro ⟨hprefix,hlast⟩ i hi
    by_cases h : i < q
    · exact hprefix i h
    · have he : i = q := by omega
      simpa [he] using hlast

lemma prefixEqual_fin (mem : ℤ → ℤ) (A B : ℤ) (q : ℕ) :
    PrefixEqual mem A B q ↔
      ∀ i : Fin q, mem (A+(i.val : ℤ)) = mem (B+(i.val : ℤ)) := by
  constructor
  · intro h i
    exact h i.val i.isLt
  · intro h i hi
    exact h ⟨i,hi⟩

/- The flag is sticky: a mismatch sets zero permanently. -/
lemma run_flag (q : ℕ) (s : Store) (hindex : s.ptrs 20 = (q : ℤ)-1) :
    (run q s).ptrs 18 =
      if PrefixEqual s.imem (s.ptrs 3) (s.ptrs 4) q then s.ptrs 18 else 0 := by
  induction q generalizing s with
  | zero => simp [run,PrefixEqual]
  | succ q ih =>
    have hi : s.ptrs 20 = (q : ℤ) := by
      rw [hindex]
      push_cast
      omega
    have hnext : (step s).ptrs 20 = (q : ℤ)-1 := by rw [step_index,hi]
    rw [run,ih (step s) hnext,(step_frame s).2.2.1,
      step_ptr_frame s 3 (by decide) (by decide) (by decide) (by decide) (by decide),
      step_ptr_frame s 4 (by decide) (by decide) (by decide) (by decide) (by decide),
      step_flag,hi,prefixEqual_succ]
    by_cases hp : PrefixEqual s.imem (s.ptrs 3) (s.ptrs 4) q <;>
      by_cases hl : s.imem (s.ptrs 3+(q : ℤ)) = s.imem (s.ptrs 4+(q : ℤ)) <;>
        simp [hp,hl]

lemma equality_flag (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    (equalityEval q s).ptrs 18 =
      if (∀ i : Fin q, s.imem (s.ptrs 3+(i.val : ℤ)) =
        s.imem (s.ptrs 4+(i.val : ℤ))) then 1 else 0 := by
  have hi : (prepEval s).ptrs 20 = (q : ℤ)-1 := by simp [prepEval,setPtr,hcount]
  have h := run_flag q (prepEval s) hi
  simpa [equalityEval,prepEval,setPtr,prefixEqual_fin] using h

lemma equality_iff (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    (equalityEval q s).ptrs 18 = 1 ↔
      ∀ i : Fin q, s.imem (s.ptrs 3+(i.val : ℤ)) =
        s.imem (s.ptrs 4+(i.val : ℤ)) := by
  rw [equality_flag q s hcount]
  split <;> simp_all

lemma equality_flag_cases (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    (equalityEval q s).ptrs 18 = 0 ∨ (equalityEval q s).ptrs 18 = 1 := by
  rw [equality_flag q s hcount]
  split <;> simp

lemma equality_zero_iff (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    (equalityEval q s).ptrs 18 = 0 ↔
      ∃ i : Fin q, s.imem (s.ptrs 3+(i.val : ℤ)) ≠
        s.imem (s.ptrs 4+(i.val : ℤ)) := by
  rw [equality_flag q s hcount]
  split <;> simp_all

/- Uniform exact equality testing for arbitrary contiguous integer arrays. -/
theorem array_equality_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 22 ∧
      ∀ (N L : ℕ) (d : Point N → Point N → ℝ) (ω : ℕ → ℝ)
        (s : Store) (w : ℕ), s.ptrs 6 = (L : ℤ) →
        ∃ t : Store,
          (t.ptrs 18 = 0 ∨ t.ptrs 18 = 1) ∧
          (t.ptrs 18 = 1 ↔ ∀ i : Fin L,
            s.imem (s.ptrs 3+(i.val : ℤ)) = s.imem (s.ptrs 4+(i.val : ℤ))) ∧
          (t.ptrs 18 = 0 ↔ ∃ i : Fin L,
            s.imem (s.ptrs 3+(i.val : ℤ)) ≠ s.imem (s.ptrs 4+(i.val : ℤ))) ∧
          (∀ j : ℕ, j ≠ 0 → j ≠ 18 → j ≠ 20 →
            j ≠ 21 → j ≠ 22 → j ≠ 23 → t.ptrs j = s.ptrs j) ∧
          t.regs = s.regs ∧ t.mem = s.mem ∧ t.imem = s.imem ∧
          t.queries = s.queries ∧ t.tapePos = s.tapePos ∧ t.output = s.output ∧
          (MinSumFPT.step P d ω)^[11*L+7] (s.state 0 w) =
            t.haltedState 21 (w+(11*L+7)) 0 := by
  refine ⟨compile equalityCmd 0,compile_deterministic equalityCmd 0,?_,?_⟩
  · simp [compile]
  · intro N L d ω s w hcount
    refine ⟨equalityEval L s,equality_flag_cases L s hcount,
      equality_iff L s hcount,equality_zero_iff L s hcount,?_,?_⟩
    · intro j h0 h18 h20 h21 h22 h23
      exact equality_ptr_frame L s j h0 h18 h20 h21 h22 h23
    · rcases equality_frame L s with ⟨h1,h2,h3,h4,h5,h6⟩
      refine ⟨h1,h2,h3,h4,h5,h6,?_⟩
      have h := compile_halts (equality_exec d L s hcount) ω w 0
      simpa only [equalityCmd_size,show 11*L+6+1=11*L+7 by omega,
        show w+(11*L+6)+1=w+(11*L+7) by omega] using h

end StableMSR.Recovery.Compiler.ArrayEquality


open scoped Classical
namespace StableMSR.Recovery.Compiler.TightBoundaryProgram
open ComponentMemory ComponentMachine

/- Preserve the input-set base before comparing the candidate set with
the newly constructed boundary bitmap. -/
def redirectCmd : Cmd :=
  .seq (.atom (.pointerCopy 24 3)) (.atom (.pointerCopy 3 17))

def redirect (s : Store) : Store :=
  { s with ptrs := Function.update (Function.update s.ptrs 24 (s.ptrs 3)) 3 (s.ptrs 17) }

def restoreCmd : Cmd := .atom (.pointerCopy 3 24)
def restore (s : Store) : Store :=
  { s with ptrs := Function.update s.ptrs 3 (s.ptrs 24) }

lemma redirect_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d redirectCmd s (redirect s) 2 := by
  have h := Executes.seq (Executes.atom (.pointerCopy 24 3) (d := d) s)
    (Executes.atom (.pointerCopy 3 17) (d := d) _)
  simpa [redirectCmd,redirect,Op.eval] using h

lemma restore_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d restoreCmd s (restore s) 1 :=
  Executes.atom (.pointerCopy 3 24) s

@[simp] lemma redirect_imem (s : Store) : (redirect s).imem = s.imem := rfl
@[simp] lemma restore_imem (s : Store) : (restore s).imem = s.imem := rfl
@[simp] lemma redirect_ptr3 (s : Store) : (redirect s).ptrs 3 = s.ptrs 17 := by
  simp [redirect]
@[simp] lemma redirect_ptr24 (s : Store) : (redirect s).ptrs 24 = s.ptrs 3 := by
  simp [redirect]
lemma redirect_ptr_ne (s : Store) (j : ℕ) (h3 : j ≠ 3) (h24 : j ≠ 24) :
    (redirect s).ptrs j = s.ptrs j := by simp [redirect,h3,h24]
lemma restore_ptr_ne (s : Store) (j : ℕ) (h3 : j ≠ 3) :
    (restore s).ptrs j = s.ptrs j := by simp [restore,h3]

/- Compose the verified commands, with one final halt only. -/
def fullCmd : Cmd := .seq BoundaryProgram.fullCmd
  (.seq redirectCmd (.seq ArrayEquality.equalityCmd restoreCmd))
noncomputable def fullEval (n m : ℕ) (s : Store) : Store :=
  restore (ArrayEquality.equalityEval n (redirect (BoundaryProgram.fullEval n m s)))
noncomputable def program : MinSumFPT.Program := compile fullCmd 0

lemma fullCmd_size : fullCmd.size = 60 := by decide
lemma program_length : program.length = 61 := by
  simp [program,compile,compileAt_length,fullCmd_size]

lemma full_exec {N : ℕ} (d : Point N → Point N → ℝ) (n m : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ)) :
    Executes d fullCmd s (fullEval n m s) (15*n+17*m+20) := by
  have hc : (redirect (BoundaryProgram.fullEval n m s)).ptrs 6 = (n:ℤ) := by
    rw [redirect_ptr_ne _ 6 (by decide) (by decide)]
    rw [BoundaryProgram.fullEval_ptr_frame n m s 6 (by omega),hn]
  have h := Executes.seq (BoundaryProgram.full_exec d n m s hm hn)
    (Executes.seq (redirect_exec d _)
      (Executes.seq (ArrayEquality.equality_exec d n _ hc) (restore_exec d _)))
  convert h using 1 <;> try rfl
  omega

lemma full_machine_execution {N : ℕ} (d : Point N → Point N → ℝ)
    (n m : ℕ) (s : Store) (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[15*n+17*m+21] (s.state 0 work) =
      (fullEval n m s).haltedState 60 (work+(15*n+17*m+21)) 0 := by
  simpa [program,fullCmd_size,Nat.add_assoc] using
    compile_halts (full_exec d n m s hm hn) ω work 0

lemma fullEval_frame (n m : ℕ) (s : Store) : DataFrame s (fullEval n m s) := by
  have h := ArrayEquality.equality_frame n (redirect (BoundaryProgram.fullEval n m s))
  exact (BoundaryProgram.fullEval_frame n m s).trans
    ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

lemma fullEval_imem (n m : ℕ) (s : Store) :
    (fullEval n m s).imem = (BoundaryProgram.fullEval n m s).imem :=
  (ArrayEquality.equality_frame n (redirect (BoundaryProgram.fullEval n m s))).2.2.1

lemma fullEval_ptr_frame (n m : ℕ) (s : Store) (j : ℕ)
    (hj : 2 ≤ j ∧ j ≤ 6 ∨ j = 17) : (fullEval n m s).ptrs j = s.ptrs j := by
  unfold fullEval
  by_cases h3 : j = 3
  · subst j
    change (ArrayEquality.equalityEval n (redirect (BoundaryProgram.fullEval n m s))).ptrs 24 = _
    rw [ArrayEquality.equality_ptr_frame n _ 24 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),redirect_ptr24]
    exact BoundaryProgram.fullEval_ptr_frame n m s 3 (by omega)
  · rw [restore_ptr_ne _ j h3,
      ArrayEquality.equality_ptr_frame n _ j (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega),redirect_ptr_ne _ j h3 (by omega)]
    exact BoundaryProgram.fullEval_ptr_frame n m s j (by omega)

lemma fullEval_boundary_bitmap {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store)
    (hC : Bitmap s.imem (s.ptrs 3) C)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) (v : Fin n) :
    (fullEval n es.length s).imem (address (s.ptrs 4) v) =
      if v ∉ C ∧ (∃ u ∈ C, G.Adj u v) then 1 else 0 := by
  rw [fullEval_imem]
  exact BoundaryProgram.fullEval_boundary_bitmap G C es s hC he hsep hesep hsound hcomplete v

lemma fullEval_imem_frame {n : ℕ} (es : List (Fin n × Fin n)) (s : Store)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (fullEval n es.length s).imem x = s.imem x := by
  rw [fullEval_imem]
  exact BoundaryProgram.fullEval_imem_frame es s he hesep x hx


/- Equality of exact zero/one bitmap cells is equality of the represented sets. -/
lemma bitmap_equal_iff {n : ℕ} (mem : ℤ → ℤ) (a b : ℤ)
    (S T : Finset (Fin n)) (hS : Bitmap mem a S) (hT : Bitmap mem b T) :
    (∀ v : Fin n, mem (address a v) = mem (address b v)) ↔ S = T := by
  constructor
  · intro h
    apply Finset.ext
    intro v
    have hv := h v
    rw [hS v,hT v] at hv
    by_cases hs : v ∈ S <;> by_cases ht : v ∈ T <;> simp_all
  · rintro rfl v
    rw [hS v,hT v]

lemma compare_inputs {n : ℕ} (G : SimpleGraph (Fin n))
    (C S : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store)
    (hC : Bitmap s.imem (s.ptrs 3) C) (hS : Bitmap s.imem (s.ptrs 17) S)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hSsep : Separate (n := n) (s.ptrs 17) (s.ptrs 4))
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    let x := redirect (BoundaryProgram.fullEval n es.length s)
    Bitmap x.imem (x.ptrs 3) S ∧
    Bitmap x.imem (x.ptrs 4) (BoundaryMemory.externalBoundary G C) := by
  dsimp only
  constructor
  · rw [redirect_imem,redirect_ptr3,
      BoundaryProgram.fullEval_ptr_frame n es.length s 17 (by omega)]
    intro v
    rw [BoundaryProgram.fullEval_imem_frame es s he hesep _ (hSsep v)]
    exact hS v
  · rw [redirect_imem,redirect_ptr_ne _ 4 (by decide) (by decide),
      BoundaryProgram.fullEval_ptr_frame n es.length s 4 (by omega)]
    exact (BoundaryProgram.fullEval_boundary G C es s hC he hsep hesep hsound hcomplete).2

lemma fullEval_flag {n : ℕ} (G : SimpleGraph (Fin n))
    (C S : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ))
    (hC : Bitmap s.imem (s.ptrs 3) C) (hS : Bitmap s.imem (s.ptrs 17) S)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hSsep : Separate (n := n) (s.ptrs 17) (s.ptrs 4))
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    (fullEval n es.length s).ptrs 18 =
      if S = BoundaryMemory.externalBoundary G C then 1 else 0 := by
  let x := redirect (BoundaryProgram.fullEval n es.length s)
  have hn' : x.ptrs 6 = (n:ℤ) := by
    rw [redirect_ptr_ne _ 6 (by decide) (by decide),
      BoundaryProgram.fullEval_ptr_frame n es.length s 6 (by omega),hn]
  have hb := compare_inputs G C S es s hC hS he hsep hSsep hesep hsound hcomplete
  change (ArrayEquality.equalityEval n x).ptrs 18 = _
  rw [ArrayEquality.equality_flag n x hn']
  have heq := bitmap_equal_iff x.imem (x.ptrs 3) (x.ptrs 4) S
    (BoundaryMemory.externalBoundary G C) hb.1 hb.2
  by_cases h : S = BoundaryMemory.externalBoundary G C
  · have h' : ∀ i : Fin n, x.imem (x.ptrs 3 + (i.val:ℤ)) =
        x.imem (x.ptrs 4 + (i.val:ℤ)) := heq.mpr h
    simp [h,h']
  · have h' : ¬ ∀ i : Fin n, x.imem (x.ptrs 3 + (i.val:ℤ)) =
        x.imem (x.ptrs 4 + (i.val:ℤ)) := fun h' => h (heq.mp h')
    simp [h,h']

lemma fullEval_flag_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (C S : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ))
    (hC : Bitmap s.imem (s.ptrs 3) C) (hS : Bitmap s.imem (s.ptrs 17) S)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hSsep : Separate (n := n) (s.ptrs 17) (s.ptrs 4))
    (hesep : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    (fullEval n es.length s).ptrs 18 = 1 ↔ S = BoundaryMemory.externalBoundary G C := by
  rw [fullEval_flag G C S es s hn hC hS he hsep hSsep hesep hsound hcomplete]
  by_cases h : S = BoundaryMemory.externalBoundary G C <;> simp [h]

/- Construct the external boundary and compare it against an ordinary candidate
bitmap, with a canonical Boolean flag and no precomputed answer as advice. -/
end StableMSR.Recovery.Compiler.TightBoundaryProgram
/- Verified boundary construction and statistics: BitmapStatsSemantics.lean -/

namespace StableMSR.Recovery.BitmapStatsSemantics

variable {n : ℕ}

/- Whether the ordinary zero-based index is marked. -/
def marked (C : Finset (Fin n)) (i : ℕ) : Prop := ∃ v ∈ C, v.val = i

instance (C : Finset (Fin n)) (i : ℕ) : Decidable (marked C i) :=
  inferInstanceAs (Decidable (∃ v ∈ C, v.val = i))

@[simp] theorem marked_iff_mem (C : Finset (Fin n)) (v : Fin n) :
    marked C v.val ↔ v ∈ C := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact (Fin.ext he : w = v) ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

theorem bitmap_positive_iff {mem : ℤ → ℤ} {base : ℤ} {C : Finset (Fin n)}
    (hbitmap : ComponentMemory.Bitmap mem base C) (k : ℕ) (hk : k < n) :
    0 < mem (base + (k : ℤ)) ↔ marked C k := by
  have h := hbitmap ⟨k,hk⟩
  change mem (base + (k : ℤ)) = _ at h
  rw [h]
  have hm : marked C k ↔ (⟨k,hk⟩ : Fin n) ∈ C := marked_iff_mem C ⟨k,hk⟩
  rw [hm]
  split <;> simp_all

/- Scan positions k-1,...,0, adding one per mark and overwriting the minimum.
The incoming minimum is at least k. -/
def scan (C : Finset (Fin n)) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, count, minimum => (count, minimum)
  | k + 1, count, minimum =>
    if marked C k then scan C k (count + 1) k else scan C k count minimum

def below (C : Finset (Fin n)) (k : ℕ) : Finset (Fin n) :=
  C.filter (fun v => v.val < k)

@[simp] theorem mem_below (C : Finset (Fin n)) (k : ℕ) (v : Fin n) :
    v ∈ below C k ↔ v ∈ C ∧ v.val < k := Finset.mem_filter

theorem below_succ_marked (C : Finset (Fin n)) (k : ℕ) {v : Fin n}
    (hv : v ∈ C) (hval : v.val = k) :
    below C (k + 1) = insert v (below C k) := by
  ext w
  simp only [mem_below, Finset.mem_insert]
  constructor
  · rintro ⟨hw, hlt⟩
    by_cases he : w.val = k
    · exact Or.inl (Fin.ext (he.trans hval.symm))
    · exact Or.inr ⟨hw, by omega⟩
  · rintro (rfl | ⟨hw, hlt⟩)
    · exact ⟨hv, by omega⟩
    · exact ⟨hw, by omega⟩

theorem below_succ_unmarked (C : Finset (Fin n)) (k : ℕ)
    (h : ¬ marked C k) : below C (k + 1) = below C k := by
  ext v
  simp only [mem_below]
  constructor
  · rintro ⟨hv, hlt⟩
    exact ⟨hv, by have hn : v.val ≠ k := fun he => h ⟨v,hv,he⟩; omega⟩
  · rintro ⟨hv, hlt⟩
    exact ⟨hv, by omega⟩

/- Complete invariant of the descending scan: exact count, all lower bounds,
and either the incoming sentinel or a genuinely marked index. -/
theorem scan_spec (C : Finset (Fin n)) (k count minimum : ℕ)
    (hb : k ≤ minimum) :
    (scan C k count minimum).1 = count + (below C k).card ∧
    (scan C k count minimum).2 ≤ minimum ∧
    (∀ v ∈ below C k, (scan C k count minimum).2 ≤ v.val) ∧
    ((scan C k count minimum).2 = minimum ∨
      ∃ v ∈ below C k, (scan C k count minimum).2 = v.val) := by
  induction k generalizing count minimum with
  | zero => simp [scan, below]
  | succ k ih =>
    by_cases hm : marked C k
    · obtain ⟨v,hv,hval⟩ := hm
      have ih' := ih (count+1) k (by omega)
      have hbelow := below_succ_marked C k hv hval
      have hn : v ∉ below C k := by simp [hval]
      simp only [scan, if_pos (show marked C k from ⟨v,hv,hval⟩)]
      refine ⟨?_, ih'.2.1.trans (by omega), ?_, ?_⟩
      · rw [hbelow, Finset.card_insert_of_notMem hn, ih'.1]
        omega
      · intro w hw
        rw [hbelow] at hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · simpa [hval] using ih'.2.1
        · exact ih'.2.2.1 w hw
      · rcases ih'.2.2.2 with he | ⟨w,hw,he⟩
        · exact Or.inr ⟨v, by rw [hbelow]; exact Finset.mem_insert_self _ _, he.trans hval.symm⟩
        · exact Or.inr ⟨w, by rw [hbelow]; exact Finset.mem_insert_of_mem hw, he⟩
    · simpa only [scan, if_neg hm, below_succ_unmarked C k hm]
        using ih count minimum (by omega)

@[simp] theorem below_all (C : Finset (Fin n)) : below C n = C := by
  ext v
  simp [v.isLt]

/- The least marked index; n is the sentinel precisely for an empty bitmap. -/
def least (C : Finset (Fin n)) : ℕ :=
  if h : C.Nonempty then (C.min' h).val else n

theorem scan_all_count (C : Finset (Fin n)) : (scan C n 0 n).1 = C.card := by
  simpa using (scan_spec C n 0 n (by omega)).1

theorem scan_all_least (C : Finset (Fin n)) : (scan C n 0 n).2 = least C := by
  have hs := scan_spec C n 0 n (by omega)
  simp only [below_all] at hs
  by_cases h : C.Nonempty
  · obtain ⟨v,hv⟩ := h
    have hn : (scan C n 0 n).2 ≠ n := by
      have := hs.2.2.1 v hv
      have := v.isLt
      omega
    obtain ⟨w,hw,he⟩ := hs.2.2.2.resolve_left hn
    have hlo : ((C.min' ⟨v,hv⟩).val) ≤ (scan C n 0 n).2 := by
      rw [he]
      exact Finset.min'_le C w hw
    have hhi := hs.2.2.1 (C.min' ⟨v,hv⟩) (Finset.min'_mem C ⟨v,hv⟩)
    simp only [least, dif_pos (show C.Nonempty from ⟨v,hv⟩)]
    exact Nat.le_antisymm hhi hlo
  · simp only [least, dif_neg h]
    rcases hs.2.2.2 with he | ⟨v,hv,_⟩
    · exact he
    · exact (h ⟨v,hv⟩).elim

theorem scan_all (C : Finset (Fin n)) : scan C n 0 n = (C.card, least C) :=
  Prod.ext (scan_all_count C) (scan_all_least C)

theorem least_eq_sentinel_iff (C : Finset (Fin n)) : least C = n ↔ C = ∅ := by
  by_cases h : C.Nonempty
  · have hlt : least C < n := by simp [least, h, (C.min' h).isLt]
    constructor
    · intro he; omega
    · intro he; exact (h.ne_empty he).elim
  · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [least, h, he]

theorem least_mem_and_le (C : Finset (Fin n)) (h : C.Nonempty) :
    (∃ v ∈ C, v.val = least C) ∧ ∀ v ∈ C, least C ≤ v.val := by
  simp only [least, dif_pos h]
  exact ⟨⟨C.min' h, Finset.min'_mem C h, rfl⟩, fun v hv => Finset.min'_le C v hv⟩

end StableMSR.Recovery.BitmapStatsSemantics



/- Verified boundary construction and statistics: BitmapStatsMachine.lean -/
set_option autoImplicit false

namespace StableMSR.Recovery.Compiler.BitmapStats

open ComponentMachine

def prepOps : List Op :=
  [.pointerConst 0 0, .pointerConst 18 0, .pointerCopy 19 6,
    .pointerCopy 20 6, .pointerDec 20]

def prepEval (s : Store) : Store :=
  setPtr (setPtr (setPtr (setPtr s 0 0) 18 0) 19 (s.ptrs 6)) 20 (s.ptrs 6 - 1)

def pad3 : Cmd := .seq nop pad2

def selectCmd : Cmd :=
  .ite (.pointerLE 22 0) pad3 (opsCmd [.pointerInc 18, .pointerCopy 19 20])

def selectEval (s : Store) : Store :=
  if s.ptrs 22 ≤ s.ptrs 0 then s else setPtr (incPtr s 18) 19 (s.ptrs 20)

def body : Cmd :=
  .seq (opsCmd [.pointerAdd 21 3 20, .integerLoad 22 21])
    (.seq selectCmd (.atom (.pointerDec 20)))

def inputEval (s : Store) : Store :=
  setPtr (setPtr s 21 (s.ptrs 3 + s.ptrs 20)) 22 (s.imem (s.ptrs 3 + s.ptrs 20))

def step (s : Store) : Store :=
  let t := selectEval (inputEval s)
  setPtr t 20 (t.ptrs 20 - 1)

def run : ℕ → Store → Store
  | 0, s => s
  | q+1, s => run q (step s)

def loop : Cmd := .whileDo (.pointerLE 0 20) body

def statsCmd : Cmd := .seq (opsCmd prepOps) loop

def statsEval (q : ℕ) (s : Store) : Store := run q (prepEval s)

@[simp] lemma statsCmd_size : statsCmd.size = 18 := rfl

lemma prep_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d (opsCmd prepOps) s (prepEval s) 5 := by
  simpa [prepOps,evalOps,prepEval,Op.eval,setPtr,Function.update_idem] using
    ops_exec d prepOps s

lemma select_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d selectCmd s (selectEval s) 4 := by
  by_cases h : s.ptrs 22 ≤ s.ptrs 0
  · have hp : Executes d pad3 s s 3 := Executes.seq (nop_exec d s) (pad2_exec d s)
    simpa [selectCmd,selectEval,h] using
      Executes.ite_true (c := Cond.pointerLE 22 0)
        (no := opsCmd [.pointerInc 18, .pointerCopy 19 20]) h hp
  · have hp := ops_exec d [.pointerInc 18, .pointerCopy 19 20] s
    simpa [selectCmd,selectEval,h,evalOps,Op.eval,incPtr,setPtr] using
      Executes.ite_false (c := Cond.pointerLE 22 0) (yes := pad3) h hp

lemma body_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d body s (step s) 7 := by
  have hi : Executes d (opsCmd [.pointerAdd 21 3 20, .integerLoad 22 21])
      s (inputEval s) 2 := by
    simpa [evalOps,Op.eval,inputEval,setPtr] using
      ops_exec d [.pointerAdd 21 3 20, .integerLoad 22 21] s
  exact Executes.seq hi (Executes.seq (select_exec d _)
    (Executes.atom (.pointerDec 20) _))

lemma step_ptr_frame (s : Store) (j : ℕ)
    (h18 : j ≠ 18) (h19 : j ≠ 19) (h20 : j ≠ 20)
    (h21 : j ≠ 21) (h22 : j ≠ 22) :
    (step s).ptrs j = s.ptrs j := by
  simp only [step,selectEval]
  split <;> simp [setPtr,incPtr,inputEval,h18,h19,h20,h21,h22]

lemma step_index (s : Store) : (step s).ptrs 20 = s.ptrs 20 - 1 := by
  simp only [step,selectEval]
  split <;> simp [setPtr,incPtr,inputEval]

lemma step_count (s : Store) :
    (step s).ptrs 18 = if s.imem (s.ptrs 3+s.ptrs 20) ≤ s.ptrs 0
      then s.ptrs 18 else s.ptrs 18+1 := by
  simp only [step,selectEval]
  split <;> simp_all [setPtr,incPtr,inputEval]

lemma step_minimum (s : Store) :
    (step s).ptrs 19 = if s.imem (s.ptrs 3+s.ptrs 20) ≤ s.ptrs 0
      then s.ptrs 19 else s.ptrs 20 := by
  simp only [step,selectEval]
  split <;> simp_all [setPtr,incPtr,inputEval]

lemma step_frame (s : Store) :
    (step s).regs = s.regs ∧ (step s).mem = s.mem ∧ (step s).imem = s.imem ∧
    (step s).queries = s.queries ∧ (step s).tapePos = s.tapePos ∧
    (step s).output = s.output := by
  simp only [step,selectEval]
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

lemma run_ptr_frame (q : ℕ) (s : Store) (j : ℕ)
    (h18 : j ≠ 18) (h19 : j ≠ 19) (h20 : j ≠ 20)
    (h21 : j ≠ 21) (h22 : j ≠ 22) :
    (run q s).ptrs j = s.ptrs j := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih => rw [run,ih,step_ptr_frame s j h18 h19 h20 h21 h22]

lemma run_frame (q : ℕ) (s : Store) :
    (run q s).regs = s.regs ∧ (run q s).mem = s.mem ∧ (run q s).imem = s.imem ∧
    (run q s).queries = s.queries ∧ (run q s).tapePos = s.tapePos ∧
    (run q s).output = s.output := by
  induction q generalizing s with
  | zero => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  | succ q ih =>
    rcases ih (step s) with ⟨h1,h2,h3,h4,h5,h6⟩
    rcases step_frame s with ⟨g1,g2,g3,g4,g5,g6⟩
    exact ⟨h1.trans g1,h2.trans g2,h3.trans g3,h4.trans g4,h5.trans g5,h6.trans g6⟩

lemma loop_exec {N : ℕ} (d : Point N → Point N → ℝ)
    (q : ℕ) (s : Store) (hzero : s.ptrs 0 = 0)
    (hindex : s.ptrs 20 = (q : ℤ)-1) :
    Executes d loop s (run q s) (9*q+2) := by
  induction q generalizing s with
  | zero =>
    apply Executes.while_false
    simp only [Cond.test,hzero,hindex,Nat.cast_zero]
    omega
  | succ q ih =>
    have hg : (Cond.pointerLE 0 20).test s := by
      simp only [Cond.test,hzero,hindex,Nat.cast_add,Nat.cast_one]
      omega
    have hz : (step s).ptrs 0 = 0 := by
      rw [step_ptr_frame s 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hzero
    have hi : (step s).ptrs 20 = (q : ℤ)-1 := by
      rw [step_index,hindex]
      push_cast
      omega
    have he := Executes.while_true hg (body_exec d s) (ih (step s) hz hi)
    simpa only [loop,run,show 1+7+1+(9*q+2)=9*(q+1)+2 by omega] using he

lemma stats_exec {N : ℕ} (d : Point N → Point N → ℝ)
    (q : ℕ) (s : Store) (hcount : s.ptrs 6 = (q : ℤ)) :
    Executes d statsCmd s (statsEval q s) (9*q+7) := by
  have hz : (prepEval s).ptrs 0 = 0 := by simp [prepEval,setPtr]
  have hi : (prepEval s).ptrs 20 = (q : ℤ)-1 := by simp [prepEval,setPtr,hcount]
  have h := Executes.seq (prep_exec d s) (loop_exec d q (prepEval s) hz hi)
  simpa only [statsCmd,statsEval,show 5+(9*q+2)=9*q+7 by omega] using h

lemma stats_ptr_frame (q : ℕ) (s : Store) (j : ℕ)
    (h0 : j ≠ 0) (h18 : j ≠ 18) (h19 : j ≠ 19) (h20 : j ≠ 20)
    (h21 : j ≠ 21) (h22 : j ≠ 22) :
    (statsEval q s).ptrs j = s.ptrs j := by
  rw [statsEval,run_ptr_frame q (prepEval s) j h18 h19 h20 h21 h22]
  simp [prepEval,setPtr,h0,h18,h19,h20]

lemma stats_frame (q : ℕ) (s : Store) :
    (statsEval q s).regs = s.regs ∧ (statsEval q s).mem = s.mem ∧
    (statsEval q s).imem = s.imem ∧ (statsEval q s).queries = s.queries ∧
    (statsEval q s).tapePos = s.tapePos ∧ (statsEval q s).output = s.output :=
  run_frame q (prepEval s)

end StableMSR.Recovery.Compiler.BitmapStats



/- Verified boundary construction and statistics: BitmapStats.lean -/
set_option autoImplicit false

namespace StableMSR.Recovery.Compiler.BitmapStats

open ComponentMachine ComponentMemory BitmapStatsSemantics

lemma run_stats {n : ℕ} (C : Finset (Fin n)) (q : ℕ) (s : Store)
    (count minimum : ℕ) (hq : q ≤ n) (hzero : s.ptrs 0 = 0)
    (hindex : s.ptrs 20 = (q : ℤ)-1)
    (hbitmap : Bitmap s.imem (s.ptrs 3) C)
    (hcount : s.ptrs 18 = (count : ℤ)) (hminimum : s.ptrs 19 = (minimum : ℤ)) :
    (run q s).ptrs 18 = ((scan C q count minimum).1 : ℤ) ∧
    (run q s).ptrs 19 = ((scan C q count minimum).2 : ℤ) := by
  induction q generalizing s count minimum with
  | zero => exact ⟨hcount,hminimum⟩
  | succ q ih =>
    let v : Fin n := ⟨q,by omega⟩
    have hv : marked C q ↔ v ∈ C := marked_iff_mem C v
    have hi : s.ptrs 20 = (q : ℤ) := by
      rw [hindex]
      push_cast
      omega
    have hcell : s.imem (s.ptrs 3+s.ptrs 20) = if v ∈ C then 1 else 0 := by
      rw [hi]
      exact hbitmap v
    have ht : s.imem (s.ptrs 3+s.ptrs 20) ≤ s.ptrs 0 ↔ ¬ marked C q := by
      rw [hcell,hzero,hv]
      by_cases hm : v ∈ C <;> simp [hm]
    have hz : (step s).ptrs 0 = 0 := by
      rw [step_ptr_frame s 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hzero
    have hb : Bitmap (step s).imem ((step s).ptrs 3) C := by
      rw [(step_frame s).2.2.1,
        step_ptr_frame s 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hbitmap
    have hnext : (step s).ptrs 20 = (q : ℤ)-1 := by rw [step_index,hi]
    by_cases hm : marked C q
    · have hn : ¬ (s.imem (s.ptrs 3+s.ptrs 20) ≤ s.ptrs 0) := by
        intro h
        exact ht.mp h hm
      have hc : (step s).ptrs 18 = ((count+1 : ℕ) : ℤ) := by
        rw [step_count,if_neg hn,hcount]
        push_cast
        rfl
      have hmin : (step s).ptrs 19 = (q : ℤ) := by rw [step_minimum,if_neg hn,hi]
      simpa only [run,scan,if_pos hm] using
        ih (step s) (count+1) q (by omega) hz hnext hb hc hmin
    · have hy := ht.mpr hm
      have hc : (step s).ptrs 18 = (count : ℤ) := by rw [step_count,if_pos hy,hcount]
      have hmin : (step s).ptrs 19 = (minimum : ℤ) := by
        rw [step_minimum,if_pos hy,hminimum]
      simpa only [run,scan,if_neg hm] using
        ih (step s) count minimum (by omega) hz hnext hb hc hmin

lemma stats_values {n : ℕ} (s : Store) (C : Finset (Fin n))
    (hcount : s.ptrs 6 = (n : ℤ)) (hbitmap : Bitmap s.imem (s.ptrs 3) C) :
    (statsEval n s).ptrs 18 = (C.card : ℤ) ∧
    (statsEval n s).ptrs 19 = (least C : ℤ) := by
  have hp : Bitmap (prepEval s).imem ((prepEval s).ptrs 3) C := by
    simpa [prepEval,setPtr] using hbitmap
  have h := run_stats C n (prepEval s) 0 n (le_refl _)
    (by simp [prepEval,setPtr]) (by simp [prepEval,setPtr,hcount]) hp
    (by simp [prepEval,setPtr]) (by simp [prepEval,setPtr,hcount])
  simpa only [statsEval,scan_all] using h

lemma stats_count {n : ℕ} (s : Store) (C : Finset (Fin n))
    (hcount : s.ptrs 6 = (n : ℤ)) (hbitmap : Bitmap s.imem (s.ptrs 3) C) :
    (statsEval n s).ptrs 18 = (C.card : ℤ) :=
  (stats_values s C hcount hbitmap).1

lemma stats_sentinel_iff {n : ℕ} (s : Store) (C : Finset (Fin n))
    (hcount : s.ptrs 6 = (n : ℤ)) (hbitmap : Bitmap s.imem (s.ptrs 3) C) :
    (statsEval n s).ptrs 19 = (n : ℤ) ↔ C = ∅ := by
  rw [(stats_values s C hcount hbitmap).2,Nat.cast_inj]
  exact least_eq_sentinel_iff C

lemma stats_minimum {n : ℕ} (s : Store) (C : Finset (Fin n))
    (hcount : s.ptrs 6 = (n : ℤ)) (hbitmap : Bitmap s.imem (s.ptrs 3) C)
    (hne : C.Nonempty) :
    ∃ v ∈ C, (statsEval n s).ptrs 19 = (v.val : ℤ) ∧
      ∀ u ∈ C, v.val ≤ u.val := by
  rcases least_mem_and_le C hne with ⟨⟨v,hv,he⟩,hmin⟩
  refine ⟨v,hv,?_,?_⟩
  · rw [(stats_values s C hcount hbitmap).2,he]
  · intro u hu
    rw [he]
    exact hmin u hu

lemma stats_minimum_bounds {n : ℕ} (s : Store) (C : Finset (Fin n))
    (hcount : s.ptrs 6 = (n : ℤ)) (hbitmap : Bitmap s.imem (s.ptrs 3) C) :
    0 ≤ (statsEval n s).ptrs 19 ∧ (statsEval n s).ptrs 19 ≤ (n : ℤ) := by
  rw [(stats_values s C hcount hbitmap).2]
  constructor
  · exact Nat.cast_nonneg _
  · apply Nat.cast_le.mpr
    by_cases h : C.Nonempty
    · simp only [least,dif_pos h]
      exact Nat.le_of_lt (C.min' h).isLt
    · simp [least,h]

/- One fixed deterministic program counts a bitmap and returns its least marked index. -/
theorem bitmap_statistics_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 19 ∧
      ∀ (N n : ℕ) (d : Point N → Point N → ℝ) (ω : ℕ → ℝ)
        (s : Store) (C : Finset (Fin n)) (w : ℕ),
        s.ptrs 6 = (n : ℤ) → Bitmap s.imem (s.ptrs 3) C →
        ∃ t : Store,
          t.ptrs 18 = (C.card : ℤ) ∧
          (t.ptrs 19 = (n : ℤ) ↔ C = ∅) ∧
          (C.Nonempty → ∃ v ∈ C, t.ptrs 19 = (v.val : ℤ) ∧
            ∀ u ∈ C, v.val ≤ u.val) ∧
          (0 ≤ t.ptrs 19 ∧ t.ptrs 19 ≤ (n : ℤ)) ∧
          (∀ j : ℕ, j ≠ 0 → j ≠ 18 → j ≠ 19 → j ≠ 20 →
            j ≠ 21 → j ≠ 22 → t.ptrs j = s.ptrs j) ∧
          t.regs = s.regs ∧ t.mem = s.mem ∧ t.imem = s.imem ∧
          t.queries = s.queries ∧ t.tapePos = s.tapePos ∧ t.output = s.output ∧
          (MinSumFPT.step P d ω)^[9*n+8] (s.state 0 w) =
            t.haltedState 18 (w+(9*n+8)) 0 := by
  refine ⟨compile statsCmd 0,compile_deterministic statsCmd 0,?_,?_⟩
  · simp [compile]
  · intro N n d ω s C w hcount hbitmap
    refine ⟨statsEval n s,stats_count s C hcount hbitmap,
      stats_sentinel_iff s C hcount hbitmap,
      stats_minimum s C hcount hbitmap,stats_minimum_bounds s C hcount hbitmap,?_,?_⟩
    · intro j h0 h18 h19 h20 h21 h22
      exact stats_ptr_frame n s j h0 h18 h19 h20 h21 h22
    · rcases stats_frame n s with ⟨h1,h2,h3,h4,h5,h6⟩
      refine ⟨h1,h2,h3,h4,h5,h6,?_⟩
      have h := compile_halts (stats_exec d n s hcount) ω w 0
      simpa only [statsCmd_size,show 9*n+7+1=9*n+8 by omega,
        show w+(9*n+7)+1=w+(9*n+8) by omega] using h

end StableMSR.Recovery.Compiler.BitmapStats



set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace StableMSR.Recovery.Compiler.MaskComplement
open ComponentMachine ComponentMemory

def bodyOps : List Op := [.pointerAdd 7 3 8,.integerLoad 10 7,.pointerSub 11 1 10,
  .pointerAdd 12 4 8,.integerStore 12 11,.pointerInc 8]
def body : Cmd := opsCmd bodyOps
def step (s : Store) : Store :=
  setPtr { (setPtr (setPtr (setPtr (setPtr s 7 (s.ptrs 3+s.ptrs 8))
      10 (s.imem (s.ptrs 3+s.ptrs 8))) 11 (s.ptrs 1-s.imem (s.ptrs 3+s.ptrs 8)))
      12 (s.ptrs 4+s.ptrs 8)) with
    imem := Function.update s.imem (s.ptrs 4+s.ptrs 8)
      (s.ptrs 1-s.imem (s.ptrs 3+s.ptrs 8)) } 8 (s.ptrs 8+1)
def run (q : ℕ) (s : Store) : Store := step^[q] s
lemma step_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d body s (step s) 6 := by
  simpa [body,bodyOps,evalOps,Op.eval,step,setPtr] using ops_exec d bodyOps s
lemma step_ptr (s : Store) (j : ℕ) (hj : j ∉ ([7,8,10,11,12]:List ℕ)) :
    (step s).ptrs j = s.ptrs j := by simp_all [step,setPtr]
lemma step_index (s : Store) : (step s).ptrs 8 = s.ptrs 8+1 := by simp [step,setPtr]
lemma step_imem (s : Store) : (step s).imem =
    Function.update s.imem (s.ptrs 4+s.ptrs 8) (s.ptrs 1-s.imem (s.ptrs 3+s.ptrs 8)) := rfl
lemma run_ptr (q : ℕ) (s : Store) (j : ℕ) (hj : j ∉ ([7,8,10,11,12]:List ℕ)) :
    (run q s).ptrs j = s.ptrs j :=
  iterate_preserves step (fun t => t.ptrs j) (fun t => step_ptr t j hj) q s
lemma run_index (q : ℕ) (s : Store) : (run q s).ptrs 8 = s.ptrs 8+(q:ℤ) := by
  simpa [run] using iterate_additive step (fun t => t.ptrs 8) 1 step_index q s
lemma run_frame (q : ℕ) (s : Store) : DataFrame s (run q s) :=
  iterate_frame step (fun _ => ⟨rfl,rfl,rfl,rfl,rfl⟩) q s

lemma run_memory_frame (q : ℕ) (s : Store) (x : ℤ)
    (hx : ∀ j : Fin q, x ≠ s.ptrs 4+s.ptrs 8+(j.val:ℤ)) :
    (run q s).imem x = s.imem x := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih =>
    rw [run,Function.iterate_succ_apply]
    change (run q (step s)).imem x = _
    rw [ih (step s)]
    · rw [step_imem,Function.update_of_ne]
      simpa using hx ⟨0,by omega⟩
    · intro j
      rw [step_ptr s 4 (by simp),step_index]
      have hh := hx ⟨j.val+1,by have := j.isLt; omega⟩
      convert hh using 1 <;> push_cast <;> ring

lemma run_readback (q : ℕ) (s : Store)
    (hsep : ∀ i j : Fin q,
      s.ptrs 3+s.ptrs 8+(i.val:ℤ) ≠ s.ptrs 4+s.ptrs 8+(j.val:ℤ)) :
    ∀ j : Fin q, (run q s).imem (s.ptrs 4+s.ptrs 8+(j.val:ℤ)) =
      s.ptrs 1-s.imem (s.ptrs 3+s.ptrs 8+(j.val:ℤ)) := by
  induction q generalizing s with
  | zero => intro j; exact Fin.elim0 j
  | succ q ih =>
    have hs : ∀ i j : Fin q, (step s).ptrs 3+(step s).ptrs 8+(i.val:ℤ) ≠
        (step s).ptrs 4+(step s).ptrs 8+(j.val:ℤ) := by
      intro i j
      rw [step_ptr s 3 (by simp),step_ptr s 4 (by simp),step_index]
      have hh := hsep ⟨i.val+1,by have := i.isLt; omega⟩ ⟨j.val+1,by have := j.isLt; omega⟩
      convert hh using 1 <;> push_cast <;> ring
    intro j
    rw [run,Function.iterate_succ_apply]
    change (run q (step s)).imem _ = _
    by_cases hz : j.val = 0
    · simp only [hz,Nat.cast_zero,add_zero]
      rw [run_memory_frame q (step s)]
      · rw [step_imem,Function.update_self]
      · intro i
        rw [step_ptr s 4 (by simp),step_index]
        have hi : 0 ≤ (i.val:ℤ) := by omega
        omega
    · let i : Fin q := ⟨j.val-1,by have := j.isLt; omega⟩
      have he : (step s).ptrs 4+(step s).ptrs 8+(i.val:ℤ) =
          s.ptrs 4+s.ptrs 8+(j.val:ℤ) := by
        rw [step_ptr s 4 (by simp),step_index]; dsimp [i]; omega
      rw [←he,ih (step s) hs i,step_ptr s 1 (by simp),step_ptr s 3 (by simp),step_index]
      have he' : s.ptrs 3+(s.ptrs 8+1)+(i.val:ℤ) =
          s.ptrs 3+s.ptrs 8+(j.val:ℤ) := by dsimp [i]; omega
      rw [he',step_imem,Function.update_of_ne]
      simpa using hsep j ⟨0,by omega⟩

def prepOps : List Op := [.pointerConst 1 1,.pointerConst 8 0,.pointerCopy 9 6,.pointerDec 9]
def prep (s : Store) : Store := setPtr (setPtr (setPtr s 1 1) 8 0) 9 (s.ptrs 6-1)
def command : Cmd := .seq (opsCmd prepOps) (.whileDo (.pointerLE 8 9) body)
def eval (n : ℕ) (s : Store) : Store := run n (prep s)
lemma exec {N : ℕ} (d : Point N → Point N → ℝ) (n : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) : Executes d command s (eval n s) (8*n+6) := by
  have hp : Executes d (opsCmd prepOps) s (prep s) 4 := by
    simpa [prepOps,prep,evalOps,Op.eval,setPtr,Function.update_idem] using ops_exec d prepOps s
  have hl := fixed_loop_exec d body step 8 9 6 ((n:ℤ)-1)
    (fun t _ => step_exec d t) step_index (fun t => step_ptr t 9 (by simp)) n (prep s)
    (by simp [prep,setPtr,hn]) (by simp [prep,setPtr])
  convert Executes.seq hp hl using 1 <;> try rfl
  omega
lemma ptr_frame (n : ℕ) (s : Store) (j : ℕ) (hj : j ∉ ([1,7,8,9,10,11,12]:List ℕ)) :
    (eval n s).ptrs j = s.ptrs j := by
  rw [eval,run_ptr n (prep s) j (by simp_all)]
  simp_all [prep,setPtr]
lemma frame (n : ℕ) (s : Store) : DataFrame s (eval n s) := run_frame n (prep s)
lemma memory_frame (n : ℕ) (s : Store) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) : (eval n s).imem x = s.imem x := by
  apply run_memory_frame n (prep s) x
  simpa [prep,setPtr,address] using hx
lemma bitmap {n : ℕ} (S : Finset (Fin n)) (s : Store)
    (hS : Bitmap s.imem (s.ptrs 3) S) (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4)) :
    Bitmap (eval n s).imem (s.ptrs 4) Sᶜ := by
  intro v
  have hs : ∀ i j : Fin n, (prep s).ptrs 3+(prep s).ptrs 8+(i.val:ℤ) ≠
      (prep s).ptrs 4+(prep s).ptrs 8+(j.val:ℤ) := by simpa [prep,setPtr,Separate,address] using hsep
  have h := run_readback n (prep s) hs v
  by_cases hv : v ∈ S <;> simpa [hv,address,eval,prep,setPtr,show s.imem (s.ptrs 3+(v.val:ℤ)) = if v ∈ S then 1 else 0 from hS v]
    using h
end StableMSR.Recovery.Compiler.MaskComplement
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace StableMSR.Recovery.Compiler.ComponentState
open ComponentMachine ComponentMemory

/- Persistent metadata: separator, allowed, component and boundary bases,
seed index, width bound and separator cardinality. -/
def saveOps : List Op := [.pointerCopy 53 3,.pointerCopy 54 4,.pointerCopy 55 50,
  .pointerCopy 56 51,.pointerCopy 57 17,.pointerCopy 58 43,.pointerCopy 59 18]
def saved (s : Store) : Store :=
  setPtr (setPtr (setPtr (setPtr (setPtr (setPtr (setPtr s 53 (s.ptrs 3))
    54 (s.ptrs 4)) 55 (s.ptrs 50)) 56 (s.ptrs 51)) 57 (s.ptrs 17))
    58 (s.ptrs 43)) 59 (s.ptrs 18)
def readOps : List Op := [.pointerAdd 7 53 57,.integerLoad 60 7]
def readSeed (s : Store) : Store :=
  setPtr (setPtr s 7 (s.ptrs 53+s.ptrs 57)) 60 (s.imem (s.ptrs 53+s.ptrs 57))
def prefixCmd : Cmd := .seq BitmapStats.statsCmd
  (.seq (opsCmd saveOps) (.seq MaskComplement.command (opsCmd readOps)))
noncomputable def prefixEval (n : ℕ) (s : Store) : Store :=
  readSeed (MaskComplement.eval n (saved (BitmapStats.statsEval n s)))
lemma prefix_exec {N : ℕ} (d : Point N → Point N → ℝ) (n : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) : Executes d prefixCmd s (prefixEval n s) (17*n+22) := by
  have hs (t : Store) : Executes d (opsCmd saveOps) t (saved t) 7 := by
    simpa [saveOps,saved,evalOps,Op.eval,setPtr] using ops_exec d saveOps t
  have hr (t : Store) : Executes d (opsCmd readOps) t (readSeed t) 2 := by
    simpa [readOps,readSeed,evalOps,Op.eval,setPtr] using ops_exec d readOps t
  have hn' : (saved (BitmapStats.statsEval n s)).ptrs 6 = (n:ℤ) := by
    simp only [saved,setPtr,Function.update_of_ne (by decide : (6:ℕ) ≠ 59),
      Function.update_of_ne (by decide : (6:ℕ) ≠ 58),Function.update_of_ne (by decide : (6:ℕ) ≠ 57),
      Function.update_of_ne (by decide : (6:ℕ) ≠ 56),Function.update_of_ne (by decide : (6:ℕ) ≠ 55),
      Function.update_of_ne (by decide : (6:ℕ) ≠ 54),Function.update_of_ne (by decide : (6:ℕ) ≠ 53)]
    rw [BitmapStats.stats_ptr_frame n s 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),hn]
  have h := Executes.seq (BitmapStats.stats_exec d n s hn)
    (Executes.seq (hs _) (Executes.seq (MaskComplement.exec d n _ hn') (hr _)))
  convert h using 1 <;> try rfl
  omega

lemma prefix_ptr (n : ℕ) (s : Store) (j : ℕ)
    (hj : j ∈ ([2,3,4,5,6,17,43,50,51] : List ℕ)) : (prefixEval n s).ptrs j = s.ptrs j := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [prefixEval,readSeed,setPtr,MaskComplement.ptr_frame,saved,BitmapStats.stats_ptr_frame]
lemma prefix_saved (n : ℕ) (s : Store) :
    (prefixEval n s).ptrs 53 = s.ptrs 3 ∧ (prefixEval n s).ptrs 54 = s.ptrs 4 ∧
    (prefixEval n s).ptrs 55 = s.ptrs 50 ∧ (prefixEval n s).ptrs 56 = s.ptrs 51 ∧
    (prefixEval n s).ptrs 57 = s.ptrs 17 ∧ (prefixEval n s).ptrs 58 = s.ptrs 43 ∧
    (prefixEval n s).ptrs 59 = (BitmapStats.statsEval n s).ptrs 18 := by
  simp [prefixEval,readSeed,setPtr,MaskComplement.ptr_frame,saved,BitmapStats.stats_ptr_frame]
lemma prefix_frame (n : ℕ) (s : Store) : DataFrame s (prefixEval n s) := by
  have hs := BitmapStats.stats_frame n s
  have hm := MaskComplement.frame n (saved (BitmapStats.statsEval n s))
  exact ⟨hm.1.trans hs.1,hm.2.1.trans hs.2.1,hm.2.2.1.trans hs.2.2.2.1,
    hm.2.2.2.1.trans hs.2.2.2.2.1,hm.2.2.2.2.trans hs.2.2.2.2.2⟩
lemma prefix_memory_frame (n : ℕ) (s : Store) (x : ℤ)
    (hx : ∀ v : Fin n, x ≠ address (s.ptrs 4) v) :
    (prefixEval n s).imem x = s.imem x := by
  change (MaskComplement.eval n (saved (BitmapStats.statsEval n s))).imem x = _
  rw [MaskComplement.memory_frame n _ x]
  · exact congrFun (BitmapStats.stats_frame n s).2.2.1 x
  · simpa [saved,setPtr,BitmapStats.stats_ptr_frame] using hx
lemma prefix_bitmaps {n : ℕ} (S : Finset (Fin n)) (s : Store)
    (hS : Bitmap s.imem (s.ptrs 3) S)
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4)) :
    Bitmap (prefixEval n s).imem (s.ptrs 3) S ∧
    Bitmap (prefixEval n s).imem (s.ptrs 4) Sᶜ := by
  constructor
  · intro v
    rw [prefix_memory_frame n s _ (hsep v)]
    exact hS v
  · have hs : Bitmap (saved (BitmapStats.statsEval n s)).imem
        ((saved (BitmapStats.statsEval n s)).ptrs 3) S := by
      simpa [saved,setPtr,BitmapStats.stats_ptr_frame,(BitmapStats.stats_frame n s).2.2.1] using hS
    have h := MaskComplement.bitmap S (saved (BitmapStats.statsEval n s)) hs
      (by simpa [saved,setPtr,BitmapStats.stats_ptr_frame] using hsep)
    simpa [prefixEval,readSeed,setPtr,saved,BitmapStats.stats_ptr_frame] using h
lemma prefix_count {n : ℕ} (S : Finset (Fin n)) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hS : Bitmap s.imem (s.ptrs 3) S) :
    (prefixEval n s).ptrs 59 = (S.card:ℤ) := by
  rw [(prefix_saved n s).2.2.2.2.2.2,BitmapStats.stats_count s S hn hS]
lemma prefix_seed {n : ℕ} (S : Finset (Fin n)) (seed : Fin n) (s : Store)
    (hS : Bitmap s.imem (s.ptrs 3) S) (hseed : s.ptrs 17 = (seed.val:ℤ))
    (hsep : Separate (n := n) (s.ptrs 3) (s.ptrs 4)) :
    (prefixEval n s).ptrs 60 = if seed ∈ S then 1 else 0 := by
  change (MaskComplement.eval n (saved (BitmapStats.statsEval n s))).imem
    ((MaskComplement.eval n (saved (BitmapStats.statsEval n s))).ptrs 53+
     (MaskComplement.eval n (saved (BitmapStats.statsEval n s))).ptrs 57) = _
  simp only [MaskComplement.ptr_frame n _ 53 (by simp),MaskComplement.ptr_frame n _ 57 (by simp)]
  have hh : (saved (BitmapStats.statsEval n s)).ptrs 53+
      (saved (BitmapStats.statsEval n s)).ptrs 57 = s.ptrs 3+(seed.val:ℤ) := by
    simp [saved,setPtr,BitmapStats.stats_ptr_frame,hseed]
  rw [hh]
  have h := (prefix_bitmaps S s hS hsep).1 seed
  exact h

/- The component is computed before its boundary is compared; no component
bitmap or componenthood certificate is part of the input. -/
def componentOps : List Op := [.pointerCopy 3 54,.pointerCopy 4 55,.pointerCopy 17 57]
def componentInput (s : Store) : Store :=
  setPtr (setPtr (setPtr s 3 (s.ptrs 54)) 4 (s.ptrs 55)) 17 (s.ptrs 57)
def boundaryOps : List Op := [.pointerCopy 3 55,.pointerCopy 4 56,.pointerCopy 17 53]
def boundaryInput (s : Store) : Store :=
  setPtr (setPtr (setPtr s 3 (s.ptrs 55)) 4 (s.ptrs 56)) 17 (s.ptrs 53)
def restoreOps : List Op := [.pointerCopy 3 53,.pointerCopy 4 54,.pointerCopy 17 57]
def restored (s : Store) : Store :=
  setPtr (setPtr (setPtr s 3 (s.ptrs 53)) 4 (s.ptrs 54)) 17 (s.ptrs 57)
def constructCmd : Cmd := .seq (opsCmd componentOps) (.seq ComponentProgram.fullCmd
  (.seq (opsCmd boundaryOps) (.seq TightBoundaryProgram.fullCmd (opsCmd restoreOps))))
noncomputable def constructEval (n m : ℕ) (s : Store) : Store :=
  restored (TightBoundaryProgram.fullEval n m
    (boundaryInput (ComponentProgram.fullEval n m (componentInput s))))
def constructCost (n m : ℕ) : ℕ := n*(17*m+11)+15*n+17*m+43

lemma component_high (n m : ℕ) (s : Store) (j : ℕ) (hj : 17 < j) :
    (ComponentProgram.fullEval n m s).ptrs j = s.ptrs j := by
  rw [ComponentProgram.fullEval,block_ptr_frame m n (ComponentInit.initEval n s) j (by omega)]
  exact ComponentInit.init_ptr_ne n j s (by omega) (by omega) (by omega) (by omega)
lemma tight_high (n m : ℕ) (s : Store) (j : ℕ) (hj : 24 < j) :
    (TightBoundaryProgram.fullEval n m s).ptrs j = s.ptrs j := by
  rw [TightBoundaryProgram.fullEval,TightBoundaryProgram.restore_ptr_ne _ j (by omega),
    ArrayEquality.equality_ptr_frame n _ j (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega),
    TightBoundaryProgram.redirect_ptr_ne _ j (by omega) (by omega),
    BoundaryProgram.fullEval_ptr_frame n m s j (by omega)]
lemma construct_exec {N : ℕ} (d : Point N → Point N → ℝ) (n m : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ)) :
    Executes d constructCmd s (constructEval n m s) (constructCost n m) := by
  have hc (t : Store) : Executes d (opsCmd componentOps) t (componentInput t) 3 := by
    simpa [componentOps,componentInput,evalOps,Op.eval,setPtr] using ops_exec d componentOps t
  have hb (t : Store) : Executes d (opsCmd boundaryOps) t (boundaryInput t) 3 := by
    simpa [boundaryOps,boundaryInput,evalOps,Op.eval,setPtr] using ops_exec d boundaryOps t
  have hr (t : Store) : Executes d (opsCmd restoreOps) t (restored t) 3 := by
    simpa [restoreOps,restored,evalOps,Op.eval,setPtr] using ops_exec d restoreOps t
  have h5 : (boundaryInput (ComponentProgram.fullEval n m (componentInput s))).ptrs 5 = (m:ℤ) := by
    simp only [boundaryInput,setPtr,Function.update_of_ne (by decide : (5:ℕ) ≠ 17),
      Function.update_of_ne (by decide : (5:ℕ) ≠ 4),Function.update_of_ne (by decide : (5:ℕ) ≠ 3)]
    rw [ComponentProgram.fullEval_ptr_frame n m _ 5 (by omega)]
    simpa [componentInput,setPtr] using hm
  have h6 : (boundaryInput (ComponentProgram.fullEval n m (componentInput s))).ptrs 6 = (n:ℤ) := by
    simp only [boundaryInput,setPtr,Function.update_of_ne (by decide : (6:ℕ) ≠ 17),
      Function.update_of_ne (by decide : (6:ℕ) ≠ 4),Function.update_of_ne (by decide : (6:ℕ) ≠ 3)]
    rw [ComponentProgram.fullEval_ptr_frame n m _ 6 (by omega)]
    simpa [componentInput,setPtr] using hn
  have h := Executes.seq (hc s) (Executes.seq
    (ComponentProgram.full_exec d n m _ (by simpa [componentInput,setPtr] using hm)
      (by simpa [componentInput,setPtr] using hn))
    (Executes.seq (hb _) (Executes.seq (TightBoundaryProgram.full_exec d n m _ h5 h6) (hr _))))
  convert h using 1 <;> try rfl
  dsimp [constructCost]; omega
lemma construct_frame (n m : ℕ) (s : Store) : DataFrame s (constructEval n m s) :=
  (ComponentProgram.fullEval_frame n m (componentInput s)).trans
    (TightBoundaryProgram.fullEval_frame n m (boundaryInput (ComponentProgram.fullEval n m (componentInput s))))
lemma construct_high (n m : ℕ) (s : Store) (j : ℕ) (hj : 60 ≤ j ∨ (25 ≤ j ∧ j ≤ 59)) :
    (constructEval n m s).ptrs j = s.ptrs j := by
  have h3 : j ≠ 3 := by omega
  have h4 : j ≠ 4 := by omega
  have h17 : j ≠ 17 := by omega
  simp only [constructEval,restored,setPtr,Function.update_of_ne h3,Function.update_of_ne h4,Function.update_of_ne h17]
  rw [tight_high n m _ j (by omega)]
  simp only [boundaryInput,setPtr,Function.update_of_ne h3,Function.update_of_ne h4,Function.update_of_ne h17]
  rw [component_high n m _ j (by omega)]
  simp [componentInput,setPtr,h3,h4,h17]

def reject (s : Store) : Store := setPtr s 18 0
def rejectCmd : Cmd := .atom (.pointerConst 18 0)
def guardedCmd : Cmd := .ite (.pointerLE 60 0)
  (.ite (.pointerLE 59 58) constructCmd rejectCmd) rejectCmd
noncomputable def guardedEval (n m : ℕ) (s : Store) : Store :=
  if s.ptrs 60 ≤ s.ptrs 0 then
    if s.ptrs 59 ≤ s.ptrs 58 then constructEval n m s else reject s
  else reject s
def guardedCost (n m : ℕ) (s : Store) : ℕ :=
  if s.ptrs 60 ≤ s.ptrs 0 then
    if s.ptrs 59 ≤ s.ptrs 58 then 2+constructCost n m else 4
  else 3
lemma guarded_exec {N : ℕ} (d : Point N → Point N → ℝ) (n m : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ)) :
    Executes d guardedCmd s (guardedEval n m s) (guardedCost n m s) := by
  have hr (t : Store) : Executes d rejectCmd t (reject t) 1 := Executes.atom (.pointerConst 18 0) t
  unfold guardedCmd guardedEval guardedCost
  split_ifs with hseed hwidth
  · have hh := Executes.ite_true (c := .pointerLE 60 0) (no := rejectCmd) hseed
      (Executes.ite_true (c := .pointerLE 59 58) (no := rejectCmd) hwidth (construct_exec d n m s hm hn))
    convert hh using 1 <;> omega
  · exact Executes.ite_true (c := .pointerLE 60 0) hseed (Executes.ite_false (c := .pointerLE 59 58) hwidth (hr s))
  · exact Executes.ite_false (c := .pointerLE 60 0) hseed (hr s)
lemma guarded_bound (n m : ℕ) (s : Store) : guardedCost n m s ≤ 2+constructCost n m := by
  unfold guardedCost constructCost; split_ifs <;> omega

def fullCmd : Cmd := .seq prefixCmd guardedCmd
noncomputable def fullEval (n m : ℕ) (s : Store) : Store := guardedEval n m (prefixEval n s)
noncomputable def steps (n m : ℕ) (s : Store) : ℕ := 17*n+22+guardedCost n m (prefixEval n s)+1
noncomputable def program : MinSumFPT.Program := compile fullCmd 0
lemma full_exec {N : ℕ} (d : Point N → Point N → ℝ) (n m : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ)) :
    Executes d fullCmd s (fullEval n m s) (steps n m s-1) := by
  have h := Executes.seq (prefix_exec d n s hn) (guarded_exec d n m _
    (by rw [prefix_ptr n s 5 (by simp),hm]) (by rw [prefix_ptr n s 6 (by simp),hn]))
  convert h using 1 <;> first | rfl | (dsimp [steps]; omega)
lemma steps_bound (n m : ℕ) (s : Store) : steps n m s ≤ n*(17*m+43)+17*m+68 := by
  have h := guarded_bound n m (prefixEval n s)
  dsimp [steps,constructCost] at *; nlinarith
lemma program_length : program.length = 161 := by decide
lemma machine_execution {N : ℕ} (d : Point N → Point N → ℝ) (n m : ℕ) (s : Store)
    (hm : s.ptrs 5 = (m:ℤ)) (hn : s.ptrs 6 = (n:ℤ)) (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[steps n m s] (s.state 0 work) =
      (fullEval n m s).haltedState fullCmd.size (work+steps n m s) 0 := by
  have hp : 1 ≤ steps n m s := by dsimp [steps]; omega
  simpa only [program,Nat.sub_add_cancel hp,
    show work+(steps n m s-1)+1 = work+steps n m s by omega] using
      compile_halts (full_exec d n m s hm hn) ω work 0
end StableMSR.Recovery.Compiler.ComponentState
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical
namespace StableMSR.Recovery.Compiler.ComponentState
open ComponentMachine ComponentMemory

/- Input arrays and separate writable workspaces only. No component, boundary,
connectivity certificate or state-validity answer is an input. -/
structure Ready {n : ℕ} (S : Finset (Fin n)) (es : List (Fin n × Fin n))
    (seed : Fin n) (s : Store) : Prop where
  edges : s.ptrs 5 = (es.length:ℤ)
  vertices : s.ptrs 6 = (n:ℤ)
  seed_index : s.ptrs 57 = (seed.val:ℤ)
  separator : Bitmap s.imem (s.ptrs 53) S
  allowed : Bitmap s.imem (s.ptrs 54) Sᶜ
  encoding : EdgeEncoding s.imem (s.ptrs 2) es
  allowed_component : Separate (n := n) (s.ptrs 54) (s.ptrs 55)
  separator_component : Separate (n := n) (s.ptrs 53) (s.ptrs 55)
  separator_boundary : Separate (n := n) (s.ptrs 53) (s.ptrs 56)
  component_boundary : Separate (n := n) (s.ptrs 55) (s.ptrs 56)
  edges_component : EdgesSeparate (s.ptrs 2) (s.ptrs 55) es
  edges_boundary : EdgesSeparate (s.ptrs 2) (s.ptrs 56) es

lemma ready_component_input {n : ℕ} {S : Finset (Fin n)} {es : List (Fin n × Fin n)}
    {seed : Fin n} {s : Store} (h : Ready S es seed s) :
    GraphInput (componentInput s) Sᶜ es seed := by
  simpa [GraphInput,componentInput,setPtr] using
    And.intro h.edges (And.intro h.vertices (And.intro h.seed_index
      (And.intro h.allowed (And.intro h.encoding (And.intro h.allowed_component h.edges_component)))))

/- Construct a component and its boundary, then perform the tight-state test. -/
theorem construct_spec {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (h : Ready S es seed s) (hseed : seed ∉ S)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    let C := Havens.componentWithin G Sᶜ seed
    (constructEval n es.length s).ptrs 18 =
      (if S = BoundaryMemory.externalBoundary G C then 1 else 0) ∧
    Bitmap (constructEval n es.length s).imem (s.ptrs 55) C ∧
    Bitmap (constructEval n es.length s).imem (s.ptrs 56) (BoundaryMemory.externalBoundary G C) ∧
    (∀ x : ℤ, (∀ v : Fin n, x ≠ address (s.ptrs 55) v) →
      (∀ v : Fin n, x ≠ address (s.ptrs 56) v) →
      (constructEval n es.length s).imem x = s.imem x) := by
  dsimp only
  let a := componentInput s
  let c := ComponentProgram.fullEval n es.length a
  let b := boundaryInput c
  let C := Havens.componentWithin G Sᶜ seed
  have ha : GraphInput a Sᶜ es seed := ready_component_input h
  have hc := ComponentProgram.fullEval_component G Sᶜ es seed a ha
    (Finset.mem_compl.mpr hseed) hsound hcomplete
  have cp (j : ℕ) (hj : 24 < j) : c.ptrs j = s.ptrs j := by
    rw [show c.ptrs j = (ComponentProgram.fullEval n es.length a).ptrs j from rfl,
      component_high n es.length a j (by omega)]
    simp [a,componentInput,setPtr,show j ≠ 17 by omega,show j ≠ 4 by omega,show j ≠ 3 by omega]
  have cl (j : ℕ) (hj : j = 2 ∨ j = 5 ∨ j = 6) : c.ptrs j = s.ptrs j := by
    rcases hj with rfl|rfl|rfl <;>
      simp [c,ComponentProgram.fullEval_ptr_frame,a,componentInput,setPtr]
  have b3 : b.ptrs 3 = s.ptrs 55 := by simp [b,boundaryInput,setPtr,cp 55 (by omega)]
  have b4 : b.ptrs 4 = s.ptrs 56 := by simp [b,boundaryInput,setPtr,cp 56 (by omega)]
  have b17 : b.ptrs 17 = s.ptrs 53 := by simp [b,boundaryInput,setPtr,cp 53 (by omega)]
  have b2 : b.ptrs 2 = s.ptrs 2 := by simp [b,boundaryInput,setPtr,cl 2 (by simp)]
  have b6 : b.ptrs 6 = (n:ℤ) := by simp [b,boundaryInput,setPtr,cl 6 (by simp),h.vertices]
  have bm : b.imem = c.imem := rfl
  have hC : Bitmap b.imem (b.ptrs 3) C := by
    rw [b3,bm]
    simpa [c,C,a,componentInput,setPtr] using hc.2
  have hS : Bitmap b.imem (b.ptrs 17) S := by
    rw [b17,bm]
    intro v
    rw [ComponentProgram.fullEval_imem_frame Sᶜ es seed a ha]
    · exact h.separator v
    · simpa [a,componentInput,setPtr] using h.separator_component v
  have he : EdgeEncoding b.imem (b.ptrs 2) es := by
    rw [b2,bm]
    intro j hj
    rw [ComponentProgram.fullEval_imem_frame Sᶜ es seed a ha,
      ComponentProgram.fullEval_imem_frame Sᶜ es seed a ha]
    · exact h.encoding j hj
    · simpa [a,componentInput,setPtr] using fun v => (h.edges_component j hj v).2
    · simpa [a,componentInput,setPtr] using fun v => (h.edges_component j hj v).1
  have hCB : Separate (n := n) (b.ptrs 3) (b.ptrs 4) := by rw [b3,b4]; exact h.component_boundary
  have hSB : Separate (n := n) (b.ptrs 17) (b.ptrs 4) := by rw [b17,b4]; exact h.separator_boundary
  have hEB : EdgesSeparate (b.ptrs 2) (b.ptrs 4) es := by rw [b2,b4]; exact h.edges_boundary
  have hbflag := TightBoundaryProgram.fullEval_flag G C S es b b6 hC hS he hCB hSB hEB hsound hcomplete
  have hbbm := TightBoundaryProgram.fullEval_boundary_bitmap G C es b hC he hCB hEB hsound hcomplete
  refine ⟨hbflag,?_,?_,?_⟩
  · intro v
    change (TightBoundaryProgram.fullEval n es.length b).imem _ = _
    rw [TightBoundaryProgram.fullEval_imem_frame es b he hEB]
    · simpa [b3] using hC v
    · simpa [b4] using h.component_boundary v
  · intro v
    change (TightBoundaryProgram.fullEval n es.length b).imem _ = _
    simpa only [b4,BoundaryMemory.mem_externalBoundary] using hbbm v
  · intro x hxc hxb
    change (TightBoundaryProgram.fullEval n es.length b).imem x = _
    rw [TightBoundaryProgram.fullEval_imem_frame es b he hEB x (by simpa [b4] using hxb)]
    change c.imem x = _
    exact ComponentProgram.fullEval_imem_frame Sᶜ es seed a ha x
      (by simpa [a,componentInput,setPtr] using hxc)

/- Ordinary walk description for the actual component output. -/
noncomputable def outsideComponent {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (seed : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∉ S)
lemma component_eq_outside {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (seed : Fin n) :
    Havens.componentWithin G Sᶜ seed = outsideComponent G S seed := by
  ext v
  simp only [outsideComponent,Finset.mem_filter,Finset.mem_univ,true_and,Havens.mem_componentWithin]
  constructor
  · rintro ⟨hv,p,hp⟩
    exact ⟨p,fun z hz => Finset.mem_compl.mp (hp z hz)⟩
  · rintro ⟨p,hp⟩
    exact ⟨Finset.mem_compl.mpr (hp v p.end_mem_support),p,fun z hz => Finset.mem_compl.mpr (hp z hz)⟩

lemma prefix_ready {n : ℕ} (S : Finset (Fin n)) (es : List (Fin n × Fin n))
    (seed : Fin n) (s : Store)
    (hm : s.ptrs 5 = (es.length:ℤ)) (hn : s.ptrs 6 = (n:ℤ))
    (hi : s.ptrs 17 = (seed.val:ℤ)) (hS : Bitmap s.imem (s.ptrs 3) S)
    (he : EdgeEncoding s.imem (s.ptrs 2) es)
    (hSA : Separate (n := n) (s.ptrs 3) (s.ptrs 4))
    (hSC : Separate (n := n) (s.ptrs 3) (s.ptrs 50))
    (hSB : Separate (n := n) (s.ptrs 3) (s.ptrs 51))
    (hAC : Separate (n := n) (s.ptrs 4) (s.ptrs 50))
    (hCB : Separate (n := n) (s.ptrs 50) (s.ptrs 51))
    (hEA : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es)
    (hEC : EdgesSeparate (s.ptrs 2) (s.ptrs 50) es)
    (hEB : EdgesSeparate (s.ptrs 2) (s.ptrs 51) es) :
    Ready S es seed (prefixEval n s) := by
  obtain ⟨h53,h54,h55,h56,h57,h58,h59⟩ := prefix_saved n s
  constructor
  · rw [prefix_ptr n s 5 (by simp),hm]
  · rw [prefix_ptr n s 6 (by simp),hn]
  · rw [h57,hi]
  · rw [h53]; exact (prefix_bitmaps S s hS hSA).1
  · rw [h54]; exact (prefix_bitmaps S s hS hSA).2
  · rw [prefix_ptr n s 2 (by simp)]
    intro j hj
    rw [prefix_memory_frame n s _ (fun v => (hEA j hj v).1),
      prefix_memory_frame n s _ (fun v => (hEA j hj v).2)]
    exact he j hj
  · rw [h54,h55]; exact hAC
  · rw [h53,h55]; exact hSC
  · rw [h53,h56]; exact hSB
  · rw [h55,h56]; exact hCB
  · rw [prefix_ptr n s 2 (by simp),h55]; exact hEC
  · rw [prefix_ptr n s 2 (by simp),h56]; exact hEB
end StableMSR.Recovery.Compiler.ComponentState
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open scoped Classical
namespace StableMSR.Recovery.Compiler.ComponentState
open ComponentMachine ComponentMemory

structure Input {n : ℕ} (w : ℕ) (S : Finset (Fin n)) (es : List (Fin n × Fin n))
    (seed : Fin n) (s : Store) : Prop where
  edges : s.ptrs 5 = (es.length:ℤ)
  vertices : s.ptrs 6 = (n:ℤ)
  seed_index : s.ptrs 17 = (seed.val:ℤ)
  width : s.ptrs 43 = (w:ℤ)
  separator : Bitmap s.imem (s.ptrs 3) S
  encoding : EdgeEncoding s.imem (s.ptrs 2) es
  separator_allowed : Separate (n := n) (s.ptrs 3) (s.ptrs 4)
  separator_component : Separate (n := n) (s.ptrs 3) (s.ptrs 50)
  separator_boundary : Separate (n := n) (s.ptrs 3) (s.ptrs 51)
  allowed_component : Separate (n := n) (s.ptrs 4) (s.ptrs 50)
  component_boundary : Separate (n := n) (s.ptrs 50) (s.ptrs 51)
  edges_allowed : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es
  edges_component : EdgesSeparate (s.ptrs 2) (s.ptrs 50) es
  edges_boundary : EdgesSeparate (s.ptrs 2) (s.ptrs 51) es
lemma input_ready {n : ℕ} {w : ℕ} {S : Finset (Fin n)} {es : List (Fin n × Fin n)}
    {seed : Fin n} {s : Store} (h : Input w S es seed s) : Ready S es seed (prefixEval n s) :=
  prefix_ready S es seed s h.edges h.vertices h.seed_index h.separator h.encoding
    h.separator_allowed h.separator_component h.separator_boundary h.allowed_component
    h.component_boundary h.edges_allowed h.edges_component h.edges_boundary
lemma prefix_zero (n : ℕ) (s : Store) : (prefixEval n s).ptrs 0 = 0 := by
  simp [prefixEval,readSeed,setPtr,MaskComplement.ptr_frame,saved,
    BitmapStats.statsEval,BitmapStats.run_ptr_frame,BitmapStats.prepEval]
lemma prefix_conditions {n : ℕ} {w : ℕ} {S : Finset (Fin n)} {es : List (Fin n × Fin n)}
    {seed : Fin n} {s : Store} (h : Input w S es seed s) :
    ((prefixEval n s).ptrs 60 ≤ (prefixEval n s).ptrs 0 ↔ seed ∉ S) ∧
    ((prefixEval n s).ptrs 59 ≤ (prefixEval n s).ptrs 58 ↔ S.card ≤ w) := by
  rw [prefix_zero,prefix_seed S seed s h.separator h.seed_index h.separator_allowed,
    prefix_count S s h.vertices h.separator,(prefix_saved n s).2.2.2.2.2.1,h.width]
  constructor
  · by_cases hv : seed ∈ S <;> simp [hv]
  · exact_mod_cast Iff.rfl
lemma full_good {n : ℕ} {w : ℕ} {S : Finset (Fin n)} {es : List (Fin n × Fin n)}
    {seed : Fin n} {s : Store} (h : Input w S es seed s) (hs : seed ∉ S) (hw : S.card ≤ w) :
    fullEval n es.length s = constructEval n es.length (prefixEval n s) := by
  have hh := prefix_conditions h
  simp only [fullEval,guardedEval,if_pos (hh.1.mpr hs),if_pos (hh.2.mpr hw)]

lemma full_flag {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store) (h : Input w S es seed s)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    (fullEval n es.length s).ptrs 18 = if seed ∉ S ∧ S.card ≤ w ∧
      S = BoundaryMemory.externalBoundary G (outsideComponent G S seed) then 1 else 0 := by
  by_cases hs : seed ∉ S
  · by_cases hw : S.card ≤ w
    · rw [full_good h hs hw]
      have hc := (construct_spec G S es seed (prefixEval n s) (input_ready h) hs hsound hcomplete).1
      rw [component_eq_outside] at hc
      simpa [hs,hw] using hc
    · have hh := prefix_conditions h
      simp only [fullEval,guardedEval,if_pos (hh.1.mpr hs),if_neg (fun h' => hw (hh.2.mp h'))]
      simp [hw,reject,setPtr]
  · have hh := prefix_conditions h
    simp only [fullEval,guardedEval,if_neg (fun h' => hs (hh.1.mp h'))]
    simp [hs,reject,setPtr]

lemma full_bitmaps {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store) (h : Input w S es seed s)
    (hs : seed ∉ S) (hw : S.card ≤ w)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    Bitmap (fullEval n es.length s).imem (s.ptrs 50) (outsideComponent G S seed) ∧
    Bitmap (fullEval n es.length s).imem (s.ptrs 51)
      (BoundaryMemory.externalBoundary G (outsideComponent G S seed)) := by
  rw [full_good h hs hw]
  have hc := (construct_spec G S es seed (prefixEval n s) (input_ready h) hs hsound hcomplete).2
  rw [component_eq_outside,(prefix_saved n s).2.2.1,(prefix_saved n s).2.2.2.1] at hc
  exact ⟨hc.1,hc.2.1⟩
lemma full_memory_frame {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store) (h : Input w S es seed s)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (x : ℤ) (hA : ∀ v : Fin n, x ≠ address (s.ptrs 4) v)
    (hC : ∀ v : Fin n, x ≠ address (s.ptrs 50) v)
    (hB : ∀ v : Fin n, x ≠ address (s.ptrs 51) v) :
    (fullEval n es.length s).imem x = s.imem x := by
  by_cases hs : seed ∉ S
  · by_cases hw : S.card ≤ w
    · rw [full_good h hs hw]
      have hc := (construct_spec G S es seed (prefixEval n s) (input_ready h) hs hsound hcomplete).2.2.2
      rw [hc x (by simpa [(prefix_saved n s).2.2.1] using hC)
        (by simpa [(prefix_saved n s).2.2.2.1] using hB)]
      exact prefix_memory_frame n s x hA
    · have hh := prefix_conditions h
      simp only [fullEval,guardedEval,if_pos (hh.1.mpr hs),if_neg (fun h' => hw (hh.2.mp h'))]
      exact prefix_memory_frame n s x hA
  · have hh := prefix_conditions h
    simp only [fullEval,guardedEval,if_neg (fun h' => hs (hh.1.mp h'))]
    exact prefix_memory_frame n s x hA
lemma full_source {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store) (h : Input w S es seed s)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    Bitmap (fullEval n es.length s).imem (s.ptrs 3) S := by
  intro v
  rw [full_memory_frame G w S es seed s h hsound hcomplete _
    (h.separator_allowed v) (h.separator_component v) (h.separator_boundary v)]
  exact h.separator v
lemma full_frame (n m : ℕ) (s : Store) : DataFrame s (fullEval n m s) := by
  unfold fullEval guardedEval
  split_ifs <;> first
  | exact (prefix_frame n s).trans (construct_frame n m (prefixEval n s))
  | exact prefix_frame n s

lemma construct_restore (n m : ℕ) (s : Store) :
    (constructEval n m s).ptrs 3 = s.ptrs 53 ∧
    (constructEval n m s).ptrs 4 = s.ptrs 54 ∧
    (constructEval n m s).ptrs 17 = s.ptrs 57 := by
  simp [constructEval,restored,setPtr,tight_high,boundaryInput,component_high,componentInput]
lemma construct_ptr (n m : ℕ) (s : Store) (j : ℕ)
    (hj : j ∈ ([2,5,6,43,50,51]:List ℕ)) : (constructEval n m s).ptrs j = s.ptrs j := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [constructEval,restored,setPtr,TightBoundaryProgram.fullEval_ptr_frame,tight_high,
      boundaryInput,ComponentProgram.fullEval_ptr_frame,component_high,componentInput]
lemma full_ptr (n m : ℕ) (s : Store) (j : ℕ)
    (hj : j ∈ ([2,3,4,5,6,17,43,50,51]:List ℕ)) : (fullEval n m s).ptrs j = s.ptrs j := by
  have hp := prefix_ptr n s j hj
  have h18 : j ≠ 18 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    omega
  unfold fullEval guardedEval
  split_ifs <;> try (simpa [reject,setPtr,h18] using hp)
  by_cases h3 : j = 3
  · subst j; rw [(construct_restore n m _).1,(prefix_saved n s).1]
  by_cases h4 : j = 4
  · subst j; rw [(construct_restore n m _).2.1,(prefix_saved n s).2.1]
  by_cases h17 : j = 17
  · subst j; rw [(construct_restore n m _).2.2,(prefix_saved n s).2.2.2.2.1]
  rw [construct_ptr n m _ j (by simp_all),hp]

/- One fixed program constructs a deletion component and decides its exact
boundary and width conditions, without any precomputed component or boundary. -/
end StableMSR.Recovery.Compiler.ComponentState
/- Verified table construction and updates: ArrayCopy.lean -/
set_option autoImplicit false

namespace StableMSR.Recovery.Compiler.ArrayCopy
open ComponentMachine

/- Copy one integer cell and advance both cursors and the loop counter. -/
def bodyOps : List Op :=
  [.integerLoad 38 34, .integerStore 35 38, .pointerInc 34,
   .pointerInc 35, .pointerInc 37]
def body : Cmd := opsCmd bodyOps

def copyOne (s : Store) : Store :=
  { s with
    imem := Function.update s.imem (s.ptrs 35) (s.imem (s.ptrs 34))
    ptrs := Function.update (Function.update (Function.update (Function.update s.ptrs
      38 (s.imem (s.ptrs 34))) 34 (s.ptrs 34+1)) 35 (s.ptrs 35+1)) 37 (s.ptrs 37+1) }

def run : ℕ → Store → Store
  | 0, s => s
  | q+1, s => run q (copyOne s)

lemma body_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d body s (copyOne s) 5 := by
  simpa [body,bodyOps,evalOps,Op.eval,copyOne,Function.update_comm,
    Function.update_idem] using ops_exec d bodyOps s

@[simp] lemma copyOne_src (s : Store) : (copyOne s).ptrs 34 = s.ptrs 34+1 := by
  simp [copyOne]
@[simp] lemma copyOne_dst (s : Store) : (copyOne s).ptrs 35 = s.ptrs 35+1 := by
  simp [copyOne]
@[simp] lemma copyOne_index (s : Store) : (copyOne s).ptrs 37 = s.ptrs 37+1 := by
  simp [copyOne]
lemma copyOne_ptr_frame (s : Store) (j : ℕ)
    (h34 : j ≠ 34) (h35 : j ≠ 35) (h37 : j ≠ 37) (h38 : j ≠ 38) :
    (copyOne s).ptrs j = s.ptrs j := by simp [copyOne,h34,h35,h37,h38]
lemma copyOne_frame (s : Store) : DataFrame s (copyOne s) := ⟨rfl,rfl,rfl,rfl,rfl⟩

lemma run_src (q : ℕ) (s : Store) : (run q s).ptrs 34 = s.ptrs 34+(q:ℤ) := by
  induction q generalizing s with
  | zero => simp [run]
  | succ q ih => rw [run,ih,copyOne_src]; push_cast; ring
lemma run_dst (q : ℕ) (s : Store) : (run q s).ptrs 35 = s.ptrs 35+(q:ℤ) := by
  induction q generalizing s with
  | zero => simp [run]
  | succ q ih => rw [run,ih,copyOne_dst]; push_cast; ring
lemma run_ptr_frame (q : ℕ) (s : Store) (j : ℕ)
    (h34 : j ≠ 34) (h35 : j ≠ 35) (h37 : j ≠ 37) (h38 : j ≠ 38) :
    (run q s).ptrs j = s.ptrs j := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih => rw [run,ih,copyOne_ptr_frame s j h34 h35 h37 h38]
lemma run_frame (q : ℕ) (s : Store) : DataFrame s (run q s) := by
  induction q generalizing s with
  | zero => exact DataFrame.refl _
  | succ q ih => exact (copyOne_frame s).trans (ih (copyOne s))

/- The final memory outside the destination interval is unchanged. -/
lemma run_memory_frame (q : ℕ) (s : Store) (x : ℤ)
    (hx : x < s.ptrs 35 ∨ s.ptrs 35+(q:ℤ) ≤ x) :
    (run q s).imem x = s.imem x := by
  induction q generalizing s with
  | zero => rfl
  | succ q ih =>
    have hnext : x < (copyOne s).ptrs 35 ∨
        (copyOne s).ptrs 35+(q:ℤ) ≤ x := by rw [copyOne_dst]; push_cast at hx; omega
    rw [run,ih (copyOne s) hnext]
    have hne : x ≠ s.ptrs 35 := by push_cast at hx; omega
    exact Function.update_of_ne hne _ _

/- Disjoint source and destination intervals give snapshot-copy semantics. -/
lemma run_memory_get (q : ℕ) (s : Store)
    (hsep : ∀ i j : Fin q, s.ptrs 34+(i.val:ℤ) ≠ s.ptrs 35+(j.val:ℤ))
    (i : Fin q) :
    (run q s).imem (s.ptrs 35+(i.val:ℤ)) = s.imem (s.ptrs 34+(i.val:ℤ)) := by
  induction q generalizing s with
  | zero => exact Fin.elim0 i
  | succ q ih =>
    have hn : (s.ptrs 34) ≠ s.ptrs 35 := by
      simpa using hsep ⟨0,by omega⟩ ⟨0,by omega⟩
    by_cases hi : i.val = 0
    · have hx : s.ptrs 35 < (copyOne s).ptrs 35 := by simp
      have hf := run_memory_frame q (copyOne s) (s.ptrs 35) (Or.inl hx)
      simpa [run,hi,copyOne] using hf
    · let j : Fin q := ⟨i.val-1,by omega⟩
      have he : (copyOne s).ptrs 35+(j.val:ℤ) = s.ptrs 35+(i.val:ℤ) := by
        simp only [copyOne_dst]; dsimp [j]; omega
      have hs : ∀ a b : Fin q,
          (copyOne s).ptrs 34+(a.val:ℤ) ≠ (copyOne s).ptrs 35+(b.val:ℤ) := by
        intro a b
        simpa only [copyOne_src,copyOne_dst,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm]
          using hsep ⟨a.val+1,by omega⟩ ⟨b.val+1,by omega⟩
      have h := ih (copyOne s) hs j
      rw [he] at h
      have haddr : (copyOne s).ptrs 34+(j.val:ℤ) = s.ptrs 34+(i.val:ℤ) := by
        rw [copyOne_src]; dsimp [j]; omega
      rw [haddr] at h
      have hne : s.ptrs 34+(i.val:ℤ) ≠ s.ptrs 35 := by
        simpa using hsep i ⟨0,by omega⟩
      simpa only [run,copyOne,Function.update_of_ne hne] using h

def setupOps : List Op :=
  [.pointerCopy 34 3, .pointerCopy 35 4, .pointerCopy 36 6,
   .pointerDec 36, .pointerConst 37 0]
def setup (s : Store) : Store :=
  setPtr (setPtr (setPtr (setPtr s 34 (s.ptrs 3)) 35 (s.ptrs 4))
    36 (s.ptrs 6-1)) 37 0

def copyCmd : Cmd := .seq (opsCmd setupOps) (.whileDo (.pointerLE 37 36) body)
def copyEval (q : ℕ) (s : Store) : Store := run q (setup s)

lemma setup_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d (opsCmd setupOps) s (setup s) 5 := by
  simpa [setupOps,evalOps,Op.eval,setup,setPtr,Function.update_idem] using
    ops_exec d setupOps s

lemma copy_exec {N : ℕ} (d : Point N → Point N → ℝ) (q : ℕ) (s : Store)
    (hq : s.ptrs 6 = (q:ℤ)) :
    Executes d copyCmd s (copyEval q s) (7*q+7) := by
  have loop : ∀ (r : ℕ) (t : Store), t.ptrs 37+(r:ℤ)-1 = t.ptrs 36 →
      Executes d (.whileDo (.pointerLE 37 36) body) t (run r t) (7*r+2) := by
    intro r
    induction r with
    | zero =>
      intro t ht
      apply Executes.while_false
      simp only [Cond.test]; omega
    | succ r ih =>
      intro t ht
      have hg : (Cond.pointerLE 37 36).test t := by simp only [Cond.test]; omega
      have hr := ih (copyOne t) (by
        rw [copyOne_index,copyOne_ptr_frame t 36 (by decide) (by decide) (by decide) (by decide)]
        push_cast at ht; omega)
      have h := Executes.while_true hg (body_exec d t) hr
      simpa only [run,show 1+5+1+(7*r+2)=7*(r+1)+2 by omega] using h
  have hl := loop q (setup s) (by simp [setup,setPtr,hq])
  convert Executes.seq (setup_exec d s) hl using 1 <;> try rfl
  omega

lemma copy_ptr_frame (q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([34,35,36,37,38] : List ℕ)) : (copyEval q s).ptrs j = s.ptrs j := by
  have h34 : j ≠ 34 := by simp_all
  have h35 : j ≠ 35 := by simp_all
  have h36 : j ≠ 36 := by simp_all
  have h37 : j ≠ 37 := by simp_all
  have h38 : j ≠ 38 := by simp_all
  rw [copyEval,run_ptr_frame q (setup s) j h34 h35 h37 h38]
  simp [setup,setPtr,h34,h35,h36,h37]
lemma copy_frame (q : ℕ) (s : Store) : DataFrame s (copyEval q s) :=
  (show DataFrame s (setup s) from ⟨rfl,rfl,rfl,rfl,rfl⟩).trans (run_frame q (setup s))
lemma copy_dst (q : ℕ) (s : Store) : (copyEval q s).ptrs 35 = s.ptrs 4+(q:ℤ) := by
  rw [copyEval,run_dst]; simp [setup,setPtr]
lemma copy_memory_frame (q : ℕ) (s : Store) (x : ℤ)
    (hx : x < s.ptrs 4 ∨ s.ptrs 4+(q:ℤ) ≤ x) :
    (copyEval q s).imem x = s.imem x := by
  exact run_memory_frame q (setup s) x (by simpa [setup,setPtr] using hx)
lemma copy_memory_get (q : ℕ) (s : Store)
    (hsep : ∀ i j : Fin q, s.ptrs 3+(i.val:ℤ) ≠ s.ptrs 4+(j.val:ℤ))
    (i : Fin q) : (copyEval q s).imem (s.ptrs 4+(i.val:ℤ)) =
      s.imem (s.ptrs 3+(i.val:ℤ)) := by
  exact run_memory_get q (setup s) (by simpa [setup,setPtr] using hsep) i

lemma copyCmd_size : copyCmd.size = 13 := by decide

end StableMSR.Recovery.Compiler.ArrayCopy


/- Verified table construction and updates: TableAppend.lean -/
set_option autoImplicit false

namespace StableMSR.Recovery.Compiler.TableAppend
open ComponentMachine ArrayCopy

/- Locate the first free record using only additions, before copying its key. -/
def seekOps : List Op :=
  [.pointerCopy 4 2, .pointerCopy 39 6, .pointerInc 39,
   .pointerCopy 40 5, .pointerDec 40, .pointerConst 41 0]
def seekSetup (s : Store) : Store :=
  setPtr (setPtr (setPtr (setPtr s 4 (s.ptrs 2)) 39 (s.ptrs 6+1))
    40 (s.ptrs 5-1)) 41 0

def seekBody : Cmd := opsCmd [.pointerAdd 4 4 39, .pointerInc 41]
def seekStep (s : Store) : Store :=
  setPtr (setPtr s 4 (s.ptrs 4+s.ptrs 39)) 41 (s.ptrs 41+1)
def seekCmd : Cmd := .seq (opsCmd seekOps) (.whileDo (.pointerLE 41 40) seekBody)
def seekEval (q : ℕ) (s : Store) : Store := seekStep^[q] (seekSetup s)

lemma seek_body_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d seekBody s (seekStep s) 2 := by
  simpa [seekBody,seekStep,evalOps,Op.eval,setPtr] using
    ops_exec d [.pointerAdd 4 4 39, .pointerInc 41] s
lemma seekStep_ptr_frame (s : Store) (j : ℕ) (h4 : j ≠ 4) (h41 : j ≠ 41) :
    (seekStep s).ptrs j = s.ptrs j := by simp [seekStep,setPtr,h4,h41]
lemma seekStep_index (s : Store) : (seekStep s).ptrs 41 = s.ptrs 41+1 := by
  simp [seekStep,setPtr]
lemma seekStep_cursor (q : ℕ) (s : Store) :
    (seekStep^[q] s).ptrs 4 = s.ptrs 4+(q:ℤ)*s.ptrs 39 := by
  induction q generalizing s with
  | zero => simp
  | succ q ih =>
    rw [Function.iterate_succ_apply,ih]
    simp [seekStep,setPtr,Nat.cast_add,Nat.cast_one]; ring
lemma seek_cursor (q : ℕ) (s : Store) :
    (seekEval q s).ptrs 4 = s.ptrs 2+(q:ℤ)*(s.ptrs 6+1) := by
  rw [seekEval,seekStep_cursor]; simp [seekSetup,setPtr]
lemma seek_ptr_frame (q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([4,39,40,41] : List ℕ)) : (seekEval q s).ptrs j = s.ptrs j := by
  have h4 : j ≠ 4 := by simp_all
  have h39 : j ≠ 39 := by simp_all
  have h40 : j ≠ 40 := by simp_all
  have h41 : j ≠ 41 := by simp_all
  rw [seekEval,iterate_preserves _ (fun t => t.ptrs j)
    (fun t => seekStep_ptr_frame t j h4 h41)]
  simp [seekSetup,setPtr,h4,h39,h40,h41]
lemma seek_imem (q : ℕ) (s : Store) : (seekEval q s).imem = s.imem := by
  exact iterate_preserves seekStep Store.imem (fun _ => rfl) q (seekSetup s)
lemma seek_frame (q : ℕ) (s : Store) : DataFrame s (seekEval q s) :=
  (show DataFrame s (seekSetup s) from ⟨rfl,rfl,rfl,rfl,rfl⟩).trans
    (iterate_frame seekStep (fun _ => ⟨rfl,rfl,rfl,rfl,rfl⟩) q (seekSetup s))

lemma seek_exec {N : ℕ} (d : Point N → Point N → ℝ) (q : ℕ) (s : Store)
    (hq : s.ptrs 5 = (q:ℤ)) :
    Executes d seekCmd s (seekEval q s) (4*q+8) := by
  have hs : Executes d (opsCmd seekOps) s (seekSetup s) 6 := by
    simpa [seekOps,evalOps,Op.eval,seekSetup,setPtr,Function.update_idem] using
      ops_exec d seekOps s
  have hl := fixed_loop_exec d seekBody seekStep 41 40 2 (s.ptrs 5-1)
    (fun t _ => seek_body_exec d t) seekStep_index
    (fun t => seekStep_ptr_frame t 40 (by decide) (by decide)) q (seekSetup s)
    (by simp [seekSetup,setPtr]) (by simp [seekSetup,setPtr,hq])
  convert Executes.seq hs hl using 1 <;> try rfl
  omega

/- Append a payload after the newly copied key and increment the row count. -/
def finishCmd : Cmd := opsCmd [.integerStore 35 17, .pointerInc 5]
def finish (s : Store) : Store :=
  { s with
    imem := Function.update s.imem (s.ptrs 35) (s.ptrs 17)
    ptrs := Function.update s.ptrs 5 (s.ptrs 5+1) }
def appendCmd : Cmd := .seq seekCmd (.seq copyCmd finishCmd)
def appendEval (q L : ℕ) (s : Store) : Store := finish (copyEval L (seekEval q s))

lemma finish_exec {N : ℕ} (d : Point N → Point N → ℝ) (s : Store) :
    Executes d finishCmd s (finish s) 2 := by
  simpa [finishCmd,finish,evalOps,Op.eval] using
    ops_exec d [.integerStore 35 17,.pointerInc 5] s
lemma append_exec {N : ℕ} (d : Point N → Point N → ℝ) (q L : ℕ) (s : Store)
    (hq : s.ptrs 5 = (q:ℤ)) (hL : s.ptrs 6 = (L:ℤ)) :
    Executes d appendCmd s (appendEval q L s) (4*q+7*L+17) := by
  have hL' : (seekEval q s).ptrs 6 = (L:ℤ) := by
    rw [seek_ptr_frame q s 6 (by simp),hL]
  have h := Executes.seq (seek_exec d q s hq)
    (Executes.seq (copy_exec d L (seekEval q s) hL') (finish_exec d _))
  convert h using 1 <;> try rfl
  omega

/- The start of record q for width L, a proof-side address abbreviation. -/
def endAddress (q L : ℕ) (s : Store) : ℤ := s.ptrs 2+(q:ℤ)*((L:ℤ)+1)
lemma copy_cursor (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ)) :
    (copyEval L (seekEval q s)).ptrs 35 = endAddress q L s+(L:ℤ) := by
  rw [copy_dst,seek_cursor,hL]; rfl
lemma append_memory (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ)) :
    (appendEval q L s).imem =
      Function.update (copyEval L (seekEval q s)).imem
        (endAddress q L s+(L:ℤ)) (s.ptrs 17) := by
  rw [appendEval,finish,copy_cursor q L s hL,
    copy_ptr_frame L (seekEval q s) 17 (by simp),seek_ptr_frame q s 17 (by simp)]
lemma append_ptr_frame (q L : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([4,5,34,35,36,37,38,39,40,41] : List ℕ)) :
    (appendEval q L s).ptrs j = s.ptrs j := by
  have h5 : j ≠ 5 := by simp_all
  change Function.update (copyEval L (seekEval q s)).ptrs 5 _ j = _
  rw [Function.update_of_ne h5,copy_ptr_frame,seek_ptr_frame] <;> simp_all
lemma append_count (q L : ℕ) (s : Store) :
    (appendEval q L s).ptrs 5 = s.ptrs 5+1 := by
  change (copyEval L (seekEval q s)).ptrs 5+1 = s.ptrs 5+1
  rw [copy_ptr_frame L (seekEval q s) 5 (by simp),seek_ptr_frame q s 5 (by simp)]
lemma append_frame (q L : ℕ) (s : Store) : DataFrame s (appendEval q L s) :=
  ((seek_frame q s).trans (copy_frame L (seekEval q s))).trans
    (show DataFrame (copyEval L (seekEval q s)) (finish (copyEval L (seekEval q s)))
      from ⟨rfl,rfl,rfl,rfl,rfl⟩)

lemma append_memory_frame (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ))
    (x : ℤ) (hx : x < endAddress q L s ∨ endAddress q L s+(L:ℤ)+1 ≤ x) :
    (appendEval q L s).imem x = s.imem x := by
  rw [append_memory q L s hL,Function.update_of_ne (show x ≠ endAddress q L s+(L:ℤ) by omega)]
  rw [copy_memory_frame L (seekEval q s) x,seek_imem]
  rw [seek_cursor,hL]
  change x < endAddress q L s ∨ endAddress q L s+(L:ℤ) ≤ x
  omega

lemma outside_interval (base x : ℤ) (L : ℕ)
    (h : ∀ i : Fin L, x ≠ base+(i.val:ℤ)) : x < base ∨ base+(L:ℤ) ≤ x := by
  by_contra hn
  have hnonneg : 0 ≤ x-base := by omega
  have hlt : (x-base).toNat < L := by omega
  exact h ⟨(x-base).toNat,hlt⟩ (by simp only [Int.toNat_of_nonneg hnonneg]; omega)

lemma append_key (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ))
    (hsep : ∀ i : Fin L, ∀ j : Fin (L+1),
      s.ptrs 3+(i.val:ℤ) ≠ endAddress q L s+(j.val:ℤ)) (i : Fin L) :
    (appendEval q L s).imem (endAddress q L s+(i.val:ℤ)) =
      s.imem (s.ptrs 3+(i.val:ℤ)) := by
  rw [append_memory q L s hL]
  have hne : endAddress q L s+(i.val:ℤ) ≠ endAddress q L s+(L:ℤ) := by
    have := i.isLt; omega
  rw [Function.update_of_ne hne]
  have hc := copy_memory_get L (seekEval q s) (by
    intro a b
    rw [seek_ptr_frame q s 3 (by simp),seek_cursor,hL]
    exact hsep a ⟨b.val,by omega⟩) i
  simpa only [seek_ptr_frame q s 3 (by simp),seek_cursor,hL,seek_imem,endAddress] using hc
lemma append_payload (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ)) :
    (appendEval q L s).imem (endAddress q L s+(L:ℤ)) = s.ptrs 17 := by
  rw [append_memory q L s hL]; simp
lemma append_query (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ))
    (hsep : ∀ i : Fin L, ∀ j : Fin (L+1),
      s.ptrs 3+(i.val:ℤ) ≠ endAddress q L s+(j.val:ℤ)) (i : Fin L) :
    (appendEval q L s).imem (s.ptrs 3+(i.val:ℤ)) =
      s.imem (s.ptrs 3+(i.val:ℤ)) := by
  apply append_memory_frame q L s hL
  have h := outside_interval (endAddress q L s) (s.ptrs 3+(i.val:ℤ)) (L+1) (hsep i)
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using h

lemma append_old_record (q L : ℕ) (s : Store) (hL : s.ptrs 6 = (L:ℤ))
    (i : Fin q) (j : Fin (L+1)) :
    (appendEval q L s).imem
      (s.ptrs 2+(i.val:ℤ)*((L:ℤ)+1)+(j.val:ℤ)) =
      s.imem (s.ptrs 2+(i.val:ℤ)*((L:ℤ)+1)+(j.val:ℤ)) := by
  apply append_memory_frame q L s hL
  left
  have hi : (i.val:ℤ)+1 ≤ (q:ℤ) := by have := i.isLt; omega
  have hj : (j.val:ℤ) < (L:ℤ)+1 := by have := j.isLt; omega
  have hp : 0 < (L:ℤ)+1 := by omega
  dsimp [endAddress]
  nlinarith

lemma appendCmd_size : appendCmd.size = 26 := by decide
noncomputable def program : MinSumFPT.Program := compile appendCmd 0
lemma program_length : program.length = 27 := by
  simp [program,compile,compileAt_length,appendCmd_size]
lemma append_machine_execution {N : ℕ} (d : Point N → Point N → ℝ)
    (q L : ℕ) (s : Store) (hq : s.ptrs 5 = (q:ℤ)) (hL : s.ptrs 6 = (L:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[4*q+7*L+18] (s.state 0 work) =
      (appendEval q L s).haltedState 26 (work+(4*q+7*L+18)) 0 := by
  simpa [program,appendCmd_size,Nat.add_assoc] using
    compile_halts (append_exec d q L s hq hL) ω work 0

end StableMSR.Recovery.Compiler.TableAppend


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace StableMSR.Recovery.Compiler.PairRecord
open ComponentMachine

/- Copy both state-key halves directly into the new record, without an
intermediate concatenated key or a precomputed output record. -/
def saveOps : List Op := [.pointerCopy 65 6,.pointerCopy 67 3,.pointerCopy 68 4,.pointerAdd 6 6 6]
def saved (s : Store) : Store :=
  setPtr (setPtr (setPtr (setPtr s 65 (s.ptrs 6)) 67 (s.ptrs 3)) 68 (s.ptrs 4)) 6 (s.ptrs 6+s.ptrs 6)
def narrowCmd : Cmd := .atom (.pointerCopy 6 65)
def narrow (s : Store) : Store := setPtr s 6 (s.ptrs 65)
def secondOps : List Op := [.pointerCopy 3 50,.pointerCopy 4 35]
def second (s : Store) : Store := setPtr (setPtr s 3 (s.ptrs 50)) 4 (s.ptrs 35)
def restoreOps : List Op := [.pointerCopy 3 67,.pointerCopy 4 68]
def restored (s : Store) : Store := setPtr (setPtr s 3 (s.ptrs 67)) 4 (s.ptrs 68)
def command : Cmd := .seq (opsCmd saveOps) (.seq TableAppend.seekCmd (.seq narrowCmd
  (.seq ArrayCopy.copyCmd (.seq (opsCmd secondOps) (.seq ArrayCopy.copyCmd
    (.seq TableAppend.finishCmd (opsCmd restoreOps)))))))
def firstStore (n q : ℕ) (s : Store) : Store :=
  ArrayCopy.copyEval n (narrow (TableAppend.seekEval q (saved s)))
def secondStore (n q : ℕ) (s : Store) : Store := ArrayCopy.copyEval n (second (firstStore n q s))
def eval (n q : ℕ) (s : Store) : Store := restored (TableAppend.finish (secondStore n q s))
def rowBase (n q : ℕ) (s : Store) : ℤ := s.ptrs 2+(q:ℤ)*((n:ℤ)+(n:ℤ)+1)

lemma first_ptr (n q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([4,34,35,36,37,38,39,40,41,65,67,68]:List ℕ)) :
    (firstStore n q s).ptrs j = s.ptrs j := by
  have h6 : (narrow (TableAppend.seekEval q (saved s))).ptrs j = s.ptrs j := by
    by_cases he : j = 6
    · subst j
      simp [narrow,setPtr,TableAppend.seek_ptr_frame,saved]
    · simp only [narrow,setPtr,Function.update_of_ne he]
      rw [TableAppend.seek_ptr_frame q (saved s) j (by simp_all)]
      simp_all [saved,setPtr]
  rw [firstStore,ArrayCopy.copy_ptr_frame n _ j (by simp_all),h6]
lemma first_memory (n q : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ)) (v : Fin n)
    (hsep : ∀ i : Fin n, ∀ j : Fin (n+n+1),
      s.ptrs 3+(i.val:ℤ) ≠ rowBase n q s+(j.val:ℤ)) :
    (firstStore n q s).imem (rowBase n q s+(v.val:ℤ)) = s.imem (s.ptrs 3+(v.val:ℤ)) := by
  have ht : (narrow (TableAppend.seekEval q (saved s))).ptrs 4 = rowBase n q s := by
    simp [narrow,setPtr,TableAppend.seek_cursor,saved,hn,rowBase]
  have hs : (narrow (TableAppend.seekEval q (saved s))).ptrs 3 = s.ptrs 3 := by
    simp [narrow,setPtr,TableAppend.seek_ptr_frame,saved]
  have hm : (narrow (TableAppend.seekEval q (saved s))).imem = s.imem := TableAppend.seek_imem q (saved s)
  have h := ArrayCopy.copy_memory_get n (narrow (TableAppend.seekEval q (saved s)))
    (by intro i j; rw [hs,ht]; exact hsep i ⟨j.val,by have := j.isLt; omega⟩) v
  simpa only [firstStore,hs,ht,hm] using h
lemma first_frame (n q : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ)) (x : ℤ)
    (hx : x < rowBase n q s ∨ rowBase n q s+(n:ℤ) ≤ x) :
    (firstStore n q s).imem x = s.imem x := by
  rw [firstStore,ArrayCopy.copy_memory_frame n _ x]
  · exact congrFun (TableAppend.seek_imem q (saved s)) x
  · simpa [narrow,setPtr,TableAppend.seek_cursor,saved,hn,rowBase] using hx
lemma first_cursor (n q : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ)) :
    (firstStore n q s).ptrs 35 = rowBase n q s+(n:ℤ) := by
  rw [firstStore,ArrayCopy.copy_dst]
  simp [narrow,setPtr,TableAppend.seek_cursor,saved,hn,rowBase]

lemma exec {N : ℕ} (d : Point N → Point N → ℝ) (n q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hq : s.ptrs 5 = (q:ℤ)) :
    Executes d command s (eval n q s) (4*q+14*n+33) := by
  have hsave : Executes d (opsCmd saveOps) s (saved s) 4 := by
    simpa [saveOps,saved,evalOps,Op.eval,setPtr] using ops_exec d saveOps s
  have hq' : (saved s).ptrs 5 = (q:ℤ) := by simpa [saved,setPtr] using hq
  have hn' : (narrow (TableAppend.seekEval q (saved s))).ptrs 6 = (n:ℤ) := by
    simp [narrow,setPtr,TableAppend.seek_ptr_frame,saved,hn]
  have hsecond : Executes d (opsCmd secondOps) (firstStore n q s) (second (firstStore n q s)) 2 := by
    simpa [secondOps,second,evalOps,Op.eval,setPtr] using ops_exec d secondOps (firstStore n q s)
  have hn'' : (second (firstStore n q s)).ptrs 6 = (n:ℤ) := by
    simp [second,setPtr,first_ptr n q s 6 (by simp),hn]
  have hrestore : Executes d (opsCmd restoreOps) (TableAppend.finish (secondStore n q s)) (eval n q s) 2 := by
    simpa [restoreOps,restored,eval,evalOps,Op.eval,setPtr] using ops_exec d restoreOps (TableAppend.finish (secondStore n q s))
  have h := Executes.seq hsave (Executes.seq (TableAppend.seek_exec d q (saved s) hq')
    (Executes.seq (Executes.atom (.pointerCopy 6 65) _) (Executes.seq (ArrayCopy.copy_exec d n _ hn')
      (Executes.seq hsecond (Executes.seq (ArrayCopy.copy_exec d n _ hn'')
        (Executes.seq (TableAppend.finish_exec d _) hrestore))))))
  convert h using 1 <;> try rfl
  omega
lemma ptr_frame (n q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([5,34,35,36,37,38,39,40,41,65,67,68]:List ℕ)) :
    (eval n q s).ptrs j = s.ptrs j := by
  have hf (k : ℕ) (hk : k ∈ ([2,3,4,6,17,50]:List ℕ)) :
      (eval n q s).ptrs k = s.ptrs k := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [eval,restored,setPtr,TableAppend.finish,secondStore,ArrayCopy.copy_ptr_frame,
        second,firstStore,ArrayCopy.copy_ptr_frame,narrow,TableAppend.seek_ptr_frame,saved]
  by_cases h3 : j = 3
  · subst j; exact hf 3 (by simp)
  by_cases h4 : j = 4
  · subst j; exact hf 4 (by simp)
  by_cases h6 : j = 6
  · subst j; exact hf 6 (by simp)
  simp only [eval,restored,setPtr,Function.update_of_ne h3,Function.update_of_ne h4]
  have h5 : j ≠ 5 := by simp_all
  simp only [TableAppend.finish,Function.update_of_ne h5,secondStore]
  rw [ArrayCopy.copy_ptr_frame n _ j (by simp_all)]
  simp only [second,setPtr,Function.update_of_ne h3,Function.update_of_ne h4]
  exact first_ptr n q s j (by simp_all)
lemma count (n q : ℕ) (s : Store) : (eval n q s).ptrs 5 = s.ptrs 5+1 := by
  simp [eval,restored,setPtr,TableAppend.finish,secondStore,ArrayCopy.copy_ptr_frame,
    second,first_ptr n q s 5 (by simp)]
lemma frame (n q : ℕ) (s : Store) : DataFrame s (eval n q s) :=
  ((TableAppend.seek_frame q (saved s)).trans
    (ArrayCopy.copy_frame n (narrow (TableAppend.seekEval q (saved s))))).trans
      (ArrayCopy.copy_frame n (second (firstStore n q s)))
lemma memory_frame (n q : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ)) (x : ℤ)
    (hx : x < rowBase n q s ∨ rowBase n q s+(n:ℤ)+(n:ℤ)+1 ≤ x) :
    (eval n q s).imem x = s.imem x := by
  change Function.update (secondStore n q s).imem ((secondStore n q s).ptrs 35) _ x = _
  have hcursor : (secondStore n q s).ptrs 35 = rowBase n q s+(n:ℤ)+(n:ℤ) := by
    rw [secondStore,ArrayCopy.copy_dst]; simp [second,setPtr,first_cursor n q s hn]
  rw [hcursor,Function.update_of_ne (by omega : x ≠ rowBase n q s+(n:ℤ)+(n:ℤ))]
  rw [secondStore,ArrayCopy.copy_memory_frame n _ x]
  · exact first_frame n q s hn x (by omega)
  · simp only [second,setPtr,Function.update_self,first_cursor n q s hn]; omega

lemma values (n q : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ))
    (hS : ∀ i : Fin n, ∀ j : Fin (n+n+1), s.ptrs 3+(i.val:ℤ) ≠ rowBase n q s+(j.val:ℤ))
    (hC : ∀ i : Fin n, ∀ j : Fin (n+n+1), s.ptrs 50+(i.val:ℤ) ≠ rowBase n q s+(j.val:ℤ)) :
    (∀ v : Fin n, (eval n q s).imem (rowBase n q s+(v.val:ℤ)) = s.imem (s.ptrs 3+(v.val:ℤ))) ∧
    (∀ v : Fin n, (eval n q s).imem (rowBase n q s+(n:ℤ)+(v.val:ℤ)) = s.imem (s.ptrs 50+(v.val:ℤ))) ∧
    (eval n q s).imem (rowBase n q s+(n:ℤ)+(n:ℤ)) = s.ptrs 17 := by
  have hc : (secondStore n q s).ptrs 35 = rowBase n q s+(n:ℤ)+(n:ℤ) := by
    rw [secondStore,ArrayCopy.copy_dst]; simp [second,setPtr,first_cursor n q s hn]
  have hm : (eval n q s).imem = Function.update (secondStore n q s).imem
      (rowBase n q s+(n:ℤ)+(n:ℤ)) (s.ptrs 17) := by
    change Function.update _ _ _ = _
    rw [hc,secondStore,ArrayCopy.copy_ptr_frame n _ 17 (by simp)]
    simp [second,setPtr,first_ptr n q s 17 (by simp)]
  rw [hm]
  refine ⟨?_,?_,by simp⟩
  · intro v
    rw [Function.update_of_ne (by have := v.isLt; omega : rowBase n q s+(v.val:ℤ) ≠ rowBase n q s+(n:ℤ)+(n:ℤ)),
      secondStore,ArrayCopy.copy_memory_frame n _ (rowBase n q s+(v.val:ℤ))]
    · exact first_memory n q s hn v hS
    · left; simp only [second,setPtr,Function.update_self,first_cursor n q s hn]
      have := v.isLt; omega
  · intro v
    rw [Function.update_of_ne (by have := v.isLt; omega : rowBase n q s+(n:ℤ)+(v.val:ℤ) ≠ rowBase n q s+(n:ℤ)+(n:ℤ))]
    have h := ArrayCopy.copy_memory_get n (second (firstStore n q s)) (by
      intro i j
      simp only [second,setPtr,Function.update_of_ne (by decide : (3:ℕ) ≠ 4),Function.update_self,
        first_ptr n q s 50 (by simp),first_cursor n q s hn]
      have hh := hC i ⟨n+j.val,by have := j.isLt; omega⟩
      convert hh using 1 <;> push_cast <;> ring) v
    simp only [second,setPtr,Function.update_self,Function.update_of_ne (by decide : (3:ℕ) ≠ 4),
      first_ptr n q s 50 (by simp),first_cursor n q s hn] at h
    have he : (secondStore n q s).imem (rowBase n q s+(n:ℤ)+(v.val:ℤ)) =
        (firstStore n q s).imem (s.ptrs 50+(v.val:ℤ)) := by
      simpa only [secondStore,second,setPtr,Function.update_self,
        Function.update_of_ne (by decide : (3:ℕ) ≠ 4),first_ptr n q s 50 (by simp),first_cursor n q s hn] using h
    rw [he]
    apply first_frame n q s hn
    exact TableAppend.outside_interval (rowBase n q s) (s.ptrs 50+(v.val:ℤ)) n
      (fun j => hC v ⟨j.val,by have := j.isLt; omega⟩)

lemma old_record (n q : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ))
    (a : Fin q) (j : Fin (n+n+1)) :
    (eval n q s).imem (s.ptrs 2+(a.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ)) =
      s.imem (s.ptrs 2+(a.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ)) := by
  apply memory_frame n q s hn
  left
  have ha : (a.val:ℤ)+1 ≤ (q:ℤ) := by have := a.isLt; omega
  have hj : (j.val:ℤ) < (n:ℤ)+(n:ℤ)+1 := by have := j.isLt; omega
  dsimp [rowBase]; nlinarith
end StableMSR.Recovery.Compiler.PairRecord
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace StableMSR.Recovery.Compiler.ComponentState
open ComponentMachine
lemma prefix_high (n : ℕ) (s : Store) (j : ℕ) (hj : 60 < j) :
    (prefixEval n s).ptrs j = s.ptrs j := by
  simp only [prefixEval,readSeed,setPtr,Function.update_of_ne (by omega : j ≠ 60),
    Function.update_of_ne (by omega : j ≠ 7)]
  rw [MaskComplement.ptr_frame n _ j (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega)]
  simp only [saved,setPtr,Function.update_of_ne (by omega : j ≠ 59),Function.update_of_ne (by omega : j ≠ 58),
    Function.update_of_ne (by omega : j ≠ 57),Function.update_of_ne (by omega : j ≠ 56),
    Function.update_of_ne (by omega : j ≠ 55),Function.update_of_ne (by omega : j ≠ 54),
    Function.update_of_ne (by omega : j ≠ 53)]
  exact BitmapStats.stats_ptr_frame n s j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
lemma full_high (n m : ℕ) (s : Store) (j : ℕ) (hj : 60 < j) :
    (fullEval n m s).ptrs j = s.ptrs j := by
  unfold fullEval guardedEval
  split_ifs <;> first
  | exact (construct_high n m _ j (by omega)).trans (prefix_high n s j hj)
  | simpa [reject,setPtr,show j ≠ 18 by omega] using prefix_high n s j hj
end StableMSR.Recovery.Compiler.ComponentState
namespace StableMSR.Recovery.Compiler.StateRecord
open ComponentMachine

def redirectOps : List Op := [.pointerCopy 63 2,.pointerCopy 64 5,.pointerCopy 66 17,
  .pointerCopy 2 61,.pointerCopy 5 62,.pointerConst 17 0]
def redirect (s : Store) : Store := setPtr (setPtr (setPtr (setPtr (setPtr (setPtr s
  63 (s.ptrs 2)) 64 (s.ptrs 5)) 66 (s.ptrs 17)) 2 (s.ptrs 61)) 5 (s.ptrs 62)) 17 0
def returnOps : List Op := [.pointerCopy 62 5,.pointerCopy 2 63,.pointerCopy 5 64,.pointerCopy 17 66]
def returned (s : Store) : Store :=
  setPtr (setPtr (setPtr (setPtr s 62 (s.ptrs 5)) 2 (s.ptrs 63)) 5 (s.ptrs 64)) 17 (s.ptrs 66)
def appendCmd : Cmd := .seq (opsCmd redirectOps) (.seq PairRecord.command (opsCmd returnOps))
def appended (n q : ℕ) (s : Store) : Store := returned (PairRecord.eval n q (redirect s))
def rowBase (n q : ℕ) (s : Store) : ℤ := s.ptrs 61+(q:ℤ)*((n:ℤ)+(n:ℤ)+1)
lemma append_exec {N : ℕ} (d : Point N → Point N → ℝ) (n q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hq : s.ptrs 62 = (q:ℤ)) :
    Executes d appendCmd s (appended n q s) (4*q+14*n+43) := by
  have hr : Executes d (opsCmd redirectOps) s (redirect s) 6 := by
    simpa [redirectOps,redirect,evalOps,Op.eval,setPtr] using ops_exec d redirectOps s
  have ht : Executes d (opsCmd returnOps) (PairRecord.eval n q (redirect s)) (appended n q s) 4 := by
    simpa [returnOps,returned,appended,evalOps,Op.eval,setPtr] using ops_exec d returnOps (PairRecord.eval n q (redirect s))
  have h := Executes.seq hr (Executes.seq (PairRecord.exec d n q (redirect s)
    (by simpa [redirect,setPtr] using hn) (by simpa [redirect,setPtr] using hq)) ht)
  convert h using 1 <;> try rfl
  omega
lemma append_ptr (n q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∉ ([34,35,36,37,38,39,40,41,62,63,64,65,66,67,68]:List ℕ)) :
    (appended n q s).ptrs j = s.ptrs j := by
  by_cases h2 : j = 2
  · subst j; simp [appended,returned,setPtr,PairRecord.ptr_frame,redirect]
  by_cases h5 : j = 5
  · subst j; simp [appended,returned,setPtr,PairRecord.ptr_frame,redirect]
  by_cases h17 : j = 17
  · subst j; simp [appended,returned,setPtr,PairRecord.ptr_frame,redirect]
  simp only [appended,returned,setPtr,Function.update_of_ne h2,Function.update_of_ne h5,
    Function.update_of_ne h17,Function.update_of_ne (by simp_all : j ≠ 62)]
  rw [PairRecord.ptr_frame n q (redirect s) j (by simp_all)]
  simp_all [redirect,setPtr]
lemma append_count (n q : ℕ) (s : Store) : (appended n q s).ptrs 62 = s.ptrs 62+1 := by
  simp [appended,returned,setPtr,PairRecord.count,redirect]
lemma append_frame (n q : ℕ) (s : Store) : DataFrame s (appended n q s) := PairRecord.frame n q (redirect s)
lemma append_memory_frame (n q : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ)) (x : ℤ)
    (hx : x < rowBase n q s ∨ rowBase n q s+(n:ℤ)+(n:ℤ)+1 ≤ x) :
    (appended n q s).imem x = s.imem x := by
  exact PairRecord.memory_frame n q (redirect s) (by simpa [redirect,setPtr] using hn) x
    (by simpa [PairRecord.rowBase,rowBase,redirect,setPtr] using hx)
lemma append_values (n q : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ))
    (hS : ∀ i : Fin n, ∀ j : Fin (n+n+1), s.ptrs 3+(i.val:ℤ) ≠ rowBase n q s+(j.val:ℤ))
    (hC : ∀ i : Fin n, ∀ j : Fin (n+n+1), s.ptrs 50+(i.val:ℤ) ≠ rowBase n q s+(j.val:ℤ)) :
    (∀ v : Fin n, (appended n q s).imem (rowBase n q s+(v.val:ℤ)) = s.imem (s.ptrs 3+(v.val:ℤ))) ∧
    (∀ v : Fin n, (appended n q s).imem (rowBase n q s+(n:ℤ)+(v.val:ℤ)) = s.imem (s.ptrs 50+(v.val:ℤ))) ∧
    (appended n q s).imem (rowBase n q s+(n:ℤ)+(n:ℤ)) = 0 := by
  simpa [appended,returned,setPtr,redirect,PairRecord.rowBase,rowBase] using
    PairRecord.values n q (redirect s) (by simpa [redirect,setPtr] using hn)
      (by simpa [redirect,setPtr,PairRecord.rowBase,rowBase] using hS)
      (by simpa [redirect,setPtr,PairRecord.rowBase,rowBase] using hC)

def retainCmd : Cmd := .ite (.pointerLE 18 0) .skip appendCmd
noncomputable def retain (n q : ℕ) (s : Store) : Store :=
  if s.ptrs 18 ≤ s.ptrs 0 then s else appended n q s
noncomputable def eval (n m q : ℕ) (s : Store) : Store := retain n q (ComponentState.fullEval n m s)
def command : Cmd := .seq ComponentState.fullCmd retainCmd
noncomputable def retainCost (n q : ℕ) (s : Store) : ℕ := if s.ptrs 18 ≤ s.ptrs 0 then 1 else 4*q+14*n+45
noncomputable def steps (n m q : ℕ) (s : Store) : ℕ :=
  ComponentState.steps n m s+retainCost n q (ComponentState.fullEval n m s)
lemma retain_exec {N : ℕ} (d : Point N → Point N → ℝ) (n q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hq : s.ptrs 62 = (q:ℤ)) :
    Executes d retainCmd s (retain n q s) (retainCost n q s) := by
  unfold retainCmd retain retainCost
  split_ifs with h
  · exact Executes.ite_true (c := .pointerLE 18 0) h (Executes.skip s)
  · have hh := Executes.ite_false (c := .pointerLE 18 0) (yes := .skip) h (append_exec d n q s hn hq)
    convert hh using 1 <;> omega
lemma exec {N : ℕ} (d : Point N → Point N → ℝ) (n m q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 62 = (q:ℤ)) :
    Executes d command s (eval n m q s) (steps n m q s-1) := by
  have hh := Executes.seq (ComponentState.full_exec d n m s hm hn)
    (retain_exec d n q (ComponentState.fullEval n m s)
      (by rw [ComponentState.full_ptr n m s 6 (by simp),hn])
      (by rw [ComponentState.full_high n m s 62 (by decide),hq]))
  convert hh using 1 <;> try rfl
  have hp : 1 ≤ ComponentState.steps n m s := by dsimp [ComponentState.steps]; omega
  have ht : 1 ≤ retainCost n q (ComponentState.fullEval n m s) := by unfold retainCost; split_ifs <;> omega
  dsimp [steps]; omega
lemma steps_bound (n m q : ℕ) (s : Store) : steps n m q s ≤ n*(17*m+57)+17*m+4*q+113 := by
  have hh := ComponentState.steps_bound n m s
  have ht : retainCost n q (ComponentState.fullEval n m s) ≤ 4*q+14*n+45 := by unfold retainCost; split_ifs <;> omega
  dsimp [steps]; nlinarith
lemma ptr_frame (n m q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∈ ([2,3,4,5,6,17,43,50,51,61]:List ℕ)) : (eval n m q s).ptrs j = s.ptrs j := by
  have hstate : (ComponentState.fullEval n m s).ptrs j = s.ptrs j := by
    by_cases he : j = 61
    · subst j; exact ComponentState.full_high n m s 61 (by decide)
    · exact ComponentState.full_ptr n m s j (by simp_all)
  unfold eval retain
  split_ifs
  · exact hstate
  · rw [append_ptr n q _ j (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj ⊢; omega),hstate]
lemma high (n m q : ℕ) (s : Store) (j : ℕ) (hj : 68 < j) : (eval n m q s).ptrs j = s.ptrs j := by
  unfold eval retain
  split_ifs
  · exact ComponentState.full_high n m s j (by omega)
  · rw [append_ptr n q _ j (by simp only [List.mem_cons,List.not_mem_nil,or_false]; omega),ComponentState.full_high n m s j (by omega)]
lemma frame (n m q : ℕ) (s : Store) : DataFrame s (eval n m q s) := by
  unfold eval retain
  split_ifs
  · exact ComponentState.full_frame n m s
  · exact (ComponentState.full_frame n m s).trans (append_frame n q _)
noncomputable def program : MinSumFPT.Program := compile command 0
lemma program_length : program.length = 221 := by decide
lemma machine_execution {N : ℕ} (d : Point N → Point N → ℝ) (n m q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 62 = (q:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[steps n m q s] (s.state 0 work) =
      (eval n m q s).haltedState command.size (work+steps n m q s) 0 := by
  have hp : 1 ≤ steps n m q s := by
    have hs : 1 ≤ ComponentState.steps n m s := by dsimp [ComponentState.steps]; omega
    dsimp [steps]; omega
  simpa only [program,Nat.sub_add_cancel hp,
    show work+(steps n m q s-1)+1 = work+steps n m q s by omega] using
      compile_halts (exec d n m q s hn hm hq) ω work 0
end StableMSR.Recovery.Compiler.StateRecord
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open scoped Classical
namespace StableMSR.Recovery.Compiler.ComponentState
open ComponentMachine
lemma full_zero (n m : ℕ) (s : Store) : (fullEval n m s).ptrs 0 = 0 := by
  have hc (t : Store) : (constructEval n m t).ptrs 0 = 0 := by
    simp [constructEval,restored,setPtr,TightBoundaryProgram.fullEval,TightBoundaryProgram.restore,
      ArrayEquality.equalityEval,ArrayEquality.run_ptr_frame,ArrayEquality.prepEval]
  unfold fullEval guardedEval
  split_ifs <;> first | exact hc _ | simpa [reject,setPtr] using prefix_zero n s
end StableMSR.Recovery.Compiler.ComponentState
namespace StableMSR.Recovery.Compiler.StateRecord
open ComponentMachine ComponentMemory

/- Ordinary free table space is separated from the immutable input and
reusable work regions. No values of old or new records are assumed. -/
structure Room (n cap : ℕ) (es : List (Fin n × Fin n)) (s : Store) : Prop where
  separator : ∀ r : Fin cap, ∀ j : Fin (n+n+1), ∀ v : Fin n,
    address (s.ptrs 3) v ≠ rowBase n r.val s+(j.val:ℤ)
  allowed : ∀ r : Fin cap, ∀ j : Fin (n+n+1), ∀ v : Fin n,
    address (s.ptrs 4) v ≠ rowBase n r.val s+(j.val:ℤ)
  component : ∀ r : Fin cap, ∀ j : Fin (n+n+1), ∀ v : Fin n,
    address (s.ptrs 50) v ≠ rowBase n r.val s+(j.val:ℤ)
  boundary : ∀ r : Fin cap, ∀ j : Fin (n+n+1), ∀ v : Fin n,
    address (s.ptrs 51) v ≠ rowBase n r.val s+(j.val:ℤ)
  edges : ∀ r : Fin cap, ∀ j : Fin (n+n+1), ∀ a (ha : a < es.length),
    s.ptrs 2+2*(a:ℤ) ≠ rowBase n r.val s+(j.val:ℤ) ∧
    s.ptrs 2+2*(a:ℤ)+1 ≠ rowBase n r.val s+(j.val:ℤ)

noncomputable def eligible {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ)
    (S : Finset (Fin n)) (seed : Fin n) : Prop :=
  seed ∉ S ∧ S.card ≤ w ∧ S = BoundaryMemory.externalBoundary G (ComponentState.outsideComponent G S seed)

lemma evaluated {n : ℕ} (G : SimpleGraph (Fin n)) (w q : ℕ) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (h : ComponentState.Input w S es seed s)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    eval n es.length q s =
      if eligible G w S seed then appended n q (ComponentState.fullEval n es.length s)
      else ComponentState.fullEval n es.length s := by
  unfold eval retain
  rw [ComponentState.full_zero,ComponentState.full_flag G w S es seed s h hsound hcomplete]
  unfold eligible
  by_cases hp : seed ∉ S ∧ S.card ≤ w ∧ S = BoundaryMemory.externalBoundary G (ComponentState.outsideComponent G S seed)
  · simp only [if_pos hp]; norm_num
  · simp only [if_neg hp]; norm_num

lemma count {n : ℕ} (G : SimpleGraph (Fin n)) (w q : ℕ) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (h : ComponentState.Input w S es seed s) (hq : s.ptrs 62 = (q:ℤ))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    (eval n es.length q s).ptrs 62 = ((q+(if eligible G w S seed then 1 else 0):ℕ):ℤ) := by
  rw [evaluated G w q S es seed s h hsound hcomplete]
  split_ifs with hp
  · rw [append_count,ComponentState.full_high n es.length s 62 (by decide),hq]; push_cast; rfl
  · rw [ComponentState.full_high n es.length s 62 (by decide),hq]; simp

lemma memory_frame {n : ℕ} (G : SimpleGraph (Fin n)) (w q : ℕ) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (h : ComponentState.Input w S es seed s)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (x : ℤ) (ha : ∀ v : Fin n, x ≠ address (s.ptrs 4) v)
    (hc : ∀ v : Fin n, x ≠ address (s.ptrs 50) v)
    (hb : ∀ v : Fin n, x ≠ address (s.ptrs 51) v)
    (hr : x < rowBase n q s ∨ rowBase n q s+(n:ℤ)+(n:ℤ)+1 ≤ x) :
    (eval n es.length q s).imem x = s.imem x := by
  rw [evaluated G w q S es seed s h hsound hcomplete]
  split_ifs
  · rw [append_memory_frame n q _ (by rw [ComponentState.full_ptr n es.length s 6 (by simp),h.vertices]) x]
    · exact ComponentState.full_memory_frame G w S es seed s h hsound hcomplete x ha hc hb
    · simpa [address,rowBase,ComponentState.full_high n es.length s 61 (by decide)] using hr
  · exact ComponentState.full_memory_frame G w S es seed s h hsound hcomplete x ha hc hb

lemma old_record {n : ℕ} (G : SimpleGraph (Fin n)) (w q : ℕ) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (h : ComponentState.Input w S es seed s) (hr : Room n (q+1) es s)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (a : Fin q) (j : Fin (n+n+1)) :
    (eval n es.length q s).imem (rowBase n a.val s+(j.val:ℤ)) = s.imem (rowBase n a.val s+(j.val:ℤ)) := by
  apply memory_frame G w q S es seed s h hsound hcomplete
  · exact fun v => Ne.symm (hr.allowed ⟨a.val,by have := a.isLt; omega⟩ j v)
  · exact fun v => Ne.symm (hr.component ⟨a.val,by have := a.isLt; omega⟩ j v)
  · exact fun v => Ne.symm (hr.boundary ⟨a.val,by have := a.isLt; omega⟩ j v)
  · left
    have ha : (a.val:ℤ)+1 ≤ (q:ℤ) := by have := a.isLt; omega
    have hj : (j.val:ℤ) < (n:ℤ)+(n:ℤ)+1 := by have := j.isLt; omega
    dsimp [rowBase]; nlinarith

lemma appended_state {n : ℕ} (G : SimpleGraph (Fin n)) (w q : ℕ) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (h : ComponentState.Input w S es seed s) (hr : Room n (q+1) es s)
    (hp : eligible G w S seed)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    (∀ v : Fin n, (eval n es.length q s).imem (rowBase n q s+(v.val:ℤ)) = if v ∈ S then 1 else 0) ∧
    (∀ v : Fin n, (eval n es.length q s).imem (rowBase n q s+(n:ℤ)+(v.val:ℤ)) =
      if v ∈ ComponentState.outsideComponent G S seed then 1 else 0) ∧
    (eval n es.length q s).imem (rowBase n q s+(n:ℤ)+(n:ℤ)) = 0 := by
  rw [evaluated G w q S es seed s h hsound hcomplete,if_pos hp]
  have hs := ComponentState.full_source G w S es seed s h hsound hcomplete
  have hc := (ComponentState.full_bitmaps G w S es seed s h hp.1 hp.2.1 hsound hcomplete).1
  have hh := append_values n q (ComponentState.fullEval n es.length s)
    (by rw [ComponentState.full_ptr n es.length s 6 (by simp),h.vertices])
    (by intro i j; simpa [address,rowBase,ComponentState.full_high n es.length s 61 (by decide),
        ComponentState.full_ptr n es.length s 3 (by simp)] using hr.separator ⟨q,by omega⟩ j i)
    (by intro i j; simpa [address,rowBase,ComponentState.full_high n es.length s 61 (by decide),
        ComponentState.full_ptr n es.length s 50 (by simp)] using hr.component ⟨q,by omega⟩ j i)
  have hbase : rowBase n q (ComponentState.fullEval n es.length s) = rowBase n q s := by
    simp [rowBase,ComponentState.full_high n es.length s 61 (by decide)]
  rw [hbase] at hh
  refine ⟨?_,?_,hh.2.2⟩
  · intro v
    rw [hh.1 v,ComponentState.full_ptr n es.length s 3 (by simp)]
    exact hs v
  · intro v
    rw [hh.2.1 v,ComponentState.full_ptr n es.length s 50 (by simp)]
    exact hc v

lemma rejected_table {n : ℕ} (G : SimpleGraph (Fin n)) (w q : ℕ) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (h : ComponentState.Input w S es seed s) (hr : Room n (q+1) es s)
    (hp : ¬eligible G w S seed)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (a : Fin (q+1)) (j : Fin (n+n+1)) :
    (eval n es.length q s).imem (rowBase n a.val s+(j.val:ℤ)) = s.imem (rowBase n a.val s+(j.val:ℤ)) := by
  rw [evaluated G w q S es seed s h hsound hcomplete,if_neg hp]
  exact ComponentState.full_memory_frame G w S es seed s h hsound hcomplete _
    (fun v => Ne.symm (hr.allowed a j v)) (fun v => Ne.symm (hr.component a j v))
    (fun v => Ne.symm (hr.boundary a j v))

lemma row_outside (n q : ℕ) (s : Store) (x : ℤ)
    (hx : ∀ j : Fin (n+n+1), x ≠ rowBase n q s+(j.val:ℤ)) :
    x < rowBase n q s ∨ rowBase n q s+(n:ℤ)+(n:ℤ)+1 ≤ x := by
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using
    TableAppend.outside_interval (rowBase n q s) x (n+n+1) hx

lemma source_preserved {n : ℕ} (G : SimpleGraph (Fin n)) (w q : ℕ) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (h : ComponentState.Input w S es seed s) (hr : Room n (q+1) es s)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    Bitmap (eval n es.length q s).imem (s.ptrs 3) S ∧ EdgeEncoding (eval n es.length q s).imem (s.ptrs 2) es := by
  constructor
  · intro v
    rw [memory_frame G w q S es seed s h hsound hcomplete _
      (h.separator_allowed v) (h.separator_component v) (h.separator_boundary v)]
    · exact h.separator v
    · exact row_outside n q s _
        (fun j => hr.separator ⟨q,by omega⟩ j v)
  · intro a ha
    rw [memory_frame G w q S es seed s h hsound hcomplete _
      (fun v => (h.edges_allowed a ha v).1) (fun v => (h.edges_component a ha v).1)
      (fun v => (h.edges_boundary a ha v).1),
      memory_frame G w q S es seed s h hsound hcomplete _
      (fun v => (h.edges_allowed a ha v).2) (fun v => (h.edges_component a ha v).2)
      (fun v => (h.edges_boundary a ha v).2)]
    · exact h.encoding a ha
    · exact row_outside n q s _
        (fun j => (hr.edges ⟨q,by omega⟩ j a ha).2)
    · exact row_outside n q s _
        (fun j => (hr.edges ⟨q,by omega⟩ j a ha).1)
end StableMSR.Recovery.Compiler.StateRecord
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateRecord
open ComponentMachine ComponentMemory

lemma flag (n m q : ℕ) (s : Store) :
    (eval n m q s).ptrs 18 = (ComponentState.fullEval n m s).ptrs 18 := by
  unfold eval retain; split_ifs
  · rfl
  · exact append_ptr n q _ 18 (by simp)

/- An actual run constructs and checks a candidate, then appends its exact
separator-component record precisely when accepted, preserving all older rows. -/
end StableMSR.Recovery.Compiler.StateRecord
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace StableMSR.Recovery.Compiler.StateSeedSweep
open ComponentMachine

noncomputable def added (n m : ℕ) (s : Store) : ℕ :=
  if (ComponentState.fullEval n m s).ptrs 18 ≤ (ComponentState.fullEval n m s).ptrs 0 then 0 else 1
lemma added_le (n m : ℕ) (s : Store) : added n m s ≤ 1 := by unfold added; split_ifs <;> omega
lemma record_count (n m q : ℕ) (s : Store) (hq : s.ptrs 62 = (q:ℤ)) :
    (StateRecord.eval n m q s).ptrs 62 = ((q+added n m s:ℕ):ℤ) := by
  unfold StateRecord.eval StateRecord.retain added
  split_ifs
  · rw [ComponentState.full_high n m s 62 (by decide),hq]; simp
  · rw [StateRecord.append_count,ComponentState.full_high n m s 62 (by decide),hq]; push_cast; rfl

def seeded (s : Store) : Store := setPtr s 17 (s.ptrs 70)
def body : Cmd := .seq (.atom (.pointerCopy 17 70)) (.seq StateRecord.command (.atom (.pointerInc 70)))
noncomputable def row (n m q : ℕ) (s : Store) : Store := incPtr (StateRecord.eval n m q (seeded s)) 70
noncomputable def nextCount (n m q : ℕ) (s : Store) : ℕ := q+added n m (seeded s)
noncomputable def run (n m : ℕ) : ℕ → ℕ → Store → Store
  | _,0,s => s
  | q,r+1,s => run n m (nextCount n m q s) r (row n m q s)
noncomputable def finalCount (n m : ℕ) : ℕ → ℕ → Store → ℕ
  | q,0,_ => q
  | q,r+1,s => finalCount n m (nextCount n m q s) r (row n m q s)
noncomputable def loopCost (n m : ℕ) : ℕ → ℕ → Store → ℕ
  | _,0,_ => 2
  | q,r+1,s => StateRecord.steps n m q (seeded s)+3+
      loopCost n m (nextCount n m q s) r (row n m q s)
lemma row_ptr (n m q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∈ ([2,3,4,5,6,43,50,51,61]:List ℕ)) : (row n m q s).ptrs j = s.ptrs j := by
  have h70 : j ≠ 70 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
  have h17 : j ≠ 17 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
  simp only [row,incPtr,setPtr,Function.update_of_ne h70]
  rw [StateRecord.ptr_frame n m q _ j (by simp_all)]
  simp [seeded,setPtr,h17]
lemma row_index (n m q : ℕ) (s : Store) : (row n m q s).ptrs 70 = s.ptrs 70+1 := by
  simp [row,incPtr,setPtr,StateRecord.high,seeded]
lemma row_high (n m q : ℕ) (s : Store) (j : ℕ) (hj : 70 < j) : (row n m q s).ptrs j = s.ptrs j := by
  simp only [row,incPtr,setPtr,Function.update_of_ne (by omega : j ≠ 70)]
  rw [StateRecord.high n m q _ j (by omega)]
  simp [seeded,setPtr,show j ≠ 17 by omega]
lemma row_count (n m q : ℕ) (s : Store) (hq : s.ptrs 62 = (q:ℤ)) :
    (row n m q s).ptrs 62 = (nextCount n m q s:ℤ) := by
  simpa [row,incPtr,setPtr,nextCount] using record_count n m q (seeded s) (by simpa [seeded,setPtr] using hq)
lemma row_exec {N : ℕ} (d : Point N → Point N → ℝ) (n m q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 62 = (q:ℤ)) :
    Executes d body s (row n m q s) (StateRecord.steps n m q (seeded s)+1) := by
  have hh := Executes.seq (Executes.atom (.pointerCopy 17 70) s)
    (Executes.seq (StateRecord.exec d n m q (seeded s)
      (by simpa [seeded,setPtr] using hn) (by simpa [seeded,setPtr] using hm)
      (by simpa [seeded,setPtr] using hq)) (Executes.atom (.pointerInc 70) (StateRecord.eval n m q (seeded s))))
  convert hh using 1 <;> try rfl
  have hp : 1 ≤ StateRecord.steps n m q (seeded s) := by
    dsimp [StateRecord.steps,ComponentState.steps]; omega
  omega
lemma loop_exec {N : ℕ} (d : Point N → Point N → ℝ) (n m q r : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 62 = (q:ℤ))
    (hstop : s.ptrs 70+(r:ℤ)-1 = s.ptrs 71) :
    Executes d (.whileDo (.pointerLE 70 71) body) s (run n m q r s) (loopCost n m q r s) := by
  induction r generalizing q s with
  | zero => apply Executes.while_false; simp only [Cond.test]; omega
  | succ r ih =>
    have hg : (Cond.pointerLE 70 71).test s := by simp only [Cond.test]; push_cast at hstop; omega
    have hh := Executes.while_true hg (row_exec d n m q s hn hm hq)
      (ih (nextCount n m q s) (row n m q s)
        (by rw [row_ptr n m q s 6 (by simp),hn]) (by rw [row_ptr n m q s 5 (by simp),hm])
        (row_count n m q s hq) (by rw [row_index,row_high n m q s 71 (by decide)]; push_cast at hstop; omega))
    convert hh using 1 <;> try rfl
    simp only [loopCost]; omega
lemma run_count (n m q r : ℕ) (s : Store) (hq : s.ptrs 62 = (q:ℤ)) :
    (run n m q r s).ptrs 62 = (finalCount n m q r s:ℤ) := by
  induction r generalizing q s with
  | zero => exact hq
  | succ r ih => exact ih (nextCount n m q s) (row n m q s) (row_count n m q s hq)
lemma count_bounds (n m q r : ℕ) (s : Store) :
    q ≤ finalCount n m q r s ∧ finalCount n m q r s ≤ q+r := by
  induction r generalizing q s with
  | zero => simp [finalCount]
  | succ r ih =>
    have hh := ih (nextCount n m q s) (row n m q s)
    have hb := added_le n m (seeded s)
    simp only [finalCount]
    exact ⟨(show q ≤ nextCount n m q s by dsimp [nextCount]; omega).trans hh.1,
      hh.2.trans (by dsimp [nextCount]; omega)⟩
lemma loop_bound (n m q r : ℕ) (s : Store) :
    loopCost n m q r s ≤ r*(n*(17*m+57)+17*m+4*(q+r)+116)+2 := by
  induction r generalizing q s with
  | zero => simp [loopCost]
  | succ r ih =>
    have hh := ih (nextCount n m q s) (row n m q s)
    have hb := added_le n m (seeded s)
    have he : nextCount n m q s+r ≤ q+(r+1) := by dsimp [nextCount]; omega
    have hmul := Nat.mul_le_mul_left r (show n*(17*m+57)+17*m+4*(nextCount n m q s+r)+116 ≤
        n*(17*m+57)+17*m+4*(q+(r+1))+116 by omega)
    have hc := StateRecord.steps_bound n m q (seeded s)
    simp only [loopCost]; nlinarith

def setupOps : List Op := [.pointerConst 70 0,.pointerCopy 71 6,.pointerDec 71]
def setup (s : Store) : Store := setPtr (setPtr s 70 0) 71 (s.ptrs 6-1)
def command : Cmd := .seq (opsCmd setupOps) (.whileDo (.pointerLE 70 71) body)
noncomputable def eval (n m q : ℕ) (s : Store) : Store := run n m q n (setup s)
noncomputable def steps (n m q : ℕ) (s : Store) : ℕ := 4+loopCost n m q n (setup s)
noncomputable def program : MinSumFPT.Program := compile command 0
lemma exec {N : ℕ} (d : Point N → Point N → ℝ) (n m q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 62 = (q:ℤ)) :
    Executes d command s (eval n m q s) (3+loopCost n m q n (setup s)) := by
  have hp : Executes d (opsCmd setupOps) s (setup s) 3 := by
    simpa [setupOps,setup,evalOps,Op.eval,setPtr,Function.update_idem] using ops_exec d setupOps s
  exact Executes.seq hp (loop_exec d n m q n (setup s)
    (by simpa [setup,setPtr] using hn) (by simpa [setup,setPtr] using hm)
    (by simpa [setup,setPtr] using hq) (by simp [setup,setPtr,hn]))
lemma steps_bound (n m q : ℕ) (s : Store) :
    steps n m q s ≤ n*(n*(17*m+57)+17*m+4*(q+n)+116)+6 := by
  have hh := loop_bound n m q n (setup s); dsimp [steps]; omega
lemma program_length : program.length = 229 := by decide
lemma machine_execution {N : ℕ} (d : Point N → Point N → ℝ) (n m q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 62 = (q:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[steps n m q s] (s.state 0 work) =
      (eval n m q s).haltedState command.size (work+steps n m q s) 0 := by
  simpa only [program,steps,show 3+loopCost n m q n (setup s)+1 = 4+loopCost n m q n (setup s) by omega,
    show work+(3+loopCost n m q n (setup s))+1 = work+(4+loopCost n m q n (setup s)) by omega] using
      compile_halts (exec d n m q s hn hm hq) ω work 0
lemma run_frame (n m q r : ℕ) (s : Store) : DataFrame s (run n m q r s) := by
  induction r generalizing q s with
  | zero => exact DataFrame.refl s
  | succ r ih =>
    have hh : DataFrame s (row n m q s) := StateRecord.frame n m q (seeded s)
    exact hh.trans (ih (nextCount n m q s) (row n m q s))

/- Charged execution and count bounds for the full seed sweep. Semantic
coverage of the retained table across all iterations is a separate invariant. -/
theorem charged_seed_sweep_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 229 ∧
    ∀ (N n m q : ℕ) (d : Point N → Point N → ℝ) (s : Store),
      s.ptrs 6 = (n:ℤ) → s.ptrs 5 = (m:ℤ) → s.ptrs 62 = (q:ℤ) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      ∃ t ≤ n*(n*(17*m+57)+17*m+4*(q+n)+116)+6,
      let result := (MinSumFPT.step P d ω)^[t] (s.state 0 work)
      result.halted = true ∧ result.work = work+t ∧
      (q:ℤ) ≤ result.cfg.ptrs 62 ∧ result.cfg.ptrs 62 ≤ ((q+n:ℕ):ℤ) ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos := by
  refine ⟨program,compile_deterministic command 0,program_length,?_⟩
  intro N n m q d s hn hm hq ω work
  refine ⟨steps n m q s,steps_bound n m q s,?_⟩
  dsimp only
  rw [machine_execution d n m q s hn hm hq ω work]
  have hq' : (setup s).ptrs 62 = (q:ℤ) := by simpa [setup,setPtr] using hq
  have hc := run_count n m q n (setup s) hq'
  have hb := count_bounds n m q n (setup s)
  have hf := run_frame n m q n (setup s)
  refine ⟨rfl,rfl,?_,?_,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩
  · change (q:ℤ) ≤ (eval n m q s).ptrs 62
    rw [eval,hc]; exact_mod_cast hb.1
  · change (eval n m q s).ptrs 62 ≤ ((q+n:ℕ):ℤ)
    rw [eval,hc]; exact_mod_cast hb.2
end StableMSR.Recovery.Compiler.StateSeedSweep

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateSeedSweep
open ComponentMachine ComponentMemory

/- Seed-independent input contract for a complete sweep. -/
structure Input {n : ℕ} (w : ℕ) (S : Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store) : Prop where
  edges : s.ptrs 5 = (es.length:ℤ)
  vertices : s.ptrs 6 = (n:ℤ)
  width : s.ptrs 43 = (w:ℤ)
  separator : Bitmap s.imem (s.ptrs 3) S
  encoding : EdgeEncoding s.imem (s.ptrs 2) es
  separator_allowed : Separate (n := n) (s.ptrs 3) (s.ptrs 4)
  separator_component : Separate (n := n) (s.ptrs 3) (s.ptrs 50)
  separator_boundary : Separate (n := n) (s.ptrs 3) (s.ptrs 51)
  allowed_component : Separate (n := n) (s.ptrs 4) (s.ptrs 50)
  component_boundary : Separate (n := n) (s.ptrs 50) (s.ptrs 51)
  edges_allowed : EdgesSeparate (s.ptrs 2) (s.ptrs 4) es
  edges_component : EdgesSeparate (s.ptrs 2) (s.ptrs 50) es
  edges_boundary : EdgesSeparate (s.ptrs 2) (s.ptrs 51) es

/- Exact two-bitmap key and zero initialization payload at row a. -/
def Record {n : ℕ} (s : Store) (a : ℕ) (S C : Finset (Fin n)) : Prop :=
  (∀ v : Fin n, s.imem (StateRecord.rowBase n a s+(v.val:ℤ)) = if v ∈ S then 1 else 0) ∧
  (∀ v : Fin n, s.imem (StateRecord.rowBase n a s+(n:ℤ)+(v.val:ℤ)) = if v ∈ C then 1 else 0) ∧
  s.imem (StateRecord.rowBase n a s+(n:ℤ)+(n:ℤ)) = 0

lemma input_seed {n w : ℕ} {S : Finset (Fin n)} {es : List (Fin n × Fin n)}
    {s : Store} (h : Input w S es s) (seed : Fin n) (hi : s.ptrs 70 = (seed.val:ℤ)) :
    ComponentState.Input w S es seed (seeded s) := by
  constructor <;> simp only [seeded,setPtr,Function.update_self,Function.update_of_ne (by decide : 5 ≠ 17),
    Function.update_of_ne (by decide : 6 ≠ 17),Function.update_of_ne (by decide : 43 ≠ 17),
    Function.update_of_ne (by decide : 3 ≠ 17),Function.update_of_ne (by decide : 2 ≠ 17),
    Function.update_of_ne (by decide : 4 ≠ 17),Function.update_of_ne (by decide : 50 ≠ 17),
    Function.update_of_ne (by decide : 51 ≠ 17)]
  all_goals first | exact h.edges | exact h.vertices | exact hi | exact h.width | exact h.separator |
    exact h.encoding | exact h.separator_allowed | exact h.separator_component | exact h.separator_boundary |
    exact h.allowed_component | exact h.component_boundary | exact h.edges_allowed | exact h.edges_component | exact h.edges_boundary

lemma room_mono {n c c' : ℕ} {es : List (Fin n × Fin n)} {s : Store}
    (h : StateRecord.Room n c es s) (hc : c' ≤ c) : StateRecord.Room n c' es s :=
  ⟨fun r j v => h.separator ⟨r.val,lt_of_lt_of_le r.isLt hc⟩ j v,
   fun r j v => h.allowed ⟨r.val,lt_of_lt_of_le r.isLt hc⟩ j v,
   fun r j v => h.component ⟨r.val,lt_of_lt_of_le r.isLt hc⟩ j v,
   fun r j v => h.boundary ⟨r.val,lt_of_lt_of_le r.isLt hc⟩ j v,
   fun r j a ha => h.edges ⟨r.val,lt_of_lt_of_le r.isLt hc⟩ j a ha⟩

lemma room_transfer {n c : ℕ} {es : List (Fin n × Fin n)} {s t : Store}
    (h : StateRecord.Room n c es s)
    (hp : ∀ j, j ∈ ([2,3,4,50,51,61]:List ℕ) → t.ptrs j = s.ptrs j) :
    StateRecord.Room n c es t := by
  have hb (a : ℕ) : StateRecord.rowBase n a t = StateRecord.rowBase n a s := by
    simp only [StateRecord.rowBase,hp 61 (by simp)]
  constructor
  · intro r j v; rw [hb,hp 3 (by simp)]; exact h.separator r j v
  · intro r j v; rw [hb,hp 4 (by simp)]; exact h.allowed r j v
  · intro r j v; rw [hb,hp 50 (by simp)]; exact h.component r j v
  · intro r j v; rw [hb,hp 51 (by simp)]; exact h.boundary r j v
  · intro r j a ha; rw [hb,hp 2 (by simp)]; exact h.edges r j a ha

lemma room_seed {n c : ℕ} {es : List (Fin n × Fin n)} {s : Store}
    (h : StateRecord.Room n c es s) : StateRecord.Room n c es (seeded s) := by
  apply room_transfer h
  intro j hj
  have hj' : j ≠ 17 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
  simp [seeded,setPtr,hj']

lemma row_room {n c m q : ℕ} {es : List (Fin n × Fin n)} {s : Store}
    (h : StateRecord.Room n c es s) : StateRecord.Room n c es (row n m q s) :=
  room_transfer h (fun j hj => row_ptr n m q s j (by simp_all; omega))

lemma row_input {n w q : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (h : Input w S es s) (hi : s.ptrs 70 = (seed.val:ℤ)) (hr : StateRecord.Room n (q+1) es s)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    Input w S es (row n es.length q s) := by
  have hh := StateRecord.source_preserved G w q S es seed (seeded s) (input_seed h seed hi)
    (room_seed hr) hsound hcomplete
  have hp := row_ptr n es.length q s
  constructor
  · rw [hp 5 (by simp)]; exact h.edges
  · rw [hp 6 (by simp)]; exact h.vertices
  · rw [hp 43 (by simp)]; exact h.width
  · rw [hp 3 (by simp)]; exact hh.1
  · rw [hp 2 (by simp)]; exact hh.2
  · rw [hp 3 (by simp),hp 4 (by simp)]; exact h.separator_allowed
  · rw [hp 3 (by simp),hp 50 (by simp)]; exact h.separator_component
  · rw [hp 3 (by simp),hp 51 (by simp)]; exact h.separator_boundary
  · rw [hp 4 (by simp),hp 50 (by simp)]; exact h.allowed_component
  · rw [hp 50 (by simp),hp 51 (by simp)]; exact h.component_boundary
  · rw [hp 2 (by simp),hp 4 (by simp)]; exact h.edges_allowed
  · rw [hp 2 (by simp),hp 50 (by simp)]; exact h.edges_component
  · rw [hp 2 (by simp),hp 51 (by simp)]; exact h.edges_boundary

lemma nextCount_spec {n w q : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (h : Input w S es s) (hi : s.ptrs 70 = (seed.val:ℤ))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    nextCount n es.length q s = q+(if StateRecord.eligible G w S seed then 1 else 0) := by
  unfold nextCount added
  rw [ComponentState.full_zero,ComponentState.full_flag G w S es seed (seeded s) (input_seed h seed hi) hsound hcomplete]
  by_cases he : StateRecord.eligible G w S seed
  · have he' : seed ∉ S ∧ S.card ≤ w ∧ S = BoundaryMemory.externalBoundary G (ComponentState.outsideComponent G S seed) := he
    simp only [if_pos he,if_pos he']; norm_num
  · have he' : ¬(seed ∉ S ∧ S.card ≤ w ∧ S = BoundaryMemory.externalBoundary G (ComponentState.outsideComponent G S seed)) := he
    simp only [if_neg he,if_neg he']; norm_num

lemma row_old {n w q : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (h : Input w S es s) (hi : s.ptrs 70 = (seed.val:ℤ)) (hr : StateRecord.Room n (q+1) es s)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (a : Fin q) (j : Fin (n+n+1)) :
    (row n es.length q s).imem (StateRecord.rowBase n a.val s+(j.val:ℤ)) =
      s.imem (StateRecord.rowBase n a.val s+(j.val:ℤ)) :=
  StateRecord.old_record G w q S es seed (seeded s) (input_seed h seed hi) (room_seed hr) hsound hcomplete a j

lemma row_new {n w q : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (seed : Fin n) (s : Store)
    (h : Input w S es s) (hi : s.ptrs 70 = (seed.val:ℤ)) (hr : StateRecord.Room n (q+1) es s)
    (he : StateRecord.eligible G w S seed)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    Record (row n es.length q s) q S (ComponentState.outsideComponent G S seed) := by
  have hh := StateRecord.appended_state G w q S es seed (seeded s)
    (input_seed h seed hi) (room_seed hr) he hsound hcomplete
  have hb : StateRecord.rowBase n q (row n es.length q s) = StateRecord.rowBase n q (seeded s) := by
    simp only [StateRecord.rowBase,row_ptr n es.length q s 61 (by simp),seeded,setPtr,Function.update_of_ne (by decide : 61 ≠ 17)]
  unfold Record
  rw [hb]
  exact hh

lemma run_ptr (n m q r : ℕ) (s : Store) (j : ℕ)
    (hj : j ∈ ([2,3,4,5,6,43,50,51,61]:List ℕ)) : (run n m q r s).ptrs j = s.ptrs j := by
  induction r generalizing q s with
  | zero => rfl
  | succ r ih => rw [run,ih _ _ ,row_ptr n m q s j hj]

lemma run_room {n c m q r : ℕ} {es : List (Fin n × Fin n)} {s : Store}
    (h : StateRecord.Room n c es s) : StateRecord.Room n c es (run n m q r s) :=
  room_transfer h (fun j hj => run_ptr n m q r s j (by simp_all; omega))

lemma record_transfer {n q : ℕ} {s t : Store} {S C : Finset (Fin n)} {a : ℕ}
    (ha : a < q) (hp : t.ptrs 61 = s.ptrs 61)
    (hm : ∀ r : Fin q, ∀ j : Fin (n+n+1), t.imem (StateRecord.rowBase n r.val s+(j.val:ℤ)) =
      s.imem (StateRecord.rowBase n r.val s+(j.val:ℤ))) (h : Record s a S C) : Record t a S C := by
  have hb : StateRecord.rowBase n a t = StateRecord.rowBase n a s := by simp only [StateRecord.rowBase,hp]
  refine ⟨?_,?_,?_⟩
  · intro v; rw [hb,hm ⟨a,ha⟩ ⟨v.val,by have := v.isLt; omega⟩]; exact h.1 v
  · intro v
    have hh := hm ⟨a,ha⟩ ⟨n+v.val,by have := v.isLt; omega⟩
    simp only [Nat.cast_add,add_assoc] at hh
    rw [hb,show StateRecord.rowBase n a s+(n:ℤ)+(v.val:ℤ) = StateRecord.rowBase n a s+((n:ℤ)+(v.val:ℤ)) by omega,hh]
    simpa only [add_assoc] using h.2.1 v
  · have hh := hm ⟨a,ha⟩ ⟨n+n,by omega⟩
    simp only [Nat.cast_add,add_assoc] at hh
    rw [hb,show StateRecord.rowBase n a s+(n:ℤ)+(n:ℤ) = StateRecord.rowBase n a s+((n:ℤ)+(n:ℤ)) by omega,hh]
    simpa only [add_assoc] using h.2.2
end StableMSR.Recovery.Compiler.StateSeedSweep
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateSeedSweep
open ComponentMachine ComponentMemory

lemma run_preserves {n w : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (r q lo : ℕ) (s : Store) (h : Input w S es s)
    (hi : s.ptrs 70 = (lo:ℤ)) (hb : lo+r ≤ n) (hr : StateRecord.Room n (q+r) es s) :
    Input w S es (run n es.length q r s) ∧
    (∀ a : Fin q, ∀ j : Fin (n+n+1),
      (run n es.length q r s).imem (StateRecord.rowBase n a.val s+(j.val:ℤ)) =
        s.imem (StateRecord.rowBase n a.val s+(j.val:ℤ))) := by
  induction r generalizing q lo s with
  | zero => exact ⟨h,fun _ _ => rfl⟩
  | succ r ih =>
    let seed : Fin n := ⟨lo,by omega⟩
    have hr1 : StateRecord.Room n (q+1) es s := room_mono hr (by omega)
    have hn := row_input G S es seed s h hi hr1 hsound hcomplete
    have hc := added_le n es.length (seeded s)
    have hq : q ≤ nextCount n es.length q s := by dsimp [nextCount]; omega
    have hq' : nextCount n es.length q s ≤ q+1 := by dsimp [nextCount]; omega
    have hhi : (row n es.length q s).ptrs 70 = ((lo+1:ℕ):ℤ) := by rw [row_index,hi]; push_cast; rfl
    have hh := ih (nextCount n es.length q s) (lo+1) (row n es.length q s) hn hhi (by omega)
      (room_mono (row_room hr) (by omega))
    refine ⟨hh.1,?_⟩
    intro a j
    have hp := hh.2 ⟨a.val,lt_of_lt_of_le a.isLt hq⟩ j
    have hbase : StateRecord.rowBase n a.val (row n es.length q s) = StateRecord.rowBase n a.val s := by
      simp only [StateRecord.rowBase,row_ptr n es.length q s 61 (by simp)]
    rw [hbase] at hp
    exact hp.trans (row_old G S es seed s h hi hr1 hsound hcomplete a j)

lemma run_record {n w : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (r q lo : ℕ) (s : Store) (h : Input w S es s)
    (hi : s.ptrs 70 = (lo:ℤ)) (hb : lo+r ≤ n) (hr : StateRecord.Room n (q+r) es s)
    (a : ℕ) (ha : a < q) (T C : Finset (Fin n)) (hrc : Record s a T C) :
    Record (run n es.length q r s) a T C :=
  record_transfer ha (run_ptr n es.length q r s 61 (by simp))
    (run_preserves G S es hsound hcomplete r q lo s h hi hb hr).2 hrc

/- Exact soundness and coverage of the newly appended table interval. -/
lemma run_coverage {n w : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (r q lo : ℕ) (s : Store) (h : Input w S es s)
    (hi : s.ptrs 70 = (lo:ℤ)) (hb : lo+r ≤ n) (hr : StateRecord.Room n (q+r) es s) :
    (∀ a : ℕ, q ≤ a → a < finalCount n es.length q r s →
      ∃ seed : Fin n, lo ≤ seed.val ∧ seed.val < lo+r ∧ StateRecord.eligible G w S seed ∧
        Record (run n es.length q r s) a S (ComponentState.outsideComponent G S seed)) ∧
    (∀ seed : Fin n, lo ≤ seed.val → seed.val < lo+r → StateRecord.eligible G w S seed →
      ∃ a : ℕ, q ≤ a ∧ a < finalCount n es.length q r s ∧
        Record (run n es.length q r s) a S (ComponentState.outsideComponent G S seed)) := by
  induction r generalizing q lo s with
  | zero =>
    constructor
    · intro a ha hb; simp only [finalCount] at hb; omega
    · intro seed hs ht; omega
  | succ r ih =>
    let seed : Fin n := ⟨lo,by omega⟩
    have hr1 : StateRecord.Room n (q+1) es s := room_mono hr (by omega)
    have hn := row_input G S es seed s h hi hr1 hsound hcomplete
    have hc := nextCount_spec (q := q) G S es seed s h hi hsound hcomplete
    have hq : q ≤ nextCount n es.length q s := by rw [hc]; omega
    have hq' : nextCount n es.length q s ≤ q+1 := by rw [hc]; split_ifs <;> omega
    have hhi : (row n es.length q s).ptrs 70 = ((lo+1:ℕ):ℤ) := by rw [row_index,hi]; push_cast; rfl
    have hrt : StateRecord.Room n (nextCount n es.length q s+r) es (row n es.length q s) :=
      room_mono (row_room hr) (by omega)
    have hh := ih (nextCount n es.length q s) (lo+1) (row n es.length q s) hn hhi (by omega) hrt
    have hnew (he : StateRecord.eligible G w S seed) :
        Record (run n es.length q (r+1) s) q S (ComponentState.outsideComponent G S seed) := by
      have hnext : nextCount n es.length q s = q+1 := by rw [hc,if_pos he]
      exact run_record G S es hsound hcomplete r (nextCount n es.length q s) (lo+1)
        (row n es.length q s) hn hhi (by omega) hrt q (by omega) S _
        (row_new G S es seed s h hi hr1 he hsound hcomplete)
    constructor
    · intro a ha hlast
      by_cases htail : nextCount n es.length q s ≤ a
      · obtain ⟨v,hvlo,hvhi,he,hrec⟩ := hh.1 a htail hlast
        exact ⟨v,by omega,by omega,he,hrec⟩
      · have haq : a = q := by omega
        subst a
        have he : StateRecord.eligible G w S seed := by
          by_contra hno
          rw [hc,if_neg hno] at htail
          omega
        exact ⟨seed,by simp [seed],by simp [seed],he,hnew he⟩
    · intro v hvlo hvhi he
      by_cases hv : v.val = lo
      · have hvseed : v = seed := Fin.ext hv
        subst v
        have hnext : nextCount n es.length q s = q+1 := by rw [hc,if_pos he]
        have hcount := (count_bounds n es.length (nextCount n es.length q s) r (row n es.length q s)).1
        refine ⟨q,le_rfl,?_,hnew he⟩
        simp only [finalCount]; omega
      · obtain ⟨a,ha,hlast,hrec⟩ := hh.2 v (by omega) (by omega) he
        exact ⟨a,by omega,hlast,hrec⟩
end StableMSR.Recovery.Compiler.StateSeedSweep
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateSeedSweep
open ComponentMachine ComponentMemory

noncomputable def acceptedSeeds {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ)
    (S : Finset (Fin n)) (lo r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => lo ≤ v.val ∧ v.val < lo+r ∧ StateRecord.eligible G w S v)

lemma acceptedSeeds_succ {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ) (S : Finset (Fin n))
    (lo r : ℕ) (hlo : lo < n) :
    (acceptedSeeds G w S lo (r+1)).card =
      (if StateRecord.eligible G w S ⟨lo,hlo⟩ then 1 else 0) + (acceptedSeeds G w S (lo+1) r).card := by
  let seed : Fin n := ⟨lo,hlo⟩
  have hnot : seed ∉ acceptedSeeds G w S (lo+1) r := by simp [acceptedSeeds,seed]
  by_cases he : StateRecord.eligible G w S seed
  · have hset : acceptedSeeds G w S lo (r+1) = insert seed (acceptedSeeds G w S (lo+1) r) := by
      ext v
      simp only [acceptedSeeds,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
      constructor
      · rintro ⟨hl,hu,hv⟩
        by_cases hvl : v.val = lo
        · left; exact Fin.ext hvl
        · right; exact ⟨by omega,by omega,hv⟩
      · rintro (rfl|⟨hl,hu,hv⟩)
        · exact ⟨le_rfl,by dsimp [seed]; omega,he⟩
        · exact ⟨by omega,by omega,hv⟩
    rw [hset,Finset.card_insert_of_notMem hnot,if_pos he]; omega
  · have hset : acceptedSeeds G w S lo (r+1) = acceptedSeeds G w S (lo+1) r := by
      ext v
      simp only [acceptedSeeds,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨hl,hu,hv⟩
        have hvl : v.val ≠ lo := by intro hh; exact he (by simpa only [show v = seed from Fin.ext hh] using hv)
        exact ⟨by omega,by omega,hv⟩
      · rintro ⟨hl,hu,hv⟩; exact ⟨by omega,by omega,hv⟩
    rw [hset,if_neg he]; omega

lemma finalCount_exact {n w : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (r q lo : ℕ) (s : Store) (h : Input w S es s)
    (hi : s.ptrs 70 = (lo:ℤ)) (hb : lo+r ≤ n) (hr : StateRecord.Room n (q+r) es s) :
    finalCount n es.length q r s = q+(acceptedSeeds G w S lo r).card := by
  induction r generalizing q lo s with
  | zero => simp [finalCount,acceptedSeeds]; intros; omega
  | succ r ih =>
    let seed : Fin n := ⟨lo,by omega⟩
    have hr1 : StateRecord.Room n (q+1) es s := room_mono hr (by omega)
    have hn := row_input G S es seed s h hi hr1 hsound hcomplete
    have hc := nextCount_spec (q := q) G S es seed s h hi hsound hcomplete
    have hq' : nextCount n es.length q s ≤ q+1 := by rw [hc]; split_ifs <;> omega
    have hhi : (row n es.length q s).ptrs 70 = ((lo+1:ℕ):ℤ) := by rw [row_index,hi]; push_cast; rfl
    have hh := ih (nextCount n es.length q s) (lo+1) (row n es.length q s) hn hhi (by omega)
      (room_mono (row_room hr) (by omega))
    rw [finalCount,hh,hc,acceptedSeeds_succ G w S lo r (by omega)]
    exact Nat.add_assoc _ _ _

lemma acceptedSeeds_all {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ) (S : Finset (Fin n)) :
    acceptedSeeds G w S 0 n = Finset.univ.filter (StateRecord.eligible G w S) := by
  ext seed
  simp only [acceptedSeeds,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun h => h.2.2,fun h => ⟨Nat.zero_le _,by simpa using seed.isLt,h⟩⟩
end StableMSR.Recovery.Compiler.StateSeedSweep
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateSeedSweep
open ComponentMachine ComponentMemory

lemma setup_input {n w : ℕ} {S : Finset (Fin n)} {es : List (Fin n × Fin n)}
    {s : Store} (h : Input w S es s) : Input w S es (setup s) := by
  constructor <;> simp [setup,setPtr]
  all_goals first | exact h.edges | exact h.vertices | exact h.width | exact h.separator |
    exact h.encoding | exact h.separator_allowed | exact h.separator_component | exact h.separator_boundary |
    exact h.allowed_component | exact h.component_boundary | exact h.edges_allowed | exact h.edges_component | exact h.edges_boundary

lemma setup_room {n c : ℕ} {es : List (Fin n × Fin n)} {s : Store}
    (h : StateRecord.Room n c es s) : StateRecord.Room n c es (setup s) := by
  apply room_transfer h
  intro j hj
  have h70 : j ≠ 70 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
  have h71 : j ≠ 71 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
  simp [setup,setPtr,h70,h71]

/- One fixed program constructs exactly valid state records and covers every
eligible seed, while retaining all earlier records and charging all execution. -/
end StableMSR.Recovery.Compiler.StateSeedSweep
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateSeedSweep
open ComponentMachine ComponentMemory
lemma run_high (n m q r : ℕ) (s : Store) (j : ℕ) (hj : 71 < j) :
    (run n m q r s).ptrs j = s.ptrs j := by
  induction r generalizing q s with
  | zero => rfl
  | succ r ih => rw [run,ih,row_high n m q s j (by omega)]
lemma full_high (n m q : ℕ) (s : Store) (j : ℕ) (hj : 71 < j) :
    (eval n m q s).ptrs j = s.ptrs j := by
  rw [eval,run_high n m q n (setup s) j hj]
  simp [setup,setPtr,show j ≠ 70 by omega,show j ≠ 71 by omega]
lemma full_ptr (n m q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∈ ([2,3,4,5,6,43,50,51,61]:List ℕ)) : (eval n m q s).ptrs j = s.ptrs j := by
  rw [eval,run_ptr n m q n (setup s) j hj]
  have h70 : j ≠ 70 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
  have h71 : j ≠ 71 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
  simp [setup,setPtr,h70,h71]
lemma run_memory_frame {n w : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (r q lo : ℕ) (s : Store) (h : Input w S es s)
    (hi : s.ptrs 70 = (lo:ℤ)) (hb : lo+r ≤ n) (hr : StateRecord.Room n (q+r) es s)
    (x : ℤ) (ha : ∀ v : Fin n, x ≠ address (s.ptrs 4) v)
    (hc : ∀ v : Fin n, x ≠ address (s.ptrs 50) v)
    (hB : ∀ v : Fin n, x ≠ address (s.ptrs 51) v)
    (ht : ∀ a : Fin (q+r), ∀ j : Fin (n+n+1), x ≠ StateRecord.rowBase n a.val s+(j.val:ℤ)) :
    (run n es.length q r s).imem x = s.imem x := by
  induction r generalizing q lo s with
  | zero => rfl
  | succ r ih =>
    let seed : Fin n := ⟨lo,by omega⟩
    have hr1 : StateRecord.Room n (q+1) es s := room_mono hr (by omega)
    have hn := row_input G S es seed s h hi hr1 hsound hcomplete
    have hq : nextCount n es.length q s ≤ q+1 := by have := added_le n es.length (seeded s); dsimp [nextCount]; omega
    have hh := ih (nextCount n es.length q s) (lo+1) (row n es.length q s) hn
      (by rw [row_index,hi]; push_cast; rfl) (by omega) (room_mono (row_room hr) (by omega))
      (by simpa only [row_ptr n es.length q s 4 (by simp)] using ha)
      (by simpa only [row_ptr n es.length q s 50 (by simp)] using hc)
      (by simpa only [row_ptr n es.length q s 51 (by simp)] using hB)
      (by intro a j; simpa only [StateRecord.rowBase,row_ptr n es.length q s 61 (by simp)] using
        ht ⟨a.val,by have := a.isLt; omega⟩ j)
    refine hh.trans ?_
    exact StateRecord.memory_frame G w q S es seed (seeded s) (input_seed h seed hi) hsound hcomplete x ha hc hB
      (StateRecord.row_outside n q (seeded s) x (fun j => ht ⟨q,by omega⟩ j))
lemma full_memory_frame {n w q : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (es : List (Fin n × Fin n)) (s : Store) (h : Input w S es s)
    (hr : StateRecord.Room n (q+n) es s)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (x : ℤ) (ha : ∀ v : Fin n, x ≠ address (s.ptrs 4) v)
    (hc : ∀ v : Fin n, x ≠ address (s.ptrs 50) v)
    (hB : ∀ v : Fin n, x ≠ address (s.ptrs 51) v)
    (ht : ∀ a : Fin (q+n), ∀ j : Fin (n+n+1), x ≠ StateRecord.rowBase n a.val s+(j.val:ℤ)) :
    (eval n es.length q s).imem x = s.imem x := by
  exact run_memory_frame G S es hsound hcomplete n q 0 (setup s) (setup_input h)
    (by simp [setup,setPtr]) (by omega) (setup_room hr) x ha hc hB ht
end StableMSR.Recovery.Compiler.StateSeedSweep
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
namespace StableMSR.Recovery.Compiler.StateCatalog
open ComponentMachine

def tailOps : List Op := [.pointerAdd 3 3 75,.pointerInc 73]
def tail (s : Store) : Store := incPtr (setPtr s 3 (s.ptrs 3+s.ptrs 75)) 73
noncomputable def row (n m q : ℕ) (s : Store) : Store := tail (StateSeedSweep.eval n m q s)
noncomputable def nextCount (n m q : ℕ) (s : Store) : ℕ := StateSeedSweep.finalCount n m q n (StateSeedSweep.setup s)
def body : Cmd := .seq StateSeedSweep.command (opsCmd tailOps)
noncomputable def run (n m : ℕ) : ℕ → ℕ → Store → Store
  | _,0,s => s
  | q,M+1,s => run n m (nextCount n m q s) M (row n m q s)
noncomputable def finalCount (n m : ℕ) : ℕ → ℕ → Store → ℕ
  | q,0,_ => q
  | q,M+1,s => finalCount n m (nextCount n m q s) M (row n m q s)
noncomputable def loopCost (n m : ℕ) : ℕ → ℕ → Store → ℕ
  | _,0,_ => 2
  | q,M+1,s => StateSeedSweep.steps n m q s+3+loopCost n m (nextCount n m q s) M (row n m q s)
lemma row_imem (n m q : ℕ) (s : Store) : (row n m q s).imem = (StateSeedSweep.eval n m q s).imem := rfl
lemma row_ptr (n m q : ℕ) (s : Store) (j : ℕ)
    (hj : j ∈ ([2,4,5,6,43,50,51,61]:List ℕ)) : (row n m q s).ptrs j = s.ptrs j := by
  have h3 : j ≠ 3 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
  have h73 : j ≠ 73 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
  simp only [row,tail,incPtr,setPtr,Function.update_of_ne h3,Function.update_of_ne h73]
  exact StateSeedSweep.full_ptr n m q s j (by simp_all)
lemma row_high (n m q : ℕ) (s : Store) (j : ℕ) (hj : 71 < j) (hne : j ≠ 73) :
    (row n m q s).ptrs j = s.ptrs j := by
  simp only [row,tail,incPtr,setPtr,Function.update_of_ne hne,Function.update_of_ne (by omega : j ≠ 3)]
  exact StateSeedSweep.full_high n m q s j hj
lemma row_index (n m q : ℕ) (s : Store) : (row n m q s).ptrs 73 = s.ptrs 73+1 := by
  simp [row,tail,incPtr,setPtr,StateSeedSweep.full_high]
lemma row_cursor (n m q : ℕ) (s : Store) : (row n m q s).ptrs 3 = s.ptrs 3+s.ptrs 75 := by
  simp [row,tail,incPtr,setPtr,StateSeedSweep.full_high,StateSeedSweep.full_ptr]
lemma row_count (n m q : ℕ) (s : Store) (hq : s.ptrs 62 = (q:ℤ)) :
    (row n m q s).ptrs 62 = (nextCount n m q s:ℤ) := by
  exact StateSeedSweep.run_count n m q n (StateSeedSweep.setup s) (by simpa [StateSeedSweep.setup,setPtr] using hq)
lemma next_bounds (n m q : ℕ) (s : Store) : q ≤ nextCount n m q s ∧ nextCount n m q s ≤ q+n :=
  StateSeedSweep.count_bounds n m q n (StateSeedSweep.setup s)
lemma row_exec {N : ℕ} (d : Point N → Point N → ℝ) (n m q : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 62 = (q:ℤ)) :
    Executes d body s (row n m q s) (StateSeedSweep.steps n m q s+1) := by
  have ht : Executes d (opsCmd tailOps) (StateSeedSweep.eval n m q s) (row n m q s) 2 := by
    simpa [tailOps,row,tail,evalOps,Op.eval,setPtr,incPtr] using ops_exec d tailOps (StateSeedSweep.eval n m q s)
  convert Executes.seq (StateSeedSweep.exec d n m q s hn hm hq) ht using 1 <;> try rfl
  simp only [StateSeedSweep.steps]; omega
lemma loop_exec {N : ℕ} (d : Point N → Point N → ℝ) (n m q M : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 62 = (q:ℤ))
    (hstop : s.ptrs 73+(M:ℤ)-1 = s.ptrs 74) :
    Executes d (.whileDo (.pointerLE 73 74) body) s (run n m q M s) (loopCost n m q M s) := by
  induction M generalizing q s with
  | zero => apply Executes.while_false; simp only [Cond.test]; omega
  | succ M ih =>
    have hg : (Cond.pointerLE 73 74).test s := by simp only [Cond.test]; push_cast at hstop; omega
    have hh := Executes.while_true hg (row_exec d n m q s hn hm hq)
      (ih (nextCount n m q s) (row n m q s)
        (by rw [row_ptr n m q s 6 (by simp),hn]) (by rw [row_ptr n m q s 5 (by simp),hm])
        (row_count n m q s hq) (by rw [row_index,row_high n m q s 74 (by decide) (by decide)]; push_cast at hstop; omega))
    convert hh using 1 <;> try rfl
    simp only [loopCost]; omega
lemma run_count (n m q M : ℕ) (s : Store) (hq : s.ptrs 62 = (q:ℤ)) :
    (run n m q M s).ptrs 62 = (finalCount n m q M s:ℤ) := by
  induction M generalizing q s with
  | zero => exact hq
  | succ M ih => exact ih (nextCount n m q s) (row n m q s) (row_count n m q s hq)
lemma count_bounds (n m q M : ℕ) (s : Store) :
    q ≤ finalCount n m q M s ∧ finalCount n m q M s ≤ q+M*n := by
  induction M generalizing q s with
  | zero => simp [finalCount]
  | succ M ih =>
    have hh := ih (nextCount n m q s) (row n m q s)
    have hb := next_bounds n m q s
    exact ⟨hb.1.trans hh.1,hh.2.trans (by nlinarith)⟩
lemma loop_bound (n m q M : ℕ) (s : Store) :
    loopCost n m q M s ≤ M*(n*(n*(17*m+57)+17*m+4*(q+M*n)+116)+9)+2 := by
  induction M generalizing q s with
  | zero => simp [loopCost]
  | succ M ih =>
    have hh := ih (nextCount n m q s) (row n m q s)
    have hb := next_bounds n m q s
    have he : nextCount n m q s+M*n ≤ q+(M+1)*n := by nlinarith
    have hm1 := Nat.mul_le_mul_left n (show n*(17*m+57)+17*m+4*(nextCount n m q s+M*n)+116 ≤
      n*(17*m+57)+17*m+4*(q+(M+1)*n)+116 by omega)
    have hm2 := Nat.mul_le_mul_left M (Nat.add_le_add_right hm1 9)
    have hc := StateSeedSweep.steps_bound n m q s
    have he2 : q+n ≤ q+(M+1)*n := by nlinarith
    have hm3 := Nat.mul_le_mul_left n (show n*(17*m+57)+17*m+4*(q+n)+116 ≤
      n*(17*m+57)+17*m+4*(q+(M+1)*n)+116 by omega)
    simp only [loopCost]; nlinarith
lemma run_ptr (n m q M : ℕ) (s : Store) (j : ℕ)
    (hj : j ∈ ([2,4,5,6,43,50,51,61]:List ℕ)) : (run n m q M s).ptrs j = s.ptrs j := by
  induction M generalizing q s with
  | zero => rfl
  | succ M ih => rw [run,ih,row_ptr n m q s j hj]
lemma run_frame (n m q M : ℕ) (s : Store) : DataFrame s (run n m q M s) := by
  induction M generalizing q s with
  | zero => exact DataFrame.refl s
  | succ M ih =>
    have hh : DataFrame s (row n m q s) := StateSeedSweep.run_frame n m q n (StateSeedSweep.setup s)
    exact hh.trans (ih (nextCount n m q s) (row n m q s))
def setupOps : List Op := [.pointerConst 73 0,.pointerCopy 74 72,.pointerDec 74,.pointerCopy 75 6,.pointerInc 75]
def setup (s : Store) : Store := setPtr (setPtr (setPtr s 73 0) 74 (s.ptrs 72-1)) 75 (s.ptrs 6+1)
def command : Cmd := .seq (opsCmd setupOps) (.whileDo (.pointerLE 73 74) body)
noncomputable def eval (n m q M : ℕ) (s : Store) : Store := run n m q M (setup s)
noncomputable def steps (n m q M : ℕ) (s : Store) : ℕ := 6+loopCost n m q M (setup s)
noncomputable def program : MinSumFPT.Program := compile command 0
lemma program_length : program.length = 239 := by decide
lemma exec {N : ℕ} (d : Point N → Point N → ℝ) (n m q M : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 62 = (q:ℤ)) (hM : s.ptrs 72 = (M:ℤ)) :
    Executes d command s (eval n m q M s) (5+loopCost n m q M (setup s)) := by
  have hp : Executes d (opsCmd setupOps) s (setup s) 5 := by
    simpa [setupOps,setup,evalOps,Op.eval,setPtr,Function.update_idem] using ops_exec d setupOps s
  exact Executes.seq hp (loop_exec d n m q M (setup s)
    (by simpa [setup,setPtr] using hn) (by simpa [setup,setPtr] using hm)
    (by simpa [setup,setPtr] using hq) (by simp [setup,setPtr,hM]))
lemma steps_bound (n m q M : ℕ) (s : Store) :
    steps n m q M s ≤ M*(n*(n*(17*m+57)+17*m+4*(q+M*n)+116)+9)+8 := by
  have hh := loop_bound n m q M (setup s); dsimp [steps]; omega
lemma machine_execution {N : ℕ} (d : Point N → Point N → ℝ) (n m q M : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hm : s.ptrs 5 = (m:ℤ)) (hq : s.ptrs 62 = (q:ℤ)) (hM : s.ptrs 72 = (M:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[steps n m q M s] (s.state 0 work) =
      (eval n m q M s).haltedState command.size (work+steps n m q M s) 0 := by
  simpa only [program,steps,show 5+loopCost n m q M (setup s)+1 = 6+loopCost n m q M (setup s) by omega,
    show work+(5+loopCost n m q M (setup s))+1 = work+(6+loopCost n m q M (setup s)) by omega] using
      compile_halts (exec d n m q M s hn hm hq hM) ω work 0
end StableMSR.Recovery.Compiler.StateCatalog
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateCatalog
open ComponentMachine ComponentMemory

def atSeparator (n : ℕ) (s : Store) (a : ℕ) : Store := setPtr s 3 (s.ptrs 3+(a:ℤ)*((n:ℤ)+1))
lemma at_zero (n : ℕ) (s : Store) : atSeparator n s 0 = s := by
  simp [atSeparator,setPtr,Function.update_eq_self]
lemma at_ptr (n : ℕ) (s : Store) (a j : ℕ) (hj : j ≠ 3) : (atSeparator n s a).ptrs j = s.ptrs j := by
  simp [atSeparator,setPtr,hj]
lemma at_source (n : ℕ) (s : Store) (a : ℕ) : (atSeparator n s a).ptrs 3 = s.ptrs 3+(a:ℤ)*((n:ℤ)+1) := by
  simp [atSeparator,setPtr]
/- Ordinary input and free-space contracts at every catalog position. -/
structure Ready {n : ℕ} (w q : ℕ) (es : List (Fin n × Fin n))
    (Ss : ℕ → Finset (Fin n)) (M : ℕ) (s : Store) : Prop where
  inputs : ∀ a, a < M → StateSeedSweep.Input w (Ss a) es (atSeparator n s a)
  rooms : ∀ a, a < M → StateRecord.Room n (q+M*n) es (atSeparator n s a)
lemma head_input {n w q M : ℕ} {es : List (Fin n × Fin n)} {Ss : ℕ → Finset (Fin n)} {s : Store}
    (h : Ready w q es Ss (M+1) s) : StateSeedSweep.Input w (Ss 0) es s := by
  simpa only [at_zero] using h.inputs 0 (by omega)
lemma head_room {n w q M : ℕ} {es : List (Fin n × Fin n)} {Ss : ℕ → Finset (Fin n)} {s : Store}
    (h : Ready w q es Ss (M+1) s) : StateRecord.Room n (q+n) es s := by
  have hh : StateRecord.Room n (q+(M+1)*n) es s := by simpa only [at_zero] using h.rooms 0 (by omega)
  exact StateSeedSweep.room_mono hh (by nlinarith)
lemma row_at_ptr {n m q : ℕ} (s : Store) (hs : s.ptrs 75 = (n:ℤ)+1) (a j : ℕ)
    (hj : j ∈ ([2,3,4,5,6,43,50,51,61]:List ℕ)) :
    (atSeparator n (row n m q s) a).ptrs j = (atSeparator n s (a+1)).ptrs j := by
  by_cases h3 : j = 3
  · subst j; rw [at_source,at_source,row_cursor,hs]; push_cast; ring
  · rw [at_ptr n _ a j h3,at_ptr n _ (a+1) j h3,row_ptr n m q s j (by simp_all)]
lemma row_input {n w q M : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n))
    (Ss : ℕ → Finset (Fin n)) (s : Store) (h : Ready w q es Ss (M+1) s)
    (hs : s.ptrs 75 = (n:ℤ)+1)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    Ready w (nextCount n es.length q s) es (fun a => Ss (a+1)) M (row n es.length q s) := by
  have hi := head_input h
  have hr := head_room h
  have hp (a j : ℕ) (hj : j ∈ ([2,3,4,5,6,43,50,51,61]:List ℕ)) := row_at_ptr (m := es.length) (q := q) s hs a j hj
  have hh := StateSeedSweep.run_preserves G (Ss 0) es hsound hcomplete n q 0 (StateSeedSweep.setup s)
    (StateSeedSweep.setup_input hi) (by simp [StateSeedSweep.setup,setPtr]) (by omega) (StateSeedSweep.setup_room hr)
  constructor
  · intro a ha
    have hin := h.inputs (a+1) (by omega)
    have hroom := h.rooms (a+1) (by omega)
    have hmask : Bitmap (row n es.length q s).imem ((atSeparator n s (a+1)).ptrs 3) (Ss (a+1)) := by
      intro v
      have heq := StateSeedSweep.full_memory_frame G (Ss 0) es s hi hr hsound hcomplete
        (address ((atSeparator n s (a+1)).ptrs 3) v)
        (by simpa only [at_ptr n s (a+1) 4 (by decide)] using hin.separator_allowed v)
        (by simpa only [at_ptr n s (a+1) 50 (by decide)] using hin.separator_component v)
        (by simpa only [at_ptr n s (a+1) 51 (by decide)] using hin.separator_boundary v)
        (by intro b j; exact hroom.separator ⟨b.val,by have := b.isLt; nlinarith⟩ j v)
      exact heq.trans (hin.separator v)
    constructor
    · rw [hp a 5 (by simp)]; exact hin.edges
    · rw [hp a 6 (by simp)]; exact hin.vertices
    · rw [hp a 43 (by simp)]; exact hin.width
    · rw [hp a 3 (by simp)]; exact hmask
    · rw [hp a 2 (by simp)]
      have he := hh.1.encoding
      rw [StateSeedSweep.run_ptr n es.length q n (StateSeedSweep.setup s) 2 (by simp)] at he
      exact he
    · rw [hp a 3 (by simp),hp a 4 (by simp)]; exact hin.separator_allowed
    · rw [hp a 3 (by simp),hp a 50 (by simp)]; exact hin.separator_component
    · rw [hp a 3 (by simp),hp a 51 (by simp)]; exact hin.separator_boundary
    · rw [hp a 4 (by simp),hp a 50 (by simp)]; exact hin.allowed_component
    · rw [hp a 50 (by simp),hp a 51 (by simp)]; exact hin.component_boundary
    · rw [hp a 2 (by simp),hp a 4 (by simp)]; exact hin.edges_allowed
    · rw [hp a 2 (by simp),hp a 50 (by simp)]; exact hin.edges_component
    · rw [hp a 2 (by simp),hp a 51 (by simp)]; exact hin.edges_boundary
  · intro a ha
    have hcap : nextCount n es.length q s+M*n ≤ q+(M+1)*n := by have := next_bounds n es.length q s; nlinarith
    exact StateSeedSweep.room_transfer (StateSeedSweep.room_mono (h.rooms (a+1) (by omega)) hcap)
      (fun j hj => hp a j (by simp_all; omega))

lemma row_old {n w q M : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n))
    (Ss : ℕ → Finset (Fin n)) (s : Store) (h : Ready w q es Ss (M+1) s)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (a : Fin q) (j : Fin (n+n+1)) :
    (row n es.length q s).imem (StateRecord.rowBase n a.val s+(j.val:ℤ)) =
      s.imem (StateRecord.rowBase n a.val s+(j.val:ℤ)) := by
  exact (StateSeedSweep.run_preserves G (Ss 0) es hsound hcomplete n q 0 (StateSeedSweep.setup s)
    (StateSeedSweep.setup_input (head_input h)) (by simp [StateSeedSweep.setup,setPtr]) (by omega)
    (StateSeedSweep.setup_room (head_room h))).2 a j
lemma row_coverage {n w q M : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n))
    (Ss : ℕ → Finset (Fin n)) (s : Store) (h : Ready w q es Ss (M+1) s)
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es) :
    (∀ a, q ≤ a → a < nextCount n es.length q s → ∃ seed : Fin n,
      StateRecord.eligible G w (Ss 0) seed ∧ StateSeedSweep.Record (row n es.length q s) a (Ss 0)
        (ComponentState.outsideComponent G (Ss 0) seed)) ∧
    (∀ seed : Fin n, StateRecord.eligible G w (Ss 0) seed → ∃ a,
      q ≤ a ∧ a < nextCount n es.length q s ∧ StateSeedSweep.Record (row n es.length q s) a (Ss 0)
        (ComponentState.outsideComponent G (Ss 0) seed)) := by
  have hh := StateSeedSweep.run_coverage G (Ss 0) es hsound hcomplete n q 0 (StateSeedSweep.setup s)
    (StateSeedSweep.setup_input (head_input h)) (by simp [StateSeedSweep.setup,setPtr]) (by omega)
    (StateSeedSweep.setup_room (head_room h))
  have transfer (a : ℕ) (seed : Fin n) (hr : StateSeedSweep.Record (StateSeedSweep.eval n es.length q s) a (Ss 0)
      (ComponentState.outsideComponent G (Ss 0) seed)) :
      StateSeedSweep.Record (row n es.length q s) a (Ss 0) (ComponentState.outsideComponent G (Ss 0) seed) := by
    simpa only [StateSeedSweep.Record,StateRecord.rowBase,row_ptr n es.length q s 61 (by simp),
      StateSeedSweep.full_ptr n es.length q s 61 (by simp),row_imem] using hr
  constructor
  · intro a ha hb
    obtain ⟨seed,_,_,he,hrec⟩ := hh.1 a ha hb
    exact ⟨seed,he,transfer a seed hrec⟩
  · intro seed he
    obtain ⟨a,ha,hb,hrec⟩ := hh.2 seed (by omega) (by simpa using seed.isLt) he
    exact ⟨a,ha,hb,transfer a seed hrec⟩
end StableMSR.Recovery.Compiler.StateCatalog
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateCatalog
open ComponentMachine ComponentMemory

lemma run_old {n w : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (M q : ℕ) (Ss : ℕ → Finset (Fin n)) (s : Store) (h : Ready w q es Ss M s)
    (hs : s.ptrs 75 = (n:ℤ)+1) (a : Fin q) (j : Fin (n+n+1)) :
    (run n es.length q M s).imem (StateRecord.rowBase n a.val s+(j.val:ℤ)) =
      s.imem (StateRecord.rowBase n a.val s+(j.val:ℤ)) := by
  induction M generalizing q Ss s with
  | zero => rfl
  | succ M ih =>
    have hq := (next_bounds n es.length q s).1
    have ht := row_input G es Ss s h hs hsound hcomplete
    have hh := ih (nextCount n es.length q s) (fun i => Ss (i+1)) (row n es.length q s) ht
      (by rw [row_high n es.length q s 75 (by decide) (by decide),hs]) ⟨a.val,lt_of_lt_of_le a.isLt hq⟩
    have hbase : StateRecord.rowBase n a.val (row n es.length q s) = StateRecord.rowBase n a.val s := by
      simp only [StateRecord.rowBase,row_ptr n es.length q s 61 (by simp)]
    rw [hbase] at hh
    exact hh.trans (row_old G es Ss s h hsound hcomplete a j)
lemma run_record {n w : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (M q : ℕ) (Ss : ℕ → Finset (Fin n)) (s : Store) (h : Ready w q es Ss M s)
    (hs : s.ptrs 75 = (n:ℤ)+1) (a : ℕ) (ha : a < q) (S C : Finset (Fin n))
    (hr : StateSeedSweep.Record s a S C) : StateSeedSweep.Record (run n es.length q M s) a S C :=
  StateSeedSweep.record_transfer ha (run_ptr n es.length q M s 61 (by simp))
    (run_old G es hsound hcomplete M q Ss s h hs) hr

lemma run_coverage {n w : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (M q : ℕ) (Ss : ℕ → Finset (Fin n)) (s : Store) (h : Ready w q es Ss M s)
    (hs : s.ptrs 75 = (n:ℤ)+1) :
    (∀ a, q ≤ a → a < finalCount n es.length q M s → ∃ i < M, ∃ seed : Fin n,
      StateRecord.eligible G w (Ss i) seed ∧ StateSeedSweep.Record (run n es.length q M s) a (Ss i)
        (ComponentState.outsideComponent G (Ss i) seed)) ∧
    (∀ i < M, ∀ seed : Fin n, StateRecord.eligible G w (Ss i) seed → ∃ a,
      q ≤ a ∧ a < finalCount n es.length q M s ∧ StateSeedSweep.Record (run n es.length q M s) a (Ss i)
        (ComponentState.outsideComponent G (Ss i) seed)) := by
  induction M generalizing q Ss s with
  | zero => constructor <;> intros <;> simp_all [finalCount] <;> omega
  | succ M ih =>
    have ht := row_input G es Ss s h hs hsound hcomplete
    have hst : (row n es.length q s).ptrs 75 = (n:ℤ)+1 := by rw [row_high n es.length q s 75 (by decide) (by decide),hs]
    have hh := ih (nextCount n es.length q s) (fun i => Ss (i+1)) (row n es.length q s) ht hst
    have hc := row_coverage G es Ss s h hsound hcomplete
    have hq := (next_bounds n es.length q s).1
    have hfinal := (count_bounds n es.length (nextCount n es.length q s) M (row n es.length q s)).1
    constructor
    · intro a ha hb
      by_cases htail : nextCount n es.length q s ≤ a
      · obtain ⟨i,hi,seed,he,hrec⟩ := hh.1 a htail hb
        exact ⟨i+1,by omega,seed,he,hrec⟩
      · obtain ⟨seed,he,hrec⟩ := hc.1 a ha (by omega)
        exact ⟨0,by omega,seed,he,run_record G es hsound hcomplete M (nextCount n es.length q s)
          (fun i => Ss (i+1)) (row n es.length q s) ht hst a (by omega) _ _ hrec⟩
    · intro i hi seed he
      cases i with
      | zero =>
        obtain ⟨a,ha,hb,hrec⟩ := hc.2 seed he
        exact ⟨a,ha,lt_of_lt_of_le hb hfinal,run_record G es hsound hcomplete M (nextCount n es.length q s)
          (fun i => Ss (i+1)) (row n es.length q s) ht hst a hb _ _ hrec⟩
      | succ i =>
        obtain ⟨a,ha,hb,hrec⟩ := hh.2 i (by omega) seed he
        exact ⟨a,le_trans hq ha,hb,hrec⟩

lemma run_memory_frame {n w : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (M q : ℕ) (Ss : ℕ → Finset (Fin n)) (s : Store) (h : Ready w q es Ss M s)
    (hs : s.ptrs 75 = (n:ℤ)+1) (x : ℤ)
    (ha : ∀ v : Fin n, x ≠ address (s.ptrs 4) v)
    (hc : ∀ v : Fin n, x ≠ address (s.ptrs 50) v)
    (hb : ∀ v : Fin n, x ≠ address (s.ptrs 51) v)
    (hr : ∀ a : Fin (q+M*n), ∀ j : Fin (n+n+1), x ≠ StateRecord.rowBase n a.val s+(j.val:ℤ)) :
    (run n es.length q M s).imem x = s.imem x := by
  induction M generalizing q Ss s with
  | zero => rfl
  | succ M ih =>
    have ht := row_input G es Ss s h hs hsound hcomplete
    have hst : (row n es.length q s).ptrs 75 = (n:ℤ)+1 := by rw [row_high n es.length q s 75 (by decide) (by decide),hs]
    have hq := (next_bounds n es.length q s).2
    have hh := ih (nextCount n es.length q s) (fun i => Ss (i+1)) (row n es.length q s) ht hst
      (by simpa only [row_ptr n es.length q s 4 (by simp)] using ha)
      (by simpa only [row_ptr n es.length q s 50 (by simp)] using hc)
      (by simpa only [row_ptr n es.length q s 51 (by simp)] using hb)
      (by intro a j; simpa only [StateRecord.rowBase,row_ptr n es.length q s 61 (by simp)] using
        hr ⟨a.val,by have := a.isLt; nlinarith⟩ j)
    refine hh.trans ?_
    exact StateSeedSweep.full_memory_frame G (Ss 0) es s (head_input h) (head_room h) hsound hcomplete x ha hc hb
      (fun a j => hr ⟨a.val,by have := a.isLt; nlinarith⟩ j)

lemma run_catalog {n w : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (M q : ℕ) (Ss : ℕ → Finset (Fin n)) (s : Store) (h : Ready w q es Ss M s)
    (hs : s.ptrs 75 = (n:ℤ)+1) (i : ℕ) (hi : i < M) :
    Bitmap (run n es.length q M s).imem (s.ptrs 3+(i:ℤ)*((n:ℤ)+1)) (Ss i) := by
  have hin := h.inputs i hi
  have hroom := h.rooms i hi
  intro v
  have hh := run_memory_frame G es hsound hcomplete M q Ss s h hs
    (address ((atSeparator n s i).ptrs 3) v)
    (by simpa only [at_ptr n s i 4 (by decide)] using hin.separator_allowed v)
    (by simpa only [at_ptr n s i 50 (by decide)] using hin.separator_component v)
    (by simpa only [at_ptr n s i 51 (by decide)] using hin.separator_boundary v)
    (fun a j => hroom.separator a j v)
  exact hh.trans (hin.separator v)
end StableMSR.Recovery.Compiler.StateCatalog
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateCatalog
open ComponentMachine ComponentMemory

lemma finalCount_exact {n w : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (M q : ℕ) (Ss : ℕ → Finset (Fin n)) (s : Store) (h : Ready w q es Ss M s)
    (hs : s.ptrs 75 = (n:ℤ)+1) :
    finalCount n es.length q M s = q+∑ i ∈ Finset.range M, (Finset.univ.filter (StateRecord.eligible G w (Ss i))).card := by
  induction M generalizing q Ss s with
  | zero => simp [finalCount]
  | succ M ih =>
    have ht := row_input G es Ss s h hs hsound hcomplete
    have hh := ih (nextCount n es.length q s) (fun i => Ss (i+1)) (row n es.length q s) ht
      (by rw [row_high n es.length q s 75 (by decide) (by decide),hs])
    have hc := StateSeedSweep.finalCount_exact G (Ss 0) es hsound hcomplete n q 0 (StateSeedSweep.setup s)
      (StateSeedSweep.setup_input (head_input h)) (by simp [StateSeedSweep.setup,setPtr]) (by omega)
      (StateSeedSweep.setup_room (head_room h))
    rw [StateSeedSweep.acceptedSeeds_all] at hc
    rw [finalCount,hh,show nextCount n es.length q s = q+(Finset.univ.filter (StateRecord.eligible G w (Ss 0))).card from hc,
      Finset.sum_range_succ']
    omega

lemma run_encoding {n w : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n))
    (hsound : ∀ e ∈ es, G.Adj e.1 e.2) (hcomplete : ∀ u v, G.Adj u v → (u,v) ∈ es)
    (M q : ℕ) (Ss : ℕ → Finset (Fin n)) (s : Store) (h : Ready w q es Ss M s)
    (hs : s.ptrs 75 = (n:ℤ)+1) (he : EdgeEncoding s.imem (s.ptrs 2) es) :
    EdgeEncoding (run n es.length q M s).imem (s.ptrs 2) es := by
  cases M with
  | zero => exact he
  | succ M =>
    have hin := head_input h
    have hr : StateRecord.Room n (q+(M+1)*n) es s := by simpa only [at_zero] using h.rooms 0 (by omega)
    intro a ha
    have hleft := run_memory_frame G es hsound hcomplete (M+1) q Ss s h hs _
      (fun v => (hin.edges_allowed a ha v).1) (fun v => (hin.edges_component a ha v).1)
      (fun v => (hin.edges_boundary a ha v).1) (fun r j => (hr.edges r j a ha).1)
    have hright := run_memory_frame G es hsound hcomplete (M+1) q Ss s h hs _
      (fun v => (hin.edges_allowed a ha v).2) (fun v => (hin.edges_component a ha v).2)
      (fun v => (hin.edges_boundary a ha v).2) (fun r j => (hr.edges r j a ha).2)
    rw [hleft,hright]; exact he a ha

lemma setup_ready {n w q M : ℕ} {es : List (Fin n × Fin n)} {Ss : ℕ → Finset (Fin n)} {s : Store}
    (h : Ready w q es Ss M s) : Ready w q es Ss M (setup s) := by
  constructor
  · intro a ha
    have hh := h.inputs a ha
    constructor
    · simpa [atSeparator,setup,setPtr] using hh.edges
    · simpa [atSeparator,setup,setPtr] using hh.vertices
    · simpa [atSeparator,setup,setPtr] using hh.width
    · simpa [atSeparator,setup,setPtr] using hh.separator
    · simpa [atSeparator,setup,setPtr] using hh.encoding
    · simpa [atSeparator,setup,setPtr] using hh.separator_allowed
    · simpa [atSeparator,setup,setPtr] using hh.separator_component
    · simpa [atSeparator,setup,setPtr] using hh.separator_boundary
    · simpa [atSeparator,setup,setPtr] using hh.allowed_component
    · simpa [atSeparator,setup,setPtr] using hh.component_boundary
    · simpa [atSeparator,setup,setPtr] using hh.edges_allowed
    · simpa [atSeparator,setup,setPtr] using hh.edges_component
    · simpa [atSeparator,setup,setPtr] using hh.edges_boundary
  · intro a ha
    apply StateSeedSweep.room_transfer (h.rooms a ha)
    intro j hj
    have h73 : j ≠ 73 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
    have h74 : j ≠ 74 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
    have h75 : j ≠ 75 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
    by_cases h3 : j = 3 <;> simp [atSeparator,setup,setPtr,h3,h73,h74,h75]
lemma full_ptr (n m q M : ℕ) (s : Store) (j : ℕ)
    (hj : j ∈ ([2,4,5,6,43,50,51,61]:List ℕ)) : (eval n m q M s).ptrs j = s.ptrs j := by
  rw [eval,run_ptr n m q M (setup s) j hj]
  have h73 : j ≠ 73 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
  have h74 : j ≠ 74 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
  have h75 : j ≠ 75 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
  simp [setup,setPtr,h73,h74,h75]
end StableMSR.Recovery.Compiler.StateCatalog
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateCatalog
open ComponentMachine ComponentMemory

/- A concrete nested catalog/seed loop constructs every eligible state pair. -/
end StableMSR.Recovery.Compiler.StateCatalog
/- Contiguous layout and executed allocator. These derive all separation
conditions from adjacent graph/catalog arrays. Generating those arrays from
canonical recovery input and composing their generation remain open. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateCatalogLayout
open ComponentMachine ComponentMemory

/- Consecutive regions: arc endpoints, catalog, three masks, state records. -/
def catalogBase (b : ℤ) (m : ℕ) : ℤ := b+2*(m:ℤ)
def workBase (b : ℤ) (m M n : ℕ) : ℤ := catalogBase b m+(M:ℤ)*((n:ℤ)+1)
def tableBase (b : ℤ) (m M n : ℕ) : ℤ := workBase b m M n+3*(n:ℤ)
def endAddress (b : ℤ) (m M n : ℕ) : ℤ := tableBase b m M n+(M:ℤ)*(n:ℤ)*(2*(n:ℤ)+1)

lemma catalog_cell_lt_work (b : ℤ) (m M n a v : ℕ) (ha : a < M) (hv : v < n) :
    catalogBase b m+(a:ℤ)*((n:ℤ)+1)+(v:ℤ) < workBase b m M n := by
  have ha' : (a:ℤ)+1 ≤ (M:ℤ) := by omega
  have hv' : (v:ℤ) < (n:ℤ) := by omega
  dsimp [workBase]; nlinarith
lemma edge_cell_lt_catalog (b : ℤ) (m a : ℕ) (ha : a < m) :
    b+2*(a:ℤ) < catalogBase b m ∧ b+2*(a:ℤ)+1 < catalogBase b m := by
  have ha' : (a:ℤ)+1 ≤ (m:ℤ) := by omega
  dsimp [catalogBase]; omega
lemma catalog_le_work (b : ℤ) (m M n : ℕ) : catalogBase b m ≤ workBase b m M n := by
  have hh : 0 ≤ (M:ℤ)*((n:ℤ)+1) := by positivity
  dsimp [workBase]; omega

/- All separation obligations of the nested state enumerator follow from
this numerical layout. Only the actual graph and catalog contents are inputs. -/
theorem ready_of_contiguous_layout {n w M : ℕ} (b : ℤ) (es : List (Fin n × Fin n))
    (Ss : ℕ → Finset (Fin n)) (s : Store)
    (h2 : s.ptrs 2 = b) (h3 : s.ptrs 3 = catalogBase b es.length)
    (h4 : s.ptrs 4 = workBase b es.length M n)
    (h50 : s.ptrs 50 = workBase b es.length M n+(n:ℤ))
    (h51 : s.ptrs 51 = workBase b es.length M n+2*(n:ℤ))
    (h61 : s.ptrs 61 = tableBase b es.length M n)
    (hm : s.ptrs 5 = (es.length:ℤ)) (hn : s.ptrs 6 = (n:ℤ)) (hw : s.ptrs 43 = (w:ℤ))
    (he : EdgeEncoding s.imem b es)
    (hcat : ∀ a < M, Bitmap s.imem (catalogBase b es.length+(a:ℤ)*((n:ℤ)+1)) (Ss a)) :
    StateCatalog.Ready w 0 es Ss M s := by
  let A := workBase b es.length M n
  have catlt (a : ℕ) (ha : a < M) (v : Fin n) :
      catalogBase b es.length+(a:ℤ)*((n:ℤ)+1)+(v.val:ℤ) < A :=
    catalog_cell_lt_work b es.length M n a v.val ha v.isLt
  have edgeLt (a : ℕ) (ha : a < es.length) : b+2*(a:ℤ) < A ∧ b+2*(a:ℤ)+1 < A :=
    ⟨lt_of_lt_of_le (edge_cell_lt_catalog b es.length a ha).1 (catalog_le_work b es.length M n),
     lt_of_lt_of_le (edge_cell_lt_catalog b es.length a ha).2 (catalog_le_work b es.length M n)⟩
  have slotge (r j : ℕ) : A+3*(n:ℤ) ≤ tableBase b es.length M n+(r:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j:ℤ) := by
    have hh : 0 ≤ (r:ℤ)*((n:ℤ)+(n:ℤ)+1) := by positivity
    dsimp [tableBase,A]; omega
  constructor
  · intro a ha
    constructor
    · simpa [StateCatalog.atSeparator,setPtr] using hm
    · simpa [StateCatalog.atSeparator,setPtr] using hn
    · simpa [StateCatalog.atSeparator,setPtr] using hw
    · simpa [StateCatalog.atSeparator,setPtr,h3] using hcat a ha
    · simpa [StateCatalog.atSeparator,setPtr,h2] using he
    · intro v u
      have hh := catlt a ha v
      simp only [StateCatalog.atSeparator,setPtr,Function.update_self,Function.update_of_ne (by decide : 4 ≠ 3),address,h3,h4]
      change catalogBase b es.length+(a:ℤ)*((n:ℤ)+1)+(v.val:ℤ) ≠ A+(u.val:ℤ)
      omega
    · intro v u
      have hh := catlt a ha v
      simp only [StateCatalog.atSeparator,setPtr,Function.update_self,Function.update_of_ne (by decide : 50 ≠ 3),address,h3,h50]
      change catalogBase b es.length+(a:ℤ)*((n:ℤ)+1)+(v.val:ℤ) ≠ A+(n:ℤ)+(u.val:ℤ)
      omega
    · intro v u
      have hh := catlt a ha v
      simp only [StateCatalog.atSeparator,setPtr,Function.update_self,Function.update_of_ne (by decide : 51 ≠ 3),address,h3,h51]
      change catalogBase b es.length+(a:ℤ)*((n:ℤ)+1)+(v.val:ℤ) ≠ A+2*(n:ℤ)+(u.val:ℤ)
      omega
    · intro v u
      simp [StateCatalog.atSeparator,setPtr,address,h4,h50]
      have := v.isLt; omega
    · intro v u
      simp [StateCatalog.atSeparator,setPtr,address,h50,h51]
      have := v.isLt; omega
    · intro j hj v
      have hh := edgeLt j hj
      simp only [StateCatalog.atSeparator,setPtr,Function.update_of_ne (by decide : 2 ≠ 3),Function.update_of_ne (by decide : 4 ≠ 3),address,h2,h4]
      change b+2*(j:ℤ) ≠ A+(v.val:ℤ) ∧ b+2*(j:ℤ)+1 ≠ A+(v.val:ℤ)
      constructor <;> omega
    · intro j hj v
      have hh := edgeLt j hj
      simp only [StateCatalog.atSeparator,setPtr,Function.update_of_ne (by decide : 2 ≠ 3),Function.update_of_ne (by decide : 50 ≠ 3),address,h2,h50]
      change b+2*(j:ℤ) ≠ A+(n:ℤ)+(v.val:ℤ) ∧ b+2*(j:ℤ)+1 ≠ A+(n:ℤ)+(v.val:ℤ)
      constructor <;> omega
    · intro j hj v
      have hh := edgeLt j hj
      simp only [StateCatalog.atSeparator,setPtr,Function.update_of_ne (by decide : 2 ≠ 3),Function.update_of_ne (by decide : 51 ≠ 3),address,h2,h51]
      change b+2*(j:ℤ) ≠ A+2*(n:ℤ)+(v.val:ℤ) ∧ b+2*(j:ℤ)+1 ≠ A+2*(n:ℤ)+(v.val:ℤ)
      constructor <;> omega
  · intro a ha
    constructor
    · intro r j v
      have hh := catlt a ha v
      have ht := slotge r.val j.val
      simp [StateCatalog.atSeparator,setPtr,StateRecord.rowBase,address,h3,h61]
      omega
    · intro r j v
      have ht := slotge r.val j.val
      have hv := v.isLt
      simp [StateCatalog.atSeparator,setPtr,StateRecord.rowBase,address,h4,h61]
      change A+(v.val:ℤ) ≠ tableBase b es.length M n+(r.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ)
      omega
    · intro r j v
      have ht := slotge r.val j.val
      have hv := v.isLt
      simp [StateCatalog.atSeparator,setPtr,StateRecord.rowBase,address,h50,h61]
      change A+(n:ℤ)+(v.val:ℤ) ≠ tableBase b es.length M n+(r.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ)
      omega
    · intro r j v
      have ht := slotge r.val j.val
      have hv := v.isLt
      simp [StateCatalog.atSeparator,setPtr,StateRecord.rowBase,address,h51,h61]
      change A+2*(n:ℤ)+(v.val:ℤ) ≠ tableBase b es.length M n+(r.val:ℤ)*((n:ℤ)+(n:ℤ)+1)+(j.val:ℤ)
      omega
    · intro r j a' ha'
      have hh := edgeLt a' ha'
      have ht := slotge r.val j.val
      simp [StateCatalog.atSeparator,setPtr,StateRecord.rowBase,h2,h61]
      constructor <;> omega

/- Exact reserved extent, independent of initial memory contents. -/
theorem allocated_extent (b : ℤ) (m M n : ℕ) :
    endAddress b m M n-b = 2*(m:ℤ)+(M:ℤ)*((n:ℤ)+1)+3*(n:ℤ)+(M:ℤ)*(n:ℤ)*(2*(n:ℤ)+1) := by
  dsimp [endAddress,tableBase,workBase,catalogBase]; ring
end StableMSR.Recovery.Compiler.StateCatalogLayout

set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateCatalogLayout
open ComponentMachine ComponentMemory

def saveOps : List Op := [.pointerCopy 76 2,.pointerCopy 77 5,.pointerCopy 2 3,.pointerCopy 5 72]
def saved (s : Store) : Store := setPtr (setPtr (setPtr (setPtr s 76 (s.ptrs 2)) 77 (s.ptrs 5)) 2 (s.ptrs 3)) 5 (s.ptrs 72)
def finishOps : List Op := [.pointerCopy 2 76,.pointerCopy 5 77,.pointerAdd 50 4 6,.pointerAdd 51 50 6,.pointerAdd 61 51 6,.pointerConst 62 0]
def finished (s : Store) : Store := setPtr (setPtr (setPtr (setPtr (setPtr (setPtr s 2 (s.ptrs 76)) 5 (s.ptrs 77))
  50 (s.ptrs 4+s.ptrs 6)) 51 (s.ptrs 4+s.ptrs 6+s.ptrs 6)) 61 (s.ptrs 4+s.ptrs 6+s.ptrs 6+s.ptrs 6)) 62 0
def command : Cmd := .seq (opsCmd saveOps) (.seq TableAppend.seekCmd (opsCmd finishOps))
def allocated (M : ℕ) (s : Store) : Store := finished (TableAppend.seekEval M (saved s))
lemma allocation_exec {N : ℕ} (d : Point N → Point N → ℝ) (M : ℕ) (s : Store)
    (hM : s.ptrs 72 = (M:ℤ)) : Executes d command s (allocated M s) (4*M+18) := by
  have hs : Executes d (opsCmd saveOps) s (saved s) 4 := by
    simpa [saveOps,saved,evalOps,Op.eval,setPtr] using ops_exec d saveOps s
  have hf : Executes d (opsCmd finishOps) (TableAppend.seekEval M (saved s)) (allocated M s) 6 := by
    simpa [finishOps,allocated,finished,evalOps,Op.eval,setPtr] using ops_exec d finishOps (TableAppend.seekEval M (saved s))
  convert Executes.seq hs (Executes.seq (TableAppend.seek_exec d M (saved s) (by simpa [saved,setPtr] using hM)) hf) using 1 <;> try rfl
  omega
lemma allocated_imem (M : ℕ) (s : Store) : (allocated M s).imem = s.imem := TableAppend.seek_imem M (saved s)
lemma allocated_frame (M : ℕ) (s : Store) : DataFrame s (allocated M s) := TableAppend.seek_frame M (saved s)
lemma allocated_metadata (n M : ℕ) (s : Store) (hn : s.ptrs 6 = (n:ℤ)) :
    (allocated M s).ptrs 2 = s.ptrs 2 ∧ (allocated M s).ptrs 3 = s.ptrs 3 ∧
    (allocated M s).ptrs 5 = s.ptrs 5 ∧ (allocated M s).ptrs 6 = (n:ℤ) ∧
    (allocated M s).ptrs 43 = s.ptrs 43 ∧ (allocated M s).ptrs 72 = s.ptrs 72 ∧
    (allocated M s).ptrs 4 = s.ptrs 3+(M:ℤ)*((n:ℤ)+1) ∧
    (allocated M s).ptrs 50 = s.ptrs 3+(M:ℤ)*((n:ℤ)+1)+(n:ℤ) ∧
    (allocated M s).ptrs 51 = s.ptrs 3+(M:ℤ)*((n:ℤ)+1)+2*(n:ℤ) ∧
    (allocated M s).ptrs 61 = s.ptrs 3+(M:ℤ)*((n:ℤ)+1)+3*(n:ℤ) ∧
    (allocated M s).ptrs 62 = 0 := by
  simp [allocated,finished,TableAppend.seek_cursor,TableAppend.seek_ptr_frame,saved,setPtr,hn]
  constructor <;> ring

/- The allocator executes the address scan itself and discharges the whole
memory-separation contract, starting with adjacent graph and catalog arrays. -/
theorem allocated_ready {n w M : ℕ} (b : ℤ) (es : List (Fin n × Fin n))
    (Ss : ℕ → Finset (Fin n)) (s : Store)
    (h2 : s.ptrs 2 = b) (h3 : s.ptrs 3 = catalogBase b es.length)
    (hm : s.ptrs 5 = (es.length:ℤ)) (hn : s.ptrs 6 = (n:ℤ)) (hw : s.ptrs 43 = (w:ℤ))
    (he : EdgeEncoding s.imem b es)
    (hcat : ∀ a < M, Bitmap s.imem (catalogBase b es.length+(a:ℤ)*((n:ℤ)+1)) (Ss a)) :
    StateCatalog.Ready w 0 es Ss M (allocated M s) := by
  obtain ⟨p2,p3,p5,p6,p43,p72,p4,p50,p51,p61,p62⟩ := allocated_metadata n M s hn
  apply ready_of_contiguous_layout b es Ss (allocated M s)
  · exact p2.trans h2
  · exact p3.trans h3
  · simpa only [h3,workBase] using p4
  · simpa only [h3,workBase] using p50
  · simpa only [h3,workBase] using p51
  · simpa only [h3,tableBase,workBase] using p61
  · exact p5.trans hm
  · exact p6
  · exact p43.trans hw
  · simpa only [allocated_imem] using he
  · simpa only [allocated_imem] using hcat
end StableMSR.Recovery.Compiler.StateCatalogLayout
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open scoped Classical
namespace StableMSR.Recovery.Compiler.StateCatalogAllocated
open ComponentMachine ComponentMemory

def command : Cmd := .seq StateCatalogLayout.command StateCatalog.command
noncomputable def result (n m M : ℕ) (s : Store) : Store :=
  StateCatalog.eval n m 0 M (StateCatalogLayout.allocated M s)
noncomputable def steps (n m M : ℕ) (s : Store) : ℕ :=
  4*M+18+StateCatalog.steps n m 0 M (StateCatalogLayout.allocated M s)
noncomputable def program : MinSumFPT.Program := compile command 0
lemma program_length : program.length = 260 := by decide
lemma exec {N : ℕ} (d : Point N → Point N → ℝ) (n m M : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hm : s.ptrs 5 = (m:ℤ)) (hM : s.ptrs 72 = (M:ℤ)) :
    Executes d command s (result n m M s) (steps n m M s-1) := by
  obtain ⟨p2,p3,p5,p6,p43,p72,p4,p50,p51,p61,p62⟩ := StateCatalogLayout.allocated_metadata n M s hn
  have h := Executes.seq (StateCatalogLayout.allocation_exec d M s hM)
    (StateCatalog.exec d n m 0 M (StateCatalogLayout.allocated M s) p6 (p5.trans hm) p62 (p72.trans hM))
  convert h using 1 <;> try rfl
  dsimp [steps,StateCatalog.steps]; omega
lemma steps_bound (n m M : ℕ) (s : Store) :
    steps n m M s ≤ M*(n*(n*(17*m+57)+17*m+4*(M*n)+116)+13)+26 := by
  have h := StateCatalog.steps_bound n m 0 M (StateCatalogLayout.allocated M s)
  simp only [zero_add] at h
  dsimp [steps]; nlinarith
lemma machine_execution {N : ℕ} (d : Point N → Point N → ℝ) (n m M : ℕ) (s : Store)
    (hn : s.ptrs 6 = (n:ℤ)) (hm : s.ptrs 5 = (m:ℤ)) (hM : s.ptrs 72 = (M:ℤ))
    (ω : ℕ → ℝ) (work : ℕ) :
    (MinSumFPT.step program d ω)^[steps n m M s] (s.state 0 work) =
      (result n m M s).haltedState command.size (work+steps n m M s) 0 := by
  have hp : 1 ≤ steps n m M s := by dsimp [steps]; omega
  simpa only [program,Nat.sub_add_cancel hp,show work+(steps n m M s-1)+1 = work+steps n m M s by omega]
    using compile_halts (exec d n m M s hn hm hM) ω work 0

end StableMSR.Recovery.Compiler.StateCatalogAllocated

open StableMSR.Recovery.Compiler.StateCatalogAllocated StableMSR.Recovery.ComponentMemory
theorem solution :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 260 ∧
    ∀ (n w M : ℕ) (b : ℤ) (d : Point n → Point n → ℝ) (G : SimpleGraph (Fin n))
      (Ss : ℕ → Finset (Fin n)) (es : List (Fin n × Fin n)) (s : Store),
      s.ptrs 2 = b → s.ptrs 3 = b+2*(es.length:ℤ) →
      s.ptrs 5 = (es.length:ℤ) → s.ptrs 6 = (n:ℤ) → s.ptrs 43 = (w:ℤ) → s.ptrs 72 = (M:ℤ) →
      EdgeEncoding s.imem b es →
      (∀ i < M, Bitmap s.imem (b+2*(es.length:ℤ)+(i:ℤ)*((n:ℤ)+1)) (Ss i)) →
      (∀ e ∈ es, G.Adj e.1 e.2) → (∀ u v, G.Adj u v → (u,v) ∈ es) →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      ∃ t ≤ M*(n*(n*(17*es.length+57)+17*es.length+4*(M*n)+116)+13)+26,
      ∃ count : ℕ, count ≤ M*n ∧
      let C := fun (i : ℕ) (seed : Fin n) => Finset.univ.filter
        (fun v : Fin n => ∃ p : G.Walk seed v, ∀ z ∈ p.support, z ∉ Ss i)
      let eligible := fun (i : ℕ) (seed : Fin n) => seed ∉ Ss i ∧ (Ss i).card ≤ w ∧
        Ss i = Finset.univ.filter (fun v : Fin n => v ∉ C i seed ∧ ∃ u ∈ C i seed, G.Adj u v)
      let result := (MinSumFPT.step P d ω)^[t] (s.state 0 work)
      let table := b+2*(es.length:ℤ)+(M:ℤ)*((n:ℤ)+1)+3*(n:ℤ)
      let record := fun (a i : ℕ) (seed : Fin n) =>
        let base := table+(a:ℤ)*((n:ℤ)+(n:ℤ)+1)
        (∀ v : Fin n, result.imem (base+(v.val:ℤ)) = if v ∈ Ss i then 1 else 0) ∧
        (∀ v : Fin n, result.imem (base+(n:ℤ)+(v.val:ℤ)) = if v ∈ C i seed then 1 else 0) ∧
        result.imem (base+(n:ℤ)+(n:ℤ)) = 0
      count = ∑ i ∈ Finset.range M, (Finset.univ.filter (eligible i)).card ∧
      result.halted = true ∧ result.work = work+t ∧ result.cfg.ptrs 62 = (count:ℤ) ∧
      result.cfg.ptrs 61 = table ∧
      (∀ a : ℕ, a < count → ∃ i < M, ∃ seed : Fin n, eligible i seed ∧ record a i seed) ∧
      (∀ i < M, ∀ seed : Fin n, eligible i seed → ∃ a : ℕ, a < count ∧ record a i seed) ∧
      (∀ i < M, Bitmap result.imem (b+2*(es.length:ℤ)+(i:ℤ)*((n:ℤ)+1)) (Ss i)) ∧
      EdgeEncoding result.imem b es ∧
      result.cfg.regs = s.regs ∧ result.cfg.mem = s.mem ∧
      result.queries = s.queries ∧ result.tapePos = s.tapePos := by
  refine ⟨program,compile_deterministic command 0,program_length,?_⟩
  intro n w M b d G Ss es s h2 h3 hm hn hw hM he hcat hsound hcomplete ω work
  let a := StateCatalogLayout.allocated M s
  obtain ⟨p2,p3,p5,p6,p43,p72,p4,p50,p51,p61,p62⟩ := StateCatalogLayout.allocated_metadata n M s hn
  have hr : StateCatalog.Ready w 0 es Ss M a := StateCatalogLayout.allocated_ready b es Ss s h2 h3 hm hn hw he hcat
  have hs : (StateCatalog.setup a).ptrs 75 = (n:ℤ)+1 := by simp [StateCatalog.setup,StableMSR.Recovery.Compiler.ComponentMachine.setPtr,p6,a]
  have hc := StateCatalog.run_coverage G es hsound hcomplete M 0 Ss (StateCatalog.setup a) (StateCatalog.setup_ready hr) hs
  have hexact := StateCatalog.finalCount_exact G es hsound hcomplete M 0 Ss (StateCatalog.setup a) (StateCatalog.setup_ready hr) hs
  have hsource := StateCatalog.run_catalog G es hsound hcomplete M 0 Ss (StateCatalog.setup a) (StateCatalog.setup_ready hr) hs
  have hedge := StateCatalog.run_encoding G es hsound hcomplete M 0 Ss (StateCatalog.setup a) (StateCatalog.setup_ready hr) hs
    (by change EdgeEncoding a.imem (a.ptrs 2) es
        simpa only [a,StateCatalogLayout.allocated_imem,p2,h2] using he)
  have hbase : (result n es.length M s).ptrs 61 = b+2*(es.length:ℤ)+(M:ℤ)*((n:ℤ)+1)+3*(n:ℤ) := by
    rw [result,StateCatalog.full_ptr n es.length 0 M _ 61 (by simp),p61,h3]
  have hrecord (r i : ℕ) (seed : Fin n)
      (hh : StateSeedSweep.Record (result n es.length M s) r (Ss i) (ComponentState.outsideComponent G (Ss i) seed)) :
      (∀ v : Fin n, (result n es.length M s).imem
        (b+2*(es.length:ℤ)+(M:ℤ)*((n:ℤ)+1)+3*(n:ℤ)+(r:ℤ)*((n:ℤ)+(n:ℤ)+1)+(v.val:ℤ)) = if v ∈ Ss i then 1 else 0) ∧
      (∀ v : Fin n, (result n es.length M s).imem
        (b+2*(es.length:ℤ)+(M:ℤ)*((n:ℤ)+1)+3*(n:ℤ)+(r:ℤ)*((n:ℤ)+(n:ℤ)+1)+(n:ℤ)+(v.val:ℤ)) =
        if v ∈ ComponentState.outsideComponent G (Ss i) seed then 1 else 0) ∧
      (result n es.length M s).imem
        (b+2*(es.length:ℤ)+(M:ℤ)*((n:ℤ)+1)+3*(n:ℤ)+(r:ℤ)*((n:ℤ)+(n:ℤ)+1)+(n:ℤ)+(n:ℤ)) = 0 := by
    simpa only [StateSeedSweep.Record,StateRecord.rowBase,hbase] using hh
  refine ⟨steps n es.length M s,steps_bound n es.length M s,StateCatalog.finalCount n es.length 0 M (StateCatalog.setup a),
    by simpa only [zero_add] using (StateCatalog.count_bounds n es.length 0 M (StateCatalog.setup a)).2,?_⟩
  dsimp only
  rw [machine_execution d n es.length M s hn hm hM ω work]
  have hf := (StateCatalogLayout.allocated_frame M s).trans (StateCatalog.run_frame n es.length 0 M (StateCatalog.setup a))
  refine ⟨?_,rfl,rfl,StateCatalog.run_count n es.length 0 M (StateCatalog.setup a)
    (by change a.ptrs 62 = (0:ℤ); exact p62),hbase,?_,?_,?_,?_,
    hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1⟩
  · rw [hexact,zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ext seed
    simp only [Finset.mem_filter,StateRecord.eligible,ComponentState.outsideComponent,BoundaryMemory.externalBoundary]
  · intro r hlt
    obtain ⟨i,hi,seed,helig,hrec⟩ := hc.1 r (Nat.zero_le _) hlt
    exact ⟨i,hi,seed,helig,hrecord r i seed hrec⟩
  · intro i hi seed helig
    obtain ⟨r,_,hlt,hrec⟩ := hc.2 i hi seed helig
    exact ⟨r,hlt,hrecord r i seed hrec⟩
  · change ∀ i < M, Bitmap (result n es.length M s).imem
      (b+2*(es.length:ℤ)+(i:ℤ)*((n:ℤ)+1)) (Ss i)
    change ∀ i < M, Bitmap (result n es.length M s).imem
      (a.ptrs 3+(i:ℤ)*((n:ℤ)+1)) (Ss i) at hsource
    rw [show a.ptrs 3 = b+2*(es.length:ℤ) from p3.trans h3] at hsource
    exact hsource
  · change EdgeEncoding (result n es.length M s).imem b es
    change EdgeEncoding (result n es.length M s).imem (a.ptrs 2) es at hedge
    rw [show a.ptrs 2 = b from p2.trans h2] at hedge
    exact hedge
