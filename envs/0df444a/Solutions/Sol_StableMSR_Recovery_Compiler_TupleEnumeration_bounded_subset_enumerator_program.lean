-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.TupleEnumeration.bounded_subset_enumerator_program
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T19:44:19.060982+00:00
-- url     : https://prove2.me/submissions/90822e38-4f17-4172-84f2-bc54bf87ca64

import Definitions.Def_StableMSR_BoundedWordCatalog
import Theorems.Thm_StableMSR_Recovery_Compiler_compiler_execution_exact
import Mathlib.Data.List.Nodup
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
namespace StableMSR.Recovery.Compiler
lemma initialStore_state (n k : ℕ) : (initialStore n k).state 0 0 =
    MinSumFPT.initState n k 0 0 := by
  simp [initialStore, Store.state, MinSumFPT.initState]

/-- A concrete compiler bridge from a structured algorithm proof to execute. -/
theorem execute_compile {n k : ℕ} {d : Point n → Point n → ℝ}
    {cmd : Cmd} {t : Store} {cost : ℕ}
    (h : Executes d cmd (initialStore n k) t cost) (result : ℕ) :
    execute (compile cmd result) n k d (cost+1) =
      t.haltedState cmd.size (cost+1) result := by
  have he := compile_halts h (fun _ => 0) 0 result
  rw [initialStore_state] at he
  simpa only [execute, MinSumFPT.run, Nat.zero_add] using he

end StableMSR.Recovery.Compiler
open scoped BigOperators
namespace StableMSR.Recovery.BoundedSubsetWords

/- Lexicographic words, with zero reserved as padding and 1,...,n as vertices. -/
@[simp] theorem mem_words (n w : ℕ) (l : List ℕ) :
    l ∈ words n w ↔ l.length = w ∧ ∀ a ∈ l, a ≤ n := by
  induction w generalizing l with
  | zero => cases l <;> simp [words]
  | succ w ih =>
    cases l with
    | nil => simp [words]
    | cons a l =>
      simp only [words,List.mem_flatMap,List.mem_map,List.cons.injEq]
      constructor
      · rintro ⟨b,hb,t,ht,hba,htl⟩
        subst b; subst t
        obtain ⟨hlen,hbound⟩ := (ih l).mp ht
        exact ⟨by simp [hlen],by simpa using And.intro (by simpa using hb) hbound⟩
      · rintro ⟨hlen,hbound⟩
        have ha := hbound a (by simp)
        have hl : ∀ b ∈ l, b ≤ n := fun b hb => hbound b (by simp [hb])
        refine ⟨a,by simpa using ha,l,(ih l).mpr ⟨?_,hl⟩,rfl,rfl⟩
        simpa using hlen

@[simp] theorem words_length (n w : ℕ) : (words n w).length = (n+1)^w := by
  induction w with
  | zero => simp [words]
  | succ w ih =>
    simp [words,List.length_flatMap,ih,Nat.pow_succ,Nat.mul_comm]

/- Each word appears once in the lexicographic stream. -/
theorem words_nodup (n w : ℕ) : (words n w).Nodup := by
  induction w with
  | zero => simp [words]
  | succ w ih =>
    apply List.nodup_flatMap.mpr
    refine ⟨fun a _ => ih.map (fun _ _ h => (List.cons.inj h).2),?_⟩
    exact (show (List.range (n+1)).Nodup from List.nodup_range).imp (fun {a b} hab l ha hb => by
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨y,_,h⟩ := List.mem_map.mp hb
      exact hab (List.cons.inj h).1.symm)

/- Decode nonzero digits; duplicates and out-of-range digits are ignored. -/
@[simp] theorem mem_decode {n : ℕ} {l : List ℕ} {v : Fin n} :
    v ∈ decode n l ↔ v.val+1 ∈ l := by simp [decode]

@[simp] theorem decode_nil (n : ℕ) : decode n [] = ∅ := by ext v; simp

@[simp] theorem decode_append (n : ℕ) (l t : List ℕ) :
    decode n (l++t) = decode n l ∪ decode n t := by ext v; simp

@[simp] theorem decode_replicate_zero (n m : ℕ) : decode n (List.replicate m 0) = ∅ := by
  ext v; simp

theorem decode_card_le_length (n : ℕ) (l : List ℕ) : (decode n l).card ≤ l.length := by
  have hi : Function.Injective (fun v : Fin n => v.val+1) := by
    intro a b h
    apply Fin.ext
    change a.val+1 = b.val+1 at h
    omega
  have hs : (decode n l).image (fun v => v.val+1) ⊆ l.toFinset := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    simpa using (mem_decode.mp hv)
  calc
    (decode n l).card = ((decode n l).image (fun v => v.val+1)).card :=
      (Finset.card_image_of_injective _ hi).symm
    _ ≤ l.toFinset.card := Finset.card_le_card hs
    _ ≤ l.length := List.toFinset_card_le _

/- A finite subset is represented by its positive vertex digits followed by zeros. -/
theorem exists_word_decoding {n w : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ w) :
    ∃ l ∈ words n w, decode n l = S := by
  classical
  let l := S.toList.map (fun v => v.val+1) ++ List.replicate (w-S.card) 0
  have hlen : l.length = w := by simp [l]; omega
  have hb : ∀ a ∈ l, a ≤ n := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
      exact Nat.succ_le_of_lt v.isLt
    · have : a = 0 := (List.mem_replicate.mp ha).2
      omega
  refine ⟨l,(mem_words n w l).mpr ⟨hlen,hb⟩,?_⟩
  ext v
  simp only [mem_decode,l,List.mem_append,List.mem_map,Finset.mem_toList,
    List.mem_replicate]
  constructor
  · rintro (⟨u,hu,h⟩ | ⟨_,h⟩)
    · have huv : u = v := by apply Fin.ext; omega
      simpa [huv] using hu
    · omega
  · intro hv
    exact Or.inl ⟨v,hv,rfl⟩

/- The decoded finite word stream is exactly the family of bounded subsets. -/
/- Padding gives a slightly sharper cardinality bound than summing binomial
bounds separately: the width-w word stream covers every bounded subset. -/
/- Exact coverage and length for the concrete finite word enumerator. -/
theorem bounded_subset_word_enumeration (n w : ℕ) :
    (words n w).length = (n+1)^w ∧ (words n w).Nodup ∧
      ∀ S : Finset (Fin n), S.card ≤ w ↔ ∃ l ∈ words n w, decode n l = S := by
  refine ⟨words_length n w,words_nodup n w,?_⟩
  intro S
  constructor
  · exact exists_word_decoding S
  · rintro ⟨l,hl,rfl⟩
    exact (decode_card_le_length n l).trans_eq ((mem_words n w l).mp hl).1

end StableMSR.Recovery.BoundedSubsetWords


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

open scoped Classical
namespace StableMSR.Recovery.Compiler.TupleEnumeration
open TupleWriter

def setPtr (s : Store) (i : ℕ) (z : ℤ) : Store :=
  { s with ptrs := Function.update s.ptrs i z }

def incPtr (s : Store) (i : ℕ) : Store := setPtr s i (s.ptrs i+1)

def nestedCmd (w start : ℕ) : ℕ → Cmd
  | 0 => writer w
  | r+1 => .seq (.atom (.pointerConst start 0))
      (.whileDo (.pointerLE start 0)
        (.seq (nestedCmd w (start+1) r) (.atom (.pointerInc start))))

def nestedEval (w n start : ℕ) : ℕ → Store → Store
  | 0, s => writerEval w s
  | r+1, s =>
      (fun t => incPtr (nestedEval w n (start+1) r t) start)^[n+1] (setPtr s start 0)

def nestedCost (w n : ℕ) : ℕ → ℕ
  | 0 => 2*(w+1)
  | r+1 => 3+(n+1)*(nestedCost w n r+3)

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

/- A projection untouched by the writer and pointer changes is preserved by
all nesting levels. This covers real data, query/tape counters, and old output. -/
lemma nested_preserves {α : Type*} (F : Store → α) (w n start r : ℕ)
    (hleaf : ∀ s, F (writerEval w s) = F s)
    (hset : ∀ s i z, F (setPtr s i z) = F s) (s : Store) :
    F (nestedEval w n start r s) = F s := by
  induction r generalizing start s with
  | zero => exact hleaf s
  | succ r ih =>
    change F ((fun t => incPtr (nestedEval w n (start+1) r t) start)^[n+1]
      (setPtr s start 0)) = F s
    rw [iterate_preserves _ F (by intro t; rw [incPtr,hset,ih])]
    exact hset s start 0

lemma nested_ptr_frame (w n start r j : ℕ) (s : Store)
    (hs : 1 ≤ start) (hb : start+r ≤ w+1)
    (hj : j < start ∨ start+r ≤ j) (hne : j ≠ w+1) :
    (nestedEval w n start r s).ptrs j = s.ptrs j := by
  induction r generalizing start s with
  | zero => exact writer_ptr_ne w j s hne
  | succ r ih =>
    have hjs : j ≠ start := by omega
    have hc (t : Store) : (nestedEval w n (start+1) r t).ptrs j = t.ptrs j :=
      ih (start+1) t (by omega) (by omega) (by omega)
    change ((fun t => incPtr (nestedEval w n (start+1) r t) start)^[n+1]
      (setPtr s start 0)).ptrs j = s.ptrs j
    rw [iterate_preserves _ (fun t => t.ptrs j) (by
      intro t; simp only [incPtr,setPtr,Function.update_of_ne hjs]; exact hc t)]
    simp [setPtr,hjs]

lemma nested_ptr_out (w n start r : ℕ) (s : Store)
    (hs : 1 ≤ start) (hb : start+r ≤ w+1) :
    (nestedEval w n start r s).ptrs (w+1) =
      s.ptrs (w+1)+((w+1)*(n+1)^r : ℕ) := by
  induction r generalizing start s with
  | zero => simpa [nestedEval] using writer_ptr_out w s
  | succ r ih =>
    have hne : w+1 ≠ start := by omega
    have hf (t : Store) :
        (incPtr (nestedEval w n (start+1) r t) start).ptrs (w+1) =
          t.ptrs (w+1)+((w+1)*(n+1)^r : ℕ) := by
      simp only [incPtr,setPtr,Function.update_of_ne hne]
      exact ih (start+1) t (by omega) (by omega)
    change ((fun t => incPtr (nestedEval w n (start+1) r t) start)^[n+1]
      (setPtr s start 0)).ptrs (w+1) = _
    rw [iterate_additive _ (fun t => t.ptrs (w+1)) _ hf]
    simp only [setPtr,Function.update_of_ne hne]
    push_cast
    rw [pow_succ]
    ring

lemma nested_frame (w n start r : ℕ) (s : Store) :
    (nestedEval w n start r s).regs = s.regs ∧
    (nestedEval w n start r s).mem = s.mem ∧
    (nestedEval w n start r s).queries = s.queries ∧
    (nestedEval w n start r s).tapePos = s.tapePos ∧
    (nestedEval w n start r s).output = s.output := by
  exact ⟨nested_preserves Store.regs w n start r (fun t => (writer_frame w t).1) (by intros; rfl) s,
    nested_preserves Store.mem w n start r (fun t => (writer_frame w t).2.1) (by intros; rfl) s,
    nested_preserves Store.queries w n start r (fun t => (writer_frame w t).2.2.1) (by intros; rfl) s,
    nested_preserves Store.tapePos w n start r (fun t => (writer_frame w t).2.2.2.1) (by intros; rfl) s,
    nested_preserves Store.output w n start r (fun t => (writer_frame w t).2.2.2.2) (by intros; rfl) s⟩

lemma fixed_loop_exec {N : ℕ} (d : Point N → Point N → ℝ)
    (body : Cmd) (f : Store → Store) (i cost : ℕ) (bound : ℤ)
    (he : ∀ s, s.ptrs 0 = bound → Executes d body s (f s) cost)
    (hi : ∀ s, (f s).ptrs i = s.ptrs i+1)
    (h0 : ∀ s, (f s).ptrs 0 = s.ptrs 0)
    (q : ℕ) (s : Store) (hb : s.ptrs 0 = bound)
    (hstop : s.ptrs i+(q:ℤ)-1 = bound) :
    Executes d (.whileDo (.pointerLE i 0) body) s (f^[q] s) ((cost+2)*q+2) := by
  induction q generalizing s with
  | zero =>
    apply Executes.while_false
    simp only [Cond.test]
    omega
  | succ q ih =>
    have ht : (Cond.pointerLE i 0).test s := by simp only [Cond.test]; omega
    have hrest := ih (f s) (by rw [h0,hb]) (by rw [hi]; push_cast at hstop; omega)
    have hrun := Executes.while_true ht (he s hb) hrest
    convert hrun using 1
    · exact Function.iterate_succ_apply f q s
    · simp only [Nat.mul_succ]; omega

/- Exact charged execution of the nested loops, with only pointer addition,
comparison, integer loads/stores and ordinary loop control. -/
theorem nested_exec {N : ℕ} (d : Point N → Point N → ℝ)
    (w n start r : ℕ) (s : Store) (hs : 1 ≤ start) (hb : start+r ≤ w+1)
    (hbound : s.ptrs 0 = (n:ℤ)) :
    Executes d (nestedCmd w start r) s (nestedEval w n start r s) (nestedCost w n r) := by
  induction r generalizing start s with
  | zero => exact writer_exec d w s
  | succ r ih =>
    let f := fun t => incPtr (nestedEval w n (start+1) r t) start
    have hi (t : Store) : (f t).ptrs start = t.ptrs start+1 := by
      dsimp [f,incPtr,setPtr]
      rw [Function.update_self]
      rw [nested_ptr_frame w n (start+1) r start t (by omega) (by omega) (by omega) (by omega)]
    have h0 (t : Store) : (f t).ptrs 0 = t.ptrs 0 := by
      dsimp [f,incPtr,setPtr]
      rw [Function.update_of_ne (by omega : 0 ≠ start)]
      exact nested_ptr_frame w n (start+1) r 0 t (by omega) (by omega) (by omega) (by omega)
    have he (t : Store) (ht : t.ptrs 0 = (n:ℤ)) :
        Executes d (.seq (nestedCmd w (start+1) r) (.atom (.pointerInc start)))
          t (f t) (nestedCost w n r+1) :=
      Executes.seq (ih (start+1) t (by omega) (by omega) ht) (Executes.atom _ _)
    have hinit : (setPtr s start 0).ptrs 0 = (n:ℤ) := by
      simp only [setPtr,Function.update_of_ne (by omega : 0 ≠ start)]
      exact hbound
    have hstop : (setPtr s start 0).ptrs start+(n+1:ℕ)-1 = (n:ℤ) := by simp [setPtr]
    have hl := fixed_loop_exec d _ f start (nestedCost w n r+1) n he hi h0
      (n+1) (setPtr s start 0) hinit hstop
    have hrun := Executes.seq (Executes.atom (.pointerConst start 0) s) hl
    convert hrun using 1
    · rfl
    · rfl
    · simp only [nestedCost]; ring

lemma nestedCost_le (w n r : ℕ) :
    nestedCost w n r ≤ (2*(w+1)+6*r)*(n+1)^r := by
  induction r with
  | zero => simp [nestedCost]
  | succ r ih =>
    have hp : n+1 ≤ (n+1)^(r+1) := Nat.le_self_pow (by omega) _
    have h1 : 1 ≤ (n+1)^(r+1) := Nat.one_le_pow _ _ (by omega)
    calc
      nestedCost w n (r+1) ≤ 3+(n+1)*((2*(w+1)+6*r)*(n+1)^r+3) := by
        dsimp [nestedCost]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right ih _)) _
      _ = (2*(w+1)+6*r)*(n+1)^(r+1)+(3+3*(n+1)) := by rw [pow_succ]; ring
      _ ≤ (2*(w+1)+6*r)*(n+1)^(r+1)+6*(n+1)^(r+1) := by omega
      _ = (2*(w+1)+6*(r+1))*(n+1)^(r+1) := by ring

def block (w : ℕ) : Cmd :=
  .seq (.atom (.pointerConst (w+2) w)) (nestedCmd w 1 w)

def blockEval (w n : ℕ) (s : Store) : Store :=
  nestedEval w n 1 w (setPtr s (w+2) w)

theorem block_exec {N : ℕ} (d : Point N → Point N → ℝ) (w n : ℕ) (s : Store)
    (hbound : s.ptrs 0 = (n:ℤ)) :
    Executes d (block w) s (blockEval w n s) (1+nestedCost w n w) := by
  apply Executes.seq (Executes.atom _ _)
  apply nested_exec d w n 1 w _ (by omega) (by omega)
  simpa [setPtr,Op.eval] using hbound

lemma blockCost_le (w n : ℕ) :
    1+nestedCost w n w ≤ (8*w+2)*(n+1)^w+1 := by
  have h := nestedCost_le w n w
  have he : 2*(w+1)+6*w = 8*w+2 := by omega
  rw [he] at h
  omega

@[simp] lemma nestedCmd_size (w start r : ℕ) :
    (nestedCmd w start r).size = 2*(w+1)+5*r := by
  induction r generalizing start with
  | zero => simp [nestedCmd]
  | succ r ih => simp only [nestedCmd,Cmd.size,ih]; omega

@[simp] lemma block_size (w : ℕ) : (block w).size = 7*w+3 := by
  simp only [block,Cmd.size,nestedCmd_size]
  omega

lemma block_ptr_out (w n : ℕ) (s : Store) :
    (blockEval w n s).ptrs (w+1) = s.ptrs (w+1)+((w+1)*(n+1)^w : ℕ) := by
  rw [blockEval,nested_ptr_out w n 1 w _ (by omega) (by omega)]
  simp [setPtr]

lemma block_ptr_zero (w n : ℕ) (s : Store) :
    (blockEval w n s).ptrs 0 = s.ptrs 0 := by
  rw [blockEval,nested_ptr_frame w n 1 w 0 _ (by omega) (by omega) (by omega) (by omega)]
  simp [setPtr]

lemma block_header_ptr (w n : ℕ) (s : Store) :
    (blockEval w n s).ptrs (w+2) = (w:ℤ) := by
  rw [blockEval,nested_ptr_frame w n 1 w (w+2) _ (by omega) (by omega) (by omega) (by omega)]
  simp [setPtr]

lemma block_frame (w n : ℕ) (s : Store) :
    (blockEval w n s).regs = s.regs ∧ (blockEval w n s).mem = s.mem ∧
    (blockEval w n s).queries = s.queries ∧ (blockEval w n s).tapePos = s.tapePos ∧
    (blockEval w n s).output = s.output :=
  nested_frame w n 1 w (setPtr s (w+2) w)

end StableMSR.Recovery.Compiler.TupleEnumeration

set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.TupleEnumeration
open TupleWriter BoundedSubsetWords

/- Snapshot of the first k digit registers. -/
def registerPrefix (s : Store) (k : ℕ) : List ℤ :=
  (List.range k).map (fun i => s.ptrs (i+1))

@[simp] lemma registerPrefix_length (s : Store) (k : ℕ) :
    (registerPrefix s k).length = k := by simp [registerPrefix]

lemma registerPrefix_succ (s : Store) (k : ℕ) :
    registerPrefix s (k+1) = registerPrefix s k ++ [s.ptrs (k+1)] := by
  simp [registerPrefix,List.range_succ]

lemma registerPrefix_congr {s t : Store} (k : ℕ)
    (h : ∀ i, i < k → s.ptrs (i+1) = t.ptrs (i+1)) :
    registerPrefix s k = registerPrefix t k := by
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/- Records of fixed total width, extending the already fixed pre with all
lexicographically enumerated suffix words. -/
@[simp] lemma wordStream_zero (n w : ℕ) (pre : List ℤ) :
    wordStream n w pre 0 = (w : ℤ) :: pre := by
  simp [wordStream,words]

lemma wordStream_succ (n w : ℕ) (pre : List ℤ) (r : ℕ) :
    wordStream n w pre (r+1) =
      (List.range (n+1)).flatMap (fun i : ℕ => wordStream n w (pre++[(i : ℤ)]) r) := by
  simp [wordStream,words,List.flatMap_assoc,List.flatMap_map,List.append_assoc]

lemma flatMap_length_const {α β : Type} (l : List α) (f : α → List β) (L : ℕ)
    (h : ∀ x ∈ l, (f x).length = L) : (l.flatMap f).length = l.length*L := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    rw [h a (by simp),ih (fun x hx => h x (by simp [hx]))]
    ring

lemma wordStream_length (n w : ℕ) (pre : List ℤ) (r : ℕ)
    (h : pre.length+r = w) :
    (wordStream n w pre r).length = (w+1)*(n+1)^r := by
  unfold wordStream
  rw [flatMap_length_const (words n r) (fun xs : List ℕ => (w : ℤ) :: (pre ++ xs.map (fun i : ℕ => (i : ℤ)))) (w+1) (by
    intro xs hx
    have hlen := ((mem_words n r xs).mp hx).1
    simp only [List.length_cons,List.length_append,List.length_map]
    omega)]
  rw [words_length]
  exact Nat.mul_comm _ _

/- Stream emitted by the first q values of the next digit. -/
def partialStream (n w : ℕ) (pre : List ℤ) (r q : ℕ) : List ℤ :=
  (List.range q).flatMap (fun i : ℕ => wordStream n w (pre++[(i : ℤ)]) r)

@[simp] lemma partialStream_zero (n w : ℕ) (pre : List ℤ) (r : ℕ) :
    partialStream n w pre r 0 = [] := rfl

lemma partialStream_succ (n w : ℕ) (pre : List ℤ) (r q : ℕ) :
    partialStream n w pre r (q+1) = partialStream n w pre r q ++
      wordStream n w (pre++[(q : ℤ)]) r := by
  simp [partialStream,List.range_succ]

lemma partialStream_length (n w : ℕ) (pre : List ℤ) (r q : ℕ)
    (h : pre.length+(r+1) = w) :
    (partialStream n w pre r q).length = q*((w+1)*(n+1)^r) := by
  unfold partialStream
  rw [flatMap_length_const (List.range q) (fun i : ℕ => wordStream n w (pre++[(i : ℤ)]) r) ((w+1)*(n+1)^r) (by
    intro i hi
    apply wordStream_length
    simp only [List.length_append,List.length_singleton]
    omega),List.length_range]

end StableMSR.Recovery.Compiler.TupleEnumeration

set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.TupleEnumeration
open TupleWriter BoundedSubsetWords

/- The completed nested loops write exactly the lexicographic record stream,
not merely the right number of memory cells. -/
theorem nested_memory (w n r k : ℕ) (hkr : k+r=w) (s : Store)
    (hw : s.ptrs (w+2) = (w:ℤ)) :
    (nestedEval w n (k+1) r s).imem =
      writeMemory (s.ptrs (w+1)) (wordStream n w (registerPrefix s k) r) s.imem := by
  induction r generalizing k s with
  | zero =>
    have hk : k=w := by omega
    subst k
    simp only [nestedEval,writer_memory,wordStream_zero]
    congr 1
    simp [writerRegs,registerPrefix,hw,List.map_map]
  | succ r ih =>
    let f : Store → Store := fun t => incPtr (nestedEval w n (k+1+1) r t) (k+1)
    let s₀ := setPtr s (k+1) 0
    have hkout : w+1 ≠ k+1 := by omega
    have hkw : w+2 ≠ k+1 := by omega
    have hcursor (t : Store) : (f t).ptrs (k+1) = t.ptrs (k+1)+1 := by
      simp only [f,incPtr,setPtr,Function.update_self]
      rw [nested_ptr_frame w n (k+1+1) r (k+1) t (by omega) (by omega) (by omega) (by omega)]
    have hpre (t : Store) : registerPrefix (f t) k = registerPrefix t k := by
      apply registerPrefix_congr
      intro i hi
      simp only [f,incPtr,setPtr,Function.update_of_ne (by omega : i+1 ≠ k+1)]
      exact nested_ptr_frame w n (k+1+1) r (i+1) t (by omega) (by omega) (by omega) (by omega)
    have hconst (t : Store) : (f t).ptrs (w+2) = t.ptrs (w+2) := by
      simp only [f,incPtr,setPtr,Function.update_of_ne hkw]
      exact nested_ptr_frame w n (k+1+1) r (w+2) t (by omega) (by omega) (by omega) (by omega)
    have hout (t : Store) : (f t).ptrs (w+1) =
        t.ptrs (w+1)+((w+1)*(n+1)^r : ℕ) := by
      simp only [f,incPtr,setPtr,Function.update_of_ne hkout]
      exact nested_ptr_out w n (k+1+1) r t (by omega) (by omega)
    have hpre₀ : registerPrefix s₀ k = registerPrefix s k := by
      apply registerPrefix_congr
      intro i hi
      simp only [s₀,setPtr,Function.update_of_ne (by omega : i+1 ≠ k+1)]
    have hiterpre (q : ℕ) : registerPrefix (f^[q] s₀) k = registerPrefix s k := by
      rw [iterate_preserves f (fun t => registerPrefix t k) hpre,hpre₀]
    have hitercursor (q : ℕ) : (f^[q] s₀).ptrs (k+1) = (q:ℤ) := by
      rw [iterate_additive f (fun t => t.ptrs (k+1)) 1 hcursor]
      simp [s₀,setPtr]
    have hiterconst (q : ℕ) : (f^[q] s₀).ptrs (w+2) = (w:ℤ) := by
      rw [iterate_preserves f (fun t => t.ptrs (w+2)) hconst]
      simpa [s₀,setPtr,hkw] using hw
    have hiterout (q : ℕ) : (f^[q] s₀).ptrs (w+1) =
        s.ptrs (w+1)+(q:ℤ)*((w+1)*(n+1)^r : ℕ) := by
      rw [iterate_additive f (fun t => t.ptrs (w+1)) _ hout]
      simp only [s₀,setPtr,Function.update_of_ne hkout]
    have hmemory (q : ℕ) : (f^[q] s₀).imem =
        writeMemory (s.ptrs (w+1)) (partialStream n w (registerPrefix s k) r q) s.imem := by
      induction q with
      | zero => rfl
      | succ q ihq =>
        rw [Function.iterate_succ_apply']
        change (nestedEval w n (k+1+1) r (f^[q] s₀)).imem = _
        rw [ih (k+1) (by omega) (f^[q] s₀) (hiterconst q)]
        have hpc : registerPrefix (f^[q] s₀) (k+1) =
            registerPrefix s k ++ [(q:ℤ)] := by
          rw [registerPrefix_succ,hiterpre,hitercursor]
        rw [hpc,hiterout,ihq,partialStream_succ,writeMemory_append]
        congr 1
        rw [partialStream_length n w (registerPrefix s k) r q (by simp; omega)]
        push_cast
        rfl
    change (f^[n+1] s₀).imem = _
    rw [hmemory]
    rw [wordStream_succ]
    rfl

/- The full concrete block emits all fixed-width words, each with its length
header, in lexicographic order at consecutive integer-memory addresses. -/
theorem block_memory (w n : ℕ) (s : Store) :
    (blockEval w n s).imem =
      writeMemory (s.ptrs (w+1)) (wordStream n w [] w) s.imem := by
  unfold blockEval
  rw [nested_memory w n w 0 (by omega) _ (by simp [setPtr])]
  simp [registerPrefix,setPtr]

end StableMSR.Recovery.Compiler.TupleEnumeration

set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.TupleEnumeration
open TupleWriter BoundedSubsetWords

/- Read the digits following a fixed-width record header. -/
/- Read all records of the concrete word catalog beginning at integer address 2. -/
lemma flatMap_getElem?_constant {α β : Type} (xs : List α) (f : α → List β)
    (L : ℕ) (hL : ∀ x ∈ xs, (f x).length = L)
    (j : ℕ) (hj : j < xs.length) (i : ℕ) (hi : i < L) :
    (xs.flatMap f)[L*j+i]? = (f xs[j])[i]? := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons a xs ih =>
    cases j with
    | zero =>
      simp only [Nat.mul_zero,Nat.zero_add,List.flatMap_cons,List.getElem_cons_zero]
      exact List.getElem?_append_left (by rw [hL a (by simp)]; exact hi)
    | succ j =>
      have hj' : j < xs.length := by simpa using hj
      have hla := hL a (by simp)
      have he : L*(j+1)+i = (f a).length+(L*j+i) := by rw [hla]; ring
      simp only [List.flatMap_cons,List.getElem_cons_succ]
      rw [he,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
      exact ih (fun x hx => hL x (by simp [hx])) j hj'

lemma record_index_lt (n w j i : ℕ) (hj : j < (n+1)^w) (hi : i < w+1) :
    (w+1)*j+i < (wordStream n w [] w).length := by
  rw [wordStream_length n w [] w (by simp)]
  calc
    (w+1)*j+i < (w+1)*j+(w+1) := Nat.add_lt_add_left hi _
    _ = (w+1)*(j+1) := by ring
    _ ≤ (w+1)*(n+1)^w := Nat.mul_le_mul_left _ hj

lemma wordStream_record_get (n w j i : ℕ) (hj : j < (n+1)^w) (hi : i < w+1) :
    (wordStream n w [] w)[(w+1)*j+i]? =
      ((w:ℤ) :: ((words n w)[j]'(by simpa using hj)).map (fun a : ℕ => (a:ℤ)))[i]? := by
  change ((words n w).flatMap (fun xs : List ℕ => (w:ℤ) :: xs.map (fun a : ℕ => (a:ℤ))))[(w+1)*j+i]? = _
  exact flatMap_getElem?_constant (words n w)
      (fun xs : List ℕ => (w:ℤ) :: xs.map (fun a : ℕ => (a:ℤ)))
      (w+1) (by
        intro xs hx
        have h := ((mem_words n w xs).mp hx).1
        simp [h]) j (by simpa using hj) i hi

/- The j-th record reads back exactly the j-th lexicographic word. -/
theorem readWord_writeMemory (n w j : ℕ) (oldmem : ℤ → ℤ) (hj : j < (n+1)^w) :
    readWord w (writeMemory 2 (wordStream n w [] w) oldmem) (2+((w+1)*j : ℕ)) =
      (words n w)[j]'(by simpa using hj) := by
  have hword : ((words n w)[j]'(by simpa using hj)).length = w :=
    ((mem_words n w _).mp (List.getElem_mem _)).1
  apply List.ext_getElem
  · simp [readWord,hword]
  · intro i hi hi'
    simp only [readWord,List.getElem_map,List.getElem_range]
    have hiw : i < w := by simpa [readWord] using hi
    have he : (2:ℤ)+((w+1)*j : ℕ)+1+(i:ℤ) = 2+((w+1)*j+(i+1) : ℕ) := by
      push_cast
      ring
    rw [he,writeMemory_get 2 _ oldmem ((w+1)*j+(i+1)) (record_index_lt n w j (i+1) hj (by omega))]
    have hget := wordStream_record_get n w j (i+1) hj (by omega)
    rw [List.getElem?_eq_getElem (record_index_lt n w j (i+1) hj (by omega))] at hget
    simp only [List.getElem?_cons_succ,List.getElem?_map] at hget
    rw [List.getElem?_eq_getElem hi'] at hget
    simp only [Option.map_some,Option.some.injEq] at hget
    rw [hget]
    simp

/- Reading the actual consecutive memory records reproduces the whole word list. -/
theorem catalogWords_writeMemory (n w : ℕ) (oldmem : ℤ → ℤ) :
    catalogWords n w (writeMemory 2 (wordStream n w [] w) oldmem) = words n w := by
  apply List.ext_getElem
  · simp [catalogWords]
  · intro j hj hj'
    simp only [catalogWords,List.getElem_map,List.getElem_range]
    apply readWord_writeMemory
    simpa [catalogWords] using hj

/- Every bounded subset occurs in a record of the written integer-memory catalog,
and every such record decodes to a bounded subset. -/
theorem memory_catalog_subset_iff (n w : ℕ) (oldmem : ℤ → ℤ) (S : Finset (Fin n)) :
    S.card ≤ w ↔ ∃ j < (n+1)^w,
      decode n (readWord w (writeMemory 2 (wordStream n w [] w) oldmem)
        (2+((w+1)*j : ℕ))) = S := by
  have h := (bounded_subset_word_enumeration n w).2.2 S
  rw [←catalogWords_writeMemory n w oldmem] at h
  rw [h]
  constructor
  · rintro ⟨l,hl,hd⟩
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hl
    exact ⟨j,List.mem_range.mp hj,hd⟩
  · rintro ⟨j,hj,hd⟩
    refine ⟨_,?_,hd⟩
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩

end StableMSR.Recovery.Compiler.TupleEnumeration

set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.TupleEnumeration
/- Read the input size from integer memory and put the output cursor after the
reserved input cells. This block is independent of the input size. -/
def inputSetup (w : ℕ) : Cmd :=
  .seq (.atom (.pointerConst 0 0))
    (.seq (.atom (.integerLoad 0 0)) (.atom (.pointerConst (w+1) 2)))

def prepared (w : ℕ) (s : Store) : Store :=
  { s with ptrs := Function.update (Function.update s.ptrs 0 (s.imem 0)) (w+1) 2 }

lemma inputSetup_exec {n : ℕ} (d : Point n → Point n → ℝ) (w : ℕ) (s : Store) :
    Executes d (inputSetup w) s (prepared w s) 3 := by
  have h := Executes.seq (Executes.atom (.pointerConst 0 0) s)
    (Executes.seq (Executes.atom (.integerLoad 0 0) ((Op.pointerConst 0 0).eval d s))
      (Executes.atom (.pointerConst (w+1) 2)
        ((Op.integerLoad 0 0).eval d ((Op.pointerConst 0 0).eval d s))))
  simpa [inputSetup,prepared,Op.eval,Function.update_idem] using h

@[simp] lemma prepared_ptr_zero (w : ℕ) (s : Store) :
    (prepared w s).ptrs 0 = s.imem 0 := by simp [prepared]
@[simp] lemma prepared_ptr_out (w : ℕ) (s : Store) :
    (prepared w s).ptrs (w+1) = 2 := by simp [prepared]
@[simp] lemma prepared_imem (w : ℕ) (s : Store) : (prepared w s).imem = s.imem := rfl
@[simp] lemma prepared_regs (w : ℕ) (s : Store) : (prepared w s).regs = s.regs := rfl
@[simp] lemma prepared_mem (w : ℕ) (s : Store) : (prepared w s).mem = s.mem := rfl
@[simp] lemma prepared_queries (w : ℕ) (s : Store) : (prepared w s).queries = s.queries := rfl
@[simp] lemma prepared_tapePos (w : ℕ) (s : Store) : (prepared w s).tapePos = s.tapePos := rfl

lemma prepared_initial_bound (w n k : ℕ) :
    (prepared w (initialStore n k)).ptrs 0 = (n : ℤ) := by simp [initialStore]

end StableMSR.Recovery.Compiler.TupleEnumeration

set_option autoImplicit false
namespace StableMSR.Recovery.Compiler.TupleEnumeration
open TupleWriter

def programCmd (w : ℕ) : Cmd := .seq (inputSetup w) (block w)
noncomputable def program (w : ℕ) : MinSumFPT.Program := compile (programCmd w) 0

def programStore (w n k : ℕ) : Store :=
  blockEval w n (prepared w (initialStore n k))

theorem program_exec (w n k : ℕ) (d : Point n → Point n → ℝ) :
    Executes d (programCmd w) (initialStore n k) (programStore w n k)
      (4+nestedCost w n w) := by
  have he := Executes.seq (inputSetup_exec d w (initialStore n k))
    (block_exec d w n (prepared w (initialStore n k)) (prepared_initial_bound w n k))
  convert he using 1 <;> first | rfl | omega

lemma program_cost_le (w n : ℕ) :
    4+nestedCost w n w+1 ≤ (8*w+2)*(n+1)^w+5 := by
  have h := blockCost_le w n
  omega

lemma programStore_ptr_out (w n k : ℕ) :
    (programStore w n k).ptrs (w+1) = 2+((w+1)*(n+1)^w : ℕ) := by
  unfold programStore blockEval
  rw [nested_ptr_out w n 1 w _ (by omega) (by omega)]
  simp [setPtr]

lemma programStore_frame (w n k : ℕ) :
    (programStore w n k).regs = (initialStore n k).regs ∧
    (programStore w n k).mem = (initialStore n k).mem ∧
    (programStore w n k).queries = 0 ∧ (programStore w n k).tapePos = 0 := by
  have h := nested_frame w n 1 w (setPtr (prepared w (initialStore n k)) (w+2) w)
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

/- A fixed-width program reads n from input memory and actually executes the
whole nested enumerator, with a polynomial charged instruction bound. -/
theorem program_execution (w n k : ℕ) (d : Point n → Point n → ℝ) :
    DeterministicProgram (program w) ∧
    (4+nestedCost w n w+1 ≤ (8*w+2)*(n+1)^w+5) ∧
    execute (program w) n k d (4+nestedCost w n w+1) =
      (programStore w n k).haltedState (programCmd w).size (4+nestedCost w n w+1) 0 := by
  exact ⟨compile_deterministic (programCmd w) 0,program_cost_le w n,
    execute_compile (program_exec w n k d) 0⟩

lemma program_length (w : ℕ) : (program w).length = 7*w+7 := by
  simp [program,compile,programCmd,Cmd.size,inputSetup,block_size]
  omega

lemma programStore_memory (w n k : ℕ) :
    (programStore w n k).imem =
      writeMemory 2 (wordStream n w [] w) (initialStore n k).imem := by
  unfold programStore
  rw [block_memory]
  simp

/- The concrete fixed-width enumerator, including input loading and halt,
writes exactly the full word stream, with polynomial charged time. -/
theorem word_stream_program (w : ℕ) :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 7*w+7 ∧
      ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
        ∃ steps ≤ (8*w+2)*(n+1)^w+5,
          let result := execute P n k d steps
          result.halted = true ∧ result.work = steps ∧
          result.queries = 0 ∧ result.tapePos = 0 ∧
          result.cfg.ptrs (w+1) = 2+((w+1)*(n+1)^w : ℕ) ∧
          result.imem = writeMemory 2 (wordStream n w [] w) (initialStore n k).imem ∧
          result.cfg.mem = (initialStore n k).mem := by
  refine ⟨program w,compile_deterministic _ _,program_length w,?_⟩
  intro n k d
  refine ⟨4+nestedCost w n w+1,program_cost_le w n,?_⟩
  dsimp only
  rw [(program_execution w n k d).2.2]
  have hf := programStore_frame w n k
  exact ⟨rfl,rfl,hf.2.2.1,hf.2.2.2,programStore_ptr_out w n k,
    programStore_memory w n k,hf.2.1⟩

/- A concrete finite program produces encodings of every bounded subset.
The subset statement reads the program's actual integer-memory records. -/
end StableMSR.Recovery.Compiler.TupleEnumeration

open StableMSR.Recovery.Compiler.TupleEnumeration StableMSR.Recovery.Compiler.TupleWriter
theorem solution (w : ℕ) :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 7*w+7 ∧
      ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
        ∃ steps ≤ (8*w+2)*(n+1)^w+5,
          let result := execute P n k d steps
          result.halted = true ∧ result.work = steps ∧
          result.queries = 0 ∧ result.tapePos = 0 ∧
          result.cfg.ptrs (w+1) = 2+((w+1)*(n+1)^w : ℕ) ∧
          result.imem 0 = (n : ℤ) ∧ result.imem 1 = (k : ℤ) ∧
          catalogWords n w result.imem = BoundedSubsetWords.words n w ∧
          (∀ S : Finset (Fin n), S.card ≤ w ↔
            ∃ j < (n+1)^w,
              BoundedSubsetWords.decode n
                (readWord w result.imem (2+((w+1)*j : ℕ))) = S) ∧
          (∀ a : ℤ, a < 2 ∨ 2+((w+1)*(n+1)^w : ℕ) ≤ a →
            result.imem a = (initialStore n k).imem a) ∧
          result.cfg.mem = (initialStore n k).mem := by
  obtain ⟨P,hP,hlen,hrun⟩ := word_stream_program w
  refine ⟨P,hP,hlen,?_⟩
  intro n k d
  obtain ⟨steps,hsteps,hh,hw,hq,ht,hout,hm,hreal⟩ := hrun n k d
  refine ⟨steps,hsteps,hh,hw,hq,ht,hout,?_,?_,?_,?_,?_,hreal⟩
  · rw [hm,writeMemory_before 2 0 _ _ (by omega)]
    simp [initialStore]
  · rw [hm,writeMemory_before 2 1 _ _ (by omega)]
    simp [initialStore]
  · rw [hm]
    exact catalogWords_writeMemory n w _
  · intro S
    rw [hm]
    exact memory_catalog_subset_iff n w _ S
  · intro a ha
    rw [hm]
    rcases ha with ha | ha
    · exact writeMemory_before 2 a _ _ ha
    · apply writeMemory_after
      simpa only [wordStream_length n w [] w (by simp)] using ha

