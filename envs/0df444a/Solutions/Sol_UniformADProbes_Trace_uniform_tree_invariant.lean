-- Prove2me | solution 1 for UniformADProbes.Trace.uniform_tree_invariant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:57:30.146994+00:00
-- url     : https://prove2.me/submissions/482c6097-eeca-468c-9eab-883cf9be9b3b

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Definitions.Def_UniformADProbes_Trace_circuits
import Theorems.Thm_UniformADProbes_Trace_distance_polynomials
import Theorems.Thm_UniformADProbes_Trace_uniform_spanning_probes
import Theorems.Thm_UniformADProbes_Trace_recover_pointed_representation
import Theorems.Thm_UniformADProbes_Trace_principal_moment_reconstruction

section
/-! The formal adjoint on `NCPoly` is additive, ℤ-linear and anti-multiplicative. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningAdj
open UniformADProbes.Trace
noncomputable section

def revWord (w : Word) : Word := FreeMonoid.ofList w.toList.reverse

def revHom : Word →* NCPolyᵐᵒᵖ where
  toFun w := MulOpposite.op (MonoidAlgebra.single (revWord w) (1 : ℤ))
  map_one' := by
    simp [revWord]
    rfl
  map_mul' a b := by
    simp only [revWord]
    rw [← MulOpposite.op_mul, MonoidAlgebra.single_mul_single]
    congr 2
    simp [FreeMonoid.toList_mul]

def L : NCPoly →ₐ[ℤ] NCPolyᵐᵒᵖ := MonoidAlgebra.lift ℤ NCPolyᵐᵒᵖ Word revHom

lemma adjoint_eq (p : NCPoly) : adjoint p = (L p).unop := by
  unfold adjoint L
  rw [MonoidAlgebra.lift_apply]
  rw [MulOpposite.unop_finsuppSum]
  refine Finsupp.sum_congr fun w _ => ?_
  simp only [revHom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op,
    revWord]
  rw [MonoidAlgebra.smul_single']
  simp

lemma adjoint_add (p q : NCPoly) : adjoint (p + q) = adjoint p + adjoint q := by
  rw [adjoint_eq, adjoint_eq, adjoint_eq, map_add]; rfl

lemma adjoint_zero : adjoint 0 = 0 := by
  rw [adjoint_eq, map_zero]; rfl

lemma adjoint_zsmul (c : ℤ) (p : NCPoly) : adjoint (c • p) = c • adjoint p := by
  rw [adjoint_eq, adjoint_eq, map_zsmul]; rfl

lemma adjoint_mul (p q : NCPoly) : adjoint (p * q) = adjoint q * adjoint p := by
  rw [adjoint_eq, adjoint_eq, adjoint_eq, map_mul]; rfl

lemma adjoint_one : adjoint 1 = 1 := by
  rw [adjoint_eq, map_one]; rfl

lemma adjoint_x : adjoint x = x := by
  unfold adjoint x
  rw [Finsupp.sum_single_index]
  · rfl
  · simp

lemma adjoint_y : adjoint y = y := by
  unfold adjoint y
  rw [Finsupp.sum_single_index]
  · rfl
  · simp

end
end UniformADProbes.Trace.Dev.SpanningAdj
end

section
/-! Register and degree arrays of a code array under `push`. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningCode
open UniformADProbes.Trace
noncomputable section

section
variable {R : Type} [Ring R]

def regs (H K : R) (c : Array Instruction) : Array R := registers ⟨c, 0⟩ H K

lemma regs_push (H K : R) (c : Array Instruction) (I : Instruction) :
    regs H K (c.push I) = (regs H K c).push (runInstruction H K (regs H K c) I) := by
  unfold regs registers
  simp [Array.foldl_push]

lemma regs_empty (H K : R) : regs H K #[] = #[] := by
  simp [regs, registers]

lemma regs_size (H K : R) (c : Array Instruction) : (regs H K c).size = c.size := by
  have : ∀ (l : List Instruction), ((l.foldl (fun regs instr => regs.push (runInstruction H K regs instr)) #[]) : Array R).size = l.length := by
    intro l
    suffices ∀ (acc : Array R), (l.foldl (fun regs instr => regs.push (runInstruction H K regs instr)) acc).size = acc.size + l.length by
      simpa using this #[]
    induction l with
    | nil => simp
    | cons a l ih => intro acc; simp [List.foldl_cons, ih]; omega
  unfold regs registers
  rw [← Array.foldl_toList]
  simpa using this c.toList

end

def degs (c : Array Instruction) : Array ℕ := degrees ⟨c, 0⟩

lemma degs_push (c : Array Instruction) (I : Instruction) :
    degs (c.push I) = (degs c).push (degreeInstruction (degs c) I) := by
  unfold degs degrees
  simp [Array.foldl_push]

lemma degs_empty : degs #[] = #[] := by simp [degs, degrees]

lemma degs_size (c : Array Instruction) : (degs c).size = c.size := by
  have : ∀ (l : List Instruction), ((l.foldl (fun d instr => d.push (degreeInstruction d instr)) #[]) : Array ℕ).size = l.length := by
    intro l
    suffices ∀ (acc : Array ℕ), (l.foldl (fun d instr => d.push (degreeInstruction d instr)) acc).size = acc.size + l.length by
      simpa using this #[]
    induction l with
    | nil => simp
    | cons a l ih => intro acc; simp [List.foldl_cons, ih]; omega
  unfold degs degrees
  rw [← Array.foldl_toList]
  simpa using this c.toList


/-- value of register `r` at (x,y) -/
abbrev rv (c : Array Instruction) (r : ℕ) : NCPoly := (regs x y c)[r]?.getD 0

abbrev dg (c : Array Instruction) (r : ℕ) : ℕ := (degs c)[r]?.getD 0

lemma rv_push (c : Array Instruction) (I : Instruction) (r : ℕ) :
    rv (c.push I) r = if r < c.size then rv c r else if r = c.size then
      runInstruction x y (regs x y c) I else 0 := by
  unfold rv
  rw [regs_push, Array.getElem?_push, regs_size]
  by_cases h1 : r < c.size
  · have : r ≠ c.size := by omega
    simp [h1, this]
  · by_cases h2 : r = c.size
    · simp [h2]
    · have : (regs x y c)[r]? = none := by
        rw [Array.getElem?_eq_none]; rw [regs_size]; omega
      simp [h1, h2, this]

lemma dg_push (c : Array Instruction) (I : Instruction) (r : ℕ) :
    dg (c.push I) r = if r < c.size then dg c r else if r = c.size then
      degreeInstruction (degs c) I else 0 := by
  unfold dg
  rw [degs_push, Array.getElem?_push, degs_size]
  by_cases h1 : r < c.size
  · have : r ≠ c.size := by omega
    simp [h1, this]
  · by_cases h2 : r = c.size
    · simp [h2]
    · have : (degs c)[r]? = none := by
        rw [Array.getElem?_eq_none]; rw [degs_size]; omega
      simp [h1, h2, this]

lemma rv_push_old (c : Array Instruction) (I : Instruction) (r : ℕ) (h : r < c.size) :
    rv (c.push I) r = rv c r := by
  rw [rv_push, if_pos h]

lemma rv_push_new (c : Array Instruction) (I : Instruction) :
    rv (c.push I) c.size = runInstruction x y (regs x y c) I := by
  rw [rv_push, if_neg (lt_irrefl _), if_pos rfl]

lemma dg_push_old (c : Array Instruction) (I : Instruction) (r : ℕ) (h : r < c.size) :
    dg (c.push I) r = dg c r := by
  rw [dg_push, if_pos h]

lemma dg_push_new (c : Array Instruction) (I : Instruction) :
    dg (c.push I) c.size = degreeInstruction (degs c) I := by
  rw [dg_push, if_neg (lt_irrefl _), if_pos rfl]

/-- the extension relation: old registers and degrees are unchanged -/
def Ext (c c' : Array Instruction) : Prop :=
  c.size ≤ c'.size ∧ ∀ r < c.size, rv c' r = rv c r ∧ dg c' r = dg c r

lemma Ext.refl (c : Array Instruction) : Ext c c := ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩⟩

lemma Ext.trans {c c' c'' : Array Instruction} (h : Ext c c') (h' : Ext c' c'') : Ext c c'' :=
  ⟨h.1.trans h'.1, fun r hr => by
    rw [(h'.2 r (lt_of_lt_of_le hr h.1)).1, (h'.2 r (lt_of_lt_of_le hr h.1)).2,
      (h.2 r hr).1, (h.2 r hr).2]
    exact ⟨rfl, rfl⟩⟩

lemma ext_push (c : Array Instruction) (I : Instruction) : Ext c (c.push I) := by
  refine ⟨by simp, fun r hr => ?_⟩
  rw [rv_push, dg_push, if_pos hr, if_pos hr]
  exact ⟨rfl, rfl⟩

end
end UniformADProbes.Trace.Dev.SpanningCode
end

section
/-! Pure versions of the dual-emission primitives and their semantic specifications. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningBody
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningAdj
noncomputable section

def pMul (c : Array Instruction) (a b : DualRef) : Array Instruction × DualRef :=
  ((c.push (.mul a.1 b.1)).push (.mul b.2 a.2), (c.size, c.size + 1))

def pAdd (c : Array Instruction) (a b : DualRef) : Array Instruction × DualRef :=
  ((c.push (.add a.1 b.1)).push (.add a.2 b.2), (c.size, c.size + 1))

def pScale (c : Array Instruction) (k : ℤ) (a : DualRef) : Array Instruction × DualRef :=
  ((c.push (.scale k a.1)).push (.scale k a.2), (c.size, c.size + 1))

def Sem (c : Array Instruction) (r : DualRef) (P : NCPoly) (e : ℕ) : Prop :=
  r.1 < c.size ∧ r.2 < c.size ∧ rv c r.1 = P ∧ rv c r.2 = adjoint P ∧ dg c r.1 ≤ e ∧
    dg c r.2 ≤ e

lemma Sem.mono {c c' : Array Instruction} {r : DualRef} {P : NCPoly} {e : ℕ}
    (h : Sem c r P e) (hx : Ext c c') : Sem c' r P e := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨lt_of_lt_of_le h1 hx.1, lt_of_lt_of_le h2 hx.1, ?_, ?_, ?_, ?_⟩
  · rw [(hx.2 _ h1).1]; exact h3
  · rw [(hx.2 _ h2).1]; exact h4
  · rw [(hx.2 _ h1).2]; exact h5
  · rw [(hx.2 _ h2).2]; exact h6

lemma Sem.le {c : Array Instruction} {r : DualRef} {P : NCPoly} {e e' : ℕ}
    (h : Sem c r P e) (he : e ≤ e') : Sem c r P e' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.trans he, h.2.2.2.2.2.trans he⟩

lemma pMul_size (c a b) : (pMul c a b).1.size = c.size + 2 := by simp [pMul]
lemma pAdd_size (c a b) : (pAdd c a b).1.size = c.size + 2 := by simp [pAdd]
lemma pScale_size (c k a) : (pScale c k a).1.size = c.size + 2 := by simp [pScale]

lemma pMul_ext (c a b) : Ext c (pMul c a b).1 := (ext_push _ _).trans (ext_push _ _)
lemma pAdd_ext (c a b) : Ext c (pAdd c a b).1 := (ext_push _ _).trans (ext_push _ _)
lemma pScale_ext (c k a) : Ext c (pScale c k a).1 := (ext_push _ _).trans (ext_push _ _)

lemma pMul_sem {c : Array Instruction} {a b : DualRef} {A B : NCPoly} {ea eb : ℕ}
    (ha : Sem c a A ea) (hb : Sem c b B eb) :
    Sem (pMul c a b).1 (pMul c a b).2 (A * B) (ea + eb) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  have hs : c.size + 1 = (c.push (Instruction.mul a.1 b.1)).size := by simp
  have e1 := (ext_push c (Instruction.mul a.1 b.1)).2
  unfold pMul Sem
  refine ⟨by simp, by simp, ?_, ?_, ?_, ?_⟩
  · simp only
    rw [rv_push_old _ _ _ (by simp), rv_push_new]
    show rv c a.1 * rv c b.1 = _
    rw [a3, b3]
  · simp only
    rw [hs, rv_push_new]
    show rv _ b.2 * rv _ a.2 = _
    rw [(e1 _ b2).1, (e1 _ a2).1, a4, b4,
      adjoint_mul]
  · simp only
    rw [dg_push_old _ _ _ (by simp), dg_push_new]
    show dg c a.1 + dg c b.1 ≤ _
    omega
  · simp only
    rw [hs, dg_push_new]
    show dg _ b.2 + dg _ a.2 ≤ _
    rw [(e1 _ b2).2, (e1 _ a2).2]
    omega

lemma pAdd_sem {c : Array Instruction} {a b : DualRef} {A B : NCPoly} {ea eb : ℕ}
    (ha : Sem c a A ea) (hb : Sem c b B eb) :
    Sem (pAdd c a b).1 (pAdd c a b).2 (A + B) (max ea eb) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  have hs : c.size + 1 = (c.push (Instruction.add a.1 b.1)).size := by simp
  have e1 := (ext_push c (Instruction.add a.1 b.1)).2
  unfold pAdd Sem
  refine ⟨by simp, by simp, ?_, ?_, ?_, ?_⟩
  · simp only
    rw [rv_push_old _ _ _ (by simp), rv_push_new]
    show rv c a.1 + rv c b.1 = _
    rw [a3, b3]
  · simp only
    rw [hs, rv_push_new]
    show rv _ a.2 + rv _ b.2 = _
    rw [(e1 _ b2).1, (e1 _ a2).1, a4, b4,
      adjoint_add]
  · simp only
    rw [dg_push_old _ _ _ (by simp), dg_push_new]
    show max (dg c a.1) (dg c b.1) ≤ _
    omega
  · simp only
    rw [hs, dg_push_new]
    show max (dg _ a.2) (dg _ b.2) ≤ _
    rw [(e1 _ b2).2, (e1 _ a2).2]
    omega

lemma pScale_sem {c : Array Instruction} {a : DualRef} {A : NCPoly} {ea : ℕ} (k : ℤ)
    (ha : Sem c a A ea) :
    Sem (pScale c k a).1 (pScale c k a).2 (k • A) ea := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  have hs : c.size + 1 = (c.push (Instruction.scale k a.1)).size := by simp
  have e1 := (ext_push c (Instruction.scale k a.1)).2
  unfold pScale Sem
  refine ⟨by simp, by simp, ?_, ?_, ?_, ?_⟩
  · simp only
    rw [rv_push_old _ _ _ (by simp), rv_push_new]
    show k • rv c a.1 = _
    rw [a3]
  · simp only
    rw [hs, rv_push_new]
    show k • rv _ a.2 = _
    rw [(e1 _ a2).1, a4, adjoint_zsmul]
  · simp only
    rw [dg_push_old _ _ _ (by simp), dg_push_new]
    show dg c a.1 ≤ _
    omega
  · simp only
    rw [hs, dg_push_new]
    show dg _ a.2 ≤ _
    rw [(e1 _ a2).2]
    omega

def BW (cd : Array Instruction) : Prop := ∀ r (h : r < cd.size), backward r cd[r]
def Lit (L : ℕ) (c : Array Instruction) : Prop :=
  ∀ I ∈ c.toList, ∀ k a, I = .scale k a → signedBits k ≤ L
def DGB (B : ℕ) (c : Array Instruction) : Prop := ∀ r, dg c r ≤ B

lemma BW.push {c : Array Instruction} (h : BW c) (I : Instruction) (hI : backward c.size I) :
    BW (c.push I) := by
  intro r hr
  rw [Array.getElem_push]
  by_cases h' : r < c.size
  · rw [dif_pos h']; exact h r h'
  · rw [dif_neg h']
    have : r = c.size := by simp at hr; omega
    subst this; exact hI

lemma BW.empty : BW #[] := fun r hr => by simp at hr

lemma Lit.push {L : ℕ} {c : Array Instruction} (h : Lit L c) (I : Instruction)
    (hI : ∀ k a, I = .scale k a → signedBits k ≤ L) : Lit L (c.push I) := by
  intro J hJ k a hk
  rw [Array.toList_push, List.mem_append] at hJ
  rcases hJ with hJ | hJ
  · exact h J hJ k a hk
  · simp at hJ; subst hJ; exact hI k a hk

lemma DGB.push {B : ℕ} {c : Array Instruction} (h : DGB B c) (I : Instruction)
    (hI : degreeInstruction (degs c) I ≤ B) : DGB B (c.push I) := by
  intro r
  rw [dg_push]
  split_ifs
  · exact h r
  · exact hI
  · exact Nat.zero_le _

lemma pMul_good {B L : ℕ} {c : Array Instruction} {a b : DualRef} {A A' : NCPoly} {ea eb : ℕ}
    (hbw : BW c) (hl : Lit L c) (hd : DGB B c) (ha : Sem c a A ea) (hb : Sem c b A' eb)
    (hB : ea + eb ≤ B) : BW (pMul c a b).1 ∧ Lit L (pMul c a b).1 ∧ DGB B (pMul c a b).1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  have e1 := (ext_push c (Instruction.mul a.1 b.1)).2
  unfold pMul
  refine ⟨?_, ?_, ?_⟩
  · refine (hbw.push (Instruction.mul a.1 b.1) ⟨a1, b1⟩).push (Instruction.mul b.2 a.2) ?_
    show b.2 < (c.push (Instruction.mul a.1 b.1)).size ∧ a.2 < (c.push (Instruction.mul a.1 b.1)).size
    simp only [Array.size_push]
    omega
  · exact (hl.push _ (by intro k a h; cases h)).push _ (by intro k a h; cases h)
  · refine (hd.push (Instruction.mul a.1 b.1) ?_).push (Instruction.mul b.2 a.2) ?_
    · show dg c a.1 + dg c b.1 ≤ B
      omega
    · show dg (c.push (Instruction.mul a.1 b.1)) b.2 + dg (c.push (Instruction.mul a.1 b.1)) a.2 ≤ B
      rw [(e1 _ b2).2, (e1 _ a2).2]
      omega

lemma pAdd_good {B L : ℕ} {c : Array Instruction} {a b : DualRef} {A A' : NCPoly} {ea eb : ℕ}
    (hbw : BW c) (hl : Lit L c) (hd : DGB B c) (ha : Sem c a A ea) (hb : Sem c b A' eb)
    (hB : max ea eb ≤ B) : BW (pAdd c a b).1 ∧ Lit L (pAdd c a b).1 ∧ DGB B (pAdd c a b).1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  have e1 := (ext_push c (Instruction.add a.1 b.1)).2
  unfold pAdd
  refine ⟨?_, ?_, ?_⟩
  · refine (hbw.push (Instruction.add a.1 b.1) ⟨a1, b1⟩).push (Instruction.add a.2 b.2) ?_
    show a.2 < (c.push (Instruction.add a.1 b.1)).size ∧ b.2 < (c.push (Instruction.add a.1 b.1)).size
    simp only [Array.size_push]
    omega
  · exact (hl.push _ (by intro k a h; cases h)).push _ (by intro k a h; cases h)
  · refine (hd.push (Instruction.add a.1 b.1) ?_).push (Instruction.add a.2 b.2) ?_
    · show max (dg c a.1) (dg c b.1) ≤ B
      omega
    · show max (dg (c.push (Instruction.add a.1 b.1)) a.2) (dg (c.push (Instruction.add a.1 b.1)) b.2) ≤ B
      rw [(e1 _ b2).2, (e1 _ a2).2]
      omega

lemma pScale_good {B L : ℕ} {c : Array Instruction} {a : DualRef} {A : NCPoly} {ea : ℕ} (k : ℤ)
    (hbw : BW c) (hl : Lit L c) (hd : DGB B c) (ha : Sem c a A ea)
    (hB : ea ≤ B) (hk : signedBits k ≤ L) :
    BW (pScale c k a).1 ∧ Lit L (pScale c k a).1 ∧ DGB B (pScale c k a).1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  have e1 := (ext_push c (Instruction.scale k a.1)).2
  unfold pScale
  refine ⟨?_, ?_, ?_⟩
  · refine (hbw.push (Instruction.scale k a.1) a1).push (Instruction.scale k a.2) ?_
    show a.2 < (c.push (Instruction.scale k a.1)).size
    simp only [Array.size_push]
    omega
  · refine (hl.push _ ?_).push _ ?_ <;> (intro k' a' h; cases h; exact hk)
  · refine (hd.push (Instruction.scale k a.1) ?_).push (Instruction.scale k a.2) ?_
    · show dg c a.1 ≤ B
      omega
    · show dg (c.push (Instruction.scale k a.1)) a.2 ≤ B
      rw [(e1 _ a2).2]
      omega

end
end UniformADProbes.Trace.Dev.SpanningBody
end

section
/-! Deterministic Hoare-style specifications of the emitter monad on the code array. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningRun
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
noncomputable section

/-- Running `m` on any state whose code is `c` returns `r` and leaves code `c'`. -/
def Trip {α : Type} (m : Emit α) (c : Array Instruction) (r : α) (c' : Array Instruction) : Prop :=
  ∀ st : Builder, st.code = c → (m.run st).1 = r ∧ (m.run st).2.code = c'

lemma Trip.bind {α β : Type} {m : Emit α} {f : α → Emit β} {c c1 c2 : Array Instruction}
    {r : α} {r2 : β} (hm : Trip m c r c1) (hf : Trip (f r) c1 r2 c2) :
    Trip (m >>= f) c r2 c2 := by
  intro st hst
  obtain ⟨h1, h2⟩ := hm st hst
  have := hf (m.run st).2 h2
  change ((f (m.run st).1).run (m.run st).2).1 = r2 ∧
    ((f (m.run st).1).run (m.run st).2).2.code = c2
  rw [h1]
  exact this

lemma Trip.pure' {α : Type} (x : α) (c : Array Instruction) : Trip (pure x : Emit α) c x c := by
  intro st hst
  exact ⟨rfl, hst⟩

lemma trip_emit (c : Array Instruction) (I : Instruction) :
    Trip (emit I) c c.size (c.push I) := by
  intro st hst
  subst hst
  exact ⟨rfl, rfl⟩

lemma trip_charge (c : Array Instruction) (k : ℕ) : Trip (charge k) c () c := by
  intro st hst
  exact ⟨rfl, hst⟩

lemma trip_tableGet (c : Array Instruction) (a : Array DualRef) (i : ℕ) (fb : DualRef) :
    Trip (tableGet a i fb) c (a[i]?.getD fb) c := by
  intro st hst
  exact ⟨rfl, hst⟩

lemma trip_dualMul (c : Array Instruction) (a b : DualRef) :
    Trip (dualMul a b) c (pMul c a b).2 (pMul c a b).1 := by
  unfold dualMul
  refine Trip.bind (trip_emit c _) ?_
  refine Trip.bind (trip_emit _ _) ?_
  have := Trip.pure' ((c.size, (c.push (Instruction.mul a.1 b.1)).size) : DualRef) ((c.push (Instruction.mul a.1 b.1)).push (Instruction.mul b.2 a.2))
  simpa [pMul, Array.size_push] using this

lemma trip_dualAdd (c : Array Instruction) (a b : DualRef) :
    Trip (dualAdd a b) c (pAdd c a b).2 (pAdd c a b).1 := by
  unfold dualAdd
  refine Trip.bind (trip_emit c _) ?_
  refine Trip.bind (trip_emit _ _) ?_
  have := Trip.pure' ((c.size, (c.push (Instruction.add a.1 b.1)).size) : DualRef) ((c.push (Instruction.add a.1 b.1)).push (Instruction.add a.2 b.2))
  simpa [pAdd, Array.size_push] using this

lemma trip_dualScale (c : Array Instruction) (k : ℤ) (a : DualRef) :
    Trip (dualScale k a) c (pScale c k a).2 (pScale c k a).1 := by
  unfold dualScale
  refine Trip.bind (trip_emit c _) ?_
  refine Trip.bind (trip_emit _ _) ?_
  have := Trip.pure' ((c.size, (c.push (Instruction.scale k a.1)).size) : DualRef) ((c.push (Instruction.scale k a.1)).push (Instruction.scale k a.2))
  simpa [pScale, Array.size_push] using this

lemma forIn_range'_trip {β : Type} (f : ℕ → β → Emit (ForInStep β))
    (P : ℕ → β → Array Instruction → Prop) :
    ∀ (m s : ℕ) (b : β) (c : Array Instruction), P s b c →
      (∀ j, s ≤ j → j < s + m → ∀ b c, P j b c →
        ∃ b' c', Trip (f j b) c (ForInStep.yield b') c' ∧ P (j + 1) b' c') →
      ∃ b' c', Trip (forIn (List.range' s m) b f) c b' c' ∧ P (s + m) b' c' := by
  intro m
  induction m with
  | zero =>
    intro s b c hP _
    refine ⟨b, c, ?_, by simpa using hP⟩
    rw [List.range'_zero, List.forIn_nil]
    exact Trip.pure' b c
  | succ m ih =>
    intro s b c hP hstep
    obtain ⟨b', c', hT, hP'⟩ := hstep s le_rfl (by omega) b c hP
    obtain ⟨b'', c'', hT2, hP''⟩ := ih (s + 1) b' c' hP' (fun j h1 h2 => hstep j (by omega)
      (by omega))
    refine ⟨b'', c'', ?_, by rw [show s + (m + 1) = s + 1 + m by omega]; exact hP''⟩
    rw [List.range'_succ, List.forIn_cons]
    exact Trip.bind hT hT2

end
end UniformADProbes.Trace.Dev.SpanningRun
end

section
/-! Row-sum norm bounds of the registers of a code array, by abstract interpretation. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalNB
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode
noncomputable section

theorem arr_ind {P : Array Instruction → Prop} (h0 : P #[])
    (hs : ∀ c I, P c → P (c.push I)) : ∀ c, P c := by
  intro c
  obtain ⟨l⟩ := c
  induction l using List.reverseRecOn with
  | nil => exact h0
  | append_singleton l I ih => simpa using hs _ I ih

def nbI (h : ℕ) (d : Array ℕ) : Instruction → ℕ
  | .identity => 1
  | .first => h
  | .second => h
  | .add a b => d[a]?.getD 0 + d[b]?.getD 0
  | .mul a b => d[a]?.getD 0 * d[b]?.getD 0
  | .scale c a => c.natAbs * d[a]?.getD 0

def nbs (h : ℕ) (c : Array Instruction) : Array ℕ :=
  c.foldl (fun d I => d.push (nbI h d I)) #[]

lemma nbs_push (h : ℕ) (c : Array Instruction) (I : Instruction) :
    nbs h (c.push I) = (nbs h c).push (nbI h (nbs h c) I) := by
  unfold nbs
  simp [Array.foldl_push]

lemma nbs_empty (h : ℕ) : nbs h #[] = #[] := by simp [nbs]

lemma nbs_size (h : ℕ) (c : Array Instruction) : (nbs h c).size = c.size := by
  refine arr_ind (P := fun c => (nbs h c).size = c.size) (by simp [nbs_empty]) ?_ c
  intro c I ih
  rw [nbs_push]; simp [ih]

/-- the abstract norm of register `r` -/
abbrev nb (h : ℕ) (c : Array Instruction) (r : ℕ) : ℕ := (nbs h c)[r]?.getD 0

lemma nb_push (h : ℕ) (c : Array Instruction) (I : Instruction) (r : ℕ) :
    nb h (c.push I) r = if r < c.size then nb h c r else if r = c.size then
      nbI h (nbs h c) I else 0 := by
  unfold nb
  rw [nbs_push, Array.getElem?_push, nbs_size]
  by_cases h1 : r < c.size
  · have : r ≠ c.size := by omega
    simp [h1, this]
  · by_cases h2 : r = c.size
    · simp [h2]
    · have : (nbs h c)[r]? = none := by
        rw [Array.getElem?_eq_none]; rw [nbs_size]; omega
      simp [h1, h2, this]

lemma nb_push_old (h : ℕ) (c : Array Instruction) (I : Instruction) (r : ℕ) (hr : r < c.size) :
    nb h (c.push I) r = nb h c r := by rw [nb_push, if_pos hr]

lemma nb_push_new (h : ℕ) (c : Array Instruction) (I : Instruction) :
    nb h (c.push I) c.size = nbI h (nbs h c) I := by
  rw [nb_push, if_neg (lt_irrefl _), if_pos rfl]

section RN
variable {n : ℕ}

def RN (M : Matrix (Fin n) (Fin n) ℤ) (β : ℕ) : Prop := ∀ i, ∑ j, |M i j| ≤ (β : ℤ)

lemma RN.mono {M : Matrix (Fin n) (Fin n) ℤ} {a b : ℕ} (h : RN M a) (hab : a ≤ b) : RN M b :=
  fun i => (h i).trans (by exact_mod_cast hab)

lemma RN.add {M M' : Matrix (Fin n) (Fin n) ℤ} {a b : ℕ} (h : RN M a) (h' : RN M' b) :
    RN (M + M') (a + b) := by
  intro i
  calc ∑ j, |(M + M') i j| ≤ ∑ j, (|M i j| + |M' i j|) :=
        Finset.sum_le_sum fun j _ => abs_add_le _ _
    _ = ∑ j, |M i j| + ∑ j, |M' i j| := Finset.sum_add_distrib
    _ ≤ a + b := by have := h i; have := h' i; push_cast; linarith

lemma RN.smul {M : Matrix (Fin n) (Fin n) ℤ} {a : ℕ} (c : ℤ) (h : RN M a) :
    RN (c • M) (c.natAbs * a) := by
  intro i
  have : ∑ j, |(c • M) i j| = |c| * ∑ j, |M i j| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [abs_mul]
  rw [this]
  push_cast
  rw [Int.abs_eq_natAbs]
  exact mul_le_mul_of_nonneg_left (h i) (by positivity)

lemma RN.mul {M M' : Matrix (Fin n) (Fin n) ℤ} {a b : ℕ} (h : RN M a) (h' : RN M' b) :
    RN (M * M') (a * b) := by
  intro i
  calc ∑ j, |(M * M') i j| = ∑ j, |∑ k, M i k * M' k j| := by simp [Matrix.mul_apply]
    _ ≤ ∑ j, ∑ k, |M i k| * |M' k j| := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        simp [abs_mul]
    _ = ∑ k, |M i k| * ∑ j, |M' k j| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ k, |M i k| * b := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact mul_le_mul_of_nonneg_left (h' k) (abs_nonneg _)
    _ = (∑ k, |M i k|) * b := by rw [Finset.sum_mul]
    _ ≤ a * b := by
        have := h i
        push_cast
        exact mul_le_mul_of_nonneg_right this (by positivity)

lemma RN.one : RN (1 : Matrix (Fin n) (Fin n) ℤ) 1 := by
  intro i
  simp only [Matrix.one_apply]
  have : ∀ j : Fin n, |if i = j then (1 : ℤ) else 0| = if i = j then 1 else 0 := by
    intro j; split_ifs <;> simp
  simp [this]

lemma RN.zero (a : ℕ) : RN (0 : Matrix (Fin n) (Fin n) ℤ) a := by
  intro i
  simp

lemma RN.entry {M : Matrix (Fin n) (Fin n) ℤ} {a : ℕ} (h : RN M a) (i j : Fin n) :
    |M i j| ≤ a :=
  (Finset.single_le_sum (f := fun j => |M i j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)).trans
    (h i)

lemma RN.trace {M : Matrix (Fin n) (Fin n) ℤ} {a : ℕ} (h : RN M a) :
    |Matrix.trace M| ≤ (n : ℤ) * a := by
  unfold Matrix.trace
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |Matrix.diag M i| ≤ ∑ _i : Fin n, (a : ℤ) := Finset.sum_le_sum fun i _ => h.entry i i
    _ = n * a := by simp

/-- Every register of a code array obeys its abstract norm. -/
theorem regs_RN (H K : Matrix (Fin n) (Fin n) ℤ) (h : ℕ) (hH : RN H h) (hK : RN K h)
    (c : Array Instruction) : ∀ r, RN ((regs H K c)[r]?.getD 0) (nb h c r) := by
  refine arr_ind (P := fun c => ∀ r, RN ((regs H K c)[r]?.getD 0) (nb h c r)) ?_ ?_ c
  · intro r
    simp [regs_empty, nbs_empty, nb]
    exact RN.zero _
  · intro c I ih r
    have hs := regs_size H K c
    rw [regs_push]
    unfold nb at *
    rw [nbs_push, Array.getElem?_push, Array.getElem?_push, hs, nbs_size]
    by_cases h1 : r < c.size
    · have : r ≠ c.size := by omega
      simp only [this, if_false]
      exact ih r
    · by_cases h2 : r = c.size
      · subst h2
        simp only [if_true]
        cases I with
        | identity => simpa [runInstruction, nbI] using RN.one
        | first => simpa [runInstruction, nbI] using hH
        | second => simpa [runInstruction, nbI] using hK
        | add a b => exact RN.add (ih a) (ih b)
        | mul a b => exact RN.mul (ih a) (ih b)
        | scale k a => exact RN.smul k (ih a)
      · have e1 : (regs H K c)[r]? = none := by
          rw [Array.getElem?_eq_none]; omega
        have e2 : (nbs h c)[r]? = none := by
          rw [Array.getElem?_eq_none]; rw [nbs_size]; omega
        simp [h1, h2, e1]
        exact RN.zero _

end RN

/-! Bit sizes of the abstract norms. -/

lemma size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  calc a * b < 2 ^ a.size * 2 ^ b.size := Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)
    _ = 2 ^ (a.size + b.size) := by rw [pow_add]

lemma size_add_le (a b : ℕ) : (a + b).size ≤ max a.size b.size + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ (max a.size b.size) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
  have hb : b < 2 ^ (max a.size b.size) :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  calc a + b < 2 ^ (max a.size b.size) + 2 ^ (max a.size b.size) := Nat.add_lt_add ha hb
    _ = 2 ^ (max a.size b.size + 1) := by rw [pow_succ]; ring

lemma size_mono {a b : ℕ} (h : a ≤ b) : a.size ≤ b.size := Nat.size_le_size h

/-- bit-size bound of the abstract norm of a dual reference -/
def NS (h : ℕ) (c : Array Instruction) (r : ℕ × ℕ) (s : ℕ) : Prop :=
  (nb h c r.1).size ≤ s ∧ (nb h c r.2).size ≤ s

def NBB (h T : ℕ) (c : Array Instruction) : Prop := ∀ r, (nb h c r).size ≤ T

lemma NS.mono {h : ℕ} {c c' : Array Instruction} {r : ℕ × ℕ} {s : ℕ}
    (hs : NS h c r s) (h1 : r.1 < c.size) (h2 : r.2 < c.size)
    (hx : ∀ k < c.size, nb h c' k = nb h c k) : NS h c' r s := by
  unfold NS at *
  rw [hx _ h1, hx _ h2]; exact hs

lemma NS.le {h : ℕ} {c : Array Instruction} {r : ℕ × ℕ} {s s' : ℕ} (hs : NS h c r s)
    (hss : s ≤ s') : NS h c r s' := ⟨hs.1.trans hss, hs.2.trans hss⟩

lemma NBB.le {h T T' : ℕ} {c : Array Instruction} (hb : NBB h T c) (hT : T ≤ T') :
    NBB h T' c := fun r => (hb r).trans hT

lemma NBB.push {h T T' : ℕ} {c : Array Instruction} (hb : NBB h T c) (I : Instruction)
    (hI : (nbI h (nbs h c) I).size ≤ T') (hT : T ≤ T') : NBB h T' (c.push I) := by
  intro r
  rw [nb_push]
  split_ifs
  · exact (hb r).trans hT
  · exact hI
  · simp

lemma nbI_mul (h : ℕ) (c : Array Instruction) (a b : ℕ) :
    nbI h (nbs h c) (.mul a b) = nb h c a * nb h c b := rfl

lemma nbI_add (h : ℕ) (c : Array Instruction) (a b : ℕ) :
    nbI h (nbs h c) (.add a b) = nb h c a + nb h c b := rfl

lemma nbI_scale (h : ℕ) (c : Array Instruction) (k : ℤ) (a : ℕ) :
    nbI h (nbs h c) (.scale k a) = k.natAbs * nb h c a := rfl

/-- `c` is a prefix of `c'` -/
def Pre (c c' : Array Instruction) : Prop := c.size ≤ c'.size ∧ ∀ k < c.size, c'[k]? = (c)[k]?

lemma Pre.trans {c c' c'' : Array Instruction} (h1 : Pre c c') (h2 : Pre c' c'') : Pre c c'' :=
  ⟨h1.1.trans h2.1, fun k hk => by rw [h2.2 k (lt_of_lt_of_le hk h1.1), h1.2 k hk]⟩

lemma Pre.push (c : Array Instruction) (I : Instruction) : Pre c (c.push I) := by
  refine ⟨by simp, fun k hk => ?_⟩
  rw [Array.getElem?_push_lt hk, Array.getElem?_eq_getElem hk]

lemma ext_of_pre (c : Array Instruction) : ∀ c' : Array Instruction, Pre c c' → Ext c c' := by
  refine arr_ind (P := fun c' => Pre c c' → Ext c c') ?_ ?_
  · intro h
    have h0 : c.size = 0 := by
      have := h.1; simp only [Array.size_empty] at this; omega
    have : c = #[] := Array.eq_empty_of_size_eq_zero h0
    subst this; exact Ext.refl _
  · intro c' I ih h
    by_cases hs : c.size = (c'.push I).size
    · have : c = c'.push I := by
        apply Array.ext hs
        intro k h1 h2
        have := h.2 k h1
        rw [Array.getElem?_eq_getElem h2, Array.getElem?_eq_getElem h1] at this
        exact (Option.some.inj this).symm
      subst this; exact Ext.refl _
    · have hle : c.size ≤ c'.size := by have := h.1; simp at this hs ⊢; omega
      have hp : Pre c c' := ⟨hle, fun k hk => by
        have := h.2 k hk
        rw [Array.getElem?_push_lt (by omega)] at this
        rw [Array.getElem?_eq_getElem (by omega : k < c'.size)]
        exact this⟩
      exact (ih hp).trans (ext_push c' I)

end

end UniformADProbes.Trace.Dev.GoalNB
end

section
/-! Cost-carrying Hoare triples for the emitter monad. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalCT
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun UniformADProbes.Trace.Dev.GoalNB
noncomputable section

/-- Running `m` on any state with code `c` returns `r`, leaves code `c'`, and costs at most `κ`. -/
def CT {α : Type} (m : Emit α) (c : Array Instruction) (r : α) (c' : Array Instruction) (κ : ℕ) :
    Prop :=
  ∀ st : Builder, st.code = c → (m.run st).1 = r ∧ (m.run st).2.code = c' ∧
    (m.run st).2.cost ≤ st.cost + κ

lemma CT.mono {α : Type} {m : Emit α} {c c' : Array Instruction} {r : α} {κ κ' : ℕ}
    (h : CT m c r c' κ) (hκ : κ ≤ κ') : CT m c r c' κ' := by
  intro st hst
  obtain ⟨h1, h2, h3⟩ := h st hst
  exact ⟨h1, h2, by omega⟩

lemma CT.bind {α β : Type} {m : Emit α} {f : α → Emit β} {c c1 c2 : Array Instruction}
    {r : α} {r2 : β} {κ1 κ2 : ℕ} (hm : CT m c r c1 κ1) (hf : CT (f r) c1 r2 c2 κ2) :
    CT (m >>= f) c r2 c2 (κ1 + κ2) := by
  intro st hst
  obtain ⟨h1, h2, h3⟩ := hm st hst
  obtain ⟨g1, g2, g3⟩ := hf (m.run st).2 h2
  change ((f (m.run st).1).run (m.run st).2).1 = r2 ∧
    ((f (m.run st).1).run (m.run st).2).2.code = c2 ∧
    ((f (m.run st).1).run (m.run st).2).2.cost ≤ st.cost + (κ1 + κ2)
  rw [h1]
  exact ⟨g1, g2, by omega⟩

lemma CT.pure' {α : Type} (x : α) (c : Array Instruction) : CT (pure x : Emit α) c x c 0 := by
  intro st hst
  exact ⟨rfl, hst, le_of_eq (by simp; rfl)⟩

/-- bits of the stored code -/
def bb (c : Array Instruction) : ℕ := c.foldl (fun b I => b + instructionBits I) 1

lemma ct_emit (c : Array Instruction) (I : Instruction) :
    CT (emit I) c c.size (c.push I) (bb c + instructionBits I + refBits c.size + 1) := by
  intro st hst
  subst hst
  refine ⟨rfl, rfl, ?_⟩
  change st.cost + builderBits st + instructionBits I + refBits st.code.size + 1 ≤ _
  unfold builderBits bb
  omega

lemma ct_charge (c : Array Instruction) (k : ℕ) : CT (charge k) c () c (k + 1) := by
  intro st hst
  exact ⟨rfl, hst, le_of_eq (by change st.cost + k + 1 = _; omega)⟩

lemma ct_tableGet (c : Array Instruction) (a : Array DualRef) (i : ℕ) (fb : DualRef) :
    CT (tableGet a i fb) c (a[i]?.getD fb) c
      (1 + refBits i + a.foldl (fun c r => c + refBits r.1 + refBits r.2) 0 + 1) := by
  intro st hst
  refine ⟨rfl, hst, le_of_eq ?_⟩
  change st.cost + (1 + refBits i + a.foldl (fun c r => c + refBits r.1 + refBits r.2) 0) + 1 = _
  omega

lemma forIn_range'_ct {β : Type} (f : ℕ → β → Emit (ForInStep β))
    (P : ℕ → β → Array Instruction → Prop) (E : ℕ) :
    ∀ (m s : ℕ) (b : β) (c : Array Instruction), P s b c →
      (∀ j, s ≤ j → j < s + m → ∀ b c, P j b c →
        ∃ b' c' κ, CT (f j b) c (ForInStep.yield b') c' κ ∧ κ ≤ E ∧ P (j + 1) b' c') →
      ∃ b' c', CT (forIn (List.range' s m) b f) c b' c' (m * E) ∧ P (s + m) b' c' := by
  intro m
  induction m with
  | zero =>
    intro s b c hP _
    refine ⟨b, c, ?_, by simpa using hP⟩
    rw [List.range'_zero, List.forIn_nil]
    simpa using CT.pure' b c
  | succ m ih =>
    intro s b c hP hstep
    obtain ⟨b', c', κ, hT, hκ, hP'⟩ := hstep s le_rfl (by omega) b c hP
    obtain ⟨b'', c'', hT2, hP''⟩ := ih (s + 1) b' c' hP' (fun j h1 h2 => hstep j (by omega)
      (by omega))
    refine ⟨b'', c'', ?_, by rw [show s + (m + 1) = s + 1 + m by omega]; exact hP''⟩
    rw [List.range'_succ, List.forIn_cons]
    refine (CT.bind (hT.mono hκ) hT2).mono ?_
    nlinarith

/-! Instruction-bit bounds -/

/-- every instruction has at most `β` bits -/
def IBd (β : ℕ) (c : Array Instruction) : Prop := ∀ J ∈ c.toList, instructionBits J ≤ β

lemma IBd.empty (β : ℕ) : IBd β #[] := fun J hJ => by simp at hJ

lemma IBd.push {β : ℕ} {c : Array Instruction} (h : IBd β c) (I : Instruction)
    (hI : instructionBits I ≤ β) : IBd β (c.push I) := by
  intro J hJ
  rw [Array.toList_push, List.mem_append] at hJ
  rcases hJ with hJ | hJ
  · exact h J hJ
  · simp at hJ; subst hJ; exact hI

lemma foldl_bits_le (β : ℕ) (l : List Instruction) (hl : ∀ J ∈ l, instructionBits J ≤ β) (acc : ℕ) :
    l.foldl (fun b I => b + instructionBits I) acc ≤ acc + l.length * β := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (fun J hJ => hl J (List.mem_cons_of_mem _ hJ)) (acc + instructionBits a)
    have h2 := hl a (List.mem_cons_self ..)
    nlinarith

lemma bb_le {β : ℕ} {c : Array Instruction} (h : IBd β c) : bb c ≤ 1 + c.size * β := by
  unfold bb
  rw [← Array.foldl_toList]
  have := foldl_bits_le β c.toList h 1
  simpa using this

lemma refBits_le (r : ℕ) : refBits r ≤ r + 1 := by
  unfold refBits
  have : r.size ≤ r := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

/-- the bit bound of an instruction whose references are at most `cap` and literals at most `L` -/
def beta (cap L : ℕ) : ℕ := 3 + 2 * (cap + 1) + L

def RefOk (cap L : ℕ) : Instruction → Prop
  | .identity | .first | .second => True
  | .add a b | .mul a b => a ≤ cap ∧ b ≤ cap
  | .scale c a => a ≤ cap ∧ signedBits c ≤ L

lemma instructionBits_le {cap L : ℕ} {I : Instruction} (h : RefOk cap L I) :
    instructionBits I ≤ beta cap L := by
  unfold beta
  cases I with
  | identity => simp [instructionBits]; omega
  | first => simp [instructionBits]; omega
  | second => simp [instructionBits]; omega
  | add a b =>
    obtain ⟨h1, h2⟩ := h
    have := refBits_le a; have := refBits_le b
    simp only [instructionBits]; omega
  | mul a b =>
    obtain ⟨h1, h2⟩ := h
    have := refBits_le a; have := refBits_le b
    simp only [instructionBits]; omega
  | scale k a =>
    obtain ⟨h1, h2⟩ := h
    have := refBits_le a
    simp only [instructionBits]; omega

/-- uniform cost of one emission -/
def Eb (cap L : ℕ) : ℕ := (cap + 1) * beta cap L + cap + 3

lemma ct_emit_le {cap L : ℕ} {c : Array Instruction} (hIB : IBd (beta cap L) c)
    (hsz : c.size ≤ cap) (I : Instruction) (hI : RefOk cap L I) :
    CT (emit I) c c.size (c.push I) (Eb cap L) := by
  refine (ct_emit c I).mono ?_
  have h1 := bb_le hIB
  have h2 := instructionBits_le hI
  have h3 := refBits_le c.size
  unfold Eb
  have : c.size * beta cap L ≤ cap * beta cap L := Nat.mul_le_mul_right _ hsz
  nlinarith

end
end UniformADProbes.Trace.Dev.GoalCT
end

section
/-! Dual operations: cost, instruction bits, and abstract-norm sizes. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalOps
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun UniformADProbes.Trace.Dev.GoalNB UniformADProbes.Trace.Dev.GoalCT
noncomputable section

/-- references of a dual reference lie below `k` -/
def Rl (k : ℕ) (r : DualRef) : Prop := r.1 < k ∧ r.2 < k

lemma pMul_ct {cap L : ℕ} {c : Array Instruction} (hIB : IBd (beta cap L) c) (hsz : c.size + 2 ≤ cap)
    {a b : DualRef} (ha : Rl c.size a) (hb : Rl c.size b) :
    CT (dualMul a b) c (pMul c a b).2 (pMul c a b).1 (2 * Eb cap L) := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  unfold dualMul
  refine CT.mono (κ := Eb cap L + (Eb cap L + 0)) ?_ (by omega)
  have h1 := ct_emit_le hIB (by omega) (Instruction.mul a.1 b.1) ⟨by omega, by omega⟩
  refine CT.bind h1 ?_
  have hIB1 : IBd (beta cap L) (c.push (Instruction.mul a.1 b.1)) :=
    hIB.push (Instruction.mul a.1 b.1) (instructionBits_le (I := Instruction.mul a.1 b.1) ⟨by omega, by omega⟩)
  have h2 := ct_emit_le hIB1 (by simp; omega) (Instruction.mul b.2 a.2)
    ⟨by omega, by omega⟩
  refine CT.bind h2 ?_
  have := CT.pure' ((c.size, (c.push (Instruction.mul a.1 b.1)).size) : DualRef)
    ((c.push (Instruction.mul a.1 b.1)).push (Instruction.mul b.2 a.2))
  simpa [pMul, Array.size_push] using this

lemma pAdd_ct {cap L : ℕ} {c : Array Instruction} (hIB : IBd (beta cap L) c) (hsz : c.size + 2 ≤ cap)
    {a b : DualRef} (ha : Rl c.size a) (hb : Rl c.size b) :
    CT (dualAdd a b) c (pAdd c a b).2 (pAdd c a b).1 (2 * Eb cap L) := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  unfold dualAdd
  refine CT.mono (κ := Eb cap L + (Eb cap L + 0)) ?_ (by omega)
  have h1 := ct_emit_le hIB (by omega) (Instruction.add a.1 b.1) ⟨by omega, by omega⟩
  refine CT.bind h1 ?_
  have hIB1 : IBd (beta cap L) (c.push (Instruction.add a.1 b.1)) :=
    hIB.push (Instruction.add a.1 b.1) (instructionBits_le (I := Instruction.add a.1 b.1) ⟨by omega, by omega⟩)
  have h2 := ct_emit_le hIB1 (by simp; omega) (Instruction.add a.2 b.2)
    ⟨by omega, by omega⟩
  refine CT.bind h2 ?_
  have := CT.pure' ((c.size, (c.push (Instruction.add a.1 b.1)).size) : DualRef)
    ((c.push (Instruction.add a.1 b.1)).push (Instruction.add a.2 b.2))
  simpa [pAdd, Array.size_push] using this

lemma pScale_ct {cap L : ℕ} {c : Array Instruction} (hIB : IBd (beta cap L) c) (hsz : c.size + 2 ≤ cap)
    {a : DualRef} (ha : Rl c.size a) (k : ℤ) (hk : signedBits k ≤ L) :
    CT (dualScale k a) c (pScale c k a).2 (pScale c k a).1 (2 * Eb cap L) := by
  obtain ⟨a1, a2⟩ := ha
  unfold dualScale
  refine CT.mono (κ := Eb cap L + (Eb cap L + 0)) ?_ (by omega)
  have h1 := ct_emit_le hIB (by omega) (Instruction.scale k a.1) ⟨by omega, hk⟩
  refine CT.bind h1 ?_
  have hIB1 : IBd (beta cap L) (c.push (Instruction.scale k a.1)) :=
    hIB.push (Instruction.scale k a.1) (instructionBits_le (I := Instruction.scale k a.1) ⟨by omega, hk⟩)
  have h2 := ct_emit_le hIB1 (by simp; omega) (Instruction.scale k a.2)
    ⟨by omega, hk⟩
  refine CT.bind h2 ?_
  have := CT.pure' ((c.size, (c.push (Instruction.scale k a.1)).size) : DualRef)
    ((c.push (Instruction.scale k a.1)).push (Instruction.scale k a.2))
  simpa [pScale, Array.size_push] using this

/-! Instruction bits after the pure steps -/

lemma pMul_ib {cap L : ℕ} {c : Array Instruction} (hIB : IBd (beta cap L) c) (hsz : c.size + 2 ≤ cap)
    {a b : DualRef} (ha : Rl c.size a) (hb : Rl c.size b) : IBd (beta cap L) (pMul c a b).1 := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  unfold pMul
  exact (hIB.push (Instruction.mul a.1 b.1) (instructionBits_le (I := Instruction.mul a.1 b.1)
    ⟨by omega, by omega⟩)).push (Instruction.mul b.2 a.2)
    (instructionBits_le (I := Instruction.mul b.2 a.2) ⟨by omega, by omega⟩)

lemma pAdd_ib {cap L : ℕ} {c : Array Instruction} (hIB : IBd (beta cap L) c) (hsz : c.size + 2 ≤ cap)
    {a b : DualRef} (ha : Rl c.size a) (hb : Rl c.size b) : IBd (beta cap L) (pAdd c a b).1 := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  unfold pAdd
  exact (hIB.push (Instruction.add a.1 b.1) (instructionBits_le (I := Instruction.add a.1 b.1)
    ⟨by omega, by omega⟩)).push (Instruction.add a.2 b.2)
    (instructionBits_le (I := Instruction.add a.2 b.2) ⟨by omega, by omega⟩)

lemma pScale_ib {cap L : ℕ} {c : Array Instruction} (hIB : IBd (beta cap L) c) (hsz : c.size + 2 ≤ cap)
    {a : DualRef} (ha : Rl c.size a) (k : ℤ) (hk : signedBits k ≤ L) :
    IBd (beta cap L) (pScale c k a).1 := by
  obtain ⟨a1, a2⟩ := ha
  unfold pScale
  exact (hIB.push (Instruction.scale k a.1) (instructionBits_le (I := Instruction.scale k a.1)
    ⟨by omega, hk⟩)).push (Instruction.scale k a.2)
    (instructionBits_le (I := Instruction.scale k a.2) ⟨by omega, hk⟩)

/-! Abstract norms after the pure steps -/

lemma nb_ext_push2 (h : ℕ) (c : Array Instruction) (I J : Instruction) (k : ℕ) (hk : k < c.size) :
    nb h ((c.push I).push J) k = nb h c k := by
  rw [nb_push_old h _ J k (by simp; omega), nb_push_old h c I k hk]

lemma pMul_nb {h : ℕ} {c : Array Instruction} {a b : DualRef} {sa sb : ℕ}
    (ha : Rl c.size a) (hb : Rl c.size b) (hsa : NS h c a sa) (hsb : NS h c b sb) :
    NS h (pMul c a b).1 (pMul c a b).2 (sa + sb) := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  unfold pMul NS
  simp only []
  constructor
  · rw [nb_push_old h _ _ c.size (by simp), nb_push_new, nbI_mul]
    exact (size_mul_le _ _).trans (Nat.add_le_add hsa.1 hsb.1)
  · have e : (c.push (Instruction.mul a.1 b.1)).size = c.size + 1 := by simp
    rw [← e, nb_push_new, nbI_mul, nb_push_old h c _ b.2 b2, nb_push_old h c _ a.2 a2]
    exact (size_mul_le _ _).trans (by have := hsa.2; have := hsb.2; omega)

lemma pAdd_nb {h : ℕ} {c : Array Instruction} {a b : DualRef} {sa sb : ℕ}
    (ha : Rl c.size a) (hb : Rl c.size b) (hsa : NS h c a sa) (hsb : NS h c b sb) :
    NS h (pAdd c a b).1 (pAdd c a b).2 (max sa sb + 1) := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  unfold pAdd NS
  simp only []
  constructor
  · rw [nb_push_old h _ _ c.size (by simp), nb_push_new, nbI_add]
    refine (size_add_le _ _).trans ?_
    have := hsa.1; have := hsb.1
    have : max (nb h c a.1).size (nb h c b.1).size ≤ max sa sb := max_le_max hsa.1 hsb.1
    omega
  · have e : (c.push (Instruction.add a.1 b.1)).size = c.size + 1 := by simp
    rw [← e, nb_push_new, nbI_add, nb_push_old h c _ a.2 a2, nb_push_old h c _ b.2 b2]
    refine (size_add_le _ _).trans ?_
    have : max (nb h c a.2).size (nb h c b.2).size ≤ max sa sb := max_le_max hsa.2 hsb.2
    omega

lemma pScale_nb {h : ℕ} {c : Array Instruction} {a : DualRef} {sa : ℕ} (k : ℤ)
    (ha : Rl c.size a) (hsa : NS h c a sa) :
    NS h (pScale c k a).1 (pScale c k a).2 (k.natAbs.size + sa) := by
  obtain ⟨a1, a2⟩ := ha
  unfold pScale NS
  simp only []
  constructor
  · rw [nb_push_old h _ _ c.size (by simp), nb_push_new, nbI_scale]
    exact (size_mul_le _ _).trans (Nat.add_le_add_left hsa.1 _)
  · have e : (c.push (Instruction.scale k a.1)).size = c.size + 1 := by simp
    rw [← e, nb_push_new, nbI_scale, nb_push_old h c _ a.2 a2]
    exact (size_mul_le _ _).trans (Nat.add_le_add_left hsa.2 _)

lemma pMul_nbb {h T : ℕ} {c : Array Instruction} {a b : DualRef} {sa sb : ℕ}
    (ha : Rl c.size a) (hb : Rl c.size b) (hsa : NS h c a sa) (hsb : NS h c b sb)
    (hT : NBB h T c) : NBB h (max T (sa + sb)) (pMul c a b).1 := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  unfold pMul
  have hle : T ≤ max T (sa + sb) := le_max_left _ _
  have h1 : NBB h (max T (sa + sb)) (c.push (Instruction.mul a.1 b.1)) := by
    refine (hT.le hle).push _ ?_ le_rfl
    rw [nbI_mul]
    exact (size_mul_le _ _).trans ((Nat.add_le_add hsa.1 hsb.1).trans (le_max_right _ _))
  refine h1.push _ ?_ le_rfl
  rw [nbI_mul, nb_push_old h c _ b.2 b2, nb_push_old h c _ a.2 a2]
  exact (size_mul_le _ _).trans ((by have := hsa.2; have := hsb.2; omega : _ ≤ sa + sb).trans
    (le_max_right _ _))

lemma pAdd_nbb {h T : ℕ} {c : Array Instruction} {a b : DualRef} {sa sb : ℕ}
    (ha : Rl c.size a) (hb : Rl c.size b) (hsa : NS h c a sa) (hsb : NS h c b sb)
    (hT : NBB h T c) : NBB h (max T (max sa sb + 1)) (pAdd c a b).1 := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  unfold pAdd
  have hle : T ≤ max T (max sa sb + 1) := le_max_left _ _
  have h1 : NBB h (max T (max sa sb + 1)) (c.push (Instruction.add a.1 b.1)) := by
    refine (hT.le hle).push _ ?_ le_rfl
    rw [nbI_add]
    refine (size_add_le _ _).trans ((by
      have : max (nb h c a.1).size (nb h c b.1).size ≤ max sa sb := max_le_max hsa.1 hsb.1
      omega : _ ≤ max sa sb + 1).trans (le_max_right _ _))
  refine h1.push _ ?_ le_rfl
  rw [nbI_add, nb_push_old h c _ a.2 a2, nb_push_old h c _ b.2 b2]
  refine (size_add_le _ _).trans ((by
      have : max (nb h c a.2).size (nb h c b.2).size ≤ max sa sb := max_le_max hsa.2 hsb.2
      omega : _ ≤ max sa sb + 1).trans (le_max_right _ _))

lemma pScale_nbb {h T : ℕ} {c : Array Instruction} {a : DualRef} {sa : ℕ} (k : ℤ)
    (ha : Rl c.size a) (hsa : NS h c a sa) (hT : NBB h T c) :
    NBB h (max T (k.natAbs.size + sa)) (pScale c k a).1 := by
  obtain ⟨a1, a2⟩ := ha
  unfold pScale
  have hle : T ≤ max T (k.natAbs.size + sa) := le_max_left _ _
  have h1 : NBB h (max T (k.natAbs.size + sa)) (c.push (Instruction.scale k a.1)) := by
    refine (hT.le hle).push _ ?_ le_rfl
    rw [nbI_scale]
    exact (size_mul_le _ _).trans ((Nat.add_le_add_left hsa.1 _).trans (le_max_right _ _))
  refine h1.push _ ?_ le_rfl
  rw [nbI_scale, nb_push_old h c _ a.2 a2]
  exact (size_mul_le _ _).trans ((Nat.add_le_add_left hsa.2 _).trans (le_max_right _ _))

lemma pMul_rl {c : Array Instruction} {a b : DualRef} {k : ℕ} (hk : c.size + 2 ≤ k) :
    Rl k (pMul c a b).2 := by
  unfold pMul Rl; simp only []; omega

lemma pAdd_rl {c : Array Instruction} {a b : DualRef} {k : ℕ} (hk : c.size + 2 ≤ k) :
    Rl k (pAdd c a b).2 := by
  unfold pAdd Rl; simp only []; omega

lemma pScale_rl {c : Array Instruction} {a : DualRef} {k : ℕ} {m : ℤ} (hk : c.size + 2 ≤ k) :
    Rl k (pScale c m a).2 := by
  unfold pScale Rl; simp only []; omega

lemma Rl.mono {k k' : ℕ} {r : DualRef} (h : Rl k r) (hk : k ≤ k') : Rl k' r :=
  ⟨by have := h.1; omega, by have := h.2; omega⟩

/-- the old norms and instructions are untouched by a pure step -/
def Kept (h : ℕ) (c c' : Array Instruction) : Prop :=
  c.size ≤ c'.size ∧ (∀ k < c.size, nb h c' k = nb h c k) ∧ ∀ k < c.size, c'[k]? = (c)[k]?

lemma Kept.refl (h : ℕ) (c : Array Instruction) : Kept h c c :=
  ⟨le_rfl, fun _ _ => rfl, fun _ _ => rfl⟩

lemma Kept.trans {h : ℕ} {c c' c'' : Array Instruction} (h1 : Kept h c c') (h2 : Kept h c' c'') :
    Kept h c c'' :=
  ⟨h1.1.trans h2.1, fun k hk => by rw [h2.2.1 k (lt_of_lt_of_le hk h1.1), h1.2.1 k hk],
    fun k hk => by rw [h2.2.2 k (lt_of_lt_of_le hk h1.1), h1.2.2 k hk]⟩

lemma Kept.pre {h : ℕ} {c c' : Array Instruction} (hk : Kept h c c') : Pre c c' := ⟨hk.1, hk.2.2⟩

lemma ns_kept {h : ℕ} {c c' : Array Instruction} {r : DualRef} {s : ℕ} (hs : NS h c r s)
    (hr : Rl c.size r) (hk : Kept h c c') : NS h c' r s := NS.mono hs hr.1 hr.2 hk.2.1

lemma pMul_kept (h : ℕ) (c : Array Instruction) (a b : DualRef) : Kept h c (pMul c a b).1 := by
  unfold pMul
  refine ⟨by simp; omega, fun k hk => nb_ext_push2 h c _ _ k hk, fun k hk => ?_⟩
  exact (Pre.push c _).trans (Pre.push _ _) |>.2 k hk

lemma pAdd_kept (h : ℕ) (c : Array Instruction) (a b : DualRef) : Kept h c (pAdd c a b).1 := by
  unfold pAdd
  refine ⟨by simp; omega, fun k hk => nb_ext_push2 h c _ _ k hk, fun k hk => ?_⟩
  exact (Pre.push c _).trans (Pre.push _ _) |>.2 k hk

lemma pScale_kept (h : ℕ) (c : Array Instruction) (m : ℤ) (a : DualRef) :
    Kept h c (pScale c m a).1 := by
  unfold pScale
  refine ⟨by simp; omega, fun k hk => nb_ext_push2 h c _ _ k hk, fun k hk => ?_⟩
  exact (Pre.push c _).trans (Pre.push _ _) |>.2 k hk

lemma mul_step {cap L h T : ℕ} {c : Array Instruction} (hIB : IBd (beta cap L) c)
    (hsz : c.size + 2 ≤ cap) {a b : DualRef} {sa sb : ℕ} (ha : Rl c.size a) (hb : Rl c.size b)
    (hsa : NS h c a sa) (hsb : NS h c b sb) (hT : NBB h T c) :
    IBd (beta cap L) (pMul c a b).1 ∧ NS h (pMul c a b).1 (pMul c a b).2 (sa + sb) ∧
    NBB h (max T (sa + sb)) (pMul c a b).1 ∧ Kept h c (pMul c a b).1 ∧
    (pMul c a b).1.size = c.size + 2 ∧ Rl (pMul c a b).1.size (pMul c a b).2 ∧
    CT (dualMul a b) c (pMul c a b).2 (pMul c a b).1 (2 * Eb cap L) :=
  ⟨pMul_ib hIB hsz ha hb, pMul_nb ha hb hsa hsb, pMul_nbb ha hb hsa hsb hT, pMul_kept h c a b,
    pMul_size c a b, pMul_rl (by rw [pMul_size]), pMul_ct hIB hsz ha hb⟩

lemma add_step {cap L h T : ℕ} {c : Array Instruction} (hIB : IBd (beta cap L) c)
    (hsz : c.size + 2 ≤ cap) {a b : DualRef} {sa sb : ℕ} (ha : Rl c.size a) (hb : Rl c.size b)
    (hsa : NS h c a sa) (hsb : NS h c b sb) (hT : NBB h T c) :
    IBd (beta cap L) (pAdd c a b).1 ∧ NS h (pAdd c a b).1 (pAdd c a b).2 (max sa sb + 1) ∧
    NBB h (max T (max sa sb + 1)) (pAdd c a b).1 ∧ Kept h c (pAdd c a b).1 ∧
    (pAdd c a b).1.size = c.size + 2 ∧ Rl (pAdd c a b).1.size (pAdd c a b).2 ∧
    CT (dualAdd a b) c (pAdd c a b).2 (pAdd c a b).1 (2 * Eb cap L) :=
  ⟨pAdd_ib hIB hsz ha hb, pAdd_nb ha hb hsa hsb, pAdd_nbb ha hb hsa hsb hT, pAdd_kept h c a b,
    pAdd_size c a b, pAdd_rl (by rw [pAdd_size]), pAdd_ct hIB hsz ha hb⟩

lemma scale_step {cap L h T : ℕ} {c : Array Instruction} (hIB : IBd (beta cap L) c)
    (hsz : c.size + 2 ≤ cap) {a : DualRef} {sa : ℕ} (m : ℤ) (hm : signedBits m ≤ L)
    (ha : Rl c.size a) (hsa : NS h c a sa) (hT : NBB h T c) :
    IBd (beta cap L) (pScale c m a).1 ∧ NS h (pScale c m a).1 (pScale c m a).2 (m.natAbs.size + sa) ∧
    NBB h (max T (m.natAbs.size + sa)) (pScale c m a).1 ∧ Kept h c (pScale c m a).1 ∧
    (pScale c m a).1.size = c.size + 2 ∧ Rl (pScale c m a).1.size (pScale c m a).2 ∧
    CT (dualScale m a) c (pScale c m a).2 (pScale c m a).1 (2 * Eb cap L) :=
  ⟨pScale_ib hIB hsz ha m hm, pScale_nb m ha hsa, pScale_nbb m ha hsa hT, pScale_kept h c m a,
    pScale_size c m a, pScale_rl (by rw [pScale_size]), pScale_ct hIB hsz ha m hm⟩

end
end UniformADProbes.Trace.Dev.GoalOps
end

section
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.Dist
open UniformADProbes.Trace

section eval
variable {R : Type} [Ring R]

def fmon (H K : R) : Bool → R := fun b => if b then K else H

lemma wordEval_eq (H K : R) (w : Word) : wordEval H K w = FreeMonoid.lift (fmon H K) w := by
  simp [wordEval, FreeMonoid.lift_apply, List.prod_eq_foldr, fmon, List.foldr_map]

noncomputable def ev (H K : R) : NCPoly →ₐ[ℤ] R :=
  MonoidAlgebra.lift ℤ R Word (FreeMonoid.lift (fmon H K))

lemma polyEval_eq_ev (H K : R) (p : NCPoly) : polyEval H K p = ev H K p := by
  rw [ev, MonoidAlgebra.lift_apply]
  simp [polyEval, wordEval_eq]

lemma polyEval_x (H K : R) : polyEval H K x = H := by
  simp [polyEval, x, wordEval]

lemma polyEval_y (H K : R) : polyEval H K y = K := by
  simp [polyEval, y, wordEval]

lemma wordEval_map {S : Type} [Ring S] (φ : R →+* S) (H K : R) (w : Word) :
    φ (wordEval H K w) = wordEval (φ H) (φ K) w := by
  unfold wordEval
  induction w.toList with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, map_mul, ih]
    cases b <;> simp

lemma polyEval_map {S : Type} [Ring S] (φ : R →+* S) (H K : R) (p : NCPoly) :
    φ (polyEval H K p) = polyEval (φ H) (φ K) p := by
  unfold polyEval
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun w _ => ?_
  rw [map_zsmul, wordEval_map]

end eval

section tree
open scoped Classical
variable {n : ℕ} {T : SimpleGraph (Fin n)}

lemma adj_apply (i j : Fin n) : adjacency T i j = if T.Adj i j then 1 else 0 := by
  unfold adjacency; rfl

lemma deg_eq (u : Fin n) :
    degreeMatrix T u u = ((Finset.univ.filter (fun w => T.Adj u w)).card : ℤ) := by
  unfold degreeMatrix
  simp only [Matrix.diagonal_apply_eq]
  have : T.neighborSet u = ↑(Finset.univ.filter (fun w => T.Adj u w)) := by
    ext w; simp
  rw [this, Set.ncard_coe_finset]

lemma D_apply (u v : Fin n) : degreeMatrix T u v =
    if u = v then ((Finset.univ.filter (fun w => T.Adj u w)).card : ℤ) else 0 := by
  by_cases huv : u = v
  · subst huv; simp [deg_eq]
  · simp only [huv, if_false]; unfold degreeMatrix; simp [Matrix.diagonal_apply, huv]

lemma ev_x (H K : Matrix (Fin n) (Fin n) ℤ) : ev H K x = H := by
  rw [← polyEval_eq_ev, polyEval_x]

lemma ev_y (H K : Matrix (Fin n) (Fin n) ℤ) : ev H K y = K := by
  rw [← polyEval_eq_ev, polyEval_y]

end tree

section part3
end part3

end UniformADProbes.Trace.Dev.Dist

namespace UniformADProbes.Trace

end UniformADProbes.Trace
end

section
/-! The probe vectors `cv k j = (polyEval H K (probes N k j)) v` and their recurrence. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningCv
open UniformADProbes.Trace UniformADProbes.Trace.Dev.Dist

noncomputable section
variable {n : ℕ}

lemma probes_out (N k : ℕ) (j : ℤ) (h : j < 0 ∨ (k : ℤ) < j) : probes N k j = 0 := by
  cases k with
  | zero =>
    have : j ≠ 0 := by omega
    simp [probes, this]
  | succ k =>
    have : j < 0 ∨ ((k + 1 : ℕ) : ℤ) < j := h
    simp only [probes]
    rw [if_pos (by push_cast at this ⊢; exact this)]

lemma probes_succ (N k : ℕ) (j : ℤ) (h : 0 ≤ j) (h2 : j ≤ (k : ℤ) + 1) :
    probes N (k + 1) j = (y + ((N : ℤ)^2 * (j - (k : ℤ))) • (1 : NCPoly)) * probes N k j +
        (N : ℤ)^2 • (x * probes N k (j - 1)) := by
  simp only [probes]
  rw [if_neg (by push_cast; omega)]

end
end UniformADProbes.Trace.Dev.SpanningCv
end

section
/-! The row emitter: one probe step as a pure code transformation. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningRows
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun
noncomputable section

def rowBody (N : ℕ) (a d zero : DualRef) (row : Array DualRef) (j : ℕ)
    (s : Array DualRef × Array DualRef) : Emit (ForInStep (Array DualRef × Array DualRef)) := do
  let u ← tableGet row j zero
  let v ← if j = 0 then pure zero else tableGet row (j - 1) zero
  let n2 := binaryMul N N
  let coeff : ℤ := (n2.value : ℤ) * ((j : ℤ) - ((row.size - 1 : ℕ) : ℤ))
  charge (n2.cost + (1 + refBits j + refBits (row.size - 1)) * (1 + refBits n2.value) +
    refBits j + refBits (row.size - 1) + 2)
  let du ← dualMul d u
  let cu ← dualScale coeff u
  let av ← dualMul a v
  let nv ← dualScale (n2.value : ℤ) av
  let q ← dualAdd (← dualAdd du cu) nv
  charge (1 + s.2.size * (1 + refBits q.1 + refBits q.2) +
    s.1.size * (1 + refBits q.1 + refBits q.2))
  pure (ForInStep.yield (s.1.push q, s.2.push q))

lemma emitProbeRows_succ (N : ℕ) (a d zero : DualRef) (k : ℕ) (row all : Array DualRef) :
    emitProbeRows N a d zero (k + 1) row all =
      (forIn (List.range (row.size - 1 + 2)) ((#[] : Array DualRef), all)
        (rowBody N a d zero row)) >>= fun p => emitProbeRows N a d zero k p.1 p.2 := by
  rfl

def vOf (zero : DualRef) (row : Array DualRef) (j : ℕ) : DualRef :=
  if j = 0 then zero else row[j - 1]?.getD zero

def bodyRes (N : ℕ) (a d zero : DualRef) (row : Array DualRef) (j : ℕ) (c : Array Instruction) :
    Array Instruction × DualRef :=
  let u := row[j]?.getD zero
  let v := vOf zero row j
  let κ := N * N
  let coeff : ℤ := (κ : ℤ) * ((j : ℤ) - ((row.size - 1 : ℕ) : ℤ))
  let r1 := pMul c d u
  let r2 := pScale r1.1 coeff u
  let r3 := pMul r2.1 a v
  let r4 := pScale r3.1 (κ : ℤ) r3.2
  let r5 := pAdd r4.1 r1.2 r2.2
  pAdd r5.1 r5.2 r4.2

lemma trip_rowBody (N : ℕ) (a d zero : DualRef) (row : Array DualRef) (j : ℕ)
    (s : Array DualRef × Array DualRef) (c : Array Instruction) :
    Trip (rowBody N a d zero row j s) c
      (ForInStep.yield (s.1.push (bodyRes N a d zero row j c).2, s.2.push (bodyRes N a d zero row j c).2))
      (bodyRes N a d zero row j c).1 := by
  unfold rowBody
  refine Trip.bind (trip_tableGet c row j zero) ?_
  by_cases hj : j = 0
  · simp only [hj, if_true]
    refine Trip.bind (Trip.pure' _ _) ?_
    refine Trip.bind (trip_charge c _) ?_
    refine Trip.bind (trip_dualMul c d _) ?_
    refine Trip.bind (trip_dualScale _ _ _) ?_
    refine Trip.bind (trip_dualMul _ a _) ?_
    refine Trip.bind (trip_dualScale _ _ _) ?_
    refine Trip.bind (trip_dualAdd _ _ _) ?_
    refine Trip.bind (trip_dualAdd _ _ _) ?_
    refine Trip.bind (trip_charge _ _) ?_
    simp only [bodyRes, vOf, hj, if_true]
    exact Trip.pure' _ _
  · simp only [hj, if_false]
    refine Trip.bind (trip_tableGet _ _ _ _) ?_
    refine Trip.bind (trip_charge c _) ?_
    refine Trip.bind (trip_dualMul c d _) ?_
    refine Trip.bind (trip_dualScale _ _ _) ?_
    refine Trip.bind (trip_dualMul _ a _) ?_
    refine Trip.bind (trip_dualScale _ _ _) ?_
    refine Trip.bind (trip_dualAdd _ _ _) ?_
    refine Trip.bind (trip_dualAdd _ _ _) ?_
    refine Trip.bind (trip_charge _ _) ?_
    simp only [bodyRes, vOf, hj, if_false]
    exact Trip.pure' _ _

lemma bodyRes_spec (N : ℕ) (a d zero : DualRef) (row : Array DualRef) (j i B L : ℕ)
    (c : Array Instruction) (hi : i = row.size - 1)
    (hbw : BW c) (hl : Lit L c) (hd : DGB B c)
    (ha : Sem c a x 1) (hdd : Sem c d y 1)
    (hu : Sem c (row[j]?.getD zero) (probes N i j) i)
    (hv : Sem c (vOf zero row j) (probes N i ((j : ℤ) - 1)) i)
    (hj : j ≤ i + 1) (hB : i + 1 ≤ B)
    (hκ : signedBits ((N * N : ℕ) : ℤ) ≤ L)
    (hco : signedBits (((N * N : ℕ) : ℤ) * ((j : ℤ) - (i : ℤ))) ≤ L) :
    Sem (bodyRes N a d zero row j c).1 (bodyRes N a d zero row j c).2 (probes N (i + 1) j) (i + 1) ∧
    Ext c (bodyRes N a d zero row j c).1 ∧ BW (bodyRes N a d zero row j c).1 ∧
    Lit L (bodyRes N a d zero row j c).1 ∧ DGB B (bodyRes N a d zero row j c).1 := by
  subst hi
  generalize hu' : row[j]?.getD zero = u at hu
  generalize hv' : vOf zero row j = v at hv
  unfold bodyRes
  simp only [hu', hv']
  set i := row.size - 1 with hi
  set κ := N * N with hκdef
  set coeff : ℤ := (κ : ℤ) * ((j : ℤ) - ((i : ℕ) : ℤ)) with hcoeff
  set P1 := pMul c d u with hP1
  set P2 := pScale P1.1 coeff u with hP2
  set P3 := pMul P2.1 a v with hP3
  set P4 := pScale P3.1 (κ : ℤ) P3.2 with hP4
  set P5 := pAdd P4.1 P1.2 P2.2 with hP5
  set P6 := pAdd P5.1 P5.2 P4.2 with hP6
  have s1 : Sem P1.1 P1.2 (y * probes N i j) (1 + i) := pMul_sem hdd hu
  have g1 := pMul_good (B := B) (L := L) hbw hl hd hdd hu (by omega)
  have e1 : Ext c P1.1 := pMul_ext c d u
  have hu2 := hu.mono e1
  have s2 : Sem P2.1 P2.2 (coeff • probes N i j) i := pScale_sem coeff hu2
  have g2 := pScale_good (B := B) (L := L) coeff g1.1 g1.2.1 g1.2.2 hu2 (by omega) hco
  have e2 : Ext P1.1 P2.1 := pScale_ext P1.1 coeff u
  have ha3 := (ha.mono e1).mono e2
  have hv3 := (hv.mono e1).mono e2
  have s3 : Sem P3.1 P3.2 (x * probes N i ((j : ℤ) - 1)) (1 + i) := pMul_sem ha3 hv3
  have g3 := pMul_good (B := B) (L := L) g2.1 g2.2.1 g2.2.2 ha3 hv3 (by omega)
  have e3 : Ext P2.1 P3.1 := pMul_ext P2.1 a v
  have s4 : Sem P4.1 P4.2 ((κ : ℤ) • (x * probes N i ((j : ℤ) - 1))) (1 + i) :=
    pScale_sem (κ : ℤ) s3
  have g4 := pScale_good (B := B) (L := L) (κ : ℤ) g3.1 g3.2.1 g3.2.2 s3 (by omega) hκ
  have e4 : Ext P3.1 P4.1 := pScale_ext P3.1 (κ : ℤ) P3.2
  have h5a : Sem P4.1 P1.2 (y * probes N i j) (1 + i) := (s1.mono e2 |>.mono e3).mono e4
  have h5b : Sem P4.1 P2.2 (coeff • probes N i j) i := (s2.mono e3).mono e4
  have s5 : Sem P5.1 P5.2 (y * probes N i j + coeff • probes N i j) (max (1 + i) i) :=
    pAdd_sem h5a h5b
  have g5 := pAdd_good (B := B) (L := L) g4.1 g4.2.1 g4.2.2 h5a h5b (by omega)
  have e5 : Ext P4.1 P5.1 := pAdd_ext P4.1 P1.2 P2.2
  have h6b : Sem P5.1 P4.2 ((κ : ℤ) • (x * probes N i ((j : ℤ) - 1))) (1 + i) := s4.mono e5
  have s6 : Sem P6.1 P6.2 ((y * probes N i j + coeff • probes N i j) +
      (κ : ℤ) • (x * probes N i ((j : ℤ) - 1))) (max (max (1 + i) i) (1 + i)) :=
    pAdd_sem s5 h6b
  have g6 := pAdd_good (B := B) (L := L) g5.1 g5.2.1 g5.2.2 s5 h6b (by omega)
  have e6 : Ext P5.1 P6.1 := pAdd_ext P5.1 P5.2 P4.2
  refine ⟨?_, ((((e1.trans e2).trans e3).trans e4).trans e5).trans e6, g6.1, g6.2.1, g6.2.2⟩
  have hP : probes N (i + 1) j = (y * probes N i j + coeff • probes N i j) +
      (κ : ℤ) • (x * probes N i ((j : ℤ) - 1)) := by
    rw [UniformADProbes.Trace.Dev.SpanningCv.probes_succ N i j (by positivity) (by omega)]
    rw [hcoeff, hκdef]
    push_cast
    rw [add_mul, smul_mul_assoc, one_mul, pow_two]
  rw [hP]
  exact s6.le (by omega)

end
end UniformADProbes.Trace.Dev.SpanningRows
end

section
/-! The row loops of `emitProbeRows`. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningLoop
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun UniformADProbes.Trace.Dev.SpanningRows
  UniformADProbes.Trace.Dev.SpanningCv
noncomputable section

def rowList (N i : ℕ) : List NCPoly := (List.range (i + 1)).map fun (j : ℕ) => probes N i (j : ℤ)

def upto (N m : ℕ) : List NCPoly := (List.range m).flatMap fun i => rowList N i

lemma upto_succ (N m : ℕ) : upto N (m + 1) = upto N m ++ rowList N m := by
  simp [upto, List.range_succ]

lemma probeList_eq (N : ℕ) : probeList N = upto N N := by
  unfold probeList probeIndices upto rowList
  rw [List.map_flatMap]
  simp only [List.map_map]
  rfl

lemma bodyRes_size (N : ℕ) (a d zero : DualRef) (row : Array DualRef) (j : ℕ) (c : Array Instruction) :
    (bodyRes N a d zero row j c).1.size = c.size + 12 := by
  simp [bodyRes, pMul_size, pAdd_size, pScale_size]

/-- The literal bound `8 * clog 2 (N+1)`. -/
lemma signedBits_le (N : ℕ) (hN : 1 ≤ N) (m : ℤ) (hm : m.natAbs ≤ N ^ 3) :
    signedBits m ≤ 8 * Nat.clog 2 (N + 1) := by
  have hc : 1 ≤ Nat.clog 2 (N + 1) := Nat.clog_pos (by norm_num) (by omega)
  have h1 : N + 1 ≤ 2 ^ Nat.clog 2 (N + 1) := Nat.le_pow_clog (by norm_num) _
  have h2 : m.natAbs < 2 ^ (3 * Nat.clog 2 (N + 1)) := by
    calc m.natAbs ≤ N ^ 3 := hm
      _ < (N + 1) ^ 3 := by gcongr; omega
      _ ≤ (2 ^ Nat.clog 2 (N + 1)) ^ 3 := by gcongr
      _ = 2 ^ (3 * Nat.clog 2 (N + 1)) := by rw [← pow_mul]; ring_nf
  have h3 : m.natAbs.size ≤ 3 * Nat.clog 2 (N + 1) := Nat.size_le.mpr h2
  unfold signedBits
  omega

lemma rowSem_get (N i : ℕ) (row : Array DualRef) (c : Array Instruction)
    (hrow : row.size = i + 1)
    (h : List.Forall₂ (fun r P => Sem c r P i) row.toList (rowList N i)) (t : ℕ) (ht : t < row.size) :
    Sem c row[t] (probes N i (t : ℤ)) i := by
  have hl : row.toList.length = (rowList N i).length := h.length_eq
  have hlen : (rowList N i).length = i + 1 := by simp [rowList]
  have := (List.forall₂_iff_get.mp h).2 t (by simp; omega) (by omega)
  simpa [rowList] using this

lemma probes_zero_row (N i : ℕ) (j : ℤ) (h : j < 0 ∨ (i : ℤ) < j) : probes N i j = 0 :=
  probes_out N i j h

lemma inner_trip (N : ℕ) (hN : 2 ≤ N) (a d zr : DualRef) (i : ℕ) (row all : Array DualRef)
    (c : Array Instruction) (hi : i + 2 ≤ N) (hrow : row.size = i + 1)
    (hbw : BW c) (hl : Lit (8 * Nat.clog 2 (N + 1)) c) (hd : DGB (N - 1) c)
    (hsz : c.size + 8 = 12 * all.size)
    (ha : Sem c a x 1) (hdd : Sem c d y 1) (hz : Sem c zr 0 0)
    (hrowS : List.Forall₂ (fun r P => Sem c r P i) row.toList (rowList N i)) :
    ∃ (next total : Array DualRef) (c' : Array Instruction),
      Trip (forIn (List.range (row.size - 1 + 2)) ((#[] : Array DualRef), all)
        (rowBody N a d zr row)) c (next, total) c' ∧
      Ext c c' ∧ BW c' ∧ Lit (8 * Nat.clog 2 (N + 1)) c' ∧ DGB (N - 1) c' ∧
      c'.size + 8 = 12 * total.size ∧
      List.Forall₂ (fun r P => Sem c' r P (i + 1)) next.toList (rowList N (i + 1)) ∧
      total.toList = all.toList ++ next.toList := by
  set L := 8 * Nat.clog 2 (N + 1) with hL
  have hrs : row.size - 1 + 2 = i + 2 := by omega
  rw [hrs, List.range_eq_range']
  let P : ℕ → (Array DualRef × Array DualRef) → Array Instruction → Prop :=
    fun j b c' => Ext c c' ∧ c'.size + 8 = 12 * (all.size + j) ∧ BW c' ∧ Lit L c' ∧
      DGB (N - 1) c' ∧
      List.Forall₂ (fun r P => Sem c' r P (i + 1)) b.1.toList
        ((List.range j).map fun (t : ℕ) => probes N (i + 1) (t : ℤ)) ∧
      b.2.toList = all.toList ++ b.1.toList
  have hP0 : P 0 ((#[] : Array DualRef), all) c :=
    ⟨Ext.refl c, by simpa using hsz, hbw, hl, hd, by simp, by simp⟩
  obtain ⟨b', c', hT, hPfin⟩ := forIn_range'_trip (rowBody N a d zr row) P (i + 2) 0 _ c hP0 (by
    intro j _ hj b cc hPj
    obtain ⟨hExt, hsz', hbw', hl', hd', hnext, htot⟩ := hPj
    have hj' : j ≤ i + 1 := by omega
    refine ⟨_, _, trip_rowBody N a d zr row j b cc, ?_⟩
    have ha' := ha.mono hExt
    have hdd' := hdd.mono hExt
    have hz' := hz.mono hExt
    have hu : Sem cc (row[j]?.getD zr) (probes N i (j : ℤ)) i := by
      by_cases hjr : j < row.size
      · rw [Array.getElem?_eq_getElem hjr, Option.getD_some]
        exact (rowSem_get N i row c hrow hrowS j hjr).mono hExt
      · have hjj : j = i + 1 := by omega
        rw [Array.getElem?_eq_none (by omega), Option.getD_none]
        have := probes_zero_row N i (j : ℤ) (Or.inr (by omega))
        rw [this]
        exact (hz'.le (Nat.zero_le _))
    have hv : Sem cc (vOf zr row j) (probes N i ((j : ℤ) - 1)) i := by
      unfold vOf
      by_cases hj0 : j = 0
      · rw [if_pos hj0]
        have := probes_zero_row N i ((j : ℤ) - 1) (Or.inl (by omega))
        rw [this]
        exact (hz'.le (Nat.zero_le _))
      · rw [if_neg hj0]
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        have hjr : j' < row.size := by omega
        rw [Nat.succ_sub_one, Array.getElem?_eq_getElem hjr, Option.getD_some]
        have := (rowSem_get N i row c hrow hrowS j' hjr).mono hExt
        have e : ((j' + 1 : ℕ) : ℤ) - 1 = (j' : ℤ) := by push_cast; ring
        rw [e]; exact this
    have hκ : signedBits ((N * N : ℕ) : ℤ) ≤ L :=
      signedBits_le N (by omega) _ (by
        simp only [Int.natAbs_natCast]
        calc N * N ≤ N * N * N := Nat.le_mul_of_pos_right _ (by omega)
          _ = N ^ 3 := by ring)
    have hco : signedBits (((N * N : ℕ) : ℤ) * ((j : ℤ) - (i : ℤ))) ≤ L :=
      signedBits_le N (by omega) _ (by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
        have : ((j : ℤ) - (i : ℤ)).natAbs ≤ N := by omega
        calc N * N * ((j : ℤ) - (i : ℤ)).natAbs ≤ N * N * N := Nat.mul_le_mul_left _ this
          _ = N ^ 3 := by ring)
    obtain ⟨hS, hE, hB2, hL2, hD2⟩ := bodyRes_spec N a d zr row j i (N - 1) L cc
      (by omega) hbw' hl' hd' ha' hdd' hu hv hj' (by omega) hκ hco
    refine ⟨hExt.trans hE, ?_, hB2, hL2, hD2, ?_, ?_⟩
    · rw [bodyRes_size]; omega
    · simp only [Array.toList_push]
      rw [List.range_succ, List.map_append]
      refine List.rel_append ?_ ?_
      · exact hnext.imp (fun r P h => h.mono hE)
      · exact List.Forall₂.cons hS List.Forall₂.nil
    · simp only [Array.toList_push, htot]
      simp)
  obtain ⟨hExt, hsz', hbw', hl', hd', hnext, htot⟩ := hPfin
  have hlen : b'.1.toList.length = i + 2 := by
    have := hnext.length_eq
    simpa using this
  refine ⟨b'.1, b'.2, c', hT, hExt, hbw', hl', hd', ?_, ?_, htot⟩
  · have : b'.2.size = all.size + (i + 2) := by
      have := congrArg List.length htot
      simp at this
      simp at hlen
      omega
    rw [this]; rw [hsz']; ring
  · have : rowList N (i + 1) = (List.range (0 + (i + 2))).map fun (t : ℕ) => probes N (i + 1) (t : ℤ) := by
      simp [rowList]
    rw [this]; exact hnext

end
end UniformADProbes.Trace.Dev.SpanningLoop
end

section
/-! The whole row emitter and the initial segment. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningProg
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun UniformADProbes.Trace.Dev.SpanningRows
  UniformADProbes.Trace.Dev.SpanningCv UniformADProbes.Trace.Dev.SpanningLoop
noncomputable section

lemma rows_trip (N : ℕ) (hN : 2 ≤ N) (a d zr : DualRef) :
    ∀ (k i : ℕ) (row all : Array DualRef) (c : Array Instruction),
      i + k + 1 = N → row.size = i + 1 → BW c → Lit (8 * Nat.clog 2 (N + 1)) c →
      DGB (N - 1) c → c.size + 8 = 12 * all.size →
      Sem c a x 1 → Sem c d y 1 → Sem c zr 0 0 →
      List.Forall₂ (fun r P => Sem c r P i) row.toList (rowList N i) →
      List.Forall₂ (fun r P => Sem c r P (N - 1)) all.toList (upto N (i + 1)) →
      ∃ (R : Array DualRef) (c' : Array Instruction),
        Trip (emitProbeRows N a d zr k row all) c R c' ∧ BW c' ∧
        Lit (8 * Nat.clog 2 (N + 1)) c' ∧ DGB (N - 1) c' ∧ c'.size + 8 = 12 * R.size ∧
        List.Forall₂ (fun r P => Sem c' r P (N - 1)) R.toList (upto N N) := by
  intro k
  induction k with
  | zero =>
    intro i row all c hk hrow hbw hl hd hsz ha hdd hz hrowS hallS
    have hN' : i + 1 = N := by omega
    refine ⟨all, c, ?_, hbw, hl, hd, hsz, by rw [hN'] at hallS; exact hallS⟩
    unfold emitProbeRows
    exact Trip.pure' _ _
  | succ k ih =>
    intro i row all c hk hrow hbw hl hd hsz ha hdd hz hrowS hallS
    obtain ⟨next, total, c', hT, hExt, hbw', hl', hd', hsz', hnextS, htot⟩ :=
      inner_trip N hN a d zr i row all c (by omega) hrow hbw hl hd hsz ha hdd hz hrowS
    have hnl : next.toList.length = i + 2 := by
      have := hnextS.length_eq
      simpa [rowList] using this
    have hnsize : next.size = (i + 1) + 1 := by simpa using hnl
    have hall' : List.Forall₂ (fun r P => Sem c' r P (N - 1)) total.toList (upto N (i + 1 + 1)) := by
      rw [htot, upto_succ]
      refine List.rel_append ?_ ?_
      · exact hallS.imp (fun r P h => h.mono hExt)
      · exact hnextS.imp (fun r P h => h.le (by omega))
    obtain ⟨R, c'', hT2, h1, h2, h3, h4, h5⟩ := ih (i + 1) next total c' (by omega) hnsize hbw' hl' hd'
      hsz' (ha.mono hExt) (hdd.mono hExt) (hz.mono hExt) hnextS hall'
    refine ⟨R, c'', ?_, h1, h2, h3, h4, h5⟩
    rw [emitProbeRows_succ]
    have hrs : row.size - 1 + 2 = i + 2 := by omega
    exact Trip.bind hT hT2

def code0 : Array Instruction :=
  (((#[].push .identity).push .first).push .second).push (.scale 0 0)

lemma trip_initial : Trip initial #[] ((0, 0), (1, 1), (2, 2), (3, 3)) code0 := by
  unfold initial
  refine Trip.bind (trip_emit #[] _) ?_
  refine Trip.bind (trip_emit _ _) ?_
  refine Trip.bind (trip_emit _ _) ?_
  refine Trip.bind (trip_emit _ _) ?_
  have := Trip.pure' (((0, 0), (1, 1), (2, 2), (3, 3)) : DualRef × DualRef × DualRef × DualRef) code0
  simpa [code0, Array.size_push] using this

lemma code0_size : code0.size = 4 := by simp [code0]

lemma sem_identity (c : Array Instruction) : Sem (c.push .identity) (c.size, c.size) 1 0 := by
  have h := rv_push_new c .identity
  have h' := dg_push_new c .identity
  refine ⟨by simp, by simp, h, ?_, h'.le, h'.le⟩
  show rv (c.push .identity) c.size = adjoint 1
  rw [SpanningAdj.adjoint_one]; exact h

lemma sem_first (c : Array Instruction) : Sem (c.push .first) (c.size, c.size) x 1 := by
  have h := rv_push_new c .first
  have h' := dg_push_new c .first
  refine ⟨by simp, by simp, h, ?_, h'.le, h'.le⟩
  show rv (c.push .first) c.size = adjoint x
  rw [SpanningAdj.adjoint_x]; exact h

lemma sem_second (c : Array Instruction) : Sem (c.push .second) (c.size, c.size) y 1 := by
  have h := rv_push_new c .second
  have h' := dg_push_new c .second
  refine ⟨by simp, by simp, h, ?_, h'.le, h'.le⟩
  show rv (c.push .second) c.size = adjoint y
  rw [SpanningAdj.adjoint_y]; exact h

lemma sem_zero (c : Array Instruction) (r : ℕ) (hr : r < c.size) (h0 : dg c r = 0) :
    Sem (c.push (.scale 0 r)) (c.size, c.size) 0 0 := by
  have h := rv_push_new c (.scale 0 r)
  have h' := dg_push_new c (.scale 0 r)
  have hv : rv (c.push (.scale 0 r)) c.size = 0 := by
    rw [h]
    show (0 : ℤ) • rv c r = 0
    rw [zero_smul]
  refine ⟨by simp, by simp, hv, ?_, ?_, ?_⟩
  · show rv (c.push (.scale 0 r)) c.size = adjoint 0
    rw [SpanningAdj.adjoint_zero]; exact hv
  · rw [h']; show dg c r ≤ 0; omega
  · rw [h']; show dg c r ≤ 0; omega

lemma init_facts (N : ℕ) (hN : 2 ≤ N) :
    Sem code0 (0, 0) 1 0 ∧ Sem code0 (1, 1) x 1 ∧ Sem code0 (2, 2) y 1 ∧ Sem code0 (3, 3) 0 0 ∧
    BW code0 ∧ Lit (8 * Nat.clog 2 (N + 1)) code0 ∧ DGB (N - 1) code0 := by
  have hc : 1 ≤ Nat.clog 2 (N + 1) := Nat.clog_pos (by norm_num) (by omega)
  have hE1 : (#[] : Array Instruction) = #[] := rfl
  set c1 : Array Instruction := (#[] : Array Instruction).push .identity with hc1
  set c2 := c1.push .first with hc2
  set c3 := c2.push .second with hc3
  have hs1 : c1.size = 1 := by simp [hc1]
  have hs2 : c2.size = 2 := by simp [hc2, hs1]
  have hs3 : c3.size = 3 := by simp [hc3, hs2]
  have hcode : code0 = c3.push (.scale 0 0) := rfl
  have S0 : Sem c1 (0, 0) 1 0 := sem_identity #[]
  have S1 : Sem c2 (1, 1) x 1 := by
    have := sem_first c1; rw [hs1] at this; exact this
  have S2 : Sem c3 (2, 2) y 1 := by
    have := sem_second c2; rw [hs2] at this; exact this
  have x1 : Ext c1 c2 := ext_push c1 .first
  have x2 : Ext c2 c3 := ext_push c2 .second
  have x3 : Ext c3 code0 := ext_push c3 (.scale 0 0)
  have S0' : Sem c3 (0, 0) 1 0 := (S0.mono x1).mono x2
  have d0 : dg c3 0 = 0 := Nat.le_zero.mp S0'.2.2.2.2.1
  have S3 : Sem code0 (3, 3) 0 0 := by
    have := sem_zero c3 0 (by omega) d0
    rw [hs3] at this
    exact this
  have hB : BW code0 := by
    have B1 : BW c1 := BW.empty.push .identity trivial
    have B2 : BW c2 := B1.push .first trivial
    have B3 : BW c3 := B2.push .second trivial
    exact B3.push (.scale 0 0) (by show 0 < c3.size; omega)
  have hL : Lit (8 * Nat.clog 2 (N + 1)) code0 := by
    have e : Lit (8 * Nat.clog 2 (N + 1)) (#[] : Array Instruction) := fun I hI => by simp at hI
    have L1 : Lit (8 * Nat.clog 2 (N + 1)) c1 := e.push .identity (by intro k a h; cases h)
    have L2 : Lit (8 * Nat.clog 2 (N + 1)) c2 := L1.push .first (by intro k a h; cases h)
    have L3 : Lit (8 * Nat.clog 2 (N + 1)) c3 := L2.push .second (by intro k a h; cases h)
    refine L3.push (.scale 0 0) ?_
    intro k a h
    cases h
    unfold signedBits
    simp
    omega
  have hD : DGB (N - 1) code0 := by
    have e : DGB 1 (#[] : Array Instruction) := fun r => by simp [dg, degs_empty]
    have D1 : DGB 1 c1 := e.push .identity (by simp [degreeInstruction])
    have D2 : DGB 1 c2 := D1.push .first (by simp [degreeInstruction])
    have D3 : DGB 1 c3 := D2.push .second (by simp [degreeInstruction])
    have D4 : DGB 1 code0 := D3.push (.scale 0 0) (by
      simp only [degreeInstruction]
      show dg c3 0 ≤ 1
      omega)
    intro r
    have := D4 r
    omega
  exact ⟨(S0.mono (x1.trans x2 |>.trans x3)), (S1.mono x2 |>.mono x3), S2.mono x3, S3, hB, hL, hD⟩

lemma probe_trip (N : ℕ) (hN : 2 ≤ N) :
    ∃ (R : Array DualRef) (c' : Array Instruction),
      (probeProgram N).1 = R ∧ (probeProgram N).2.code = c' ∧ BW c' ∧
      Lit (8 * Nat.clog 2 (N + 1)) c' ∧ DGB (N - 1) c' ∧ c'.size + 8 = 12 * R.size ∧
      List.Forall₂ (fun r P => Sem c' r P (N - 1)) R.toList (probeList N) := by
  obtain ⟨s0, s1, s2, s3, hB, hL, hD⟩ := init_facts N hN
  have e : rowList N 0 = [1] := by simp [rowList, probes]
  have hrow : List.Forall₂ (fun r P => Sem code0 r P 0) (#[((0 : ℕ), (0 : ℕ))] : Array DualRef).toList
      (rowList N 0) := by
    rw [e]
    exact List.Forall₂.cons s0 List.Forall₂.nil
  have hall : List.Forall₂ (fun r P => Sem code0 r P (N - 1))
      (#[((0 : ℕ), (0 : ℕ))] : Array DualRef).toList (upto N (0 + 1)) := by
    have : upto N (0 + 1) = rowList N 0 := by simp [upto]
    rw [this]
    exact hrow.imp (fun r P h => h.le (by omega))
  obtain ⟨R, c', hT, h1, h2, h3, h4, h5⟩ := rows_trip N hN (1, 1) (2, 2) (3, 3) (N - 1) 0
    #[((0 : ℕ), (0 : ℕ))] #[((0 : ℕ), (0 : ℕ))] code0 (by omega) (by simp) hB hL hD
    (by rw [code0_size]; simp) s1 s2 s3 hrow hall
  have hT' : Trip (emitProbes N (0, 0) (1, 1) (2, 2) (3, 3)) code0 R c' := by
    unfold emitProbes
    rw [if_neg (by omega)]
    exact hT
  have hpp : probeProgram N =
      (initial >>= fun t => emitProbes N t.1 t.2.1 t.2.2.1 t.2.2.2).run {} := by
    unfold probeProgram
    rw [if_neg (by omega)]
  have hfull : Trip (initial >>= fun t => emitProbes N t.1 t.2.1 t.2.2.1 t.2.2.2) #[] R c' :=
    Trip.bind trip_initial hT'
  obtain ⟨e1, e2⟩ := hfull {} rfl
  refine ⟨R, c', ?_, ?_, h1, h2, h3, h4, by rw [probeList_eq]; exact h5⟩
  · rw [hpp]; exact e1
  · rw [hpp]; exact e2

end
end UniformADProbes.Trace.Dev.SpanningProg
end

section
/-! The probe phase: sizes of abstract norms, instruction bits and cost. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalProbe
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun UniformADProbes.Trace.Dev.SpanningRows
  UniformADProbes.Trace.Dev.SpanningLoop UniformADProbes.Trace.Dev.GoalNB
  UniformADProbes.Trace.Dev.GoalCT UniformADProbes.Trace.Dev.GoalOps
noncomputable section

/-- the global parameters -/
abbrev capN (N : ℕ) : ℕ := 100 * N ^ 2
abbrev LN (N : ℕ) : ℕ := 20 * N * Nat.clog 2 (N + 1)
abbrev clg (N : ℕ) : ℕ := Nat.clog 2 (N + 1)
/-- per-row growth of the bit size of the norms -/
abbrev delta (N : ℕ) : ℕ := 3 * clg N + 2
abbrev Qc (cap : ℕ) : ℕ := 8 * (cap + 1) ^ 2

lemma clg_pos (N : ℕ) (hN : 1 ≤ N) : 1 ≤ clg N := Nat.clog_pos (by norm_num) (by omega)

lemma size_le_pow (N m k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) (hm : m ≤ N ^ k) :
    m.size ≤ k * clg N := by
  have h1 : N + 1 ≤ 2 ^ clg N := Nat.le_pow_clog (by norm_num) _
  have h2 : m < 2 ^ (k * clg N) := by
    calc m ≤ N ^ k := hm
      _ < (N + 1) ^ k := Nat.pow_lt_pow_left (by omega) (by omega)
      _ ≤ (2 ^ clg N) ^ k := by gcongr
      _ = 2 ^ (k * clg N) := by rw [← pow_mul]; ring_nf
  exact Nat.size_le.mpr h2

lemma size_N1 (N : ℕ) (hN : 1 ≤ N) : (N - 1).size ≤ clg N := by
  have := size_le_pow N (N - 1) 1 hN le_rfl (by simp)
  simpa using this

lemma size_NN (N : ℕ) (hN : 1 ≤ N) : (N * N).size ≤ 2 * clg N :=
  size_le_pow N _ 2 hN (by norm_num) (by rw [pow_two])

lemma size_coeff (N : ℕ) (hN : 1 ≤ N) (m : ℤ) (hm : m.natAbs ≤ N ^ 3) :
    m.natAbs.size ≤ 3 * clg N := size_le_pow N _ 3 hN (by norm_num) hm

/-- instruction bits are fine for every literal that occurs -/
lemma lit_ok (N : ℕ) (hN : 1 ≤ N) (m : ℤ) (hm : m.natAbs ≤ N ^ 3) : signedBits m ≤ LN N := by
  have h0 := signedBits_le N hN m hm
  have h1 : 1 ≤ clg N := clg_pos N hN
  have h3 : 8 * clg N ≤ LN N := by show 8 * clg N ≤ 20 * N * clg N; nlinarith
  exact le_trans h0 h3

lemma foldl_refs_le (cap : ℕ) (a : Array DualRef) (k : ℕ) (hk : k ≤ cap)
    (h : ∀ r ∈ a.toList, Rl k r) :
    a.foldl (fun c r => c + refBits r.1 + refBits r.2) 0 ≤ a.size * (2 * (cap + 1)) := by
  rw [← Array.foldl_toList]
  have : ∀ (l : List DualRef), (∀ r ∈ l, Rl k r) → ∀ acc,
      l.foldl (fun c r => c + refBits r.1 + refBits r.2) acc ≤ acc + l.length * (2 * (cap + 1)) := by
    intro l
    induction l with
    | nil => intros; simp
    | cons r l ih =>
      intro hl acc
      simp only [List.foldl_cons, List.length_cons]
      have h1 := ih (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')) (acc + refBits r.1 + refBits r.2)
      have h2 := hl r (List.mem_cons_self ..)
      have := refBits_le r.1
      have := refBits_le r.2
      have := h2.1; have := h2.2
      nlinarith
  simpa using this a.toList h 0

lemma getD_prop (row : Array DualRef) (zero : DualRef) (j : ℕ) (P : DualRef → Prop) (hz : P zero)
    (hrow : ∀ r ∈ row.toList, P r) : P (row[j]?.getD zero) := by
  by_cases hj : j < row.size
  · rw [Array.getElem?_eq_getElem hj, Option.getD_some]
    exact hrow _ (by simp)
  · rw [Array.getElem?_eq_none (by omega), Option.getD_none]
    exact hz

/-- bound for one table read -/
lemma ct_tableGet_le (c : Array Instruction) (cap k : ℕ) (a : Array DualRef) (i : ℕ) (fb : DualRef)
    (hk : k ≤ cap) (ha : ∀ r ∈ a.toList, Rl k r) (hsz : a.size ≤ cap) (hi : i ≤ cap) :
    CT (tableGet a i fb) c (a[i]?.getD fb) c (Qc cap) := by
  refine (ct_tableGet c a i fb).mono ?_
  have h1 := foldl_refs_le cap a k hk ha
  have h2 := refBits_le i
  have h3 : a.size * (2 * (cap + 1)) ≤ cap * (2 * (cap + 1)) := Nat.mul_le_mul_right _ hsz
  unfold Qc
  nlinarith

lemma ct_charge_le (c : Array Instruction) (cap k : ℕ) (hk : k + 1 ≤ Qc cap) :
    CT (charge k) c () c (Qc cap) := (ct_charge c k).mono hk

lemma chg1_le (N j rs : ℕ) (hN : 1 ≤ N) (hj : j ≤ N) (hrs : rs ≤ N) :
    (binaryMul N N).cost + (1 + refBits j + refBits rs) * (1 + refBits (binaryMul N N).value) +
      refBits j + refBits rs + 2 + 1 ≤ Qc (capN N) := by
  have h1 := refBits_le j
  have h2 := refBits_le rs
  have h3 : refBits (N * N) ≤ N * N + 1 := refBits_le _
  have h4 : N.size ≤ N := Nat.size_le.mpr Nat.lt_two_pow_self
  have h5 : (1 + N.size) * (1 + N.size) ≤ (1 + N) * (1 + N) := Nat.mul_le_mul (by omega) (by omega)
  show (1 + N.size) * (1 + N.size) + (1 + refBits j + refBits rs) * (1 + refBits (N * N)) +
      refBits j + refBits rs + 2 + 1 ≤ 8 * (100 * N ^ 2 + 1) ^ 2
  have h6 : (1 + refBits j + refBits rs) * (1 + refBits (N * N)) ≤ (2 * N + 3) * (N * N + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have ht : 1 ≤ N * N := Nat.mul_le_mul hN hN
  have hNt : N ≤ N * N := Nat.le_mul_of_pos_left N (by omega)
  have e1 : (1 + N) * (1 + N) ≤ 4 * (N * N) := by nlinarith
  have e2 : (2 * N + 3) * (N * N + 2) ≤ 15 * ((N * N) * (N * N)) := by nlinarith
  have e3 : (N * N) ≤ (N * N) * (N * N) := Nat.le_mul_of_pos_left _ (by omega)
  have e4 : 8 * (100 * N ^ 2 + 1) ^ 2 ≥ 8 * (100 * (N * N)) ^ 2 := by
    have : (100 * N ^ 2) = 100 * (N * N) := by ring
    rw [this]; nlinarith
  have e5 : (100 * (N * N)) ^ 2 = 10000 * ((N * N) * (N * N)) := by ring
  nlinarith

lemma chg2_le (cap a b : ℕ) (q : DualRef) (hq : Rl cap q) (ha : a ≤ cap) (hb : b ≤ cap) :
    1 + a * (1 + refBits q.1 + refBits q.2) + b * (1 + refBits q.1 + refBits q.2) + 1 ≤ Qc cap := by
  have h1 := refBits_le q.1
  have h2 := refBits_le q.2
  have := hq.1; have := hq.2
  have h3 : 1 + refBits q.1 + refBits q.2 ≤ 2 * cap + 3 := by omega
  have h4 : a * (1 + refBits q.1 + refBits q.2) ≤ cap * (2 * cap + 3) := Nat.mul_le_mul ha h3
  have h5 : b * (1 + refBits q.1 + refBits q.2) ≤ cap * (2 * cap + 3) := Nat.mul_le_mul hb h3
  unfold Qc
  nlinarith

abbrev b1 (c : Array Instruction) (d u : DualRef) := pMul c d u
abbrev b2 (c : Array Instruction) (d u : DualRef) (co : ℤ) := pScale (b1 c d u).1 co u
abbrev b3 (c : Array Instruction) (d u a v : DualRef) (co : ℤ) := pMul (b2 c d u co).1 a v
abbrev b4 (c : Array Instruction) (d u a v : DualRef) (co κ : ℤ) :=
  pScale (b3 c d u a v co).1 κ (b3 c d u a v co).2
abbrev b5 (c : Array Instruction) (d u a v : DualRef) (co κ : ℤ) :=
  pAdd (b4 c d u a v co κ).1 (b1 c d u).2 (b2 c d u co).2
abbrev b6 (c : Array Instruction) (d u a v : DualRef) (co κ : ℤ) :=
  pAdd (b5 c d u a v co κ).1 (b5 c d u a v co κ).2 (b4 c d u a v co κ).2

lemma bodyRes_eq (N : ℕ) (a d zero : DualRef) (row : Array DualRef) (j : ℕ) (c : Array Instruction) :
    bodyRes N a d zero row j c = b6 c d (row[j]?.getD zero) a (vOf zero row j)
      (((N * N : ℕ) : ℤ) * ((j : ℤ) - ((row.size - 1 : ℕ) : ℤ))) ((N * N : ℕ) : ℤ) := rfl

lemma b6_facts (N : ℕ) (hN : 2 ≤ N) (c : Array Instruction) (d u a v : DualRef) (co κ : ℤ)
    (si T : ℕ) (hIB : IBd (beta (capN N) (LN N)) c) (hsz : c.size + 12 ≤ capN N)
    (hnbb : NBB (N - 1) T c)
    (hd : Rl c.size d) (ha : Rl c.size a) (hu1 : Rl c.size u) (hv1 : Rl c.size v)
    (hsa : NS (N - 1) c a (clg N)) (hsd : NS (N - 1) c d (clg N))
    (hu2 : NS (N - 1) c u si) (hv2 : NS (N - 1) c v si)
    (hco : signedBits co ≤ LN N) (hκ : signedBits κ ≤ LN N)
    (hcs : co.natAbs.size ≤ 3 * clg N) (hκs : κ.natAbs.size ≤ 2 * clg N) :
    (b6 c d u a v co κ).1.size = c.size + 12 ∧
    IBd (beta (capN N) (LN N)) (b6 c d u a v co κ).1 ∧
    NBB (N - 1) (max T (si + delta N)) (b6 c d u a v co κ).1 ∧
    Kept (N - 1) c (b6 c d u a v co κ).1 ∧
    Rl (b6 c d u a v co κ).1.size (b6 c d u a v co κ).2 ∧
    NS (N - 1) (b6 c d u a v co κ).1 (b6 c d u a v co κ).2 (si + delta N) ∧
    CT (dualMul d u) c (b1 c d u).2 (b1 c d u).1 (2 * Eb (capN N) (LN N)) ∧
    CT (dualScale co u) (b1 c d u).1 (b2 c d u co).2 (b2 c d u co).1 (2 * Eb (capN N) (LN N)) ∧
    CT (dualMul a v) (b2 c d u co).1 (b3 c d u a v co).2 (b3 c d u a v co).1
      (2 * Eb (capN N) (LN N)) ∧
    CT (dualScale κ (b3 c d u a v co).2) (b3 c d u a v co).1 (b4 c d u a v co κ).2
      (b4 c d u a v co κ).1 (2 * Eb (capN N) (LN N)) ∧
    CT (dualAdd (b1 c d u).2 (b2 c d u co).2) (b4 c d u a v co κ).1 (b5 c d u a v co κ).2
      (b5 c d u a v co κ).1 (2 * Eb (capN N) (LN N)) ∧
    CT (dualAdd (b5 c d u a v co κ).2 (b4 c d u a v co κ).2) (b5 c d u a v co κ).1
      (b6 c d u a v co κ).2 (b6 c d u a v co κ).1 (2 * Eb (capN N) (LN N)) := by
  obtain ⟨ib1, ns1, bb1, k1, sz1, rl1, ct1⟩ :=
    mul_step (L := LN N) hIB (by omega) hd hu1 hsd hu2 hnbb
  obtain ⟨ib2, ns2, bb2, k2, sz2, rl2, ct2⟩ :=
    scale_step (L := LN N) ib1 (by omega) co hco (hu1.mono (by omega)) (ns_kept hu2 hu1 k1) bb1
  obtain ⟨ib3, ns3, bb3, k3, sz3, rl3, ct3⟩ :=
    mul_step (L := LN N) ib2 (by omega) (ha.mono (by omega)) (hv1.mono (by omega))
      (ns_kept hsa ha (k1.trans k2)) (ns_kept hv2 hv1 (k1.trans k2)) bb2
  obtain ⟨ib4, ns4, bb4, k4, sz4, rl4, ct4⟩ :=
    scale_step (L := LN N) ib3 (by omega) κ hκ rl3 ns3 bb3
  obtain ⟨ib5, ns5, bb5, k5, sz5, rl5, ct5⟩ :=
    add_step (L := LN N) ib4 (by omega) (rl1.mono (by omega)) (rl2.mono (by omega))
      (ns_kept ns1 rl1 (k2.trans (k3.trans k4))) (ns_kept ns2 rl2 (k3.trans k4)) bb4
  obtain ⟨ib6, ns6, bb6, k6, sz6, rl6, ct6⟩ :=
    add_step (L := LN N) ib5 (by omega) rl5 (rl4.mono (by omega))
      ns5 (ns_kept ns4 rl4 k5) bb5
  have hδ : delta N = 3 * clg N + 2 := rfl
  have s1 : (b1 c d u).1.size = c.size + 2 := sz1
  have s2 : (b2 c d u co).1.size = (b1 c d u).1.size + 2 := sz2
  have s3 : (b3 c d u a v co).1.size = (b2 c d u co).1.size + 2 := sz3
  have s4 : (b4 c d u a v co κ).1.size = (b3 c d u a v co).1.size + 2 := sz4
  have s5 : (b5 c d u a v co κ).1.size = (b4 c d u a v co κ).1.size + 2 := sz5
  have s6 : (b6 c d u a v co κ).1.size = (b5 c d u a v co κ).1.size + 2 := sz6
  refine ⟨by omega, ib6, ?_, k1.trans (k2.trans (k3.trans (k4.trans (k5.trans k6)))), rl6, ?_,
    ct1, ct2, ct3, ct4, ct5, ct6⟩
  · refine bb6.le ?_
    simp only [hδ]
    omega
  · refine ns6.le ?_
    simp only [hδ]
    omega

lemma ct_rowBody (N : ℕ) (hN : 2 ≤ N) (a d zero : DualRef) (row : Array DualRef)
    (j si T : ℕ) (s : Array DualRef × Array DualRef) (c : Array Instruction)
    (hrs1 : 1 ≤ row.size) (hiN : row.size + 1 ≤ N) (hj : j ≤ row.size)
    (hIB : IBd (beta (capN N) (LN N)) c) (hsz : c.size + 12 ≤ capN N)
    (hnbb : NBB (N - 1) T c)
    (ha : Rl c.size a) (hd : Rl c.size d) (hz : Rl c.size zero)
    (hsa : NS (N - 1) c a (clg N)) (hsd : NS (N - 1) c d (clg N)) (hsz0 : NS (N - 1) c zero 0)
    (hrow : ∀ r ∈ row.toList, Rl c.size r ∧ NS (N - 1) c r si)
    (hs1 : s.1.size ≤ capN N) (hs2 : s.2.size ≤ capN N) :
    (∃ κ, CT (rowBody N a d zero row j s) c
      (ForInStep.yield (s.1.push (bodyRes N a d zero row j c).2,
        s.2.push (bodyRes N a d zero row j c).2)) (bodyRes N a d zero row j c).1 κ ∧
      κ ≤ 12 * Eb (capN N) (LN N) + 4 * Qc (capN N)) ∧
    (bodyRes N a d zero row j c).1.size = c.size + 12 ∧
    IBd (beta (capN N) (LN N)) (bodyRes N a d zero row j c).1 ∧
    NBB (N - 1) (max T (si + delta N)) (bodyRes N a d zero row j c).1 ∧
    Kept (N - 1) c (bodyRes N a d zero row j c).1 ∧
    Rl (bodyRes N a d zero row j c).1.size (bodyRes N a d zero row j c).2 ∧
    NS (N - 1) (bodyRes N a d zero row j c).1 (bodyRes N a d zero row j c).2 (si + delta N) := by
  have hN1 : 1 ≤ N := by omega
  have hNcap : N ≤ capN N := by show N ≤ 100 * N ^ 2; nlinarith
  have hrowR : ∀ r ∈ row.toList, Rl c.size r := fun r hr => (hrow r hr).1
  have hu : Rl c.size (row[j]?.getD zero) ∧ NS (N - 1) c (row[j]?.getD zero) si :=
    getD_prop row zero j (fun r => Rl c.size r ∧ NS (N - 1) c r si)
      ⟨hz, hsz0.le (Nat.zero_le _)⟩ hrow
  have hv : Rl c.size (vOf zero row j) ∧ NS (N - 1) c (vOf zero row j) si := by
    unfold vOf
    split_ifs
    · exact ⟨hz, hsz0.le (Nat.zero_le _)⟩
    · exact getD_prop row zero (j - 1) (fun r => Rl c.size r ∧ NS (N - 1) c r si)
        ⟨hz, hsz0.le (Nat.zero_le _)⟩ hrow
  have hκ : signedBits ((N * N : ℕ) : ℤ) ≤ LN N :=
    lit_ok N hN1 _ (by
      simp only [Int.natAbs_natCast]
      calc N * N ≤ N * N * N := Nat.le_mul_of_pos_right _ (by omega)
        _ = N ^ 3 := by ring)
  have hcn : (((N * N : ℕ) : ℤ) * ((j : ℤ) - ((row.size - 1 : ℕ) : ℤ))).natAbs ≤ N ^ 3 := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    have : ((j : ℤ) - ((row.size - 1 : ℕ) : ℤ)).natAbs ≤ N := by omega
    calc N * N * ((j : ℤ) - ((row.size - 1 : ℕ) : ℤ)).natAbs ≤ N * N * N :=
          Nat.mul_le_mul_left _ this
      _ = N ^ 3 := by ring
  have hco := lit_ok N hN1 _ hcn
  have hκs : (((N * N : ℕ) : ℤ)).natAbs.size ≤ 2 * clg N := by
    rw [Int.natAbs_natCast]; exact size_NN N hN1
  have hcs := size_coeff N hN1 _ hcn
  rw [bodyRes_eq]
  by_cases hj0 : j = 0
  · have hvj : vOf zero row j = zero := by simp [vOf, hj0]
    rw [hvj] at hv ⊢
    let V := zero
    obtain ⟨f1, f2, f3, f4, f5, f6, c1, c2, c3, c4, c5, c6⟩ :=
      b6_facts N hN c d (row[j]?.getD zero) a V
        (((N * N : ℕ) : ℤ) * ((j : ℤ) - ((row.size - 1 : ℕ) : ℤ))) ((N * N : ℕ) : ℤ) si T hIB hsz
        hnbb hd ha hu.1 hv.1 hsa hsd hu.2 hv.2 hco hκ hcs hκs
    refine ⟨?_, f1, f2, f3, f4, f5, f6⟩
    refine ⟨Qc (capN N) + (Qc (capN N) + (Qc (capN N) + (2 * Eb (capN N) (LN N) +
      (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) +
      (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (Qc (capN N) + 0))))))))), ?_, by omega⟩
    unfold rowBody
    refine CT.bind (ct_tableGet_le c (capN N) c.size row j zero (by omega) hrowR
      (by omega) (by omega)) ?_
    simp only [if_pos hj0]
    refine CT.bind ((CT.pure' zero c).mono (Nat.zero_le (Qc (capN N)))) ?_
    refine CT.bind (ct_charge_le c (capN N) _ ?_) ?_
    · exact chg1_le N j (row.size - 1) hN1 (by omega) (by omega)
    refine CT.bind c1 ?_
    refine CT.bind c2 ?_
    refine CT.bind c3 ?_
    refine CT.bind c4 ?_
    refine CT.bind c5 ?_
    refine CT.bind c6 ?_
    refine CT.bind (ct_charge_le _ (capN N) _ (chg2_le (capN N) s.2.size s.1.size _
      (f5.mono (by omega)) hs2 hs1)) ?_
    exact CT.pure' _ _
  · have hvj : vOf zero row j = row[j - 1]?.getD zero := by simp [vOf, hj0]
    rw [hvj] at hv ⊢
    let V := row[j - 1]?.getD zero
    obtain ⟨f1, f2, f3, f4, f5, f6, c1, c2, c3, c4, c5, c6⟩ :=
      b6_facts N hN c d (row[j]?.getD zero) a V
        (((N * N : ℕ) : ℤ) * ((j : ℤ) - ((row.size - 1 : ℕ) : ℤ))) ((N * N : ℕ) : ℤ) si T hIB hsz
        hnbb hd ha hu.1 hv.1 hsa hsd hu.2 hv.2 hco hκ hcs hκs
    refine ⟨?_, f1, f2, f3, f4, f5, f6⟩
    refine ⟨Qc (capN N) + (Qc (capN N) + (Qc (capN N) + (2 * Eb (capN N) (LN N) +
      (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) +
      (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (Qc (capN N) + 0))))))))), ?_, by omega⟩
    unfold rowBody
    refine CT.bind (ct_tableGet_le c (capN N) c.size row j zero (by omega) hrowR
      (by omega) (by omega)) ?_
    simp only [if_neg hj0]
    refine CT.bind (ct_tableGet_le c (capN N) c.size row (j - 1) zero (by omega) hrowR
      (by omega) (by omega)) ?_
    refine CT.bind (ct_charge_le c (capN N) _ ?_) ?_
    · exact chg1_le N j (row.size - 1) hN1 (by omega) (by omega)
    refine CT.bind c1 ?_
    refine CT.bind c2 ?_
    refine CT.bind c3 ?_
    refine CT.bind c4 ?_
    refine CT.bind c5 ?_
    refine CT.bind c6 ?_
    refine CT.bind (ct_charge_le _ (capN N) _ (chg2_le (capN N) s.2.size s.1.size _
      (f5.mono (by omega)) hs2 hs1)) ?_
    exact CT.pure' _ _

abbrev Krow (N : ℕ) : ℕ := 12 * Eb (capN N) (LN N) + 4 * Qc (capN N)

lemma ct_inner (N : ℕ) (hN : 2 ≤ N) (a d zr : DualRef) (i si T : ℕ) (row all : Array DualRef)
    (c : Array Instruction) (hi : i + 2 ≤ N) (hrow : row.size = i + 1)
    (hall : all.size + (i + 2) ≤ capN N)
    (hIB : IBd (beta (capN N) (LN N)) c) (hsz : c.size + 12 * (i + 2) ≤ capN N)
    (hnbb : NBB (N - 1) T c)
    (ha : Rl c.size a) (hd : Rl c.size d) (hz : Rl c.size zr)
    (hsa : NS (N - 1) c a (clg N)) (hsd : NS (N - 1) c d (clg N)) (hsz0 : NS (N - 1) c zr 0)
    (hrowS : ∀ r ∈ row.toList, Rl c.size r ∧ NS (N - 1) c r si) :
    ∃ (next total : Array DualRef) (c' : Array Instruction),
      CT (forIn (List.range (row.size - 1 + 2)) ((#[] : Array DualRef), all)
        (rowBody N a d zr row)) c (next, total) c' ((i + 2) * Krow N) ∧
      c'.size = c.size + 12 * (i + 2) ∧ IBd (beta (capN N) (LN N)) c' ∧
      NBB (N - 1) (max T (si + delta N)) c' ∧ Kept (N - 1) c c' ∧
      next.size = i + 2 ∧ total.size = all.size + (i + 2) ∧ total.toList = all.toList ++ next.toList ∧
      ∀ r ∈ next.toList, Rl c'.size r ∧ NS (N - 1) c' r (si + delta N) := by
  have hrs : row.size - 1 + 2 = i + 2 := by omega
  rw [hrs, List.range_eq_range']
  let P : ℕ → (Array DualRef × Array DualRef) → Array Instruction → Prop :=
    fun j b cc => cc.size = c.size + 12 * j ∧ IBd (beta (capN N) (LN N)) cc ∧
      NBB (N - 1) (max T (si + delta N)) cc ∧ Kept (N - 1) c cc ∧
      b.1.size = j ∧ b.2.size = all.size + j ∧ b.2.toList = all.toList ++ b.1.toList ∧
      ∀ r ∈ b.1.toList, Rl cc.size r ∧ NS (N - 1) cc r (si + delta N)
  have hP0 : P 0 ((#[] : Array DualRef), all) c :=
    ⟨by simp, hIB, hnbb.le (le_max_left _ _), Kept.refl _ _, by simp, by simp, by simp, by simp⟩
  obtain ⟨b', c', hT, hPfin⟩ := forIn_range'_ct (rowBody N a d zr row) P (Krow N) (i + 2) 0
    ((#[] : Array DualRef), all) c hP0 (by
      intro j _ hj b cc hPj
      obtain ⟨hsz1, hIB1, hnb1, hk1, hb1, hb2, hb3, hnext⟩ := hPj
      have hjr : j ≤ row.size := by omega
      obtain ⟨⟨κ, hCT, hκ⟩, f1, f2, f3, f4, f5, f6⟩ := ct_rowBody N hN a d zr row j (si) (max T (si + delta N)) b cc
        (by omega) (by omega) hjr hIB1 (by omega) hnb1
        (ha.mono (by omega)) (hd.mono (by omega)) (hz.mono (by omega))
        (ns_kept hsa ha hk1) (ns_kept hsd hd hk1) (ns_kept hsz0 hz hk1)
        (fun r hr => ⟨(hrowS r hr).1.mono (by omega), ns_kept (hrowS r hr).2 (hrowS r hr).1 hk1⟩)
        (by omega) (by omega)
      refine ⟨_, _, κ, hCT, hκ, ?_⟩
      refine ⟨by omega, f2, f3.le (by omega), hk1.trans f4, ?_, ?_, ?_, ?_⟩
      · simp only [Array.size_push]; omega
      · simp only [Array.size_push]; omega
      · simp only [Array.toList_push, hb3]; simp
      · intro r hr
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | hr
        · obtain ⟨h1, h2⟩ := hnext r hr
          exact ⟨h1.mono (by omega), ns_kept h2 h1 f4⟩
        · subst hr; exact ⟨f5, f6⟩)
  obtain ⟨hs1, hi1, hn1, hk1, hb1, hb2, hb3, hnext⟩ := hPfin
  refine ⟨b'.1, b'.2, c', ?_, by omega, hi1, hn1, hk1, by omega, by omega, hb3, hnext⟩
  exact hT

lemma ct_rows (N : ℕ) (hN : 2 ≤ N) (a d zr : DualRef) :
    ∀ (k i : ℕ) (row all : Array DualRef) (c : Array Instruction) (si T : ℕ),
      i + k + 1 = N → row.size = i + 1 → 2 * all.size = (i + 1) * (i + 2) →
      c.size + 8 = 12 * all.size →
      IBd (beta (capN N) (LN N)) c → NBB (N - 1) T c →
      Rl c.size a → Rl c.size d → Rl c.size zr →
      NS (N - 1) c a (clg N) → NS (N - 1) c d (clg N) → NS (N - 1) c zr 0 →
      (∀ r ∈ row.toList, Rl c.size r ∧ NS (N - 1) c r si) →
      (∀ r ∈ all.toList, Rl c.size r ∧ NS (N - 1) c r si) →
      ∃ (R : Array DualRef) (c' : Array Instruction),
        CT (emitProbeRows N a d zr k row all) c R c' (k * (N * Krow N)) ∧
        IBd (beta (capN N) (LN N)) c' ∧ NBB (N - 1) (max T (si + k * delta N)) c' ∧
        Kept (N - 1) c c' ∧ 2 * R.size = N * (N + 1) ∧ c'.size + 8 = 12 * R.size ∧
        ∀ r ∈ R.toList, Rl c'.size r ∧ NS (N - 1) c' r (si + k * delta N) := by
  intro k
  induction k with
  | zero =>
    intro i row all c si T hk hrow hall hsz hIB hnbb ha hd hz hsa hsd hsz0 hrowS hallS
    have hN' : i + 1 = N := by omega
    refine ⟨all, c, ?_, hIB, hnbb.le (by simp), Kept.refl _ _, ?_, hsz, ?_⟩
    · unfold emitProbeRows
      simpa using CT.pure' all c
    · rw [← hN'] at *; nlinarith
    · simpa using hallS
  | succ k ih =>
    intro i row all c si T hk hrow hall hsz hIB hnbb ha hd hz hsa hsd hsz0 hrowS hallS
    have hcap : c.size + 12 * (i + 2) ≤ capN N ∧ all.size + (i + 2) ≤ capN N := by
      have h1 : (i + 2) * (i + 3) ≤ N * (N + 1) := Nat.mul_le_mul (by omega) (by omega)
      constructor
      · show c.size + 12 * (i + 2) ≤ 100 * N ^ 2
        nlinarith
      · show all.size + (i + 2) ≤ 100 * N ^ 2
        nlinarith
    obtain ⟨next, total, c1, hCT, hs1, hI1, hn1, hk1, hnx, htt, htl, hnS⟩ :=
      ct_inner N hN a d zr i si T row all c (by omega) hrow hcap.2 hIB hcap.1 hnbb ha hd hz hsa hsd
        hsz0 hrowS
    have hall1 : 2 * total.size = (i + 1 + 1) * (i + 1 + 2) := by
      rw [htt]; nlinarith
    have hsz1 : c1.size + 8 = 12 * total.size := by rw [hs1, htt]; omega
    obtain ⟨R, c2, hCT2, hI2, hn2, hk2, hR1, hR2, hR3⟩ :=
      ih (i + 1) next total c1 (si + delta N) (max T (si + delta N)) (by omega) (by omega) hall1 hsz1
        hI1 hn1 (ha.mono hk1.1) (hd.mono hk1.1) (hz.mono hk1.1) (ns_kept hsa ha hk1)
        (ns_kept hsd hd hk1) (ns_kept hsz0 hz hk1) hnS (by
          intro r hr
          rw [htl, List.mem_append] at hr
          rcases hr with hr | hr
          · exact ⟨(hallS r hr).1.mono hk1.1, (ns_kept (hallS r hr).2 (hallS r hr).1 hk1).le (by omega)⟩
          · exact hnS r hr)
    refine ⟨R, c2, ?_, hI2, ?_, hk1.trans hk2, hR1, hR2, ?_⟩
    · rw [emitProbeRows_succ]
      refine (CT.bind (m := forIn (List.range (row.size - 1 + 2)) ((#[] : Array DualRef), all)
        (rowBody N a d zr row)) hCT hCT2).mono ?_
      rw [Nat.succ_mul]
      have : (i + 2) * Krow N ≤ N * Krow N := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    · refine hn2.le ?_
      have : (k + 1) * delta N = delta N + k * delta N := by ring
      omega
    · intro r hr
      refine ⟨(hR3 r hr).1, (hR3 r hr).2.le (by have : (k + 1) * delta N = delta N + k * delta N := by ring
                                                omega)⟩

open UniformADProbes.Trace.Dev.SpanningProg in
lemma nb_code0 (h : ℕ) : nb h code0 0 = 1 ∧ nb h code0 1 = h ∧ nb h code0 2 = h ∧
    nb h code0 3 = 0 ∧ ∀ r, 4 ≤ r → nb h code0 r = 0 := by
  have e : ∀ r, nb h code0 r = (nbs h code0)[r]?.getD 0 := fun r => rfl
  have hs : nbs h code0 = #[1, h, h, 0] := by
    simp [code0, nbs, nbI, Array.foldl_push]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e, hs]; rfl
  · rw [e, hs]; rfl
  · rw [e, hs]; rfl
  · rw [e, hs]; rfl
  · intro r hr
    rw [e, hs]
    rw [Array.getElem?_eq_none (by simp; omega)]
    rfl

open UniformADProbes.Trace.Dev.SpanningProg in
lemma ct_initial (N : ℕ) (hN : 2 ≤ N) :
    CT initial #[] ((0, 0), (1, 1), (2, 2), (3, 3)) code0 (4 * Eb (capN N) (LN N)) ∧
    IBd (beta (capN N) (LN N)) code0 ∧ NBB (N - 1) (clg N) code0 ∧
    NS (N - 1) code0 (0, 0) 1 ∧ NS (N - 1) code0 (1, 1) (clg N) ∧
    NS (N - 1) code0 (2, 2) (clg N) ∧ NS (N - 1) code0 (3, 3) 0 := by
  obtain ⟨n0, n1, n2, n3, n4⟩ := nb_code0 (N - 1)
  have hcl := clg_pos N (by omega)
  have hNcap : 4 ≤ capN N := by show 4 ≤ 100 * N ^ 2; nlinarith
  have hsN := size_N1 N (by omega)
  have hL : 2 ≤ LN N := by
    show 2 ≤ 20 * N * clg N; nlinarith
  have i1 : IBd (beta (capN N) (LN N)) (#[] : Array Instruction) := IBd.empty _
  have b1 : instructionBits Instruction.identity ≤ beta (capN N) (LN N) :=
    instructionBits_le (cap := capN N) (L := LN N) (I := Instruction.identity) trivial
  have b2 : instructionBits Instruction.first ≤ beta (capN N) (LN N) :=
    instructionBits_le (cap := capN N) (L := LN N) (I := Instruction.first) trivial
  have b3 : instructionBits Instruction.second ≤ beta (capN N) (LN N) :=
    instructionBits_le (cap := capN N) (L := LN N) (I := Instruction.second) trivial
  have b4 : instructionBits (Instruction.scale 0 0) ≤ beta (capN N) (LN N) :=
    instructionBits_le (cap := capN N) (L := LN N) (I := Instruction.scale 0 0)
      ⟨by omega, by show signedBits 0 ≤ LN N; simp [signedBits]; omega⟩
  have i2 := i1.push _ b1
  have i3 := i2.push _ b2
  have i4 := i3.push _ b3
  have i5 := i4.push _ b4
  refine ⟨?_, i5, ?_, ?_, ?_, ?_, ?_⟩
  · unfold initial
    refine CT.mono (κ := Eb (capN N) (LN N) + (Eb (capN N) (LN N) + (Eb (capN N) (LN N) +
      (Eb (capN N) (LN N) + 0)))) ?_ (by omega)
    refine CT.bind (ct_emit_le (IBd.empty _) (by simp) Instruction.identity trivial) ?_
    refine CT.bind (ct_emit_le i2 (by simp; omega) Instruction.first trivial) ?_
    refine CT.bind (ct_emit_le i3 (by simp; omega) Instruction.second trivial) ?_
    refine CT.bind (ct_emit_le i4 (by simp; omega) (Instruction.scale 0 0)
      ⟨by omega, by show signedBits 0 ≤ LN N; simp [signedBits]; omega⟩) ?_
    have := CT.pure' (((0, 0), (1, 1), (2, 2), (3, 3)) : DualRef × DualRef × DualRef × DualRef) code0
    simpa [code0, Array.size_push] using this
  · intro r
    by_cases hr : r < 4
    · interval_cases r <;> simp [n0, n1, n2, n3] <;> omega
    · rw [n4 r (by omega)]; simp
  · refine ⟨by rw [n0]; simp, by rw [n0]; simp⟩
  · refine ⟨by rw [n1]; exact hsN, by rw [n1]; exact hsN⟩
  · refine ⟨by rw [n2]; exact hsN, by rw [n2]; exact hsN⟩
  · refine ⟨by rw [n3]; simp, by rw [n3]; simp⟩

open UniformADProbes.Trace.Dev.SpanningProg in
/-- The row emission after the initial segment. -/
lemma ct_probe_core (N : ℕ) (hN : 2 ≤ N) :
    ∃ (R : Array DualRef) (c' : Array Instruction),
      CT (emitProbes N (0, 0) (1, 1) (2, 2) (3, 3)) code0 R c' ((N - 1) * (N * Krow N)) ∧
      IBd (beta (capN N) (LN N)) c' ∧
      NBB (N - 1) (max (clg N) (1 + (N - 1) * delta N)) c' ∧
      Kept (N - 1) code0 c' ∧ 2 * R.size = N * (N + 1) ∧ c'.size + 8 = 12 * R.size ∧
      (∀ r ∈ R.toList, Rl c'.size r ∧ NS (N - 1) c' r (1 + (N - 1) * delta N)) := by
  obtain ⟨ct0, ib0, nb0, s0, s1, s2, s3⟩ := ct_initial N hN
  have hR : Rl code0.size (0, 0) := by rw [code0_size]; exact ⟨by omega, by omega⟩
  have hR1 : Rl code0.size (1, 1) := by rw [code0_size]; exact ⟨by omega, by omega⟩
  have hR2 : Rl code0.size (2, 2) := by rw [code0_size]; exact ⟨by omega, by omega⟩
  have hR3 : Rl code0.size (3, 3) := by rw [code0_size]; exact ⟨by omega, by omega⟩
  obtain ⟨R, c', hCT, hI, hn, hk, hR1', hR2', hR3'⟩ :=
    ct_rows N hN (1, 1) (2, 2) (3, 3) (N - 1) 0 #[((0 : ℕ), (0 : ℕ))] #[((0 : ℕ), (0 : ℕ))] code0 1
      (clg N) (by omega) (by simp) (by simp) (by rw [code0_size]; simp) ib0 nb0 hR1 hR2 hR3 s1 s2 s3
      (by intro r hr; simp at hr; subst hr; exact ⟨hR, s0⟩)
      (by intro r hr; simp at hr; subst hr; exact ⟨hR, s0⟩)
  refine ⟨R, c', ?_, hI, hn, hk, hR1', hR2', ?_⟩
  · unfold emitProbes
    rw [if_neg (by omega)]
    exact hCT
  · simpa using hR3'

end
end UniformADProbes.Trace.Dev.GoalProbe
end

section
/-! The tail of the emitter: bundled step lemmas (semantics, degrees, literals, norms, cost). -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalTail1
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun UniformADProbes.Trace.Dev.GoalNB
  UniformADProbes.Trace.Dev.GoalCT UniformADProbes.Trace.Dev.GoalOps UniformADProbes.Trace.Dev.GoalProbe
noncomputable section

/-- the invariants of a code array in the tail -/
def TS (N T : ℕ) (c : Array Instruction) : Prop :=
  BW c ∧ Lit (LN N) c ∧ DGB (3 * N - 2) c ∧ IBd (beta (capN N) (LN N)) c ∧ c.size ≤ capN N ∧
    NBB (N - 1) T c

def RS (N : ℕ) (c : Array Instruction) (r : DualRef) (P : NCPoly) (e s : ℕ) : Prop :=
  Sem c r P e ∧ NS (N - 1) c r s

lemma RS.mono {N : ℕ} {c c' : Array Instruction} {r : DualRef} {P : NCPoly} {e s : ℕ}
    (h : RS N c r P e s) (hx : Ext c c') (hk : Kept (N - 1) c c') : RS N c' r P e s :=
  ⟨h.1.mono hx, ns_kept h.2 ⟨h.1.1, h.1.2.1⟩ hk⟩

lemma RS.le {N : ℕ} {c : Array Instruction} {r : DualRef} {P : NCPoly} {e e' s s' : ℕ}
    (h : RS N c r P e s) (he : e ≤ e') (hs : s ≤ s') : RS N c r P e' s' :=
  ⟨h.1.le he, h.2.le hs⟩

lemma TS.le {N T T' : ℕ} {c : Array Instruction} (h : TS N T c) (hT : T ≤ T') : TS N T' c :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.le hT⟩

lemma mulS {N T : ℕ} {c : Array Instruction} (hst : TS N T c) (hsz : c.size + 2 ≤ capN N)
    {a b : DualRef} {A B : NCPoly} {ea eb sa sb : ℕ}
    (ha : RS N c a A ea sa) (hb : RS N c b B eb sb) (hB : ea + eb ≤ 3 * N - 2) :
    RS N (pMul c a b).1 (pMul c a b).2 (A * B) (ea + eb) (sa + sb) ∧
    TS N (max T (sa + sb)) (pMul c a b).1 ∧ Ext c (pMul c a b).1 ∧ Kept (N - 1) c (pMul c a b).1 ∧
    (pMul c a b).1.size = c.size + 2 ∧
    CT (dualMul a b) c (pMul c a b).2 (pMul c a b).1 (2 * Eb (capN N) (LN N)) := by
  obtain ⟨hbw, hl, hd, hib, hs, hn⟩ := hst
  obtain ⟨hsemA, hnsA⟩ := ha
  obtain ⟨hsemB, hnsB⟩ := hb
  have rla : Rl c.size a := ⟨hsemA.1, hsemA.2.1⟩
  have rlb : Rl c.size b := ⟨hsemB.1, hsemB.2.1⟩
  obtain ⟨ib, ns, bb, kk, sz, rl, ct⟩ := mul_step (L := LN N) hib hsz rla rlb hnsA hnsB hn
  obtain ⟨g1, g2, g3⟩ := pMul_good (B := 3 * N - 2) (L := LN N) hbw hl hd hsemA hsemB hB
  refine ⟨⟨pMul_sem hsemA hsemB, ns⟩, ⟨g1, g2, g3, ib, by omega, bb⟩, pMul_ext c a b, kk, sz, ct⟩

lemma addS {N T : ℕ} {c : Array Instruction} (hst : TS N T c) (hsz : c.size + 2 ≤ capN N)
    {a b : DualRef} {A B : NCPoly} {ea eb sa sb : ℕ}
    (ha : RS N c a A ea sa) (hb : RS N c b B eb sb) (hB : max ea eb ≤ 3 * N - 2) :
    RS N (pAdd c a b).1 (pAdd c a b).2 (A + B) (max ea eb) (max sa sb + 1) ∧
    TS N (max T (max sa sb + 1)) (pAdd c a b).1 ∧ Ext c (pAdd c a b).1 ∧
    Kept (N - 1) c (pAdd c a b).1 ∧ (pAdd c a b).1.size = c.size + 2 ∧
    CT (dualAdd a b) c (pAdd c a b).2 (pAdd c a b).1 (2 * Eb (capN N) (LN N)) := by
  obtain ⟨hbw, hl, hd, hib, hs, hn⟩ := hst
  obtain ⟨hsemA, hnsA⟩ := ha
  obtain ⟨hsemB, hnsB⟩ := hb
  have rla : Rl c.size a := ⟨hsemA.1, hsemA.2.1⟩
  have rlb : Rl c.size b := ⟨hsemB.1, hsemB.2.1⟩
  obtain ⟨ib, ns, bb, kk, sz, rl, ct⟩ := add_step (L := LN N) hib hsz rla rlb hnsA hnsB hn
  obtain ⟨g1, g2, g3⟩ := pAdd_good (B := 3 * N - 2) (L := LN N) hbw hl hd hsemA hsemB hB
  refine ⟨⟨pAdd_sem hsemA hsemB, ns⟩, ⟨g1, g2, g3, ib, by omega, bb⟩, pAdd_ext c a b, kk, sz, ct⟩

lemma scaleS {N T : ℕ} {c : Array Instruction} (hst : TS N T c) (hsz : c.size + 2 ≤ capN N)
    {a : DualRef} {A : NCPoly} {ea sa : ℕ} (m : ℤ) (hm : signedBits m ≤ LN N)
    (ha : RS N c a A ea sa) (hB : ea ≤ 3 * N - 2) :
    RS N (pScale c m a).1 (pScale c m a).2 (m • A) ea (m.natAbs.size + sa) ∧
    TS N (max T (m.natAbs.size + sa)) (pScale c m a).1 ∧ Ext c (pScale c m a).1 ∧
    Kept (N - 1) c (pScale c m a).1 ∧ (pScale c m a).1.size = c.size + 2 ∧
    CT (dualScale m a) c (pScale c m a).2 (pScale c m a).1 (2 * Eb (capN N) (LN N)) := by
  obtain ⟨hbw, hl, hd, hib, hs, hn⟩ := hst
  obtain ⟨hsemA, hnsA⟩ := ha
  have rla : Rl c.size a := ⟨hsemA.1, hsemA.2.1⟩
  obtain ⟨ib, ns, bb, kk, sz, rl, ct⟩ := scale_step (L := LN N) hib hsz m hm rla hnsA hn
  obtain ⟨g1, g2, g3⟩ := pScale_good (B := 3 * N - 2) (L := LN N) m hbw hl hd hsemA hB hm
  refine ⟨⟨pScale_sem m hsemA, ns⟩, ⟨g1, g2, g3, ib, by omega, bb⟩, pScale_ext c m a, kk, sz, ct⟩

lemma mulE {N T : ℕ} {c : Array Instruction} (hst : TS N T c) (hsz : c.size + 2 ≤ capN N)
    {a b : DualRef} {A B : NCPoly} {ea eb sa sb : ℕ}
    (ha : RS N c a A ea sa) (hb : RS N c b B eb sb) (hB : ea + eb ≤ 3 * N - 2) :
    ∃ (r : DualRef) (c' : Array Instruction), RS N c' r (A * B) (ea + eb) (sa + sb) ∧
      TS N (max T (sa + sb)) c' ∧ Ext c c' ∧ Kept (N - 1) c c' ∧ c'.size = c.size + 2 ∧
      CT (dualMul a b) c r c' (2 * Eb (capN N) (LN N)) := by
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := mulS hst hsz ha hb hB
  exact ⟨_, _, m1, m2, m3, m4, m5, m6⟩

lemma addE {N T : ℕ} {c : Array Instruction} (hst : TS N T c) (hsz : c.size + 2 ≤ capN N)
    {a b : DualRef} {A B : NCPoly} {ea eb sa sb : ℕ}
    (ha : RS N c a A ea sa) (hb : RS N c b B eb sb) (hB : max ea eb ≤ 3 * N - 2) :
    ∃ (r : DualRef) (c' : Array Instruction), RS N c' r (A + B) (max ea eb) (max sa sb + 1) ∧
      TS N (max T (max sa sb + 1)) c' ∧ Ext c c' ∧ Kept (N - 1) c c' ∧ c'.size = c.size + 2 ∧
      CT (dualAdd a b) c r c' (2 * Eb (capN N) (LN N)) := by
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := addS hst hsz ha hb hB
  exact ⟨_, _, m1, m2, m3, m4, m5, m6⟩

lemma scaleE {N T : ℕ} {c : Array Instruction} (hst : TS N T c) (hsz : c.size + 2 ≤ capN N)
    {a : DualRef} {A : NCPoly} {ea sa : ℕ} (m : ℤ) (hm : signedBits m ≤ LN N)
    (ha : RS N c a A ea sa) (hB : ea ≤ 3 * N - 2) :
    ∃ (r : DualRef) (c' : Array Instruction), RS N c' r (m • A) ea (m.natAbs.size + sa) ∧
      TS N (max T (m.natAbs.size + sa)) c' ∧ Ext c c' ∧ Kept (N - 1) c c' ∧
      c'.size = c.size + 2 ∧ CT (dualScale m a) c r c' (2 * Eb (capN N) (LN N)) := by
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := scaleS hst hsz m hm ha hB
  exact ⟨_, _, m1, m2, m3, m4, m5, m6⟩

lemma ct_power (N : ℕ) (hN : 2 ≤ N) (base i : DualRef) (P : NCPoly) (sb si T : ℕ)
    (c : Array Instruction) :
    ∀ k : ℕ, c.size + 2 * k ≤ capN N → k ≤ capN N → TS N T c → RS N c base P 0 sb →
      RS N c i 1 0 si →
      ∃ (r : DualRef) (c' : Array Instruction),
        CT (emitPower base i k) c r c' (k * (2 * Eb (capN N) (LN N) + Qc (capN N))) ∧
        RS N c' r (P ^ k) 0 (si + k * sb) ∧ TS N (max T (si + k * sb)) c' ∧ Ext c c' ∧
        Kept (N - 1) c c' ∧ c'.size = c.size + 2 * k := by
  intro k
  induction k generalizing c T with
  | zero =>
    intro _ _ hts hb hi
    refine ⟨i, c, ?_, by simpa using hi, by simpa using hts.le (le_max_left _ _),
      Ext.refl c, Kept.refl _ _, by simp⟩
    simpa [emitPower] using CT.pure' i c
  | succ k ih =>
    intro hsz hk hts hb hi
    obtain ⟨r, c1, hCT, hr, hts1, hx1, hk1, hs1⟩ := ih T c (by omega) (by omega) hts hb hi
    have hb1 := hb.mono hx1 hk1
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := mulS (a := r) (b := base) (A := P ^ k) (B := P) (ea := 0)
      (eb := 0) (sa := si + k * sb) (sb := sb) hts1 (by omega) hr hb1 (by omega)
    have hmul : (k + 1) * sb = k * sb + sb := by ring
    refine ⟨(pMul c1 r base).2, (pMul c1 r base).1, ?_, ?_, ?_, hx1.trans m3, hk1.trans m4, ?_⟩
    · unfold emitPower
      refine CT.mono (κ := (Qc (capN N)) + (k * (2 * Eb (capN N) (LN N) + Qc (capN N)) +
        2 * Eb (capN N) (LN N))) ?_ ?_
      · refine CT.bind (ct_charge_le c (capN N) _ ?_) ?_
        · have := refBits_le k
          show refBits k + 1 + 1 ≤ 8 * (capN N + 1) ^ 2
          nlinarith
        · exact CT.bind hCT m6
      · nlinarith
    · rw [pow_succ]
      exact m1.le (by omega) (by omega)
    · exact m2.le (by omega)
    · omega

end
end UniformADProbes.Trace.Dev.GoalTail1
end

section
/-! Horner emission. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalTail2
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun UniformADProbes.Trace.Dev.GoalNB
  UniformADProbes.Trace.Dev.GoalCT UniformADProbes.Trace.Dev.GoalOps UniformADProbes.Trace.Dev.GoalProbe
  UniformADProbes.Trace.Dev.GoalTail1
noncomputable section

/-- Horner value -/
def hv (P : NCPoly) : List NCPoly → NCPoly
  | [] => 0
  | u :: l => u + P * hv P l

lemma hv_eq (P : NCPoly) (l : List NCPoly) :
    hv P l = ∑ j ∈ Finset.range l.length, P ^ j * l[j]! := by
  induction l with
  | nil => simp [hv]
  | cons u l ih =>
    rw [hv, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, one_mul, List.getElem!_cons_zero, List.getElem!_cons_succ, pow_succ']
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc]

lemma hv_drop (P : NCPoly) (l : List NCPoly) (m : ℕ) (hm : m < l.length) :
    hv P (l.drop m) = l[m]! + P * hv P (l.drop (m + 1)) := by
  rw [List.drop_eq_getElem_cons hm, hv]
  simp [hm]

lemma forall2_mem {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) {a : α} (ha : a ∈ l1) : ∃ b, R a b := by
  induction h with
  | nil => cases ha
  | cons hab _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨_, hab⟩
    · exact ih ha'

def hStep (base zero : DualRef) (U : Array DualRef) (j : ℕ) (acc : DualRef) :
    Emit (ForInStep DualRef) := do
  let u ← tableGet U j zero
  let m ← dualMul base acc
  let acc' ← dualAdd u m
  pure (ForInStep.yield acc')

lemma emitHorner_eq (base zero : DualRef) (U : Array DualRef) :
    emitHorner base zero U =
      (forIn (List.range U.size).reverse zero (hStep base zero U)) >>= fun s => pure s := rfl

lemma ct_horner_loop (N : ℕ) (hN : 2 ≤ N) (base zero : DualRef) (P : NCPoly) (sb su : ℕ)
    (c : Array Instruction) (U : Array DualRef) (Ul : List NCPoly)
    (hb : RS N c base P 0 sb) (hU : List.Forall₂ (fun r Q => RS N c r Q (N - 1) su) U.toList Ul)
    (hz : RS N c zero 0 0 0) (hM : U.size ≤ capN N) :
    ∀ m : ℕ, m ≤ U.size → ∀ (c1 : Array Instruction) (acc1 : DualRef) (T1 s1 : ℕ),
      Ext c c1 → Kept (N - 1) c c1 → c1.size + 4 * m ≤ capN N → TS N T1 c1 →
      RS N c1 acc1 (hv P (Ul.drop m)) (N - 1) s1 →
      ∃ (acc' : DualRef) (c' : Array Instruction),
        CT (forIn (List.range m).reverse acc1 (hStep base zero U)) c1 acc' c'
          (m * (Qc (capN N) + 4 * Eb (capN N) (LN N))) ∧
        RS N c' acc' (hv P Ul) (N - 1) (s1 + m * (su + sb + 1)) ∧
        TS N (max T1 (s1 + m * (su + sb + 1))) c' ∧ Ext c1 c' ∧ Kept (N - 1) c1 c' ∧
        c'.size = c1.size + 4 * m := by
  have hlen : Ul.length = U.size := by
    have := hU.length_eq; simpa using this.symm
  intro m
  induction m with
  | zero =>
    intro _ c1 acc1 T1 s1 hx hk _ hts hacc
    refine ⟨acc1, c1, ?_, ?_, ?_, Ext.refl _, Kept.refl _ _, by simp⟩
    · simpa using CT.pure' acc1 c1
    · simpa using hacc
    · simpa using hts.le (le_max_left _ _)
  | succ m ih =>
    intro hm c1 acc1 T1 s1 hx hk hsz hts hacc
    have hmU : m < U.size := by omega
    have hmUl : m < Ul.length := by omega
    have hent : RS N c (U[m]) (Ul[m]!) (N - 1) su := by
      have := (List.forall₂_iff_get.mp hU).2 m (by simpa using hmU) hmUl
      simpa [hmUl] using this
    have hent1 := hent.mono hx hk
    have hbz : RS N c1 base P 0 sb := hb.mono hx hk
    have hRl : ∀ r ∈ U.toList, Rl c1.size r := by
      intro r hr
      obtain ⟨Q, hQ⟩ := forall2_mem hU hr
      exact ⟨lt_of_lt_of_le hQ.1.1 hx.1, lt_of_lt_of_le hQ.1.2.1 hx.1⟩
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := mulS (a := base) (b := acc1) (A := P)
      (B := hv P (Ul.drop (m + 1))) (ea := 0) (eb := N - 1) (sa := sb) (sb := s1) hts (by omega)
      hbz hacc (by omega)
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := addS (a := U[m]) (b := (pMul c1 base acc1).2)
      (A := Ul[m]!) (B := P * hv P (Ul.drop (m + 1))) (ea := N - 1) (eb := 0 + (N - 1)) (sa := su)
      (sb := sb + s1) m2 (by omega) (hent1.mono m3 m4) m1 (by omega)
    have hmul : (m + 1) * (su + sb + 1) = m * (su + sb + 1) + (su + sb + 1) := by ring
    have hval : hv P (Ul.drop m) = Ul[m]! + P * hv P (Ul.drop (m + 1)) := hv_drop P Ul m hmUl
    have ha1 : RS N (pAdd (pMul c1 base acc1).1 U[m] (pMul c1 base acc1).2).1
        (pAdd (pMul c1 base acc1).1 U[m] (pMul c1 base acc1).2).2 (hv P (Ul.drop m)) (N - 1)
        (s1 + (su + sb + 1)) := by
      rw [hval]; exact a1.le (by omega) (by omega)
    obtain ⟨acc', c', hCT, hr, hts', hx', hk', hs'⟩ := ih (by omega)
      (pAdd (pMul c1 base acc1).1 U[m] (pMul c1 base acc1).2).1
      (pAdd (pMul c1 base acc1).1 U[m] (pMul c1 base acc1).2).2 _ _
      (hx.trans (m3.trans a3)) (hk.trans (m4.trans a4)) (by omega) a2 ha1
    refine ⟨acc', c', ?_, ?_, ?_, m3.trans (a3.trans hx'), m4.trans (a4.trans hk'), by omega⟩
    · rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.forIn_cons]
      have hstep : CT (hStep base zero U m acc1) c1
          (ForInStep.yield (pAdd (pMul c1 base acc1).1 U[m] (pMul c1 base acc1).2).2)
          (pAdd (pMul c1 base acc1).1 U[m] (pMul c1 base acc1).2).1
          (Qc (capN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + 0))) := by
        unfold hStep
        have e1 : U[m]?.getD zero = U[m] := by simp [hmU]
        refine CT.bind (r := U[m]?.getD zero) (ct_tableGet_le c1 (capN N) c1.size U m zero
          (by omega) hRl hM (by omega)) ?_
        rw [e1]
        exact CT.bind m6 (CT.bind a6 (CT.pure' _ _))
      refine (CT.bind hstep hCT).mono ?_
      nlinarith
    · simpa [hmul] using hr.le (by omega) (by omega)
    · exact hts'.le (by omega)

lemma ct_horner (N : ℕ) (hN : 2 ≤ N) (base zero : DualRef) (P : NCPoly) (sb su T : ℕ)
    (c : Array Instruction) (U : Array DualRef) (Ul : List NCPoly) (hts : TS N T c)
    (hb : RS N c base P 0 sb) (hU : List.Forall₂ (fun r Q => RS N c r Q (N - 1) su) U.toList Ul)
    (hz : RS N c zero 0 0 0) (hM : U.size ≤ capN N) (hsz : c.size + 4 * U.size ≤ capN N) :
    ∃ (r : DualRef) (c' : Array Instruction),
      CT (emitHorner base zero U) c r c' (U.size * (Qc (capN N) + 4 * Eb (capN N) (LN N))) ∧
      RS N c' r (hv P Ul) (N - 1) (U.size * (su + sb + 1)) ∧
      TS N (max T (U.size * (su + sb + 1))) c' ∧ Ext c c' ∧ Kept (N - 1) c c' ∧
      c'.size = c.size + 4 * U.size := by
  have hlen : Ul.length = U.size := by
    have := hU.length_eq; simpa using this.symm
  have h0 : hv P (Ul.drop U.size) = 0 := by
    rw [← hlen, List.drop_length]; rfl
  obtain ⟨acc', c', hCT, hr, hts', hx', hk', hs'⟩ := ct_horner_loop N hN base zero P sb su c U Ul hb hU
    hz hM U.size le_rfl c zero T 0 (Ext.refl _) (Kept.refl _ _) hsz hts (by rw [h0]; exact hz.le (by omega) (by omega))
  refine ⟨acc', c', ?_, by simpa using hr, by simpa using hts', hx', hk', hs'⟩
  rw [emitHorner_eq]
  simpa using (CT.bind hCT (CT.pure' acc' c'))

end
end UniformADProbes.Trace.Dev.GoalTail2
end

section
/-! Algebra of `adjoint`, evaluation, and the shape of `packedPoly`. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalAlg
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningAdj UniformADProbes.Trace.Dev.Dist Matrix
noncomputable section

lemma adjoint_single (w : Word) : adjoint (MonoidAlgebra.single w (1 : ℤ)) =
    MonoidAlgebra.single (revWord w) (1 : ℤ) := by
  rw [adjoint_eq]
  unfold L
  rw [MonoidAlgebra.lift_single]
  simp [revHom]

lemma revWord_revWord (w : Word) : revWord (revWord w) = w := by
  simp [revWord]

lemma adjoint_adjoint (p : NCPoly) : adjoint (adjoint p) = p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    have : MonoidAlgebra.of ℤ Word w = MonoidAlgebra.single w (1 : ℤ) := rfl
    rw [this, adjoint_single, adjoint_single, revWord_revWord]
  | add f g hf hg => rw [adjoint_add, adjoint_add, hf, hg]
  | smul r f hf => rw [adjoint_zsmul, adjoint_zsmul, hf]

section eval
variable {n : ℕ}

lemma wordEval_rev (H K : Matrix (Fin n) (Fin n) ℤ) (hH : Hᵀ = H) (hK : Kᵀ = K) (l : List Bool) :
    wordEval H K (FreeMonoid.ofList l.reverse) = (wordEval H K (FreeMonoid.ofList l))ᵀ := by
  induction l with
  | nil => simp [wordEval]
  | cons a l ih =>
    have e1 : FreeMonoid.ofList (a :: l) = FreeMonoid.ofList [a] * FreeMonoid.ofList l := rfl
    have e2 : FreeMonoid.ofList (a :: l).reverse =
        FreeMonoid.ofList l.reverse * FreeMonoid.ofList [a] := by
      rw [List.reverse_cons, ← FreeMonoid.ofList_append]
    have wm : ∀ u v : Word, wordEval H K (u * v) = wordEval H K u * wordEval H K v := by
      intro u v; simp only [wordEval_eq, map_mul]
    rw [e1, e2, wm, wm, ih, Matrix.transpose_mul]
    have : wordEval H K (FreeMonoid.ofList [a]) = if a then K else H := by
      simp [wordEval]
    rw [this]
    cases a <;> simp [hH, hK]

lemma polyEval_adjoint (H K : Matrix (Fin n) (Fin n) ℤ) (hH : Hᵀ = H) (hK : Kᵀ = K)
    (p : NCPoly) : polyEval H K (adjoint p) = (polyEval H K p)ᵀ := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    have : MonoidAlgebra.of ℤ Word w = MonoidAlgebra.single w (1 : ℤ) := rfl
    rw [this, adjoint_single, polyEval_eq_ev, polyEval_eq_ev]
    simp only [ev, MonoidAlgebra.lift_single, one_smul]
    have := wordEval_rev H K hH hK w.toList
    rw [wordEval_eq, wordEval_eq] at this
    simpa [revWord] using this
  | add f g hf hg =>
    rw [adjoint_add, polyEval_eq_ev, map_add, ← polyEval_eq_ev, ← polyEval_eq_ev, hf, hg,
      polyEval_eq_ev, polyEval_eq_ev, polyEval_eq_ev, map_add, Matrix.transpose_add]
  | smul r f hf =>
    rw [adjoint_zsmul, polyEval_eq_ev, map_zsmul, ← polyEval_eq_ev, hf, polyEval_eq_ev,
      polyEval_eq_ev, map_zsmul, Matrix.transpose_smul]

end eval

end
end UniformADProbes.Trace.Dev.GoalAlg
end

section
/-! The shape of `packedPoly` and the trace as a base-`b` packing of Gram entries. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalTr2
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningAdj UniformADProbes.Trace.Dev.Dist
  UniformADProbes.Trace.Dev.GoalAlg Matrix
noncomputable section

def Mn (N : ℕ) : ℕ := N * (N + 1) / 2
def bb (N : ℕ) : ℤ := (packingBase N : ℤ)
def Ub (N j : ℕ) : NCPoly := (probeList N)[j]!
def Yp (N : ℕ) : NCPoly := ((List.range (Mn N)).map fun j => bb N ^ j • Ub N j).sum
def Zp (N : ℕ) : NCPoly := ((List.range (Mn N)).map fun i => bb N ^ (i * Mn N) • Ub N i).sum
def Wp (N : ℕ) : NCPoly := 1 + bb N ^ (Mn N ^ 2) • x + bb N ^ (2 * Mn N ^ 2) • y
def Pp (N : ℕ) : NCPoly := distanceSum N * adjoint (Zp N) * Wp N * Yp N

lemma packedPoly_eq (N : ℕ) (hN : 2 ≤ N) : packedPoly N = Pp N + adjoint (Pp N) := by
  have h : ¬ N ≤ 1 := by omega
  unfold packedPoly
  rw [if_neg h]
  unfold Pp
  simp only [adjoint_mul, adjoint_adjoint]
  have hW : adjoint (Wp N) = Wp N := by
    unfold Wp
    rw [adjoint_add, adjoint_add, adjoint_one, adjoint_zsmul, adjoint_zsmul, adjoint_x, adjoint_y]
  rw [hW]
  simp only [Zp, Yp, Wp, Ub, Mn, bb, mul_assoc]

lemma packed_selfadjoint (N : ℕ) : adjoint (packedPoly N) = packedPoly N := by
  by_cases hN : 2 ≤ N
  · rw [packedPoly_eq N hN, adjoint_add, adjoint_adjoint, add_comm]
  · have : packedPoly N = 1 := by
      unfold packedPoly; rw [if_pos (by omega)]
    rw [this, adjoint_one]

lemma list_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

section ev
variable {n : ℕ}

def tot (X : Matrix (Fin n) (Fin n) ℤ) : ℤ := ∑ a, ∑ c, X a c

lemma tot_sum {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) ℤ) :
    tot (∑ i ∈ s, f i) = ∑ i ∈ s, tot (f i) := by
  unfold tot
  simp only [Matrix.sum_apply]
  calc ∑ a, ∑ c, ∑ i ∈ s, f i a c = ∑ a, ∑ i ∈ s, ∑ c, f i a c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ a, ∑ c, f i a c := Finset.sum_comm

lemma tot_smul (c : ℤ) (X : Matrix (Fin n) (Fin n) ℤ) : tot (c • X) = c * tot X := by
  unfold tot
  simp [Finset.mul_sum]

def Oc : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun _ _ => (1 : ℤ)

lemma trace_ones_mul (X : Matrix (Fin n) (Fin n) ℤ) :
    Matrix.trace (Oc * X) = tot X := by
  simp only [Oc, Matrix.trace, Matrix.diag, Matrix.mul_apply, tot, Matrix.of_apply, one_mul]
  rw [Finset.sum_comm]

/-- the three words `W_s` -/
def Wm (A D : Matrix (Fin n) (Fin n) ℤ) : ℕ → Matrix (Fin n) (Fin n) ℤ
  | 0 => 1
  | 1 => A
  | _ => D

/-- Gram entries -/
def G (A D : Matrix (Fin n) (Fin n) ℤ) (N s i j : ℕ) : ℤ :=
  tot ((ev A D (Ub N i))ᵀ * Wm A D s * ev A D (Ub N j))

lemma ev_Yp (A D : Matrix (Fin n) (Fin n) ℤ) (N : ℕ) :
    ev A D (Yp N) = ∑ j ∈ Finset.range (Mn N), bb N ^ j • ev A D (Ub N j) := by
  unfold Yp
  rw [list_sum_range, map_sum]
  simp [map_zsmul]

lemma ev_Zp_adj (A D : Matrix (Fin n) (Fin n) ℤ) (hA : Aᵀ = A) (hD : Dᵀ = D) (N : ℕ) :
    ev A D (adjoint (Zp N)) = ∑ i ∈ Finset.range (Mn N), bb N ^ (i * Mn N) • (ev A D (Ub N i))ᵀ := by
  rw [← polyEval_eq_ev, polyEval_adjoint A D hA hD, polyEval_eq_ev]
  unfold Zp
  rw [list_sum_range, map_sum, Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Matrix.transpose_smul]

lemma ev_Wp (A D : Matrix (Fin n) (Fin n) ℤ) (N : ℕ) :
    ev A D (Wp N) = ∑ s ∈ Finset.range 3, bb N ^ (s * Mn N ^ 2) • Wm A D s := by
  unfold Wp
  simp [Finset.sum_range_succ, Wm, map_add, map_zsmul, ev_x, ev_y]

lemma trace_packed (A D : Matrix (Fin n) (Fin n) ℤ) (hA : Aᵀ = A) (hD : Dᵀ = D)
    (N : ℕ) (hN : 2 ≤ N)
    (hJ : ev A D (distanceSum N) = Oc) :
    Matrix.trace (polyEval A D (packedPoly N)) =
      2 * ∑ s ∈ Finset.range 3, ∑ i ∈ Finset.range (Mn N), ∑ j ∈ Finset.range (Mn N),
        bb N ^ (s * Mn N ^ 2 + i * Mn N + j) * G A D N s i j := by
  have h2 : polyEval A D (packedPoly N) = ev A D (Pp N) + (ev A D (Pp N))ᵀ := by
    rw [packedPoly_eq N hN, polyEval_eq_ev, map_add, ← polyEval_eq_ev A D (adjoint (Pp N)),
      polyEval_adjoint A D hA hD, polyEval_eq_ev]
  have hP : ev A D (Pp N) = Oc * (
      (∑ i ∈ Finset.range (Mn N), bb N ^ (i * Mn N) • (ev A D (Ub N i))ᵀ) *
      (∑ s ∈ Finset.range 3, bb N ^ (s * Mn N ^ 2) • Wm A D s) *
      (∑ j ∈ Finset.range (Mn N), bb N ^ j • ev A D (Ub N j))) := by
    unfold Pp
    rw [map_mul, map_mul, map_mul, hJ, ev_Zp_adj A D hA hD, ev_Wp, ev_Yp]
    simp only [mul_assoc]
  rw [h2, Matrix.trace_add, Matrix.trace_transpose, hP, trace_ones_mul]
  have e2 : ∀ a b : ℤ, a = b → a + a = 2 * b := by intro a b h; rw [h]; ring
  refine e2 _ _ ?_
  have hexp : ∀ (f : ℕ → Matrix (Fin n) (Fin n) ℤ) (g : ℕ → Matrix (Fin n) (Fin n) ℤ)
      (h : ℕ → Matrix (Fin n) (Fin n) ℤ) (a b c : Finset ℕ),
      (∑ i ∈ a, f i) * (∑ s ∈ b, g s) * (∑ j ∈ c, h j) =
        ∑ i ∈ a, ∑ s ∈ b, ∑ j ∈ c, f i * g s * h j := by
    intro f g h a b c
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
  rw [hexp, tot_sum]
  simp only [tot_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  have key : ∀ (c1 c2 c3 : ℤ) (P Q R : Matrix (Fin n) (Fin n) ℤ),
      ((c1 • P) * (c2 • Q)) * (c3 • R) = (c1 * c2 * c3) • (P * Q * R) := by
    intro c1 c2 c3 P Q R
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    congr 1
    ring
  rw [key, tot_smul]
  unfold G
  rw [pow_add, pow_add]
  ring

end ev

end
end UniformADProbes.Trace.Dev.GoalTr2
end

section
/-! Emission of the distance polynomial sum. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalTail3
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun UniformADProbes.Trace.Dev.GoalNB
  UniformADProbes.Trace.Dev.GoalCT UniformADProbes.Trace.Dev.GoalOps UniformADProbes.Trace.Dev.GoalProbe
  UniformADProbes.Trace.Dev.GoalTail1 UniformADProbes.Trace.Dev.GoalTr2
noncomputable section

lemma distanceSum_eq (N : ℕ) : distanceSum N = ∑ t ∈ Finset.range N, distancePoly t := by
  unfold distanceSum
  exact list_sum_range _ _

lemma dp_succ (k : ℕ) : distancePoly (k + 3) =
    x * distancePoly (k + 2) + (-1 : ℤ) • ((y + (-1 : ℤ) • (1 : NCPoly)) * distancePoly (k + 1)) := by
  show x * distancePoly (k + 2) - (y - 1) * distancePoly (k + 1) = _
  simp [sub_eq_add_neg, neg_smul, one_smul]

lemma dp_two : distancePoly 2 = x * x + (-1 : ℤ) • y := by
  show x * x - y = _
  simp [sub_eq_add_neg, neg_smul, one_smul]

lemma lit_neg_one (N : ℕ) (hN : 1 ≤ N) : signedBits (-1) ≤ LN N := by
  have h1 : 1 ≤ clg N := clg_pos N hN
  show signedBits (-1) ≤ 20 * N * clg N
  have : signedBits (-1) = 2 := by decide
  rw [this]; nlinarith

/-- the bit-size bound at loop step `k` -/
def wk (N k : ℕ) : ℕ := 2 * clg N + 2 + k * (clg N + 5)

lemma wk_succ (N k : ℕ) : wk N (k + 1) = wk N k + (clg N + 5) := by simp only [wk]; ring

lemma wk_zero (N : ℕ) : wk N 0 = 2 * clg N + 2 := by simp [wk]

def distBody (N : ℕ) (a dm : DualRef) (k : ℕ) (s : DualRef × DualRef × DualRef) :
    Emit (ForInStep (DualRef × DualRef × DualRef)) := do
  charge (refBits k + refBits N + 1)
  let q1 ← dualMul a s.2.2
  let q2 ← dualMul dm s.2.1
  let q3 ← dualScale (-1) q2
  let q ← dualAdd q1 q3
  let sum' ← dualAdd s.1 q
  pure (ForInStep.yield (sum', s.2.2, q))

abbrev d1 (cc : Array Instruction) (a curr : DualRef) := pMul cc a curr
abbrev d2 (cc : Array Instruction) (a curr dm prev : DualRef) := pMul (d1 cc a curr).1 dm prev
abbrev d3 (cc : Array Instruction) (a curr dm prev : DualRef) :=
  pScale (d2 cc a curr dm prev).1 (-1) (d2 cc a curr dm prev).2
abbrev d4 (cc : Array Instruction) (a curr dm prev : DualRef) :=
  pAdd (d3 cc a curr dm prev).1 (d1 cc a curr).2 (d3 cc a curr dm prev).2
abbrev d5 (cc : Array Instruction) (a curr dm prev sum : DualRef) :=
  pAdd (d4 cc a curr dm prev).1 sum (d4 cc a curr dm prev).2

lemma ct_dist_loop (N : ℕ) (hN : 3 ≤ N) (a dm : DualRef) (T : ℕ) (c : Array Instruction)
    (ha : RS N c a x 1 (clg N)) (hdm : RS N c dm (y + (-1 : ℤ) • (1 : NCPoly)) 1 (clg N + 2))
    (hsz : c.size + 10 * (N - 3) ≤ capN N)
    (sum prev curr : DualRef)
    (hsum : RS N c sum (∑ t ∈ Finset.range 3, distancePoly t) 2 (wk N 0))
    (hprev : RS N c prev (distancePoly 1) 1 (wk N 0))
    (hcurr : RS N c curr (distancePoly 2) 2 (wk N 0))
    (hts : TS N T c) :
    ∃ (r : DualRef × DualRef × DualRef) (c' : Array Instruction),
      CT (forIn (List.range (N - 3)) (sum, prev, curr) (distBody N a dm)) c r c'
        ((N - 3) * (Qc (capN N) + 10 * Eb (capN N) (LN N))) ∧
      RS N c' r.1 (∑ t ∈ Finset.range N, distancePoly t) (N - 1) (wk N (N - 3)) ∧
      TS N (max T (wk N (N - 3))) c' ∧ Ext c c' ∧ Kept (N - 1) c c' ∧
      c'.size = c.size + 10 * (N - 3) := by
  have hcl := clg_pos N (by omega)
  rw [List.range_eq_range']
  let P : ℕ → (DualRef × DualRef × DualRef) → Array Instruction → Prop :=
    fun k b cc => Ext c cc ∧ Kept (N - 1) c cc ∧ cc.size = c.size + 10 * k ∧
      TS N (max T (wk N k)) cc ∧
      RS N cc b.1 (∑ t ∈ Finset.range (k + 3), distancePoly t) (k + 2) (wk N k) ∧
      RS N cc b.2.1 (distancePoly (k + 1)) (k + 1) (wk N k) ∧
      RS N cc b.2.2 (distancePoly (k + 2)) (k + 2) (wk N k)
  have hP0 : P 0 (sum, prev, curr) c := by
    refine ⟨Ext.refl _, Kept.refl _ _, by simp, by simpa using hts.le (le_max_left _ _), ?_, ?_, ?_⟩
    · simpa using hsum
    · simpa using hprev
    · simpa using hcurr
  obtain ⟨b', c', hT, hPfin⟩ := forIn_range'_ct (distBody N a dm) P
    (Qc (capN N) + 10 * Eb (capN N) (LN N)) (N - 3) 0
    (sum, prev, curr) c hP0 (by
      intro k _ hk b cc hPk
      obtain ⟨hx, hkp, hs, hts1, hsm, hpv, hcu⟩ := hPk
      have hka : RS N cc a x 1 (clg N) := ha.mono hx hkp
      have hkd : RS N cc dm (y + (-1 : ℤ) • (1 : NCPoly)) 1 (clg N + 2) := hdm.mono hx hkp
      have hw : wk N (k + 1) = wk N k + (clg N + 5) := wk_succ N k
      obtain ⟨m1, t1, x1, k1, s1, c1⟩ := mulS (a := a) (b := b.2.2) (A := x)
        (B := distancePoly (k + 2)) (ea := 1) (eb := k + 2) (sa := clg N) (sb := wk N k) hts1
        (by omega) hka hcu (by omega)
      obtain ⟨m2, t2, x2, k2, s2, c2⟩ := mulS (a := dm) (b := b.2.1)
        (A := y + (-1 : ℤ) • (1 : NCPoly)) (B := distancePoly (k + 1)) (ea := 1) (eb := k + 1)
        (sa := clg N + 2) (sb := wk N k) t1 (by omega) (hkd.mono x1 k1) (hpv.mono x1 k1) (by omega)
      obtain ⟨m3, t3, x3, k3, s3, c3⟩ := scaleS (a := (pMul (pMul cc a b.2.2).1 dm b.2.1).2)
        (A := (y + (-1 : ℤ) • (1 : NCPoly)) * distancePoly (k + 1)) (ea := 1 + (k + 1))
        (sa := clg N + 2 + wk N k) t2 (by omega) (-1) (lit_neg_one N (by omega))  m2 (by omega)
      obtain ⟨m4, t4, x4, k4, s4, c4⟩ := addS (a := (pMul cc a b.2.2).2)
        (b := (pScale (pMul (pMul cc a b.2.2).1 dm b.2.1).1 (-1) (pMul (pMul cc a b.2.2).1 dm b.2.1).2).2)
        (A := x * distancePoly (k + 2))
        (B := (-1 : ℤ) • ((y + (-1 : ℤ) • (1 : NCPoly)) * distancePoly (k + 1)))
        (ea := 1 + (k + 2)) (eb := 1 + (k + 1)) (sa := clg N + wk N k)
        (sb := (-1 : ℤ).natAbs.size + (clg N + 2 + wk N k)) t3 (by omega)
        (m1.mono (x2.trans x3) (k2.trans k3)) m3 (by omega)
      obtain ⟨m5, t5, x5, k5, s5, c5⟩ := addS (a := b.1)
        (b := (pAdd (pScale (pMul (pMul cc a b.2.2).1 dm b.2.1).1 (-1) (pMul (pMul cc a b.2.2).1 dm b.2.1).2).1
          (pMul cc a b.2.2).2 (pScale (pMul (pMul cc a b.2.2).1 dm b.2.1).1 (-1) (pMul (pMul cc a b.2.2).1 dm b.2.1).2).2).2)
        (A := ∑ t ∈ Finset.range (k + 3), distancePoly t)
        (B := x * distancePoly (k + 2) + (-1 : ℤ) • ((y + (-1 : ℤ) • (1 : NCPoly)) * distancePoly (k + 1)))
        (ea := k + 2) (eb := max (1 + (k + 2)) (1 + (k + 1)))
        (sa := wk N k)
        (sb := max (clg N + wk N k) ((-1 : ℤ).natAbs.size + (clg N + 2 + wk N k)) + 1) t4 (by omega)
        (hsm.mono (x1.trans (x2.trans (x3.trans x4))) (k1.trans (k2.trans (k3.trans k4)))) m4 (by omega)
      have hn1 : ((-1 : ℤ).natAbs).size = 1 := by decide
      rw [hn1] at m5 t5 t4
      refine ⟨((d5 cc a b.2.2 dm b.2.1 b.1).2, b.2.2, (d4 cc a b.2.2 dm b.2.1).2),
        (d5 cc a b.2.2 dm b.2.1 b.1).1, Qc (capN N) + 10 * Eb (capN N) (LN N), ?_, le_rfl, ?_⟩
      · unfold distBody
        refine CT.mono (κ := Qc (capN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) +
          (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + 0)))))) ?_ ?_
        · refine CT.bind (ct_charge_le cc (capN N) _ ?_) ?_
          · have := refBits_le k; have := refBits_le N
            show refBits k + refBits N + 1 + 1 ≤ 8 * (capN N + 1) ^ 2
            have : N ≤ capN N := by show N ≤ 100 * N ^ 2; nlinarith
            nlinarith
          · exact CT.bind c1 (CT.bind c2 (CT.bind c3 (CT.bind c4 (CT.bind c5 (CT.pure' _ _)))))
        · omega
      · have hsize : (d5 cc a b.2.2 dm b.2.1 b.1).1.size = cc.size + 10 := by
          simp [d5, d4, d3, d2, d1, pMul_size, pAdd_size, pScale_size]
        have hvv : (∑ t ∈ Finset.range (k + 3), distancePoly t) +
            (x * distancePoly (k + 2) + (-1 : ℤ) • ((y + (-1 : ℤ) • (1 : NCPoly)) *
              distancePoly (k + 1))) = ∑ t ∈ Finset.range (k + 1 + 3), distancePoly t := by
          rw [← dp_succ, show k + 1 + 3 = (k + 3) + 1 by ring, Finset.sum_range_succ _ (k + 3)]
        refine ⟨hx.trans (x1.trans (x2.trans (x3.trans (x4.trans x5)))),
          hkp.trans (k1.trans (k2.trans (k3.trans (k4.trans k5)))), by omega, ?_, ?_, ?_, ?_⟩
        · refine t5.le ?_
          simp only [hw]; omega
        · rw [hvv] at m5
          exact m5.le (by omega) (by omega)
        · have := (hcu.mono (x1.trans (x2.trans (x3.trans (x4.trans x5))))
            (k1.trans (k2.trans (k3.trans (k4.trans k5)))))
          exact this.le (by omega) (by omega)
        · have := m4.mono x5 k5
          rw [← dp_succ] at this
          exact this.le (by omega) (by omega))
  obtain ⟨hx, hk, hs, hts', hsm, -, -⟩ := hPfin
  simp only [zero_add] at hsm hts' hs
  have e1 : N - 3 + 3 = N := by omega
  have e2 : N - 3 + 2 = N - 1 := by omega
  rw [e1, e2] at hsm
  refine ⟨b', c', by simpa using hT, hsm, hts', hx, hk, hs⟩

lemma emitDistance_eq (N : ℕ) (hN : 3 ≤ N) (i a d : DualRef) :
    emitDistance N i a d =
      (dualAdd i a >>= fun sum0 =>
        dualMul a a >>= fun l1 => dualScale (-1) d >>= fun l2 =>
        dualAdd l1 l2 >>= fun p2 => dualAdd sum0 p2 >>= fun sum1 =>
        dualScale (-1) i >>= fun l3 => dualAdd d l3 >>= fun dm =>
        (forIn (List.range (N - 3)) (sum1, a, p2) (distBody N a dm)) >>= fun s => pure s.1) := by
  unfold emitDistance
  simp only [if_neg (show ¬ N ≤ 1 by omega), if_neg (show ¬ N = 2 by omega)]
  rfl

lemma kappa_aux (E Q m : ℕ) : 14 * E + m * (Q + 10 * E) ≤ (m + 3) * (Q + 14 * E) := by
  nlinarith [Nat.zero_le (m * Q), Nat.zero_le (m * E), Nat.zero_le Q, Nat.zero_le E]

lemma wk_mono' (N : ℕ) {k k' : ℕ} (h : k ≤ k') : wk N k ≤ wk N k' := by
  simp only [wk]; have := Nat.mul_le_mul_right (clg N + 5) h; omega

abbrev e1 (c : Array Instruction) (i a : DualRef) := pAdd c i a
abbrev e2 (c : Array Instruction) (i a : DualRef) := pMul (e1 c i a).1 a a
abbrev e3 (c : Array Instruction) (i a d : DualRef) := pScale (e2 c i a).1 (-1) d
abbrev e4 (c : Array Instruction) (i a d : DualRef) :=
  pAdd (e3 c i a d).1 (e2 c i a).2 (e3 c i a d).2
abbrev e5 (c : Array Instruction) (i a d : DualRef) :=
  pAdd (e4 c i a d).1 (e1 c i a).2 (e4 c i a d).2
abbrev e6 (c : Array Instruction) (i a d : DualRef) := pScale (e5 c i a d).1 (-1) i
abbrev e7 (c : Array Instruction) (i a d : DualRef) :=
  pAdd (e6 c i a d).1 d (e6 c i a d).2

lemma ct_distance (N : ℕ) (hN : 2 ≤ N) (i a d : DualRef) (T : ℕ) (c : Array Instruction)
    (hts : TS N T c) (hi : RS N c i 1 0 1) (ha : RS N c a x 1 (clg N))
    (hd : RS N c d y 1 (clg N)) (hsz : c.size + 10 * N ≤ capN N) :
    ∃ (J : DualRef) (c' : Array Instruction),
      CT (emitDistance N i a d) c J c' (N * (Qc (capN N) + 14 * Eb (capN N) (LN N))) ∧
      RS N c' J (distanceSum N) (N - 1) (wk N N) ∧ TS N (max T (wk N N)) c' ∧ Ext c c' ∧
      Kept (N - 1) c c' ∧ c'.size ≤ c.size + 10 * N := by
  have hcl := clg_pos N (by omega)
  have hwk : 2 * clg N + 2 + N * (clg N + 5) = wk N N := rfl
  obtain ⟨s0, st0, sx0, sk0, ss0, sc0⟩ := addS (a := i) (b := a) (A := 1) (B := x) (ea := 0)
    (eb := 1) (sa := 1) (sb := clg N) hts (by omega) hi ha (by omega)
  by_cases hN2 : N = 2
  · subst hN2
    refine ⟨(pAdd c i a).2, (pAdd c i a).1, ?_, ?_, ?_, sx0, sk0, by omega⟩
    · unfold emitDistance
      simp only [if_neg (show ¬ (2 ≤ 1) by omega), if_pos rfl]
      refine CT.mono (κ := 2 * Eb (capN 2) (LN 2) + 0) ?_ ?_
      · exact CT.bind sc0 (CT.pure' _ _)
      · nlinarith [Nat.zero_le (Qc (capN 2))]
    · have hs : distanceSum 2 = 1 + x := by
        rw [distanceSum_eq]; simp [Finset.sum_range_succ, distancePoly]
      rw [hs]
      refine s0.le (by omega) ?_
      simp only [wk]; omega
    · refine st0.le ?_
      simp only [wk]; omega
  · have hN3 : 3 ≤ N := by omega
    have ha1 := ha.mono sx0 sk0
    obtain ⟨m1, t1, x1, k1, s1, c1⟩ := mulS st0 (by omega) ha1 ha1 (by omega)
    have hd2 := hd.mono (sx0.trans x1) (sk0.trans k1)
    obtain ⟨m2, t2, x2, k2, s2, c2⟩ := scaleS t1 (by omega) (-1) (lit_neg_one N (by omega)) hd2 (by omega)
    obtain ⟨m3, t3, x3, k3, s3, c3⟩ := addS t2 (by omega) (m1.mono x2 k2) m2 (by omega)
    obtain ⟨m4, t4, x4, k4, s4, c4⟩ := addS t3 (by omega) (s0.mono (x1.trans (x2.trans x3)) (k1.trans (k2.trans k3))) m3 (by omega)
    have hi5 := hi.mono (sx0.trans (x1.trans (x2.trans (x3.trans x4)))) (sk0.trans (k1.trans (k2.trans (k3.trans k4))))
    obtain ⟨m5, t5, x5, k5, s5, c5⟩ := scaleS t4 (by omega) (-1) (lit_neg_one N (by omega)) hi5 (by omega)
    have hd6 := hd.mono (sx0.trans (x1.trans (x2.trans (x3.trans (x4.trans x5)))))
      (sk0.trans (k1.trans (k2.trans (k3.trans (k4.trans k5)))))
    have hn1 : ((-1 : ℤ).natAbs).size = 1 := by decide
    rw [hn1] at m5 t5 t2 t3
    obtain ⟨m6, t6, x6, k6, s6, c6⟩ := addS t5 (by omega) hd6 m5 (by omega)
    have xall := sx0.trans (x1.trans (x2.trans (x3.trans (x4.trans (x5.trans x6)))))
    have kall := sk0.trans (k1.trans (k2.trans (k3.trans (k4.trans (k5.trans k6)))))
    have ha7 := ha.mono xall kall
    have hwk0 : wk N 0 = 2 * clg N + 2 := wk_zero N
    have hs3 : ∑ t ∈ Finset.range 3, distancePoly t = (1 + x) + (x * x + (-1 : ℤ) • y) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, dp_two]; rfl
    have z1 : (e1 c i a).1.size = c.size + 2 := ss0
    have z2 : (e2 c i a).1.size = (e1 c i a).1.size + 2 := s1
    have z3 : (e3 c i a d).1.size = (e2 c i a).1.size + 2 := s2
    have z4 : (e4 c i a d).1.size = (e3 c i a d).1.size + 2 := s3
    have z5 : (e5 c i a d).1.size = (e4 c i a d).1.size + 2 := s4
    have z6 : (e6 c i a d).1.size = (e5 c i a d).1.size + 2 := s5
    have z7 : (e7 c i a d).1.size = (e6 c i a d).1.size + 2 := s6
    have hsum : RS N (e7 c i a d).1 (e5 c i a d).2 (∑ t ∈ Finset.range 3, distancePoly t) 2
        (wk N 0) := by
      rw [hs3]
      exact (m4.mono (x5.trans x6) (k5.trans k6)).le (by omega) (by omega)
    have hprev : RS N (e7 c i a d).1 a (distancePoly 1) 1 (wk N 0) := by
      have e : distancePoly 1 = x := rfl
      rw [e]; exact ha7.le le_rfl (by omega)
    have hcurr : RS N (e7 c i a d).1 (e4 c i a d).2 (distancePoly 2) 2 (wk N 0) := by
      rw [dp_two]
      exact (m3.mono (x4.trans (x5.trans x6)) (k4.trans (k5.trans k6))).le (by omega) (by omega)
    have hdm7 : RS N (e7 c i a d).1 (e7 c i a d).2 (y + (-1 : ℤ) • (1 : NCPoly)) 1 (clg N + 2) :=
      m6.le (by omega) (by omega)
    obtain ⟨r, c', hCT, hr, hts', hx', hk', hs'⟩ := ct_dist_loop N hN3 a (e7 c i a d).2 _
      (e7 c i a d).1 ha7 hdm7 (by omega)
      (e5 c i a d).2 a (e4 c i a d).2 hsum hprev hcurr t6
    refine ⟨r.1, c', ?_, ?_, ?_, xall.trans hx', kall.trans hk', by omega⟩
    · rw [emitDistance_eq N hN3]
      refine CT.mono (κ := 2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) +
        (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) +
        (2 * Eb (capN N) (LN N) + ((N - 3) * (Qc (capN N) + 10 * Eb (capN N) (LN N)) + 0))))))))
        ?_ ?_
      · exact CT.bind sc0 (CT.bind c1 (CT.bind c2 (CT.bind c3 (CT.bind c4 (CT.bind c5
          (CT.bind c6 (CT.bind hCT (CT.pure' _ _))))))))
      · have := kappa_aux (Eb (capN N) (LN N)) (Qc (capN N)) (N - 3)
        have e : N - 3 + 3 = N := by omega
        rw [e] at this
        omega
    · exact hr.le le_rfl (wk_mono' N (by omega))
    · have hm0 : wk N 0 ≤ wk N (N - 3) := wk_mono' N (by omega)
      have hm1 : wk N (N - 3) ≤ wk N N := wk_mono' N (by omega)
      refine hts'.le ?_
      omega

end
end UniformADProbes.Trace.Dev.GoalTail3
end

section
/-! The packing base: value, bit size, and the cost of its construction. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalBase
open UniformADProbes.Trace UniformADProbes.Trace.Dev.GoalNB UniformADProbes.Trace.Dev.GoalProbe
  UniformADProbes.Trace.Dev.GoalCT
noncomputable section

lemma bpow_val (a k : ℕ) : (binaryPower a k).value = a ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (binaryMul (binaryPower a k).value a).value = _
    rw [ih]; show a ^ k * a = _; ring

lemma size_pow_le (a k : ℕ) : (a ^ k).size ≤ k * a.size + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have := size_mul_le (a ^ k) a
    nlinarith

lemma bpow_cost (a K : ℕ) : ∀ k, k ≤ K → (binaryPower a k).cost ≤
    1 + k * ((K * a.size + 2) * (1 + a.size) + K + 2) := by
  intro k
  induction k with
  | zero => intro _; simp [binaryPower]
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := size_pow_le a k
    have h3 := refBits_le k
    have e : (binaryPower a (k + 1)).cost = (binaryPower a k).cost +
        (binaryMul (binaryPower a k).value a).cost + refBits k + 1 := rfl
    rw [e, bpow_val]
    have h4 : (binaryMul (a ^ k) a).cost = (1 + (a ^ k).size) * (1 + a.size) := rfl
    rw [h4]
    have h5 : (1 + (a ^ k).size) * (1 + a.size) ≤ (K * a.size + 2) * (1 + a.size) := by
      apply Nat.mul_le_mul _ le_rfl
      have : k * a.size ≤ K * a.size := Nat.mul_le_mul_right _ (by omega : k ≤ K)
      omega
    nlinarith

lemma cb_val (N : ℕ) : (chargedBase N).value = packingBase N := by
  unfold chargedBase packingBase
  simp only [binaryMul, binaryAdd, bpow_val]
  ring

lemma clg_le (N : ℕ) : clg N ≤ N := by
  show Nat.clog 2 (N + 1) ≤ N
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  exact Nat.lt_two_pow_self

lemma size_le_self (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self

lemma size_3N3 (N : ℕ) (hN : 1 ≤ N) : (3 * (N * N * N)).size ≤ 3 * clg N + 2 := by
  have h1 : N + 1 ≤ 2 ^ clg N := Nat.le_pow_clog (by norm_num) _
  apply Nat.size_le.mpr
  have : N * N * N < 2 ^ (3 * clg N) := by
    calc N * N * N < (N + 1) * (N + 1) * (N + 1) := by
          apply Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (by omega) (by omega)) (by omega)
      _ ≤ 2 ^ clg N * 2 ^ clg N * 2 ^ clg N := by gcongr
      _ = 2 ^ (3 * clg N) := by rw [← pow_add, ← pow_add]; ring_nf
  calc 3 * (N * N * N) < 3 * 2 ^ (3 * clg N) := by omega
    _ ≤ 4 * 2 ^ (3 * clg N) := by omega
    _ = 2 ^ (3 * clg N + 2) := by rw [pow_add]; ring

lemma size_pb (N : ℕ) (hN : 1 ≤ N) : (packingBase N).size ≤ 10 * N * clg N := by
  have hcl := clg_pos N hN
  have e1 := size_le_pow N (N ^ 2) 2 hN (by norm_num) le_rfl
  have e2 := size_pow_le (3 * N ^ 3) (N - 1)
  have e3 : (3 * N ^ 3).size ≤ 3 * clg N + 2 := by
    have := size_3N3 N hN
    have e : N * N * N = N ^ 3 := by ring
    rw [e] at this; exact this
  have e4 := size_mul_le (N ^ 2) (((3 * N ^ 3) ^ (N - 1)) ^ 2)
  have e5 := size_pow_le ((3 * N ^ 3) ^ (N - 1)) 2
  have e6 := size_mul_le 2 (N ^ 2 * (((3 * N ^ 3) ^ (N - 1)) ^ 2))
  have e7 := size_add_le (2 * (N ^ 2 * (((3 * N ^ 3) ^ (N - 1)) ^ 2))) 1
  have h2 : (2 : ℕ).size = 2 := by decide
  have h1 : (1 : ℕ).size = 1 := by decide
  unfold packingBase
  have e8 : (N - 1) * (3 * N ^ 3).size ≤ (N - 1) * (3 * clg N + 2) := Nat.mul_le_mul_left _ e3
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have h10 : 10 * (m + 1) * clg (m + 1) = 10 * (m * clg (m + 1)) + 10 * clg (m + 1) := by ring
  have hm : m * (3 * clg (m + 1) + 2) = 3 * (m * clg (m + 1)) + 2 * m := by ring
  have hmc : m ≤ m * clg (m + 1) := Nat.le_mul_of_pos_right _ hcl
  omega

lemma lit_b (N : ℕ) (hN : 1 ≤ N) : signedBits ((packingBase N : ℕ) : ℤ) ≤ LN N := by
  have h := size_pb N hN
  have hcl := clg_pos N hN
  unfold signedBits
  rw [Int.natAbs_natCast]
  show 1 + max 1 (packingBase N).size ≤ 20 * N * clg N
  have h1 : N * clg N ≥ 1 := Nat.mul_pos (by omega) hcl
  have e1 : 20 * N * clg N = 20 * (N * clg N) := by ring
  have e2 : 10 * N * clg N = 10 * (N * clg N) := by ring
  omega

lemma cb_cost (N : ℕ) (hN : 1 ≤ N) : (chargedBase N).cost + 1 ≤ Qc (capN N) := by
  unfold chargedBase
  simp only [binaryMul, binaryAdd, bpow_val]
  have hcl := clg_pos N hN
  have hcN := clg_le N
  have h3 : (3 : ℕ).size = 2 := by decide
  have h2 : (2 : ℕ).size = 2 := by decide
  have h1 : (1 : ℕ).size = 1 := by decide
  have hs1 : N.size ≤ N := size_le_self N
  have hs2 : (N * N).size ≤ 2 * N := by
    have := size_NN N hN; omega
  have hs3 : (N * N * N).size ≤ 3 * N := by
    have := size_le_pow N (N * N * N) 3 hN (by norm_num) (le_of_eq (by ring))
    omega
  have hs5 : (3 * (N * N * N)).size ≤ 3 * N + 2 := by
    have := size_3N3 N hN; omega
  have hbp := bpow_cost (3 * (N * N * N)) (N - 1) (N - 1) le_rfl
  have hsR0 := size_pow_le (3 * (N * N * N)) (N - 1)
  set R := (3 * (N * N * N)) ^ (N - 1) with hR
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hsR : R.size ≤ m * (3 * (m + 1) + 2) + 1 := by
    have h' : m * (3 * ((m + 1) * (m + 1) * (m + 1))).size ≤ m * (3 * (m + 1) + 2) :=
      Nat.mul_le_mul_left _ hs5
    omega
  have hsR' : R.size ≤ 3 * ((m + 1) * (m + 1)) := by nlinarith
  have hrr : (R * R).size ≤ 6 * ((m + 1) * (m + 1)) := by
    have := size_mul_le R R; omega
  have h8 : ((m + 1) * (m + 1) * (R * R)).size ≤ 2 * (m + 1) + 6 * ((m + 1) * (m + 1)) := by
    have := size_mul_le ((m + 1) * (m + 1)) (R * R); omega
  have h9 : (2 * ((m + 1) * (m + 1) * (R * R))).size ≤ 2 + 2 * (m + 1) + 6 * ((m + 1) * (m + 1)) := by
    have := size_mul_le 2 ((m + 1) * (m + 1) * (R * R)); omega
  have hm : m ≤ m + 1 := by omega
  have c1 : (1 + (m + 1).size) * (1 + (m + 1).size) ≤ (1 + (m + 1)) * (1 + (m + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have c2 : (1 + ((m + 1) * (m + 1)).size) * (1 + (m + 1).size) ≤
      (1 + 2 * (m + 1)) * (1 + (m + 1)) := Nat.mul_le_mul (by omega) (by omega)
  have c3 : (1 + Nat.size 3) * (1 + ((m + 1) * (m + 1) * (m + 1)).size) ≤ 3 * (1 + 3 * (m + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have c4 : (binaryPower (3 * ((m + 1) * (m + 1) * (m + 1))) m).cost ≤
      1 + (m + 1) * (((m + 1) * (3 * (m + 1) + 2) + 2) * (3 * (m + 1) + 3) + (m + 1) + 2) := by
    refine hbp.trans ?_
    have e1 : m * (3 * ((m + 1) * (m + 1) * (m + 1))).size + 2 ≤ (m + 1) * (3 * (m + 1) + 2) + 2 := by
      have := Nat.mul_le_mul hm hs5
      omega
    have e2 : (m * (3 * ((m + 1) * (m + 1) * (m + 1))).size + 2) *
        (1 + (3 * ((m + 1) * (m + 1) * (m + 1))).size) ≤
        ((m + 1) * (3 * (m + 1) + 2) + 2) * (3 * (m + 1) + 3) :=
      Nat.mul_le_mul e1 (by omega)
    have e3 : m * ((m * (3 * ((m + 1) * (m + 1) * (m + 1))).size + 2) *
        (1 + (3 * ((m + 1) * (m + 1) * (m + 1))).size) + m + 2) ≤
        (m + 1) * (((m + 1) * (3 * (m + 1) + 2) + 2) * (3 * (m + 1) + 3) + (m + 1) + 2) :=
      Nat.mul_le_mul hm (by omega)
    omega
  have c5 : (1 + R.size) * (1 + R.size) ≤ (1 + 3 * ((m + 1) * (m + 1))) * (1 + 3 * ((m + 1) * (m + 1))) :=
    Nat.mul_le_mul (by omega) (by omega)
  have c6 : (1 + ((m + 1) * (m + 1)).size) * (1 + (R * R).size) ≤
      (1 + 2 * (m + 1)) * (1 + 6 * ((m + 1) * (m + 1))) := Nat.mul_le_mul (by omega) (by omega)
  have c7 : (1 + Nat.size 2) * (1 + ((m + 1) * (m + 1) * (R * R)).size) ≤
      3 * (1 + 2 * (m + 1) + 6 * ((m + 1) * (m + 1))) := Nat.mul_le_mul (by omega) (by omega)
  have c9 := refBits_le (m + 1)
  have hq1 : m + 1 ≤ (m + 1) * (m + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hq2 : (m + 1) * (m + 1) ≤ (m + 1) * (m + 1) * (m + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq3 : (m + 1) * (m + 1) * (m + 1) ≤ (m + 1) * (m + 1) * (m + 1) * (m + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  show _ ≤ 8 * (100 * (m + 1) ^ 2 + 1) ^ 2
  nlinarith

end
end UniformADProbes.Trace.Dev.GoalBase
end

section
/-! The part of the emitter after the probes. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalRest
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun UniformADProbes.Trace.Dev.GoalNB
  UniformADProbes.Trace.Dev.GoalCT UniformADProbes.Trace.Dev.GoalOps UniformADProbes.Trace.Dev.GoalProbe
  UniformADProbes.Trace.Dev.GoalTail1 UniformADProbes.Trace.Dev.GoalTail2 UniformADProbes.Trace.Dev.GoalTail3
  UniformADProbes.Trace.Dev.GoalBase UniformADProbes.Trace.Dev.GoalTr2 UniformADProbes.Trace.Dev.GoalAlg
noncomputable section

def restProg (N : ℕ) (i a d z : DualRef) (U : Array DualRef) : Emit ℕ := do
  let J ← emitDistance N i a d
  let b := chargedBase N
  charge b.cost
  let B ← dualScale (b.value : ℤ) i
  let BM ← emitPower B i U.size
  let BM2 ← emitPower BM i U.size
  let B2M2 ← dualMul BM2 BM2
  let Y ← emitHorner B z U
  let Z ← emitHorner BM z U
  let l1 ← dualMul BM2 a
  let l2 ← dualAdd i l1
  let l3 ← dualMul B2M2 d
  let W ← dualAdd l2 l3
  let l4 ← dualMul J (dualSwap Z)
  let l5 ← dualMul l4 W
  let t ← dualMul l5 Y
  let out ← dualAdd t (dualSwap t)
  return out.1

open UniformADProbes.Trace.Dev.SpanningProg in
lemma invariantProgram_eq (N : ℕ) (hN : 2 ≤ N) :
    invariantProgram N =
      (initial >>= fun t => (emitProbes N t.1 t.2.1 t.2.2.1 t.2.2.2) >>= fun U =>
        restProg N t.1 t.2.1 t.2.2.1 t.2.2.2 U).run {} := by
  unfold invariantProgram restProg
  simp only [if_neg (show ¬ N ≤ 1 by omega)]

lemma smul_one_pow (c : ℤ) (k : ℕ) : (c • (1 : NCPoly)) ^ k = (c ^ k) • (1 : NCPoly) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, smul_mul_assoc, one_mul, smul_smul, pow_succ]

lemma smul_one_mul' (c : ℤ) (p : NCPoly) : (c • (1 : NCPoly)) * p = c • p := by
  rw [smul_mul_assoc, one_mul]

lemma RS.swap {N : ℕ} {c : Array Instruction} {r : DualRef} {P : NCPoly} {e s : ℕ}
    (h : RS N c r P e s) : RS N c (r.2, r.1) (adjoint P) e s := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩ := h
  refine ⟨⟨h2, h1, h4, ?_, h6, h5⟩, h8, h7⟩
  show rv c r.1 = adjoint (adjoint P)
  rw [adjoint_adjoint]; exact h3

/-- size functions -/
def sB (N : ℕ) : ℕ := (packingBase N).size + 1
def sBM (N M : ℕ) : ℕ := 1 + M * sB N
def sBM2 (N M : ℕ) : ℕ := 1 + M * sBM N M
def sB2M2 (N M : ℕ) : ℕ := sBM2 N M + sBM2 N M
def sY (N M su : ℕ) : ℕ := M * (su + sB N + 1)
def sZ (N M su : ℕ) : ℕ := M * (su + sBM N M + 1)
def sW (N M : ℕ) : ℕ := max (max 1 (sBM2 N M + clg N) + 1) (sB2M2 N M + clg N) + 1
def sT (N M su : ℕ) : ℕ := ((wk N N + sZ N M su) + sW N M) + sY N M su

def Kc (N M : ℕ) : ℕ :=
  N * (Qc (capN N) + 14 * Eb (capN N) (LN N)) + Qc (capN N) + 2 * Eb (capN N) (LN N) +
    2 * (M * (2 * Eb (capN N) (LN N) + Qc (capN N))) + 2 * Eb (capN N) (LN N) +
    2 * (M * (Qc (capN N) + 4 * Eb (capN N) (LN N))) +
    2 * Eb (capN N) (LN N) + 2 * Eb (capN N) (LN N) + 2 * Eb (capN N) (LN N) +
    2 * Eb (capN N) (LN N) + 2 * Eb (capN N) (LN N) + 2 * Eb (capN N) (LN N) +
    2 * Eb (capN N) (LN N) + 2 * Eb (capN N) (LN N)

lemma hv_scalar (c : ℤ) (l : List NCPoly) :
    hv (c • (1 : NCPoly)) l = ∑ j ∈ Finset.range l.length, c ^ j • l[j]! := by
  rw [hv_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_one_pow, smul_one_mul']

lemma Yp_eq (N : ℕ) (hlen : (probeList N).length = Mn N) :
    hv ((bb N) • (1 : NCPoly)) (probeList N) = Yp N := by
  rw [hv_scalar, hlen]
  unfold Yp
  rw [list_sum_range]
  rfl

lemma Zp_eq (N : ℕ) (hlen : (probeList N).length = Mn N) :
    hv ((bb N) ^ Mn N • (1 : NCPoly)) (probeList N) = Zp N := by
  rw [hv_scalar, hlen]
  unfold Zp
  rw [list_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm]
  rfl

lemma Wp_eq (N : ℕ) :
    (1 : NCPoly) + ((((bb N) • (1 : NCPoly)) ^ Mn N) ^ Mn N) * x +
      (((((bb N) • (1 : NCPoly)) ^ Mn N) ^ Mn N) * ((((bb N) • (1 : NCPoly)) ^ Mn N) ^ Mn N)) * y =
    Wp N := by
  unfold Wp
  simp only [smul_one_pow, smul_one_mul', smul_mul_assoc, one_mul, ← pow_mul, smul_smul, ← pow_add]
  congr 3 <;> ring_nf

lemma ct_rest (N : ℕ) (hN : 2 ≤ N) (i a d z : DualRef) (U : Array DualRef) (c : Array Instruction)
    (T Tf su : ℕ) (hts : TS N T c)
    (hi : RS N c i 1 0 1) (ha : RS N c a x 1 (clg N)) (hd : RS N c d y 1 (clg N))
    (hz : RS N c z 0 0 0)
    (hU : List.Forall₂ (fun r Q => RS N c r Q (N - 1) su) U.toList (probeList N))
    (hMU : U.size = Mn N) (hlen : (probeList N).length = Mn N)
    (hsz : c.size + 12 * U.size + 10 * N + 20 ≤ capN N) (hM : U.size ≤ capN N)
    (hT : T ≤ Tf) (hJ : wk N N ≤ Tf) (hB : sB N ≤ Tf) (hBM : sBM N U.size ≤ Tf)
    (hBM2 : sBM2 N U.size ≤ Tf) (hB2M2 : sB2M2 N U.size ≤ Tf)
    (hY : sY N U.size su ≤ Tf) (hZ : sZ N U.size su ≤ Tf) (hl1 : sBM2 N U.size + clg N ≤ Tf)
    (hl2 : max 1 (sBM2 N U.size + clg N) + 1 ≤ Tf) (hl3 : sB2M2 N U.size + clg N ≤ Tf)
    (hW : sW N U.size ≤ Tf) (hl4 : wk N N + sZ N U.size su ≤ Tf)
    (hl5 : wk N N + sZ N U.size su + sW N U.size ≤ Tf) (ht : sT N U.size su ≤ Tf)
    (hout : sT N U.size su + 1 ≤ Tf) :
    ∃ (out : ℕ) (c' : Array Instruction) (κ : ℕ),
      CT (restProg N i a d z U) c out c' κ ∧ κ ≤ Kc N U.size ∧
      TS N Tf c' ∧ c'.size ≤ c.size + 12 * U.size + 10 * N + 20 ∧ out < c'.size ∧
      rv c' out = packedPoly N := by
  have ts0 := hts.le hT
  -- 1: the distance polynomial
  obtain ⟨J, c1, hCT1, hJr, tsd, ex1, ke1, sz1⟩ := ct_distance N hN i a d Tf c ts0 hi ha hd (by omega)
  have ts1 : TS N Tf c1 := tsd.le (max_le le_rfl hJ)
  have hi1 := hi.mono ex1 ke1
  have ha1 := ha.mono ex1 ke1
  have hd1 := hd.mono ex1 ke1
  have hz1 := hz.mono ex1 ke1
  have hU1 : List.Forall₂ (fun r Q => RS N c1 r Q (N - 1) su) U.toList (probeList N) :=
    hU.imp (fun r Q h => h.mono ex1 ke1)
  -- 2: the charge
  have hCT2 := ct_charge_le c1 (capN N) (chargedBase N).cost (cb_cost N (by omega))
  -- 3: B
  obtain ⟨B, c2, hBr, tsB, ex2, ke2, sz2, hCT3⟩ := scaleE (m := ((packingBase N : ℕ) : ℤ)) ts1
    (by omega) (lit_b N (by omega)) hi1 (by omega)
  have hsB : ((packingBase N : ℕ) : ℤ).natAbs.size + 1 ≤ Tf := by
    rw [Int.natAbs_natCast]; exact hB
  have ts2 : TS N Tf c2 := tsB.le (max_le le_rfl hsB)
  have hB2 : RS N c2 B ((bb N) • (1 : NCPoly)) 0 (sB N) :=
    hBr.le le_rfl (by rw [Int.natAbs_natCast]; exact le_rfl)
  have hJ2 := hJr.mono ex2 ke2
  have hi2 := hi1.mono ex2 ke2
  have ha2 := ha1.mono ex2 ke2
  have hd2 := hd1.mono ex2 ke2
  have hz2 := hz1.mono ex2 ke2
  have hU2 : List.Forall₂ (fun r Q => RS N c2 r Q (N - 1) su) U.toList (probeList N) :=
    hU1.imp (fun r Q h => h.mono ex2 ke2)
  obtain ⟨BM, c3, hCT4, hBM3, tsBM, ex3, ke3, sz3⟩ := ct_power N hN B i ((bb N) • (1 : NCPoly))
    (sB N) 1 Tf c2 U.size (by omega) hM ts2 hB2 hi2
  have ts3 : TS N Tf c3 := tsBM.le (max_le le_rfl hBM)
  have hJ3 := hJ2.mono ex3 ke3
  have hB3 := hB2.mono ex3 ke3
  have hi3 := hi2.mono ex3 ke3
  have ha3 := ha2.mono ex3 ke3
  have hd3 := hd2.mono ex3 ke3
  have hz3 := hz2.mono ex3 ke3
  have hU3 : List.Forall₂ (fun r Q => RS N c3 r Q (N - 1) su) U.toList (probeList N) :=
    hU2.imp (fun r Q h => h.mono ex3 ke3)
  have hBM3' : RS N c3 BM (((bb N) • (1 : NCPoly)) ^ U.size) 0 (sBM N U.size) := hBM3
  obtain ⟨BM2, c4, hCT5, hBM2r, tsBM2, ex4, ke4, sz4⟩ := ct_power N hN BM i
    (((bb N) • (1 : NCPoly)) ^ U.size) (sBM N U.size) 1 Tf c3 U.size (by omega) hM ts3 hBM3' hi3
  have ts4 : TS N Tf c4 := tsBM2.le (max_le le_rfl hBM2)
  have hBM2' : RS N c4 BM2 ((((bb N) • (1 : NCPoly)) ^ U.size) ^ U.size) 0 (sBM2 N U.size) := hBM2r
  have hJ4 := hJ3.mono ex4 ke4
  have hB4 := hB3.mono ex4 ke4
  have hBM4 := hBM3'.mono ex4 ke4
  have hi4 := hi3.mono ex4 ke4
  have ha4 := ha3.mono ex4 ke4
  have hd4 := hd3.mono ex4 ke4
  have hz4 := hz3.mono ex4 ke4
  have hU4 : List.Forall₂ (fun r Q => RS N c4 r Q (N - 1) su) U.toList (probeList N) :=
    hU3.imp (fun r Q h => h.mono ex4 ke4)
  obtain ⟨B2M2, c5, hB2M2r, tsB2, ex5, ke5, sz5, hCT6⟩ := mulE ts4 (by omega) hBM2' hBM2' (by omega)
  have ts5 : TS N Tf c5 := tsB2.le (max_le le_rfl hB2M2)
  have hB2M2' : RS N c5 B2M2 (((((bb N) • (1 : NCPoly)) ^ U.size) ^ U.size) *
      ((((bb N) • (1 : NCPoly)) ^ U.size) ^ U.size)) 0 (sB2M2 N U.size) :=
    hB2M2r.le (by omega) le_rfl
  have hJ5 := hJ4.mono ex5 ke5
  have hB5 := hB4.mono ex5 ke5
  have hBM5 := hBM4.mono ex5 ke5
  have hi5 := hi4.mono ex5 ke5
  have ha5 := ha4.mono ex5 ke5
  have hd5 := hd4.mono ex5 ke5
  have hz5 := hz4.mono ex5 ke5
  have hU5 : List.Forall₂ (fun r Q => RS N c5 r Q (N - 1) su) U.toList (probeList N) :=
    hU4.imp (fun r Q h => h.mono ex5 ke5)
  have hBM25 := hBM2'.mono ex5 ke5
  obtain ⟨Y, c6, hCT7, hYr, tsY, ex6, ke6, sz6⟩ := ct_horner N hN B z ((bb N) • (1 : NCPoly)) (sB N) su
    Tf c5 U (probeList N) ts5 hB5 hU5 hz5 hM (by omega)
  have ts6 : TS N Tf c6 := tsY.le (max_le le_rfl hY)
  rw [Yp_eq N hlen] at hYr
  have hJ6 := hJ5.mono ex6 ke6
  have hB6 := hB5.mono ex6 ke6
  have hBM6 := hBM5.mono ex6 ke6
  have hi6 := hi5.mono ex6 ke6
  have ha6 := ha5.mono ex6 ke6
  have hd6 := hd5.mono ex6 ke6
  have hz6 := hz5.mono ex6 ke6
  have hU6 : List.Forall₂ (fun r Q => RS N c6 r Q (N - 1) su) U.toList (probeList N) :=
    hU5.imp (fun r Q h => h.mono ex6 ke6)
  have hBM26 := hBM25.mono ex6 ke6
  have hB2M26 := hB2M2'.mono ex6 ke6
  have hBM6' : RS N c6 BM (((bb N) • (1 : NCPoly)) ^ U.size) 0 (sBM N U.size) := hBM6
  obtain ⟨Z, c7, hCT8, hZr, tsZ, ex7, ke7, sz7⟩ := ct_horner N hN BM z
    (((bb N) • (1 : NCPoly)) ^ U.size) (sBM N U.size) su Tf c6 U (probeList N) ts6 hBM6' hU6 hz6 hM
    (by omega)
  have ts7 : TS N Tf c7 := tsZ.le (max_le le_rfl hZ)
  have eZ : (((bb N) • (1 : NCPoly)) ^ U.size) = (bb N) ^ Mn N • (1 : NCPoly) := by
    rw [smul_one_pow, hMU]
  rw [eZ, Zp_eq N hlen] at hZr
  have hJ7 := hJ6.mono ex7 ke7
  have hB7 := hB6.mono ex7 ke7
  have hBM7 := hBM6.mono ex7 ke7
  have hi7 := hi6.mono ex7 ke7
  have ha7 := ha6.mono ex7 ke7
  have hd7 := hd6.mono ex7 ke7
  have hz7 := hz6.mono ex7 ke7
  have hU7 : List.Forall₂ (fun r Q => RS N c7 r Q (N - 1) su) U.toList (probeList N) :=
    hU6.imp (fun r Q h => h.mono ex7 ke7)
  have hBM27 := hBM26.mono ex7 ke7
  have hB2M27 := hB2M26.mono ex7 ke7
  have hY7 := hYr.mono ex7 ke7
  obtain ⟨l1, c8, hl1r, tsl1, ex8, ke8, sz8, hCT9⟩ := mulE ts7 (by omega) hBM27 ha7 (by omega)
  have ts8 : TS N Tf c8 := tsl1.le (max_le le_rfl (by simpa using hl1))
  have hl1' : RS N c8 l1 ((((bb N • (1 : NCPoly)) ^ U.size) ^ U.size) * x) 1 (sBM2 N U.size + clg N) :=
    hl1r.le (by omega) le_rfl
  have hi8 := hi7.mono ex8 ke8
  have ha8 := ha7.mono ex8 ke8
  have hd8 := hd7.mono ex8 ke8
  have hJ8 := hJ7.mono ex8 ke8
  have hZ8 := hZr.mono ex8 ke8
  have hY8 := hY7.mono ex8 ke8
  have hB2M28 := hB2M27.mono ex8 ke8
  obtain ⟨l2, c9, hl2r, tsl2, ex9, ke9, sz9, hCT10⟩ := addE ts8 (by omega) hi8 hl1' (by omega)
  have ts9 : TS N Tf c9 := tsl2.le (max_le le_rfl hl2)
  have hd9 := hd8.mono ex9 ke9
  have hJ9 := hJ8.mono ex9 ke9
  have hZ9 := hZ8.mono ex9 ke9
  have hY9 := hY8.mono ex9 ke9
  have hB2M29 := hB2M28.mono ex9 ke9
  obtain ⟨l3, c10, hl3r, tsl3, ex10, ke10, sz10, hCT11⟩ := mulE ts9 (by omega) hB2M29 hd9 (by omega)
  have ts10 : TS N Tf c10 := tsl3.le (max_le le_rfl hl3)
  have hl2' : RS N c10 l2 (1 + (((((bb N • (1 : NCPoly)) ^ U.size) ^ U.size) * x))) 1
      (max 1 (sBM2 N U.size + clg N) + 1) := (hl2r.mono ex10 ke10).le (by omega) le_rfl
  have hJ10 := hJ9.mono ex10 ke10
  have hZ10 := hZ9.mono ex10 ke10
  have hY10 := hY9.mono ex10 ke10
  obtain ⟨W, c11, hWr, tsW, ex11, ke11, sz11, hCT12⟩ := addE ts10 (by omega) hl2' hl3r (by omega)
  have ts11 : TS N Tf c11 := tsW.le (max_le le_rfl hW)
  have hJ11 := hJ10.mono ex11 ke11
  have hZ11 := hZ10.mono ex11 ke11
  have hY11 := hY10.mono ex11 ke11
  have eW : (((bb N • (1 : NCPoly)) ^ U.size) ^ U.size) = (((bb N • (1 : NCPoly)) ^ Mn N) ^ Mn N) := by
    rw [hMU]
  rw [eW, Wp_eq] at hWr
  have hWr' : RS N c11 W (Wp N) 1 (sW N U.size) := hWr.le (by omega) le_rfl
  obtain ⟨l4, c12, hl4r, tsl4, ex12, ke12, sz12, hCT13⟩ := mulE ts11 (by omega) hJ11 (RS.swap hZ11)
    (by omega)
  have ts12 : TS N Tf c12 := tsl4.le (max_le le_rfl hl4)
  have hW12 := hWr'.mono ex12 ke12
  have hY12 := hY11.mono ex12 ke12
  obtain ⟨l5, c13, hl5r, tsl5, ex13, ke13, sz13, hCT14⟩ := mulE ts12 (by omega) hl4r hW12 (by omega)
  have ts13 : TS N Tf c13 := tsl5.le (max_le le_rfl hl5)
  have hY13 := hY12.mono ex13 ke13
  obtain ⟨t, c14, htr, tst, ex14, ke14, sz14, hCT15⟩ := mulE ts13 (by omega) hl5r hY13 (by omega)
  have ts14 : TS N Tf c14 := tst.le (max_le le_rfl ht)
  have htr' : RS N c14 t _ _ _ := htr
  obtain ⟨o, c15, hor, tso, ex15, ke15, sz15, hCT16⟩ := addE ts14 (by omega) htr' (RS.swap htr') (by omega)
  have ts15 : TS N Tf c15 := tso.le (max_le le_rfl (by rw [max_self]; exact hout))
  have chain : CT (restProg N i a d z U) c o.1 c15 (Kc N U.size) := by
    unfold restProg
    simp only [cb_val]
    refine CT.mono (κ := N * (Qc (capN N) + 14 * Eb (capN N) (LN N)) + (Qc (capN N) + (2 * Eb (capN N) (LN N) + (U.size * (2 * Eb (capN N) (LN N) + Qc (capN N)) + (U.size * (2 * Eb (capN N) (LN N) + Qc (capN N)) + (2 * Eb (capN N) (LN N) + (U.size * (Qc (capN N) + 4 * Eb (capN N) (LN N)) + (U.size * (Qc (capN N) + 4 * Eb (capN N) (LN N)) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (2 * Eb (capN N) (LN N) + (0))))))))))))))))) ?_ (le_of_eq (by unfold Kc; ring))
    exact CT.bind hCT1 (CT.bind hCT2 (CT.bind hCT3 (CT.bind hCT4 (CT.bind hCT5 (CT.bind hCT6
      (CT.bind hCT7 (CT.bind hCT8 (CT.bind hCT9 (CT.bind hCT10 (CT.bind hCT11 (CT.bind hCT12
      (CT.bind hCT13 (CT.bind hCT14 (CT.bind hCT15 (CT.bind hCT16 (CT.pure' _ _))))))))))))))))
  refine ⟨o.1, c15, Kc N U.size, chain, le_rfl, ts15, by omega, hor.1.1, ?_⟩
  · have h1 := hor.1.2.2.1
    rw [h1]
    rw [packedPoly_eq N hN]
    rfl

end
end UniformADProbes.Trace.Dev.GoalRest
end

section
/-! The numeric bounds on the bit sizes in the tail. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalNum
open UniformADProbes.Trace UniformADProbes.Trace.Dev.GoalNB UniformADProbes.Trace.Dev.GoalProbe
  UniformADProbes.Trace.Dev.GoalBase UniformADProbes.Trace.Dev.GoalRest UniformADProbes.Trace.Dev.GoalTr2
  UniformADProbes.Trace.Dev.GoalTail3
noncomputable section

lemma Mn_le (N : ℕ) : Mn N ≤ N * N := by
  unfold Mn
  apply Nat.div_le_of_le_mul
  nlinarith

/-- the global bit-size bound -/
abbrev Tfin (N : ℕ) : ℕ := 90 * N ^ 5 * clg N

lemma Mn_eq (N : ℕ) (hN : 1 ≤ N) : 2 * Mn N = N * (N + 1) := by
  unfold Mn
  have : 2 ∣ N * (N + 1) := by
    rcases Nat.even_or_odd N with h | h
    · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp h) _
    · exact Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.even_add_one.mpr (by simpa using h))) _
  omega

lemma num_all (N : ℕ) (hN : 2 ≤ N) (M : ℕ) (hM : M ≤ N * N) (su : ℕ) (hsu : su ≤ 5 * N * clg N) :
    sB N ≤ Tfin N ∧ sBM N M ≤ Tfin N ∧ sBM2 N M ≤ Tfin N ∧ sB2M2 N M ≤ Tfin N ∧
    sY N M su ≤ Tfin N ∧ sZ N M su ≤ Tfin N ∧ sBM2 N M + clg N ≤ Tfin N ∧
    max 1 (sBM2 N M + clg N) + 1 ≤ Tfin N ∧ sB2M2 N M + clg N ≤ Tfin N ∧ sW N M ≤ Tfin N ∧
    wk N N + sZ N M su ≤ Tfin N ∧ wk N N + sZ N M su + sW N M ≤ Tfin N ∧ sT N M su ≤ Tfin N ∧
    sT N M su + 1 ≤ Tfin N ∧ wk N N ≤ Tfin N := by
  have hc : 1 ≤ clg N := clg_pos N (by omega)
  have hcN : clg N ≤ N := clg_le N
  have hpb := size_pb N (by omega)
  have hnc : 1 ≤ N * clg N := Nat.mul_pos (by omega) hc
  have hA13 : N * clg N ≤ N * N * N * clg N := by
    have : N ≤ N * N * N :=
      (Nat.le_mul_of_pos_left _ (by omega : 0 < N)).trans (Nat.le_mul_of_pos_right _ (by omega))
    exact Nat.mul_le_mul_right _ this
  have hA35 : N * N * N * clg N ≤ N * N * N * N * N * clg N := by
    have : N * N * N ≤ N * N * N * N * N :=
      (Nat.le_mul_of_pos_right _ (by omega : 0 < N)).trans (Nat.le_mul_of_pos_right _ (by omega))
    exact Nat.mul_le_mul_right _ this
  have eq1 : (N * N) * (N * clg N) = N * N * N * clg N := by ring
  have eq3 : (N * N) * (N * N * N * clg N) = N * N * N * N * N * clg N := by ring
  have hnA : N ≤ N * clg N := Nat.le_mul_of_pos_right _ hc
  have hcA : clg N ≤ N * clg N := Nat.le_mul_of_pos_left _ (by omega)
  have e90 : 90 * N ^ 5 * clg N = 90 * (N * N * N * N * N * clg N) := by ring
  have hpb' : (packingBase N).size ≤ 10 * (N * clg N) := by
    have : 10 * N * clg N = 10 * (N * clg N) := by ring
    omega
  have hsu' : su ≤ 5 * (N * clg N) := by
    have : 5 * N * clg N = 5 * (N * clg N) := by ring
    omega
  generalize hA1 : N * clg N = A1 at *
  generalize hA3 : N * N * N * clg N = A3 at *
  generalize hA5 : N * N * N * N * N * clg N = A5 at *
  have hsB : sB N ≤ 11 * A1 := by unfold sB; omega
  have hsBM : sBM N M ≤ 12 * A3 := by
    unfold sBM
    have : M * sB N ≤ (N * N) * (11 * A1) := Nat.mul_le_mul hM hsB
    have e : (N * N) * (11 * A1) = 11 * ((N * N) * A1) := by ring
    rw [e, eq1] at this
    omega
  have hsBM2 : sBM2 N M ≤ 13 * A5 := by
    unfold sBM2
    have : M * sBM N M ≤ (N * N) * (12 * A3) := Nat.mul_le_mul hM hsBM
    have e : (N * N) * (12 * A3) = 12 * ((N * N) * A3) := by ring
    rw [e, eq3] at this
    omega
  have hsB2 : sB2M2 N M ≤ 26 * A5 := by unfold sB2M2; omega
  have hsY : sY N M su ≤ 17 * A3 := by
    unfold sY
    have e1 : su + sB N + 1 ≤ 17 * A1 := by omega
    have : M * (su + sB N + 1) ≤ (N * N) * (17 * A1) := Nat.mul_le_mul hM e1
    have e : (N * N) * (17 * A1) = 17 * ((N * N) * A1) := by ring
    rw [e, eq1] at this
    omega
  have hsZ : sZ N M su ≤ 18 * A5 := by
    unfold sZ
    have e1 : su + sBM N M + 1 ≤ 18 * A3 := by omega
    have : M * (su + sBM N M + 1) ≤ (N * N) * (18 * A3) := Nat.mul_le_mul hM e1
    have e : (N * N) * (18 * A3) = 18 * ((N * N) * A3) := by ring
    rw [e, eq3] at this
    omega
  have hwk : wk N N ≤ 12 * A1 := by
    unfold wk
    have e : N * (clg N + 5) = N * clg N + 5 * N := by ring
    rw [e, hA1]
    omega
  have hsW : sW N M ≤ 28 * A5 := by unfold sW; omega
  have hT : sT N M su ≤ 75 * A5 := by unfold sT; omega
  simp only [Tfin]
  rw [e90]
  unfold sBM2 at *
  unfold sB2M2 sBM2 at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | omega | (unfold sBM2 sB2M2 sZ sW sT at *; omega)

end
end UniformADProbes.Trace.Dev.GoalNum
end

section
/-! The whole emitter: its result and cost. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalMain
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun UniformADProbes.Trace.Dev.GoalNB
  UniformADProbes.Trace.Dev.GoalCT UniformADProbes.Trace.Dev.GoalOps UniformADProbes.Trace.Dev.GoalProbe
  UniformADProbes.Trace.Dev.GoalTail1 UniformADProbes.Trace.Dev.GoalTail3
  UniformADProbes.Trace.Dev.GoalBase UniformADProbes.Trace.Dev.GoalTr2 UniformADProbes.Trace.Dev.GoalRest
  UniformADProbes.Trace.Dev.GoalNum UniformADProbes.Trace.Dev.SpanningProg
noncomputable section

lemma forall2_and {α β : Type} {R : α → β → Prop} {S : α → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) (hs : ∀ a ∈ l1, S a) : List.Forall₂ (fun a b => R a b ∧ S a) l1 l2 := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih =>
    exact List.Forall₂.cons ⟨hab, hs _ (List.mem_cons_self ..)⟩
      (ih (fun a ha => hs a (List.mem_cons_of_mem _ ha)))

lemma sz_aux (N s R : ℕ) (hN : 2 ≤ N) (h1 : 2 * R = N * (N + 1)) (h2 : s + 8 = 12 * R) :
    s + 12 * R + 10 * N + 20 ≤ 100 * N ^ 2 ∧ s ≤ 100 * N ^ 2 ∧ R ≤ N * N ∧ R ≤ 100 * N ^ 2 := by
  have h3 : 2 * N ≤ N * N := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma su_aux (N : ℕ) (hN : 2 ≤ N) : 1 + (N - 1) * delta N ≤ 5 * N * clg N := by
  have hc := clg_pos N (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel, delta, clg] at *
  nlinarith

lemma T0_aux (N : ℕ) (hN : 2 ≤ N) : max (clg N) (1 + (N - 1) * delta N) ≤ Tfin N := by
  have hc := clg_pos N (by omega)
  have hcN := clg_le N
  have hsu := su_aux N hN
  have h5 : N ≤ N ^ 5 := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : 5 * N * clg N ≤ 90 * N ^ 5 * clg N := by
    have : N * clg N ≤ N ^ 5 * clg N := Nat.mul_le_mul_right _ h5
    nlinarith
  have h7 : clg N ≤ 5 * N * clg N := by nlinarith
  exact max_le (by simp only [Tfin]; omega) (by simp only [Tfin]; omega)

def Ktot (N : ℕ) : ℕ :=
  4 * Eb (capN N) (LN N) + (N - 1) * (N * Krow N) + Kc N (Mn N)

lemma main_prog (N : ℕ) (hN : 2 ≤ N) :
    ∃ (c' : Array Instruction) (out : ℕ),
      (invariantProgram N).1 = out ∧ (invariantProgram N).2.code = c' ∧
      (invariantProgram N).2.cost ≤ Ktot N ∧
      TS N (Tfin N) c' ∧ out < c'.size ∧ rv c' out = packedPoly N := by
  obtain ⟨ct0, ib0, nb0, s0, s1, s2, s3⟩ := ct_initial N hN
  obtain ⟨R, c1, hCTp, hI, hn, hk, hR1, hR2, hR3⟩ := ct_probe_core N hN
  -- identification with the sibling's description of the probe run
  obtain ⟨Rs, cs, e1, e2, hbw, hlit, hdgb, hsz', hsem⟩ := probe_trip N hN
  have hpp : probeProgram N =
      (initial >>= fun t => emitProbes N t.1 t.2.1 t.2.2.1 t.2.2.2).run {} := by
    unfold probeProgram
    rw [if_neg (by omega)]
  have hCTa : CT (initial >>= fun t => emitProbes N t.1 t.2.1 t.2.2.1 t.2.2.2) #[] R c1
      (4 * Eb (capN N) (LN N) + (N - 1) * (N * Krow N)) := CT.bind ct0 hCTp
  obtain ⟨r1, r2, -⟩ := hCTa {} rfl
  have hRR : R = Rs := by rw [← e1, hpp]; exact r1.symm
  have hcc : c1 = cs := by rw [← e2, hpp]; exact r2.symm
  subst hRR; subst hcc
  have hext : Ext code0 c1 := ext_of_pre code0 c1 hk.pre
  obtain ⟨i0, i1, i2, i3, -, -, -⟩ := init_facts N hN
  have hMU : R.size = Mn N := by
    have := Mn_eq N (by omega); omega
  have hlen : (probeList N).length = Mn N := by
    have := hsem.length_eq; simp at this; omega
  have hcl := clg_pos N (by omega)
  have hszA := sz_aux N c1.size R.size hN (by have := Mn_eq N (by omega); omega) (by omega)
  have hsz : c1.size + 12 * R.size + 10 * N + 20 ≤ capN N := hszA.1
  have hM : R.size ≤ capN N := hszA.2.2.2
  have hRs : R.size ≤ N * N := hszA.2.2.1
  have hsu := su_aux N hN
  have hT0 := T0_aux N hN
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15⟩ :=
    num_all N hN R.size hRs _ hsu
  have hts : TS N (max (clg N) (1 + (N - 1) * delta N)) c1 := by
    refine ⟨hbw, ?_, ?_, hI, ?_, hn⟩
    · intro I hI' k a hIa
      have := hlit I hI' k a hIa
      have h2 : 8 * Nat.clog 2 (N + 1) ≤ LN N := by
        show 8 * Nat.clog 2 (N + 1) ≤ 20 * N * Nat.clog 2 (N + 1)
        nlinarith
      exact this.trans h2
    · intro r
      have := hdgb r
      omega
    · exact hszA.2.1
  have hi : RS N c1 (0, 0) 1 0 1 := ⟨i0.mono hext, ns_kept s0 ⟨by simp [code0_size], by simp [code0_size]⟩ hk⟩
  have ha : RS N c1 (1, 1) x 1 (clg N) := ⟨i1.mono hext, ns_kept s1 ⟨by simp [code0_size], by simp [code0_size]⟩ hk⟩
  have hd : RS N c1 (2, 2) y 1 (clg N) := ⟨i2.mono hext, ns_kept s2 ⟨by simp [code0_size], by simp [code0_size]⟩ hk⟩
  have hz : RS N c1 (3, 3) 0 0 0 := ⟨i3.mono hext, ns_kept s3 ⟨by simp [code0_size], by simp [code0_size]⟩ hk⟩
  have hU : List.Forall₂ (fun r Q => RS N c1 r Q (N - 1) (1 + (N - 1) * delta N)) R.toList (probeList N) := by
    have := forall2_and hsem (S := fun r => Rl c1.size r ∧ NS (N - 1) c1 r (1 + (N - 1) * delta N)) hR3
    exact this.imp (fun r Q h => ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2⟩, h.2.2⟩)
  obtain ⟨out, c', κ, hCTr, hκ, hts', hsz2, hout, hrv⟩ := ct_rest N hN (0, 0) (1, 1) (2, 2) (3, 3) R c1
    _ (Tfin N) _ hts hi ha hd hz hU hMU hlen hsz hM hT0 n15 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14
  have hCTb : CT (initial >>= fun t => (emitProbes N t.1 t.2.1 t.2.2.1 t.2.2.2) >>= fun U =>
        restProg N t.1 t.2.1 t.2.2.1 t.2.2.2 U) #[] out c'
      (4 * Eb (capN N) (LN N) + ((N - 1) * (N * Krow N) + κ)) := CT.bind ct0 (CT.bind hCTp hCTr)
  rw [invariantProgram_eq N hN]
  obtain ⟨q1, q2, q3⟩ := hCTb {} rfl
  refine ⟨c', out, q1, q2, ?_, hts', hout, hrv⟩
  have : (({} : Builder)).cost = 0 := rfl
  unfold Ktot
  rw [this] at q3
  rw [hMU] at hκ
  omega

end
end UniformADProbes.Trace.Dev.GoalMain
end

section
/-! The numeric bound of the construction cost. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalCostNum
open UniformADProbes.Trace UniformADProbes.Trace.Dev.GoalCT UniformADProbes.Trace.Dev.GoalProbe
  UniformADProbes.Trace.Dev.GoalRest UniformADProbes.Trace.Dev.GoalMain UniformADProbes.Trace.Dev.GoalNum
  UniformADProbes.Trace.Dev.GoalTr2 UniformADProbes.Trace.Dev.GoalBase
noncomputable section

lemma E_le (N : ℕ) (hN : 2 ≤ N) : Eb (capN N) (LN N) ≤ 23000 * (N + 1) ^ 4 := by
  have hcN := clg_le N
  have hL : LN N ≤ 20 * (N + 1) ^ 2 := by
    show 20 * N * clg N ≤ 20 * (N + 1) ^ 2
    nlinarith
  have hcap : capN N + 1 ≤ 100 * (N + 1) ^ 2 := by show 100 * N ^ 2 + 1 ≤ _; nlinarith
  unfold Eb beta
  have hb : 3 + 2 * (capN N + 1) + LN N ≤ 224 * (N + 1) ^ 2 := by nlinarith
  have h1 : (capN N + 1) * (3 + 2 * (capN N + 1) + LN N) ≤ (100 * (N + 1) ^ 2) * (224 * (N + 1) ^ 2) :=
    Nat.mul_le_mul hcap hb
  have hX : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hX3 : 9 ≤ (N + 1) ^ 2 := by nlinarith
  nlinarith

lemma Q_le (N : ℕ) (hN : 2 ≤ N) : Qc (capN N) ≤ 80000 * (N + 1) ^ 4 := by
  have hcap : capN N + 1 ≤ 100 * (N + 1) ^ 2 := by show 100 * N ^ 2 + 1 ≤ _; nlinarith
  unfold Qc
  have : (capN N + 1) ^ 2 ≤ (100 * (N + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hcap 2
  nlinarith

lemma ktot_le (N : ℕ) (hN : 2 ≤ N) : Ktot N ≤ 100000000 * (N + 1) ^ 12 := by
  have hE := E_le N hN
  have hQ := Q_le N hN
  have hM : Mn N ≤ (N + 1) ^ 2 := by
    have := Mn_le N; nlinarith
  set E := Eb (capN N) (LN N) with hEdef
  set Q := Qc (capN N) with hQdef
  set X := N + 1 with hX
  have hX3 : 3 ≤ X := by omega
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX4 : X ^ 2 ≤ X ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hX6 : X ^ 4 ≤ X ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hX12 : 729 * X ^ 6 ≤ X ^ 12 := by
    have : 729 ≤ X ^ 6 := by
      calc 729 = 3 ^ 6 := by norm_num
        _ ≤ X ^ 6 := Nat.pow_le_pow_left hX3 6
    calc 729 * X ^ 6 ≤ X ^ 6 * X ^ 6 := Nat.mul_le_mul_right _ this
      _ = X ^ 12 := by ring
  have hKrow : Krow N ≤ 600000 * X ^ 4 := by
    show 12 * E + 4 * Q ≤ _
    omega
  have hNN : (N - 1) * N ≤ X ^ 2 := by
    have : (N - 1) * N ≤ N * N := Nat.mul_le_mul (by omega) le_rfl
    nlinarith
  have t1 : (N - 1) * (N * Krow N) ≤ 600000 * X ^ 6 := by
    have e : (N - 1) * (N * Krow N) = ((N - 1) * N) * Krow N := by ring
    rw [e]
    calc ((N - 1) * N) * Krow N ≤ X ^ 2 * (600000 * X ^ 4) := Nat.mul_le_mul hNN hKrow
      _ = 600000 * X ^ 6 := by ring
  have hKc : Kc N (Mn N) ≤ 1500000 * X ^ 6 := by
    unfold Kc
    have a1 : N * (Q + 14 * E) ≤ X * (80000 * X ^ 4 + 14 * (23000 * X ^ 4)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have a2 : Mn N * (2 * E + Q) ≤ X ^ 2 * (2 * (23000 * X ^ 4) + 80000 * X ^ 4) :=
      Nat.mul_le_mul hM (by omega)
    have a3 : Mn N * (Q + 4 * E) ≤ X ^ 2 * (80000 * X ^ 4 + 4 * (23000 * X ^ 4)) :=
      Nat.mul_le_mul hM (by omega)
    have b1 : X * (80000 * X ^ 4 + 14 * (23000 * X ^ 4)) ≤ 402000 * X ^ 6 := by
      have : X * X ^ 4 ≤ X ^ 6 := by
        calc X * X ^ 4 = X ^ 5 := by ring
          _ ≤ X ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
    have b2 : X ^ 2 * (2 * (23000 * X ^ 4) + 80000 * X ^ 4) = 126000 * X ^ 6 := by ring
    have b3 : X ^ 2 * (80000 * X ^ 4 + 4 * (23000 * X ^ 4)) = 172000 * X ^ 6 := by ring
    nlinarith
  unfold Ktot
  have h4 : 4 * E ≤ 92000 * X ^ 6 := by nlinarith
  have : 100000000 * X ^ 12 ≥ 100000000 * (729 * X ^ 6) := by nlinarith
  nlinarith

end
end UniformADProbes.Trace.Dev.GoalCostNum
end

section
/-! Base-`b` digit injectivity and the size of the Gram entries. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalTr3
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningAdj UniformADProbes.Trace.Dev.Dist
  UniformADProbes.Trace.Dev.GoalAlg UniformADProbes.Trace.Dev.GoalTr2 UniformADProbes.Trace.Dev.GoalNB
  UniformADProbes.Trace.Dev.SpanningCv Matrix
noncomputable section

lemma digits_inj (H : ℤ) (hH : 0 ≤ H) :
    ∀ (K : ℕ) (f g : ℕ → ℤ), (∀ ν < K, |f ν| ≤ H) → (∀ ν < K, |g ν| ≤ H) →
      ∑ ν ∈ Finset.range K, (2 * H + 1) ^ ν * f ν = ∑ ν ∈ Finset.range K, (2 * H + 1) ^ ν * g ν →
      ∀ ν < K, f ν = g ν := by
  intro K
  induction K with
  | zero => intro f g _ _ _ ν hν; omega
  | succ K ih =>
    intro f g hf hg hsum
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hsum
    simp only [pow_zero, one_mul, pow_succ] at hsum
    set b := 2 * H + 1 with hb
    have e1 : ∑ x ∈ Finset.range K, b ^ x * b * f (x + 1) =
        b * ∑ x ∈ Finset.range K, b ^ x * f (x + 1) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have e2 : ∑ x ∈ Finset.range K, b ^ x * b * g (x + 1) =
        b * ∑ x ∈ Finset.range K, b ^ x * g (x + 1) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    rw [e1, e2] at hsum
    set Sf := ∑ x ∈ Finset.range K, b ^ x * f (x + 1)
    set Sg := ∑ x ∈ Finset.range K, b ^ x * g (x + 1)
    have h0f := hf 0 (by omega)
    have h0g := hg 0 (by omega)
    have hbpos : 0 < b := by omega
    have hdiff : f 0 - g 0 = b * (Sg - Sf) := by linarith
    have hS : Sg - Sf = 0 := by
      by_contra hne
      have : b ≤ |b * (Sg - Sf)| := by
        rw [abs_mul, abs_of_pos hbpos]
        have : 1 ≤ |Sg - Sf| := Int.one_le_abs hne
        nlinarith
      rw [← hdiff] at this
      have := abs_sub (f 0) (g 0)
      rw [abs_le] at h0f h0g
      rw [abs_le] at *
      have h3 : |f 0 - g 0| ≤ 2 * H := by
        rw [abs_le]; constructor <;> linarith [h0f.1, h0f.2, h0g.1, h0g.2]
      linarith
    have hf0 : f 0 = g 0 := by
      have : f 0 - g 0 = 0 := by rw [hdiff, hS]; ring
      linarith
    have hSeq : Sf = Sg := by linarith
    have := ih (fun x => f (x + 1)) (fun x => g (x + 1)) (fun ν h => hf (ν + 1) (by omega))
      (fun ν h => hg (ν + 1) (by omega)) hSeq
    intro ν hν
    rcases ν with _ | ν
    · exact hf0
    · exact this ν (by omega)

lemma sum_range_mul_split (f : ℕ → ℤ) (a c : ℕ) :
    ∑ ν ∈ Finset.range (a * c), f ν = ∑ q ∈ Finset.range a, ∑ r ∈ Finset.range c, f (q * c + r) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Equality of the packed traces gives equality of every Gram entry. -/
lemma gram_inj (M : ℕ) (hM : 0 < M) (H : ℤ) (hH : 0 ≤ H) (G G' : ℕ → ℕ → ℕ → ℤ)
    (hG : ∀ s < 3, ∀ i < M, ∀ j < M, |G s i j| ≤ H)
    (hG' : ∀ s < 3, ∀ i < M, ∀ j < M, |G' s i j| ≤ H)
    (h : ∑ s ∈ Finset.range 3, ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        (2 * H + 1) ^ (s * M ^ 2 + i * M + j) * G s i j =
      ∑ s ∈ Finset.range 3, ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        (2 * H + 1) ^ (s * M ^ 2 + i * M + j) * G' s i j) :
    ∀ s < 3, ∀ i < M, ∀ j < M, G s i j = G' s i j := by
  let F : (ℕ → ℕ → ℕ → ℤ) → ℕ → ℤ := fun G ν => G (ν / (M * M)) (ν % (M * M) / M) (ν % M)
  have hdec : ∀ s i j, i < M → j < M → ∀ (G : ℕ → ℕ → ℕ → ℤ),
      F G (s * (M * M) + (i * M + j)) = G s i j := by
    intro s i j hi hj G
    have h1 : i * M + j < M * M := by nlinarith
    have e1 : (s * (M * M) + (i * M + j)) / (M * M) = s := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt h1]; simp
    have e2 : (s * (M * M) + (i * M + j)) % (M * M) = i * M + j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
    have e3 : (i * M + j) / M = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hj]; simp
    have e4 : (s * (M * M) + (i * M + j)) % M = j := by
      have : s * (M * M) + (i * M + j) = j + M * (s * M + i) := by ring
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    simp only [F, e1, e2, e3, e4]
  have hsum : ∀ (G : ℕ → ℕ → ℕ → ℤ),
      ∑ s ∈ Finset.range 3, ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        (2 * H + 1) ^ (s * M ^ 2 + i * M + j) * G s i j =
      ∑ ν ∈ Finset.range (3 * (M * M)), (2 * H + 1) ^ ν * F G ν := by
    intro G
    symm
    rw [sum_range_mul_split]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [sum_range_mul_split]
    refine Finset.sum_congr rfl fun i hi => ?_
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hi hj
    rw [show s * (M * M) + (i * M + j) = s * (M * M) + (i * M + j) from rfl, hdec s i j hi hj G]
    congr 2
    ring
  have hFb : ∀ (G : ℕ → ℕ → ℕ → ℤ), (∀ s < 3, ∀ i < M, ∀ j < M, |G s i j| ≤ H) →
      ∀ ν < 3 * (M * M), |F G ν| ≤ H := by
    intro G hG ν hν
    have h1 : ν / (M * M) < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
    have h2 : ν % (M * M) / M < M := by
      rw [Nat.div_lt_iff_lt_mul hM]; exact Nat.mod_lt _ (by positivity)
    have h3 : ν % M < M := Nat.mod_lt _ hM
    exact hG _ h1 _ h2 _ h3
  have key := digits_inj H hH (3 * (M * M)) (F G) (F G') (hFb G hG) (hFb G' hG')
    (by rw [← hsum, ← hsum]; exact h)
  intro s hs i hi j hj
  have h1 : i * M + j < M * M := by nlinarith
  have := key (s * (M * M) + (i * M + j)) (by nlinarith)
  rwa [hdec s i j hi hj, hdec s i j hi hj] at this

end
end UniformADProbes.Trace.Dev.GoalTr3
end

section
/-! Norm bounds for the probes and the Gram entries. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalTr4
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningAdj UniformADProbes.Trace.Dev.Dist
  UniformADProbes.Trace.Dev.GoalAlg UniformADProbes.Trace.Dev.GoalTr2 UniformADProbes.Trace.Dev.GoalNB
  UniformADProbes.Trace.Dev.SpanningCv Matrix
noncomputable section

section
variable {n : ℕ}

lemma tot_sandwich (P W Q : Matrix (Fin n) (Fin n) ℤ) :
    tot (Pᵀ * W * Q) = ∑ c, ∑ d, (∑ a, P c a) * W c d * (∑ b, Q d b) := by
  simp only [tot, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  calc ∑ a, ∑ b, ∑ d, ∑ c, P c a * W c d * Q d b
      = ∑ a, ∑ d, ∑ b, ∑ c, P c a * W c d * Q d b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ c, ∑ b, P c a * W c d * Q d b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, P c a * W c d * Q d b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, P c a * W c d * Q d b := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, P c a * W c d * Q d b :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, P c a * W c d * Q d b :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => Finset.sum_comm

lemma rs_le {P : Matrix (Fin n) (Fin n) ℤ} {R : ℕ} (h : RN P R) (c : Fin n) :
    |∑ a, P c a| ≤ R :=
  (Finset.abs_sum_le_sum_abs _ _).trans (h c)

lemma sandwich_le {P Q W : Matrix (Fin n) (Fin n) ℤ} {R w : ℕ} (hP : RN P R) (hQ : RN Q R)
    (hW : RN W w) : |tot (Pᵀ * W * Q)| ≤ (n : ℤ) * w * R * R := by
  rw [tot_sandwich]
  calc |∑ c, ∑ d, (∑ a, P c a) * W c d * (∑ b, Q d b)|
      ≤ ∑ c, |∑ d, (∑ a, P c a) * W c d * (∑ b, Q d b)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : Fin n, ((w : ℤ) * R * R) := by
        refine Finset.sum_le_sum fun c _ => ?_
        calc |∑ d, (∑ a, P c a) * W c d * (∑ b, Q d b)|
            ≤ ∑ d, |(∑ a, P c a) * W c d * (∑ b, Q d b)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ d, (R * |W c d| * R : ℤ) := by
              refine Finset.sum_le_sum fun d _ => ?_
              rw [abs_mul, abs_mul]
              have h1 := rs_le hP c
              have h2 := rs_le hQ d
              gcongr
          _ = (R * R : ℤ) * ∑ d, |W c d| := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
          _ ≤ (R * R : ℤ) * w := by
              exact mul_le_mul_of_nonneg_left (hW c) (by positivity)
          _ = w * R * R := by ring
    _ = (n : ℤ) * w * R * R := by simp; ring

lemma aux_ineq (N : ℕ) (hN : 1 ≤ N) : (N - 1) * (1 + 2 * N ^ 2) ≤ 3 * N ^ 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  nlinarith [Nat.zero_le m, Nat.zero_le (m * m)]

lemma probes_RN (N : ℕ) (hN : 2 ≤ N) (A D : Matrix (Fin n) (Fin n) ℤ) (hA : RN A (N - 1))
    (hD : RN D (N - 1)) : ∀ i : ℕ, i < N → ∀ j : ℤ, RN (ev A D (probes N i j)) ((3 * N ^ 3) ^ i) := by
  intro i
  induction i with
  | zero =>
    intro _ j
    simp only [probes]
    split_ifs
    · simpa using (RN.one : RN (1 : Matrix (Fin n) (Fin n) ℤ) 1)
    · simpa using RN.zero (n := n) _
  | succ i ih =>
    intro hi j
    by_cases hj : j < 0 ∨ ((i + 1 : ℕ) : ℤ) < j
    · rw [probes_out N (i + 1) j hj, map_zero]
      exact RN.zero _
    · have hj0 : 0 ≤ j := by omega
      have hj1 : j ≤ (i : ℤ) + 1 := by omega
      rw [probes_succ N i j hj0 hj1]
      simp only [map_add, map_mul, map_zsmul, map_one, ev_x, ev_y, map_natCast]
      have hP := ih (by omega) j
      have hP' := ih (by omega) (j - 1)
      set c : ℤ := (N : ℤ) ^ 2 * (j - i) with hc
      have h1 : RN (D + c • (1 : Matrix (Fin n) (Fin n) ℤ)) ((N - 1) + c.natAbs * 1) :=
        RN.add hD (RN.smul c RN.one)
      have h2 := RN.mul h1 hP
      have h3 := RN.smul ((N : ℤ) ^ 2) (RN.mul hA hP')
      have h4 := RN.add h2 h3
      refine RN.mono h4 ?_
      have hcn : c.natAbs ≤ N ^ 2 * (N - 1) := by
        rw [hc, Int.natAbs_mul]
        have : (j - i : ℤ).natAbs ≤ N - 1 := by omega
        have e : ((N : ℤ) ^ 2).natAbs = N ^ 2 := by simp
        rw [e]
        exact Nat.mul_le_mul_left _ this
      have e2 : (((N : ℤ) ^ 2).natAbs) = N ^ 2 := by simp
      rw [e2, pow_succ]
      have hL : 1 ≤ (3 * N ^ 3) ^ i := Nat.one_le_pow _ _ (by positivity)
      have hN1 : 1 ≤ N - 1 := by omega
      calc ((N - 1) + c.natAbs * 1) * (3 * N ^ 3) ^ i + N ^ 2 * ((N - 1) * (3 * N ^ 3) ^ i)
          ≤ ((N - 1) + N ^ 2 * (N - 1)) * (3 * N ^ 3) ^ i + N ^ 2 * ((N - 1) * (3 * N ^ 3) ^ i) := by
            have e1 : (N - 1) + c.natAbs * 1 ≤ (N - 1) + N ^ 2 * (N - 1) :=
              Nat.add_le_add_left (by simpa using hcn) _
            exact Nat.add_le_add_right (Nat.mul_le_mul_right _ e1) _
        _ = ((N - 1) * (1 + 2 * N ^ 2)) * (3 * N ^ 3) ^ i := by ring
        _ ≤ (3 * N ^ 3) * (3 * N ^ 3) ^ i := by
            exact Nat.mul_le_mul_right _ (aux_ineq N (by omega))
        _ = (3 * N ^ 3) ^ i * (3 * N ^ 3) := by ring

lemma Ub_mem (N : ℕ) (hlen : (probeList N).length = Mn N) (k : ℕ) (hk : k < Mn N) :
    ∃ i < N, ∃ j : ℕ, Ub N k = probes N i (j : ℤ) := by
  have hk' : k < (probeList N).length := by omega
  have : Ub N k = (probeList N)[k] := by
    unfold Ub; simp [hk']
  have hm := List.getElem_mem hk'
  rw [← this] at hm
  unfold probeList at hm
  rw [List.mem_map] at hm
  obtain ⟨⟨i, j⟩, hij, he⟩ := hm
  unfold probeIndices at hij
  rw [List.mem_flatMap] at hij
  obtain ⟨i', hi', hj'⟩ := hij
  rw [List.mem_map] at hj'
  obtain ⟨j', hj'', hq⟩ := hj'
  simp only [Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  exact ⟨i', List.mem_range.mp hi', j', he.symm⟩

/-- the half-width of the digits -/
def Hn (N : ℕ) : ℕ := N ^ 2 * ((3 * N ^ 3) ^ (N - 1)) ^ 2

lemma bb_eq (N : ℕ) : bb N = 2 * (Hn N : ℤ) + 1 := by
  unfold bb packingBase Hn
  push_cast
  ring

lemma G_bound (N : ℕ) (hN : 2 ≤ N) (hlen : (probeList N).length = Mn N)
    (A D : Matrix (Fin n) (Fin n) ℤ) (hA : RN A (N - 1)) (hD : RN D (N - 1)) (hnN : n ≤ N)
    (s i j : ℕ) (hs : s < 3) (hi : i < Mn N) (hj : j < Mn N) :
    |G A D N s i j| ≤ (Hn N : ℤ) := by
  have hU : ∀ k < Mn N, RN (ev A D (Ub N k)) ((3 * N ^ 3) ^ (N - 1)) := by
    intro k hk
    obtain ⟨i', hi', j', he⟩ := Ub_mem N hlen k hk
    rw [he]
    refine RN.mono (probes_RN N hN A D hA hD i' hi' _) ?_
    exact Nat.pow_le_pow_right (by positivity) (by omega)
  have hW : RN (Wm A D s) (N - 1) := by
    unfold Wm
    match s, hs with
    | 0, _ => exact RN.mono RN.one (by omega)
    | 1, _ => exact hA
    | 2, _ => exact hD
  unfold G
  have := sandwich_le (hU i hi) (hU j hj) hW
  refine this.trans ?_
  unfold Hn
  push_cast
  have h1 : (n : ℤ) * ((N - 1 : ℕ) : ℤ) ≤ (N : ℤ) * N := by
    have : ((N - 1 : ℕ) : ℤ) ≤ N := by omega
    have : (n : ℤ) ≤ N := by exact_mod_cast hnN
    nlinarith [Int.natCast_nonneg n, Int.natCast_nonneg (N - 1)]
  have h2 : (0 : ℤ) ≤ ((3 * (N : ℤ) ^ 3) ^ (N - 1)) * ((3 * (N : ℤ) ^ 3) ^ (N - 1)) := by positivity
  calc (n : ℤ) * ((N - 1 : ℕ) : ℤ) * ((3 * (N : ℤ) ^ 3) ^ (N - 1)) * ((3 * (N : ℤ) ^ 3) ^ (N - 1))
      = ((n : ℤ) * ((N - 1 : ℕ) : ℤ)) * (((3 * (N : ℤ) ^ 3) ^ (N - 1)) * ((3 * (N : ℤ) ^ 3) ^ (N - 1))) := by ring
    _ ≤ ((N : ℤ) * N) * (((3 * (N : ℤ) ^ 3) ^ (N - 1)) * ((3 * (N : ℤ) ^ 3) ^ (N - 1))) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = (N : ℤ) ^ 2 * ((3 * (N : ℤ) ^ 3) ^ (N - 1)) ^ 2 := by ring

end

end
end UniformADProbes.Trace.Dev.GoalTr4
end

section
/-! Trees: norms of the matrices, real Gram data, moments of a pointed equivalence. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalTr5
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningAdj UniformADProbes.Trace.Dev.Dist
  UniformADProbes.Trace.Dev.GoalAlg UniformADProbes.Trace.Dev.GoalTr2 UniformADProbes.Trace.Dev.GoalNB
  UniformADProbes.Trace.Dev.GoalTr4 Matrix
noncomputable section

section tree
open scoped Classical
variable {n : ℕ} (T : SimpleGraph (Fin n))

lemma adj_symm : (adjacency T)ᵀ = adjacency T := by
  ext i j
  simp only [Matrix.transpose_apply, adj_apply]
  simp [T.adj_comm]

lemma deg_symm : (degreeMatrix T)ᵀ = degreeMatrix T := by
  unfold degreeMatrix
  exact Matrix.diagonal_transpose _

lemma deg_le (i : Fin n) : (Finset.univ.filter (fun w => T.Adj i w)).card ≤ n - 1 := by
  have : (Finset.univ.filter (fun w => T.Adj i w)) ⊆ Finset.univ.erase i := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact (T.ne_of_adj hw).symm
  calc _ ≤ (Finset.univ.erase i).card := Finset.card_le_card this
    _ = n - 1 := by simp

lemma RN_adj : RN (adjacency T) (n - 1) := by
  intro i
  have : ∑ j, |adjacency T i j| = ((Finset.univ.filter (fun w => T.Adj i w)).card : ℤ) := by
    simp only [adj_apply]
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [this]
  exact_mod_cast deg_le T i

lemma RN_deg : RN (degreeMatrix T) (n - 1) := by
  intro i
  have : ∑ j, |degreeMatrix T i j| = ((Finset.univ.filter (fun w => T.Adj i w)).card : ℤ) := by
    rw [Finset.sum_eq_single i]
    · rw [deg_eq]; simp
    · intro j _ hj
      rw [D_apply]; simp [Ne.symm hj]
    · simp
  rw [this]
  exact_mod_cast deg_le T i

end tree

section real
variable {n : ℕ}

lemma real_eq (A : Matrix (Fin n) (Fin n) ℤ) :
    realMatrix A = (Int.castRingHom ℝ).mapMatrix A := by
  ext i j; simp [realMatrix]

lemma gram_real (P W Q : Matrix (Fin n) (Fin n) ℤ) :
    dot ((P.map (Int.cast : ℤ → ℝ)).mulVec (ones n))
      ((W.map (Int.cast : ℤ → ℝ)).mulVec ((Q.map (Int.cast : ℤ → ℝ)).mulVec (ones n))) =
      ((tot (Pᵀ * W * Q) : ℤ) : ℝ) := by
  rw [tot_sandwich]
  push_cast
  simp only [dot, ones, Matrix.mulVec, dotProduct, Matrix.map_apply, mul_one, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [mul_assoc]

lemma gramData_eq (N : ℕ) (A D : Matrix (Fin n) (Fin n) ℤ)
    (s : Fin 3) (i j : Fin (probeList N).length) :
    gramData (realMatrix A) (realMatrix D) (ones n) (probeList N) s i j =
      ((G A D N s.val i.val j.val : ℤ) : ℝ) := by
  have hUi : (probeList N)[i] = Ub N i.val := by unfold Ub; simp
  have hUj : (probeList N)[j] = Ub N j.val := by unfold Ub; simp
  have hp : ∀ p, polyEval (realMatrix A) (realMatrix D) p = (polyEval A D p).map (Int.cast : ℤ → ℝ) := by
    intro p
    rw [real_eq, real_eq, ← polyEval_map]
    ext a b
    simp [RingHom.mapMatrix_apply]
  have hX : (if s.val = 0 then (1 : Matrix (Fin n) (Fin n) ℝ) else if s.val = 1 then realMatrix A
      else realMatrix D) = (Wm A D s.val).map (Int.cast : ℤ → ℝ) := by
    fin_cases s <;> simp [Wm, realMatrix]
  unfold gramData
  simp only []
  rw [hUi, hUj, hp, hp, hX, gram_real]
  unfold G
  rw [polyEval_eq_ev, polyEval_eq_ev]

end real

section pointed

lemma moments_of_pointed {n m : ℕ} (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (H' K' : Matrix (Fin m) (Fin m) ℝ) (v' : Fin m → ℝ)
    (hP : PointedEquivalent H K v H' K' v') (w : Word) :
    dot v ((wordEval H K w).mulVec v) = dot v' ((wordEval H' K' w).mulVec v') := by
  obtain ⟨e, hiso, ⟨hv, hv', hev⟩, hint⟩ := hP
  let cm : Word → cyclicModule H K v := fun w =>
    ⟨(wordEval H K w).mulVec v, Submodule.subset_span ⟨w, rfl⟩⟩
  let cm' : Word → cyclicModule H' K' v' := fun w =>
    ⟨(wordEval H' K' w).mulVec v', Submodule.subset_span ⟨w, rfl⟩⟩
  have h1 : cm 1 = ⟨v, hv⟩ := by
    apply Subtype.ext
    simp [cm, wordEval]
  have h1' : cm' 1 = ⟨v', hv'⟩ := by
    apply Subtype.ext
    simp [cm', wordEval]
  have key : ∀ l : List Bool, e (cm (FreeMonoid.ofList l)) = cm' (FreeMonoid.ofList l) := by
    intro l
    induction l with
    | nil =>
      have : FreeMonoid.ofList ([] : List Bool) = 1 := rfl
      rw [this, h1, h1', hev]
    | cons a l ih =>
      obtain ⟨hH, hK, e1, e2⟩ := hint (cm (FreeMonoid.ofList l))
      apply Subtype.ext
      cases a
      · have c1 : cm (FreeMonoid.ofList (false :: l)) =
            ⟨H.mulVec (cm (FreeMonoid.ofList l)).val, hH⟩ := by
          apply Subtype.ext
          simp [cm, wordEval, Matrix.mulVec_mulVec]
        rw [c1, e1, ih]
        simp [cm', wordEval, Matrix.mulVec_mulVec]
      · have c1 : cm (FreeMonoid.ofList (true :: l)) =
            ⟨K.mulVec (cm (FreeMonoid.ofList l)).val, hK⟩ := by
          apply Subtype.ext
          simp [cm, wordEval, Matrix.mulVec_mulVec]
        rw [c1, e2, ih]
        simp [cm', wordEval, Matrix.mulVec_mulVec]
  have hw : e (cm w) = cm' w := by
    have := key w.toList
    simpa using this
  have := hiso (cm 1) (cm w)
  rw [hw, h1, hev] at this
  have e2 : (cm w).val = (wordEval H K w).mulVec v := rfl
  have e3 : (cm' w).val = (wordEval H' K' w).mulVec v' := rfl
  rw [← e2, ← e3]
  simp only [] at this
  exact this.symm

end pointed

end
end UniformADProbes.Trace.Dev.GoalTr5
end

section
/-! The trace equivalence: equality of the packed traces iff isomorphism. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.GoalTr6
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningAdj UniformADProbes.Trace.Dev.Dist
  UniformADProbes.Trace.Dev.GoalAlg UniformADProbes.Trace.Dev.GoalTr2 UniformADProbes.Trace.Dev.GoalNB
  UniformADProbes.Trace.Dev.GoalTr3 UniformADProbes.Trace.Dev.GoalTr4 UniformADProbes.Trace.Dev.GoalTr5
  Matrix
noncomputable section

section iso
open scoped Classical

lemma iso_trace {n m : ℕ} (T : SimpleGraph (Fin n)) (T' : SimpleGraph (Fin m)) (φ : T ≃g T')
    (p : NCPoly) :
    Matrix.trace (polyEval (adjacency T) (degreeMatrix T) p) =
      Matrix.trace (polyEval (adjacency T') (degreeMatrix T') p) := by
  have hnm : n = m := by simpa using Fintype.card_congr φ.toEquiv
  subst hnm
  set σ := φ.toEquiv with hσ
  let ψ : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) ℤ :=
    (Matrix.reindexAlgEquiv ℤ ℤ σ).toAlgHom.toRingHom
  have hψ : ∀ M, ψ M = M.submatrix σ.symm σ.symm := by
    intro M; rfl
  have hA : ψ (adjacency T) = adjacency T' := by
    ext i j
    rw [hψ]
    simp only [Matrix.submatrix_apply, adj_apply]
    have : T'.Adj i j ↔ T.Adj (σ.symm i) (σ.symm j) := by
      rw [← φ.map_adj_iff]
      have e1 : φ (σ.symm i) = i := φ.apply_symm_apply i
      have e2 : φ (σ.symm j) = j := φ.apply_symm_apply j
      rw [e1, e2]
    simp [this]
  have hD : ψ (degreeMatrix T) = degreeMatrix T' := by
    ext i j
    rw [hψ]
    simp only [Matrix.submatrix_apply, D_apply]
    have hij : σ.symm i = σ.symm j ↔ i = j := σ.symm.injective.eq_iff
    simp only [hij]
    split_ifs with h
    · subst h
      congr 1
      refine Finset.card_equiv σ ?_
      intro w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← φ.map_adj_iff]
      have e1 : φ (σ.symm i) = i := φ.apply_symm_apply i
      rw [e1]
      rfl
    · rfl
  rw [← hA, ← hD, ← polyEval_map ψ]
  rw [hψ]
  simp [Matrix.trace, Matrix.diag]
  exact (Equiv.sum_comp σ.symm (fun i => polyEval (adjacency T) (degreeMatrix T) p i i)).symm

end iso

section fwd
open scoped Classical

lemma tree_pos {n : ℕ} {T : SimpleGraph (Fin n)} (hT : T.IsTree) : 1 ≤ n := by
  obtain ⟨i⟩ := hT.isConnected.nonempty
  exact i.pos

lemma head_probe (N : ℕ) (hN : 1 ≤ N) : (probeList N).head? = some 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  simp [probeList, probeIndices, List.range_succ_eq_map, probes]

lemma specdiam {n : ℕ} (T : SimpleGraph (Fin n)) (hn : 1 ≤ n) (N : ℕ) (hnN : n ≤ N) :
    spectralDiameter (realMatrix (degreeMatrix T)) ≤ (N : ℝ) - 1 := by
  have hdiag : realMatrix (degreeMatrix T) =
      Matrix.diagonal (fun i => ((degreeMatrix T i i : ℤ) : ℝ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [realMatrix]
    · simp [realMatrix, D_apply, h, Matrix.diagonal_apply]
  have hrange : spectrum ℝ (realMatrix (degreeMatrix T)) =
      Set.range (fun i => ((degreeMatrix T i i : ℤ) : ℝ)) := by
    rw [hdiag, spectrum_diagonal]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold spectralDiameter
  rw [hrange]
  have hb : ∀ i, ((degreeMatrix T i i : ℤ) : ℝ) ≤ (N : ℝ) - 1 := by
    intro i
    rw [deg_eq]
    have := deg_le T i
    have h1 : ((Finset.univ.filter (fun w => T.Adj i w)).card : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn]; simp
    have h3 : (n : ℝ) ≤ N := by exact_mod_cast hnN
    push_cast
    linarith
  have hsup : sSup (Set.range (fun i => ((degreeMatrix T i i : ℤ) : ℝ))) ≤ (N : ℝ) - 1 :=
    csSup_le (Set.range_nonempty _) (by rintro _ ⟨i, rfl⟩; exact hb i)
  have hinf : 0 ≤ sInf (Set.range (fun i => ((degreeMatrix T i i : ℤ) : ℝ))) := by
    refine le_csInf (Set.range_nonempty _) ?_
    rintro _ ⟨i, rfl⟩
    show (0 : ℝ) ≤ ((degreeMatrix T i i : ℤ) : ℝ)
    rw [deg_eq]; positivity
  linarith

lemma tree_data {n : ℕ} (N : ℕ) (hN : 2 ≤ N) (hnN : n ≤ N) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    (adjacency T)ᵀ = adjacency T ∧ (degreeMatrix T)ᵀ = degreeMatrix T ∧
    RN (adjacency T) (N - 1) ∧ RN (degreeMatrix T) (N - 1) ∧
    ev (adjacency T) (degreeMatrix T) (distanceSum N) = Oc := by
  refine ⟨adj_symm T, deg_symm T, ?_, ?_, ?_⟩
  · exact RN.mono (RN_adj T) (by omega)
  · exact RN.mono (RN_deg T) (by omega)
  · have := (UniformADProbes.Trace.distance_polynomials n T hT).2.1 N hnN
    rw [← polyEval_eq_ev]
    exact this

lemma gram_eq_of_trace_eq (N : ℕ) (hN : 2 ≤ N) (hlen : (probeList N).length = Mn N)
    {n m : ℕ} (hn : n ≤ N) (hm : m ≤ N) (T : SimpleGraph (Fin n)) (T' : SimpleGraph (Fin m))
    (hT : T.IsTree) (hT' : T'.IsTree)
    (h : Matrix.trace (polyEval (adjacency T) (degreeMatrix T) (packedPoly N)) =
      Matrix.trace (polyEval (adjacency T') (degreeMatrix T') (packedPoly N))) :
    ∀ s < 3, ∀ i < Mn N, ∀ j < Mn N,
      G (adjacency T) (degreeMatrix T) N s i j = G (adjacency T') (degreeMatrix T') N s i j := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := tree_data N hN hn T hT
  obtain ⟨b1, b2, b3, b4, b5⟩ := tree_data N hN hm T' hT'
  rw [trace_packed _ _ a1 a2 N hN a5, trace_packed _ _ b1 b2 N hN b5] at h
  have h2 := (mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h)
  simp only [bb_eq] at h2
  have hM : 0 < Mn N := by
    unfold Mn
    apply Nat.div_pos _ (by norm_num)
    nlinarith
  exact gram_inj (Mn N) hM (Hn N) (Nat.cast_nonneg _) _ _
    (fun s hs i hi j hj => G_bound N hN hlen _ _ a3 a4 hn s i j hs hi hj)
    (fun s hs i hi j hj => G_bound N hN hlen _ _ b3 b4 hm s i j hs hi hj) h2

lemma real_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (h : Aᵀ = A) : (realMatrix A).IsSymm := by
  unfold Matrix.IsSymm realMatrix
  rw [← Matrix.transpose_map, h]

lemma real_moment {n : ℕ} (A D : Matrix (Fin n) (Fin n) ℤ) (w : Word) :
    dot (ones n) ((wordEval (realMatrix A) (realMatrix D) w).mulVec (ones n)) =
      ((∑ i, ∑ j, wordEval A D w i j : ℤ) : ℝ) := by
  have : wordEval (realMatrix A) (realMatrix D) w = (wordEval A D w).map (Int.cast : ℤ → ℝ) := by
    rw [real_eq, real_eq, ← wordEval_map]
    ext a b
    simp [RingHom.mapMatrix_apply]
  rw [this]
  simp only [dot, ones, Matrix.mulVec, dotProduct, Matrix.map_apply, mul_one, one_mul]
  push_cast
  rfl

theorem forward (N : ℕ) (hN : 2 ≤ N) {n m : ℕ} (hn : n ≤ N) (hm : m ≤ N)
    (T : SimpleGraph (Fin n)) (T' : SimpleGraph (Fin m)) (hT : T.IsTree) (hT' : T'.IsTree)
    (h : Matrix.trace (polyEval (adjacency T) (degreeMatrix T) (packedPoly N)) =
      Matrix.trace (polyEval (adjacency T') (degreeMatrix T') (packedPoly N))) :
    Nonempty (T ≃g T') := by
  have hsp := UniformADProbes.Trace.uniform_spanning_probes N (by omega)
  obtain ⟨-, hlen0, -, -, -, -, -, hspan⟩ := hsp
  have hlen : (probeList N).length = Mn N := hlen0
  have hg := gram_eq_of_trace_eq N hN hlen hn hm T T' hT hT' h
  obtain ⟨a1, a2, a3, a4, a5⟩ := tree_data N hN hn T hT
  obtain ⟨b1, b2, b3, b4, b5⟩ := tree_data N hN hm T' hT'
  have hn1 := tree_pos hT
  have hm1 := tree_pos hT'
  have hH := real_symm _ a1
  have hK := real_symm _ a2
  have hH' := real_symm _ b1
  have hK' := real_symm _ b2
  have hsp1 := hspan n hn1 hn _ _ hH hK (specdiam T hn1 N hn) (ones n)
  have hsp2 := hspan m hm1 hm _ _ hH' hK' (specdiam T' hm1 N hm) (ones m)
  have hgram : gramData (realMatrix (adjacency T)) (realMatrix (degreeMatrix T)) (ones n)
      (probeList N) =
      gramData (realMatrix (adjacency T')) (realMatrix (degreeMatrix T')) (ones m)
      (probeList N) := by
    funext s i j
    rw [gramData_eq, gramData_eq]
    congr 1
    exact_mod_cast hg s.val s.isLt i.val (by rw [← hlen]; exact i.isLt) j.val
      (by rw [← hlen]; exact j.isLt)
  have hP := UniformADProbes.Trace.recover_pointed_representation n m _ _ (ones n) _ _ (ones m)
    hH hK hH' hK' (probeList N) (head_probe N (by omega)) hsp1 hsp2 hgram
  refine UniformADProbes.Trace.principal_moment_reconstruction n m T T' hT hT' ?_
  intro w
  have := moments_of_pointed _ _ _ _ _ _ hP w
  rw [real_moment, real_moment] at this
  exact_mod_cast this

theorem trace_iff (N : ℕ) (hN : 1 ≤ N) (n m : ℕ) (hn : n ≤ N) (hm : m ≤ N)
    (T : SimpleGraph (Fin n)) (T' : SimpleGraph (Fin m)) (hT : T.IsTree) (hT' : T'.IsTree) :
    Nonempty (T ≃g T') ↔
      Matrix.trace (polyEval (adjacency T) (degreeMatrix T) (packedPoly N)) =
        Matrix.trace (polyEval (adjacency T') (degreeMatrix T') (packedPoly N)) := by
  by_cases h2 : 2 ≤ N
  · constructor
    · rintro ⟨φ⟩
      exact iso_trace T T' φ _
    · exact forward N h2 hn hm T T' hT hT'
  · have hN1 : N = 1 := by omega
    subst hN1
    have hn1 : n = 1 := by have := tree_pos hT; omega
    have hm1 : m = 1 := by have := tree_pos hT'; omega
    subst hn1
    subst hm1
    have hp : packedPoly 1 = 1 := by unfold packedPoly; rw [if_pos (by omega)]
    rw [hp]
    constructor
    · intro _
      rw [polyEval_eq_ev, polyEval_eq_ev, map_one, map_one]
    · intro _
      refine ⟨⟨Equiv.refl _, ?_⟩⟩
      intro a b
      have h1 : ¬ T.Adj a b := fun h => T.ne_of_adj h (Subsingleton.elim _ _)
      have h3 : ¬ T'.Adj a b := fun h => T'.ne_of_adj h (Subsingleton.elim _ _)
      simp [h1, h3]

end fwd

end
end UniformADProbes.Trace.Dev.GoalTr6
end

section
/-! The goal: the uniform tree invariant. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.Goal
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.GoalNB
  UniformADProbes.Trace.Dev.GoalProbe UniformADProbes.Trace.Dev.GoalTail1 UniformADProbes.Trace.Dev.GoalMain
  UniformADProbes.Trace.Dev.GoalNum UniformADProbes.Trace.Dev.GoalCostNum UniformADProbes.Trace.Dev.GoalTr5
  UniformADProbes.Trace.Dev.GoalTr6 UniformADProbes.Trace.Dev.GoalBase
noncomputable section

lemma signedBits_le_of (z : ℤ) (b T : ℕ) (hz : |z| ≤ (b : ℤ)) (hT : b.size ≤ T) :
    signedBits z ≤ 1 + max 1 T := by
  unfold signedBits
  have h1 : z.natAbs ≤ b := by
    rw [Int.abs_eq_natAbs] at hz
    exact_mod_cast hz
  have := size_mono h1
  omega

lemma entry_bound (N : ℕ) (hN : 2 ≤ N) (c' : Array Instruction) (out : ℕ)
    (hts : TS N (Tfin N) c') (hout : out < c'.size) :
    (⟨c', out⟩ : Circuit).EntryBound N (100 * N ^ 5 * Nat.clog 2 (N + 1)) := by
  intro n hn T hT
  obtain ⟨a1, a2, a3, a4, a5⟩ := tree_data N hN hn T hT
  have hreg := regs_RN (adjacency T) (degreeMatrix T) (N - 1) a3 a4 c'
  have hcl := clg_pos N (by omega)
  have hK : 1 ≤ N ^ 5 * clg N := Nat.mul_pos (pow_pos (by omega) 5) hcl
  have hNK : N ≤ N ^ 5 * clg N := by
    have h1 : N ≤ N ^ 5 := by
      calc N = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
    exact h1.trans (Nat.le_mul_of_pos_right _ hcl)
  have e100 : 100 * N ^ 5 * Nat.clog 2 (N + 1) = 100 * (N ^ 5 * clg N) := by
    show 100 * N ^ 5 * clg N = _; ring
  have e90 : Tfin N = 90 * (N ^ 5 * clg N) := by show 90 * N ^ 5 * clg N = _; ring
  rw [e100]
  constructor
  · intro r i j
    have hr : (registers (⟨c', out⟩ : Circuit) (adjacency T) (degreeMatrix T))[r] =
        (regs (adjacency T) (degreeMatrix T) c')[r.1]?.getD 0 := by
      show _ = ((registers (⟨c', out⟩ : Circuit) (adjacency T) (degreeMatrix T))[r.1]?).getD 0
      rw [Array.getElem?_eq_getElem r.2]
      rfl
    rw [hr]
    have h1 := (hreg r.1).entry i j
    have h2 := signedBits_le_of _ _ (Tfin N) h1 (hts.2.2.2.2.2 r.1)
    rw [e90] at h2
    omega
  · have hr : outputValue (⟨c', out⟩ : Circuit) (adjacency T) (degreeMatrix T) =
        (regs (adjacency T) (degreeMatrix T) c')[out]?.getD 0 := rfl
    rw [hr]
    have h1 := (hreg out).trace
    have h2 := signedBits_le_of _ (n * nb (N - 1) c' out) (N + Tfin N) h1 (by
      refine (size_mul_le _ _).trans ?_
      have := hts.2.2.2.2.2 out
      have h3 : n.size ≤ n := size_le_self n
      omega)
    rw [e90] at h2
    omega

end
end UniformADProbes.Trace.Dev.Goal

namespace UniformADProbes.Trace
open UniformADProbes.Trace.Dev.Goal UniformADProbes.Trace.Dev.GoalMain UniformADProbes.Trace.Dev.GoalNum
  UniformADProbes.Trace.Dev.GoalCostNum UniformADProbes.Trace.Dev.GoalTr6
  UniformADProbes.Trace.Dev.GoalTr2 UniformADProbes.Trace.Dev.GoalProbe UniformADProbes.Trace.Dev.GoalAlg
  UniformADProbes.Trace.Dev.SpanningCode

theorem chk_uniform_tree_invariant :
    ∀ N : ℕ, 1 ≤ N →
      let C := invariantCircuit N
      C.Valid ∧
      C.denotation = packedPoly N ∧
      adjoint (packedPoly N) = packedPoly N ∧
      C.code.size ≤ 100 * N^2 ∧
      C.DegreeBound (3 * N - 2) ∧
      C.LiteralBound (20 * N * Nat.clog 2 (N + 1)) ∧
      C.EntryBound N (100 * N^5 * Nat.clog 2 (N + 1)) ∧
      constructionCost N ≤ 100000000 * (N + 1)^12 ∧
      (∀ n m : ℕ, n ≤ N → m ≤ N →
        ∀ T : SimpleGraph (Fin n), ∀ T' : SimpleGraph (Fin m),
        T.IsTree → T'.IsTree →
        (Nonempty (T ≃g T') ↔
          Matrix.trace (polyEval (adjacency T) (degreeMatrix T) (packedPoly N)) =
          Matrix.trace (polyEval (adjacency T') (degreeMatrix T') (packedPoly N)))) := by
  intro N hN
  by_cases hN1 : N = 1
  · subst hN1
    have hp : invariantProgram 1 = (0, ⟨#[Instruction.identity], 6⟩) := by rfl
    have hC : invariantCircuit 1 = (⟨#[Instruction.identity], 0⟩ : Circuit) := by
      show (⟨(invariantProgram 1).2.code, (invariantProgram 1).1⟩ : Circuit) = _
      rw [hp]
    intro C
    simp only [C]
    rw [hC]
    have hp1 : packedPoly 1 = 1 := by unfold packedPoly; rw [if_pos (by norm_num)]
    refine ⟨⟨by simp, fun k => ?_⟩, ?_, packed_selfadjoint 1, by simp, ?_, ?_, ?_, ?_,
      fun n m hn hm T T' hT hT' => trace_iff 1 le_rfl n m hn hm T T' hT hT'⟩
    · obtain ⟨k, hk⟩ := k
      have : k = 0 := by simpa using hk
      subst this
      trivial
    · rw [hp1]
      show (registers (⟨#[Instruction.identity], 0⟩ : Circuit) x y)[0]?.getD 0 = 1
      rfl
    · intro i
      have hs : (degrees (⟨#[Instruction.identity], 0⟩ : Circuit)).size = 1 :=
        degs_size #[Instruction.identity]
      have hk : i.1 = 0 := by have := i.2; omega
      obtain ⟨k, hk'⟩ := i
      simp only at hk
      subst hk
      show 0 ≤ 3 * 1 - 2
      omega
    · intro I hI k a h
      simp at hI
      subst hI
      cases h
    · intro n hn T hT
      have hn1 : n = 1 := by have := tree_pos hT; omega
      subst hn1
      have hsz : (registers (⟨#[Instruction.identity], 0⟩ : Circuit) (adjacency T)
          (degreeMatrix T)).size = 1 := regs_size (adjacency T) (degreeMatrix T) #[Instruction.identity]
      have hr : ∀ (k : ℕ) (hk : k < (registers (⟨#[Instruction.identity], 0⟩ : Circuit) (adjacency T)
          (degreeMatrix T)).size), (registers (⟨#[Instruction.identity], 0⟩ : Circuit) (adjacency T)
          (degreeMatrix T))[k] = 1 := by
        intro k hk
        have : k = 0 := by omega
        subst this
        rfl
      constructor
      · intro r i j
        have e : (registers (⟨#[Instruction.identity], 0⟩ : Circuit) (adjacency T)
            (degreeMatrix T))[r] = 1 := hr r.1 r.2
        rw [e]
        have : i = j := Subsingleton.elim _ _
        subst this
        have hc : 1 ≤ Nat.clog 2 2 := Nat.clog_pos (by norm_num) (by norm_num)
        simp [signedBits, Matrix.one_apply]
        omega
      · have : outputValue (⟨#[Instruction.identity], 0⟩ : Circuit) (adjacency T) (degreeMatrix T) = 1 := rfl
        rw [this]
        have hc : 1 ≤ Nat.clog 2 2 := Nat.clog_pos (by norm_num) (by norm_num)
        simp [signedBits]
        omega
    · have : constructionCost 1 = 6 := by
        show (invariantProgram 1).2.cost = 6
        rw [hp]
      rw [this]; norm_num
  · have hN2 : 2 ≤ N := by omega
    obtain ⟨c', out, e1, e2, hcost, hts, hout, hrv⟩ := main_prog N hN2
    have hC : invariantCircuit N = (⟨c', out⟩ : Circuit) := by
      show (⟨(invariantProgram N).2.code, (invariantProgram N).1⟩ : Circuit) = ⟨c', out⟩
      rw [e1, e2]
    intro C
    simp only [C]
    rw [hC]
    refine ⟨⟨hout, fun k => hts.1 k.1 k.2⟩, hrv, packed_selfadjoint N, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hts.2.2.2.2.1
    · intro i
      have h := hts.2.2.1 i.1
      change (degs c')[i.1]?.getD 0 ≤ 3 * N - 2 at h
      have hi : i.1 < (degs c').size := i.2
      rw [Array.getElem?_eq_getElem hi, Option.getD_some] at h
      exact h
    · exact hts.2.1
    · exact entry_bound N hN2 c' out hts hout
    · have : constructionCost N = (invariantProgram N).2.cost := rfl
      rw [this]
      exact hcost.trans (ktot_le N hN2)
    · intro n m hn hm T T' hT hT'
      exact trace_iff N hN n m hn hm T T' hT hT'

end UniformADProbes.Trace
end

theorem solution : type_of% @UniformADProbes.Trace.chk_uniform_tree_invariant := @UniformADProbes.Trace.chk_uniform_tree_invariant
