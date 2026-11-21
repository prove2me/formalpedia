-- Prove2me | solution 1 for ReLUBinaryDepth.ProductTradeoff.Supplement.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T16:22:46.515006+00:00
-- url     : https://prove2.me/submissions/b463a331-422f-4128-8a24-c338b90cca13

import Mathlib
import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Product
import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Supplement_Dyadic
import Definitions.Def_QNatProofs_ThrCircuit

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
/-!
Blueprint for `ReLUBinaryDepth.ProductTradeoff.Supplement.theorem_1_2`
(nonuniform TC⁰ approximation of a bounded Boolean product).

Route: round `θ` to integers, compute the integer product `A(x)` exactly by CRT over the
primes up to a polynomial bound (residue mod `p` = `g^(sum of discrete logs)`, a function of a
polynomial-range weighted sum of input literals), recover the CRT quotient by coarse threshold
gates, and add up the weighted gate outputs mod `2^R` by block sums and carry-lookahead.
Everything is built as threshold *formulas* (`TF`), compiled at the end to a `ThrCircuit`.
-/
/-! ## Threshold formulas -/
/-- Threshold formulas over `n` inputs: a literal `xor b (x j)`, or a gate with `k` children,
each with a negation flag and a multiplicity, firing iff the weighted count of true (possibly
negated) children is at least the threshold. -/
inductive TF (n : ℕ) : Type
  | lit : Fin n → Bool → TF n
  | gate : (k : ℕ) → (Fin k → TF n) → (Fin k → Bool) → (Fin k → ℕ) → ℕ → TF n

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
namespace TF
variable {n : ℕ}
def eval : TF n → (Fin n → Bool) → Bool
  | .lit j b, x => xor b (x j)
  | .gate k c neg w t, x =>
      decide (t ≤ ∑ i : Fin k, w i * (if xor (neg i) ((c i).eval x) then 1 else 0))

def depth : TF n → ℕ
  | .lit _ _ => 0
  | .gate _ c _ _ _ => 1 + Finset.univ.sup fun i => (c i).depth

/-- Gates plus wires (a child of multiplicity `w` is `w` wires); literals cost nothing. -/
def size : TF n → ℕ
  | .lit _ _ => 0
  | .gate _ c _ w _ => 1 + ∑ i, (w i + (c i).size)

end TF
end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
/-- A weighted literal: (formula, negated?, multiplicity). -/
abbrev WL (n : ℕ) := TF n × Bool × ℕ

/-- The contribution of a weighted literal at input `x`. -/
def wval {n : ℕ} (x : Fin n → Bool) (u : WL n) : ℕ :=
  u.2.2 * (if xor u.2.1 (u.1.eval x) then 1 else 0)

/-- The cost (wires plus subformula size) of a weighted literal. -/
def wcost {n : ℕ} (u : WL n) : ℕ := u.2.2 + u.1.size

/-- A gate from a list of weighted literals. -/
def gateL {n : ℕ} (l : List (WL n)) (t : ℕ) : TF n :=
  .gate l.length (fun i => (l.get i).1) (fun i => (l.get i).2.1) (fun i => (l.get i).2.2) t

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartF
open ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
theorem sum_get {α : Type} (l : List α) (f : α → ℕ) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := Fin.sum_univ_fun_getElem l f

theorem eval_gateL {n : ℕ} (l : List (WL n)) (t : ℕ) (x : Fin n → Bool) :
    (gateL l t).eval x = decide (t ≤ (l.map (wval x)).sum) := by
  simp only [gateL, TF.eval]
  rw [← sum_get l (wval x)]
  rfl

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartF
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
/-! ### Part F: formula helpers and compilation to `ThrCircuit` -/
alias eval_gateL := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartF.eval_gateL

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartF
open ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
theorem depth_gateL_le {n : ℕ} (l : List (WL n)) (t D : ℕ) (hD : ∀ u ∈ l, u.1.depth ≤ D) :
    (gateL l t).depth ≤ D + 1 := by
  simp only [gateL, TF.depth]
  have : (Finset.univ.sup fun i : Fin l.length => (l.get i).1.depth) ≤ D :=
    Finset.sup_le fun i _ => hD _ (List.get_mem l i)
  omega

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartF
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
alias depth_gateL_le := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartF.depth_gateL_le

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartF
open ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
theorem size_gateL {n : ℕ} (l : List (WL n)) (t : ℕ) :
    (gateL l t).size = 1 + (l.map wcost).sum := by
  simp only [gateL, TF.size]
  rw [← sum_get l wcost]
  rfl

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartF
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
alias size_gateL := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartF.size_gateL

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartF
open ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
/-! ## Compilation -/
/-- Raw gate: input literals with *relative* gate references (`inr d` = the gate `d` places
back), and a threshold. -/
abbrev RG (n : ℕ) := List ((Fin n ⊕ ℕ) × Bool) × ℕ

/-- Offset of block `i` in a flattened list of blocks. -/
def blk {α : Type} (L : List (List α)) (i : ℕ) : ℕ := (L.take i).flatten.length

def childLit {n : ℕ} : TF n → Bool → ℕ → (Fin n ⊕ ℕ) × Bool
  | .lit j b, ng, _ => (.inl j, xor ng b)
  | .gate _ _ _ _ _, ng, d => (.inr d, ng)

def comp {n : ℕ} : TF n → List (RG n)
  | .lit _ _ => []
  | .gate k c neg w t =>
    (List.ofFn fun i => comp (c i)).flatten ++
      [((List.ofFn fun i : Fin k => List.replicate (w i) (childLit (c i) (neg i)
          ((List.ofFn fun i => comp (c i)).flatten.length
            - blk (List.ofFn fun i => comp (c i)) (i.1 + 1) + 1))).flatten, t)]

theorem comp_gate {n k : ℕ} (c : Fin k → TF n) (neg : Fin k → Bool) (w : Fin k → ℕ) (t : ℕ) :
    comp (.gate k c neg w t) =
    (List.ofFn fun i => comp (c i)).flatten ++
      [((List.ofFn fun i : Fin k => List.replicate (w i) (childLit (c i) (neg i)
          ((List.ofFn fun i => comp (c i)).flatten.length
            - blk (List.ofFn fun i => comp (c i)) (i.1 + 1) + 1))).flatten, t)] := by
  rw [comp]

theorem blk_succ {α : Type} (L : List (List α)) (i : ℕ) (hi : i < L.length) :
    blk L (i + 1) = blk L i + L[i].length := by
  unfold blk
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [List.flatten_append, List.length_append, Option.toList_some, List.flatten_cons,
    List.flatten_nil, List.append_nil]

theorem blk_le {α : Type} (L : List (List α)) (i : ℕ) : blk L i ≤ L.flatten.length := by
  unfold blk
  exact (List.take_sublist i L).flatten.length_le

theorem comp_gate_length {n k : ℕ} (c : Fin k → TF n) (neg : Fin k → Bool) (w : Fin k → ℕ)
    (t : ℕ) : (comp (.gate k c neg w t)).length =
      (List.ofFn fun i => comp (c i)).flatten.length + 1 := by
  rw [comp_gate]; simp

/-! ### Placement -/
def Placed {α : Type} (G : List α) (off : ℕ) (F : List α) : Prop :=
  ∀ j, j < G.length → F[off + j]? = G[j]?

theorem placed_left {α : Type} {A B F : List α} {off : ℕ} (h : Placed (A ++ B) off F) :
    Placed A off F := by
  intro j hj
  rw [h j (by simp; omega), List.getElem?_append_left hj]

theorem placed_right {α : Type} {A B F : List α} {off : ℕ} (h : Placed (A ++ B) off F) :
    Placed B (off + A.length) F := by
  intro j hj
  have := h (A.length + j) (by simp; omega)
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at this
  rw [← this, Nat.add_assoc]

theorem placed_ofFn {α : Type} {k : ℕ} (f : Fin k → List α) (i : Fin k) {off : ℕ} {F : List α}
    (h : Placed (List.ofFn f).flatten off F) :
    Placed (f i) (off + blk (List.ofFn f) i.1) F := by
  have hi : i.1 < (List.ofFn f).length := by simp
  have e : (List.ofFn f) = (List.ofFn f).take i.1 ++ (f i :: (List.ofFn f).drop (i.1 + 1)) := by
    conv_lhs => rw [← List.take_append_drop i.1 (List.ofFn f)]
    rw [List.drop_eq_getElem_cons hi]
    simp
  rw [e, List.flatten_append, List.flatten_cons] at h
  have h2 := placed_left (placed_right h)
  unfold blk
  exact h2

theorem placed_self {α : Type} (F : List α) : Placed F 0 F := by
  intro j _; simp

/-! ### Well-formed raw gate lists -/
def WF {n : ℕ} (F : List (RG n)) : Prop :=
  ∀ i (hi : i < F.length), ∀ l ∈ (F[i]).1, ∀ d, l.1 = Sum.inr d → 1 ≤ d ∧ d ≤ i

theorem WF_nil {n : ℕ} : WF ([] : List (RG n)) := by
  intro i hi; simp at hi

theorem WF_append {n : ℕ} {A B : List (RG n)} (hA : WF A) (hB : WF B) : WF (A ++ B) := by
  intro i hi l hl d hd
  by_cases h : i < A.length
  · rw [List.getElem_append_left h] at hl; exact hA i h l hl d hd
  · rw [List.getElem_append_right (by omega)] at hl
    have := hB (i - A.length) (by simp at hi; omega) l hl d hd
    omega

theorem WF_append_single {n : ℕ} {A : List (RG n)} (g : RG n) (hA : WF A)
    (hg : ∀ l ∈ g.1, ∀ d, l.1 = Sum.inr d → 1 ≤ d ∧ d ≤ A.length) : WF (A ++ [g]) := by
  intro i hi l hl d hd
  by_cases h : i < A.length
  · rw [List.getElem_append_left h] at hl; exact hA i h l hl d hd
  · have hi' : i = A.length := by simp at hi; omega
    subst hi'
    rw [List.getElem_append_right (by omega)] at hl
    simp at hl
    exact hg l hl d hd

theorem WF_flatten {n : ℕ} (L : List (List (RG n))) (h : ∀ G ∈ L, WF G) : WF L.flatten := by
  induction L with
  | nil => exact WF_nil
  | cons G L ih =>
    rw [List.flatten_cons]
    exact WF_append (h G (by simp)) (ih fun G' hG' => h G' (by simp [hG']))

theorem mem_ins {n k : ℕ} {f : Fin k → ℕ} {a : Fin k → (Fin n ⊕ ℕ) × Bool}
    {l : (Fin n ⊕ ℕ) × Bool}
    (h : l ∈ (List.ofFn fun i => List.replicate (f i) (a i)).flatten) : ∃ i, l = a i := by
  simp only [List.mem_flatten, List.mem_ofFn] at h
  obtain ⟨_, ⟨i, rfl⟩, hl⟩ := h
  exact ⟨i, (List.mem_replicate.1 hl).2⟩

theorem WF_comp {n : ℕ} (T : TF n) : WF (comp T) := by
  induction T with
  | lit j b => simp [comp]; exact WF_nil
  | gate k c neg w t ih =>
    rw [comp_gate]
    apply WF_append_single _ (WF_flatten _ ?_)
    · intro l hl d hd
      obtain ⟨i, rfl⟩ := mem_ins hl
      have hs := blk_succ (List.ofFn fun i => comp (c i)) i.1 (by simp)
      have hle := blk_le (List.ofFn fun i => comp (c i)) (i.1 + 1)
      cases hci : c i with
      | lit j b => rw [hci] at hd; simp [childLit] at hd
      | gate k' c' neg' w' t' =>
        rw [hci] at hd
        simp only [childLit, Sum.inr.injEq] at hd
        have hpos : (comp (c i)).length ≥ 1 := by rw [hci, comp_gate_length]; omega
        simp only [List.getElem_ofFn, Fin.eta] at hs

        omega
    · intro G hG
      simp only [List.mem_ofFn] at hG
      obtain ⟨i, rfl⟩ := hG
      exact ih i

/-! ### The circuit of a well-formed raw gate list -/
def toFin {n : ℕ} (i : ℕ) : (s : Fin n ⊕ ℕ) → (∀ d, s = Sum.inr d → 1 ≤ d ∧ d ≤ i) →
    Fin n ⊕ Fin i
  | .inl j, _ => .inl j
  | .inr d, h => .inr ⟨i - d, by have := h d rfl; omega⟩

def toFinAbs {n : ℕ} (N : ℕ) : (s : Fin n ⊕ ℕ) → (∀ m, s = Sum.inr m → m < N) → Fin n ⊕ Fin N
  | .inl j, _ => .inl j
  | .inr m, h => .inr ⟨m, h m rfl⟩

def mkCirc {n R : ℕ} (F : List (RG n)) (hF : WF F)
    (out : Fin R → (Fin n ⊕ Fin F.length) × Bool) : QNatProofs.ThrCircuit n R where
  numGates := F.length
  ins i := (F[i.1]'i.2).1.attach.map fun l => (toFin i.1 l.1.1 (hF i.1 i.2 l.1 l.2), l.1.2)
  thr i := (F[i.1]'i.2).2
  out := out

def gv {n R : ℕ} (Φ : QNatProofs.ThrCircuit n R) (x : Fin n → Bool) (m : ℕ) : Bool :=
  if h : m < Φ.numGates then Φ.gateVal x m h else false

def gd {n R : ℕ} (Φ : QNatProofs.ThrCircuit n R) (m : ℕ) : ℕ :=
  if h : m < Φ.numGates then Φ.gateDepth m h else 0

def srcVal {n R : ℕ} (Φ : QNatProofs.ThrCircuit n R) (x : Fin n → Bool) (i : ℕ) :
    Fin n ⊕ ℕ → Bool
  | .inl j => x j
  | .inr d => gv Φ x (i - d)

def srcDep {n R : ℕ} (Φ : QNatProofs.ThrCircuit n R) (i : ℕ) : Fin n ⊕ ℕ → ℕ
  | .inl _ => 0
  | .inr d => gd Φ (i - d)

theorem gateVal_mk {n R : ℕ} (F : List (RG n)) (hF : WF F)
    (out : Fin R → (Fin n ⊕ Fin F.length) × Bool) (x : Fin n → Bool) (i : ℕ)
    (hi : i < (mkCirc F hF out).numGates) :
    (mkCirc F hF out).gateVal x i hi = decide ((F[i]'hi).2 ≤
      ((F[i]'hi).1.filter fun l => xor l.2 (srcVal (mkCirc F hF out) x i l.1)).length) := by
  rw [QNatProofs.ThrCircuit.gateVal.eq_1]
  congr 2
  show (List.filter _ (((F[i]'hi).1.attach.map fun l =>
    (toFin i l.1.1 (hF i hi l.1 l.2), l.1.2)))).length = _
  rw [List.filter_map, List.length_map, ← List.countP_eq_length_filter,
    ← List.countP_eq_length_filter]
  conv_rhs => rw [← List.countP_attach]
  congr 1
  funext ⟨⟨s, b⟩, hl⟩
  cases s with
  | inl j => rfl
  | inr d =>
    have := hF i hi _ hl d rfl
    simp [toFin, srcVal, gv, show i - d < (mkCirc F hF out).numGates by omega]

theorem foldr_max_le (L : List ℕ) (B : ℕ) (h : ∀ a ∈ L, a ≤ B) : L.foldr max 0 ≤ B := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem gateDepth_mk_le {n R : ℕ} (F : List (RG n)) (hF : WF F)
    (out : Fin R → (Fin n ⊕ Fin F.length) × Bool) (i : ℕ)
    (hi : i < (mkCirc F hF out).numGates) (B : ℕ)
    (h : ∀ l ∈ (F[i]'hi).1, srcDep (mkCirc F hF out) i l.1 ≤ B) :
    (mkCirc F hF out).gateDepth i hi ≤ 1 + B := by
  rw [QNatProofs.ThrCircuit.gateDepth.eq_1]
  refine Nat.add_le_add_left (foldr_max_le _ B ?_) 1
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨l, hl, rfl⟩ := ha
  change l ∈ (F[i]'hi).1.attach.map _ at hl
  rw [List.mem_map] at hl
  obtain ⟨⟨⟨s, b⟩, hm⟩, _, rfl⟩ := hl
  have hB := h _ hm
  cases s with
  | inl j => simp [toFin]
  | inr d =>
    have := hF i hi _ hm d rfl
    simpa [toFin, srcDep, gd, show i - d < (mkCirc F hF out).numGates by omega] using hB

/-! ### Root literals -/
def rootLit {n : ℕ} : TF n → ℕ → (Fin n ⊕ ℕ) × Bool
  | .lit j b, _ => (.inl j, b)
  | .gate k c neg w t, off => (.inr (off + (comp (.gate k c neg w t)).length - 1), false)

def aval {n R : ℕ} (Φ : QNatProofs.ThrCircuit n R) (x : Fin n → Bool)
    (l : (Fin n ⊕ ℕ) × Bool) : Bool :=
  xor l.2 (match l.1 with
    | .inl j => x j
    | .inr m => gv Φ x m)

def adep {n R : ℕ} (Φ : QNatProofs.ThrCircuit n R) : Fin n ⊕ ℕ → ℕ
  | .inl _ => 0
  | .inr m => gd Φ m

theorem childLit_val {n R : ℕ} (Φ : QNatProofs.ThrCircuit n R) (x : Fin n → Bool) (T : TF n)
    (ng : Bool) (P d o : ℕ) (h : (comp T).length ≠ 0 → P - d = o + (comp T).length - 1) :
    xor (childLit T ng d).2 (srcVal Φ x P (childLit T ng d).1) =
      xor ng (aval Φ x (rootLit T o)) := by
  cases T with
  | lit j b => simp [childLit, srcVal, aval, rootLit]
  | gate k c neg w t =>
    have := h (by rw [comp_gate_length]; omega)
    simp only [childLit, srcVal, aval, rootLit]
    rw [this]
    simp

theorem childLit_dep {n R : ℕ} (Φ : QNatProofs.ThrCircuit n R) (T : TF n)
    (ng : Bool) (P d o : ℕ) (h : (comp T).length ≠ 0 → P - d = o + (comp T).length - 1) :
    srcDep Φ P (childLit T ng d).1 = adep Φ (rootLit T o).1 := by
  cases T with
  | lit j b => simp [childLit, srcDep, adep, rootLit]
  | gate k c neg w t =>
    have := h (by rw [comp_gate_length]; omega)
    simp only [childLit, srcDep, adep, rootLit]
    rw [this]

theorem count_rep {α : Type} {k : ℕ} (w : Fin k → ℕ) (a : Fin k → α) (p : α → Bool) :
    (((List.ofFn fun i => List.replicate (w i) (a i)).flatten).filter p).length =
      ∑ i, w i * (if p (a i) then 1 else 0) := by
  rw [List.filter_flatten, List.length_flatten, List.map_ofFn, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp, List.filter_replicate]
  split <;> simp_all

theorem main_inv {n R : ℕ} (F : List (RG n)) (hF : WF F)
    (out : Fin R → (Fin n ⊕ Fin F.length) × Bool) (x : Fin n → Bool) (T : TF n) :
    ∀ off, Placed (comp T) off F →
      aval (mkCirc F hF out) x (rootLit T off) = T.eval x ∧
        adep (mkCirc F hF out) (rootLit T off).1 ≤ T.depth := by
  induction T with
  | lit j b => intro off _; simp [aval, rootLit, adep, TF.eval, TF.depth]
  | gate k c neg w t ih =>
    intro off hpl
    have hS := comp_gate_length c neg w t
    rw [comp_gate] at hpl
    have hch : ∀ i : Fin k, Placed (comp (c i))
        (off + blk (List.ofFn fun i => comp (c i)) i.1) F :=
      fun i => placed_ofFn (fun i => comp (c i)) i (placed_left hpl)
    have hroot := placed_right hpl 0 (by simp)
    rw [Nat.add_zero, List.getElem?_cons_zero] at hroot
    obtain ⟨hP, hFP⟩ := List.getElem?_eq_some_iff.1 hroot
    have hP' : off + (List.ofFn fun i => comp (c i)).flatten.length <
        (mkCirc F hF out).numGates := hP
    have hFP' := hFP
    change (F[off + (List.ofFn fun i => comp (c i)).flatten.length]'hP') = _ at hFP'
    have hci : ∀ i : Fin k, (comp (c i)).length ≠ 0 →
        (off + (List.ofFn fun i => comp (c i)).flatten.length) -
          ((List.ofFn fun i => comp (c i)).flatten.length
            - blk (List.ofFn fun i => comp (c i)) (i.1 + 1) + 1) =
        (off + blk (List.ofFn fun i => comp (c i)) i.1) + (comp (c i)).length - 1 := by
      intro i hne
      have hs := blk_succ (List.ofFn fun i => comp (c i)) i.1 (by simp)
      have hle := blk_le (List.ofFn fun i => comp (c i)) (i.1 + 1)
      simp only [List.getElem_ofFn, Fin.eta] at hs
      omega
    have hidx : off + (comp (TF.gate k c neg w t)).length - 1 =
        off + (List.ofFn fun i => comp (c i)).flatten.length := by omega
    constructor
    · simp only [rootLit, aval, hidx, gv, dif_pos hP', Bool.false_xor]
      rw [gateVal_mk]
      simp only [hFP']
      rw [count_rep]
      simp only [TF.eval]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      rw [childLit_val _ _ (c i) (neg i) _ _ (off + blk (List.ofFn fun i => comp (c i)) i.1)
        (hci i), (ih i _ (hch i)).1]
    · simp only [rootLit, adep, hidx, gd, dif_pos hP', TF.depth]
      apply gateDepth_mk_le
      intro l hl
      simp only [hFP'] at hl
      obtain ⟨i, rfl⟩ := mem_ins hl
      rw [childLit_dep _ (c i) (neg i) _ _ (off + blk (List.ofFn fun i => comp (c i)) i.1)
        (hci i)]
      exact le_trans (ih i _ (hch i)).2
        (Finset.le_sup (f := fun i => (c i).depth) (Finset.mem_univ i))

theorem rootLit_lt {n : ℕ} (T : TF n) (o : ℕ) (F : List (RG n)) (hpl : Placed (comp T) o F)
    (m : ℕ) (h : (rootLit T o).1 = Sum.inr m) : m < F.length := by
  cases T with
  | lit j b => simp [rootLit] at h
  | gate k c neg w t =>
    simp only [rootLit, Sum.inr.injEq] at h
    subst h
    have hS := comp_gate_length c neg w t
    by_contra hc
    have := hpl ((comp (TF.gate k c neg w t)).length - 1) (by omega)
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_getElem (by omega)] at this
    simp at this

theorem toFinAbs_inl {n N : ℕ} (s : Fin n ⊕ ℕ) (h : ∀ m, s = Sum.inr m → m < N) (j : Fin n)
    (e : toFinAbs N s h = Sum.inl j) : s = Sum.inl j := by
  cases s with
  | inl j' => simpa [toFinAbs] using e
  | inr m => simp [toFinAbs] at e

theorem toFinAbs_inr {n N : ℕ} (s : Fin n ⊕ ℕ) (h : ∀ m, s = Sum.inr m → m < N) (i : Fin N)
    (e : toFinAbs N s h = Sum.inr i) : s = Sum.inr i.1 := by
  cases s with
  | inl j' => simp [toFinAbs] at e
  | inr m => simp only [toFinAbs, Sum.inr.injEq] at e; rw [← e]

/-! ### Size -/
def rsize {n : ℕ} (G : List (RG n)) : ℕ := G.length + (G.map fun g => g.1.length).sum

theorem rsize_append {n : ℕ} (A B : List (RG n)) : rsize (A ++ B) = rsize A + rsize B := by
  simp [rsize]; omega

theorem rsize_flatten {n : ℕ} (L : List (List (RG n))) : rsize L.flatten = (L.map rsize).sum := by
  induction L with
  | nil => simp [rsize]
  | cons G L ih => rw [List.flatten_cons, rsize_append, ih]; simp

theorem rsize_comp {n : ℕ} (T : TF n) : rsize (comp T) = T.size := by
  induction T with
  | lit j b => simp [comp, rsize, TF.size]
  | gate k c neg w t ih =>
    rw [comp_gate, rsize_append, rsize_flatten, List.map_ofFn, List.sum_ofFn, TF.size,
      Finset.sum_add_distrib]
    have : ∀ i, (rsize ∘ fun i => comp (c i)) i = (c i).size := fun i => ih i
    simp only [this]
    simp [rsize, List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp]
    omega

theorem size_mk {n R : ℕ} (F : List (RG n)) (hF : WF F)
    (out : Fin R → (Fin n ⊕ Fin F.length) × Bool) : (mkCirc F hF out).size = rsize F := by
  simp only [QNatProofs.ThrCircuit.size, rsize]
  congr 1
  simp only [mkCirc, List.length_map, List.length_attach]
  exact Fin.sum_univ_fun_getElem F (fun g => g.1.length)

/-- Compile `R` formulas to one threshold circuit with `R` outputs. -/
theorem compile {n R : ℕ} (T : Fin R → TF n) (d : ℕ) (hd : ∀ r, (T r).depth ≤ d) :
    ∃ Φ : QNatProofs.ThrCircuit n R, Φ.depth ≤ d ∧ Φ.size ≤ ∑ r, (T r).size ∧
      ∀ x, Φ.eval x = fun r => (T r).eval x := by
  let L := List.ofFn fun r => comp (T r)
  let F := L.flatten
  have hF : WF F := WF_flatten _ (by
    intro G hG
    simp only [L, List.mem_ofFn] at hG
    obtain ⟨r, rfl⟩ := hG
    exact WF_comp _)
  have hpl : ∀ r : Fin R, Placed (comp (T r)) (0 + blk L r.1) F :=
    fun r => placed_ofFn (fun r => comp (T r)) r (placed_self F)
  have hlt : ∀ r : Fin R, ∀ m, (rootLit (T r) (0 + blk L r.1)).1 = Sum.inr m → m < F.length :=
    fun r m h => rootLit_lt (T r) _ F (hpl r) m h
  let out : Fin R → (Fin n ⊕ Fin F.length) × Bool := fun r =>
    (toFinAbs F.length _ (hlt r), (rootLit (T r) (0 + blk L r.1)).2)
  refine ⟨mkCirc F hF out, ?_, ?_, ?_⟩
  · simp only [QNatProofs.ThrCircuit.depth]
    apply foldr_max_le
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨r, _, rfl⟩ := ha
    have key := (main_inv F hF out (fun _ => false) (T r) _ (hpl r)).2
    split
    · exact Nat.zero_le _
    · rename_i i e
      have e' := toFinAbs_inr _ (hlt r) i e
      rw [e'] at key
      simp only [adep, gd, dif_pos i.isLt] at key
      exact le_trans key (hd r)
  · rw [size_mk, rsize_flatten, List.map_ofFn, List.sum_ofFn]
    exact le_of_eq (Finset.sum_congr rfl fun r _ => rsize_comp (T r))
  · intro x
    funext r
    rw [← (main_inv F hF out x (T r) _ (hpl r)).1]
    simp only [QNatProofs.ThrCircuit.eval, aval]
    congr 1
    split
    · rename_i j e
      have e' := toFinAbs_inl _ (hlt r) j e
      simp only [mkCirc, out] at e ⊢
      rw [e']
    · rename_i i e
      have e' := toFinAbs_inr _ (hlt r) i e
      simp only [mkCirc, out] at e ⊢
      rw [e']
      have hi : i.1 < F.length := i.isLt
      simp only [gv]
      rw [dif_pos hi]

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartF
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
alias compile := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartF.compile

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartS
open ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
theorem sum_indicator (v : ℕ) (L : List ℕ) (hL : L.Nodup) :
    (L.map fun t => if v = t then 1 else 0).sum = if v ∈ L then 1 else 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.sum_cons, ih hL.2]
    by_cases h : v = a
    · subst h; simp [hL.1]
    · simp [h]

theorem sym_fn {n : ℕ} (l : List (WL n)) (D W : ℕ) (g : ℕ → Bool)
    (hD : ∀ u ∈ l, u.1.depth ≤ D) (hW : ∀ x, (l.map (wval x)).sum ≤ W) :
    ∃ T : TF n, T.depth ≤ D + 3 ∧ T.size ≤ (W + 1) * (8 + 2 * (l.map wcost).sum) ∧
      ∀ x, T.eval x = g (l.map (wval x)).sum := by
  set Sl := (l.map wcost).sum with hSl
  let ge : ℕ → TF n := fun t => gateL l t
  let eq : ℕ → TF n := fun t => gateL [(ge t, false, 1), (ge (t + 1), true, 1)] 2
  let L : List ℕ := (List.range (W + 1)).filter g
  let T : TF n := gateL (L.map fun t => (eq t, false, 1)) 1
  have ge_eval : ∀ t x, (ge t).eval x = decide (t ≤ (l.map (wval x)).sum) :=
    fun t x => PartF.eval_gateL l t x
  have eq_eval : ∀ t x, (eq t).eval x = decide ((l.map (wval x)).sum = t) := by
    intro t x
    simp only [eq, PartF.eval_gateL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      wval, ge_eval]
    by_cases h1 : t ≤ (l.map (wval x)).sum <;> by_cases h2 : t + 1 ≤ (l.map (wval x)).sum <;>
      simp [h1, h2] <;> omega
  have ge_depth : ∀ t, (ge t).depth ≤ D + 1 := fun t => PartF.depth_gateL_le l t D hD
  have eq_depth : ∀ t, (eq t).depth ≤ D + 2 := by
    intro t
    apply PartF.depth_gateL_le
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> exact ge_depth _
  have ge_size : ∀ t, (ge t).size = 1 + Sl := fun t => PartF.size_gateL l t
  have eq_size : ∀ t, (eq t).size = 5 + 2 * Sl := by
    intro t
    simp only [eq, PartF.size_gateL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      wcost, ge_size]
    omega
  refine ⟨T, ?_, ?_, ?_⟩
  · apply PartF.depth_gateL_le
    intro u hu
    simp only [List.mem_map] at hu
    obtain ⟨t, _, rfl⟩ := hu
    exact eq_depth t
  · simp only [T, PartF.size_gateL]
    have hc : ∀ u ∈ (L.map fun t => ((eq t, false, 1) : WL n)).map wcost, u ≤ 6 + 2 * Sl := by
      intro u hu
      simp only [List.map_map, List.mem_map] at hu
      obtain ⟨t, _, rfl⟩ := hu
      simp only [Function.comp, wcost, eq_size]
      omega
    have h1 := List.sum_le_card_nsmul _ _ hc
    have hlen : L.length ≤ W + 1 := by
      have := List.length_filter_le g (List.range (W + 1))
      simpa using this
    simp only [List.length_map, smul_eq_mul] at h1
    have h2 : L.length * (6 + 2 * Sl) ≤ (W + 1) * (6 + 2 * Sl) := Nat.mul_le_mul_right _ hlen
    nlinarith
  · intro x
    simp only [T, PartF.eval_gateL, List.map_map]
    have hfun : (wval x ∘ fun t => ((eq t, false, 1) : WL n)) =
        fun t => if (l.map (wval x)).sum = t then 1 else 0 := by
      funext t
      simp only [Function.comp, wval, eq_eval]
      by_cases h : (l.map (wval x)).sum = t <;> simp [h]
    rw [hfun, sum_indicator _ L ((List.nodup_range).filter _)]
    have hV := hW x
    by_cases hg : g (l.map (wval x)).sum = true
    · have : (l.map (wval x)).sum ∈ L := by
        simp only [L, List.mem_filter, List.mem_range]; exact ⟨by omega, hg⟩
      simp [this, hg]
    · have : (l.map (wval x)).sum ∉ L := by
        simp only [L, List.mem_filter, List.mem_range]; exact fun h => hg h.2
      simp only [this, if_false]
      simp at hg ⊢
      exact hg

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartS
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
/-! ### Part S: any function of a polynomial-range weighted sum -/
alias sym_fn := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartS.sym_fn

/-! ### Part A: iterated addition of big-weight signals, bits below `R` -/
/-- The value `∑ W_u [f_u(x)]` of a list of (formula, big weight) pairs. -/
def bigSum {n : ℕ} (l : List (TF n × ℕ)) (x : Fin n → Bool) : ℕ :=
  (l.map fun u => if u.1.eval x then u.2 else 0).sum

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartA
open Finset
/-!
Part A of the q416 `theorem_1_2` Blueprint: iterated addition of big-weight signals
(block sums of base-`2^ℓ` digits, then carry-lookahead on the two resulting addends).
-/
/-! ## Binary addition and digit expansions -/
/-- carry into position `r` of `X + Y`. -/
def cy (X Y r : ℕ) : Bool := decide (2 ^ r ≤ X % 2 ^ r + Y % 2 ^ r)

theorem bit_add (X Y r : ℕ) :
    (X + Y).testBit r = xor (xor (X.testBit r) (Y.testBit r)) (cy X Y r) := by
  have hP : 0 < 2 ^ r := by positivity
  have hX := Nat.mod_add_div X (2 ^ r)
  have hY := Nat.mod_add_div Y (2 ^ r)
  have ha := Nat.mod_lt X hP
  have hb := Nat.mod_lt Y hP
  set a := X % 2 ^ r
  set b := Y % 2 ^ r
  set q1 := X / 2 ^ r
  set q2 := Y / 2 ^ r
  have hsum : (X + Y) / 2 ^ r = (a + b) / 2 ^ r + (q1 + q2) := by
    rw [show X + Y = (a + b) + 2 ^ r * (q1 + q2) by rw [← hX, ← hY]; ring]
    exact Nat.add_mul_div_left _ _ hP
  simp only [Nat.testBit_eq_decide_div_mod_eq, cy]
  rw [hsum]
  change decide (((a + b) / 2 ^ r + (q1 + q2)) % 2 = 1) =
    xor (xor (decide (q1 % 2 = 1)) (decide (q2 % 2 = 1))) (decide (2 ^ r ≤ a + b))
  by_cases hc : 2 ^ r ≤ a + b
  · have : (a + b) / 2 ^ r = 1 := by
      rw [Nat.div_eq_iff hP]; constructor <;> omega
    rw [this]
    rcases Nat.mod_two_eq_zero_or_one q1 with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one q2 with h2 | h2 <;> simp [h1, h2, hc] <;> omega
  · have : (a + b) / 2 ^ r = 0 := Nat.div_eq_of_lt (by omega)
    rw [this]
    rcases Nat.mod_two_eq_zero_or_one q1 with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one q2 with h2 | h2 <;> simp [h1, h2, hc] <;> omega

theorem cy_succ (X Y r : ℕ) :
    cy X Y (r + 1) = ((X.testBit r && Y.testBit r) || ((X.testBit r || Y.testBit r) && cy X Y r)) := by
  have hP : 0 < 2 ^ r := by positivity
  have h1 : X % 2 ^ (r + 1) = X % 2 ^ r + 2 ^ r * (X / 2 ^ r % 2) := Nat.mod_pow_succ
  have h2 : Y % 2 ^ (r + 1) = Y % 2 ^ r + 2 ^ r * (Y / 2 ^ r % 2) := Nat.mod_pow_succ
  have ha := Nat.mod_lt X hP
  have hb := Nat.mod_lt Y hP
  simp only [cy, Nat.testBit_eq_decide_div_mod_eq]
  rw [h1, h2, pow_succ]
  set P := 2 ^ r
  rcases Nat.mod_two_eq_zero_or_one (X / P) with e1 | e1 <;>
    rcases Nat.mod_two_eq_zero_or_one (Y / P) with e2 | e2 <;> rw [e1, e2] <;>
    by_cases hc : P ≤ X % P + Y % P <;> simp [hc] <;> omega

theorem cy_iff (X Y : ℕ) (xb yb : ℕ → Bool) (r : ℕ)
    (hxy : ∀ j < r, X.testBit j = xb j ∧ Y.testBit j = yb j) :
    cy X Y r = true ↔ ∃ j < r, (xb j && yb j) = true ∧
      ∀ k, j < k → k < r → (xb k || yb k) = true := by
  induction r with
  | zero => simp [cy, Nat.mod_one]
  | succ r ih =>
    rw [cy_succ, (hxy r (by omega)).1, (hxy r (by omega)).2]
    have ih' := ih (fun j hj => hxy j (by omega))
    constructor
    · intro h
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨hp, hc⟩
      · exact ⟨r, by omega, by simpa using h, fun k h1 h2 => by omega⟩
      obtain ⟨j, hj, hg, hk⟩ := ih'.1 hc
      refine ⟨j, by omega, hg, fun k h1 h2 => ?_⟩
      rcases Nat.lt_or_ge k r with h3 | h3
      · exact hk k h1 h3
      · obtain rfl : k = r := by omega
        simpa using hp
    · rintro ⟨j, hj, hg, hk⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true]
      rcases Nat.lt_or_ge j r with h3 | h3
      · right
        exact ⟨by simpa using hk r h3 (by omega),
          ih'.2 ⟨j, h3, hg, fun k h1 h2 => hk k h1 (by omega)⟩⟩
      · obtain rfl : j = r := by omega
        left; simpa using hg

theorem digit_sum_lt (B : ℕ) (d : ℕ → ℕ) (hd : ∀ β, d β < B) (nb : ℕ) :
    ∑ β ∈ range nb, d β * B ^ β < B ^ nb := by
  induction nb with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, pow_succ]
    have := hd k
    have h2 : d k * B ^ k ≤ (B - 1) * B ^ k := Nat.mul_le_mul_right _ (by omega)
    have h3 : (B - 1) * B ^ k + B ^ k = B ^ k * B := by
      rw [mul_comm (B ^ k) B, ← Nat.succ_mul]; congr 1; omega
    omega

theorem digit_extract (B : ℕ) (d : ℕ → ℕ) (hd : ∀ β, d β < B) (nb γ : ℕ) (hγ : γ < nb) :
    (∑ β ∈ range nb, d β * B ^ β) / B ^ γ % B = d γ := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hd 0)
  induction nb with
  | zero => omega
  | succ k ih =>
    rw [sum_range_succ]
    rcases Nat.lt_or_ge γ k with h | h
    · have e : d k * B ^ k = B ^ γ * (B * (d k * B ^ (k - γ - 1))) := by
        rw [show k = γ + (k - γ - 1) + 1 by omega, pow_succ, pow_add]
        rw [show γ + (k - γ - 1) + 1 - γ - 1 = k - γ - 1 by omega]; ring
      rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
      exact ih h
    · obtain rfl : γ = k := by omega
      rw [mul_comm (d γ), Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt (digit_sum_lt B d hd γ), zero_add, Nat.mod_eq_of_lt (hd γ)]

theorem digit_testBit (ℓ : ℕ) (d : ℕ → ℕ) (hd : ∀ β, d β < 2 ^ ℓ) (nb i : ℕ)
    (hi : i < ℓ * nb) :
    (∑ β ∈ range nb, d β * (2 ^ ℓ) ^ β).testBit i = (d (i / ℓ)).testBit (i % ℓ) := by
  have hℓ : 0 < ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · subst h; simp at hi
    · exact h
  have hγ : i / ℓ < nb := by rw [Nat.div_lt_iff_lt_mul hℓ]; linarith [mul_comm ℓ nb]
  rw [← digit_extract _ d hd nb (i / ℓ) hγ, ← pow_mul, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  simp [Nat.mod_lt _ hℓ, Nat.mod_add_div]

theorem mod_expand (B W nb : ℕ) : W % B ^ nb = ∑ β ∈ range nb, W / B ^ β % B * B ^ β := by
  induction nb with
  | zero => simp [Nat.mod_one]
  | succ k ih => rw [Nat.mod_pow_succ, ih, sum_range_succ, mul_comm (B ^ k)]

/-- block sum of digit `β`. -/
def blk (B β : ℕ) (a : List ℕ) : ℕ := (a.map fun w => w / B ^ β % B).sum

def hiD (B : ℕ) (a : List ℕ) (β : ℕ) : ℕ := if β = 0 then 0 else blk B (β - 1) a / B

def Xn (B nb : ℕ) (a : List ℕ) : ℕ := ∑ β ∈ range nb, blk B β a % B * B ^ β

def Yn (B nb : ℕ) (a : List ℕ) : ℕ := ∑ β ∈ range nb, hiD B a β * B ^ β

theorem sum_mod_blk (B nb : ℕ) (a : List ℕ) :
    a.sum % B ^ nb = (∑ β ∈ range nb, blk B β a * B ^ β) % B ^ nb := by
  induction a with
  | nil => simp [blk]
  | cons w a ih =>
    have e : ∑ β ∈ range nb, blk B β (w :: a) * B ^ β =
        ∑ β ∈ range nb, w / B ^ β % B * B ^ β + ∑ β ∈ range nb, blk B β a * B ^ β := by
      rw [← sum_add_distrib]; refine sum_congr rfl fun β _ => ?_
      simp [blk, add_mul]
    rw [e, List.sum_cons, Nat.add_mod, ih, ← mod_expand, Nat.add_mod_mod]

theorem sum_mod_XY (B k : ℕ) (a : List ℕ) :
    a.sum % B ^ (k + 1) = (Xn B (k + 1) a + Yn B (k + 1) a) % B ^ (k + 1) := by
  rw [sum_mod_blk]
  have e1 : ∑ β ∈ range (k + 1), blk B β a * B ^ β =
      Xn B (k + 1) a + ∑ β ∈ range (k + 1), blk B β a / B * B ^ (β + 1) := by
    rw [Xn, ← sum_add_distrib]; refine sum_congr rfl fun β _ => ?_
    conv_lhs => rw [← Nat.mod_add_div (blk B β a) B]
    ring
  have e2 : Yn B (k + 1) a = ∑ β ∈ range k, blk B β a / B * B ^ (β + 1) := by
    rw [Yn, sum_range_succ']; simp [hiD]
  rw [e1, e2, sum_range_succ, ← add_assoc, Nat.add_mul_mod_self_right]

theorem blk_le (B β : ℕ) (a : List ℕ) (hB : 0 < B) : blk B β a ≤ a.length * (B - 1) := by
  have := List.sum_le_card_nsmul (a.map fun w => w / B ^ β % B) (B - 1) (by
    simp only [List.mem_map]; rintro _ ⟨w, _, rfl⟩; have := Nat.mod_lt (w / B ^ β) hB; omega)
  simpa [blk] using this

theorem hiD_lt (B : ℕ) (a : List ℕ) (hB : 0 < B) (hm : a.length < B) (β : ℕ) : hiD B a β < B := by
  unfold hiD
  split_ifs
  · exact hB
  · rw [Nat.div_lt_iff_lt_mul hB]
    have h1 := blk_le B (β - 1) a hB
    have h2 : a.length * (B - 1) ≤ (B - 1) * (B - 1) := Nat.mul_le_mul_right _ (by omega)
    have h3 : (B - 1) * (B - 1) < B * B := Nat.mul_lt_mul'' (by omega) (by omega)
    omega

/-- The main bit identity. -/
theorem bits_main (a : List ℕ) (ℓ : ℕ) (k r : ℕ) (hr : r < ℓ * (k + 1)) :
    a.sum.testBit r = (Xn (2 ^ ℓ) (k + 1) a + Yn (2 ^ ℓ) (k + 1) a).testBit r := by
  have h := sum_mod_XY (2 ^ ℓ) k a
  rw [← pow_mul] at h
  rw [← Bool.and_true (a.sum.testBit r), ← decide_eq_true (show r < ℓ * (k + 1) from hr),
    Bool.and_comm, ← Nat.testBit_mod_two_pow, h, Nat.testBit_mod_two_pow]
  simp [hr]

theorem Xn_bit (a : List ℕ) (ℓ nb i : ℕ) (hi : i < ℓ * nb) :
    (Xn (2 ^ ℓ) nb a).testBit i = (blk (2 ^ ℓ) (i / ℓ) a % 2 ^ ℓ).testBit (i % ℓ) :=
  digit_testBit ℓ (fun β => blk (2 ^ ℓ) β a % 2 ^ ℓ) (fun β => Nat.mod_lt _ (by positivity)) nb i hi

theorem Yn_bit (a : List ℕ) (ℓ nb i : ℕ) (hm : a.length < 2 ^ ℓ) (hi : i < ℓ * nb) :
    (Yn (2 ^ ℓ) nb a).testBit i = (hiD (2 ^ ℓ) a (i / ℓ)).testBit (i % ℓ) :=
  digit_testBit ℓ (hiD (2 ^ ℓ) a) (hiD_lt _ a (by positivity) hm) nb i hi

/-! ## AND / OR gates -/
def wlit {n : ℕ} (f : TF n) : WL n := (f, false, 1)

def andL {n : ℕ} (fs : List (TF n)) : TF n := gateL (fs.map wlit) fs.length

def orL {n : ℕ} (fs : List (TF n)) : TF n := gateL (fs.map wlit) 1

def ind {n : ℕ} (x : Fin n → Bool) (f : TF n) : ℕ := if f.eval x then 1 else 0

theorem sum_wlit {n : ℕ} (fs : List (TF n)) (x : Fin n → Bool) :
    ((fs.map wlit).map (wval x)).sum = (fs.map (ind x)).sum := by
  simp [List.map_map, Function.comp_def, wval, wlit]; rfl

theorem ind_sum_le {n : ℕ} (fs : List (TF n)) (x : Fin n → Bool) :
    (fs.map (ind x)).sum ≤ fs.length := by
  induction fs with
  | nil => simp
  | cons f fs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ind]; split_ifs <;> omega

theorem eval_andL {n : ℕ} (fs : List (TF n)) (x : Fin n → Bool) :
    (andL fs).eval x = decide (∀ f ∈ fs, f.eval x = true) := by
  rw [andL, T12.eval_gateL, sum_wlit]
  congr 1
  apply propext
  induction fs with
  | nil => simp
  | cons f fs ih =>
    have := ind_sum_le fs x
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.mem_cons, forall_eq_or_imp,
      ind] at ih ⊢
    split_ifs with h
    · rw [← ih]; simp [h]; omega
    · simp [h]; omega

theorem eval_orL {n : ℕ} (fs : List (TF n)) (x : Fin n → Bool) :
    (orL fs).eval x = decide (∃ f ∈ fs, f.eval x = true) := by
  rw [orL, T12.eval_gateL, sum_wlit]
  congr 1
  apply propext
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons, List.sum_cons, List.mem_cons, exists_eq_or_imp, ind] at ih ⊢
    split_ifs with h
    · simp [h]
    · simp [h, ih]

theorem depth_andL {n : ℕ} (fs : List (TF n)) (D : ℕ) (h : ∀ f ∈ fs, f.depth ≤ D) :
    (andL fs).depth ≤ D + 1 :=
  T12.depth_gateL_le _ _ _ (by simpa [wlit] using h)

theorem depth_orL {n : ℕ} (fs : List (TF n)) (D : ℕ) (h : ∀ f ∈ fs, f.depth ≤ D) :
    (orL fs).depth ≤ D + 1 :=
  T12.depth_gateL_le _ _ _ (by simpa [wlit] using h)

theorem cost_wlit_le {n : ℕ} (fs : List (TF n)) (S : ℕ) (h : ∀ f ∈ fs, f.size ≤ S) :
    ((fs.map wlit).map wcost).sum ≤ fs.length * (1 + S) := by
  have := List.sum_le_card_nsmul ((fs.map wlit).map wcost) (1 + S) (by
    simp only [List.map_map, List.mem_map, Function.comp_def]
    rintro _ ⟨f, hf, rfl⟩; have := h f hf; simp [wcost, wlit]; omega)
  simpa using this

theorem size_andL {n : ℕ} (fs : List (TF n)) (S : ℕ) (h : ∀ f ∈ fs, f.size ≤ S) :
    (andL fs).size ≤ 1 + fs.length * (1 + S) := by
  rw [andL, T12.size_gateL]; have := cost_wlit_le fs S h; omega

theorem size_orL {n : ℕ} (fs : List (TF n)) (S : ℕ) (h : ∀ f ∈ fs, f.size ≤ S) :
    (orL fs).size ≤ 1 + fs.length * (1 + S) := by
  rw [orL, T12.size_gateL]; have := cost_wlit_le fs S h; omega

/-! ## Size arithmetic -/
theorem S0_le (m B Sf : ℕ) (hB : B ≤ 2 * (m + 1)) :
    (m * B + 1) * (8 + 2 * (m * B + Sf)) ≤ 42 * ((m + 1) ^ 4 * (Sf + 1)) := by
  have h1 : m * B ≤ 2 * (m + 1) ^ 2 := by
    calc m * B ≤ (m + 1) * (2 * (m + 1)) := Nat.mul_le_mul (by omega) hB
      _ = 2 * (m + 1) ^ 2 := by ring
  have hM : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : m * B + 1 ≤ 3 * (m + 1) ^ 2 := by omega
  have h3 : 8 + 2 * (m * B + Sf) ≤ 14 * ((m + 1) ^ 2 * (Sf + 1)) := by
    have : Sf ≤ (m + 1) ^ 2 * Sf := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  calc (m * B + 1) * (8 + 2 * (m * B + Sf)) ≤ (3 * (m + 1) ^ 2) * (14 * ((m + 1) ^ 2 * (Sf + 1))) :=
        Nat.mul_le_mul h2 h3
    _ = 42 * ((m + 1) ^ 4 * (Sf + 1)) := by ring

theorem final_arith (K R r S0 : ℕ) (hK : 1 ≤ K) (hS : S0 ≤ 42 * K) (hr : r < R) :
    4 * (8 + 2 * (3 + 2 * S0 + (1 + r * (2 + r * (4 + 2 * S0))))) ≤ 10000 * (R + 1) ^ 3 * K := by
  have h1 : r * (2 + r * (4 + 2 * S0)) ≤ R * (2 + R * (4 + 2 * S0)) :=
    Nat.mul_le_mul hr.le (by have := Nat.mul_le_mul_right (4 + 2 * S0) hr.le; omega)
  have h2 : R * (2 + R * (4 + 2 * S0)) ≤ R * (2 + R * (4 + 84 * K)) :=
    Nat.mul_le_mul_left _ (by have := Nat.mul_le_mul_left R (show 4 + 2 * S0 ≤ 4 + 84 * K by omega); omega)
  have h3 : 4 * (8 + 2 * (3 + 2 * 42 * K + (1 + R * (2 + R * (4 + 84 * K))))) ≤
      10000 * (R + 1) ^ 3 * K := by
    have hR : 0 ≤ R := Nat.zero_le _
    nlinarith [Nat.mul_le_mul_left (R * R) hK, Nat.mul_le_mul_left R hK, Nat.zero_le (R * R * K),
      Nat.zero_le (R * R * R * K), Nat.zero_le (R * K)]
  omega

/-! ## Literal lists for the block sums -/
def vals {n : ℕ} (l : List (TF n × ℕ)) (x : Fin n → Bool) : List ℕ :=
  l.map fun u => if u.1.eval x then u.2 else 0

def lits {n : ℕ} (l : List (TF n × ℕ)) (B β : ℕ) : List (WL n) :=
  l.map fun u => (u.1, false, u.2 / B ^ β % B)

theorem vals_length {n : ℕ} (l : List (TF n × ℕ)) (x : Fin n → Bool) :
    (vals l x).length = l.length := by simp [vals]

theorem lits_sum {n : ℕ} (l : List (TF n × ℕ)) (B β : ℕ) (x : Fin n → Bool) :
    ((lits l B β).map (wval x)).sum = blk B β (vals l x) := by
  simp only [lits, vals, blk, List.map_map]
  congr 1
  apply List.map_congr_left
  intro u _
  simp only [Function.comp, wval]
  cases u.1.eval x <;> simp

theorem lits_depth {n : ℕ} (l : List (TF n × ℕ)) (B β D : ℕ) (hD : ∀ u ∈ l, u.1.depth ≤ D) :
    ∀ u ∈ lits l B β, u.1.depth ≤ D := by
  simp only [lits, List.mem_map]
  rintro _ ⟨u, hu, rfl⟩
  exact hD u hu

theorem lits_W {n : ℕ} (l : List (TF n × ℕ)) (B β : ℕ) (hB : 0 < B) (x : Fin n → Bool) :
    ((lits l B β).map (wval x)).sum ≤ l.length * B := by
  rw [lits_sum]
  have := blk_le B β (vals l x) hB
  rw [vals_length] at this
  exact this.trans (Nat.mul_le_mul_left _ (by omega))

theorem lits_cost {n : ℕ} (l : List (TF n × ℕ)) (B β : ℕ) (hB : 0 < B) :
    ((lits l B β).map wcost).sum ≤ l.length * B + (l.map fun u => u.1.size).sum := by
  have e : ((lits l B β).map wcost).sum =
      (l.map fun u => u.2 / B ^ β % B).sum + (l.map fun u => u.1.size).sum := by
    simp only [lits, List.map_map, Function.comp_def, wcost]
    exact List.sum_map_add
  rw [e]
  have := List.sum_le_card_nsmul (l.map fun u => u.2 / B ^ β % B) B (by
    simp only [List.mem_map]; rintro _ ⟨u, _, rfl⟩; exact (Nat.mod_lt _ hB).le)
  simp only [List.length_map, smul_eq_mul] at this
  omega

theorem exists_ell (m : ℕ) : ∃ ℓ : ℕ, 0 < ℓ ∧ m < 2 ^ ℓ ∧ 2 ^ ℓ ≤ 2 * (m + 1) := by
  refine ⟨Nat.log 2 m + 1, by omega, Nat.lt_pow_succ_log_self (by norm_num) m, ?_⟩
  rw [pow_succ]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp h0); omega

theorem iter_add {n : ℕ} (l : List (TF n × ℕ)) (D R : ℕ) (hD : ∀ u ∈ l, u.1.depth ≤ D) :
    ∃ T : Fin R → TF n, (∀ r, (T r).depth ≤ D + 10) ∧
      (∀ r, (T r).size ≤
        10000 * (R + 1) ^ 3 * (l.length + 1) ^ 4 * ((l.map fun u => u.1.size).sum + 1)) ∧
      ∀ x r, (T r).eval x = (bigSum l x).testBit r := by
  obtain ⟨ℓ, hℓ, hmB, hB2⟩ := exists_ell l.length
  have hBpos : 0 < 2 ^ ℓ := by positivity
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = (l.length * 2 ^ ℓ + 1) *
      (8 + 2 * (l.length * 2 ^ ℓ + (l.map fun u => u.1.size).sum)) := ⟨_, rfl⟩
  have hX : ∀ i : ℕ, ∃ T : TF n, T.depth ≤ D + 3 ∧ T.size ≤ S0 ∧
      ∀ x, T.eval x = (blk (2 ^ ℓ) (i / ℓ) (vals l x) % 2 ^ ℓ).testBit (i % ℓ) := by
    intro i
    obtain ⟨T, h1, h2, h3⟩ := T12.sym_fn (lits l (2 ^ ℓ) (i / ℓ)) D (l.length * 2 ^ ℓ)
      (fun s => (s % 2 ^ ℓ).testBit (i % ℓ)) (lits_depth l _ _ D hD) (lits_W l _ _ hBpos)
    refine ⟨T, h1, h2.trans ?_, fun x => by rw [h3, lits_sum]⟩
    have := lits_cost l (2 ^ ℓ) (i / ℓ) hBpos
    rw [hS0]
    exact Nat.mul_le_mul_left _ (by omega)
  have hY : ∀ i : ℕ, ∃ T : TF n, T.depth ≤ D + 3 ∧ T.size ≤ S0 ∧
      ∀ x, T.eval x = (hiD (2 ^ ℓ) (vals l x) (i / ℓ)).testBit (i % ℓ) := by
    intro i
    obtain ⟨T, h1, h2, h3⟩ := T12.sym_fn (lits l (2 ^ ℓ) (i / ℓ - 1)) D (l.length * 2 ^ ℓ)
      (fun s => if i / ℓ = 0 then false else (s / 2 ^ ℓ).testBit (i % ℓ))
      (lits_depth l _ _ D hD) (lits_W l _ _ hBpos)
    refine ⟨T, h1, h2.trans ?_, fun x => ?_⟩
    · have := lits_cost l (2 ^ ℓ) (i / ℓ - 1) hBpos
      rw [hS0]
      exact Nat.mul_le_mul_left _ (by omega)
    · rw [h3, lits_sum, hiD]
      split_ifs <;> simp
  choose Xf hXd hXs hXe using hX
  choose Yf hYd hYs hYe using hY
  obtain ⟨g, hg⟩ : ∃ g : ℕ → TF n, g = fun j => andL [Xf j, Yf j] := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ → TF n, p = fun j => orL [Xf j, Yf j] := ⟨_, rfl⟩
  obtain ⟨term, hterm⟩ : ∃ term : ℕ → ℕ → TF n,
      term = fun j r => andL (g j :: (List.range' (j + 1) (r - j - 1)).map p) := ⟨_, rfl⟩
  obtain ⟨cf, hcf⟩ : ∃ cf : ℕ → TF n,
      cf = fun r => orL ((List.range r).map fun j => term j r) := ⟨_, rfl⟩
  -- depths
  have hgd : ∀ j, (g j).depth ≤ D + 4 := fun j => by
    rw [hg]; exact depth_andL _ _ (by simpa using ⟨hXd j, hYd j⟩)
  have hpd : ∀ j, (p j).depth ≤ D + 4 := fun j => by
    rw [hp]; exact depth_orL _ _ (by simpa using ⟨hXd j, hYd j⟩)
  have htd : ∀ j r, (term j r).depth ≤ D + 5 := fun j r => by
    rw [hterm]
    refine depth_andL _ _ ?_
    simp only [List.mem_cons, List.mem_map]
    rintro f (rfl | ⟨k, _, rfl⟩)
    · exact hgd j
    · exact hpd k
  have hcd : ∀ r, (cf r).depth ≤ D + 6 := fun r => by
    rw [hcf]
    refine depth_orL _ _ ?_
    simp only [List.mem_map]
    rintro f ⟨j, _, rfl⟩
    exact htd j r
  -- sizes
  have hgs : ∀ j, (g j).size ≤ 3 + 2 * S0 := fun j => by
    rw [hg]; dsimp only
    have := size_andL [Xf j, Yf j] S0 (by simpa using ⟨hXs j, hYs j⟩)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hps : ∀ j, (p j).size ≤ 3 + 2 * S0 := fun j => by
    rw [hp]; dsimp only
    have := size_orL [Xf j, Yf j] S0 (by simpa using ⟨hXs j, hYs j⟩)
    simp only [List.length_cons, List.length_nil] at this
    omega
  have hts : ∀ j r, j < r → (term j r).size ≤ 1 + r * (4 + 2 * S0) := fun j r hjr => by
    rw [hterm]; dsimp only
    have := size_andL (g j :: (List.range' (j + 1) (r - j - 1)).map p) (3 + 2 * S0) (by
      simp only [List.mem_cons, List.mem_map]
      rintro f (rfl | ⟨k, _, rfl⟩)
      · exact hgs j
      · exact hps k)
    simp only [List.length_cons, List.length_map, List.length_range'] at this
    have h2 : (r - j - 1 + 1) * (1 + (3 + 2 * S0)) ≤ r * (4 + 2 * S0) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hcs : ∀ r, (cf r).size ≤ 1 + r * (2 + r * (4 + 2 * S0)) := fun r => by
    rw [hcf]; dsimp only
    have := size_orL ((List.range r).map fun j => term j r) (1 + r * (4 + 2 * S0)) (by
      simp only [List.mem_map, List.mem_range]
      rintro f ⟨j, hj, rfl⟩
      exact hts j r hj)
    simp only [List.length_map, List.length_range] at this
    have e : r * (1 + (1 + r * (4 + 2 * S0))) = r * (2 + r * (4 + 2 * S0)) := by ring
    omega
  -- evaluations
  have hge : ∀ j x, (g j).eval x = ((Xf j).eval x && (Yf j).eval x) := fun j x => by
    rw [hg]; simp [eval_andL]
  have hpe : ∀ j x, (p j).eval x = ((Xf j).eval x || (Yf j).eval x) := fun j x => by
    rw [hp]; simp [eval_orL]
  have hce : ∀ r x, (cf r).eval x = true ↔ ∃ j < r, ((Xf j).eval x && (Yf j).eval x) = true ∧
      ∀ k, j < k → k < r → ((Xf k).eval x || (Yf k).eval x) = true := fun r x => by
    rw [hcf, eval_orL, decide_eq_true_iff]
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨f, ⟨j, hj, rfl⟩, hf⟩
      rw [hterm, eval_andL, decide_eq_true_iff] at hf
      refine ⟨j, hj, by rw [← hge]; exact hf _ (by simp), fun k h1 h2 => ?_⟩
      rw [← hpe]
      exact hf _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k, by
        rw [List.mem_range'_1]; omega, rfl⟩))
    · rintro ⟨j, hj, hgj, hk⟩
      refine ⟨_, ⟨j, hj, rfl⟩, ?_⟩
      rw [hterm, eval_andL, decide_eq_true_iff]
      simp only [List.mem_cons, List.mem_map, List.mem_range'_1]
      rintro f (rfl | ⟨k, hk', rfl⟩)
      · rw [hge]; exact hgj
      · rw [hpe]; exact hk k (by omega) (by omega)
  -- outputs
  have hO : ∀ r, ∃ T : TF n, T.depth ≤ D + 10 ∧
      T.size ≤ 4 * (8 + 2 * (3 + 2 * S0 + (1 + r * (2 + r * (4 + 2 * S0))))) ∧
      ∀ x, T.eval x = decide ((ind x (Xf r) + (ind x (Yf r) + ind x (cf r))) % 2 = 1) := by
    intro r
    obtain ⟨T, h1, h2, h3⟩ := T12.sym_fn [wlit (Xf r), wlit (Yf r), wlit (cf r)] (D + 6) 3
      (fun s => decide (s % 2 = 1)) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false, wlit]
        rintro u (rfl | rfl | rfl)
        · have := hXd r; simp only; omega
        · have := hYd r; simp only; omega
        · exact hcd r) (by
        intro x
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wval, wlit]
        split_ifs <;> simp)
    refine ⟨T, by omega, h2.trans ?_, fun x => ?_⟩
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wcost, wlit]
      have := hXs r; have := hYs r; have := hcs r
      omega
    · rw [h3]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, wval, wlit]
      unfold ind
      cases (Xf r).eval x <;> cases (Yf r).eval x <;> cases (cf r).eval x <;> rfl
  choose O hOd hOs hOe using hO
  refine ⟨fun r => O r, fun r => hOd r, fun r => ?_, fun x r => ?_⟩
  · refine (hOs r).trans ?_
    have hK : 1 ≤ (l.length + 1) ^ 4 * ((l.map fun u => u.1.size).sum + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    have := final_arith _ R r S0 hK (by rw [hS0]; exact S0_le _ _ _ hB2) r.2
    simpa [mul_assoc] using this
  · have hr : (r : ℕ) < ℓ * (R + 1) := by nlinarith [r.2]
    have hbits : ∀ j, j ≤ (r : ℕ) →
        (Xn (2 ^ ℓ) (R + 1) (vals l x)).testBit j = (Xf j).eval x ∧
        (Yn (2 ^ ℓ) (R + 1) (vals l x)).testBit j = (Yf j).eval x := by
      intro j hj
      rw [Xn_bit _ _ _ _ (by omega), Yn_bit _ _ _ _ (by rw [vals_length]; exact hmB) (by omega),
        hXe, hYe]
      exact ⟨rfl, rfl⟩
    have hc : cy (Xn (2 ^ ℓ) (R + 1) (vals l x)) (Yn (2 ^ ℓ) (R + 1) (vals l x)) r =
        (cf r).eval x := by
      rw [Bool.eq_iff_iff, hce, cy_iff _ _ (fun j => (Xf j).eval x) (fun j => (Yf j).eval x) r
        (fun j hj => hbits j hj.le)]
    show (O r).eval x = (vals l x).sum.testBit r
    rw [hOe, bits_main (vals l x) ℓ R r hr, bit_add, (hbits r le_rfl).1, (hbits r le_rfl).2, hc]
    unfold ind
    cases (Xf r).eval x <;> cases (Yf r).eval x <;> cases (cf r).eval x <;> rfl

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartA
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
alias iter_add := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartA.iter_add

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartP
open Real
/-!
Part P of the q416 `theorem_1_2` Blueprint: the primorial of `C (B+1)^2` exceeds `2^B`
(Chebyshev's lower bound for `θ`).
-/
/-- The real inequality behind `primorial_large`, with `s = 1024 m`. -/
theorem key_ineq (B : ℕ) :
    (B : ℝ) * log 2 ≤ ((1024 * (B + 1)) ^ 2 : ℕ) * log 2 - log (((1024 * (B + 1)) ^ 2 : ℕ) + 1)
      - 2 * √(((1024 * (B + 1)) ^ 2 : ℕ) : ℝ) * log (((1024 * (B + 1)) ^ 2 : ℕ) : ℝ) := by
  set m : ℝ := (B : ℝ) + 1 with hm
  have hm1 : (1 : ℝ) ≤ m := by rw [hm]; linarith [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have hcast : (((1024 * (B + 1)) ^ 2 : ℕ) : ℝ) = (1024 * m) ^ 2 := by rw [hm]; push_cast; ring
  rw [hcast, Real.sqrt_sq (by positivity)]
  have hs : (0 : ℝ) < 1024 * m := by positivity
  have hlogs : log (1024 * m) = 10 * log 2 + log m := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    congr 1
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  have hlogsq : log ((1024 * m) ^ 2) = 2 * log (1024 * m) := by
    rw [Real.log_pow]; norm_num
  have hlog1 : log ((1024 * m) ^ 2 + 1) ≤ log 2 + 2 * log (1024 * m) := by
    rw [← hlogsq, ← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    nlinarith
  have hlm : log m ≤ m - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlm0 : 0 ≤ log m := Real.log_nonneg hm1
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  rw [hlogsq, hlogs] at *
  have hB : (B : ℝ) = m - 1 := by rw [hm]; ring
  rw [hB]
  have hmlm : m * log m ≤ m * (m - 1) := mul_le_mul_of_nonneg_left hlm (by linarith)
  have hmL : m * log 2 ≤ m * m * log 2 := by
    have : m ≤ m * m := by nlinarith
    nlinarith
  nlinarith

theorem primorial_large : ∃ C : ℕ, 1 ≤ C ∧ ∀ B : ℕ, 2 ^ B ≤ primorial (C * (B + 1) ^ 2) := by
  refine ⟨1024 ^ 2, by norm_num, fun B => ?_⟩
  rw [← mul_pow]
  set n := (1024 * (B + 1)) ^ 2
  have h := (key_ineq B).trans (Chebyshev.theta_ge n)
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at h
  have hpos : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  rw [← Real.log_pow, Real.log_le_log_iff (by positivity) hpos] at h
  exact_mod_cast h

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartP
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
/-! ### Part P: enough small primes -/
alias primorial_large := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartP.primorial_large

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartR
open ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
/-- The weighted literals `[x_i] · u i true + [¬x_i] · u i false`. -/
def litList {n : ℕ} (u : Fin n → Bool → ℕ) : List (WL n) :=
  ((List.finRange n).map fun i =>
    [((TF.lit i false : TF n), false, u i true), ((TF.lit i true : TF n), false, u i false)]).flatten

theorem litList_sum {n : ℕ} (u : Fin n → Bool → ℕ) (x : Fin n → Bool) :
    ((litList u).map (wval x)).sum = ∑ i, u i (x i) := by
  rw [Fin.sum_univ_def, litList, List.map_flatten, List.sum_flatten, List.map_map,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  cases h : x i <;> simp [wval, TF.eval, h]

theorem litList_cost {n : ℕ} (u : Fin n → Bool → ℕ) :
    ((litList u).map wcost).sum = ∑ i, (u i true + u i false) := by
  rw [Fin.sum_univ_def, litList, List.map_flatten, List.sum_flatten, List.map_map,
    List.map_map]
  congr 1

theorem litList_depth {n : ℕ} (u : Fin n → Bool → ℕ) : ∀ v ∈ litList u, v.1.depth ≤ 0 := by
  intro v hv
  simp only [litList, List.mem_flatten, List.mem_map] at hv
  obtain ⟨_, ⟨i, _, rfl⟩, hv⟩ := hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> simp [TF.depth]

theorem residue_indicator {n : ℕ} (p : ℕ) (hp : p.Prime) (a : Fin n → Bool → ℕ) (t : ℕ) :
    ∃ T : TF n, T.depth ≤ 3 ∧ T.size ≤ (n * (n * p + p) + 1) * (8 + 4 * n * (n * p + p)) ∧
      ∀ x, T.eval x = decide ((∏ i, a i (x i)) % p = t) := by
  have := Fact.mk hp
  have hp2 := hp.two_le
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hex : ∀ u : (ZMod p)ˣ, ∃ e, e < p ∧ γ ^ e = u := by
    intro u
    obtain ⟨e, he⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hγ u))
    refine ⟨e % orderOf γ, ?_, by rw [pow_mod_orderOf, he]⟩
    have h1 := Nat.mod_lt e (orderOf_pos γ)
    have h2 := orderOf_le_card_univ (x := γ)
    rw [ZMod.card_units] at h2
    omega
  choose elog helog_lt helog using hex
  let Z := n * p + 1
  let u : Fin n → Bool → ℕ := fun i b =>
    if h : ((a i b : ℕ) : ZMod p) = 0 then Z else elog (Units.mk0 _ h)
  have hu_le : ∀ i b, u i b ≤ n * p + p := by
    intro i b
    simp only [u]
    split
    · omega
    · have := helog_lt (Units.mk0 _ ‹_›); nlinarith
  have hu_nz : ∀ i b (h : ((a i b : ℕ) : ZMod p) ≠ 0),
      u i b < p ∧ (((γ ^ u i b : (ZMod p)ˣ)) : ZMod p) = ((a i b : ℕ) : ZMod p) := by
    intro i b h
    simp only [u, dif_neg h]
    exact ⟨helog_lt _, by rw [helog]; rfl⟩
  have hu_z : ∀ i b, ((a i b : ℕ) : ZMod p) = 0 → u i b = Z := by
    intro i b h
    simp only [u, dif_pos h]
  let ρ : ℕ → ℕ := fun v => if Z ≤ v then 0 else ((γ ^ v : (ZMod p)ˣ) : ZMod p).val
  have key : ∀ x : Fin n → Bool, (∏ i, a i (x i)) % p = ρ (∑ i, u i (x i)) := by
    intro x
    rw [← ZMod.val_natCast, Nat.cast_prod]
    by_cases hz : ∃ i, ((a i (x i) : ℕ) : ZMod p) = 0
    · obtain ⟨i, hi⟩ := hz
      have h1 : Z ≤ ∑ i, u i (x i) := by
        rw [← hu_z i (x i) hi]
        exact Finset.single_le_sum (f := fun i => u i (x i)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      simp only [ρ, if_pos h1]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, ZMod.val_zero]
    · push Not at hz
      have h1 : ∑ i, u i (x i) < Z := by
        have : ∑ i, u i (x i) ≤ ∑ _i : Fin n, (p - 1) :=
          Finset.sum_le_sum fun i _ => by have := (hu_nz i (x i) (hz i)).1; omega
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
        have : n * (p - 1) ≤ n * p := Nat.mul_le_mul_left _ (by omega)
        omega
      simp only [ρ, if_neg (not_le.2 h1)]
      congr 1
      rw [← Finset.prod_pow_eq_pow_sum, Units.coe_prod]
      exact (Finset.prod_congr rfl fun i _ => (hu_nz i (x i) (hz i)).2).symm
  obtain ⟨T, hTd, hTs, hTe⟩ := PartS.sym_fn (litList u) 0 (n * (n * p + p))
    (fun v => decide (ρ v = t)) (litList_depth u) (by
      intro x
      rw [litList_sum]
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hu_le i (x i)
      simpa using this)
  refine ⟨T, by simpa using hTd, ?_, ?_⟩
  · refine le_trans hTs (Nat.mul_le_mul_left _ ?_)
    rw [litList_cost]
    have := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      Nat.add_le_add (hu_le i true) (hu_le i false)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    nlinarith
  · intro x
    rw [hTe x, litList_sum, key x]

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartR
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
/-! ### Part R: indicator of the residue of the product modulo a prime -/
alias residue_indicator := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartR.residue_indicator

/-! ### Part C: CRT bookkeeping -/
/-- The CRT coefficient of `p`: `≡ 1 (mod p)`, `≡ 0` modulo the other primes of `P`. -/
noncomputable def crtCoef (P : Finset ℕ) (p : ℕ) : ℕ :=
  (∏ q ∈ P, q) / p * ((((∏ q ∈ P, q) / p : ℕ) : ZMod p)⁻¹).val

/-- The coarse weight `⌊4|P| c_p t / Q⌋`. -/
noncomputable def crtOmega (P : Finset ℕ) (p t : ℕ) : ℕ :=
  4 * P.card * (crtCoef P p * t) / ∏ q ∈ P, q

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC
open Finset
/-!
Part C of the q416 `theorem_1_2` Blueprint: CRT bookkeeping.
-/
theorem prod_div_eq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (p : ℕ) (hp : p ∈ P) :
    (∏ q ∈ P, q) / p = ∏ q ∈ P.erase p, q := by
  rw [← mul_prod_erase P (fun q => q) hp]
  exact Nat.mul_div_cancel_left _ (hP p hp).pos

theorem coprime_quot (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (p : ℕ) (hp : p ∈ P) :
    Nat.Coprime ((∏ q ∈ P, q) / p) p := by
  rw [prod_div_eq P hP p hp]
  apply Nat.Coprime.prod_left
  intro q hq
  rw [Nat.coprime_primes (hP q (mem_of_mem_erase hq)) (hP p hp)]
  exact ne_of_mem_erase hq

theorem crtCoef_cast_self (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (p : ℕ) (hp : p ∈ P) :
    ((crtCoef P p : ℕ) : ZMod p) = 1 := by
  have : NeZero p := ⟨(hP p hp).ne_zero⟩
  rw [crtCoef, Nat.cast_mul, ZMod.natCast_zmod_val]
  exact ZMod.coe_mul_inv_eq_one _ (coprime_quot P hP p hp)

theorem dvd_crtCoef (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (p q : ℕ) (hp : p ∈ P) (hq : q ∈ P)
    (hne : q ≠ p) : q ∣ crtCoef P p := by
  rw [crtCoef, prod_div_eq P hP p hp]
  exact Dvd.dvd.mul_right (dvd_prod_of_mem _ (mem_erase.2 ⟨hne, hq⟩)) _

theorem crtCoef_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (p : ℕ) (hp : p ∈ P) :
    crtCoef P p ≤ ∏ q ∈ P, q := by
  have : NeZero p := ⟨(hP p hp).ne_zero⟩
  rw [crtCoef]
  calc (∏ q ∈ P, q) / p * ((((∏ q ∈ P, q) / p : ℕ) : ZMod p)⁻¹).val
      ≤ (∏ q ∈ P, q) / p * p := Nat.mul_le_mul_left _ (ZMod.val_lt _).le
    _ ≤ ∏ q ∈ P, q := Nat.div_mul_le_self _ _

theorem crt_sum_modEq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (A p : ℕ) (hp : p ∈ P) :
    ∑ q ∈ P, crtCoef P q * (A % q) ≡ A [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_sum,
    sum_eq_single_of_mem p hp (fun q hq hne => by
      rw [Nat.cast_mul, (ZMod.natCast_eq_zero_iff _ _).2 (dvd_crtCoef P hP q p hq hp (Ne.symm hne)),
        zero_mul])]
  rw [Nat.cast_mul, crtCoef_cast_self P hP p hp, one_mul, ZMod.natCast_mod]

theorem crt_sum_mod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (A : ℕ) :
    (∑ p ∈ P, crtCoef P p * (A % p)) % (∏ p ∈ P, p) = A % ∏ p ∈ P, p := by
  have h : (∑ p ∈ P, crtCoef P p * (A % p)) ≡ A [MOD ∏ p ∈ P, p] := by
    rw [Nat.modEq_iff_dvd, Nat.cast_prod]
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hne
      exact Nat.isCoprime_iff_coprime.2
        ((Nat.coprime_primes (hP p hp) (hP q hq)).2 hne)
    · intro p hp
      exact (Nat.modEq_iff_dvd).1 (crt_sum_modEq P hP A p hp)
  exact h

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
alias crt_sum_mod := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC.crt_sum_mod

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC
open Finset
theorem crt_omega_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (p : ℕ) (hp : p ∈ P) (t : ℕ)
    (ht : t < p) : crtOmega P p t ≤ 4 * P.card * p := by
  rw [crtOmega]
  apply Nat.div_le_of_le_mul
  have h1 := crtCoef_le P hP p hp
  calc 4 * P.card * (crtCoef P p * t) = 4 * P.card * (crtCoef P p * t) := rfl
    _ ≤ 4 * P.card * ((∏ q ∈ P, q) * p) := by gcongr
    _ = (∏ q ∈ P, q) * (4 * P.card * p) := by ring

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
alias crt_omega_le := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC.crt_omega_le

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC
open Finset
theorem crt_quot_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (A : ℕ) :
    (∑ p ∈ P, crtCoef P p * (A % p)) / (∏ p ∈ P, p) ≤ ∑ p ∈ P, p := by
  apply Nat.div_le_of_le_mul
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have h1 := crtCoef_le P hP p hp
  have h2 : A % p ≤ p := (Nat.mod_lt _ (hP p hp).pos).le
  exact Nat.mul_le_mul h1 h2

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
alias crt_quot_le := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC.crt_quot_le

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC
open Finset
theorem crt_threshold (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) (A : ℕ)
    (hA : 2 * A < ∏ p ∈ P, p) (m : ℕ) (hm : 1 ≤ m) :
    m ≤ (∑ p ∈ P, crtCoef P p * (A % p)) / (∏ p ∈ P, p) ↔
      P.card * (4 * m - 1) ≤ ∑ p ∈ P, crtOmega P p (A % p) := by
  set Q := ∏ p ∈ P, p with hQ
  set S := ∑ p ∈ P, crtCoef P p * (A % p) with hS
  set Ω := ∑ p ∈ P, crtOmega P p (A % p) with hΩ
  set s := P.card with hs
  have hQpos : 0 < Q := by omega
  have hspos : 0 < s := card_pos.2 hne
  -- `Q Ω ≤ 4 s S`
  have h1 : Ω * Q ≤ 4 * s * S := by
    rw [hΩ, hS, sum_mul, mul_sum]
    exact sum_le_sum fun p _ => Nat.div_mul_le_self _ _
  -- `4 s S < Q Ω + s Q`
  have h2 : 4 * s * S < Ω * Q + s * Q := by
    have : ∑ p ∈ P, 4 * s * (crtCoef P p * (A % p)) <
        ∑ p ∈ P, (crtOmega P p (A % p) * Q + Q) :=
      sum_lt_sum_of_nonempty hne fun p _ => Nat.lt_div_mul_add hQpos
    rw [sum_add_distrib, ← sum_mul, sum_const, smul_eq_mul, ← mul_sum] at this
    exact this
  have h3 : S % Q = A := by
    rw [hS, hQ, crt_sum_mod P hP A, Nat.mod_eq_of_lt (by omega)]
  have h4 := Nat.div_add_mod S Q
  rw [h3] at h4
  set k := S / Q
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have e : 4 * (m' + 1) - 1 = 4 * m' + 3 := by omega
  rw [e]
  constructor
  · intro hk
    have hkQ : 4 * s * (Q * (m' + 1)) ≤ 4 * s * (Q * k) := by gcongr
    by_contra hlt
    push Not at hlt
    have : Ω * Q + Q ≤ s * (4 * m' + 3) * Q := by
      have := Nat.mul_le_mul_right Q (Nat.succ_le_of_lt hlt); nlinarith
    nlinarith
  · intro hle
    by_contra hk
    push Not at hk
    have hk' : k ≤ m' := by omega
    have : s * (4 * m' + 3) * Q ≤ Ω * Q := Nat.mul_le_mul_right Q hle
    have hkQ : 4 * s * (Q * k) ≤ 4 * s * (Q * m') := by gcongr
    nlinarith

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
alias crt_threshold := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC.crt_threshold

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC
open Finset
theorem mod_pow_recover (S Q R : ℕ) :
    (S + S / Q * (2 ^ R - Q % 2 ^ R)) % 2 ^ R = S % Q % 2 ^ R := by
  have hS := Nat.div_add_mod S Q
  have hQ := Nat.div_add_mod Q (2 ^ R)
  have hr := Nat.mod_lt Q (Nat.two_pow_pos R)
  generalize S / Q = k at *
  generalize Q / 2 ^ R = q at *
  generalize Q % 2 ^ R = r at *
  generalize S % Q = u at *
  generalize 2 ^ R = M at *
  have h : S + k * (M - r) = u + M * (k * q + k) := by
    obtain ⟨d, rfl⟩ : ∃ d, M = r + d := ⟨M - r, by omega⟩
    rw [show r + d - r = d by omega]
    subst hQ hS
    ring
  rw [h, Nat.add_mul_mod_self_left]

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
alias mod_pow_recover := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartC.mod_pow_recover

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartE
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement Finset
/-!
Part E of the q416 `theorem_1_2` Blueprint: rounding error of the integer product and the
binary read-out.
-/
theorem round_le (K G : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h : t ≤ (2 : ℝ) ^ K) :
    ⌊t * (2 : ℝ) ^ G⌋₊ ≤ 2 ^ (K + G) := by
  clear h0
  apply Nat.floor_le_of_le
  push_cast
  rw [pow_add]
  exact mul_le_mul_of_nonneg_right h (by positivity)

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartE
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
/-! ### Part E: rounding and binary read-out -/
alias round_le := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartE.round_le

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartE
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement Finset
/-- Product perturbation bound for factors in `[0, M]`, `1 ≤ M`. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (M ε : ℝ)
    (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ M) (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ M)
    (hfg : ∀ i ∈ s, |f i - g i| ≤ ε) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ s.card * ε * M ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hf' : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ M := fun i hi => hf i (mem_insert_of_mem hi)
    have hg' : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ M := fun i hi => hg i (mem_insert_of_mem hi)
    have hfg' : ∀ i ∈ s, |f i - g i| ≤ ε := fun i hi => hfg i (mem_insert_of_mem hi)
    have IH := ih hf' hg' hfg'
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha]
    have hF0 : 0 ≤ ∏ i ∈ s, f i := prod_nonneg fun i hi => (hf' i hi).1
    have hFM : ∏ i ∈ s, f i ≤ M ^ s.card := by
      rw [← prod_const]; exact prod_le_prod (fun i hi => (hf' i hi).1) fun i hi => (hf' i hi).2
    have ha1 := hfg a (mem_insert_self a s)
    have hga := hg a (mem_insert_self a s)
    have hM0 : (0 : ℝ) ≤ M ^ s.card := by positivity
    have hMk : M ^ s.card ≤ M ^ (s.card + 1) := pow_le_pow_right₀ hM (Nat.le_succ _)
    have key : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        (f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by ring
    rw [key]
    calc |(f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)|
        ≤ |f a - g a| * |∏ i ∈ s, f i| + |g a| * |∏ i ∈ s, f i - ∏ i ∈ s, g i| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ ε * M ^ s.card + M * (s.card * ε * M ^ s.card) := by
          rw [abs_of_nonneg hF0, abs_of_nonneg hga.1]
          gcongr
          · exact hga.2
      _ ≤ ((s.card + 1 : ℕ) : ℝ) * ε * M ^ (s.card + 1) := by
          push_cast
          have : M * (s.card * ε * M ^ s.card) = s.card * ε * M ^ (s.card + 1) := by ring
          rw [this]
          nlinarith [mul_le_mul_of_nonneg_left hMk hε]

theorem round_err (n K N : ℕ) (θ : Fin n → Bool → ℝ)
    (hθ : ∀ i b, 0 ≤ θ i b ∧ θ i b ≤ (2 : ℝ) ^ K) (x : Cube n) :
    |(∏ i, (⌊θ i (x i) * (2 : ℝ) ^ (N + n * K + n)⌋₊ : ℝ)) / (2 : ℝ) ^ (n * (N + n * K + n))
        - productMap θ x| ≤ (2 : ℝ) ^ (-(N : ℤ)) := by
  set G := N + n * K + n with hG
  have hP : (0 : ℝ) < 2 ^ G := by positivity
  have hrw : (∏ i, (⌊θ i (x i) * (2 : ℝ) ^ G⌋₊ : ℝ)) / (2 : ℝ) ^ (n * G) =
      ∏ i, ((⌊θ i (x i) * (2 : ℝ) ^ G⌋₊ : ℝ) / 2 ^ G) := by
    rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin, ← pow_mul, mul_comm G n]
  rw [hrw, productMap]
  have hbound := abs_prod_sub_prod_le (univ : Finset (Fin n))
    (fun i => (⌊θ i (x i) * (2 : ℝ) ^ G⌋₊ : ℝ) / 2 ^ G) (fun i => θ i (x i))
    ((2 : ℝ) ^ K) (1 / 2 ^ G) (one_le_pow₀ (by norm_num)) (by positivity)
    (fun i _ => by
      have h1 := hθ i (x i)
      have hfl : (⌊θ i (x i) * (2 : ℝ) ^ G⌋₊ : ℝ) ≤ θ i (x i) * 2 ^ G :=
        Nat.floor_le (mul_nonneg h1.1 hP.le)
      refine ⟨by positivity, ?_⟩
      rw [div_le_iff₀ hP]
      nlinarith)
    (fun i _ => hθ i (x i))
    (fun i _ => by
      have h1 := hθ i (x i)
      have hfl : (⌊θ i (x i) * (2 : ℝ) ^ G⌋₊ : ℝ) ≤ θ i (x i) * 2 ^ G :=
        Nat.floor_le (mul_nonneg h1.1 hP.le)
      have hfl2 : θ i (x i) * 2 ^ G < (⌊θ i (x i) * (2 : ℝ) ^ G⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      set a := (⌊θ i (x i) * (2 : ℝ) ^ G⌋₊ : ℝ)
      have hq : a / 2 ^ G - θ i (x i) = -((θ i (x i) * 2 ^ G - a) / 2 ^ G) := by
        field_simp; ring
      have hd1 : 0 ≤ (θ i (x i) * 2 ^ G - a) / 2 ^ G := div_nonneg (by linarith) hP.le
      have hd2 : (θ i (x i) * 2 ^ G - a) / 2 ^ G ≤ 1 / 2 ^ G :=
        div_le_div_of_nonneg_right (by linarith) hP.le
      rw [hq, abs_neg, abs_of_nonneg hd1]
      exact hd2)
  refine hbound.trans ?_
  simp only [card_univ, Fintype.card_fin]
  rw [zpow_neg, zpow_natCast, ← pow_mul, hG]
  have hn : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  rw [show K * n = n * K by ring, pow_add, pow_add]
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have h2nK : (0 : ℝ) < 2 ^ (n * K) := by positivity
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hn h2nK.le]

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartE
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
alias round_err := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartE.round_err

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartE
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement Finset
theorem dyadic_bits (F R A : ℕ) (hA : A < 2 ^ R) :
    dyadicValue F (fun r : Fin R => A.testBit r) = (A : ℝ) / (2 : ℝ) ^ F := by
  rw [dyadicValue]
  congr 1
  induction R generalizing A with
  | zero => simp at hA; simp [hA]
  | succ R ih =>
    rw [Fin.sum_univ_succ]
    have hA2 : A / 2 < 2 ^ R := by omega
    have := ih (A / 2) hA2
    simp only [Fin.val_succ, Fin.val_zero, pow_zero, mul_one, pow_succ]
    simp_rw [Nat.testBit_succ] 
    have e : ∀ r : Fin R, bit ((A / 2).testBit r) * ((2 : ℝ) ^ (r : ℕ) * 2) =
        2 * (bit ((A / 2).testBit r) * 2 ^ (r : ℕ)) := fun r => by ring
    simp_rw [e, ← mul_sum, this, Nat.testBit_zero, bit]
    have hm := Nat.mod_add_div A 2
    rcases Nat.mod_two_eq_zero_or_one A with h | h
    · simp [h]
      have : (A : ℝ) = 2 * (A / 2 : ℕ) := by exact_mod_cast (by omega : A = 2 * (A / 2))
      rw [this]
    · simp [h]
      have : (A : ℝ) = 1 + 2 * (A / 2 : ℕ) := by exact_mod_cast (by omega : A = 1 + 2 * (A / 2))
      rw [this]

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartE
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
alias dyadic_bits := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartE.dyadic_bits

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartZ
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
open ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
/-! ### Pairs `(p, t)` with `p ∈ P`, `t < p` -/
/-- All pairs `(p, t)` with `p ∈ P` and `t < p`. -/
noncomputable def pairs (P : Finset ℕ) : List (ℕ × ℕ) :=
  P.toList.flatMap (fun p => (List.range p).map (fun t => (p, t)))

theorem mem_pairs (P : Finset ℕ) (pt : ℕ × ℕ) : pt ∈ pairs P ↔ pt.1 ∈ P ∧ pt.2 < pt.1 := by
  obtain ⟨p, t⟩ := pt
  simp only [pairs, List.mem_flatMap, Finset.mem_toList, List.mem_map, List.mem_range,
    Prod.mk.injEq]
  constructor
  · rintro ⟨q, hq, s, hs, rfl, rfl⟩; exact ⟨hq, hs⟩
  · rintro ⟨hp, ht⟩; exact ⟨p, hp, t, ht, rfl, rfl⟩

theorem sum_range_list (p : ℕ) (f : ℕ → ℕ) :
    ((List.range p).map f).sum = ∑ t ∈ Finset.range p, f t := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe,
    Multiset.sum_coe]

theorem sum_pairs (P : Finset ℕ) (F : ℕ → ℕ → ℕ) :
    ((pairs P).map fun pt => F pt.1 pt.2).sum = ∑ p ∈ P, ∑ t ∈ Finset.range p, F p t := by
  rw [pairs, List.flatMap, List.map_flatten, List.sum_flatten, List.map_map, List.map_map,
    ← Finset.sum_map_toList]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_def, List.map_map]
  exact sum_range_list p _

theorem length_pairs (P : Finset ℕ) : (pairs P).length = ∑ p ∈ P, p := by
  simp [pairs, List.length_flatMap]

theorem sum_pairs_ite (P : Finset ℕ) (hpos : ∀ p ∈ P, 0 < p) (A : ℕ) (g : ℕ → ℕ → ℕ) :
    ((pairs P).map fun pt => if A % pt.1 = pt.2 then g pt.1 pt.2 else 0).sum =
      ∑ p ∈ P, g p (A % p) := by
  rw [sum_pairs P (fun p t => if A % p = t then g p t else 0)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_ite_eq]
  simp [Nat.mod_lt _ (hpos p hp)]

theorem sum_pairs_le (P : Finset ℕ) (F : ℕ → ℕ → ℕ) (b : ℕ)
    (hF : ∀ p ∈ P, ∀ t < p, F p t ≤ b) :
    ((pairs P).map fun pt => F pt.1 pt.2).sum ≤ (∑ p ∈ P, p) * b := by
  rw [sum_pairs, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  calc ∑ t ∈ Finset.range p, F p t ≤ ∑ t ∈ Finset.range p, b :=
        Finset.sum_le_sum fun t ht => hF p hp t (Finset.mem_range.1 ht)
    _ = p * b := by simp

theorem sum_range_ite (Mk k W : ℕ) (hk : k ≤ Mk) :
    ∑ m ∈ Finset.range Mk, (if m + 1 ≤ k then W else 0) = k * W := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Finset.sum_range_add]
  have h1 : ∑ m ∈ Finset.range k, (if m + 1 ≤ k then W else 0) = ∑ m ∈ Finset.range k, W :=
    Finset.sum_congr rfl fun m hm => if_pos (by simp at hm; omega)
  have h2 : ∑ m ∈ Finset.range j, (if k + m + 1 ≤ k then W else 0) = 0 :=
    Finset.sum_eq_zero fun m _ => if_neg (by omega)
  rw [h1, h2]
  simp

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartZ
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartZ
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
open ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
variable {n : ℕ} (P : Finset ℕ) (I : ℕ → ℕ → TF n)
/-! ### The construction -/
/-- The weighted literals of the quotient gates. -/
noncomputable def gList : List (WL n) :=
  (pairs P).map fun pt => (I pt.1 pt.2, false, crtOmega P pt.1 pt.2)

/-- The `m`-th quotient gate: fires iff `m ≤ k(x)`. -/
noncomputable def Gm (m : ℕ) : TF n := gateL (gList P I) (P.card * (4 * m - 1))

/-- The big list fed to `iter_add`. -/
noncomputable def L2 (Mk W : ℕ) : List (TF n × ℕ) :=
  (pairs P).map (fun pt => (I pt.1 pt.2, crtCoef P pt.1 * pt.2)) ++
    (List.range Mk).map (fun m => (Gm P I (m + 1), W))

theorem gList_sum (hpos : ∀ p ∈ P, 0 < p) (x : Fin n → Bool) (A : ℕ)
    (hI : ∀ p ∈ P, ∀ t, (I p t).eval x = decide (A % p = t)) :
    ((gList P I).map (wval x)).sum = ∑ p ∈ P, crtOmega P p (A % p) := by
  rw [← sum_pairs_ite P hpos A (fun p t => crtOmega P p t), gList, List.map_map]
  congr 1
  apply List.map_congr_left
  intro pt hpt
  have hp := ((mem_pairs P pt).1 hpt).1
  simp only [Function.comp_apply, wval, hI _ hp, Bool.false_xor, decide_eq_true_eq]
  split_ifs <;> simp

theorem eval_Gm (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) (x : Fin n → Bool) (A : ℕ)
    (hI : ∀ p ∈ P, ∀ t, (I p t).eval x = decide (A % p = t)) (hA : 2 * A < ∏ p ∈ P, p)
    (m : ℕ) (hm : 1 ≤ m) :
    (Gm P I m).eval x =
      decide (m ≤ (∑ p ∈ P, crtCoef P p * (A % p)) / (∏ p ∈ P, p)) := by
  rw [Gm, T12.eval_gateL, gList_sum P I (fun p hp => (hP p hp).pos) x A hI]
  simp only [decide_eq_decide]
  exact (T12.crt_threshold P hP hne A hA m hm).symm

theorem bigSum_L2 (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) (x : Fin n → Bool) (A : ℕ)
    (hI : ∀ p ∈ P, ∀ t, (I p t).eval x = decide (A % p = t)) (hA : 2 * A < ∏ p ∈ P, p)
    (Mk W : ℕ) (hk : (∑ p ∈ P, crtCoef P p * (A % p)) / (∏ p ∈ P, p) ≤ Mk) :
    bigSum (L2 P I Mk W) x = (∑ p ∈ P, crtCoef P p * (A % p)) +
      (∑ p ∈ P, crtCoef P p * (A % p)) / (∏ p ∈ P, p) * W := by
  have h1 : ((pairs P).map fun pt =>
      if (I pt.1 pt.2).eval x then crtCoef P pt.1 * pt.2 else 0).sum =
      ∑ p ∈ P, crtCoef P p * (A % p) := by
    rw [← sum_pairs_ite P (fun p hp => (hP p hp).pos) A (fun p t => crtCoef P p * t)]
    congr 1
    apply List.map_congr_left
    intro pt hpt
    have hp := ((mem_pairs P pt).1 hpt).1
    simp only [hI _ hp, decide_eq_true_eq]
  have h2 : ((List.range Mk).map fun m => if (Gm P I (m + 1)).eval x then W else 0).sum =
      (∑ p ∈ P, crtCoef P p * (A % p)) / (∏ p ∈ P, p) * W := by
    rw [← sum_range_ite Mk _ W hk, ← sum_range_list]
    congr 1
    apply List.map_congr_left
    intro m _
    simp only [eval_Gm P I hP hne x A hI hA (m + 1) (by omega), decide_eq_true_eq]
  rw [bigSum, L2, List.map_append, List.sum_append, List.map_map, List.map_map]
  exact congrArg₂ (· + ·) h1 h2

theorem depth_Gm (hI3 : ∀ p ∈ P, ∀ t, (I p t).depth ≤ 3) (m : ℕ) : (Gm P I m).depth ≤ 4 := by
  apply T12.depth_gateL_le _ _ 3
  intro u hu
  rw [gList, List.mem_map] at hu
  obtain ⟨pt, hpt, rfl⟩ := hu
  exact hI3 _ ((mem_pairs P pt).1 hpt).1 _

theorem depth_L2 (hI3 : ∀ p ∈ P, ∀ t, (I p t).depth ≤ 3) (Mk W : ℕ) :
    ∀ u ∈ L2 P I Mk W, u.1.depth ≤ 4 := by
  intro u hu
  rw [L2, List.mem_append, List.mem_map, List.mem_map] at hu
  rcases hu with ⟨pt, hpt, rfl⟩ | ⟨m, _, rfl⟩
  · exact (hI3 _ ((mem_pairs P pt).1 hpt).1 _).trans (by norm_num)
  · exact depth_Gm P I hI3 _

theorem size_Gm (w0 SI : ℕ) (hω : ∀ p ∈ P, ∀ t < p, crtOmega P p t ≤ w0)
    (hS : ∀ p ∈ P, ∀ t < p, (I p t).size ≤ SI) (m : ℕ) :
    (Gm P I m).size ≤ 1 + (∑ p ∈ P, p) * (w0 + SI) := by
  rw [Gm, T12.size_gateL, gList, List.map_map]
  have := sum_pairs_le P (fun p t => crtOmega P p t + (I p t).size) (w0 + SI)
    (fun p hp t ht => Nat.add_le_add (hω p hp t ht) (hS p hp t ht))
  exact Nat.add_le_add_left this 1

theorem length_L2 (Mk W : ℕ) : (L2 P I Mk W).length = (∑ p ∈ P, p) + Mk := by
  simp [L2, length_pairs]

theorem sizes_L2 (SI SG : ℕ) (hS : ∀ p ∈ P, ∀ t < p, (I p t).size ≤ SI)
    (hG : ∀ m, (Gm P I m).size ≤ SG) (Mk W : ℕ) :
    ((L2 P I Mk W).map fun u => u.1.size).sum ≤ (∑ p ∈ P, p) * SI + Mk * SG := by
  rw [L2, List.map_append, List.sum_append, List.map_map, List.map_map]
  apply Nat.add_le_add
  · exact sum_pairs_le P (fun p t => (I p t).size) SI hS
  · rw [sum_range_list]
    calc ∑ m ∈ Finset.range Mk, (Gm P I (m + 1)).size ≤ ∑ m ∈ Finset.range Mk, SG :=
          Finset.sum_le_sum fun m _ => hG _
      _ = Mk * SG := by simp

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartZ
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartZ
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
open ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
/-- The constant `c` of the theorem, as a function of the primorial constant `C`. -/
def cst (C : ℕ) : ℕ := 10000 * 81 * 102 * 50 ^ 22 * C ^ 22 + 132

theorem arith (L n C B X Mk SI SG Sf : ℕ) (hL : 1 ≤ L) (hn : n ≤ L) (hC : 1 ≤ C)
    (hB : B ≤ 5 * L ^ 3) (hX : X = C * (B + 2) ^ 2) (hMk : Mk ≤ (X + 1) ^ 2)
    (hSI : SI ≤ (n * (n * X + X) + 1) * (8 + 4 * n * (n * X + X)))
    (hSG : SG ≤ 1 + Mk * (4 * (X + 1) * X + SI)) (hSf : Sf ≤ Mk * SI + Mk * SG) :
    B * (10000 * (B + 1) ^ 3 * ((Mk + Mk) + 1) ^ 4 * (Sf + 1)) ≤ cst C * L ^ cst C := by
  set Z := 50 * (C * L ^ 6) with hZ
  have hL3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ hL
  have hL36 : L ^ 3 ≤ C * L ^ 6 :=
    (Nat.pow_le_pow_right hL (by norm_num)).trans (Nat.le_mul_of_pos_left _ hC)
  have hLL3 : L ≤ L ^ 3 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 3 := Nat.pow_le_pow_right hL (by norm_num)
  have hZ1 : 1 ≤ Z := by omega
  have hX1 : X + 1 ≤ Z := by
    have hB2 : B + 2 ≤ 7 * L ^ 3 := by omega
    have : X ≤ 49 * (C * L ^ 6) := by
      rw [hX]
      calc C * (B + 2) ^ 2 ≤ C * (7 * L ^ 3) ^ 2 := by gcongr
        _ = 49 * (C * L ^ 6) := by ring
    omega
  have hBZ : B + 1 ≤ Z := by omega
  have hnZ : n ≤ Z := by omega
  have hXZ : X ≤ Z := by omega
  have hZ2 : 1 ≤ Z ^ 2 := Nat.one_le_pow _ _ hZ1
  have hZ3 : 1 ≤ Z ^ 3 := Nat.one_le_pow _ _ hZ1
  have hMZ : Mk ≤ Z ^ 2 := hMk.trans (Nat.pow_le_pow_left hX1 2)
  have hY : n * (n * X + X) ≤ 2 * Z ^ 3 := by
    calc n * (n * X + X) ≤ Z * (Z * Z + Z * Z) := by
          gcongr
          exact hXZ.trans (Nat.le_mul_of_pos_left _ hZ1)
      _ = 2 * Z ^ 3 := by ring
  have hSI' : SI ≤ 48 * Z ^ 6 := by
    have e : (n * (n * X + X) + 1) * (8 + 4 * n * (n * X + X)) =
        (n * (n * X + X) + 1) * (8 + 4 * (n * (n * X + X))) := by ring
    rw [e] at hSI
    refine hSI.trans ?_
    calc (n * (n * X + X) + 1) * (8 + 4 * (n * (n * X + X)))
        ≤ (2 * Z ^ 3 + 1) * (8 + 4 * (2 * Z ^ 3)) := by gcongr
      _ ≤ (3 * Z ^ 3) * (16 * Z ^ 3) := by gcongr <;> omega
      _ = 48 * Z ^ 6 := by ring
  have hw : 4 * (X + 1) * X ≤ 4 * Z ^ 2 := by
    calc 4 * (X + 1) * X ≤ 4 * Z * Z := by gcongr
      _ = 4 * Z ^ 2 := by ring
  have hZ48 : Z ^ 4 ≤ Z ^ 8 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have hZ18 : 1 ≤ Z ^ 8 := Nat.one_le_pow _ _ hZ1
  have hSG' : SG ≤ 53 * Z ^ 8 := by
    refine hSG.trans ?_
    calc 1 + Mk * (4 * (X + 1) * X + SI) ≤ 1 + Z ^ 2 * (4 * Z ^ 2 + 48 * Z ^ 6) := by gcongr
      _ = 1 + 4 * Z ^ 4 + 48 * Z ^ 8 := by ring
      _ ≤ 53 * Z ^ 8 := by omega
  have hZ810 : Z ^ 8 ≤ Z ^ 10 := Nat.pow_le_pow_right hZ1 (by norm_num)
  have hZ110 : 1 ≤ Z ^ 10 := Nat.one_le_pow _ _ hZ1
  have hSf' : Sf + 1 ≤ 102 * Z ^ 10 := by
    have : Sf ≤ 48 * Z ^ 8 + 53 * Z ^ 10 := by
      refine hSf.trans ?_
      calc Mk * SI + Mk * SG ≤ Z ^ 2 * (48 * Z ^ 6) + Z ^ 2 * (53 * Z ^ 8) := by gcongr
        _ = 48 * Z ^ 8 + 53 * Z ^ 10 := by ring
    omega
  have hM2 : (Mk + Mk) + 1 ≤ 3 * Z ^ 2 := by omega
  have hBZ' : B ≤ Z := by omega
  calc B * (10000 * (B + 1) ^ 3 * ((Mk + Mk) + 1) ^ 4 * (Sf + 1))
      ≤ Z * (10000 * Z ^ 3 * (3 * Z ^ 2) ^ 4 * (102 * Z ^ 10)) := by gcongr
    _ = (10000 * 81 * 102 * 50 ^ 22 * C ^ 22) * L ^ 132 := by rw [hZ]; ring
    _ ≤ cst C * L ^ cst C := by
      gcongr
      all_goals unfold cst; omega

theorem R_le (L C B : ℕ) (hL : 1 ≤ L) (hB : B ≤ 5 * L ^ 3) : B ≤ cst C * L ^ cst C := by
  calc B ≤ 5 * L ^ 3 := hB
    _ ≤ cst C * L ^ cst C := by
      gcongr
      all_goals unfold cst; omega

/-! ### Assembly -/
theorem prod_le_two_pow {n : ℕ} (a : Fin n → Bool → ℕ) (KG : ℕ) (ha : ∀ i b, a i b ≤ 2 ^ KG)
    (x : Fin n → Bool) : ∏ i, a i (x i) < 2 ^ (n * KG + 1) := by
  have h := Finset.prod_le_pow_card (s := Finset.univ) (f := fun i => a i (x i)) (n := 2 ^ KG)
    (fun i _ => ha i (x i))
  rw [Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm] at h
  exact Nat.lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (by omega))

theorem B_le (n N K : ℕ) :
    n * (K + (N + n * K + n)) + 1 ≤ 5 * (n + N + K + 1) ^ 3 := by
  set L := n + N + K + 1 with hLdef
  have hL : 1 ≤ L := by omega
  have h1 : K + (N + n * K + n) ≤ 4 * L ^ 2 := by
    have : n * K ≤ L ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    have : L ≤ L ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left _ hL
    omega
  calc n * (K + (N + n * K + n)) + 1 ≤ L * (4 * L ^ 2) + L ^ 3 := by
        gcongr
        · omega
        · exact Nat.one_le_pow _ _ hL
    _ = 5 * L ^ 3 := by ring

theorem sum_P_le (X : ℕ) :
    ∑ p ∈ (Finset.range (X + 1)).filter Nat.Prime, p ≤ (X + 1) ^ 2 := by
  calc ∑ p ∈ (Finset.range (X + 1)).filter Nat.Prime, p
      ≤ ∑ p ∈ Finset.range (X + 1), p := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ ∑ p ∈ Finset.range (X + 1), (X + 1) :=
        Finset.sum_le_sum fun p hp => (Finset.mem_range.1 hp).le
    _ = (X + 1) ^ 2 := by simp [sq]

theorem main :
    ∃ d c : ℕ, ∀ (K n N : ℕ), 1 ≤ N → ∀ θ : Fin n → Bool → ℝ,
      (∀ i b, 0 ≤ θ i b ∧ θ i b ≤ (2 : ℝ) ^ K) →
      ∃ (R F : ℕ) (Φ : QNatProofs.ThrCircuit n R),
        Φ.depth ≤ d ∧ Φ.size ≤ c * (n + N + K + 1) ^ c ∧ R ≤ c * (n + N + K + 1) ^ c ∧
        ∀ x : Cube n, |dyadicValue F (Φ.eval x) - productMap θ x| ≤ (2 : ℝ) ^ (-(N : ℤ)) := by
  obtain ⟨C, hC, hprim⟩ := T12.primorial_large
  refine ⟨14, cst C, ?_⟩
  intro K n N _ θ hθ
  set G := N + n * K + n with hG
  set a : Fin n → Bool → ℕ := fun i b => ⌊θ i b * (2 : ℝ) ^ G⌋₊ with ha_def
  have ha : ∀ i b, a i b ≤ 2 ^ (K + G) := fun i b => T12.round_le K G _ (hθ i b).1 (hθ i b).2
  set A : (Fin n → Bool) → ℕ := fun x => ∏ i, a i (x i) with hA_def
  set B := n * (K + G) + 1 with hB_def
  have hAB : ∀ x, A x < 2 ^ B := fun x => prod_le_two_pow a (K + G) ha x
  set X := C * (B + 2) ^ 2 with hX
  set P := (Finset.range (X + 1)).filter Nat.Prime with hP_def
  set Q := ∏ p ∈ P, p with hQ_def
  have hQB : 2 ^ (B + 1) ≤ Q := hprim (B + 1)
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2
  have hPle : ∀ p ∈ P, p ≤ X := fun p hp =>
    Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_filter.1 hp).1)
  have h2A : ∀ x, 2 * A x < Q := fun x => by
    have := hAB x
    rw [pow_succ] at hQB
    omega
  have hne : P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have h1 : Q = 1 := by rw [hQ_def, h, Finset.prod_empty]
    have := h2A (fun _ => false)
    have : 1 ≤ 2 ^ B := Nat.one_le_two_pow
    rw [pow_succ] at hQB
    omega
  -- indicators
  have hIex : ∀ p t : ℕ, ∃ T : TF n, p.Prime → T.depth ≤ 3 ∧
      T.size ≤ (n * (n * p + p) + 1) * (8 + 4 * n * (n * p + p)) ∧
      ∀ x, T.eval x = decide (A x % p = t) := by
    intro p t
    by_cases hp : p.Prime
    · obtain ⟨T, h⟩ := T12.residue_indicator p hp a t
      exact ⟨T, fun _ => h⟩
    · exact ⟨gateL [] 0, fun h => absurd h hp⟩
  choose I hI using hIex
  have hIe : ∀ x, ∀ p ∈ P, ∀ t, (I p t).eval x = decide (A x % p = t) :=
    fun x p hp t => (hI p t (hPprime p hp)).2.2 x
  have hI3 : ∀ p ∈ P, ∀ t, (I p t).depth ≤ 3 := fun p hp t => (hI p t (hPprime p hp)).1
  set SI := (n * (n * X + X) + 1) * (8 + 4 * n * (n * X + X)) with hSI
  have hIs : ∀ p ∈ P, ∀ t < p, (I p t).size ≤ SI := by
    intro p hp t _
    refine (hI p t (hPprime p hp)).2.1.trans ?_
    have := hPle p hp
    show _ ≤ (n * (n * X + X) + 1) * (8 + 4 * n * (n * X + X))
    gcongr
  set Mk := ∑ p ∈ P, p with hMk
  set W := 2 ^ B - Q % 2 ^ B with hW
  obtain ⟨T, hTd, hTs, hTe⟩ := T12.iter_add (L2 P I Mk W) 4 B (depth_L2 P I hI3 Mk W)
  obtain ⟨Φ, hΦd, hΦs, hΦe⟩ := T12.compile T 14 hTd
  have hω : ∀ p ∈ P, ∀ t < p, crtOmega P p t ≤ 4 * (X + 1) * X := by
    intro p hp t ht
    refine (T12.crt_omega_le P hPprime p hp t ht).trans ?_
    have hc : P.card ≤ X + 1 := (Finset.card_filter_le _ _).trans (by simp)
    have := hPle p hp
    gcongr
  have hSG : ∀ m, (Gm P I m).size ≤ 1 + Mk * (4 * (X + 1) * X + SI) :=
    size_Gm P I _ _ hω hIs
  have hSf := sizes_L2 P I SI _ hIs hSG Mk W
  rw [← hMk] at hSf
  have hBL := B_le n N K
  refine ⟨B, n * G, Φ, hΦd, ?_, R_le _ C B (by omega) hBL, ?_⟩
  · refine hΦs.trans ?_
    calc ∑ r, (T r).size
        ≤ ∑ _r : Fin B, 10000 * (B + 1) ^ 3 * ((L2 P I Mk W).length + 1) ^ 4 *
            (((L2 P I Mk W).map fun u => u.1.size).sum + 1) := Finset.sum_le_sum fun r _ => hTs r
      _ = B * (10000 * (B + 1) ^ 3 * ((Mk + Mk) + 1) ^ 4 *
            (((L2 P I Mk W).map fun u => u.1.size).sum + 1)) := by
          rw [length_L2, ← hMk]; simp
      _ ≤ cst C * (n + N + K + 1) ^ cst C :=
          arith (n + N + K + 1) n C B X Mk SI _ _ (by omega) (by omega) hC hBL hX
            (sum_P_le X) le_rfl le_rfl hSf
  · intro x
    have hbits : (fun r : Fin B => (T r).eval x) = fun r : Fin B => (A x).testBit r := by
      funext r
      rw [hTe x r]
      have hk := T12.crt_quot_le P hPprime (A x)
      have hAQ : A x < ∏ p ∈ P, p := by have := h2A x; omega
      have key : bigSum (L2 P I Mk W) x % 2 ^ B = A x := by
        rw [bigSum_L2 P I hPprime hne x (A x) (hIe x) (h2A x) Mk W hk, hW, T12.mod_pow_recover,
          T12.crt_sum_mod P hPprime, Nat.mod_eq_of_lt hAQ, Nat.mod_eq_of_lt (hAB x)]
      rw [← key, Nat.testBit_mod_two_pow]
      simp [r.isLt]
    rw [hΦe x, hbits, T12.dyadic_bits _ _ _ (hAB x)]
    have := T12.round_err n K N θ hθ x
    convert this using 3
    simp only [hA_def, ha_def, Nat.cast_prod, hG]

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartZ
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
open ReLUBinaryDepth.ProductTradeoff ReLUBinaryDepth.ProductTradeoff.Supplement
/-! ### Part Z: assembly -/
alias main := ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12.PartZ.main

end ReLUBinaryDepth.ProductTradeoff.Supplement.Dev.T12
end

section
set_option autoImplicit false
namespace ReLUBinaryDepth.ProductTradeoff.Supplement
open ReLUBinaryDepth.ProductTradeoff
theorem chk_theorem_1_2 :
    ∃ d c : ℕ, ∀ (K n N : ℕ), 1 ≤ N → ∀ θ : Fin n → Bool → ℝ,
      (∀ i b, 0 ≤ θ i b ∧ θ i b ≤ (2 : ℝ) ^ K) →
      ∃ (R F : ℕ) (Φ : QNatProofs.ThrCircuit n R),
        Φ.depth ≤ d ∧ Φ.size ≤ c * (n + N + K + 1) ^ c ∧ R ≤ c * (n + N + K + 1) ^ c ∧
        ∀ x : Cube n, |dyadicValue F (Φ.eval x) - productMap θ x| ≤ (2 : ℝ) ^ (-(N : ℤ)) :=
  Dev.T12.main

end ReLUBinaryDepth.ProductTradeoff.Supplement
end

theorem solution : type_of% @ReLUBinaryDepth.ProductTradeoff.Supplement.chk_theorem_1_2 := @ReLUBinaryDepth.ProductTradeoff.Supplement.chk_theorem_1_2
