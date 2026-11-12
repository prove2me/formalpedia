-- Prove2me | solution 1 for Puder.isPrimitiveIn_of_ncard_traverses_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:28:11.178558+00:00
-- url     : https://prove2.me/submissions/dc2c4d6e-0612-41cb-9c45-3734e80c45fd

import Mathlib
import Definitions.Def_StrongConvPuder
import Definitions.Def_StrongConvPuderAlg
import Definitions.Def_StrongConvPuderCore
section
section
namespace Puder.Q284
variable {d : ℕ}
/-!
# q284 Blueprint: PP15 Claim 4.2, Lemma 4.1 and Takahasi from Claim 3.3(4) and Lemma 4.1's last step

Infrastructure on walks of words in Schreier coset graphs (stubs, proved in Parts), then the three
reductions, proved here from the stubs.
-/

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}
theorem mk_cancel_pair (L₁ L₂ : List (Fin d × Bool)) (z : Fin d) (c : Bool) :
    FreeGroup.mk (L₁ ++ (z, c) :: (z, !c) :: L₂) = FreeGroup.mk (L₁ ++ L₂) :=
  Quot.sound FreeGroup.Red.Step.not

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}
theorem traverses_lt_length (J : Subgroup (FreeGroup (Fin d))) {w : FreeGroup (Fin d)} {i : ℕ}
    {g : FreeGroup (Fin d)} {x : Fin d} (h : Traverses J w i g x) : i < w.toWord.length := by
  obtain ⟨p, s, b, hw, hp, -⟩ := h
  rw [hw]; simp; omega

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}

alias traverses_lt_length := Puder.Q284.PartW.traverses_lt_length

end Puder.Q284
end

section
namespace Puder.Q284.PartT
open Puder Puder.Q284
variable {d : ℕ}

theorem mk_letter (x : Fin d) (c : Bool) :
    FreeGroup.mk [(x, c)] = if c then FreeGroup.of x else (FreeGroup.of x)⁻¹ := by
  cases c
  · simp [FreeGroup.inv_mk, FreeGroup.invRev, FreeGroup.of]
  · rfl

end Puder.Q284.PartT
end

section
namespace Puder.Q284
variable {d : ℕ}
end Puder.Q284
end
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
/-!
# q284 Blueprint: Schreier bases adapted to a set of edges; Claim 3.3(4) and Lemma 4.1's last step

For a subgroup `J ≤ F_d` and a coset-invariant set `P` of edges of its Schreier graph, the transversal
`tr J P g` is the element of the coset `J g` minimising (number of steps of its reduced walk outside `P`,
shortlex code of its reduced word). It is a Schreier transversal (prefix-closed), and the elements
`v x tr(v x)⁻¹` over the non-tree edges `(v, x)` form a basis of `J`, the coordinates of `g ∈ J`
being read off the walk of `g` (Reidemeister–Schreier).
-/
/-- The vertex (as a representative `g` of the coset `J g`) of the edge crossed at step `k` of the
walk of the list `L`: the `x`-edge leaving `J g`, where `L[k] = (x, b)`. -/
def vtx (L : List (Fin d × Bool)) (k : Fin L.length) : FreeGroup (Fin d) :=
  if L[k].2 then FreeGroup.mk (L.take k) else FreeGroup.mk (L.take k) * (FreeGroup.of L[k].1)⁻¹

open Classical in
/-- Number of steps of the reduced walk of `g` crossing an edge outside `P`. -/
noncomputable def nonCount (P : FreeGroup (Fin d) → Fin d → Prop) (g : FreeGroup (Fin d)) : ℕ :=
  (Finset.univ.filter fun k : Fin g.toWord.length => ¬ P (vtx g.toWord k) (g.toWord[k]).1).card

/-- Shortlex code of a word, in base `2d + 1` with nonzero digits, first letter most significant. -/
def code (L : List (Fin d × Bool)) : ℕ :=
  L.foldl (fun n a => n * (2 * d + 1) + (2 * (a.1 : ℕ) + if a.2 then 1 else 2)) 0

/-- The key minimised by the transversal. -/
noncomputable def key (P : FreeGroup (Fin d) → Fin d → Prop) (g : FreeGroup (Fin d)) : ℕ ×ₗ ℕ :=
  toLex (nonCount P g, code g.toWord)

/-- The transversal: the element of `J g` of least key. -/
noncomputable def tr (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (g : FreeGroup (Fin d)) : FreeGroup (Fin d) :=
  Function.argminOn (key P) {h | h * g⁻¹ ∈ J} ⟨g, by simp⟩

/-- `P` depends only on the coset of the vertex. -/
def CosetInv (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop) : Prop :=
  ∀ g g' x, g * g'⁻¹ ∈ J → P g x → P g' x

/-- The non-tree edges, indexed by their transversal vertex. -/
def Idx (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop) : Type :=
  {e : FreeGroup (Fin d) × Fin d // tr J P e.1 = e.1 ∧ tr J P (e.1 * FreeGroup.of e.2) ≠ e.1 * FreeGroup.of e.2}

/-- The Schreier generator of a non-tree edge. -/
noncomputable def basisElt (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (e : Idx J P) : FreeGroup (Fin d) :=
  e.1.1 * FreeGroup.of e.1.2 * (tr J P (e.1.1 * FreeGroup.of e.1.2))⁻¹

open Classical in
/-- The contribution of step `k` of the walk of `g` to its Schreier coordinates. -/
noncomputable def stepLabel (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (g : FreeGroup (Fin d)) (k : Fin g.toWord.length) : FreeGroup (Idx J P) :=
  if h : tr J P (tr J P (vtx g.toWord k)) = tr J P (vtx g.toWord k) ∧
      tr J P (tr J P (vtx g.toWord k) * FreeGroup.of (g.toWord[k]).1) ≠
        tr J P (vtx g.toWord k) * FreeGroup.of (g.toWord[k]).1 then
    (if (g.toWord[k]).2 then FreeGroup.of (⟨(tr J P (vtx g.toWord k), (g.toWord[k]).1), h⟩ : Idx J P)
      else (FreeGroup.of (⟨(tr J P (vtx g.toWord k), (g.toWord[k]).1), h⟩ : Idx J P))⁻¹)
  else 1

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS1
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
/-! ## Codes -/
/-- The digit of a letter in the shortlex code. -/
def digit (a : Fin d × Bool) : ℕ := 2 * (a.1 : ℕ) + if a.2 then 1 else 2

theorem digit_pos (a : Fin d × Bool) : 1 ≤ digit a := by
  unfold digit; split <;> omega

theorem digit_lt (a : Fin d × Bool) : digit a < 2 * d + 1 := by
  have := a.1.isLt
  unfold digit; split <;> omega

theorem digit_inj {a a' : Fin d × Bool} (h : digit a = digit a') : a = a' := by
  obtain ⟨x, b⟩ := a
  obtain ⟨x', b'⟩ := a'
  unfold digit at h
  cases b <;> cases b' <;> simp at h <;> first
    | (exfalso; omega)
    | (have : (x : ℕ) = x' := by omega
       simp [Fin.ext this])

theorem foldl_code (L : List (Fin d × Bool)) (n : ℕ) :
    L.foldl (fun n a => n * (2 * d + 1) + (2 * (a.1 : ℕ) + if a.2 then 1 else 2)) n =
      n * (2 * d + 1) ^ L.length + code L := by
  induction L generalizing n with
  | nil => simp [code]
  | cons a L ih =>
    simp only [code, List.foldl_cons, List.length_cons] at ih ⊢
    rw [ih, ih (0 * (2 * d + 1) + _)]
    ring

theorem code_cons (a : Fin d × Bool) (L : List (Fin d × Bool)) :
    code (a :: L) = digit a * (2 * d + 1) ^ L.length + code L := by
  have := foldl_code L (0 * (2 * d + 1) + digit a)
  simp only [code, List.foldl_cons, digit] at this ⊢
  rw [this]; ring

theorem code_nil : code ([] : List (Fin d × Bool)) = 0 := rfl

theorem code_append (A B : List (Fin d × Bool)) :
    code (A ++ B) = code A * (2 * d + 1) ^ B.length + code B := by
  have := foldl_code B (code A)
  simp only [code, List.foldl_append] at this ⊢
  exact this

theorem code_lt (L : List (Fin d × Bool)) : code L < (2 * d + 1) ^ L.length := by
  induction L with
  | nil => simp [code_nil]
  | cons a L ih =>
    rw [code_cons, List.length_cons, pow_succ]
    have := digit_lt a
    have h2 : digit a * (2 * d + 1) ^ L.length + (2 * d + 1) ^ L.length ≤
        (2 * d + 1) ^ L.length * (2 * d + 1) := by
      rw [← Nat.succ_mul, mul_comm]; exact Nat.mul_le_mul_left _ this
    omega

theorem le_code_cons (a : Fin d × Bool) (L : List (Fin d × Bool)) :
    (2 * d + 1) ^ L.length ≤ code (a :: L) := by
  rw [code_cons]
  have := Nat.mul_le_mul_right ((2 * d + 1) ^ L.length) (digit_pos a)
  omega

theorem length_eq_of_code_eq {L L' : List (Fin d × Bool)} (h : code L = code L') :
    L.length = L'.length := by
  have key : ∀ L L' : List (Fin d × Bool), L.length < L'.length → code L < code L' := by
    intro L L' hl
    match L' with
    | [] => simp at hl
    | a :: L'' =>
      have h1 := code_lt L
      have h2 := le_code_cons a L''
      have h3 : (2 * d + 1) ^ L.length ≤ (2 * d + 1) ^ L''.length :=
        Nat.pow_le_pow_right (by omega) (by simp at hl; omega)
      omega
  rcases lt_trichotomy L.length L'.length with hl | hl | hl
  · exact absurd h (key L L' hl).ne
  · exact hl
  · exact absurd h (key L' L hl).ne'

theorem code_inj_aux : ∀ (L L' : List (Fin d × Bool)), L.length = L'.length →
    code L = code L' → L = L'
  | [], [], _, _ => rfl
  | a :: L, a' :: L', hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [code_cons, code_cons, hl] at h
    have hlt := code_lt L
    have hlt' := code_lt L'
    rw [hl] at hlt
    have hpos : 0 < (2 * d + 1) ^ L'.length := by positivity
    have hm := congrArg (· % (2 * d + 1) ^ L'.length) h
    have hd := congrArg (· / (2 * d + 1) ^ L'.length) h
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt,
      add_comm (digit a' * _), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt'] at hm
    rw [add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt,
      add_comm (digit a' * _), Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt'] at hd
    simp only [zero_add] at hd
    rw [digit_inj hd, code_inj_aux L L' hl hm]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem code_inj {L L' : List (Fin d × Bool)} (h : code L = code L') : L = L' :=
  code_inj_aux L L' (length_eq_of_code_eq h) h

/-! ## Counting non-`P` steps -/
open Classical in
/-- Number of non-`P` steps of the walk of the list `L` started at the coset of `u`. -/
noncomputable def cntR (P : FreeGroup (Fin d) → Fin d → Prop) :
    FreeGroup (Fin d) → List (Fin d × Bool) → ℕ
  | _, [] => 0
  | u, a :: L =>
    (if P (if a.2 then u else u * (FreeGroup.of a.1)⁻¹) a.1 then 0 else 1) +
      cntR P (u * FreeGroup.mk [a]) L

theorem cntR_append (P : FreeGroup (Fin d) → Fin d → Prop) (A B : List (Fin d × Bool)) (u : FreeGroup (Fin d)) :
    cntR P u (A ++ B) = cntR P u A + cntR P (u * FreeGroup.mk A) B := by
  induction A generalizing u with
  | nil => simp [cntR, ← FreeGroup.one_eq_mk]
  | cons a A ih =>
    simp only [List.cons_append, cntR, ih, mul_assoc, FreeGroup.mul_mk, List.nil_append]
    ring

open Classical in
theorem cntR_coset (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (hP : CosetInv J P) (L : List (Fin d × Bool)) :
    ∀ u u' : FreeGroup (Fin d), u * u'⁻¹ ∈ J → cntR P u L = cntR P u' L := by
  induction L with
  | nil => intros; rfl
  | cons a L ih =>
    intro u u' h
    have hv : (if a.2 then u else u * (FreeGroup.of a.1)⁻¹) *
        (if a.2 then u' else u' * (FreeGroup.of a.1)⁻¹)⁻¹ ∈ J := by
      split
      · exact h
      · simpa [mul_assoc] using h
    have hv' := J.inv_mem hv
    rw [mul_inv_rev, inv_inv] at hv'
    have hiff : P (if a.2 then u else u * (FreeGroup.of a.1)⁻¹) a.1 ↔
        P (if a.2 then u' else u' * (FreeGroup.of a.1)⁻¹) a.1 :=
      ⟨hP _ _ _ hv, hP _ _ _ hv'⟩
    simp only [cntR]
    congr 1
    · exact if_congr hiff rfl rfl
    apply ih
    have : u * FreeGroup.mk [a] * (u' * FreeGroup.mk [a])⁻¹ = u * u'⁻¹ := by group
    rw [this]; exact h

theorem cntR_step (P : FreeGroup (Fin d) → Fin d → Prop) {L L' : List (Fin d × Bool)}
    (h : FreeGroup.Red.Step L L') (u : FreeGroup (Fin d)) : cntR P u L' ≤ cntR P u L := by
  cases h with
  | @not L₁ L₂ z c =>
    rw [cntR_append, cntR_append]
    have : u * FreeGroup.mk L₁ * FreeGroup.mk [(z, c)] * FreeGroup.mk [(z, !c)] =
        u * FreeGroup.mk L₁ := by
      rw [mul_assoc (u * _), FreeGroup.mul_mk]
      have : FreeGroup.mk ([(z, c)] ++ [(z, !c)]) = 1 := by
        have := Puder.Q284.PartW.mk_cancel_pair [] [] z c
        rw [FreeGroup.one_eq_mk]; simpa using this
      rw [this, mul_one]
    simp only [cntR, this]
    omega

theorem cntR_red (P : FreeGroup (Fin d) → Fin d → Prop) {L L' : List (Fin d × Bool)}
    (h : FreeGroup.Red L L') (u : FreeGroup (Fin d)) : cntR P u L' ≤ cntR P u L := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (cntR_step P hstep u).trans ih

open Classical in
theorem sum_eq_cntR (P : FreeGroup (Fin d) → Fin d → Prop) (L : List (Fin d × Bool)) :
    ∀ u : FreeGroup (Fin d),
      (∑ k : Fin L.length, if P (u * vtx L k) (L[k]).1 then 0 else 1) = cntR P u L := by
  induction L with
  | nil => intro u; simp [cntR]
  | cons a L ih =>
    intro u
    refine (Fin.sum_univ_succ (n := L.length)
      (fun k => if P (u * vtx (a :: L) k) ((a :: L)[k]).1 then 0 else 1)).trans ?_
    simp only [cntR]
    rw [← ih (u * FreeGroup.mk [a])]
    congr 1
    · refine if_congr (Iff.of_eq ?_) rfl rfl
      have hv : u * vtx (a :: L) 0 = if a.2 then u else u * (FreeGroup.of a.1)⁻¹ := by
        obtain ⟨x, b⟩ := a
        cases b <;> simp [vtx, ← FreeGroup.one_eq_mk]
      rw [hv]; rfl
    · apply Finset.sum_congr rfl
      intro k _
      refine if_congr (Iff.of_eq ?_) rfl rfl
      have hv : u * vtx (a :: L) k.succ = u * FreeGroup.mk [a] * vtx L k := by
        have : FreeGroup.mk (a :: List.take (↑k) L) =
            FreeGroup.mk [a] * FreeGroup.mk (List.take (↑k) L) := by
          rw [FreeGroup.mul_mk]; rfl
        have hk : (a :: L)[k.succ] = L[k] := rfl
        simp only [vtx, hk, Fin.val_succ, List.take_succ_cons, this]
        split <;> simp only [mul_assoc]
      rw [hv]; rfl

theorem nonCount_eq (P : FreeGroup (Fin d) → Fin d → Prop) (g : FreeGroup (Fin d)) :
    nonCount P g = cntR P 1 g.toWord := by
  rw [← sum_eq_cntR, nonCount, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro k _
  rw [one_mul]
  by_cases h : P (vtx g.toWord k) (g.toWord[k]).1 <;> simp

theorem code_le_cons (a : Fin d × Bool) (L : List (Fin d × Bool)) : code L ≤ code (a :: L) := by
  rw [code_cons]; omega

theorem code_step {L L' : List (Fin d × Bool)} (h : FreeGroup.Red.Step L L') : code L' ≤ code L := by
  cases h with
  | @not L₁ L₂ z c =>
    rw [code_append, code_append]
    have h1 := (code_le_cons (z, !c) L₂).trans (code_le_cons (z, c) _)
    have h2 : (2 * d + 1) ^ L₂.length ≤ (2 * d + 1) ^ ((z, c) :: (z, !c) :: L₂).length :=
      Nat.pow_le_pow_right (by omega) (by simp only [List.length_cons]; omega)
    have h3 := Nat.mul_le_mul_left (code L₁) h2
    omega

theorem code_red {L L' : List (Fin d × Bool)} (h : FreeGroup.Red L L') : code L' ≤ code L := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (code_step hstep).trans ih

/-! ## The key -/
theorem key_le_iff (P : FreeGroup (Fin d) → Fin d → Prop) (a b : FreeGroup (Fin d)) :
    key P a ≤ key P b ↔ nonCount P a < nonCount P b ∨
      nonCount P a = nonCount P b ∧ code a.toWord ≤ code b.toWord := by
  unfold key; exact Prod.Lex.toLex_le_toLex

theorem key_inj (P : FreeGroup (Fin d) → Fin d → Prop) {a b : FreeGroup (Fin d)}
    (h : key P a = key P b) : a = b := by
  unfold key at h
  have h' := toLex.injective h
  simp only [Prod.mk.injEq] at h'
  exact FreeGroup.toWord_injective (code_inj h'.2)

theorem key_tr_le (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    {g h : FreeGroup (Fin d)} (hh : h * g⁻¹ ∈ J) : key P (tr J P g) ≤ key P h :=
  Function.argminOn_le (key P) {h | h * g⁻¹ ∈ J} (a := h) hh

theorem argminOn_congr {α β : Type*} [LT β] [WellFoundedLT β] (f : α → β) {s t : Set α}
    (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    Function.argminOn f s hs = Function.argminOn f t ht := by
  subst h; rfl

/-! ## Part S1 -/
theorem tr_mem (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (g : FreeGroup (Fin d)) : tr J P g * g⁻¹ ∈ J :=
  Function.argminOn_mem (key P) {h | h * g⁻¹ ∈ J} ⟨g, by simp⟩

end Puder.Q284S.PartS1
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
/-! ## Part S1: the transversal -/
alias tr_mem := Puder.Q284S.PartS1.tr_mem

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS1
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
theorem tr_congr (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    {g g' : FreeGroup (Fin d)} (h : g * g'⁻¹ ∈ J) : tr J P g = tr J P g' := by
  unfold tr
  apply argminOn_congr
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hx
    have := J.mul_mem hx h
    simpa [mul_assoc] using this
  · intro hx
    have := J.mul_mem hx (J.inv_mem h)
    simpa [mul_assoc] using this

end Puder.Q284S.PartS1
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
alias tr_congr := Puder.Q284S.PartS1.tr_congr

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS1
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
theorem tr_one (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop) :
    tr J P 1 = 1 := by
  apply key_inj P
  apply le_antisymm (key_tr_le J P (by simp))
  rw [key_le_iff]
  have h1 : nonCount P (1 : FreeGroup (Fin d)) = 0 := by
    rw [nonCount_eq, FreeGroup.toWord_one]; rfl
  have h2 : code (1 : FreeGroup (Fin d)).toWord = 0 := by
    rw [FreeGroup.toWord_one]; rfl
  rw [h1, h2]
  rcases Nat.eq_zero_or_pos (nonCount P (tr J P 1)) with h | h
  · exact Or.inr ⟨h.symm, Nat.zero_le _⟩
  · exact Or.inl h

end Puder.Q284S.PartS1
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
alias tr_one := Puder.Q284S.PartS1.tr_one

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS1
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
theorem nonCount_tr_eq_zero (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    {g h : FreeGroup (Fin d)} (hgh : h * g⁻¹ ∈ J) (hh : nonCount P h = 0) : nonCount P (tr J P g) = 0 := by
  have := (key_le_iff P _ _).mp (key_tr_le J P hgh)
  omega

theorem toWord_mk_of_isReduced {L : List (Fin d × Bool)} (h : FreeGroup.IsReduced L) :
    (FreeGroup.mk L).toWord = L := by
  rw [FreeGroup.toWord_mk, h.reduce_eq]

theorem tr_take (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (hP : CosetInv J P) (g : FreeGroup (Fin d)) (k : ℕ) :
    tr J P (FreeGroup.mk ((tr J P g).toWord.take k)) = FreeGroup.mk ((tr J P g).toWord.take k) := by
  set t := tr J P g with ht
  set p := t.toWord.take k with hpdef
  set s := t.toWord.drop k with hsdef
  have hps : t.toWord = p ++ s := (List.take_append_drop k t.toWord).symm
  have hp : (FreeGroup.mk p).toWord = p :=
    toWord_mk_of_isReduced (FreeGroup.isReduced_toWord.infix (List.take_prefix k _).isInfix)
  set p' := tr J P (FreeGroup.mk p) with hp'def
  set A := p'.toWord with hA
  have hp'mem : p' * (FreeGroup.mk p)⁻¹ ∈ J := tr_mem J P _
  have hkey1 := (key_le_iff P _ _).mp (key_tr_le J P (g := FreeGroup.mk p)
    (h := FreeGroup.mk p) (by rw [mul_inv_cancel]; exact J.one_mem))
  have htmk : t = FreeGroup.mk p * FreeGroup.mk s := by
    rw [FreeGroup.mul_mk, ← hps, FreeGroup.mk_toWord]
  have hp'A : p' = FreeGroup.mk A := FreeGroup.mk_toWord.symm
  set g' := FreeGroup.mk (A ++ s) with hg'
  have hg'mem : g' * g⁻¹ ∈ J := by
    have e : g' * g⁻¹ = (p' * (FreeGroup.mk p)⁻¹) * (t * g⁻¹) := by
      rw [hg', ← FreeGroup.mul_mk, ← hp'A, htmk]; group
    rw [e]; exact J.mul_mem hp'mem (tr_mem J P g)
  have hkey2 := (key_le_iff P _ _).mp (key_tr_le J P hg'mem)
  -- counts
  have hnt : nonCount P t = cntR P 1 p + cntR P (FreeGroup.mk p) s := by
    rw [nonCount_eq, hps, cntR_append, one_mul]
  have hnp : nonCount P (FreeGroup.mk p) = cntR P 1 p := by rw [nonCount_eq, hp]
  have hnp' : nonCount P p' = cntR P 1 A := nonCount_eq P p'
  have hng' : nonCount P g' ≤ cntR P 1 A + cntR P (FreeGroup.mk p) s := by
    rw [nonCount_eq, hg', FreeGroup.toWord_mk]
    refine (cntR_red P FreeGroup.reduce.red 1).trans (le_of_eq ?_)
    rw [cntR_append, one_mul, ← hp'A]
    congr 1
    exact cntR_coset J P hP s _ _ hp'mem
  -- codes
  have hct : code t.toWord = code p * (2 * d + 1) ^ s.length + code s := by
    rw [hps, code_append]
  have hcp : code (FreeGroup.mk p).toWord = code p := by rw [hp]
  have hcg' : code g'.toWord ≤ code A * (2 * d + 1) ^ s.length + code s := by
    rw [← code_append, hg', FreeGroup.toWord_mk]
    exact code_red FreeGroup.reduce.red
  have hpos : 0 < (2 * d + 1) ^ s.length := by positivity
  have hA' : code (tr J P (FreeGroup.mk p)).toWord = code A := rfl
  rw [hnp, hnp', hcp, hA'] at hkey1
  rw [hnt, hct] at hkey2
  -- key p' = key (mk p)
  have hn : cntR P 1 A = cntR P 1 p := by
    rcases hkey1 with h | ⟨h, -⟩
    · exfalso; omega
    · exact h
  have hc : code A = code p := by
    rcases hkey1 with h | ⟨-, h⟩
    · exfalso; omega
    · rcases Nat.lt_or_ge (code A) (code p) with h' | h'
      · exfalso
        have := Nat.mul_lt_mul_of_pos_right h' hpos
        omega
      · omega
  have hAp : A = p := code_inj hc
  rw [hp'A, hAp]

end Puder.Q284S.PartS1
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
alias tr_take := Puder.Q284S.PartS1.tr_take

alias nonCount_tr_eq_zero := Puder.Q284S.PartS1.nonCount_tr_eq_zero

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS2
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
variable (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
/-!
# q284 Part S2: the Schreier basis (Reidemeister–Schreier)
-/
local notation "G" => FreeGroup (Fin d)

theorem tr_tr (g : G) : tr J P (tr J P g) = tr J P g := tr_congr J P (tr_mem J P g)

theorem tr_mul_right (g h : G) : tr J P (tr J P g * h) = tr J P (g * h) := by
  apply tr_congr
  have := tr_mem J P g
  simpa [mul_assoc] using this

/-- Transversal elements. -/
abbrev T := {v : G // tr J P v = v}

/-- The label of the `x`-edge leaving the transversal vertex `w`. -/
noncomputable def lab (w : G) (x : Fin d) : FreeGroup (Idx J P) := by
  classical
  exact if h : tr J P w = w ∧ tr J P (w * FreeGroup.of x) ≠ w * FreeGroup.of x then
    FreeGroup.of (⟨(w, x), h⟩ : Idx J P) else 1

/-- The permutation of `T × FreeGroup ι` given by the letter `x`. -/
noncomputable def sig (x : Fin d) : Equiv.Perm (T J P × FreeGroup (Idx J P)) where
  toFun s := (⟨tr J P (s.1.1 * FreeGroup.of x), tr_tr J P _⟩, s.2 * lab J P s.1.1 x)
  invFun s := (⟨tr J P (s.1.1 * (FreeGroup.of x)⁻¹), tr_tr J P _⟩,
    s.2 * (lab J P (tr J P (s.1.1 * (FreeGroup.of x)⁻¹)) x)⁻¹)
  left_inv s := by
    obtain ⟨⟨v, hv⟩, u⟩ := s
    have h1 : tr J P (tr J P (v * FreeGroup.of x) * (FreeGroup.of x)⁻¹) = v := by
      rw [tr_mul_right]; simpa using hv
    ext1
    · exact Subtype.ext h1
    · simp only
      rw [h1]; simp
  right_inv s := by
    obtain ⟨⟨v, hv⟩, u⟩ := s
    have h1 : tr J P (tr J P (v * (FreeGroup.of x)⁻¹) * FreeGroup.of x) = v := by
      rw [tr_mul_right]; simpa using hv
    ext1
    · exact Subtype.ext h1
    · simp

/-- The right action of `F_d`. -/
noncomputable def A : G →* (Equiv.Perm (T J P × FreeGroup (Idx J P)))ᵐᵒᵖ :=
  FreeGroup.lift fun x => MulOpposite.op (sig J P x)

noncomputable def act (s : T J P × FreeGroup (Idx J P)) (g : G) : T J P × FreeGroup (Idx J P) :=
  (A J P g).unop s

theorem act_one (s) : act J P s 1 = s := by simp [act]

theorem act_mul (s) (g h : G) : act J P s (g * h) = act J P (act J P s g) h := by
  simp [act, map_mul, Equiv.Perm.mul_apply]

theorem act_of (s) (x : Fin d) : act J P s (FreeGroup.of x) = sig J P x s := by
  simp [act, A]

theorem act_inv_of (s) (x : Fin d) : act J P s (FreeGroup.of x)⁻¹ = (sig J P x).symm s := by
  simp [act, A, map_inv]

theorem mk_single (a : Fin d × Bool) :
    FreeGroup.mk [a] = if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹ := by
  obtain ⟨x, b⟩ := a
  cases b
  · simp [FreeGroup.inv_mk, FreeGroup.of, FreeGroup.invRev]
  · rfl

/-- Induction on words. -/
theorem ind {p : G → Prop} (h1 : p 1) (hm : ∀ a g, p g → p (FreeGroup.mk [a] * g)) (g : G) : p g := by
  rw [← FreeGroup.mk_toWord (x := g)]
  induction g.toWord with
  | nil => exact h1
  | cons a L ih =>
    have : FreeGroup.mk (a :: L) = FreeGroup.mk [a] * FreeGroup.mk L := by
      rw [FreeGroup.mul_mk]; rfl
    rw [this]; exact hm a _ ih

theorem act_single (s) (a : Fin d × Bool) :
    act J P s (FreeGroup.mk [a]) =
      if a.2 then (⟨⟨tr J P (s.1.1 * FreeGroup.of a.1), tr_tr J P _⟩, s.2 * lab J P s.1.1 a.1⟩)
      else (⟨tr J P (s.1.1 * (FreeGroup.of a.1)⁻¹), tr_tr J P _⟩,
        s.2 * (lab J P (tr J P (s.1.1 * (FreeGroup.of a.1)⁻¹)) a.1)⁻¹) := by
  rw [mk_single]
  obtain ⟨x, b⟩ := a
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, act_inv_of]; rfl
  · simp only [↓reduceIte, act_of]; rfl

theorem act_fst (g : G) : ∀ s, ((act J P s g).1 : G) = tr J P (s.1.1 * g) := by
  induction g using ind with
  | h1 => intro s; simp [act_one, s.1.2]
  | hm a g ih =>
    intro s
    rw [act_mul, ih, act_single]
    split_ifs with hb
    · simp only; rw [tr_mul_right, mk_single, if_pos hb, mul_assoc]
    · simp only; rw [tr_mul_right, mk_single, if_neg hb, mul_assoc]

theorem act_snd (g : G) : ∀ s, (act J P s g).2 = s.2 * (act J P (s.1, 1) g).2 := by
  induction g using ind with
  | h1 => intro s; simp [act_one]
  | hm a g ih =>
    intro s
    rw [act_mul, act_mul, ih, ih (act J P (s.1, 1) (FreeGroup.mk [a])), act_single, act_single]
    split_ifs <;> simp [mul_assoc]

/-- The cocycle. -/
noncomputable def C (v : T J P) (g : G) : FreeGroup (Idx J P) := (act J P (v, 1) g).2

theorem C_mul (v : T J P) (g h : G) :
    C J P v (g * h) = C J P v g * C J P (act J P (v, 1) g).1 h := by
  unfold C
  rw [act_mul, act_snd]

theorem C_single (v : T J P) (a : Fin d × Bool) :
    C J P v (FreeGroup.mk [a]) = if a.2 then lab J P v.1 a.1
      else (lab J P (tr J P (v.1 * (FreeGroup.of a.1)⁻¹)) a.1)⁻¹ := by
  unfold C; rw [act_single]; split_ifs <;> simp

/-- The vertex `1`. -/
def oneT : T J P := ⟨1, tr_one J P⟩

theorem vert_eq (v : T J P) (g : G) (w : T J P) (h : tr J P (v.1 * g) = w.1) :
    (act J P (v, 1) g).1 = w := Subtype.ext (by rw [act_fst]; exact h)

/-- The map `ψ`. -/
noncomputable def psi : FreeGroup (Idx J P) →* J :=
  FreeGroup.lift fun e => ⟨basisElt J P e, by
    have := tr_mem J P (e.1.1 * FreeGroup.of e.1.2)
    have := J.inv_mem this
    simpa [basisElt, mul_assoc] using this⟩

theorem psi_of (e : Idx J P) : (psi J P (FreeGroup.of e) : G) = basisElt J P e := by
  simp [psi]

theorem psi_lab (w : G) (hw : tr J P w = w) (x : Fin d) :
    (psi J P (lab J P w x) : G) = w * FreeGroup.of x * (tr J P (w * FreeGroup.of x))⁻¹ := by
  unfold lab
  split_ifs with h
  · exact psi_of J P ⟨(w, x), h⟩
  · have : tr J P (w * FreeGroup.of x) = w * FreeGroup.of x := by
      by_contra h'; exact h ⟨hw, h'⟩
    rw [this]; simp

theorem psi_C (g : G) : ∀ v : T J P, (psi J P (C J P v g) : G) = v.1 * g * (tr J P (v.1 * g))⁻¹ := by
  induction g using ind with
  | h1 => intro v; simp [C, act_one, v.2]
  | hm a g ih =>
    intro v
    rw [C_mul, map_mul, Subgroup.coe_mul, ih, act_fst, C_single, tr_mul_right]
    have key : (psi J P (if a.2 then lab J P v.1 a.1
        else (lab J P (tr J P (v.1 * (FreeGroup.of a.1)⁻¹)) a.1)⁻¹) : G) =
        v.1 * FreeGroup.mk [a] * (tr J P (v.1 * FreeGroup.mk [a]))⁻¹ := by
      rw [mk_single]
      split_ifs
      · rw [psi_lab J P _ v.2]
      · rw [map_inv, Subgroup.coe_inv, psi_lab J P _ (tr_tr J P _), tr_mul_right]
        simp [v.2, mul_assoc]
    rw [key]
    simp [mul_assoc]

/-- The inverse map `ρ`. -/
noncomputable def rho : J →* FreeGroup (Idx J P) where
  toFun g := C J P (oneT J P) g.1
  map_one' := by simp [C, act_one]
  map_mul' g h := by
    simp only [Subgroup.coe_mul]
    rw [C_mul]
    congr 2
    apply vert_eq
    simp only [oneT, one_mul]
    rw [tr_congr J P (g := g.1) (g' := 1) (by simpa using g.2), tr_one]

theorem C_oneT_fixed (hP : CosetInv J P) (v : G) (hv : tr J P v = v) : C J P (oneT J P) v = 1 := by
  have ht := tr_take J P hP v
  rw [hv] at ht
  set L := v.toWord
  have key : ∀ k, C J P (oneT J P) (FreeGroup.mk (L.take k)) = 1 := by
    intro k
    induction k with
    | zero => show C J P (oneT J P) 1 = 1; simp [C, act_one]
    | succ k ih =>
      by_cases hk : k < L.length
      · have hsplit : FreeGroup.mk (L.take (k + 1)) = FreeGroup.mk (L.take k) * FreeGroup.mk [L[k]] := by
          rw [FreeGroup.mul_mk, List.take_add_one, List.getElem?_eq_getElem hk]; rfl
        have hfix := ht (k + 1)
        rw [hsplit] at hfix ⊢
        rw [C_mul, ih, one_mul]
        have hv' : (act J P (oneT J P, 1) (FreeGroup.mk (L.take k))).1 = ⟨_, ht k⟩ :=
          vert_eq J P _ _ _ (by simp [oneT, ht k])
        rw [hv', C_single]
        rw [mk_single] at hfix
        split_ifs at hfix ⊢ with hb
        · unfold lab; rw [dif_neg]; simp [hfix]
        · simp only [hfix]
          unfold lab; rw [dif_neg]; · simp
          simp [ht k]
      · push Not at hk
        rw [List.take_of_length_le hk, List.take_of_length_le (by omega)] at *
        exact ih
  have := key L.length
  rwa [List.take_length, FreeGroup.mk_toWord] at this

theorem rho_psi (hP : CosetInv J P) : (rho J P).comp (psi J P) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro e
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
  change C J P (oneT J P) (psi J P (FreeGroup.of e) : G) = _
  rw [psi_of]
  obtain ⟨⟨v, x⟩, hv, hne⟩ := e
  simp only [basisElt]
  rw [C_mul, C_mul, C_oneT_fixed J P hP v hv, one_mul]
  have h1 : (act J P (oneT J P, 1) v).1 = ⟨v, hv⟩ := vert_eq J P _ _ _ (by simp [oneT, hv])
  rw [h1]
  have h2 : C J P ⟨v, hv⟩ (FreeGroup.of x) = FreeGroup.of ⟨(v, x), hv, hne⟩ := by
    have := C_single J P ⟨v, hv⟩ (x, true)
    simp only [↓reduceIte] at this
    rw [show FreeGroup.mk [(x, true)] = FreeGroup.of x from rfl] at this
    rw [this]; unfold lab; rw [dif_pos ⟨hv, hne⟩]
  rw [h2]
  set w := tr J P (v * FreeGroup.of x)
  have h3 : (act J P (oneT J P, 1) (v * FreeGroup.of x)).1 = ⟨w, tr_tr J P _⟩ :=
    vert_eq J P _ _ _ (by simp [oneT, w])
  rw [h3]
  -- C_w (w⁻¹) = (C_1 w)⁻¹ = 1
  have h4 := C_mul J P ⟨w, tr_tr J P _⟩ w⁻¹ w
  rw [inv_mul_cancel] at h4
  have h5 : (act J P (⟨w, tr_tr J P _⟩, 1) w⁻¹).1 = oneT J P :=
    vert_eq J P _ _ _ (by simp [oneT, tr_one])
  rw [h5, C_oneT_fixed J P hP w (tr_tr J P _)] at h4
  have h6 : C J P ⟨w, tr_tr J P _⟩ 1 = 1 := by simp [C, act_one]
  rw [h6, mul_one] at h4
  rw [← h4, mul_one]

theorem psi_rho : (psi J P).comp (rho J P) = MonoidHom.id _ := by
  ext g
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
  change (psi J P (C J P (oneT J P) g.1) : G) = g.1
  rw [psi_C]
  simp [oneT, tr_congr J P (g := g.1) (g' := 1) (by simpa using g.2), tr_one]

theorem stepLabel_eq (g : G) (k : Fin g.toWord.length) :
    stepLabel J P g k = if (g.toWord[k]).2 then lab J P (tr J P (vtx g.toWord k)) (g.toWord[k]).1
      else (lab J P (tr J P (vtx g.toWord k)) (g.toWord[k]).1)⁻¹ := by
  unfold stepLabel lab
  split_ifs <;> rfl

theorem rho_eq (g : G) :
    C J P (oneT J P) g = ((List.finRange g.toWord.length).map (stepLabel J P g)).prod := by
  set L := g.toWord with hL
  classical
  let s : ℕ → FreeGroup (Idx J P) := fun k => if h : k < L.length then stepLabel J P g ⟨k, h⟩ else 1
  have hs : (List.finRange L.length).map (stepLabel J P g) = (List.range L.length).map s := by
    rw [← List.map_coe_finRange_eq_range, List.map_map]
    apply List.map_congr_left
    intro k _
    simp [s]
  have key : ∀ n, n ≤ L.length → C J P (oneT J P) (FreeGroup.mk (L.take n)) =
      ((List.range n).map s).prod := by
    intro n
    induction n with
    | zero => intro; show C J P (oneT J P) 1 = _; simp [C, act_one]
    | succ n ih =>
      intro hn
      have hk : n < L.length := hn
      have hsplit : FreeGroup.mk (L.take (n + 1)) = FreeGroup.mk (L.take n) * FreeGroup.mk [L[n]] := by
        rw [FreeGroup.mul_mk, List.take_add_one, List.getElem?_eq_getElem hk]; rfl
      rw [hsplit, C_mul, ih (by omega), List.range_succ, List.map_append, List.prod_append]
      congr 1
      have hv' : (act J P (oneT J P, 1) (FreeGroup.mk (L.take n))).1 =
          ⟨tr J P (FreeGroup.mk (L.take n)), tr_tr J P _⟩ :=
        vert_eq J P _ _ _ (by simp [oneT])
      rw [hv', C_single]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, s, dif_pos hk]
      rw [stepLabel_eq]
      simp only [vtx]
      split_ifs <;> simp_all [tr_mul_right]
  have := key L.length le_rfl
  rw [List.take_length, hL, FreeGroup.mk_toWord] at this
  rw [this, hs]

end Puder.Q284S.PartS2
end

section
namespace Puder.Q284S.PartS2
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
theorem exists_basis (J : Subgroup (FreeGroup (Fin d))) (P : FreeGroup (Fin d) → Fin d → Prop)
    (hP : CosetInv J P) :
    ∃ b : FreeGroupBasis (Idx J P) J, (∀ e, (b e : FreeGroup (Fin d)) = basisElt J P e) ∧
      ∀ (g : FreeGroup (Fin d)) (hg : g ∈ J),
        b.repr ⟨g, hg⟩ = ((List.finRange g.toWord.length).map (stepLabel J P g)).prod := by
  let E : FreeGroup (Idx J P) ≃* J :=
    MonoidHom.toMulEquiv (psi J P) (rho J P) (rho_psi J P hP) (psi_rho J P)
  refine ⟨FreeGroupBasis.ofRepr E.symm, ?_, ?_⟩
  · intro e
    change ((E.symm.symm (FreeGroup.of e) : J) : FreeGroup (Fin d)) = _
    rw [MulEquiv.symm_symm]
    exact psi_of J P e
  · intro g hg
    change rho J P ⟨g, hg⟩ = _
    exact rho_eq J P g

end Puder.Q284S.PartS2
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
/-! ## Part S2: the Schreier basis -/
alias exists_basis := Puder.Q284S.PartS2.exists_basis

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS3
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
/-!
# q284 Part S3: Claim 3.3(4)

If every edge traversed by an element of `J` that is also traversed by some element of `H`
forces membership in `H`, then `H` is a free factor of `J`: it is generated by the Schreier
basis elements of the non-tree edges lying in the image subgraph of `H`.
-/

end Puder.Q284S.PartS3
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
/-! ## Part S3: Claim 3.3(4) -/

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS4
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}
/-- The edge set of Lemma 4.1's last step: every edge except the `x`-edge at `N g`. -/
def PE (N : Subgroup (FreeGroup (Fin d))) (g : FreeGroup (Fin d)) (x : Fin d) :
    FreeGroup (Fin d) → Fin d → Prop :=
  fun y z => ¬ (y * g⁻¹ ∈ N ∧ z = x)

theorem forall_vtx_iff (P : FreeGroup (Fin d) → Fin d → Prop) (L : List (Fin d × Bool)) :
    (∀ k : Fin L.length, P (vtx L k) L[k].1) ↔ ∀ (p s : List (Fin d × Bool)) (c : Fin d × Bool),
      L = p ++ c :: s →
      P (if c.2 then FreeGroup.mk p else FreeGroup.mk p * (FreeGroup.of c.1)⁻¹) c.1 := by
  constructor
  · intro H p s c hL
    subst hL
    have hk : p.length < (p ++ c :: s).length := by simp
    have := H ⟨p.length, hk⟩
    simp only [vtx] at this
    simpa [List.take_left'] using this
  · intro H k
    have hk := k.2
    have hL : L = L.take k ++ L[k.1] :: L.drop (k+1) := by
      rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
    have := H _ _ _ hL
    simpa [vtx] using this

open Classical in
theorem nonCount_eq_zero_iff (P : FreeGroup (Fin d) → Fin d → Prop) (h : FreeGroup (Fin d)) :
    nonCount P h = 0 ↔ ∀ (p s : List (Fin d × Bool)) (c : Fin d × Bool), h.toWord = p ++ c :: s →
      P (if c.2 then FreeGroup.mk p else FreeGroup.mk p * (FreeGroup.of c.1)⁻¹) c.1 := by
  rw [← forall_vtx_iff]
  unfold nonCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [Finset.mem_univ, not_not, forall_const]

theorem mk_toWord_of_eq {h : FreeGroup (Fin d)} {p s : List (Fin d × Bool)} {c : Fin d × Bool}
    (hL : h.toWord = p ++ c :: s) : (FreeGroup.mk p).toWord = p := by
  rw [FreeGroup.toWord_mk]
  exact ((FreeGroup.isReduced_toWord (x := h)).infix ⟨[], c :: s, by simp [hL]⟩).reduce_eq

/-- A prefix ending just before the only crossing of the edge avoids it. -/
theorem avoid (N : Subgroup (FreeGroup (Fin d))) (g : FreeGroup (Fin d)) (x : Fin d)
    {h : FreeGroup (Fin d)} {p s : List (Fin d × Bool)} {c : Fin d × Bool}
    (hL : h.toWord = p ++ c :: s) (huniq : ∀ k, Traverses N h k g x → k = p.length) :
    nonCount (PE N g x) (FreeGroup.mk p) = 0 := by
  rw [nonCount_eq_zero_iff]
  intro p' s' c' hp'
  rw [mk_toWord_of_eq hL] at hp'
  rintro ⟨hm, hx⟩
  have htr : Traverses N h p'.length g x := by
    refine ⟨p', s' ++ c :: s, c'.2, ?_, rfl, ?_⟩
    · rw [hL, hp', ← hx]; simp
    · rw [← hx]; exact hm
  have := huniq _ htr
  rw [hp'] at this
  simp at this

theorem traverses_inv_idx (J : Subgroup (FreeGroup (Fin d))) {a : FreeGroup (Fin d)} (ha : a ∈ J)
    {i : ℕ} {g : FreeGroup (Fin d)} {x : Fin d} (h : Traverses J a⁻¹ i g x) :
    Traverses J a (a.toWord.length - 1 - i) g x := by
  obtain ⟨p, s, b, hw, hi, hm⟩ := h
  have hmk : a⁻¹ = FreeGroup.mk p * FreeGroup.mk [(x, b)] * FreeGroup.mk s := by
    rw [FreeGroup.mul_mk, FreeGroup.mul_mk, List.append_assoc, List.singleton_append, ← hw,
      FreeGroup.mk_toWord]
  have hword : a.toWord = FreeGroup.invRev s ++ (x, !b) :: FreeGroup.invRev p := by
    have := congrArg FreeGroup.invRev hw
    rw [← FreeGroup.toWord_inv, inv_inv] at this
    rw [this]; simp [FreeGroup.invRev]
  have hidx : a.toWord.length - 1 - i = (FreeGroup.invRev s).length := by
    rw [hword]; simp [FreeGroup.invRev_length]; omega
  rw [hidx]
  refine ⟨_, _, _, hword, rfl, ?_⟩
  rw [← FreeGroup.inv_mk]
  have ha' : a = (FreeGroup.mk p * FreeGroup.mk [(x, b)] * FreeGroup.mk s)⁻¹ := by
    rw [← hmk, inv_inv]
  cases b
  · have hx : FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ := by
      rw [FreeGroup.of, FreeGroup.inv_mk]; rfl
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hm ⊢
    rw [hx] at ha'
    have : (FreeGroup.mk s)⁻¹ * g⁻¹ = a * (FreeGroup.mk p * (FreeGroup.of x)⁻¹ * g⁻¹) := by
      rw [ha']; group
    rw [this]; exact J.mul_mem ha hm
  · have hx : FreeGroup.mk [(x, true)] = FreeGroup.of x := rfl
    simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true] at hm ⊢
    rw [hx] at ha'
    have : (FreeGroup.mk s)⁻¹ * (FreeGroup.of x)⁻¹ * g⁻¹ = a * (FreeGroup.mk p * g⁻¹) := by
      rw [ha']; group
    rw [this]; exact J.mul_mem ha hm

/-- If both endpoints' transversal-like representatives avoid the edge, it is not a tree edge. -/
theorem not_tree (N : Subgroup (FreeGroup (Fin d))) (g : FreeGroup (Fin d)) (x : Fin d)
    (v0 : FreeGroup (Fin d)) (hv0 : v0 * g⁻¹ ∈ N) (h0 : nonCount (PE N g x) v0 = 0)
    (h1 : nonCount (PE N g x) (v0 * FreeGroup.of x) = 0) : False := by
  rw [nonCount_eq_zero_iff] at h0 h1
  by_cases hend : ∃ q, v0.toWord = q ++ [(x, false)]
  · obtain ⟨q, hq⟩ := hend
    have := h0 q [] (x, false) hq
    apply this
    refine ⟨?_, rfl⟩
    have h2 : FreeGroup.mk (q ++ [(x, false)]) = v0 := by rw [← hq, FreeGroup.mk_toWord]
    have : FreeGroup.mk q * (FreeGroup.of x)⁻¹ = v0 := by
      rw [← h2, ← FreeGroup.mul_mk, Puder.Q284.PartT.mk_letter]; rfl
    simpa [this] using hv0
  · have hred : (v0 * FreeGroup.of x).toWord = v0.toWord ++ [(x, true)] := by
      rw [FreeGroup.toWord_mul, FreeGroup.toWord_of]
      apply FreeGroup.IsReduced.reduce_eq
      unfold FreeGroup.IsReduced
      rw [List.isChain_append]
      refine ⟨FreeGroup.isReduced_toWord, List.isChain_singleton _, ?_⟩
      intro y hy z hz
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      subst hz
      intro hyx
      by_contra hb
      apply hend
      refine ⟨v0.toWord.dropLast, ?_⟩
      have hy' : y = (x, false) := Prod.ext hyx (by simpa using hb)
      subst hy'
      obtain ⟨hne, hlast⟩ := List.mem_getLast?_eq_getLast hy
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      rw [← hlast]
    have := h1 v0.toWord [] (x, true) hred
    apply this
    simpa [FreeGroup.mk_toWord] using hv0

/-- In a free group, `u * (of i)^{±1} * u'` with `u, u'` in the subgroup generated by the other
generators is the image of `of i` under an automorphism. -/
theorem exists_mulEquiv_of_mem {ι : Type*} (i : ι) (u u' c : FreeGroup ι)
    (hu : u ∈ Subgroup.closure (FreeGroup.of '' {j | j ≠ i}))
    (hu' : u' ∈ Subgroup.closure (FreeGroup.of '' {j | j ≠ i}))
    (hc : c = FreeGroup.of i ∨ c = (FreeGroup.of i)⁻¹) :
    ∃ φ : FreeGroup ι ≃* FreeGroup ι, φ (FreeGroup.of i) = u * c * u' := by
  classical
  let F : FreeGroup ι → (FreeGroup ι →* FreeGroup ι) := fun a =>
    FreeGroup.lift (fun j => if j = i then a else FreeGroup.of j)
  have hFi : ∀ a, F a (FreeGroup.of i) = a := fun a => by simp [F]
  have hFj : ∀ a j, j ≠ i → F a (FreeGroup.of j) = FreeGroup.of j := fun a j hj => by
    simp [F, hj]
  have hfix : ∀ a, ∀ s ∈ Subgroup.closure (FreeGroup.of '' {j | j ≠ i}), F a s = s := by
    intro a s hs
    have : Subgroup.closure (FreeGroup.of '' {j | j ≠ i}) ≤
        (F a).eqLocus (MonoidHom.id _) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      exact hFj a j hj
    exact this hs
  have build : ∀ a t, F a t = FreeGroup.of i → F t a = FreeGroup.of i →
      ∃ φ : FreeGroup ι ≃* FreeGroup ι, φ (FreeGroup.of i) = a := by
    intro a t h1 h2
    have e1 : ∀ y, F t (F a y) = y := by
      have : (F t).comp (F a) = MonoidHom.id _ := by
        ext j
        by_cases hj : j = i
        · subst hj; simp [hFi, h2]
        · simp [hFj _ _ hj]
      intro y; exact DFunLike.congr_fun this y
    have e2 : ∀ y, F a (F t y) = y := by
      have : (F a).comp (F t) = MonoidHom.id _ := by
        ext j
        by_cases hj : j = i
        · subst hj; simp [hFi, h1]
        · simp [hFj _ _ hj]
      intro y; exact DFunLike.congr_fun this y
    exact ⟨⟨⟨F a, F t, e1, e2⟩, (F a).map_mul⟩, hFi a⟩
  rcases hc with rfl | rfl
  · refine build _ (u⁻¹ * FreeGroup.of i * u'⁻¹) ?_ ?_
    · simp only [map_mul, map_inv, hFi, hfix _ u hu, hfix _ u' hu']; group
    · simp only [map_mul, hFi, hfix _ u hu, hfix _ u' hu']; group
  · refine build _ (u' * (FreeGroup.of i)⁻¹ * u) ?_ ?_
    · simp only [map_mul, map_inv, hFi, hfix _ u hu, hfix _ u' hu']; group
    · simp only [map_mul, map_inv, hFi, hfix _ u hu, hfix _ u' hu']; group

theorem list_prod_split {G : Type*} [Group G] (S : Subgroup G) (l : List G) (i : ℕ)
    (hi : i < l.length) (h : ∀ j (hj : j < l.length), j ≠ i → l[j] ∈ S) :
    ∃ u ∈ S, ∃ u' ∈ S, l.prod = u * l[i] * u' := by
  refine ⟨(l.take i).prod, ?_, (l.drop (i+1)).prod, ?_, ?_⟩
  · apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    rw [List.getElem_take]
    simp at hj
    exact h j (by omega) (by omega)
  · apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    rw [List.getElem_drop]
    simp at hj
    exact h _ (by omega) (by omega)
  · rw [← List.prod_take_mul_prod_drop l i, List.drop_eq_getElem_cons hi, List.prod_cons,
      mul_assoc]

theorem isPrimitiveIn_of_ncard_traverses_eq_one_dev (N : Subgroup (FreeGroup (Fin d))) (hN : N.FG)
    (w : FreeGroup (Fin d)) (hw : w ∈ N) (g : FreeGroup (Fin d)) (x : Fin d)
    (h1 : {i : ℕ | Traverses N w i g x}.ncard = 1) : IsPrimitiveIn N w := by
  classical
  obtain ⟨i0, hi0⟩ := Set.ncard_eq_one.mp h1
  have huniq : ∀ k, Traverses N w k g x ↔ k = i0 := fun k => by
    have := congrArg (k ∈ ·) hi0
    simpa using this
  set P := PE N g x with hPdef
  have hP : CosetInv N P := by
    intro g1 g2 z h12 hP1 hm
    apply hP1
    refine ⟨?_, hm.2⟩
    have := N.mul_mem h12 hm.1
    simpa [mul_assoc] using this
  obtain ⟨p, s, b, hwL, hplen, hmem⟩ := (huniq i0).mpr rfl
  have hlen : w.toWord.length = p.length + 1 + s.length := by rw [hwL]; simp; omega
  -- the two avoiders
  have hA1 : nonCount P (FreeGroup.mk p) = 0 :=
    avoid N g x hwL (fun k hk => by rw [huniq] at hk; omega)
  have hwinv : w⁻¹.toWord = FreeGroup.invRev s ++ (x, !b) :: FreeGroup.invRev p := by
    rw [FreeGroup.toWord_inv, hwL]; simp [FreeGroup.invRev]
  have hA2 : nonCount P (FreeGroup.mk (FreeGroup.invRev s)) = 0 := by
    refine avoid N g x hwinv (fun k hk => ?_)
    have hlt := traverses_lt_length N hk
    have := (huniq _).mp (traverses_inv_idx N hw hk)
    rw [hwinv] at hlt
    simp [FreeGroup.invRev_length] at hlt ⊢
    omega
  have hw' : w = FreeGroup.mk p * FreeGroup.mk [(x, b)] * FreeGroup.mk s := by
    rw [FreeGroup.mul_mk, FreeGroup.mul_mk, List.append_assoc, List.singleton_append, ← hwL,
      FreeGroup.mk_toWord]
  rw [Puder.Q284.PartT.mk_letter] at hw'
  have hs : FreeGroup.mk (FreeGroup.invRev s) = (FreeGroup.mk s)⁻¹ := (FreeGroup.inv_mk).symm
  have hcos : (∃ h, h * g⁻¹ ∈ N ∧ nonCount P h = 0) ∧
      ∃ h, h * (g * FreeGroup.of x)⁻¹ ∈ N ∧ nonCount P h = 0 := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hmem hw'
      refine ⟨⟨_, ?_, hA2⟩, ⟨_, ?_, hA1⟩⟩
      · have := N.mul_mem (N.inv_mem hw) hmem
        convert this using 1
        rw [hs, hw']; group
      · simpa [mul_assoc] using hmem
    · simp only [↓reduceIte] at hmem hw'
      refine ⟨⟨_, hmem, hA1⟩, ⟨_, ?_, hA2⟩⟩
      have := N.mul_mem (N.inv_mem hw) hmem
      convert this using 1
      rw [hs, hw']; group
  obtain ⟨⟨h1', hh1, hn1⟩, ⟨h2', hh2, hn2⟩⟩ := hcos
  have hg0 : nonCount P (tr N P g) = 0 := nonCount_tr_eq_zero N P hh1 hn1
  have hgx : nonCount P (tr N P (g * FreeGroup.of x)) = 0 := nonCount_tr_eq_zero N P hh2 hn2
  set v0 := tr N P g with hv0def
  have hv0g : v0 * g⁻¹ ∈ N := tr_mem N P g
  have htv0 : tr N P v0 = v0 := tr_congr N P hv0g
  have htvx : tr N P (v0 * FreeGroup.of x) ≠ v0 * FreeGroup.of x := by
    intro heq
    have : tr N P (v0 * FreeGroup.of x) = tr N P (g * FreeGroup.of x) :=
      tr_congr N P (by simpa [mul_assoc] using hv0g)
    rw [heq] at this
    rw [← this] at hgx
    exact not_tree N g x v0 hv0g hg0 hgx
  let e0 : Idx N P := ⟨(v0, x), htv0, htvx⟩
  obtain ⟨B, -, hrepr⟩ := exists_basis N P hP
  set S := Subgroup.closure (FreeGroup.of '' {e : Idx N P | e ≠ e0}) with hS
  have hi0len : i0 < w.toWord.length := by rw [hlen]; omega
  -- labels away from `i0`
  have hother : ∀ k : Fin w.toWord.length, k.1 ≠ i0 → stepLabel N P w k ∈ S := by
    intro k hk
    have hne : ∀ hc : tr N P (tr N P (vtx w.toWord k)) = tr N P (vtx w.toWord k) ∧
        tr N P (tr N P (vtx w.toWord k) * FreeGroup.of (w.toWord[k]).1) ≠
          tr N P (vtx w.toWord k) * FreeGroup.of (w.toWord[k]).1,
        (⟨(tr N P (vtx w.toWord k), (w.toWord[k]).1), hc⟩ : Idx N P) ≠ e0 := by
      intro hc heq
      have ha : tr N P (vtx w.toWord k) = v0 := congrArg (fun e : Idx N P => e.1.1) heq
      have hx : (w.toWord[k]).1 = x := congrArg (fun e : Idx N P => e.1.2) heq
      apply hk
      rw [← huniq]
      have hm : vtx w.toWord k * g⁻¹ ∈ N := by
        have h3 := tr_mem N P (vtx w.toWord k)
        rw [ha] at h3
        have := N.mul_mem (N.inv_mem h3) hv0g
        simpa [mul_assoc] using this
      have hx' : (w.toWord[k.1]).1 = x := by simpa using hx
      have hwk : w.toWord[k.1] = (x, (w.toWord[k.1]).2) := Prod.ext hx' rfl
      refine ⟨w.toWord.take k, w.toWord.drop (k + 1), (w.toWord[k.1]).2, ?_, by simp, ?_⟩
      · rw [← hwk, ← List.drop_eq_getElem_cons k.2, List.take_append_drop]
      · simpa [vtx, hx'] using hm
    unfold stepLabel
    split_ifs with hc hb
    · exact Subgroup.subset_closure ⟨_, hne hc, rfl⟩
    · exact S.inv_mem (Subgroup.subset_closure ⟨_, hne hc, rfl⟩)
    · exact S.one_mem
  -- the label at `i0`
  have hlab : stepLabel N P w ⟨i0, hi0len⟩ = FreeGroup.of e0 ∨
      stepLabel N P w ⟨i0, hi0len⟩ = (FreeGroup.of e0)⁻¹ := by
    have hget : w.toWord[i0] = (x, b) := by simp [hwL, ← hplen]
    have hvtx : vtx w.toWord ⟨i0, hi0len⟩ =
        if b then FreeGroup.mk p else FreeGroup.mk p * (FreeGroup.of x)⁻¹ := by
      simp [vtx, hwL, ← hplen]
    have ha0 : tr N P (vtx w.toWord ⟨i0, hi0len⟩) = v0 := by
      rw [hvtx]; exact tr_congr N P hmem
    have hlet : (w.toWord[(⟨i0, hi0len⟩ : Fin w.toWord.length)]).1 = x := by
      simp [hget]
    unfold stepLabel
    split_ifs with hc hb
    · left; congr 1; exact Subtype.ext (Prod.ext ha0 hlet)
    · right; congr 2; exact Subtype.ext (Prod.ext ha0 hlet)
    · exfalso; apply hc
      rw [ha0, hlet]
      exact ⟨htv0, htvx⟩
  set l := (List.finRange w.toWord.length).map (stepLabel N P w) with hl
  have hll : l.length = w.toWord.length := by simp [l]
  obtain ⟨u, hu, u', hu', hprod⟩ := list_prod_split S l i0 (by rw [hll]; exact hi0len)
    (fun j hj hji => by
      simp only [l, List.getElem_map, List.getElem_finRange]
      exact hother _ hji)
  have hli : l[i0]'(by rw [hll]; exact hi0len) = stepLabel N P w ⟨i0, hi0len⟩ := by
    simp [l]
  rw [hli] at hprod
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_mem e0 u u' _ hu hu' hlab
  refine ⟨Idx N P, FreeGroupBasis.ofRepr (B.repr.trans φ.symm), e0, ?_⟩
  show (((B.repr.trans φ.symm).symm (FreeGroup.of e0) : N) : FreeGroup (Fin d)) = w
  rw [MulEquiv.symm_trans_apply, MulEquiv.symm_symm, hφ, ← hprod, ← hrepr w hw]
  simp

end Puder.Q284S.PartS4
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
/-! ## Part S4: the last step of Lemma 4.1 -/
alias isPrimitiveIn_of_ncard_traverses_eq_one_dev := Puder.Q284S.PartS4.isPrimitiveIn_of_ncard_traverses_eq_one_dev

end Puder.Q284S
end

section
open Puder
open Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
theorem solution (N : Subgroup (FreeGroup (Fin d))) (hN : N.FG)
    (w : FreeGroup (Fin d)) (hw : w ∈ N) (g : FreeGroup (Fin d)) (x : Fin d)
    (h1 : {i : ℕ | Traverses N w i g x}.ncard = 1) : IsPrimitiveIn N w := by
  exact Puder.Q284S.isPrimitiveIn_of_ncard_traverses_eq_one_dev N hN w hw g x h1
end
