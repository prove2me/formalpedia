-- Prove2me | solution 1 for Puder.isFreeFactor_of_le_of_mem_of_traverses
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:27:58.535043+00:00
-- url     : https://prove2.me/submissions/20364889-88b0-4fb6-a30e-e37b4ec95b2f

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
/-- The walk of the (not necessarily reduced) list `L` from the coset `J` crosses the `x`-edge
leaving the coset `J g`. -/
def ListTraverses (J : Subgroup (FreeGroup (Fin d))) (L : List (Fin d × Bool))
    (g : FreeGroup (Fin d)) (x : Fin d) : Prop :=
  ∃ (p s : List (Fin d × Bool)) (b : Bool), L = p ++ (x, b) :: s ∧
    (if b then FreeGroup.mk p else FreeGroup.mk p * (FreeGroup.of x)⁻¹) * g⁻¹ ∈ J

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}
theorem exists_traverses_iff (J : Subgroup (FreeGroup (Fin d))) (w g : FreeGroup (Fin d))
    (x : Fin d) : (∃ i, Traverses J w i g x) ↔ ListTraverses J w.toWord g x := by
  constructor
  · rintro ⟨i, p, s, b, hw, -, hm⟩
    exact ⟨p, s, b, hw, hm⟩
  · rintro ⟨p, s, b, hw, hm⟩
    exact ⟨p.length, p, s, b, hw, rfl, hm⟩

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}
alias exists_traverses_iff := Puder.Q284.PartW.exists_traverses_iff

end Puder.Q284
end

section
namespace Puder.Q284.PartW
open Puder Puder.Q284
variable {d : ℕ}
theorem mk_cancel_pair (L₁ L₂ : List (Fin d × Bool)) (z : Fin d) (c : Bool) :
    FreeGroup.mk (L₁ ++ (z, c) :: (z, !c) :: L₂) = FreeGroup.mk (L₁ ++ L₂) :=
  Quot.sound FreeGroup.Red.Step.not

theorem listTraverses_of_step (J : Subgroup (FreeGroup (Fin d))) {L L' : List (Fin d × Bool)}
    (h : FreeGroup.Red.Step L L') (g : FreeGroup (Fin d)) (x : Fin d) :
    ListTraverses J L' g x → ListTraverses J L g x := by
  cases h with
  | @not L₁ L₂ z c =>
    rintro ⟨p, s, b, hL, hm⟩
    rcases List.append_eq_append_iff.mp hL with ⟨a', rfl, rfl⟩ | ⟨c', rfl, hc⟩
    · refine ⟨L₁ ++ (z, c) :: (z, !c) :: a', s, b, by simp, ?_⟩
      rwa [mk_cancel_pair]
    · rcases List.cons_eq_append_iff.mp hc with ⟨rfl, rfl⟩ | ⟨c'', rfl, rfl⟩
      · refine ⟨p ++ (z, c) :: (z, !c) :: [], s, b, by simp, ?_⟩
        rwa [mk_cancel_pair, List.append_nil]
      · exact ⟨p, c'' ++ (z, c) :: (z, !c) :: L₂, b, by simp, hm⟩

theorem listTraverses_of_red (J : Subgroup (FreeGroup (Fin d))) {L L' : List (Fin d × Bool)}
    (h : FreeGroup.Red L L') (g : FreeGroup (Fin d)) (x : Fin d) :
    ListTraverses J L' g x → ListTraverses J L g x := by
  induction h with
  | refl => exact id
  | tail _ hstep ih => exact fun h' => ih (listTraverses_of_step J hstep g x h')

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}
alias listTraverses_of_red := Puder.Q284.PartW.listTraverses_of_red

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

end Puder.Q284.PartW
end

section
namespace Puder.Q284
variable {d : ℕ}

end Puder.Q284
end

section
namespace Puder.Q284.PartT
open Puder Puder.Q284
variable {d : ℕ}

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
/-- The walk of the list `L` started at the coset `J a` crosses the `x`-edge leaving `J y`. -/
def LTF (J : Subgroup (FreeGroup (Fin d))) (a : FreeGroup (Fin d)) (L : List (Fin d × Bool))
    (y : FreeGroup (Fin d)) (x : Fin d) : Prop :=
  ∃ (p s : List (Fin d × Bool)) (b : Bool), L = p ++ (x, b) :: s ∧
    (if b then a * FreeGroup.mk p else a * FreeGroup.mk p * (FreeGroup.of x)⁻¹) * y⁻¹ ∈ J

theorem ltf_one (J : Subgroup (FreeGroup (Fin d))) (L : List (Fin d × Bool))
    (y : FreeGroup (Fin d)) (x : Fin d) : ListTraverses J L y x ↔ LTF J 1 L y x := by
  simp [ListTraverses, LTF]

theorem ltf_append (J : Subgroup (FreeGroup (Fin d))) (a : FreeGroup (Fin d))
    (L₁ L₂ : List (Fin d × Bool)) (y : FreeGroup (Fin d)) (x : Fin d) :
    LTF J a (L₁ ++ L₂) y x → LTF J a L₁ y x ∨ LTF J (a * FreeGroup.mk L₁) L₂ y x := by
  rintro ⟨p, s, b, hL, hm⟩
  rcases List.append_eq_append_iff.mp hL with ⟨a', rfl, rfl⟩ | ⟨c', rfl, hc⟩
  · refine Or.inr ⟨a', s, b, rfl, ?_⟩
    rw [← FreeGroup.mul_mk] at hm
    cases b <;> simpa only [mul_assoc, Bool.false_eq_true, if_true, if_false] using hm
  · rcases List.cons_eq_append_iff.mp hc with ⟨rfl, rfl⟩ | ⟨c'', rfl, rfl⟩
    · refine Or.inr ⟨[], s, b, rfl, ?_⟩
      simpa [← FreeGroup.one_eq_mk] using hm
    · exact Or.inl ⟨p, c'', b, by simp, hm⟩

theorem ltf_cons_true (J : Subgroup (FreeGroup (Fin d))) (a : FreeGroup (Fin d)) (x₀ : Fin d)
    (rest : List (Fin d × Bool)) (y : FreeGroup (Fin d)) (x : Fin d) :
    LTF J a ([(x₀, true)] ++ rest) y x →
      (x = x₀ ∧ a * y⁻¹ ∈ J) ∨ LTF J (a * FreeGroup.of x₀) rest y x := by
  intro h
  rcases ltf_append J a [(x₀, true)] rest y x h with ⟨p, s, b, hL, hm⟩ | h2
  · left
    cases p with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hL
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hL
      refine ⟨rfl, ?_⟩
      simpa [← FreeGroup.one_eq_mk] using hm
    | cons q p => simp at hL
  · exact Or.inr h2

theorem ltf_coset (J : Subgroup (FreeGroup (Fin d))) {a a' : FreeGroup (Fin d)}
    (L : List (Fin d × Bool)) (y : FreeGroup (Fin d)) (x : Fin d) (h : a' * a⁻¹ ∈ J) :
    LTF J a L y x → LTF J a' L y x := by
  rintro ⟨p, s, b, hL, hm⟩
  refine ⟨p, s, b, hL, ?_⟩
  have := J.mul_mem h hm
  cases b <;> simpa [mul_assoc] using this

theorem mk_false (x : Fin d) : FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ := by
  simp [FreeGroup.inv_mk, FreeGroup.invRev, FreeGroup.of]

theorem ltf_invRev (J : Subgroup (FreeGroup (Fin d))) (L : List (Fin d × Bool))
    (y : FreeGroup (Fin d)) (x : Fin d) :
    LTF J (FreeGroup.mk L) (FreeGroup.invRev L) y x → ListTraverses J L y x := by
  rintro ⟨p, s, b, hL, hm⟩
  have hL' : L = FreeGroup.invRev s ++ (x, !b) :: FreeGroup.invRev p := by
    have := congrArg FreeGroup.invRev hL
    rw [FreeGroup.invRev_invRev] at this
    rw [this]; simp [FreeGroup.invRev]
  refine ⟨FreeGroup.invRev s, FreeGroup.invRev p, !b, hL', ?_⟩
  have h1 : (FreeGroup.mk L)⁻¹ = FreeGroup.mk p * FreeGroup.mk [(x, b)] * FreeGroup.mk s := by
    rw [FreeGroup.inv_mk, hL, FreeGroup.mul_mk, FreeGroup.mul_mk]; simp
  have h2 : FreeGroup.mk L = (FreeGroup.mk s)⁻¹ * (FreeGroup.mk [(x, b)])⁻¹ * (FreeGroup.mk p)⁻¹ := by
    rw [← inv_inv (FreeGroup.mk L), h1]; group
  rw [h2] at hm
  rw [← FreeGroup.inv_mk]
  cases b
  · rw [mk_false] at hm
    simp only [Bool.not_false, Bool.false_eq_true, if_true, if_false] at hm ⊢
    convert hm using 1
    group
  · have hx : FreeGroup.mk [(x, true)] = FreeGroup.of x := rfl
    rw [hx] at hm
    simp only [Bool.not_true, Bool.false_eq_true, if_true, if_false] at hm ⊢
    convert hm using 1
    group

theorem listTraverses_iff (J : Subgroup (FreeGroup (Fin d))) (L : List (Fin d × Bool))
    (y : FreeGroup (Fin d)) (x : Fin d) :
    ListTraverses J L y x ↔ ∃ k : Fin L.length, (L[k]).1 = x ∧ vtx L k * y⁻¹ ∈ J := by
  constructor
  · rintro ⟨p, s, b, rfl, hm⟩
    refine ⟨⟨p.length, by simp⟩, by simp, ?_⟩
    simpa [vtx] using hm
  · rintro ⟨k, rfl, hm⟩
    refine ⟨L.take k, L.drop (k + 1), (L[k]).2, ?_, ?_⟩
    · rw [Prod.mk.eta, Fin.getElem_fin, ← List.drop_eq_getElem_cons, List.take_append_drop]
    · simpa [vtx] using hm

theorem forall_of_nonCount (P : FreeGroup (Fin d) → Fin d → Prop) (g : FreeGroup (Fin d))
    (h0 : nonCount P g = 0) (k : Fin g.toWord.length) : P (vtx g.toWord k) (g.toWord[k]).1 := by
  classical
  unfold nonCount at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  by_contra hc
  exact h0 (Finset.mem_univ k) hc

theorem nonCount_eq_zero_of (P : FreeGroup (Fin d) → Fin d → Prop) (g : FreeGroup (Fin d))
    (h : ∀ k : Fin g.toWord.length, P (vtx g.toWord k) (g.toWord[k]).1) : nonCount P g = 0 := by
  classical
  unfold nonCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _ hc
  exact hc (h k)

theorem forall_of_prefix (P : FreeGroup (Fin d) → Fin d → Prop) {L M t : List (Fin d × Bool)}
    (hall : ∀ k : Fin L.length, P (vtx L k) (L[k]).1) (ht : M ++ t = L) :
    ∀ k : Fin M.length, P (vtx M k) (M[k]).1 := by
  subst ht
  intro k
  have hk := hall ⟨k, by simp; omega⟩
  have e1 : (M ++ t)[(k : ℕ)] = M[(k : ℕ)] := List.getElem_append_left k.2
  have e2 : (M ++ t).take k = M.take k := List.take_append_of_le_length (le_of_lt k.2)
  simp only [vtx, Fin.getElem_fin, e1, e2] at hk ⊢
  exact hk

theorem isFreeFactor_of_le_of_mem_of_traverses_dev (H J : Subgroup (FreeGroup (Fin d)))
    (hHJ : H ≤ J)
    (hmem : ∀ g ∈ J, (∀ (i : ℕ) (y : FreeGroup (Fin d)) (x : Fin d), Traverses J g i y x →
        ∃ h ∈ H, ∃ j : ℕ, Traverses J h j y x) → g ∈ H) :
    IsFreeFactor H J := by
  set Q : FreeGroup (Fin d) → Fin d → Prop := fun y x => ∃ h ∈ H, ∃ j : ℕ, Traverses J h j y x
    with hQdef
  have hQinv : CosetInv J Q := by
    rintro g g' x hgg ⟨h, hh, j, p, s, c, hw, hl, hm⟩
    refine ⟨h, hh, j, p, s, c, hw, hl, ?_⟩
    have := J.mul_mem hm hgg
    cases c <;> simpa [mul_assoc] using this
  obtain ⟨b, hb, hrepr⟩ := exists_basis J Q hQinv
  have hQwalk : ∀ h ∈ H, ∀ k : Fin h.toWord.length, Q (vtx h.toWord k) (h.toWord[k]).1 := by
    intro h hh k
    exact ⟨h, hh, (exists_traverses_iff J h _ _).mpr
      ((listTraverses_iff J _ _ _).mpr ⟨k, rfl, by simp⟩)⟩
  have hgood : ∀ g, nonCount Q g = 0 → ∀ y x, ListTraverses J g.toWord y x → Q y x := by
    intro g hg y x htr
    obtain ⟨k, rfl, hk⟩ := (listTraverses_iff J _ _ _).mp htr
    exact hQinv _ _ _ hk (forall_of_nonCount Q g hg k)
  have hpre : ∀ h ∈ H, ∀ n, nonCount Q (FreeGroup.mk (h.toWord.take n)) = 0 := by
    intro h hh n
    apply nonCount_eq_zero_of
    have hred : (FreeGroup.mk (h.toWord.take n)).toWord = h.toWord.take n := by
      rw [FreeGroup.toWord_mk]
      exact (FreeGroup.isReduced_toWord.infix (List.take_prefix n _).isInfix).reduce_eq
    have ht : (FreeGroup.mk (h.toWord.take n)).toWord ++ h.toWord.drop n = h.toWord := by
      rw [hred, List.take_append_drop]
    exact forall_of_prefix Q (hQwalk h hh) ht
  refine ⟨Idx J Q, b, {e | Q e.1.1 e.1.2}, le_antisymm ?_ ?_⟩
  · -- `H ≤ closure`
    intro h hh
    have hJ := hHJ hh
    have hw : b.repr ⟨h, hJ⟩ ∈ Subgroup.closure (FreeGroup.of '' {e : Idx J Q | Q e.1.1 e.1.2}) := by
      rw [hrepr h hJ]
      apply Subgroup.list_prod_mem
      intro z hz
      simp only [List.mem_map, List.mem_finRange, true_and] at hz
      obtain ⟨k, rfl⟩ := hz
      have hS : Q (tr J Q (vtx h.toWord k)) (h.toWord[k]).1 := by
        refine hQinv _ _ _ ?_ (hQwalk h hh k)
        have := J.inv_mem (tr_mem J Q (vtx h.toWord k))
        rwa [mul_inv_rev, inv_inv] at this
      unfold stepLabel
      split_ifs with h1 h2
      · exact Subgroup.subset_closure ⟨_, hS, rfl⟩
      · exact inv_mem (Subgroup.subset_closure ⟨_, hS, rfl⟩)
      · exact one_mem _
    have key : ∀ w ∈ Subgroup.closure (FreeGroup.of '' {e : Idx J Q | Q e.1.1 e.1.2}),
        ((b.repr.symm w : J) : FreeGroup (Fin d)) ∈
          Subgroup.closure ((fun i => (b i : FreeGroup (Fin d))) '' {e : Idx J Q | Q e.1.1 e.1.2}) := by
      intro w hw'
      induction hw' using Subgroup.closure_induction with
      | mem w hw'' =>
        obtain ⟨e, he, rfl⟩ := hw''
        exact Subgroup.subset_closure ⟨e, he, rfl⟩
      | one => simp
      | mul u v _ _ hu hv =>
        rw [map_mul, Subgroup.coe_mul]; exact mul_mem hu hv
      | inv u _ hu =>
        rw [map_inv, Subgroup.coe_inv]; exact inv_mem hu
    simpa using key _ hw
  · -- `closure ≤ H`
    rw [Subgroup.closure_le]
    rintro _ ⟨e, heQ, rfl⟩
    rw [SetLike.mem_coe]; show (b e : FreeGroup (Fin d)) ∈ H; rw [hb e]
    revert heQ
    obtain ⟨⟨v, x⟩, hvt, hne⟩ := e
    intro heQ
    change Q v x at heQ
    change tr J Q v = v at hvt
    simp only [basisElt]
    set v' := tr J Q (v * FreeGroup.of x) with hv'
    -- both endpoints have walks inside `Q`
    have hends : nonCount Q v = 0 ∧ nonCount Q v' = 0 := by
      obtain ⟨h, hh, j, q, s, c, hw, -, hm⟩ := heQ
      have N0 : nonCount Q (FreeGroup.mk q) = 0 := by
        have := hpre h hh q.length
        rwa [hw, List.take_left'] at this
        rfl
      have N1 : nonCount Q (FreeGroup.mk q * FreeGroup.mk [(x, c)]) = 0 := by
        have := hpre h hh (q.length + 1)
        rw [FreeGroup.mul_mk]
        convert this using 3
        rw [hw]
        clear this hw N0 hm
        induction q with
        | nil => rfl
        | cons a q ih => simp [ih]
      cases c
      · rw [mk_false] at N1
        simp only [Bool.false_eq_true, if_false] at hm
        refine ⟨?_, nonCount_tr_eq_zero J Q (h := FreeGroup.mk q) ?_ N0⟩
        · have := nonCount_tr_eq_zero J Q (g := v) hm N1
          rwa [hvt] at this
        · simpa [mul_assoc] using hm
      · have hx : FreeGroup.mk [(x, true)] = FreeGroup.of x := rfl
        rw [hx] at N1
        simp only [if_true] at hm
        refine ⟨?_, nonCount_tr_eq_zero J Q (h := FreeGroup.mk q * FreeGroup.of x) ?_ N1⟩
        · have := nonCount_tr_eq_zero J Q (g := v) hm N0
          rwa [hvt] at this
        · simpa [mul_assoc] using hm
    have hgJ : v * FreeGroup.of x * v'⁻¹ ∈ J := by
      have := J.inv_mem (tr_mem J Q (v * FreeGroup.of x))
      rwa [mul_inv_rev, inv_inv] at this
    apply hmem _ hgJ
    intro i y x' htr
    have h1 := (exists_traverses_iff J _ y x').mp ⟨i, htr⟩
    have hgM : (v * FreeGroup.of x * v'⁻¹).toWord =
        FreeGroup.reduce (v.toWord ++ ([(x, true)] ++ (v'⁻¹).toWord)) := by
      rw [← FreeGroup.toWord_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, FreeGroup.mk_toWord,
        FreeGroup.mk_toWord, mul_assoc]
      rfl
    rw [hgM] at h1
    have h2 := listTraverses_of_red J FreeGroup.reduce.red y x' h1
    rw [ltf_one] at h2
    rcases ltf_append J 1 _ _ y x' h2 with h3 | h3
    · exact hgood v hends.1 y x' ((ltf_one J _ y x').mpr h3)
    · rcases ltf_cons_true J _ x _ y x' h3 with ⟨rfl, hy⟩ | h4
      · exact hQinv v y x' (by simpa [FreeGroup.mk_toWord] using hy) heQ
      · rw [FreeGroup.toWord_inv] at h4
        have h5 := ltf_coset J (a' := FreeGroup.mk v'.toWord) _ y x' (by
          have := tr_mem J Q (v * FreeGroup.of x)
          simpa [FreeGroup.mk_toWord, mul_assoc] using this) h4
        exact hgood v' hends.2 y x' (ltf_invRev J _ y x' h5)

end Puder.Q284S.PartS3
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
/-! ## Part S3: Claim 3.3(4) -/
alias isFreeFactor_of_le_of_mem_of_traverses_dev := Puder.Q284S.PartS3.isFreeFactor_of_le_of_mem_of_traverses_dev

end Puder.Q284S
end

section
namespace Puder.Q284S.PartS4
open Puder Puder.Q284 Puder.Q284S
variable {d : ℕ}

end Puder.Q284S.PartS4
end

section
namespace Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
/-! ## Part S4: the last step of Lemma 4.1 -/

end Puder.Q284S
end

section
open Puder
open Puder.Q284S
open Puder Puder.Q284
variable {d : ℕ}
theorem solution (H J : Subgroup (FreeGroup (Fin d)))
    (hHJ : H ≤ J)
    (hmem : ∀ g ∈ J, (∀ (i : ℕ) (y : FreeGroup (Fin d)) (x : Fin d), Traverses J g i y x →
        ∃ h ∈ H, ∃ j : ℕ, Traverses J h j y x) → g ∈ H) :
    IsFreeFactor H J := by
  exact Puder.Q284S.isFreeFactor_of_le_of_mem_of_traverses_dev H J hHJ hmem
end
