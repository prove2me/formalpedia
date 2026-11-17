-- Prove2me | solution 1 for RandomInvolutions.norm_sum_c2count_mul_trace_Bprod_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T11:49:28.945919+00:00
-- url     : https://prove2.me/submissions/4719bf74-a800-4bd0-99e0-af4eacdd61da

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_ZigZagStrong_ZigZag_Models
import Definitions.Def_RandomInvolutions

section
/-!
# Strong convergence of uniform random involutions: definitions

Shared definitions for the proof of `ZigZagStrong.ZigZag.involution_strong_convergence`.
NEVER EDIT (the Blueprint and all Parts build on this file).

The group is `Γ_r = Z₂^{*r}`, in the encoding `BordenaveCollins.G 0 r` (no free generators, `r`
involutions `m_i = genL (Sum.inr i)`), so that the published Bordenave–Collins statements
(`exists_linearization`, `norm_sum_cfun_mul_trace_Bprod_le`, `tendsto_expFix`,
`tendsto_re_trTau_pow_rpow`) apply verbatim with `r := 0`, `s := r`.

* `homI τ : G 0 r →* Perm (Fin N)` for a tuple of involutions `τ`.
* The conditional model `OmK r N κ`: the `i`-th involution has exactly `κ i` fixed points;
  admissible sizes `AdmK N κ` (`κ i ≤ N`, `κ i ≡ N mod 2`), the filter `admF κ` of admissible
  sizes, the weight `lam κ = 1 + ∑ κ i`.
* Expected fixed points `expFixOn`, `expFixK`; the compressed model operator `perpOp`; the
  spectral functional `specE` of any finite family of representations.
* Colourings with loops of the closed path of a word, and their weights `wtF`, `wtK`.
* The coefficient counts `Bcount` (conjugates of `m_i`) and `C2count` (the two-loop shapes
  `a (ρ m_j ρ⁻¹ σ m_i σ⁻¹)^t a⁻¹`).
* `toAlg`: a scalar `*`-polynomial as an element of the group algebra.
-/

open Finset BordenaveCollins

noncomputable section

namespace RandomInvolutions.Dev

/-! ## The group `Γ_r = G 0 r` and its words -/

/-- The inverse letter. -/
def bar {r s : ℕ} : Lt r s → Lt r s
  | Sum.inl (i, b) => Sum.inl (i, !b)
  | Sum.inr j => Sum.inr j

/-- A reduced word: no letter is followed by its inverse. -/
def Red {r s : ℕ} (u : List (Lt r s)) : Prop := u.IsChain (fun a b => b ≠ bar a)

/-! ## Involutions and the representation they define -/

/-! ## The conditional model `M(N, κ)` -/

/-! ## Expected fixed points -/

/-! ## Operators -/

/-! ## Colourings with loops of the closed path of a word

A path is `x : Fin (u.length + 1) → α` with `x t = letter_t (x (t+1))` (so that
`x t = wordPermI τ (u.drop t) y`). Step `t` with letter `m_i` is a *loop* of colour `i` at
`x t` when `x t = x (t+1)` (that vertex is fixed by `τ_i`), and a *pair* `{x t, x (t+1)}` of
`τ_i` otherwise. -/

/-! ## The coefficient counts -/

/-! ## Scalar polynomials as group-algebra elements -/

end RandomInvolutions.Dev

end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartX
variable {r : ℕ}
/-!
# Part X: mixing over the fixed-point counts

* `mixture`: the uniform law on tuples of involutions is the mixture of the conditional models.
* `fixCount_exp_le`: `E[#fix] ≤ √N + 1`. In fact `E[#fix²] = N` exactly (`sum_fix_sq`): multiplying
  by the transposition `(x y)` is a bijection between involutions fixing `x ≠ y` and involutions
  swapping them, so `E[f (f - 1)] = E[N - f]`; then Cauchy–Schwarz gives `E[#fix] ≤ √N`.
* `mix_affine`: a conditional bound `a * lam κ + b` integrates to `a (1 + r (√N + 1)) + b`.
* `expFix_unif_le`, `upper_unif`.
-/
abbrev Inv (N : ℕ) := ZigZagStrong.ZigZag.Involution N

/-! ## Generic finite probability -/

/-! ## The mixture -/

end RandomInvolutions.Dev.PartX
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartX
variable {r : ℕ}
/-! ## The second moment of the number of fixed points -/

instance (N : ℕ) : Nonempty (Inv N) := ⟨⟨1, fun _ => rfl⟩⟩

end RandomInvolutions.Dev.PartX
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-!
# Part F, toolkit: normal forms in `F_r * Γ_s` (van der Waerden's trick) and reduced words

Stated for `G r s`, `Lt r s` with the `RandomInvolutions.Dev` versions of `bar`, `Red`, `CycRed`; Part F uses it at
`G 0 r`.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## Aliases -/

/-! ## Generic group identities

(`simp`, `rw` and `group` do not see through the instance path of `G r s`, so identities are
proved in a generic group and applied with `exact`.) -/

/-! ## The inverse word -/
/-- The inverse word: reversed, with `bar` applied. -/
def ibar (u : List (Lt r s)) : List (Lt r s) := (u.map bar).reverse

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
@[simp] theorem ibar_nil : ibar ([] : List (Lt r s)) = [] := rfl

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
@[simp] theorem length_ibar (u : List (Lt r s)) : (ibar u).length = u.length := by simp [ibar]

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-! ## Repeated words -/
/-- `Z` repeated `k` times. -/
def rep (Z : List (Lt r s)) (k : ℕ) : List (Lt r s) := (List.replicate k Z).flatten

@[simp] theorem rep_zero (Z : List (Lt r s)) : rep Z 0 = [] := by simp [rep]

theorem rep_succ (Z : List (Lt r s)) (k : ℕ) : rep Z (k + 1) = Z ++ rep Z k := by
  simp [rep, List.replicate_succ]

@[simp] theorem rep_nil (k : ℕ) : rep ([] : List (Lt r s)) k = [] := by simp [rep]

@[simp] theorem length_rep (Z : List (Lt r s)) (k : ℕ) : (rep Z k).length = k * Z.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, List.length_append, ih]; ring

end RandomInvolutions.Dev.PartF
end
end

section
open Finset
noncomputable section
namespace RandomInvolutions.Dev.PartP3a.F1
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r s : ℕ}
/-!
# Part P3a, module 0: normal forms in `F_r * Γ_s` (van der Waerden's trick)

Copy of bc214's Part F1 (general `G r s`), so that the first-passage modules below do not depend
on the Part F stubs.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## The stubs -/

end RandomInvolutions.Dev.PartP3a.F1
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3a
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r₀ s₀ : ℕ}
/-!
# Part P2, module 1: normal forms, word lengths, involutions, balls

Everything here is derived from the Part F stubs `BordenaveCollins.nf_exists` and `BordenaveCollins.genL_bar`.
-/

/-! ### Bridging lemmas (the `Inv` instance of `Monoid.Coprod` is not syntactically the group one) -/

/-! ### Products of optional letters -/

/-! ### Lengths -/

/-! ### Inverse words -/

/-! ### Involutions -/

/-! ### Balls -/

end RandomInvolutions.Dev.PartP3a
end
end

section
open Finset
noncomputable section
namespace RandomInvolutions.Dev.PartP3b.F1
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r s : ℕ}
/-!
# Part P3a, module 0: normal forms in `F_r * Γ_s` (van der Waerden's trick)

Copy of bc214's Part F1 (general `G r s`), so that the first-passage modules below do not depend
on the Part F stubs.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem push_of_red_cons {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) :
    push a t = a :: t := by
  cases t with
  | nil => rfl
  | cons b t => exact push_cons_ne _ _ _ (red_cons_cons.1 h).1

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

theorem red_nf (g : G r s) : Red (nf g) := (hom r s g ⟨[], red_nil⟩).2

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem hom_wprod_nil (u : List (Lt r s)) (hu : Red u) :
    hom r s (wprod u) ⟨[], red_nil⟩ = ⟨u, hu⟩ := by
  induction u with
  | nil => simp
  | cons a t ih =>
    apply Subtype.ext
    rw [wprod_cons, hom_genL_mul, ih (Red.tail' hu)]
    exact push_of_red_cons hu

theorem nf_wprod (u : List (Lt r s)) (hu : Red u) : nf (wprod u) = u :=
  congrArg Subtype.val (hom_wprod_nil u hu)

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## The stubs -/
theorem nf_exists (r s : ℕ) : ∃ nf : G r s → List (Lt r s),
    (∀ g, Red (nf g)) ∧ (∀ g, wprod (nf g) = g) ∧ (∀ u, Red u → nf (wprod u) = u) ∧
      ∀ g, len g = (nf g).length :=
  ⟨nf, red_nf, wprod_nf, nf_wprod, len_eq_length_nf⟩

end RandomInvolutions.Dev.PartP3b.F1
end
end

section
open Finset
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
/-- Reduced words are a normal form, and `len` is the length of the reduced word (general
`G r s`). -/
theorem nf_exists (r s : ℕ) : ∃ nf : G r s → List (Lt r s),
    (∀ g, Red (nf g)) ∧ (∀ g, wprod (nf g) = g) ∧ (∀ u, Red u → nf (wprod u) = u) ∧
      ∀ g, len g = (nf g).length :=
  F1.nf_exists r s

theorem genL_bar {r s : ℕ} (a : Lt r s) : genL (bar a) = (genL a)⁻¹ :=
  F1.genL_bar a

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r₀ s₀ : ℕ}
/-!
# Part P2, module 1: normal forms, word lengths, involutions, balls

Everything here is derived from the Part F stubs `BordenaveCollins.nf_exists` and `BordenaveCollins.genL_bar`.
-/
/-- Optional letters. -/
abbrev Lo (r₀ s₀ : ℕ) := Option (Lt r₀ s₀)

/-- The normal form (a choice from `nf_exists`). -/
def nf (g : G r₀ s₀) : List (Lt r₀ s₀) := Classical.choose (nf_exists r₀ s₀) g

lemma nf_red (g : G r₀ s₀) : Red (nf g) := (Classical.choose_spec (nf_exists r₀ s₀)).1 g

lemma wprod_nf (g : G r₀ s₀) : wprod (nf g) = g := (Classical.choose_spec (nf_exists r₀ s₀)).2.1 g

lemma nf_wprod (u : List (Lt r₀ s₀)) (h : Red u) : nf (wprod u) = u :=
  (Classical.choose_spec (nf_exists r₀ s₀)).2.2.1 u h

lemma len_eq (g : G r₀ s₀) : len g = (nf g).length :=
  (Classical.choose_spec (nf_exists r₀ s₀)).2.2.2 g

/-! ### Bridging lemmas (the `Inv` instance of `Monoid.Coprod` is not syntactically the group one) -/
lemma g_mul_inv_rev (a b : G r₀ s₀) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b

lemma g_mul_inv_cancel (a : G r₀ s₀) : a * a⁻¹ = 1 := mul_inv_cancel a

lemma g_inv_mul_cancel (a : G r₀ s₀) : a⁻¹ * a = 1 := inv_mul_cancel a

lemma g_inv_inv (a : G r₀ s₀) : a⁻¹⁻¹ = a := inv_inv a

lemma g_mul_inv_cancel_left (a b : G r₀ s₀) : a * (a⁻¹ * b) = b := mul_inv_cancel_left a b

lemma g_inv_mul_cancel_left (a b : G r₀ s₀) : a⁻¹ * (a * b) = b := inv_mul_cancel_left a b

lemma g_inv_inj {a b : G r₀ s₀} (h : a⁻¹ = b⁻¹) : a = b := by
  rw [← g_inv_inv a, h, g_inv_inv]

lemma g_inv_mul_eq_one {a b : G r₀ s₀} : a⁻¹ * b = 1 ↔ a = b := by
  constructor
  · intro h
    have := g_mul_inv_cancel_left a b
    rw [h, mul_one] at this
    exact this
  · rintro rfl; exact g_inv_mul_cancel a

lemma g_mul_eq_iff {a b c : G r₀ s₀} : a * b = c ↔ b = a⁻¹ * c := by
  constructor
  · rintro rfl; rw [g_inv_mul_cancel_left]
  · rintro rfl; rw [g_mul_inv_cancel_left]

lemma g_mul_inv_cancel_right (a b : G r₀ s₀) : a * b * b⁻¹ = a := by
  rw [mul_assoc, g_mul_inv_cancel, mul_one]

lemma g_mul_right_cancel {a b c : G r₀ s₀} (h : a * c = b * c) : a = b := by
  rw [← g_mul_inv_cancel_right a c, h, g_mul_inv_cancel_right]

lemma g_mul_eq_right {a b : G r₀ s₀} : a * b = b ↔ a = 1 := by
  constructor
  · intro h
    rw [← g_mul_inv_cancel_right a b, h, g_mul_inv_cancel]
  · rintro rfl; exact one_mul b

lemma wprod_nil : wprod ([] : List (Lt r₀ s₀)) = 1 := by simp [wprod]

lemma wprod_cons (a : Lt r₀ s₀) (u : List (Lt r₀ s₀)) : wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

lemma wprod_append (u v : List (Lt r₀ s₀)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

lemma wprod_singleton (a : Lt r₀ s₀) : wprod [a] = genL a := by simp [wprod]

lemma bar_bar (a : Lt r₀ s₀) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

lemma red_nil : Red ([] : List (Lt r₀ s₀)) := List.IsChain.nil

lemma red_singleton (a : Lt r₀ s₀) : Red [a] := List.isChain_singleton a

lemma red_cons_cons (a b : Lt r₀ s₀) (l : List (Lt r₀ s₀)) :
    Red (a :: b :: l) ↔ b ≠ bar a ∧ Red (b :: l) := List.isChain_cons_cons

lemma nf_one : nf (1 : G r₀ s₀) = [] := by
  have := nf_wprod ([] : List (Lt r₀ s₀)) red_nil
  rwa [wprod_nil] at this

lemma nf_eq_nil {g : G r₀ s₀} : nf g = [] ↔ g = 1 :=
  ⟨fun h => by rw [← wprod_nf g, h, wprod_nil], fun h => by rw [h, nf_one]⟩

lemma nf_genL (x : Lt r₀ s₀) : nf (genL x) = [x] := by
  have := nf_wprod [x] (red_singleton x)
  rwa [wprod_singleton] at this

lemma len_le_length (u : List (Lt r₀ s₀)) : len (wprod u) ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, rfl⟩

lemma len_one : len (1 : G r₀ s₀) = 0 := by rw [len_eq, nf_one]; rfl

lemma len_genL (x : Lt r₀ s₀) : len (genL x) = 1 := by rw [len_eq, nf_genL]; rfl

lemma nf_genL_mul (x : Lt r₀ s₀) (T : G r₀ s₀) :
    nf (genL x * T) <:+ nf T ∨ nf (genL x * T) = x :: nf T := by
  rcases hu : nf T with _ | ⟨y, tl⟩
  · right
    have hT : T = 1 := nf_eq_nil.mp hu
    rw [hT, mul_one, nf_genL]
  · have hT : wprod (y :: tl) = T := by rw [← hu, wprod_nf]
    have hred0 : Red (y :: tl) := by rw [← hu]; exact nf_red T
    by_cases hy : y = bar x
    · left
      have hred : Red tl := List.IsChain.tail hred0
      have : genL x * T = wprod tl := by
        rw [← hT, wprod_cons, hy, genL_bar, g_mul_inv_cancel_left]
      rw [this, nf_wprod tl hred]; exact List.suffix_cons _ _
    · right
      have hred : Red (x :: y :: tl) := (red_cons_cons _ _ _).mpr ⟨hy, hred0⟩
      have := nf_wprod _ hred
      rwa [wprod_cons, hT] at this

lemma nf_genO_mul (a : Lo r₀ s₀) (T : G r₀ s₀) :
    nf (genO a * T) <:+ nf T ∨ ∃ p, nf (genO a * T) = p :: nf T := by
  rcases a with _ | x
  · left
    have : genO (none : Lo r₀ s₀) = 1 := rfl
    rw [this, one_mul]
  · rcases nf_genL_mul x T with h | h
    · exact Or.inl h
    · exact Or.inr ⟨x, h⟩

/-! ### Products of optional letters -/
/-- The group element of a list of optional letters. -/
def iprodL (w : List (Lo r₀ s₀)) : G r₀ s₀ := (w.map genO).prod

lemma iprodL_nil : iprodL ([] : List (Lo r₀ s₀)) = 1 := by simp [iprodL]

lemma iprodL_cons (a : Lo r₀ s₀) (w : List (Lo r₀ s₀)) :
    iprodL (a :: w) = genO a * iprodL w := by simp [iprodL]

lemma iprodL_append (w w' : List (Lo r₀ s₀)) :
    iprodL (w ++ w') = iprodL w * iprodL w' := by simp [iprodL]

lemma iprod_eq {m : ℕ} (i : Fin m → Lo r₀ s₀) : iprod i = iprodL (List.ofFn i) := by
  simp only [iprod, iprodL, List.map_ofFn]
  rfl

theorem walk_hit (v : G r₀ s₀) : ∀ w : List (Lo r₀ s₀),
    nf v <:+ nf (iprodL w) → ∃ l, l ≤ w.length ∧ iprodL (w.drop l) = v := by
  intro w
  induction w with
  | nil =>
    intro h
    refine ⟨0, le_rfl, ?_⟩
    rw [iprodL_nil, nf_one] at h
    have := List.eq_nil_of_suffix_nil h
    simpa [iprodL_nil] using (nf_eq_nil.mp this).symm
  | cons a w ih =>
    intro h
    by_cases hs : nf v <:+ nf (iprodL w)
    · obtain ⟨l, hl, hv⟩ := ih hs
      exact ⟨l + 1, by simp; omega, by simpa using hv⟩
    · refine ⟨0, by simp, ?_⟩
      rw [iprodL_cons] at h
      rcases nf_genO_mul a (iprodL w) with h1 | ⟨p, hp⟩
      · exact absurd (h.trans h1) hs
      · rw [hp] at h
        rcases List.suffix_cons_iff.mp h with h2 | h2
        · simp only [List.drop_zero, iprodL_cons]
          rw [← wprod_nf v, h2, ← hp, wprod_nf]
        · exact absurd h2 hs

/-! ### Lengths -/
lemma exists_shorter : ∀ u : List (Lt r₀ s₀), ¬ Red u →
    ∃ u' : List (Lt r₀ s₀), u'.length < u.length ∧ wprod u' = wprod u
  | [], h => absurd red_nil h
  | [a], h => absurd (red_singleton a) h
  | a :: b :: l, h => by
    by_cases hb : b = bar a
    · refine ⟨l, by simp only [List.length_cons]; omega, ?_⟩
      rw [wprod_cons, wprod_cons, hb, genL_bar, g_mul_inv_cancel_left]
    · have h' : ¬ Red (b :: l) := fun h2 => h ((red_cons_cons _ _ _).mpr ⟨hb, h2⟩)
      obtain ⟨u', h1, h2⟩ := exists_shorter (b :: l) h'
      exact ⟨a :: u', by simpa using h1, by rw [wprod_cons, wprod_cons a, h2]⟩

lemma nf_of_length_le (u : List (Lt r₀ s₀)) (h : u.length ≤ len (wprod u)) :
    nf (wprod u) = u := by
  apply nf_wprod
  by_contra hr
  obtain ⟨u', h1, h2⟩ := exists_shorter u hr
  have := len_le_length u'
  rw [h2] at this
  omega

lemma len_mul_le (x y : G r₀ s₀) : len (x * y) ≤ len x + len y := by
  have := len_le_length (nf x ++ nf y)
  rwa [wprod_append, wprod_nf, wprod_nf, List.length_append, ← len_eq, ← len_eq] at this

lemma nf_mul_of_len (x y : G r₀ s₀) (h : len (x * y) = len x + len y) :
    nf (x * y) = nf x ++ nf y := by
  have := nf_of_length_le (nf x ++ nf y)
    (by rw [wprod_append, wprod_nf, wprod_nf, List.length_append, ← len_eq, ← len_eq, h])
  rwa [wprod_append, wprod_nf, wprod_nf] at this

lemma len_prod_le : ∀ xs : List (G r₀ s₀), len xs.prod ≤ (xs.map len).sum
  | [] => by simp [len_one]
  | x :: xs => by
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    exact (len_mul_le _ _).trans (Nat.add_le_add_left (len_prod_le xs) _)

theorem nf_prod : ∀ xs : List (G r₀ s₀), len xs.prod = (xs.map len).sum →
    nf xs.prod = (xs.map nf).flatten
  | [], _ => by simp [nf_one]
  | x :: xs, h => by
    simp only [List.prod_cons, List.map_cons, List.sum_cons, List.flatten_cons] at h ⊢
    have h1 := len_mul_le x xs.prod
    have h2 := len_prod_le xs
    rw [nf_mul_of_len x xs.prod (by omega), nf_prod xs (by omega)]

/-! ### Inverse words -/
/-- The inverse word. -/
def ibar (u : List (Lt r₀ s₀)) : List (Lt r₀ s₀) := (u.map bar).reverse

lemma ibar_nil : ibar ([] : List (Lt r₀ s₀)) = [] := rfl

lemma ibar_cons (a : Lt r₀ s₀) (u : List (Lt r₀ s₀)) : ibar (a :: u) = ibar u ++ [bar a] := by
  simp [ibar]

lemma ibar_length (u : List (Lt r₀ s₀)) : (ibar u).length = u.length := by simp [ibar]

lemma wprod_ibar (u : List (Lt r₀ s₀)) : wprod (ibar u) = (wprod u)⁻¹ := by
  induction u with
  | nil => simp [ibar_nil, wprod_nil]
  | cons a u ih =>
    rw [ibar_cons, wprod_append, ih, wprod_singleton, genL_bar, wprod_cons, g_mul_inv_rev]

lemma red_ibar (u : List (Lt r₀ s₀)) (h : Red u) : Red (ibar u) := by
  unfold Red ibar
  rw [List.isChain_reverse, List.isChain_map]
  refine List.IsChain.imp (fun a b hab => ?_) h
  show bar a ≠ bar (bar b)
  rw [bar_bar]
  exact fun h => hab h.symm

lemma nf_inv (g : G r₀ s₀) : nf g⁻¹ = ibar (nf g) := by
  have := nf_wprod (ibar (nf g)) (red_ibar _ (nf_red g))
  rwa [wprod_ibar, wprod_nf] at this

lemma len_inv (g : G r₀ s₀) : len g⁻¹ = len g := by
  rw [len_eq, nf_inv, ibar_length, ← len_eq]

lemma wprod_replicate (c : List (Lt r₀ s₀)) (k : ℕ) :
    wprod (List.replicate k c).flatten = wprod c ^ k := by
  induction k with
  | zero => simp [wprod_nil]
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, wprod_append, ih, pow_succ']

/-- The normal form of a reduced conjugate of a power. -/
theorem nf_conj_pow (a z : G r₀ s₀) (k : ℕ)
    (h : len (a * z ^ k * a⁻¹) = 2 * len a + k * len z) :
    nf (a * z ^ k * a⁻¹) = nf a ++ (List.replicate k (nf z)).flatten ++ ibar (nf a) := by
  have hp : (a :: (List.replicate k z ++ [a⁻¹])).prod = a * z ^ k * a⁻¹ := by
    simp [mul_assoc]
  have hl : ((a :: (List.replicate k z ++ [a⁻¹])).map len).sum = 2 * len a + k * len z := by
    simp [len_inv]; ring
  have := nf_prod (a :: (List.replicate k z ++ [a⁻¹])) (by rw [hp, hl, h])
  rw [hp] at this
  rw [this]
  simp [nf_inv]

/-! ### Involutions -/

/-! ### Balls -/
/-- The elements that are products of `m` optional letters (= elements of length at most `m`). -/
def Ball (r₀ s₀ m : ℕ) : Finset (G r₀ s₀) :=
  (univ : Finset (Fin m → Lo r₀ s₀)).image iprod

lemma iprodL_mem_Ball (w : List (Lo r₀ s₀)) : iprodL w ∈ Ball r₀ s₀ w.length := by
  refine Finset.mem_image.mpr ⟨w.get, Finset.mem_univ _, ?_⟩
  rw [iprod_eq, List.ofFn_get]

lemma iprodL_map_some (u : List (Lt r₀ s₀)) : iprodL (u.map some) = wprod u := by
  induction u with
  | nil => simp [iprodL_nil, wprod_nil]
  | cons a u ih => rw [List.map_cons, iprodL_cons, ih, wprod_cons]; rfl

lemma iprodL_replicate_none (n : ℕ) : iprodL (List.replicate n (none : Lo r₀ s₀)) = 1 := by
  induction n with
  | zero => simp [iprodL_nil]
  | succ n ih => rw [List.replicate_succ, iprodL_cons, ih]; rfl

lemma mem_Ball_of_len {m : ℕ} (g : G r₀ s₀) (h : len g ≤ m) : g ∈ Ball r₀ s₀ m := by
  set w : List (Lo r₀ s₀) := (nf g).map some ++ List.replicate (m - len g) none with hw
  have hlen : w.length = m := by
    simp only [hw, List.length_append, List.length_map, List.length_replicate, ← len_eq]
    omega
  have hprod : iprodL w = g := by
    rw [hw, iprodL_append, iprodL_map_some, iprodL_replicate_none, mul_one, wprod_nf]
  have := iprodL_mem_Ball w
  rwa [hlen, hprod] at this

lemma len_iprodL_le : ∀ w : List (Lo r₀ s₀), len (iprodL w) ≤ w.length
  | [] => by simp [iprodL_nil, len_one]
  | a :: w => by
    rw [iprodL_cons, List.length_cons]
    have ih := len_iprodL_le w
    rcases a with _ | x
    · have : genO (none : Lo r₀ s₀) = 1 := rfl
      rw [this, one_mul]; omega
    · have h1 := len_mul_le (genL x) (iprodL w)
      have h2 := len_genL x
      have : genO (some x) = genL x := rfl
      rw [this]; omega

lemma len_iprod_le {m : ℕ} (i : Fin m → Lo r₀ s₀) : len (iprod i) ≤ m := by
  have := len_iprodL_le (List.ofFn i)
  rwa [← iprod_eq, List.length_ofFn] at this

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r₀ s₀ : ℕ}
variable (L : Lin r₀ s₀)
/-!
# Part P2, module 2: block sums, first-passage kernels, convolution chains
-/
abbrev Mt := Matrix (Fin L.Dm) (Fin L.Dm) ℂ

def Omg : ℕ → ℕ → (List (Lo r₀ s₀) → ℂ) → Mt L
  | _, 0, φ => φ [] • (1 : Mt L)
  | t, n + 1, φ => ∑ a : Lo r₀ s₀, L.B t a * Omg (t + 1) n (fun w => φ (a :: w))

theorem Omg_congr : ∀ (n t : ℕ) (φ ψ : List (Lo r₀ s₀) → ℂ),
    (∀ w, w.length = n → φ w = ψ w) → Omg L t n φ = Omg L t n ψ
  | 0, t, φ, ψ, h => by simp [Omg, h [] rfl]
  | n + 1, t, φ, ψ, h => by
    simp only [Omg]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Omg_congr n (t + 1) _ (fun w => ψ (a :: w)) (fun w hw => h _ (by simp [hw]))]

theorem Omg_add : ∀ (n t : ℕ) (φ ψ : List (Lo r₀ s₀) → ℂ),
    Omg L t n (fun w => φ w + ψ w) = Omg L t n φ + Omg L t n ψ
  | 0, t, φ, ψ => by simp [Omg, add_smul]
  | n + 1, t, φ, ψ => by
    simp only [Omg]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Omg_add n (t + 1) (fun w => φ (a :: w)) (fun w => ψ (a :: w)), mul_add]

theorem Omg_smul (c : ℂ) : ∀ (n t : ℕ) (φ : List (Lo r₀ s₀) → ℂ),
    Omg L t n (fun w => c * φ w) = c • Omg L t n φ
  | 0, t, φ => by simp [Omg, smul_smul]
  | n + 1, t, φ => by
    simp only [Omg]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Omg_smul c n (t + 1) (fun w => φ (a :: w)), mul_smul_comm]

theorem Omg_zero : ∀ (n t : ℕ), Omg L t n (fun _ => (0 : ℂ)) = 0
  | 0, t => by simp [Omg]
  | n + 1, t => by simp [Omg, Omg_zero n]

theorem Omg_sum {ι : Type*} (s : Finset ι) (n t : ℕ) (φ : ι → List (Lo r₀ s₀) → ℂ) :
    Omg L t n (fun w => ∑ i ∈ s, φ i w) = ∑ i ∈ s, Omg L t n (φ i) := by
  induction s using Finset.induction_on with
  | empty => simpa using Omg_zero L n t
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Omg_add L n t (φ a) (fun w => ∑ i ∈ s, φ i w), ih]

theorem Omg_split (φ1 φ2 : List (Lo r₀ s₀) → ℂ) : ∀ (a t b : ℕ),
    Omg L t (a + b) (fun w => φ1 (w.take a) * φ2 (w.drop a)) = Omg L t a φ1 * Omg L (t + a) b φ2 := by
  intro a
  induction a generalizing φ1 with
  | zero =>
    intro t b
    have := Omg_smul L (φ1 []) b t φ2
    simp only [Omg, List.take_zero, List.drop_zero, zero_add, add_zero, smul_mul_assoc, one_mul]
    exact this
  | succ a ih =>
    intro t b
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    simp only [Omg, List.take_succ_cons, List.drop_succ_cons, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc]
    congr 1
    have := ih (fun y => φ1 (x :: y)) (t + 1) b
    rw [show t + (a + 1) = t + 1 + a by omega]
    exact this

/-! ### Kernels -/
def Fr (t n : ℕ) (u : G r₀ s₀) : Mt L :=
  Omg L t n (fun w => if iprodL w = u then 1 else 0)

def FPc (v : G r₀ s₀) (w : List (Lo r₀ s₀)) : Prop :=
  iprodL w = v ∧ ∀ l, 1 ≤ l → l < w.length → iprodL (w.drop l) ≠ v

def FP (t n : ℕ) (v : G r₀ s₀) : Mt L :=
  Omg L t n (fun w => if FPc v w then 1 else 0)

lemma ite_mul_ite (A B : Prop) [Decidable A] [Decidable B] : ((if A then (1 : ℂ) else 0) * (if B then 1 else 0)) =
    if A ∧ B then 1 else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

lemma iprodL_split (w : List (Lo r₀ s₀)) (n : ℕ) :
    iprodL w = iprodL (w.take n) * iprodL (w.drop n) := by
  conv_lhs => rw [← List.take_append_drop n w]
  exact iprodL_append _ _

theorem fr_scalar (V v : G r₀ s₀) (hv : v ≠ 1) (hs : nf v <:+ nf (V * v))
    (w : List (Lo r₀ s₀)) :
    ((if iprodL w = V * v then 1 else 0 : ℂ)) =
      ∑ n' ∈ Finset.range (w.length + 1),
        (if iprodL (w.take n') = V then 1 else 0) * (if FPc v (w.drop n') then 1 else 0) := by
  simp_rw [ite_mul_ite]
  by_cases hW : iprodL w = V * v
  · rw [if_pos hW]
    obtain ⟨l0, hl0, hl0v⟩ := walk_hit v w (by rw [hW]; exact hs)
    set P : ℕ → Prop := fun l => iprodL (w.drop l) = v with hP
    set n0 := Nat.findGreatest P w.length with hn0
    have hspec : P n0 := Nat.findGreatest_spec (P := P) hl0 hl0v
    have hn0le : n0 ≤ w.length := Nat.findGreatest_le _
    have hgreat : ∀ k, n0 < k → k ≤ w.length → ¬ P k := fun k hk hkl =>
      Nat.findGreatest_is_greatest hk hkl
    have hmain : ∀ n', n' ≤ w.length →
        ((iprodL (w.take n') = V ∧ FPc v (w.drop n')) ↔ n' = n0) := by
      intro n' hn'
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · -- n' < n0
          have hlen : (w.drop n').length = w.length - n' := List.length_drop
          have hlt2 : n0 - n' < (w.drop n').length := by
            rcases Nat.lt_or_ge n0 w.length with h | h
            · omega
            · have : n0 = w.length := le_antisymm hn0le h
              -- then drop n0 w = [] and iprodL = 1 ≠ v
              exfalso
              have hd : w.drop n0 = [] := by simp [this]
              have := hspec
              simp only [hP, hd, iprodL_nil] at this
              exact hv this.symm
          refine h3 (n0 - n') (by omega) hlt2 ?_
          rw [List.drop_drop, Nat.add_sub_cancel' hlt.le]
          exact hspec
        · exact hgreat n' hgt hn' h2
      · rintro rfl
        refine ⟨?_, hspec, ?_⟩
        · have := iprodL_split w n0
          rw [hW] at this
          have h2 : iprodL (w.drop n0) = v := hspec
          rw [h2] at this
          exact (g_mul_right_cancel this).symm
        · intro l hl1 hl2 hlv
          rw [List.drop_drop] at hlv
          exact hgreat (n0 + l) (by omega) (by
            have : (w.drop n0).length = w.length - n0 := List.length_drop
            omega) hlv
    rw [Finset.sum_eq_single n0]
    · rw [if_pos]
      exact (hmain n0 hn0le).mpr rfl
    · intro b hb hbne
      rw [if_neg]
      intro hh
      exact hbne ((hmain b (by have := Finset.mem_range.mp hb; omega)).mp hh)
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg hW]
    symm
    refine Finset.sum_eq_zero fun n' _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2, _⟩
    apply hW
    rw [iprodL_split w n', h1, h2]

theorem Fr_rec (V v : G r₀ s₀) (hv : v ≠ 1) (hs : nf v <:+ nf (V * v))
    (t n : ℕ) :
    Fr L t n (V * v) = ∑ n' ∈ Finset.range (n + 1), Fr L t n' V * FP L (t + n') (n - n') v := by
  unfold Fr FP
  rw [Omg_congr L n t _ (fun w => ∑ n' ∈ Finset.range (n + 1),
      (if iprodL (w.take n') = V then (1 : ℂ) else 0) *
        (if FPc v (w.drop n') then 1 else 0))
      (fun w hw => by rw [fr_scalar V v hv hs w, hw]), Omg_sum]
  refine Finset.sum_congr rfl fun n' hn' => ?_
  have hle : n' ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn')
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.add_sub_cancel_left]
  exact Omg_split L (fun x => if iprodL x = V then (1 : ℂ) else 0)
    (fun y => if FPc v y then (1 : ℂ) else 0) n' t b

/-! ### First passage expansion (Lemma 9.4) -/
def NR (w : List (Lo r₀ s₀)) : Prop := ∀ l, 1 ≤ l → l < w.length → iprodL (w.drop l) ≠ 1

def Rc (w : List (Lo r₀ s₀)) : Prop := iprodL w = 1 ∧ NR w

def γ (s : ℕ) (x : List (Lo r₀ s₀)) : ℂ := if s = 0 then 1 else -(if Rc x then 1 else 0)

def Gam (t s : ℕ) : Mt L := Omg L t s (γ s)

lemma Rc_take_iff (v : G r₀ s₀) (w : List (Lo r₀ s₀)) (hW : iprodL w = v) (i : ℕ)
    (hi : i < w.length) (hv : iprodL (w.drop (i + 1)) = v) :
    Rc (w.take (i + 1)) ↔ ∀ j, j < i → iprodL (w.drop (j + 1)) ≠ v := by
  have hlen : (w.take (i + 1)).length = i + 1 := by simp; omega
  have hsplit : w = w.take (i + 1) ++ w.drop (i + 1) := (List.take_append_drop _ _).symm
  have hx : iprodL (w.take (i + 1)) = 1 := by
    have := iprodL_split w (i + 1)
    rw [hW, hv] at this
    exact (g_mul_eq_right.mp this.symm)
  have hj : ∀ j, j < i → iprodL (w.drop (j + 1)) = iprodL ((w.take (i + 1)).drop (j + 1)) * v := by
    intro j hji
    conv_lhs => rw [hsplit]
    rw [List.drop_append_of_le_length (by omega), iprodL_append, hv]
  constructor
  · rintro ⟨-, hNR⟩ j hji h
    apply hNR (j + 1) (by omega) (by omega)
    rw [hj j hji] at h
    exact g_mul_eq_right.mp h
  · intro h
    refine ⟨hx, fun l hl1 hl2 => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
    intro h1
    apply h j (by omega)
    rw [hj j (by omega), h1, one_mul]

theorem fp_scalar (v : G r₀ s₀) (hv : v ≠ 1) (w : List (Lo r₀ s₀)) :
    (if FPc v w then (1 : ℂ) else 0) = ∑ s ∈ Finset.range (w.length + 1),
      γ s (w.take s) * (if iprodL (w.drop s) = v then 1 else 0) := by
  rw [Finset.sum_range_succ']
  simp only [γ, List.take_zero, List.drop_zero, if_true, one_mul, Nat.add_one_ne_zero, if_false]
  by_cases hW : iprodL w = v
  · rw [if_pos hW]
    simp_rw [neg_mul, ite_mul_ite, Finset.sum_neg_distrib, Finset.sum_boole]
    set n := w.length with hn
    set Zs := (Finset.range n).filter (fun i => iprodL (w.drop (i + 1)) = v) with hZs
    have hfil : ((Finset.range n).filter (fun i => Rc (w.take (i + 1)) ∧
        iprodL (w.drop (i + 1)) = v)) = (Zs.filter fun i => ∀ j, j < i → j ∉ Zs) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, hZs]
      constructor
      · rintro ⟨hi, hR, hvi⟩
        refine ⟨⟨hi, hvi⟩, fun j hj hjZ => ?_⟩
        exact (Rc_take_iff v w hW i hi hvi).mp hR j hj hjZ.2
      · rintro ⟨⟨hi, hvi⟩, hj⟩
        refine ⟨hi, (Rc_take_iff v w hW i hi hvi).mpr fun j hji hjv => ?_, hvi⟩
        exact hj j hji ⟨by omega, hjv⟩
    rw [hfil]
    by_cases hZ : Zs.Nonempty
    · set i0 := Zs.min' hZ with hi0
      have hcard : (Zs.filter fun i => ∀ j, j < i → j ∉ Zs) = {i0} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hiZ, hj⟩
          have h1 : i0 ≤ i := Finset.min'_le _ _ hiZ
          by_contra hne
          exact hj i0 (lt_of_le_of_ne h1 (Ne.symm hne)) (Finset.min'_mem _ _)
        · rintro rfl
          refine ⟨Finset.min'_mem _ _, fun j hj hjZ => ?_⟩
          exact absurd (Finset.min'_le _ _ hjZ) (not_le.mpr hj)
      rw [hcard, Finset.card_singleton]
      rw [if_neg]
      · norm_num
      · rintro ⟨-, h2⟩
        obtain ⟨i, hiZ⟩ := hZ
        simp only [hZs, Finset.mem_filter, Finset.mem_range] at hiZ
        by_cases hin : i + 1 < n
        · exact h2 (i + 1) (by omega) hin hiZ.2
        · have : i + 1 = n := by omega
          have hd : w.drop (i + 1) = [] := by simp [this, hn]
          rw [hd, iprodL_nil] at hiZ
          exact hv hiZ.2.symm
    · rw [Finset.not_nonempty_iff_eq_empty] at hZ
      have : (Zs.filter fun i => ∀ j, j < i → j ∉ Zs) = ∅ := by simp [hZ]
      rw [this, Finset.card_empty, if_pos]
      · norm_num
      · refine ⟨hW, fun l hl1 hl2 hlv => ?_⟩
        have : l - 1 ∈ Zs := by
          simp only [hZs, Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ?_⟩
          rw [show l - 1 + 1 = l by omega]
          exact hlv
        rw [hZ] at this
        simp at this
  · rw [if_neg (fun h => hW h.1), if_neg hW, add_zero]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : iprodL (w.drop (i + 1)) = v
    · by_cases h2 : Rc (w.take (i + 1))
      · exfalso
        apply hW
        rw [iprodL_split w (i + 1), h2.1, h1, one_mul]
      · simp [h2]
    · simp [h1]

theorem FP_expand (v : G r₀ s₀) (hv : v ≠ 1) (t n : ℕ) :
    FP L t n v = ∑ s ∈ Finset.range (n + 1), Gam L t s * Fr L (t + s) (n - s) v := by
  unfold FP Gam Fr
  rw [Omg_congr L n t _ (fun w => ∑ s ∈ Finset.range (n + 1),
      γ s (w.take s) * (if iprodL (w.drop s) = v then (1 : ℂ) else 0))
      (fun w hw => by rw [fp_scalar v hv w, hw]), Omg_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))
  rw [Nat.add_sub_cancel_left]
  exact Omg_split L (γ s) (fun y => if iprodL y = v then (1 : ℂ) else 0) s t b

/-! ### Convolution of kernels -/
def cv {α : Type*} [NonUnitalNonAssocSemiring α] (F G : ℕ → ℕ → α) : ℕ → ℕ → α :=
  fun t n => ∑ a ∈ Finset.range (n + 1), F t a * G (t + a) (n - a)

theorem cv_assoc {α : Type*} [NonUnitalSemiring α] (A B C : ℕ → ℕ → α) :
    cv (cv A B) C = cv A (cv B C) := by
  funext t n
  simp only [cv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun b => Finset.Ico b (n + 1))]
  · refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.sum_Ico_eq_sum_range]
    have hb' : b ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    rw [show n + 1 - b = n - b + 1 by omega]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Nat.add_sub_cancel_left, mul_assoc, ← add_assoc, Nat.sub_add_eq]
  · intro a b
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

/-! ### Chains of blocks -/
def FrK (u : G r₀ s₀) : ℕ → ℕ → Mt L := fun t n => Fr L t n u

def FPK (v : G r₀ s₀) : ℕ → ℕ → Mt L := fun t n => FP L t n v

theorem Fr_rec_cv (V v : G r₀ s₀) (hv : v ≠ 1) (hs : nf v <:+ nf (V * v)) :
    FrK L (V * v) = cv (FrK L V) (FPK L v) := by
  funext t n
  exact Fr_rec L V v hv hs t n

theorem FPK_eq (v : G r₀ s₀) (hv : v ≠ 1) :
    FPK L v = cv (Gam L) (FrK L v) := by
  funext t n
  exact FP_expand L v hv t n

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r₀ s₀ : ℕ}
variable (L : Lin r₀ s₀)
open scoped InnerProductSpace
/-!
# Part P2, module 3: operators on `ℓ²(G)`, entry bounds, Bessel
-/
def delta (v : G r₀ s₀) : DerandSq.L2 (G r₀ s₀) := lp.single 2 v (1 : ℂ)

lemma leftReg_apply (g : G r₀ s₀) (f : DerandSq.L2 (G r₀ s₀)) (h : G r₀ s₀) :
    DerandSq.leftReg g f h = f (g⁻¹ * h) := rfl

theorem tensorOp_apply {a : Type*} [Fintype a] [DecidableEq a] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (σ : Matrix a a ℂ) (ω : E →L[ℂ] E)
    (x : AccessibleMaps.Composite a E) (i : a) :
    (AccessibleMaps.tensorOp σ ω x) i = ∑ j, σ i j • ω (x j) := by
  simp [AccessibleMaps.tensorOp, AccessibleMaps.inject]
  simp [Pi.single_apply]

abbrev Vec := PiLp 2 (fun _ : Fin L.Dm => DerandSq.L2 (G r₀ s₀))

def ev (y : Fin L.Dm) : Vec L := PiLp.single 2 y (delta (1 : G r₀ s₀))

lemma ev_apply (y x : Fin L.Dm) (u : G r₀ s₀) :
    (ev L y) x u = if x = y then (if u = 1 then 1 else 0) else 0 := by
  by_cases h : x = y
  · subst h
    by_cases hu : u = 1 <;> simp [ev, delta, lp.single_apply, hu, Pi.single_apply]
  · simp [ev, h]

lemma ev_norm (y : Fin L.Dm) : ‖ev L y‖ = 1 := by
  simp [ev, delta]

lemma X_apply (j : ℕ) (z : Vec L) (x : Fin L.Dm) (u : G r₀ s₀) :
    (Xop L j z) x u = ∑ x', ∑ a : Lo r₀ s₀, L.B j a x x' * (z x') ((genO a)⁻¹ * u) := by
  unfold Xop
  simp only [ContinuousLinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply, tensorOp_apply,
    lp.coeFn_sum, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, leftReg_apply]
  rw [Finset.sum_comm]

def XP : ℕ → ℕ → (Vec L →L[ℂ] Vec L)
  | _, 0 => 1
  | t, n + 1 => Xop L t * XP (t + 1) n

theorem Fr_succ (t n : ℕ) (u : G r₀ s₀) :
    Fr L t (n + 1) u = ∑ a : Lo r₀ s₀, L.B t a * Fr L (t + 1) n ((genO a)⁻¹ * u) := by
  unfold Fr
  simp only [Omg]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  apply Omg_congr
  intro w _
  rw [iprodL_cons]
  simp only [g_mul_eq_iff]

theorem Fr_entry : ∀ (n t : ℕ) (u : G r₀ s₀) (x y : Fin L.Dm),
    Fr L t n u x y = (XP L t n (ev L y)) x u
  | 0, t, u, x, y => by
    simp only [Fr, Omg, XP, iprodL_nil, ContinuousLinearMap.one_apply]
    rw [ev_apply]
    by_cases hxy : x = y <;> by_cases hu : u = 1 <;> simp [hxy, hu, Matrix.one_apply, eq_comm]
  | n + 1, t, u, x, y => by
    rw [Fr_succ]
    simp only [XP, ContinuousLinearMap.mul_apply]
    rw [X_apply]
    simp only [Matrix.sum_apply, Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Fr_entry n (t + 1) _ x' y]

theorem XP_norm (ρ : ℝ) (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) : ∀ n t, ‖XP L t n‖ ≤ ρ ^ n := by
  intro n
  induction n with
  | zero =>
    intro t
    have : XP L t 0 = ContinuousLinearMap.id ℂ _ := rfl
    rw [this, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    intro t
    have h0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
    have : XP L t (n + 1) = Xop L t * XP L (t + 1) n := rfl
    rw [this, pow_succ']
    have hc : ‖(Xop L t).comp (XP L (t + 1) n)‖ ≤ ‖Xop L t‖ * ‖XP L (t + 1) n‖ :=
      ContinuousLinearMap.opNorm_comp_le (Xop L t) (XP L (t + 1) n)
    exact hc.trans (mul_le_mul (hρ t) (ih (t + 1)) (norm_nonneg _) h0)

lemma entry_le (Z : Vec L) (x : Fin L.Dm) (u : G r₀ s₀) : ‖Z x u‖ ≤ ‖Z‖ :=
  (lp.norm_apply_le_norm (by simp) (Z x) u).trans (PiLp.norm_apply_le Z x)

lemma bessel (Z : Vec L) (S : Finset (G r₀ s₀)) :
    ∑ x, ∑ u ∈ S, ‖Z x u‖ ^ 2 ≤ ‖Z‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum fun x _ => ?_
  have := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) (Z x) S
  simpa using this

theorem Fr_entry_le (ρ : ℝ) (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (t n : ℕ) (u : G r₀ s₀)
    (x y : Fin L.Dm) : ‖Fr L t n u x y‖ ≤ ρ ^ n := by
  rw [Fr_entry]
  refine (entry_le L _ x u).trans ?_
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [ev_norm, mul_one]
  exact XP_norm L ρ hρ n t

theorem Fr_bessel (ρ : ℝ) (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (t n : ℕ) (S : Finset (G r₀ s₀))
    (y : Fin L.Dm) : ∑ x, ∑ u ∈ S, ‖Fr L t n u x y‖ ^ 2 ≤ ρ ^ (2 * n) := by
  simp_rw [Fr_entry]
  refine (bessel L _ S).trans ?_
  have h0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
  have : ‖XP L t n (ev L y)‖ ≤ ρ ^ n := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ev_norm, mul_one]
    exact XP_norm L ρ hρ n t
  calc ‖XP L t n (ev L y)‖ ^ 2 ≤ (ρ ^ n) ^ 2 := by gcongr
    _ = ρ ^ (2 * n) := by rw [← pow_mul, mul_comm]

/-! ### The projection `Q` -/
def Qop : DerandSq.L2 (G r₀ s₀) →L[ℂ] DerandSq.L2 (G r₀ s₀) :=
  ContinuousLinearMap.id ℂ _ - (innerSL ℂ (delta (1 : G r₀ s₀))).smulRight (delta 1)

lemma Qop_apply (f : DerandSq.L2 (G r₀ s₀)) (u : G r₀ s₀) :
    Qop f u = if u = 1 then 0 else f u := by
  have h1 : (innerSL ℂ (delta (1 : G r₀ s₀))) f = f 1 := by
    simp [delta, lp.inner_single_left]
  simp only [Qop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, h1, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hu : u = 1
  · subst hu; simp [delta, lp.single_apply]
  · simp [delta, lp.single_apply, hu, Pi.single_apply]

lemma Qop_norm (f : DerandSq.L2 (G r₀ s₀)) : ‖Qop f‖ ≤ ‖f‖ := by
  have h1 : f = Qop f + (f 1) • delta (1 : G r₀ s₀) := by
    ext u
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Qop_apply]
    by_cases hu : u = 1
    · subst hu; simp [delta, lp.single_apply]
    · simp [delta, lp.single_apply, hu, Pi.single_apply]
  have h2 : inner ℂ (Qop f) ((f 1) • delta (1 : G r₀ s₀)) = 0 := by
    rw [inner_smul_right]
    simp [delta, lp.inner_single_right, Qop_apply]
  have h3 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (Qop f) _ h2
  rw [← h1] at h3
  by_contra hcon
  have hcon := not_le.mp hcon
  nlinarith [norm_nonneg (Qop f), norm_nonneg f, mul_self_nonneg ‖(f 1) • delta (1 : G r₀ s₀)‖]

def Qt : Vec L →L[ℂ] Vec L := AccessibleMaps.tensorOp (1 : Matrix (Fin L.Dm) (Fin L.Dm) ℂ) (Qop (r₀ := r₀) (s₀ := s₀))

lemma Qt_apply (z : Vec L) (x : Fin L.Dm) : (Qt L z) x = Qop (z x) := by
  simp [Qt, tensorOp_apply, Matrix.one_apply]

lemma Qt_norm : ‖Qt L‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [one_mul]
  have h1 : ‖Qt L z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Qt_apply]
    exact pow_le_pow_left₀ (norm_nonneg _) (Qop_norm _) 2
  exact le_of_sq_le_sq h1 (norm_nonneg _)

theorem Omg_succ (t n : ℕ) (φ : List (Lo r₀ s₀) → ℂ) :
    Omg L t (n + 1) φ = ∑ a : Lo r₀ s₀, L.B t a * Omg L (t + 1) n (fun w => φ (a :: w)) := rfl

def YQ : ℕ → ℕ → (Vec L →L[ℂ] Vec L)
  | t, 0 => Xop L t
  | t, s + 1 => Xop L t * Qt L * YQ (t + 1) s

theorem YQ_norm (ρ : ℝ) (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) : ∀ s t, ‖YQ L t s‖ ≤ ρ ^ (s + 1) := by
  intro s
  induction s with
  | zero => intro t; simpa [YQ] using hρ t
  | succ s ih =>
    intro t
    have h0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
    have : YQ L t (s + 1) = ((Xop L t).comp (Qt L)).comp (YQ L (t + 1) s) := rfl
    rw [this, pow_succ' ρ (s + 1)]
    have hc1 : ‖(Xop L t).comp (Qt L)‖ ≤ ‖Xop L t‖ * ‖Qt L‖ :=
      ContinuousLinearMap.opNorm_comp_le (Xop L t) (Qt L)
    have hc2 : ‖((Xop L t).comp (Qt L)).comp (YQ L (t + 1) s)‖ ≤
        ‖(Xop L t).comp (Qt L)‖ * ‖YQ L (t + 1) s‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have h1 : ‖(Xop L t).comp (Qt L)‖ ≤ ρ := by
      refine hc1.trans ?_
      calc ‖Xop L t‖ * ‖Qt L‖ ≤ ρ * 1 :=
            mul_le_mul (hρ t) (Qt_norm L) (norm_nonneg _) h0
        _ = ρ := mul_one _
    exact hc2.trans (mul_le_mul h1 (ih (t + 1)) (norm_nonneg _) h0)

lemma NR_cons (a : Lo r₀ s₀) (w : List (Lo r₀ s₀)) (hw : w ≠ []) :
    NR (a :: w) ↔ iprodL w ≠ 1 ∧ NR w := by
  have hlen : 1 ≤ w.length := List.length_pos_iff.mpr hw
  constructor
  · intro h
    refine ⟨?_, fun l hl1 hl2 => ?_⟩
    · have := h 1 le_rfl (by simp; omega)
      simpa using this
    · have := h (l + 1) (by omega) (by simp; omega)
      simpa using this
  · rintro ⟨h1, h2⟩ l hl1 hl2
    by_cases hl : l = 1
    · subst hl; simpa using h1
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have := h2 l' (by omega) (by simp at hl2; omega)
      simpa using this

theorem YQ_entry : ∀ (s t : ℕ) (u : G r₀ s₀) (x y : Fin L.Dm),
    (YQ L t s (ev L y)) x u =
      Omg L t (s + 1) (fun w => if iprodL w = u ∧ NR w then 1 else 0) x y
  | 0, t, u, x, y => by
    have : YQ L t 0 = Xop L t := rfl
    rw [this, X_apply]
    simp only [Omg, Matrix.sum_apply, Matrix.mul_apply, ev_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h1 : iprodL [a] = genO a := by simp [iprodL]
    have h2 : ((if iprodL [a] = u ∧ NR [a] then (1 : ℂ) else 0) • (1 : Mt L)) = 
        (if genO a = u then (1 : ℂ) else 0) • (1 : Mt L) := by
      have : NR [a] := fun l hl1 hl2 => by simp at hl2; omega
      simp [h1, this]
    rw [h2]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hg : genO a = u
    · subst hg; simp [g_inv_mul_cancel]
    · have : (genO a)⁻¹ * u ≠ 1 := fun h => hg (g_inv_mul_eq_one.mp h)
      simp [hg, this]
  | s + 1, t, u, x, y => by
    have : YQ L t (s + 1) = ((Xop L t).comp (Qt L)).comp (YQ L (t + 1) s) := rfl
    rw [this]
    simp only [ContinuousLinearMap.comp_apply]
    rw [X_apply]
    simp only [Qt_apply, Qop_apply, YQ_entry s (t + 1)]
    rw [Omg_succ]
    simp only [Matrix.sum_apply, Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x' _ => ?_
    congr 1
    by_cases hv : (genO a)⁻¹ * u = 1
    · rw [if_pos hv]
      have : Omg L (t + 1) (s + 1) (fun w => if iprodL (a :: w) = u ∧ NR (a :: w) then (1 : ℂ) else 0)
          = 0 := by
        rw [← Omg_zero L (s + 1) (t + 1)]
        apply Omg_congr
        intro w hw
        have hne : w ≠ [] := by rintro rfl; simp at hw
        rw [if_neg]
        rintro ⟨h1, h2⟩
        rw [NR_cons a w hne] at h2
        rw [iprodL_cons] at h1
        apply h2.1
        have : iprodL w = (genO a)⁻¹ * u := g_mul_eq_iff.mp h1
        rw [this, hv]
      rw [this]; simp
    · rw [if_neg hv]
      have : Omg L (t + 1) (s + 1) (fun w => if iprodL (a :: w) = u ∧ NR (a :: w) then (1 : ℂ) else 0)
          = Omg L (t + 1) (s + 1) (fun w => if iprodL w = (genO a)⁻¹ * u ∧ NR w then 1 else 0) := by
        apply Omg_congr
        intro w hw
        have hne : w ≠ [] := by rintro rfl; simp at hw
        rw [NR_cons a w hne, iprodL_cons]
        by_cases hh : iprodL w = (genO a)⁻¹ * u
        · have : genO a * iprodL w = u := g_mul_eq_iff.mpr hh
          simp [hh, hv, g_mul_inv_cancel_left]
        · have : ¬ genO a * iprodL w = u := fun h => hh (g_mul_eq_iff.mp h)
          simp [hh, this]
      rw [this]

theorem Gam_entry_le (ρ : ℝ) (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (t s : ℕ) (x y : Fin L.Dm) :
    ‖Gam L t s x y‖ ≤ ρ ^ s := by
  cases s with
  | zero =>
    simp only [Gam, Omg, γ, if_true, pow_zero]
    by_cases hxy : x = y <;> simp [hxy, Matrix.one_apply]
  | succ s =>
    have h : Gam L t (s + 1) = (-1 : ℂ) • Omg L t (s + 1) (fun w => if Rc w then 1 else 0) := by
      unfold Gam
      rw [← Omg_smul]
      apply Omg_congr
      intro w _
      by_cases hr : Rc w <;> simp [γ, hr]
    rw [h, Matrix.smul_apply, smul_eq_mul]
    have h2 : Omg L t (s + 1) (fun w => if Rc w then (1 : ℂ) else 0) x y =
        (YQ L t s (ev L y)) x 1 := by
      rw [YQ_entry]
      have : Omg L t (s + 1) (fun w => if Rc w then (1 : ℂ) else 0) =
          Omg L t (s + 1) (fun w => if iprodL w = 1 ∧ NR w then 1 else 0) := by
        apply Omg_congr
        intro w _
        simp only [Rc]
        congr
      rw [this]
    rw [h2, neg_one_mul, norm_neg]
    refine (entry_le L _ x 1).trans ?_
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ev_norm, mul_one]
    exact YQ_norm L ρ hρ s t

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r₀ s₀ : ℕ}
variable (L : Lin r₀ s₀)
/-!
# Part P2, module 4: real convolution kernels, Cauchy–Schwarz pairings, Frobenius norms
-/
/-! ### Real kernels -/
abbrev RK := ℕ → ℕ → ℝ

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r : ℕ}
/-!
# Part P3b: `norm_sum_c2count_mul_trace_Bprod_le`

The two-loop coefficient. `C2count i₀ j₀ g` counts the reduced factorizations
`g = a (ρ m_{j₀} ρ⁻¹ σ m_{i₀} σ⁻¹)^t a⁻¹`, `t ≥ 1`. The normal form of such a `g` is the
concatenation of the blocks

`a | ρ | m_{j₀} | ρ⁻¹ | σ | m_{i₀} | σ⁻¹ | (ρ m_{j₀} ρ⁻¹ σ m_{i₀} σ⁻¹)^{t-1} | a⁻¹`

(any of which may be empty). The first-passage decomposition (CGTvH Lemma 9.4, `Fr_rec_cv`,
`FPK_eq`) bounds `‖Fr L t n g‖` by a convolution chain of the Frobenius-norm kernels of the
blocks (`Fr_blocks`; an empty block only makes the bound larger). The block
`(…)^{t-1}` is bounded by the operator norm, and the sums over `a`, `ρ`, `σ` are collapsed by
Cauchy–Schwarz/Bessel (`pair_Fr_inv`), pairing `a` with `a⁻¹`, `ρ` with `ρ⁻¹` and `σ` with `σ⁻¹`
(`collapse_flat`).
-/
/-! ### The unit kernel and flat chains -/
/-- The unit of the convolution `cv`. -/
def E1 : RK := fun _ n => if n = 0 then 1 else 0

lemma cv_E1 (k : RK) : cv k E1 = k := by
  funext t n
  simp only [cv, E1]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b hb hbn
    have hb' : b < n + 1 := Finset.mem_range.mp hb
    have : n - b ≠ 0 := by omega
    simp [this]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r₀ s₀ : ℕ}
variable (L : Lin r₀ s₀)
def RNN (k : RK) : Prop := ∀ t n, 0 ≤ k t n

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r : ℕ}
lemma E1_nn : RNN E1 := fun _ n => by
  unfold E1
  split_ifs <;> norm_num

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r₀ s₀ : ℕ}
variable (L : Lin r₀ s₀)
def RLE (k k' : RK) : Prop := ∀ t n, k t n ≤ k' t n

theorem cv_nonneg {A B : RK} (hA : RNN A) (hB : RNN B) : RNN (cv A B) := fun t n =>
  Finset.sum_nonneg fun a _ => mul_nonneg (hA _ _) (hB _ _)

theorem cv_mono {A A' B B' : RK} (hA : RNN A) (hB : RNN B) (hAA : RLE A A') (hBB : RLE B B') :
    RLE (cv A B) (cv A' B') := fun t n =>
  Finset.sum_le_sum fun a _ =>
    mul_le_mul (hAA _ _) (hBB _ _) (hB _ _) ((hA _ _).trans (hAA _ _))

def chainL {α : Type*} [NonUnitalNonAssocSemiring α] :
    List (ℕ → ℕ → α) → (ℕ → ℕ → α) → (ℕ → ℕ → α)
  | [], q => q
  | m :: ms, q => cv m (chainL ms q)

theorem chainL_append {α : Type*} [NonUnitalNonAssocSemiring α] (l1 l2 : List (ℕ → ℕ → α))
    (q : ℕ → ℕ → α) : chainL (l1 ++ l2) q = chainL l1 (chainL l2 q) := by
  induction l1 with
  | nil => rfl
  | cons m l1 ih => simp only [List.cons_append, chainL, ih]

theorem chainL_nonneg : ∀ (ms : List RK) (q : RK), (∀ m ∈ ms, RNN m) → RNN q → RNN (chainL ms q)
  | [], q, _, hq => hq
  | m :: ms, q, hms, hq =>
    cv_nonneg (hms m (by simp)) (chainL_nonneg ms q (fun m' h => hms m' (by simp [h])) hq)

theorem chainL_mono : ∀ (ms ms' : List RK) (q q' : RK), List.Forall₂ (fun a b => RNN a ∧ RLE a b) ms ms' →
    RNN q → RLE q q' → RNN (chainL ms q) ∧ RLE (chainL ms q) (chainL ms' q')
  | [], [], q, q', _, hq, hqq => ⟨hq, hqq⟩
  | [], _ :: _, q, q', h, hq, hqq => by cases h
  | _ :: _, [], q, q', h, hq, hqq => by cases h
  | m :: ms, m' :: ms', q, q', h, hq, hqq => by
    obtain ⟨⟨hm, hmm⟩, h'⟩ := List.forall₂_cons.mp h
    obtain ⟨h1, h2⟩ := chainL_mono ms ms' q q' h' hq hqq
    exact ⟨cv_nonneg hm h1, cv_mono hm h1 hmm h2⟩

def Bd (c : ℝ) (i : ℕ) (ρ : ℝ) : RK := fun _ n => c * ((n : ℝ) + 1) ^ i * ρ ^ n

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r : ℕ}
/-- A nonnegative kernel bounded by `c ρ^n`. -/
def GoodK (c ρ : ℝ) (k : RK) : Prop := RNN k ∧ RLE k (Bd c 0 ρ)

lemma good_cons {P : RK → Prop} {a : RK} {l : List RK} (h1 : P a) (h2 : ∀ m ∈ l, P m) :
    ∀ m ∈ a :: l, P m := by
  intro m hm
  rcases List.mem_cons.mp hm with rfl | h
  · exact h1
  · exact h2 m h

lemma good_nil {P : RK → Prop} : ∀ m ∈ ([] : List RK), P m := by
  intro m hm
  simp at hm

theorem chainL_sum_le {ι : Type*} (S : Finset ι) : ∀ (l : List RK), (∀ m ∈ l, RNN m) →
    ∀ (X : ι → RK) (Y : RK), (∀ t n, ∑ i ∈ S, X i t n ≤ Y t n) →
    ∀ t n, ∑ i ∈ S, chainL l (X i) t n ≤ chainL l Y t n
  | [], _, X, Y, h => h
  | m :: l, hl, X, Y, h => by
    intro t n
    have ih := chainL_sum_le S l (fun m' hm' => hl m' (by simp [hm'])) X Y h
    have hm := hl m (by simp)
    show ∑ i ∈ S, cv m (chainL l (X i)) t n ≤ cv m (chainL l Y) t n
    simp only [cv]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (ih _ _) (hm _ _)

theorem pair_ext {ι : Type*} (S : Finset ι) (p q : ι → RK) (e1 e2 R : RK) (hR : RNN R)
    (hpair : ∀ t1 t2 a c, ∑ i ∈ S, p i t1 a * q i t2 c ≤ e1 t1 a * e2 t2 c) :
    ∀ t1 t2 a c, ∑ i ∈ S, p i t1 a * cv (q i) R t2 c ≤ e1 t1 a * cv e2 R t2 c := by
  intro t1 t2 a c
  simp only [cv, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun b _ => ?_
  calc ∑ i ∈ S, p i t1 a * (q i t2 b * R (t2 + b) (c - b))
      = (∑ i ∈ S, p i t1 a * q i t2 b) * R (t2 + b) (c - b) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (e1 t1 a * e2 t2 b) * R (t2 + b) (c - b) :=
        mul_le_mul_of_nonneg_right (hpair _ _ _ _) (hR _ _)
    _ = e1 t1 a * (e2 t2 b * R (t2 + b) (c - b)) := by ring

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r₀ s₀ : ℕ}
variable (L : Lin r₀ s₀)
theorem cv_Bd {ρ : ℝ} (hρ : 0 ≤ ρ) {A B : RK} (hA : RNN A) (hB : RNN B) {a b : ℝ} {i j : ℕ}
    (hAB : RLE A (Bd a i ρ)) (hBB : RLE B (Bd b j ρ)) :
    RLE (cv A B) (Bd (a * b) (i + j + 1) ρ) := by
  intro t n
  have ha : 0 ≤ a := by
    have := (hA t 0).trans (hAB t 0)
    simpa [Bd] using this
  have hb : 0 ≤ b := by
    have := (hB t 0).trans (hBB t 0)
    simpa [Bd] using this
  simp only [cv, Bd]
  calc ∑ a' ∈ Finset.range (n + 1), A t a' * B (t + a') (n - a')
      ≤ ∑ a' ∈ Finset.range (n + 1), (a * ((n : ℝ) + 1) ^ i * (b * ((n : ℝ) + 1) ^ j) * ρ ^ n) := by
        refine Finset.sum_le_sum fun a' ha' => ?_
        have hle : a' ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha')
        have h1 := hAB t a'
        have h2 := hBB (t + a') (n - a')
        simp only [Bd] at h1 h2
        have h3 : A t a' * B (t + a') (n - a') ≤
            (a * ((a' : ℝ) + 1) ^ i * ρ ^ a') * (b * (((n - a' : ℕ) : ℝ) + 1) ^ j * ρ ^ (n - a')) :=
          mul_le_mul h1 h2 (hB _ _) (by positivity)
        refine h3.trans ?_
        have e1 : ((a' : ℝ) + 1) ^ i ≤ ((n : ℝ) + 1) ^ i :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hle) i
        have e2 : (((n - a' : ℕ) : ℝ) + 1) ^ j ≤ ((n : ℝ) + 1) ^ j :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ (Nat.sub_le n a')) j
        have e3 : ρ ^ a' * ρ ^ (n - a') = ρ ^ n := by rw [← pow_add, Nat.add_sub_cancel' hle]
        calc (a * ((a' : ℝ) + 1) ^ i * ρ ^ a') * (b * (((n - a' : ℕ) : ℝ) + 1) ^ j * ρ ^ (n - a'))
            = (a * ((a' : ℝ) + 1) ^ i) * (b * (((n - a' : ℕ) : ℝ) + 1) ^ j) *
                (ρ ^ a' * ρ ^ (n - a')) := by ring
          _ ≤ (a * ((n : ℝ) + 1) ^ i) * (b * ((n : ℝ) + 1) ^ j) * ρ ^ n := by
              rw [e3]
              gcongr
      _ = (a * b) * ((n : ℝ) + 1) ^ (i + j + 1) * ρ ^ n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem chainL_Bd {ρ : ℝ} (hρ : 0 ≤ ρ) {c : ℝ} (hc : 0 ≤ c) : ∀ (ms : List RK) (q : RK),
    (∀ m ∈ ms, RNN m ∧ RLE m (Bd c 0 ρ)) → RNN q → RLE q (Bd c 0 ρ) →
    RLE (chainL ms q) (Bd (c ^ (ms.length + 1)) ms.length ρ)
  | [], q, _, _, hq => by
    intro t n
    have := hq t n
    simp only [chainL, List.length_nil, Bd] at this ⊢
    simpa using this
  | m :: ms, q, hms, hq0, hq => by
    have ih := chainL_Bd hρ hc ms q (fun m' h => hms m' (by simp [h])) hq0 hq
    have hnn := chainL_nonneg ms q (fun m' h => (hms m' (by simp [h])).1) hq0
    have := cv_Bd hρ (hms m (by simp)).1 hnn (hms m (by simp)).2 ih
    intro t n
    have h := this t n
    show cv m (chainL ms q) t n ≤ _
    refine h.trans (le_of_eq ?_)
    simp only [Bd, List.length_cons, zero_add]
    rw [pow_succ' c (ms.length + 1)]

theorem collapse_aux {ι : Type*} (S : Finset ι) (p q : ι → RK) (e1 e2 : RK)
    (hpair : ∀ t1 t2 a c, ∑ i ∈ S, p i t1 a * q i t2 c ≤ e1 t1 a * e2 t2 c)
    (hp : ∀ i, RNN (p i)) :
    ∀ (ms : List RK), (∀ m ∈ ms, RNN m) → ∀ tp a t' n',
      ∑ i ∈ S, p i tp a * chainL ms (q i) t' n' ≤ e1 tp a * chainL ms e2 t' n'
  | [], _, tp, a, t', n' => hpair tp t' a n'
  | m :: ms, hms, tp, a, t', n' => by
    have ih := collapse_aux S p q e1 e2 hpair hp ms (fun m' h => hms m' (by simp [h]))
    have hm := hms m (by simp)
    show ∑ i ∈ S, p i tp a * cv m (chainL ms (q i)) t' n' ≤ e1 tp a * cv m (chainL ms e2) t' n'
    simp only [cv, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b _ => ?_
    calc ∑ i ∈ S, p i tp a * (m t' b * chainL ms (q i) (t' + b) (n' - b))
        = m t' b * ∑ i ∈ S, p i tp a * chainL ms (q i) (t' + b) (n' - b) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ m t' b * (e1 tp a * chainL ms e2 (t' + b) (n' - b)) :=
          mul_le_mul_of_nonneg_left (ih tp a _ _) (hm _ _)
      _ = e1 tp a * (m t' b * chainL ms e2 (t' + b) (n' - b)) := by ring

theorem collapse {ι : Type*} (S : Finset ι) (p q : ι → RK) (e1 e2 : RK)
    (hpair : ∀ t1 t2 a c, ∑ i ∈ S, p i t1 a * q i t2 c ≤ e1 t1 a * e2 t2 c)
    (hp : ∀ i, RNN (p i)) (ms : List RK) (hms : ∀ m ∈ ms, RNN m) (t n : ℕ) :
    ∑ i ∈ S, cv (p i) (chainL ms (q i)) t n ≤ cv e1 (chainL ms e2) t n := by
  simp only [cv]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun a _ => collapse_aux S p q e1 e2 hpair hp ms hms t a _ _

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r : ℕ}
/-- Collapse a paired sum inside a flat chain. -/
theorem collapse_flat {ι : Type*} (S : Finset ι) (p q : ι → RK) (e1 e2 : RK)
    (hpair : ∀ t1 t2 a c, ∑ i ∈ S, p i t1 a * q i t2 c ≤ e1 t1 a * e2 t2 c)
    (hp : ∀ i, RNN (p i)) (l1 l2 l3 : List RK) (h1 : ∀ m ∈ l1, RNN m) (h2 : ∀ m ∈ l2, RNN m)
    (h3 : ∀ m ∈ l3, RNN m) (t n : ℕ) :
    ∑ i ∈ S, chainL (l1 ++ p i :: (l2 ++ q i :: l3)) E1 t n ≤
      chainL (l1 ++ e1 :: (l2 ++ e2 :: l3)) E1 t n := by
  set R := chainL l3 E1 with hR
  have hRnn : RNN R := chainL_nonneg l3 E1 h3 E1_nn
  have e : ∀ (x y : RK), chainL (l1 ++ x :: (l2 ++ y :: l3)) E1 =
      chainL l1 (cv x (chainL l2 (cv y R))) := by
    intro x y
    rw [chainL_append]
    show chainL l1 (cv x (chainL (l2 ++ y :: l3) E1)) = _
    rw [chainL_append]
    rfl
  simp only [e]
  refine chainL_sum_le S l1 h1 _ _ (fun t n => ?_) t n
  exact collapse S p (fun i => cv (q i) R) e1 (cv e2 R)
    (pair_ext S p q e1 e2 R hRnn hpair) hp l2 h2 t n

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r₀ s₀ : ℕ}
variable (L : Lin r₀ s₀)
open scoped Matrix.Norms.Frobenius
/-! ### Frobenius norms and the pair bounds -/
lemma fro_sq (A : Mt L) : ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · simp [Real.rpow_two]
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

lemma fro_entry_le (A : Mt L) (i j : Fin L.Dm) : ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [fro_sq]
    calc ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact le_of_sq_le_sq h (norm_nonneg _)

lemma fro_le_of_entries (A : Mt L) (M : ℝ) (hM : 0 ≤ M) (h : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A‖ ≤ L.Dm * M := by
  have h2 : ‖A‖ ^ 2 ≤ ((L.Dm : ℝ) * M) ^ 2 := by
    rw [fro_sq]
    calc ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin L.Dm, ∑ _j : Fin L.Dm, M ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
      _ = ((L.Dm : ℝ) * M) ^ 2 := by simp; ring
  exact le_of_sq_le_sq h2 (by positivity)

lemma fro_trace (A : Mt L) : ‖A.trace‖ ≤ L.Dm * ‖A‖ := by
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖A.diag i‖ ≤ ∑ _i : Fin L.Dm, ‖A‖ :=
        Finset.sum_le_sum fun i _ => fro_entry_le L A i i
    _ = L.Dm * ‖A‖ := by simp

lemma fro_cv (F G : ℕ → ℕ → Mt L) (t n : ℕ) :
    ‖cv F G t n‖ ≤ cv (fun t n => ‖F t n‖) (fun t n => ‖G t n‖) t n := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  exact norm_mul_le _ _

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r₀ s₀ : ℕ}
variable (L : Lin r₀ s₀)
open scoped Matrix.Norms.Frobenius
variable {L}
/-- real kernel of Frobenius norms -/
def NF (L : Lin r₀ s₀) (u : G r₀ s₀) : RK := fun t n => ‖Fr L t n u‖

def NG (L : Lin r₀ s₀) : RK := fun t n => ‖Gam L t n‖

theorem fro_Fr {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (t n : ℕ) (u : G r₀ s₀) :
    ‖Fr L t n u‖ ≤ L.Dm * ρ ^ n :=
  fro_le_of_entries L _ _ (pow_nonneg ((norm_nonneg _).trans (hρ 0)) n)
    (fun x y => Fr_entry_le L ρ hρ t n u x y)

theorem fro_Gam {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (t n : ℕ) :
    ‖Gam L t n‖ ≤ L.Dm * ρ ^ n :=
  fro_le_of_entries L _ _ (pow_nonneg ((norm_nonneg _).trans (hρ 0)) n)
    (fun x y => Gam_entry_le L ρ hρ t n x y)

theorem fro_Fr_bessel {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (t n : ℕ) (S : Finset (G r₀ s₀)) :
    ∑ u ∈ S, ‖Fr L t n u‖ ^ 2 ≤ L.Dm * ρ ^ (2 * n) := by
  have h1 : ∀ u, ‖Fr L t n u‖ ^ 2 = ∑ x, ∑ y, ‖Fr L t n u x y‖ ^ 2 := fun u => fro_sq L _
  simp_rw [h1]
  calc ∑ u ∈ S, ∑ x, ∑ y, ‖Fr L t n u x y‖ ^ 2
      = ∑ x, ∑ u ∈ S, ∑ y, ‖Fr L t n u x y‖ ^ 2 := Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ u ∈ S, ‖Fr L t n u x y‖ ^ 2 :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ u ∈ S, ‖Fr L t n u x y‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ _y : Fin L.Dm, ρ ^ (2 * n) := Finset.sum_le_sum fun y _ => by
        exact Fr_bessel L ρ hρ t n S y
    _ = L.Dm * ρ ^ (2 * n) := by simp

theorem cs_pair {ι : Type*} (S : Finset ι) (f g : ι → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∑ i ∈ S, f i ^ 2 ≤ A ^ 2) (hg : ∑ i ∈ S, g i ^ 2 ≤ B ^ 2) :
    ∑ i ∈ S, f i * g i ≤ A * B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S f g
  have h2 : (∑ i ∈ S, f i * g i) ^ 2 ≤ (A * B) ^ 2 := by
    refine h.trans ?_
    rw [mul_pow]
    exact mul_le_mul hf hg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  exact le_of_sq_le_sq h2 (mul_nonneg hA hB)

theorem pair_Fr_inv {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (S : Finset (G r₀ s₀))
    (t1 t2 a c : ℕ) :
    ∑ u ∈ S, ‖Fr L t1 a u‖ * ‖Fr L t2 c u⁻¹‖ ≤ (L.Dm * ρ ^ a) * ρ ^ c := by
  have h0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
  have hD : (0 : ℝ) ≤ L.Dm := Nat.cast_nonneg _
  have himg : ∑ u ∈ S, ‖Fr L t2 c u⁻¹‖ ^ 2 = ∑ u ∈ S.image (fun u => u⁻¹), ‖Fr L t2 c u‖ ^ 2 := by
    rw [Finset.sum_image]
    intro x _ y _ h
    exact g_inv_inj h
  have := cs_pair S (fun u => ‖Fr L t1 a u‖) (fun u => ‖Fr L t2 c u⁻¹‖)
    (A := Real.sqrt L.Dm * ρ ^ a) (B := Real.sqrt L.Dm * ρ ^ c) (by positivity) (by positivity)
    (by
      refine (fro_Fr_bessel hρ t1 a S).trans (le_of_eq ?_)
      rw [mul_pow, Real.sq_sqrt hD, ← pow_mul, mul_comm a 2])
    (by
      rw [himg]
      refine (fro_Fr_bessel hρ t2 c _).trans (le_of_eq ?_)
      rw [mul_pow, Real.sq_sqrt hD, ← pow_mul, mul_comm c 2])
  refine this.trans (le_of_eq ?_)
  have : Real.sqrt L.Dm * Real.sqrt L.Dm = L.Dm := Real.mul_self_sqrt hD
  calc Real.sqrt L.Dm * ρ ^ a * (Real.sqrt L.Dm * ρ ^ c)
      = (Real.sqrt L.Dm * Real.sqrt L.Dm) * ρ ^ a * ρ ^ c := by ring
    _ = (L.Dm * ρ ^ a) * ρ ^ c := by rw [this]

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r₀ s₀ : ℕ}
variable (L : Lin r₀ s₀)
theorem forall2_refl_nn : ∀ (l : List RK), (∀ m ∈ l, RNN m) →
    List.Forall₂ (fun a b => RNN a ∧ RLE a b) l l
  | [], _ => List.Forall₂.nil
  | m :: l, h => List.Forall₂.cons ⟨h m (by simp), fun _ _ => le_rfl⟩
      (forall2_refl_nn l (fun m' hm' => h m' (by simp [hm'])))

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r : ℕ}
theorem chainL_mono_at (l1 l2 : List RK) (k k' : RK) (h1 : ∀ m ∈ l1, RNN m)
    (h2 : ∀ m ∈ l2, RNN m) (hk : RNN k) (hkk : RLE k k') (t n : ℕ) :
    chainL (l1 ++ k :: l2) E1 t n ≤ chainL (l1 ++ k' :: l2) E1 t n :=
  (chainL_mono _ _ E1 E1 (List.rel_append (forall2_refl_nn l1 h1)
    (List.Forall₂.cons ⟨hk, hkk⟩ (forall2_refl_nn l2 h2))) E1_nn (fun _ _ => le_rfl)).2 t n

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r : ℕ}
open scoped Matrix.Norms.Frobenius
variable {L : Lin 0 r}
/-! ### The norm of a product of blocks -/
lemma fro_one_sq (hD1 : 1 ≤ L.Dm) : (1 : ℝ) ≤ ‖(1 : Mt L)‖ * ‖(1 : Mt L)‖ := by
  have h := fro_sq L (1 : Mt L)
  have h2 : ∑ i : Fin L.Dm, ∑ j : Fin L.Dm, ‖(1 : Mt L) i j‖ ^ 2 = L.Dm := by
    have : ∀ i j : Fin L.Dm, ‖(1 : Mt L) i j‖ ^ 2 = if i = j then (1 : ℝ) else 0 := by
      intro i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    simp [this]
  rw [h2] at h
  rw [← sq, h]
  exact_mod_cast hD1

/-- Inserting the kernel of an empty block only increases a kernel. -/
lemma unit_le (hD1 : 1 ≤ L.Dm) (X : RK) (hX : RNN X) (t n : ℕ) :
    X t n ≤ cv X (cv (NG L) (NF L 1)) t n := by
  set U : RK := cv (NG L) (NF L 1) with hUdef
  have hU : ∀ t', (1 : ℝ) ≤ U t' 0 := by
    intro t'
    have hG : Gam L t' 0 = 1 := by simp [Gam, Omg, γ]
    have hF : Fr L (t' + 0) (0 - 0) (1 : G 0 r) = 1 := by simp [Fr, Omg, iprodL_nil]
    show (1 : ℝ) ≤ ∑ a ∈ Finset.range (0 + 1), ‖Gam L t' a‖ * ‖Fr L (t' + a) (0 - a) 1‖
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    rw [hG, hF]
    exact fro_one_sq hD1
  have hnn : RNN U := cv_nonneg (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
  show X t n ≤ ∑ a ∈ Finset.range (n + 1), X t a * U (t + a) (n - a)
  calc X t n ≤ X t n * U (t + n) (n - n) := by
        rw [Nat.sub_self]
        exact le_mul_of_one_le_right (hX t n) (hU _)
    _ ≤ ∑ a ∈ Finset.range (n + 1), X t a * U (t + a) (n - a) :=
        Finset.single_le_sum (f := fun a => X t a * U (t + a) (n - a))
          (fun a _ => mul_nonneg (hX _ _) (hnn _ _))
          (Finset.mem_range.mpr (Nat.lt_succ_self n))

/-- The kernels of a list of blocks. -/
def blk (L : Lin 0 r) (Bs : List (List (Lt 0 r))) : List RK :=
  Bs.flatMap fun B => [NG L, NF L (wprod B)]

lemma blk_nn (Bs : List (List (Lt 0 r))) : ∀ m ∈ blk L Bs, RNN m := by
  intro m hm
  simp only [blk, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hm
  obtain ⟨B', -, rfl | rfl⟩ := hm <;> exact fun _ _ => norm_nonneg _

/-- First-passage decomposition of a reduced product of (possibly empty) blocks, in norm. -/
theorem Fr_blocks (hD1 : 1 ≤ L.Dm) : ∀ (Bs : List (List (Lt 0 r))) (B1 : List (Lt 0 r)),
    Red (B1 ++ Bs.flatten) → ∀ t n,
      ‖Fr L t n (wprod (B1 ++ Bs.flatten))‖ ≤
        cv (NF L (wprod B1)) (chainL (blk L Bs) E1) t n
  | [], B1, _, t, n => by
    have e : chainL (blk L []) E1 = E1 := rfl
    rw [e, cv_E1, List.flatten_nil, List.append_nil]
    exact le_rfl
  | B :: Bs, B1, hred, t, n => by
    have e : B1 ++ (B :: Bs).flatten = (B1 ++ B) ++ Bs.flatten := by simp
    rw [e] at hred ⊢
    have ih := Fr_blocks hD1 Bs (B1 ++ B) hred t n
    refine ih.trans ?_
    set R := chainL (blk L Bs) E1 with hR
    have hRnn : RNN R := chainL_nonneg _ _ (blk_nn Bs) E1_nn
    have hstep : RLE (NF L (wprod (B1 ++ B)))
        (cv (NF L (wprod B1)) (cv (NG L) (NF L (wprod B)))) := by
      intro t n
      by_cases hB : B = []
      · subst hB
        rw [List.append_nil, wprod_nil]
        exact unit_le hD1 (NF L (wprod B1)) (fun _ _ => norm_nonneg _) t n
      · have hredP : Red (B1 ++ B) := hred.infix ⟨[], Bs.flatten, by simp⟩
        have hredB : Red B := hredP.infix ⟨B1, [], by simp⟩
        have hmkB : nf (wprod B) = B := nf_wprod B hredB
        have hv : wprod B ≠ 1 := by
          intro h
          rw [← nf_eq_nil, hmkB] at h
          exact hB h
        have hs : nf (wprod B) <:+ nf (wprod B1 * wprod B) := by
          rw [← wprod_append, nf_wprod _ hredP, hmkB]
          exact List.suffix_append _ _
        have h1 : FrK L (wprod (B1 ++ B)) =
            cv (FrK L (wprod B1)) (cv (Gam L) (FrK L (wprod B))) := by
          rw [wprod_append, Fr_rec_cv L _ _ hv hs, FPK_eq L _ hv]
        show ‖FrK L (wprod (B1 ++ B)) t n‖ ≤ _
        rw [h1]
        refine (fro_cv L _ _ t n).trans ?_
        have hA : RNN (fun t n => ‖FrK L (wprod B1) t n‖) := fun _ _ => norm_nonneg _
        have hC : RNN (fun t n => ‖cv (Gam L) (FrK L (wprod B)) t n‖) :=
          fun _ _ => norm_nonneg _
        refine cv_mono hA hC (fun _ _ => le_rfl) ?_ t n
        intro t n
        exact fro_cv L _ _ t n
    have h2 := cv_mono (fun _ _ => norm_nonneg _) hRnn hstep (fun _ _ => le_rfl) t n
    refine h2.trans (le_of_eq ?_)
    rw [cv_assoc, cv_assoc]
    rfl

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r : ℕ}
/-! ### The two-loop words -/
/-- `ρ m_{j₀} ρ⁻¹ σ m_{i₀} σ⁻¹`. -/
def zz (i0 j0 : Fin r) (b s : G 0 r) : G 0 r :=
  b * mI j0 * b⁻¹ * (s * mI i0 * s⁻¹)

/-- `a (ρ m_{j₀} ρ⁻¹ σ m_{i₀} σ⁻¹)^t a⁻¹` for `p = (a, ρ, σ)`. -/
def gg (i0 j0 : Fin r) (t : ℕ) (p : G 0 r × G 0 r × G 0 r) : G 0 r :=
  p.1 * zz i0 j0 p.2.1 p.2.2 ^ t * p.1⁻¹

/-- The configuration is reduced. -/
def Pt (i0 j0 : Fin r) (t : ℕ) (p : G 0 r × G 0 r × G 0 r) : Prop :=
  len (gg i0 j0 t p) = 2 * len p.1 + t * (2 * len p.2.1 + 2 * len p.2.2 + 2)

/-- The normal form of `ρ m_{j₀} ρ⁻¹ σ m_{i₀} σ⁻¹` in a reduced configuration. -/
def cyc (i0 j0 : Fin r) (b s : G 0 r) : List (Lt 0 r) :=
  nf b ++ [Sum.inr j0] ++ ibar (nf b) ++ (nf s ++ [Sum.inr i0] ++ ibar (nf s))

lemma mI_eq (i : Fin r) : mI i = genL (Sum.inr i : Lt 0 r) := rfl

lemma zz_prod (i0 j0 : Fin r) (b s : G 0 r) :
    ([b, genL (Sum.inr j0), b⁻¹, s, genL (Sum.inr i0), s⁻¹] : List (G 0 r)).prod =
      zz i0 j0 b s := by
  simp [zz, mI_eq, mul_assoc]

lemma zz_lens (i0 j0 : Fin r) (b s : G 0 r) :
    (([b, genL (Sum.inr j0), b⁻¹, s, genL (Sum.inr i0), s⁻¹] : List (G 0 r)).map len).sum =
      2 * len b + 2 * len s + 2 := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, len_inv, len_genL]
  omega

lemma len_zz_le (i0 j0 : Fin r) (b s : G 0 r) :
    len (zz i0 j0 b s) ≤ 2 * len b + 2 * len s + 2 := by
  have := len_prod_le [b, genL (Sum.inr j0), b⁻¹, s, genL (Sum.inr i0), s⁻¹]
  rwa [zz_prod, zz_lens] at this

lemma nf_zz (i0 j0 : Fin r) (b s : G 0 r)
    (h : len (zz i0 j0 b s) = 2 * len b + 2 * len s + 2) :
    nf (zz i0 j0 b s) = cyc i0 j0 b s := by
  have := nf_prod [b, genL (Sum.inr j0), b⁻¹, s, genL (Sum.inr i0), s⁻¹]
    (by rw [zz_prod, zz_lens, h])
  rw [zz_prod] at this
  rw [this]
  simp [cyc, nf_inv, nf_genL]

lemma nf_gg (i0 j0 : Fin r) (t : ℕ) (ht : 1 ≤ t) (p : G 0 r × G 0 r × G 0 r)
    (h : Pt i0 j0 t p) :
    nf (gg i0 j0 t p) =
      nf p.1 ++ (List.replicate t (cyc i0 j0 p.2.1 p.2.2)).flatten ++ ibar (nf p.1) := by
  obtain ⟨a, b, s⟩ := p
  simp only [Pt, gg] at h ⊢
  have h1 := len_zz_le i0 j0 b s
  set z := zz i0 j0 b s with hz
  have hp : (a :: (List.replicate t z ++ [a⁻¹])).prod = a * z ^ t * a⁻¹ := by
    simp [mul_assoc]
  have hl : ((a :: (List.replicate t z ++ [a⁻¹])).map len).sum = 2 * len a + t * len z := by
    simp [len_inv]; ring
  have h2 := len_prod_le (a :: (List.replicate t z ++ [a⁻¹]))
  rw [hp, hl, h] at h2
  have h3 : t * (2 * len b + 2 * len s + 2) ≤ t * len z := Nat.le_of_add_le_add_left h2
  have h4 : 2 * len b + 2 * len s + 2 ≤ len z := Nat.le_of_mul_le_mul_left h3 (by omega)
  have h5 : len z = 2 * len b + 2 * len s + 2 := le_antisymm h1 h4
  have h6 : len (a * z ^ t * a⁻¹) = 2 * len a + t * len z := by rw [h, h5]
  rw [nf_conj_pow a z t h6, nf_zz i0 j0 b s h5]

/-! ### The counting identity -/
lemma card_subtype_eq {α : Type*} (F : Finset α) (P : α → Prop) (hF : ∀ t, P t → t ∈ F) :
    Nat.card {t : α // P t} = (F.filter P).card :=
  Nat.subtype_card (F.filter P) (fun x => by
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hF x h, h⟩⟩)

/-- Reordering of the tuples `(a, ρ, σ, t)`. -/
def eqv (r : ℕ) : G 0 r × G 0 r × G 0 r × ℕ ≃ ℕ × (G 0 r × G 0 r × G 0 r) where
  toFun q := (q.2.2.2, (q.1, q.2.1, q.2.2.1))
  invFun q := (q.2.1, q.2.2.1, q.2.2.2, q.1)
  left_inv _ := rfl
  right_inv _ := rfl

lemma c2count_eq (i0 j0 : Fin r) (m : ℕ) (g : G 0 r) (hg : len g ≤ m) :
    (C2count i0 j0 g : ℂ) =
      ∑ t ∈ Finset.Ico 1 (m + 1), ∑ p ∈ Ball 0 r m ×ˢ Ball 0 r m ×ˢ Ball 0 r m,
        (if Pt i0 j0 t p ∧ g = gg i0 j0 t p then (1 : ℂ) else 0) := by
  set P : ℕ × (G 0 r × G 0 r × G 0 r) → Prop := fun q => 1 ≤ q.1 ∧ g = gg i0 j0 q.1 q.2 ∧
    len g = 2 * len q.2.1 + q.1 * (2 * len q.2.2.1 + 2 * len q.2.2.2 + 2) with hP
  have hB : C2count i0 j0 g = Nat.card {q : ℕ × (G 0 r × G 0 r × G 0 r) // P q} := by
    unfold C2count
    exact Nat.card_congr ((eqv r).subtypeEquiv (fun q => Iff.rfl))
  set F : Finset (ℕ × (G 0 r × G 0 r × G 0 r)) :=
    Finset.Ico 1 (m + 1) ×ˢ (Ball 0 r m ×ˢ Ball 0 r m ×ˢ Ball 0 r m) with hF
  have hmem : ∀ q, P q → q ∈ F := by
    rintro ⟨t, a, b, s⟩ ⟨h1, -, hl⟩
    simp only at h1 hl
    have hX : 2 * len b + 2 * len s + 2 ≤ t * (2 * len b + 2 * len s + 2) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have ht : t ≤ t * (2 * len b + 2 * len s + 2) := Nat.le_mul_of_pos_right t (by omega)
    simp only [hF, Finset.mem_product, Finset.mem_Ico]
    exact ⟨⟨h1, by omega⟩, mem_Ball_of_len a (by omega), mem_Ball_of_len b (by omega),
      mem_Ball_of_len s (by omega)⟩
  rw [hB, card_subtype_eq F P hmem, Finset.card_filter, Nat.cast_sum, hF, Finset.sum_product]
  refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun p _ => ?_
  have ht1 : 1 ≤ t := (Finset.mem_Ico.mp ht).1
  have hiff : P (t, p) ↔ (Pt i0 j0 t p ∧ g = gg i0 j0 t p) := by
    simp only [hP, Pt]
    constructor
    · rintro ⟨-, hgeq, hl⟩
      exact ⟨by rw [← hgeq]; exact hl, hgeq⟩
    · rintro ⟨hl, hgeq⟩
      exact ⟨ht1, hgeq, by rw [hgeq]; exact hl⟩
  by_cases h : P (t, p)
  · rw [if_pos h, if_pos (hiff.mp h)]; simp
  · rw [if_neg h, if_neg (mt hiff.mpr h)]; simp

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r₀ s₀ : ℕ}
variable (L : Lin r₀ s₀)

/-! ### Bridge to the sum over words -/
theorem Omg_eq_sum : ∀ (n t : ℕ) (φ : List (Lo r₀ s₀) → ℂ),
    Omg L t n φ = ∑ i : Fin n → Lo r₀ s₀, φ (List.ofFn i) •
      (List.ofFn fun j : Fin n => L.B (t + (j : ℕ)) (i j)).prod
  | 0, t, φ => by simp [Omg]
  | n + 1, t, φ => by
    rw [Omg_succ]
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Lo r₀ s₀))
      (fun p => φ (List.ofFn (Fin.consEquiv (fun _ : Fin (n + 1) => Lo r₀ s₀) p)) •
        (List.ofFn fun j : Fin (n + 1) => L.B (t + (j : ℕ))
          ((Fin.consEquiv (fun _ : Fin (n + 1) => Lo r₀ s₀) p) j)).prod) _ (fun p => rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Omg_eq_sum n (t + 1) (fun w => φ (a :: w)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
      Fin.val_succ, add_zero, List.prod_cons]
    rw [mul_smul_comm]
    simp only [show ∀ j : ℕ, t + 1 + j = t + (j + 1) from fun j => by omega]

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r : ℕ}
lemma trace_Fr (L : Lin 0 r) (m : ℕ) (u : G 0 r) :
    (Fr L 1 m u).trace =
      ∑ i : Fin m → Lo 0 r, if iprod i = u then (Bprod L m i).trace else 0 := by
  unfold Fr
  rw [Omg_eq_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, ← iprod_eq]
  have : (List.ofFn fun j : Fin m => L.B (1 + (j : ℕ)) (i j)).prod = Bprod L m i := by
    unfold Bprod
    simp only [add_comm]
  rw [this]
  split_ifs <;> simp

/-- The sum of the theorem, rewritten as a sum of traces of the kernels `Fr`. -/
theorem sum_eq (L : Lin 0 r) (i0 j0 : Fin r) (m : ℕ) :
    (∑ i : Fin m → Option (Lt 0 r), (C2count i0 j0 (iprod i) : ℂ) * (Bprod L m i).trace) =
      ∑ t ∈ Finset.Ico 1 (m + 1),
        ∑ p ∈ (Ball 0 r m ×ˢ Ball 0 r m ×ˢ Ball 0 r m).filter (Pt i0 j0 t),
          (Fr L 1 m (gg i0 j0 t p)).trace := by
  have key : ∀ i : Fin m → Option (Lt 0 r),
      (C2count i0 j0 (iprod i) : ℂ) * (Bprod L m i).trace =
        ∑ t ∈ Finset.Ico 1 (m + 1), ∑ p ∈ Ball 0 r m ×ˢ Ball 0 r m ×ˢ Ball 0 r m,
          (if Pt i0 j0 t p ∧ iprod i = gg i0 j0 t p then (Bprod L m i).trace else 0) := by
    intro i
    rw [c2count_eq i0 j0 m (iprod i) (len_iprod_le i), Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : Pt i0 j0 t p
  · rw [if_pos hp, trace_Fr]
    exact Finset.sum_congr rfl fun i _ => if_congr (and_iff_right hp) rfl rfl
  · rw [if_neg hp]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    exact fun h => hp h.1

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r : ℕ}
open scoped Matrix.Norms.Frobenius
variable {L : Lin 0 r}
/-! ### The bound for one exponent `t` -/
/-- The chain of kernels of the nine blocks (after the trivial first block). -/
def KL (L : Lin 0 r) (x1 x2 : Lt 0 r) (A A' P P' Q Q' K : RK) : List RK :=
  [NF L 1, NG L, A, NG L, P, NG L, NF L (genL x1), NG L, P', NG L, Q, NG L,
    NF L (genL x2), NG L, Q', NG L, K, NG L, A']

/-- `Dm ρ^n`. -/
def e1K (L : Lin 0 r) (ρ : ℝ) : RK := fun _ a => (L.Dm : ℝ) * ρ ^ a

/-- `ρ^n`. -/
def e2K (ρ : ℝ) : RK := fun _ a => ρ ^ a

lemma good_NG {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) : GoodK (L.Dm : ℝ) ρ (NG L) :=
  ⟨fun _ _ => norm_nonneg _, fun t n => by simpa [NG, Bd] using fro_Gam hρ t n⟩

lemma good_NF {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (u : G 0 r) : GoodK (L.Dm : ℝ) ρ (NF L u) :=
  ⟨fun _ _ => norm_nonneg _, fun t n => by simpa [NF, Bd] using fro_Fr hρ t n u⟩

lemma good_e1 {ρ : ℝ} (hρ0 : 0 ≤ ρ) : GoodK (L.Dm : ℝ) ρ (e1K L ρ) :=
  ⟨fun _ _ => by unfold e1K; positivity, fun t n => by simp [Bd, e1K]⟩

lemma good_e2 {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hD1 : 1 ≤ L.Dm) : GoodK (L.Dm : ℝ) ρ (e2K ρ) := by
  refine ⟨fun _ _ => by unfold e2K; positivity, fun t n => ?_⟩
  have : (1 : ℝ) ≤ L.Dm := by exact_mod_cast hD1
  simp only [Bd, e2K, pow_zero, mul_one]
  nlinarith [pow_nonneg hρ0 n]

lemma good_E1 {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hD1 : 1 ≤ L.Dm) : GoodK (L.Dm : ℝ) ρ E1 := by
  refine ⟨E1_nn, fun t n => ?_⟩
  have hDr : (1 : ℝ) ≤ L.Dm := by exact_mod_cast hD1
  simp only [Bd, E1, pow_zero, mul_one]
  split_ifs with h
  · subst h; simpa using hDr
  · have := pow_nonneg hρ0 n
    nlinarith

lemma KL_good {c ρ : ℝ} (x1 x2 : Lt 0 r) (A A' P P' Q Q' K : RK)
    (hG : GoodK c ρ (NG L)) (hF : ∀ u, GoodK c ρ (NF L u))
    (hA : GoodK c ρ A) (hA' : GoodK c ρ A') (hP : GoodK c ρ P) (hP' : GoodK c ρ P')
    (hQ : GoodK c ρ Q) (hQ' : GoodK c ρ Q') (hK : GoodK c ρ K) :
    ∀ k ∈ KL L x1 x2 A A' P P' Q Q' K, GoodK c ρ k := by
  unfold KL
  repeat' first
    | exact good_nil
    | exact hG
    | exact hF _
    | exact hA
    | exact hA'
    | exact hP
    | exact hP'
    | exact hQ
    | exact hQ'
    | exact hK
    | apply good_cons

/-- The bound of one configuration by its chain of kernels. -/
theorem shape_one {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (hD1 : 1 ≤ L.Dm) (i0 j0 : Fin r)
    (t' m : ℕ) (p : G 0 r × G 0 r × G 0 r) (hp : Pt i0 j0 (t' + 1) p) :
    ‖Fr L 1 m (gg i0 j0 (t' + 1) p)‖ ≤
      chainL (KL L (Sum.inr j0) (Sum.inr i0) (NF L p.1) (NF L p.1⁻¹) (NF L p.2.1)
        (NF L p.2.1⁻¹) (NF L p.2.2) (NF L p.2.2⁻¹) (e1K L ρ)) E1 1 m := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
  have hnf := nf_gg i0 j0 (t' + 1) (by omega) p hp
  obtain ⟨a, b, s⟩ := p
  simp only at hnf ⊢
  set Bs : List (List (Lt 0 r)) := [nf a, nf b, [Sum.inr j0], ibar (nf b), nf s, [Sum.inr i0],
    ibar (nf s), (List.replicate t' (cyc i0 j0 b s)).flatten, ibar (nf a)] with hBs
  have hflat : ([] : List (Lt 0 r)) ++ Bs.flatten = nf (gg i0 j0 (t' + 1) (a, b, s)) := by
    rw [hnf]
    simp [hBs, cyc, List.replicate_succ]
  have hred : Red (([] : List (Lt 0 r)) ++ Bs.flatten) := by
    rw [hflat]; exact nf_red _
  have h := Fr_blocks (L := L) hD1 Bs [] hred 1 m
  rw [hflat, wprod_nf] at h
  have hb : cv (NF L (wprod ([] : List (Lt 0 r)))) (chainL (blk L Bs) E1) =
      chainL (KL L (Sum.inr j0) (Sum.inr i0) (NF L a) (NF L a⁻¹) (NF L b)
        (NF L b⁻¹) (NF L s) (NF L s⁻¹) (NF L (wprod (cyc i0 j0 b s) ^ t'))) E1 := by
    simp only [hBs, blk, KL, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, chainL, wprod_nf, wprod_ibar, wprod_singleton, wprod_nil, wprod_replicate]
  rw [hb] at h
  refine h.trans ?_
  have gNG := good_NG hρ
  have gNF := good_NF hρ
  exact chainL_mono_at
    [NF L 1, NG L, NF L a, NG L, NF L b, NG L, NF L (genL (Sum.inr j0)), NG L, NF L b⁻¹, NG L,
      NF L s, NG L, NF L (genL (Sum.inr i0)), NG L, NF L s⁻¹, NG L]
    [NG L, NF L a⁻¹] _ (e1K L ρ)
    (by repeat' first | exact good_nil | exact fun _ _ => norm_nonneg _ | apply good_cons)
    (by repeat' first | exact good_nil | exact fun _ _ => norm_nonneg _ | apply good_cons)
    (fun _ _ => norm_nonneg _) (fun t n => fro_Fr hρ t n _) 1 m

/-- The sum over the reduced configurations with exponent `t' + 1`. -/
theorem shape2 {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (hD1 : 1 ≤ L.Dm) (i0 j0 : Fin r)
    (t' m : ℕ) :
    ∑ p ∈ (Ball 0 r m ×ˢ Ball 0 r m ×ˢ Ball 0 r m).filter (Pt i0 j0 (t' + 1)),
        ‖Fr L 1 m (gg i0 j0 (t' + 1) p)‖ ≤
      (L.Dm : ℝ) ^ 20 * ((m : ℝ) + 1) ^ 19 * ρ ^ m := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
  have hDr : (1 : ℝ) ≤ L.Dm := by exact_mod_cast hD1
  have hD0 : (0 : ℝ) ≤ L.Dm := by linarith
  have gNG := good_NG hρ
  have gNF := good_NF hρ
  have ge1 : GoodK (L.Dm : ℝ) ρ (e1K L ρ) := good_e1 hρ0
  have ge2 : GoodK (L.Dm : ℝ) ρ (e2K ρ) := good_e2 hρ0 hD1
  have gE : GoodK (L.Dm : ℝ) ρ E1 := good_E1 hρ0 hD1
  set B := Ball 0 r m with hB
  set x1 : Lt 0 r := Sum.inr j0 with hx1
  set x2 : Lt 0 r := Sum.inr i0 with hx2
  have hpair : ∀ t1 t2 a c, ∑ u ∈ B, NF L u t1 a * NF L u⁻¹ t2 c ≤ e1K L ρ t1 a * e2K ρ t2 c :=
    fun t1 t2 a c => pair_Fr_inv hρ B t1 t2 a c
  have hnnF : ∀ u : G 0 r, RNN (NF L u) := fun u => (gNF u).1
  have hKLnn : ∀ A A' P P' Q Q' K : RK, GoodK (L.Dm : ℝ) ρ A → GoodK (L.Dm : ℝ) ρ A' →
      GoodK (L.Dm : ℝ) ρ P → GoodK (L.Dm : ℝ) ρ P' → GoodK (L.Dm : ℝ) ρ Q →
      GoodK (L.Dm : ℝ) ρ Q' → GoodK (L.Dm : ℝ) ρ K →
      0 ≤ chainL (KL L x1 x2 A A' P P' Q Q' K) E1 1 m :=
    fun A A' P P' Q Q' K hA hA' hP hP' hQ hQ' hK =>
      chainL_nonneg _ _ (fun k hk =>
        (KL_good x1 x2 A A' P P' Q Q' K gNG gNF hA hA' hP hP' hQ hQ' hK k hk).1) E1_nn 1 m
  calc ∑ p ∈ (B ×ˢ B ×ˢ B).filter (Pt i0 j0 (t' + 1)), ‖Fr L 1 m (gg i0 j0 (t' + 1) p)‖
      ≤ ∑ p ∈ (B ×ˢ B ×ˢ B).filter (Pt i0 j0 (t' + 1)),
          chainL (KL L x1 x2 (NF L p.1) (NF L p.1⁻¹) (NF L p.2.1)
            (NF L p.2.1⁻¹) (NF L p.2.2) (NF L p.2.2⁻¹) (e1K L ρ)) E1 1 m :=
        Finset.sum_le_sum fun p hp =>
          shape_one hρ hD1 i0 j0 t' m p (Finset.mem_filter.mp hp).2
    _ ≤ ∑ p ∈ B ×ˢ B ×ˢ B,
          chainL (KL L x1 x2 (NF L p.1) (NF L p.1⁻¹) (NF L p.2.1)
            (NF L p.2.1⁻¹) (NF L p.2.2) (NF L p.2.2⁻¹) (e1K L ρ)) E1 1 m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => hKLnn _ _ _ _ _ _ _ (gNF _) (gNF _) (gNF _) (gNF _) (gNF _) (gNF _) ge1)
    _ = ∑ a ∈ B, ∑ b ∈ B, ∑ s ∈ B,
          chainL (KL L x1 x2 (NF L a) (NF L a⁻¹) (NF L b)
            (NF L b⁻¹) (NF L s) (NF L s⁻¹) (e1K L ρ)) E1 1 m := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_product]
    _ ≤ ∑ a ∈ B, ∑ b ∈ B,
          chainL (KL L x1 x2 (NF L a) (NF L a⁻¹) (NF L b)
            (NF L b⁻¹) (e1K L ρ) (e2K ρ) (e1K L ρ)) E1 1 m :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          collapse_flat B (fun s => NF L s) (fun s => NF L s⁻¹) (e1K L ρ) (e2K ρ) hpair hnnF
            [NF L 1, NG L, NF L a, NG L, NF L b, NG L, NF L (genL x1), NG L, NF L b⁻¹, NG L]
            [NG L, NF L (genL x2), NG L] [NG L, e1K L ρ, NG L, NF L a⁻¹]
            (by repeat' first | exact good_nil | exact fun _ _ => norm_nonneg _ | apply good_cons)
            (by repeat' first | exact good_nil | exact fun _ _ => norm_nonneg _ | apply good_cons)
            (by repeat' first | exact good_nil | exact ge1.1 | exact fun _ _ => norm_nonneg _
                              | apply good_cons)
            1 m
    _ ≤ ∑ a ∈ B,
          chainL (KL L x1 x2 (NF L a) (NF L a⁻¹) (e1K L ρ) (e2K ρ) (e1K L ρ) (e2K ρ)
            (e1K L ρ)) E1 1 m :=
        Finset.sum_le_sum fun a _ =>
          collapse_flat B (fun b => NF L b) (fun b => NF L b⁻¹) (e1K L ρ) (e2K ρ) hpair hnnF
            [NF L 1, NG L, NF L a, NG L]
            [NG L, NF L (genL x1), NG L]
            [NG L, e1K L ρ, NG L, NF L (genL x2), NG L, e2K ρ, NG L, e1K L ρ, NG L, NF L a⁻¹]
            (by repeat' first | exact good_nil | exact fun _ _ => norm_nonneg _ | apply good_cons)
            (by repeat' first | exact good_nil | exact fun _ _ => norm_nonneg _ | apply good_cons)
            (by repeat' first | exact good_nil | exact ge1.1 | exact ge2.1
                              | exact fun _ _ => norm_nonneg _ | apply good_cons)
            1 m
    _ ≤ chainL (KL L x1 x2 (e1K L ρ) (e2K ρ) (e1K L ρ) (e2K ρ) (e1K L ρ) (e2K ρ)
            (e1K L ρ)) E1 1 m :=
        collapse_flat B (fun a => NF L a) (fun a => NF L a⁻¹) (e1K L ρ) (e2K ρ) hpair hnnF
          [NF L 1, NG L]
          [NG L, e1K L ρ, NG L, NF L (genL x1), NG L, e2K ρ, NG L, e1K L ρ, NG L,
            NF L (genL x2), NG L, e2K ρ, NG L, e1K L ρ, NG L]
          []
          (by repeat' first | exact good_nil | exact fun _ _ => norm_nonneg _ | apply good_cons)
          (by repeat' first | exact good_nil | exact ge1.1 | exact ge2.1
                            | exact fun _ _ => norm_nonneg _ | apply good_cons)
          good_nil 1 m
    _ ≤ (L.Dm : ℝ) ^ 20 * ((m : ℝ) + 1) ^ 19 * ρ ^ m := by
        have h := chainL_Bd hρ0 hD0
          (KL L x1 x2 (e1K L ρ) (e2K ρ) (e1K L ρ) (e2K ρ) (e1K L ρ) (e2K ρ) (e1K L ρ)) E1
          (KL_good x1 x2 _ _ _ _ _ _ _ gNG gNF ge1 ge2 ge1 ge2 ge1 ge2 ge1) gE.1 gE.2 1 m
        have hlen : (KL L x1 x2 (e1K L ρ) (e2K ρ) (e1K L ρ) (e2K ρ) (e1K L ρ) (e2K ρ)
            (e1K L ρ)).length = 19 := rfl
        rw [hlen] at h
        simpa [Bd] using h

theorem c2_main {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (hD1 : 1 ≤ L.Dm) (i0 j0 : Fin r) (m : ℕ) :
    ‖∑ i : Fin m → Option (Lt 0 r), (C2count i0 j0 (iprod i) : ℂ) * (Bprod L m i).trace‖ ≤
      (m : ℝ) * ((L.Dm : ℝ) * ((L.Dm : ℝ) ^ 20 * ((m : ℝ) + 1) ^ 19 * ρ ^ m)) := by
  have hD0 : (0 : ℝ) ≤ L.Dm := Nat.cast_nonneg _
  rw [sum_eq]
  have h1 : ∀ t ∈ Finset.Ico 1 (m + 1),
      ‖∑ p ∈ (Ball 0 r m ×ˢ Ball 0 r m ×ˢ Ball 0 r m).filter (Pt i0 j0 t),
          (Fr L 1 m (gg i0 j0 t p)).trace‖ ≤
        (L.Dm : ℝ) * ((L.Dm : ℝ) ^ 20 * ((m : ℝ) + 1) ^ 19 * ρ ^ m) := by
    intro t ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by have := (Finset.mem_Ico.mp ht).1; omega⟩
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => fro_trace L _).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (shape2 hρ hD1 i0 j0 t' m) hD0
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum h1).trans (le_of_eq ?_))
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
  simp

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3b
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r : ℕ}
/-- The two-loop coefficient: `a (ρ m_j ρ⁻¹ σ m_i σ⁻¹)^t a⁻¹`. -/
theorem norm_sum_c2count_mul_trace_Bprod_le (L : Lin 0 r) (R : ℝ) (hR : 0 ≤ R) (hX : ∀ j, ‖Xop L j‖ ≤ R)
    (i0 j0 : Fin r) :
    ∃ (C : ℝ) (k : ℕ), ∀ m : ℕ, 1 ≤ m →
      ‖∑ i : Fin m → Option (Lt 0 r), (C2count i0 j0 (iprod i) : ℂ) * (Bprod L m i).trace‖ ≤
        C * (m : ℝ) ^ k * R ^ m := by
  by_cases hD : L.Dm = 0
  · refine ⟨0, 0, fun m _ => ?_⟩
    have : IsEmpty (Fin L.Dm) := by rw [hD]; infer_instance
    have h0 : ∀ i : Fin m → Option (Lt 0 r), (Bprod L m i).trace = 0 := fun i => by
      simp [Matrix.trace]
    simp [h0]
  · have hD1 : 1 ≤ L.Dm := Nat.one_le_iff_ne_zero.mpr hD
    have hDr : (1 : ℝ) ≤ L.Dm := by exact_mod_cast hD1
    refine ⟨(L.Dm : ℝ) ^ 21 * 2 ^ 19, 20, fun m hm => ?_⟩
    refine (c2_main hX hD1 i0 j0 m).trans ?_
    set Dr : ℝ := (L.Dm : ℝ) with hDr_def
    set X : ℝ := R ^ m with hXdef
    have hX0 : 0 ≤ X := pow_nonneg hR m
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hD0 : (0 : ℝ) ≤ Dr := by linarith
    have hM : ((m : ℝ) + 1) ^ 19 ≤ 2 ^ 19 * (m : ℝ) ^ 19 := by
      calc ((m : ℝ) + 1) ^ 19 ≤ (2 * (m : ℝ)) ^ 19 :=
            pow_le_pow_left₀ (by linarith) (by linarith) 19
        _ = 2 ^ 19 * (m : ℝ) ^ 19 := by ring
    calc (m : ℝ) * (Dr * (Dr ^ 20 * ((m : ℝ) + 1) ^ 19 * X))
        = Dr ^ 21 * (m : ℝ) * ((m : ℝ) + 1) ^ 19 * X := by ring
      _ ≤ Dr ^ 21 * (m : ℝ) * (2 ^ 19 * (m : ℝ) ^ 19) * X := by gcongr
      _ = Dr ^ 21 * 2 ^ 19 * (m : ℝ) ^ 20 * X := by ring

end RandomInvolutions.Dev.PartP3b
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias norm_sum_c2count_mul_trace_Bprod_le := RandomInvolutions.Dev.PartP3b.norm_sum_c2count_mul_trace_Bprod_le

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r s : ℕ}
/-!
# Part W, words: the two-loop factorizations of a cyclically reduced word and `C2count`

The first half is the reduced-word toolkit of Part F (normal forms by van der Waerden's trick),
copied here because Parts do not import each other.  The second half identifies the folds
`Par u j i` with the tuples counted by `C2count i j (a * wprod u * a⁻¹)`.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## Aliases -/

/-! ## Generic group identities

(`simp`, `rw` and `group` do not see through the instance path of `G r s`, so identities are
proved in a generic group and applied with `exact`.) -/

/-! ## The inverse word -/
/-- The inverse word: reversed, with `bar` applied. -/
def ibar (u : List (Lt r s)) : List (Lt r s) := (u.map bar).reverse

@[simp] theorem ibar_nil : ibar ([] : List (Lt r s)) = [] := rfl

@[simp] theorem length_ibar (u : List (Lt r s)) : (ibar u).length = u.length := by simp [ibar]

/-! ## Non-reduced words are not shortest -/

/-! ## Repeated words -/
/-- `Z` repeated `k` times. -/
def rep (Z : List (Lt r s)) (k : ℕ) : List (Lt r s) := (List.replicate k Z).flatten

@[simp] theorem rep_zero (Z : List (Lt r s)) : rep Z 0 = [] := by simp [rep]

theorem rep_succ (Z : List (Lt r s)) (k : ℕ) : rep Z (k + 1) = Z ++ rep Z k := by
  simp [rep, List.replicate_succ]

@[simp] theorem rep_nil (k : ℕ) : rep ([] : List (Lt r s)) k = [] := by simp [rep]

@[simp] theorem length_rep (Z : List (Lt r s)) (k : ℕ) : (rep Z k).length = k * Z.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, List.length_append, ih]; ring

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
open RandomInvolutions
open RandomInvolutions.Dev
theorem solution {r : ℕ} (L : Lin 0 r) (R : ℝ) (hR : 0 ≤ R) (hX : ∀ j, ‖Xop L j‖ ≤ R)
    (i0 j0 : Fin r) :
    ∃ (C : ℝ) (k : ℕ), ∀ m : ℕ, 1 ≤ m →
      ‖∑ i : Fin m → Option (Lt 0 r), (C2count i0 j0 (iprod i) : ℂ) * (Bprod L m i).trace‖ ≤
        C * (m : ℝ) ^ k * R ^ m := by
  exact RandomInvolutions.Dev.norm_sum_c2count_mul_trace_Bprod_le L R hR hX i0 j0
end
end
