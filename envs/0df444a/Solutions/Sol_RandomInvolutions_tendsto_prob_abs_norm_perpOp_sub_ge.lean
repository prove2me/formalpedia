-- Prove2me | solution 1 for RandomInvolutions.tendsto_prob_abs_norm_perpOp_sub_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T11:49:29.577113+00:00
-- url     : https://prove2.me/submissions/d839725d-4aca-41f3-8549-872cbad96270

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_StrongConv
import Definitions.Def_DerandSq_permOp
import Definitions.Def_ZigZagStrong_ZigZag_Models
import Definitions.Def_RandomInvolutions
import Theorems.Thm_BordenaveCollins_tendsto_re_trTau_pow_rpow
import Theorems.Thm_RandomInvolutions_prob_norm_perpOp_ge_le

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

/-- `u` is cyclically reduced: no letter is followed (cyclically) by its inverse. A one-letter
word `[m_j]` is not cyclically reduced in this sense; the empty word is. -/
def CycRed {r s : ℕ} (u : List (Lt r s)) : Prop :=
  ∀ t : Fin u.length,
    u.get ⟨(t.val + 1) % u.length, Nat.mod_lt _ (by have := t.2; omega)⟩ ≠ bar (u.get t)

/-! ## Involutions and the representation they define -/

/-- The permutation of a letter (the free letters `Sum.inl _` do not occur in `Lt 0 r`). -/
def letterPermI {r N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) :
    Lt 0 r → Equiv.Perm (Fin N)
  | Sum.inl _ => 1
  | Sum.inr i => (τ i).1

/-- The permutation of a word (product in the order the letters appear). -/
def wordPermI {r N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (u : List (Lt 0 r)) :
    Equiv.Perm (Fin N) :=
  (u.map (letterPermI τ)).prod

/-! ## The conditional model `M(N, κ)` -/

/-! ## Expected fixed points -/

/-! ## Operators -/

/-! ## Colourings with loops of the closed path of a word

A path is `x : Fin (u.length + 1) → α` with `x t = letter_t (x (t+1))` (so that
`x t = wordPermI τ (u.drop t) y`). Step `t` with letter `m_i` is a *loop* of colour `i` at
`x t` when `x t = x (t+1)` (that vertex is fixed by `τ_i`), and a *pair* `{x t, x (t+1)}` of
`τ_i` otherwise. -/

section Colour

variable {r : ℕ} (u : List (Lt 0 r))

/-- A finite set of unordered pairs is a partial matching: no loops, pairwise disjoint. -/
def PMat {α : Type*} (E : Finset (Sym2 α)) : Prop :=
  (∀ p ∈ E, ¬ p.IsDiag) ∧ ∀ p ∈ E, ∀ q ∈ E, (∃ a, a ∈ p ∧ a ∈ q) → p = q

/-- The vertices forced to be fixed points of `τ_i` (loops of colour `i`). -/
def Ls {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) (i : Fin r) : Finset α :=
  (univ.filter fun t : Fin u.length => u.get t = Sum.inr i ∧ x t.castSucc = x t.succ).image
    fun t => x t.castSucc

/-- The unordered pairs forced to be 2-cycles of `τ_i`. -/
def Ps {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) (i : Fin r) :
    Finset (Sym2 α) :=
  (univ.filter fun t : Fin u.length => u.get t = Sum.inr i ∧ x t.castSucc ≠ x t.succ).image
    fun t => s(x t.castSucc, x t.succ)

/-- A closed path consistent with involutions: under each colour the pairs form a partial
matching and no loop vertex lies on a pair. -/
def GoodL {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) : Prop :=
  (∀ i, PMat (Ps u x i)) ∧ (∀ i, ∀ a ∈ Ls u x i, ∀ p ∈ Ps u x i, a ∉ p) ∧
    x 0 = x (Fin.last _)

/-- The first position where `x` takes the value `x t`. -/
def canon {n : ℕ} {α : Type*} [DecidableEq α] (x : Fin n → α) (t : Fin n) : Fin n :=
  (univ.filter fun s => x s = x t).min' ⟨t, by simp⟩

/-- The number of values of a path. -/
def nv {n : ℕ} {α : Type*} [DecidableEq α] (x : Fin n → α) : ℕ := (univ.image x).card

/-- Canonical good colourings (with loops) of the closed path of `u`. -/
def CGL : Finset (Fin (u.length + 1) → Fin (u.length + 1)) := by
  classical exact (univ.filter fun c => canon c = c).filter (GoodL u)

/-- The number `e_i` of pairs of colour `i`. -/
def eK (c : Fin (u.length + 1) → Fin (u.length + 1)) (i : Fin r) : ℕ := (Ps u c i).card

/-- The number `f_i` of loops of colour `i`. -/
def fK (c : Fin (u.length + 1) → Fin (u.length + 1)) (i : Fin r) : ℕ := (Ls u c i).card

/-- `e = ∑ e_i`. -/
def Ecount (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℕ := ∑ i, eK u c i

/-- `f = ∑ f_i`. -/
def Fcount (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℕ := ∑ i, fK u c i

end Colour

/-- The weight of a colouring with `v` vertices, `e i` pairs and `f i` loops of colour `i`:
`[N]_v ∏_i [κ_i]_{f_i} ∏_{l < e_i} (N - κ_i - 2l) / [N]_{f_i + 2 e_i}`. The `i`-th factor is the
probability that an involution with `κ_i` fixed points fixes `f_i` given points and contains
`e_i` given disjoint pairs (on `f_i + 2 e_i` distinct points). -/
def wtF {r : ℕ} (N : ℕ) (κ : Fin r → ℕ) (v : ℕ) (e f : Fin r → ℕ) : ℝ :=
  (N.descFactorial v : ℝ) *
    ∏ i, ((((κ i).descFactorial (f i) : ℝ) *
        ∏ l ∈ range (e i), ((N : ℝ) - κ i - 2 * l)) / (N.descFactorial (f i + 2 * e i) : ℝ))

/-- The weight of a colouring of `u`. -/
def wtK {r : ℕ} (u : List (Lt 0 r)) (N : ℕ) (κ : Fin r → ℕ)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℝ :=
  wtF N κ (nv c) (eK u c) (fK u c)

/-! ## The coefficient counts -/

/-! ## Scalar polynomials as group-algebra elements -/

end RandomInvolutions.Dev

end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartK2
variable {r : ℕ}
/-!
# Part K2: the expansion of expected fixed points to second order along a ray

`tendsto_mul_expFixK_sub_first_order` and `expFixK_le`, from the stubs of Parts F, C2, W, the limits of the weights
(`PartK2_Wt`) and the published `BordenaveCollins.tendsto_expFix` (at `κ = 0`).
-/
/-! ## Fixed points: conjugation, torsion, crude bound -/
lemma fixCount_conj {N : ℕ} (p q : Equiv.Perm (Fin N)) :
    fixCount (p * q * p⁻¹) = fixCount q := by
  unfold fixCount
  refine (card_bij' (fun x _ => p⁻¹ x) (fun x _ => p x) ?_ ?_ ?_ ?_).trans rfl
  · intro x hx
    rw [mem_filter] at hx ⊢
    refine ⟨mem_univ _, ?_⟩
    have h := congrArg (fun y => p⁻¹ y) hx.2
    simpa using h
  · intro x hx
    rw [mem_filter] at hx ⊢
    refine ⟨mem_univ _, ?_⟩
    simp [hx.2]
  · intro x _; simp
  · intro x _; simp

lemma fixCount_hom_conj {H : Type*} [Group H] {N : ℕ} (φ : H →* Equiv.Perm (Fin N)) (a w : H) :
    fixCount (φ (a * w * a⁻¹)) = fixCount (φ w) := by
  rw [map_mul, map_mul, map_inv, fixCount_conj]

lemma expFixK_conj (N : ℕ) (κ : Fin r → ℕ) (a w : G 0 r) :
    expFixK r N κ (a * w * a⁻¹) = expFixK r N κ w := by
  unfold expFixK expFixOn
  congr 1
  refine sum_congr rfl fun τ _ => ?_
  exact congrArg _ (fixCount_hom_conj (homK τ) a w)

lemma wprod_single (i : Fin r) : (wprod [Sum.inr i] : G 0 r) = mI i := by
  simp [wprod, genL, mI]

end RandomInvolutions.Dev.PartK2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-! ## Part P3: growth of the coefficient moments (linearization and first passage) -/

/-! ## Part U2: the upper tail in the conditional model, uniformly along rays -/
theorem prob_norm_perpOp_ge_le {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (hz : adj z = z) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (N : ℕ) (κ : Fin r → ℕ), AdmK N κ → 1 ≤ N →
      StrongConv.uniformProb (fun τ : OmK r N κ => ‖regOp z‖ + ε ≤ ‖perpOp (homK τ) z‖) ≤
        C * lam κ / N + C * lam κ ^ 3 / (N : ℝ) ^ 2 := by
  exact RandomInvolutions.prob_norm_perpOp_ge_le hD z hz ε hε

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
theorem uniformExp_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    StrongConv.uniformExp (fun _ : Ω => c) = c := by
  unfold StrongConv.uniformExp
  have : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [Finset.sum_const, Finset.card_univ]

theorem uniformExp_mono {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) (h : ∀ ω, f ω ≤ g ω) :
    StrongConv.uniformExp f ≤ StrongConv.uniformExp g := by
  unfold StrongConv.uniformExp
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω) (Nat.cast_nonneg _)

theorem uniformProb_eq_exp {Ω : Type*} [Fintype Ω] (A : Ω → Prop) :
    StrongConv.uniformProb A = StrongConv.uniformExp (fun ω => if A ω then (1 : ℝ) else 0) := by
  unfold StrongConv.uniformProb StrongConv.uniformExp
  congr 1
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem uniformProb_le_one {Ω : Type*} [Fintype Ω] (A : Ω → Prop) :
    StrongConv.uniformProb A ≤ 1 := by
  unfold StrongConv.uniformProb
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.card_le_univ _)

/-- The marginal of a product of uniform laws. -/
theorem uniformExp_coord {A : Type*} [Fintype A] [Nonempty A] (i : Fin r) (f : A → ℝ) :
    StrongConv.uniformExp (fun τ : Fin r → A => f (τ i)) = StrongConv.uniformExp f := by
  unfold StrongConv.uniformExp
  have h1 : ∑ τ : Fin r → A, f (τ i) =
      (Fintype.card ({j : Fin r // j ≠ i} → A) : ℝ) * ∑ a, f a := by
    rw [← (Equiv.funSplitAt i A).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_symm_mk, dite_true]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Finset.sum_const, Finset.card_univ]
  have h2 : (Fintype.card (Fin r → A) : ℝ) =
      (Fintype.card ({j : Fin r // j ≠ i} → A) : ℝ) * Fintype.card A := by
    rw [Fintype.card_congr (Equiv.funSplitAt i A), Fintype.card_prod]
    push_cast; ring
  have h3 : (Fintype.card ({j : Fin r // j ≠ i} → A) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h4 : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [h1, h2]
  field_simp

/-! ## The mixture -/
theorem sum_fibre (N : ℕ) (κ : Fin r → ℕ) (F : (Fin r → Inv N) → ℝ) :
    ∑ τ ∈ univ.filter (fun τ : Fin r → Inv N => ∀ i, fixCount (τ i).1 = κ i), F τ =
      ∑ τ : OmK r N κ, F (fun i => (τ i).1) := by
  rw [Finset.sum_subtype (p := fun τ : Fin r → Inv N => ∀ i, fixCount (τ i).1 = κ i)
    (univ.filter (fun τ : Fin r → Inv N => ∀ i, fixCount (τ i).1 = κ i)) (by simp)]
  exact Fintype.sum_equiv (Equiv.subtypePiEquivPi
    (p := fun _ (σ : Inv N) => fixCount σ.1 = κ _)) _ _ (fun _ => rfl)

theorem card_fibre (N : ℕ) (κ : Fin r → ℕ) :
    ((univ.filter (fun τ : Fin r → Inv N => ∀ i, fixCount (τ i).1 = κ i)).card : ℝ) =
      Fintype.card (OmK r N κ) := by
  have := sum_fibre N κ (fun _ => (1 : ℝ))
  simpa [Finset.card_univ] using this

theorem fixCount_le (N : ℕ) (π : Equiv.Perm (Fin N)) : fixCount π ≤ N := by
  unfold fixCount
  simpa using Finset.card_le_univ (univ.filter fun x => π x = x)

theorem mix_arith (a T S c : ℝ) (h : a = c) (hc : ¬ c = 0) : a / T * (S / c) = S / T := by
  subst h; field_simp

/-- The uniform law on `r`-tuples of involutions is the mixture of the conditional models. -/
theorem mixture (N : ℕ) (F : (Fin r → ZigZagStrong.ZigZag.Involution N) → ℝ) :
    StrongConv.uniformExp F =
      ∑ κ : Fin r → Fin (N + 1),
        StrongConv.uniformProb (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
            ∀ i, fixCount (τ i).1 = κ i) *
          StrongConv.uniformExp (fun τ : OmK r N (fun i => (κ i : ℕ)) => F (fun i => (τ i).1)) := by
  have hterm : ∀ κ : Fin r → Fin (N + 1),
      StrongConv.uniformProb (fun τ : Fin r → Inv N => ∀ i, fixCount (τ i).1 = κ i) *
          StrongConv.uniformExp (fun τ : OmK r N (fun i => (κ i : ℕ)) => F (fun i => (τ i).1)) =
        (∑ τ ∈ univ.filter (fun τ : Fin r → Inv N =>
          (fun i => (⟨fixCount (τ i).1, Nat.lt_succ_of_le (fixCount_le N _)⟩ : Fin (N + 1))) = κ),
            F τ) / (Fintype.card (Fin r → Inv N) : ℝ) := by
    intro κ
    have hfilt : univ.filter (fun τ : Fin r → Inv N =>
          (fun i => (⟨fixCount (τ i).1, Nat.lt_succ_of_le (fixCount_le N _)⟩ : Fin (N + 1))) = κ) =
        univ.filter (fun τ : Fin r → Inv N => ∀ i, fixCount (τ i).1 = (κ i : ℕ)) := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Fin.ext_iff]
    rw [hfilt, sum_fibre N (fun i => (κ i : ℕ)) F]
    unfold StrongConv.uniformProb StrongConv.uniformExp
    have hc := card_fibre (r := r) N (fun i => (κ i : ℕ))
    by_cases h0 : (Fintype.card (OmK r N (fun i => (κ i : ℕ))) : ℝ) = 0
    · have : IsEmpty (OmK r N (fun i => (κ i : ℕ))) := by
        rw [← Fintype.card_eq_zero_iff]; exact_mod_cast h0
      simp
    · exact mix_arith _ _ _ _ (by rw [← hc]; congr!) h0
  rw [Finset.sum_congr rfl (fun κ _ => hterm κ), ← Finset.sum_div]
  unfold StrongConv.uniformExp
  congr 1
  exact (Finset.sum_fiberwise univ (fun τ : Fin r → Inv N =>
    (fun i => (⟨fixCount (τ i).1, Nat.lt_succ_of_le (fixCount_le N _)⟩ : Fin (N + 1)))) F).symm

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
theorem swap_invol {N : ℕ} (τ : Equiv.Perm (Fin N)) (hτ : ∀ z, τ (τ z) = z) (x y : Fin N)
    (h : (τ x = x ∧ τ y = y) ∨ τ x = y) :
    ∀ z, (τ * Equiv.swap x y) ((τ * Equiv.swap x y) z) = z := by
  have hc : τ * Equiv.swap x y = Equiv.swap x y * τ := by
    rw [Equiv.mul_swap_eq_swap_mul]
    rcases h with ⟨h1, h2⟩ | h1
    · rw [h1, h2]
    · have h2 : τ y = x := by rw [← h1, hτ]
      rw [h1, h2, Equiv.swap_comm]
  have hττ : τ * τ = 1 := by ext z; simp [hτ z]
  have : (τ * Equiv.swap x y) * (τ * Equiv.swap x y) = 1 := by
    calc (τ * Equiv.swap x y) * (τ * Equiv.swap x y)
        = (τ * Equiv.swap x y) * (Equiv.swap x y * τ) := by rw [← hc]
      _ = τ * (Equiv.swap x y * Equiv.swap x y) * τ := by group
      _ = 1 := by rw [Equiv.swap_mul_self, mul_one, hττ]
  intro z
  have := congrArg (fun p : Equiv.Perm (Fin N) => p z) this
  simpa using this

/-- Multiply by the transposition `(x y)` when the result is an involution. -/
def flip {N : ℕ} (p : Inv N × Fin N × Fin N) : Inv N × Fin N × Fin N :=
  if h : ∀ z, (p.1.1 * Equiv.swap p.2.1 p.2.2) ((p.1.1 * Equiv.swap p.2.1 p.2.2) z) = z then
    (⟨p.1.1 * Equiv.swap p.2.1 p.2.2, h⟩, p.2) else p

theorem flip_eq {N : ℕ} (τ : Inv N) (x y : Fin N) (h : (τ.1 x = x ∧ τ.1 y = y) ∨ τ.1 x = y) :
    flip (τ, x, y) = (⟨τ.1 * Equiv.swap x y, swap_invol τ.1 τ.2 x y h⟩, x, y) := by
  unfold flip
  rw [dif_pos (swap_invol τ.1 τ.2 x y h)]

/-- Ordered pairs of distinct fixed points, summed over involutions, are as many as ordered
2-cycles. -/
theorem card_fixpairs_eq (N : ℕ) :
    (univ.filter fun p : Inv N × Fin N × Fin N =>
        p.2.1 ≠ p.2.2 ∧ p.1.1 p.2.1 = p.2.1 ∧ p.1.1 p.2.2 = p.2.2).card =
      (univ.filter fun p : Inv N × Fin N × Fin N =>
        p.2.1 ≠ p.2.2 ∧ p.1.1 p.2.1 = p.2.2).card := by
  apply Finset.card_nbij' flip flip
  · rintro ⟨τ, x, y⟩ hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rw [flip_eq τ x y (Or.inl hp.2)]
    refine ⟨hp.1, ?_⟩
    simp [hp.2.2]
  · rintro ⟨τ, x, y⟩ hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rw [flip_eq τ x y (Or.inr hp.2)]
    have h2 : τ.1 y = x := by rw [← hp.2, τ.2]
    refine ⟨hp.1, ?_, ?_⟩
    · simp [h2]
    · simp [hp.2]
  · rintro ⟨τ, x, y⟩ hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp
    rw [flip_eq τ x y (Or.inl hp.2)]
    rw [flip_eq _ x y (Or.inr (by simp [hp.2.2]))]
    simp [mul_assoc]
  · rintro ⟨τ, x, y⟩ hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp
    have h2 : τ.1 y = x := by rw [← hp.2, τ.2]
    rw [flip_eq τ x y (Or.inr hp.2)]
    rw [flip_eq _ x y (Or.inl (by simp [h2, hp.2]))]
    simp [mul_assoc]

theorem card_prod_fibre {A B : Type*} [Fintype A] [Fintype B] (P : A → B → Prop)
    [DecidablePred fun p : A × B => P p.1 p.2] [∀ a, DecidablePred (P a)] :
    (univ.filter fun p : A × B => P p.1 p.2).card = ∑ a, (univ.filter fun b => P a b).card := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_prod_type]

theorem card_fix_offDiag {N : ℕ} (τ : Equiv.Perm (Fin N)) :
    (univ.filter fun q : Fin N × Fin N => q.1 ≠ q.2 ∧ τ q.1 = q.1 ∧ τ q.2 = q.2).card =
      fixCount τ * fixCount τ - fixCount τ := by
  unfold fixCount
  rw [← Finset.offDiag_card]
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
  tauto

theorem card_two_cycles {N : ℕ} (τ : Equiv.Perm (Fin N)) :
    (univ.filter fun q : Fin N × Fin N => q.1 ≠ q.2 ∧ τ q.1 = q.2).card + fixCount τ = N := by
  have h1 : (univ.filter fun q : Fin N × Fin N => q.1 ≠ q.2 ∧ τ q.1 = q.2).card =
      (univ.filter fun x : Fin N => ¬ τ x = x).card := by
    apply Finset.card_nbij' (fun q => q.1) (fun x => (x, τ x))
    · rintro ⟨x, y⟩ hq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hq ⊢
      rw [hq.2]; exact fun h => hq.1 h.symm
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      exact ⟨fun h => hx h.symm, trivial⟩
    · rintro ⟨x, y⟩ hq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hq
      simp [hq.2]
    · intro x _; rfl
  unfold fixCount
  rw [h1, add_comm]
  simpa using Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin N)))
    (fun x => τ x = x)

/-- `E[#fix²] = N` for a uniform involution. -/
theorem sum_fix_sq (N : ℕ) :
    ∑ τ : Inv N, (fixCount τ.1 : ℝ) ^ 2 = (Fintype.card (Inv N) : ℝ) * N := by
  have h : ∑ τ : Inv N, (univ.filter fun q : Fin N × Fin N =>
        q.1 ≠ q.2 ∧ τ.1 q.1 = q.1 ∧ τ.1 q.2 = q.2).card =
      ∑ τ : Inv N, (univ.filter fun q : Fin N × Fin N => q.1 ≠ q.2 ∧ τ.1 q.1 = q.2).card := by
    have e3 := card_fixpairs_eq N
    rw [card_prod_fibre (fun (τ : Inv N) (q : Fin N × Fin N) =>
        q.1 ≠ q.2 ∧ τ.1 q.1 = q.1 ∧ τ.1 q.2 = q.2),
      card_prod_fibre (fun (τ : Inv N) (q : Fin N × Fin N) => q.1 ≠ q.2 ∧ τ.1 q.1 = q.2)] at e3
    convert e3
  have hR : ∑ τ : Inv N, ((fixCount τ.1 : ℝ) ^ 2 - fixCount τ.1) =
      ∑ τ : Inv N, ((N : ℝ) - fixCount τ.1) := by
    have h' := congrArg (fun n : ℕ => (n : ℝ)) h
    simp only [Nat.cast_sum] at h'
    convert h' using 2 with τ _ τ _
    · rw [card_fix_offDiag, Nat.cast_sub (Nat.le_mul_self _)]
      push_cast; ring
    · have := card_two_cycles τ.1
      have h2 : ((univ.filter fun q : Fin N × Fin N => q.1 ≠ q.2 ∧ τ.1 q.1 = q.2).card : ℝ) +
          fixCount τ.1 = N := by exact_mod_cast this
      linarith
  simp only [Finset.sum_sub_distrib] at hR
  have : ∑ τ : Inv N, (N : ℝ) = (Fintype.card (Inv N) : ℝ) * N := by
    simp [Finset.sum_const, Finset.card_univ]
  linarith

instance (N : ℕ) : Nonempty (Inv N) := ⟨⟨1, fun _ => rfl⟩⟩

theorem fixCount_exp_le_sqrt (N : ℕ) :
    StrongConv.uniformExp (fun τ : Inv N => (fixCount τ.1 : ℝ)) ≤ Real.sqrt N := by
  unfold StrongConv.uniformExp
  have hI : (0 : ℝ) < Fintype.card (Inv N) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hI]
  have h1 := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Inv N)))
    (f := fun τ => (fixCount τ.1 : ℝ))
  rw [sum_fix_sq, Finset.card_univ] at h1
  have h0 : (0 : ℝ) ≤ ∑ τ : Inv N, (fixCount τ.1 : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  refine (pow_le_pow_iff_left₀ h0 (by positivity) (two_ne_zero)).1 ?_
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  nlinarith [h1]

/-- A uniform involution of `Fin N` has at most `√N + 1` fixed points on average. -/
theorem fixCount_exp_le (N : ℕ) :
    StrongConv.uniformExp (fun τ : ZigZagStrong.ZigZag.Involution N => (fixCount τ.1 : ℝ)) ≤
      Real.sqrt N + 1 :=
  (fixCount_exp_le_sqrt N).trans (by linarith)

end RandomInvolutions.Dev.PartX
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartX
variable {r : ℕ}
/-! ## Admissibility of the fixed-point count of an involution -/
theorem adm_of_inv {N : ℕ} (τ : Inv N) : fixCount τ.1 ≤ N ∧ fixCount τ.1 % 2 = N % 2 := by
  refine ⟨fixCount_le N _, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : (show Function.End (Fin N) from ⇑τ.1) ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext z
    exact τ.2 z
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  have hc : Fintype.card (Function.fixedPoints (τ.1 : Fin N → Fin N)) = fixCount τ.1 := by
    unfold fixCount
    rw [Fintype.card_subtype]
    rfl
  rw [hc, Fintype.card_fin] at h
  exact h.symm

/-! ## Integrating an affine conditional bound -/
theorem uniformExp_affine (N : ℕ) (a b : ℝ) :
    StrongConv.uniformExp (fun τ : Fin r → Inv N =>
        a * (1 + ∑ i, (fixCount (τ i).1 : ℝ)) + b) =
      a * (1 + ∑ i : Fin r,
        StrongConv.uniformExp (fun τ : Fin r → Inv N => (fixCount (τ i).1 : ℝ))) + b := by
  unfold StrongConv.uniformExp
  have hc : (Fintype.card (Fin r → Inv N) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  field_simp

end RandomInvolutions.Dev.PartX
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical InnerProductSpace
noncomputable section
namespace RandomInvolutions.Dev.PartL2
set_option linter.unusedSectionVars false
variable {r s : ℕ} {D : ℕ}
/-!
# Part L2: the lower tail for uniform random involutions (`lower_unif`)

As bc214's Part L: the trace formula `trace_perpOp`, positivity of `(Y* Y)^p`, Markov's
inequality for the fixed-point counts (`expFix_unif_le`: `E[fix g] = O(√N)` for `g ≠ 1`) and
faithfulness of the trace (published `BordenaveCollins.tendsto_re_trTau_pow_rpow`).
-/
/-! ## The vector state: the moments `trTau ((x* x)^p)` are nonnegative -/
lemma leftReg_apply {Γ : Type*} [Group Γ] (g : Γ) (f : DerandSq.L2 Γ) (h : Γ) :
    DerandSq.leftReg g f h = f (g⁻¹ * h) := rfl

lemma star_leftReg {Γ : Type*} [Group Γ] (g : Γ) :
    star (DerandSq.leftReg g : DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) = DerandSq.leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [leftReg_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq]
  simp

lemma leftReg_one {Γ : Type*} [Group Γ] :
    (DerandSq.leftReg (1 : Γ) : DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) = 1 := by
  ext f h
  simp [leftReg_apply]

lemma leftReg_mul {Γ : Type*} [Group Γ] (a b : Γ) :
    (DerandSq.leftReg (a * b) : DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) =
      DerandSq.leftReg a * DerandSq.leftReg b := by
  ext f h
  simp [leftReg_apply, mul_assoc]

/-- The left-regular representation as a monoid homomorphism. -/
def lregHom (Γ : Type*) [Group Γ] : Γ →* (DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) where
  toFun g := DerandSq.leftReg g
  map_one' := leftReg_one
  map_mul' a b := leftReg_mul a b

/-- `δ_g`. -/
def delta {Γ : Type*} (g : Γ) : DerandSq.L2 Γ := lp.single 2 g (1 : ℂ)

lemma leftReg_delta_one {Γ : Type*} [Group Γ] (g : Γ) :
    DerandSq.leftReg g (delta 1) = delta g := by
  ext h
  simp only [leftReg_apply, delta, lp.single_apply, Pi.single_apply]
  by_cases hh : h = g
  · subst hh; simp
  · rw [if_neg (by intro h'; apply hh; exact (inv_mul_eq_one.mp h').symm), if_neg hh]

lemma inner_delta {Γ : Type*} [Group Γ] (g : Γ) :
    ⟪delta (1 : Γ), delta g⟫_ℂ = if g = 1 then 1 else 0 := by
  unfold delta
  rw [lp.inner_single_left]
  simp [lp.single_apply, Pi.single_apply, eq_comm]

abbrev EE (D r s : ℕ) := PiLp 2 (fun _ : Fin D => DerandSq.L2 (G r s))

lemma tensorOp_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Matrix (Fin D) (Fin D) ℂ) (T : H →L[ℂ] H)
    (y : PiLp 2 (fun _ : Fin D => H)) (a : Fin D) :
    AccessibleMaps.tensorOp A T y a = ∑ b, A a b • T (y b) := by
  simp [AccessibleMaps.tensorOp, AccessibleMaps.inject, Pi.single_apply]

/-- `e_a ⊗ δ_e`. -/
abbrev vv (D r s : ℕ) (a : Fin D) : EE D r s := PiLp.single 2 a (delta 1)

/-- The vector state `D⁻¹ ∑_a ⟪e_a ⊗ δ_1, Y (e_a ⊗ δ_1)⟫`. -/
def tauOp (Y : (EE D r s) →L[ℂ] (EE D r s)) : ℂ :=
  (D : ℂ)⁻¹ * ∑ a : Fin D, ⟪vv D r s a, Y (vv D r s a)⟫_ℂ

lemma inner_vv_tensorOp (A : Matrix (Fin D) (Fin D) ℂ) (g : G r s) (a : Fin D) :
    ⟪vv D r s a, AccessibleMaps.tensorOp A (DerandSq.leftReg g) (vv D r s a)⟫_ℂ =
      if g = 1 then A a a else 0 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single a]
  · rw [tensorOp_apply, Finset.sum_eq_single a]
    · simp only [PiLp.single_apply, if_true, inner_smul_right, leftReg_delta_one, inner_delta]
      split_ifs <;> simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro b _ hb
    simp [hb]
  · simp

lemma trTau_eq_tauOp (y : MG D r s) : trTau y = tauOp (regOp y) := by
  unfold trTau tauOp regOp opOf
  congr 1
  simp only [_root_.sum_apply, inner_sum, inner_vv_tensorOp]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.sum_const_zero]
  by_cases h1 : (1 : G r s) ∈ y.coeff.support
  · simp [h1, Matrix.trace]
  · have : y.coeff 1 = 0 := Finsupp.notMem_support_iff.mp h1
    simp [h1, this]

lemma tauOp_re (Y : (EE D r s) →L[ℂ] (EE D r s)) :
    (tauOp Y).re = (D : ℝ)⁻¹ * ∑ a : Fin D, (⟪vv D r s a, Y (vv D r s a)⟫_ℂ).re := by
  unfold tauOp
  have h1 : ((D : ℂ)⁻¹) = (((D : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [h1, Complex.re_ofReal_mul, Complex.re_sum]

lemma re_tauOp_nonneg (X : (EE D r s) →L[ℂ] (EE D r s)) (hX : 0 ≤ X) : 0 ≤ (tauOp X).re := by
  have hpos : X.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive X).mp hX
  rw [tauOp_re]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => hpos.re_inner_nonneg_right _)

end RandomInvolutions.Dev.PartL2
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartT2
variable {r : ℕ}
variable {s D : ℕ}
/-!
# Part T2: the core theorem (`tendsto_prob_abs_norm_perpOp_sub_ge`)

From `upper_unif` (applied to `z = adj x * x`) and `lower_unif`.
-/
/-! ## The adjoint on `MG D r s` -/
theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_mul_inv_rev (a b : G r s) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b

theorem adj_eq_sum (x : MG D r s) :
    adj x = x.coeff.sum fun g A => MonoidAlgebra.single g⁻¹ A.conjTranspose := rfl

theorem adj_zero : adj (0 : MG D r s) = 0 := by
  simp [adj]

theorem adj_add (x y : MG D r s) : adj (x + y) = adj x + adj y := by
  rw [adj_eq_sum, adj_eq_sum, adj_eq_sum, MonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun g => by simp)
    (fun g A B => by rw [Matrix.conjTranspose_add, MonoidAlgebra.single_add])

theorem adj_single (g : G r s) (A : Matrix (Fin D) (Fin D) ℂ) :
    adj (MonoidAlgebra.single g A) = MonoidAlgebra.single g⁻¹ A.conjTranspose := by
  rw [adj_eq_sum, MonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (by simp)

theorem adj_mul (x y : MG D r s) : adj (x * y) = adj y * adj x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, adj_zero, mul_zero]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, adj_add, adj_add, h₁, h₂, mul_add]
  | single g A =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [mul_zero, adj_zero, zero_mul]
    | add y₁ y₂ h₁ h₂ => rw [mul_add, adj_add, adj_add, h₁, h₂, add_mul]
    | single h B =>
      rw [MonoidAlgebra.single_mul_single, adj_single, adj_single, adj_single,
        MonoidAlgebra.single_mul_single, Matrix.conjTranspose_mul, g_mul_inv_rev]

theorem adj_adj (x : MG D r s) : adj (adj x) = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [adj_zero, adj_zero]
  | add x₁ x₂ h₁ h₂ => rw [adj_add, adj_add, h₁, h₂]
  | single g A =>
    rw [adj_single, adj_single, Matrix.conjTranspose_conjTranspose, g_inv_inv]

theorem adj_adj_mul_self (x : MG D r s) : adj (adj x * x) = adj x * x := by
  rw [adj_mul, adj_adj]

end RandomInvolutions.Dev.PartT2
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartT2
variable {r : ℕ}
/-! ## The left-regular representation -/
theorem leftReg_apply {Γ : Type*} [Group Γ] (g : Γ) (f : DerandSq.L2 Γ) (h : Γ) :
    DerandSq.leftReg g f h = f (g⁻¹ * h) := rfl

theorem star_leftReg {Γ : Type*} [Group Γ] (g : Γ) :
    star (DerandSq.leftReg g : DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) = DerandSq.leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [leftReg_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq]
  simp

theorem leftReg_one {Γ : Type*} [Group Γ] :
    (DerandSq.leftReg (1 : Γ) : DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) = 1 := by
  ext f h
  simp [leftReg_apply]

theorem leftReg_mul {Γ : Type*} [Group Γ] (a b : Γ) :
    (DerandSq.leftReg (a * b) : DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) =
      DerandSq.leftReg a * DerandSq.leftReg b := by
  ext f h
  simp [leftReg_apply, mul_assoc]

/-- The left-regular representation as a monoid homomorphism. -/
def lregHom (Γ : Type*) [Group Γ] : Γ →* (DerandSq.L2 Γ →L[ℂ] DerandSq.L2 Γ) where
  toFun g := DerandSq.leftReg g
  map_one' := leftReg_one
  map_mul' a b := leftReg_mul a b

end RandomInvolutions.Dev.PartT2
end
end

section
open Finset BordenaveCollins
open scoped Classical InnerProductSpace
set_option linter.unusedSectionVars false
noncomputable section
namespace RandomInvolutions.Dev.PartB
open DerandSq
/-! ## The model side -/

end RandomInvolutions.Dev.PartB
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}

/-! ## Glue (proved here) -/
theorem uniformProb_nonneg {Ω : Type*} [Fintype Ω] (A : Ω → Prop) :
    0 ≤ StrongConv.uniformProb A := by
  unfold StrongConv.uniformProb
  positivity

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartX
variable {r : ℕ}
theorem mix_affine (N : ℕ) (F : (Fin r → Inv N) → ℝ) (a b : ℝ) (ha : 0 ≤ a)
    (h : ∀ κ : Fin r → ℕ, AdmK N κ →
      StrongConv.uniformExp (fun τ : OmK r N κ => F (fun i => (τ i).1)) ≤ a * lam κ + b) :
    StrongConv.uniformExp F ≤ a * (1 + r * (Real.sqrt N + 1)) + b := by
  have step1 : StrongConv.uniformExp F ≤ StrongConv.uniformExp (fun τ : Fin r → Inv N =>
      a * (1 + ∑ i, (fixCount (τ i).1 : ℝ)) + b) := by
    rw [mixture N F, mixture N (fun τ : Fin r → Inv N => a * (1 + ∑ i, (fixCount (τ i).1 : ℝ)) + b)]
    refine Finset.sum_le_sum fun κ _ => mul_le_mul_of_nonneg_left ?_ (uniformProb_nonneg _)
    by_cases hne : Nonempty (OmK r N (fun i => (κ i : ℕ)))
    · obtain ⟨τ0⟩ := hne
      have hA : AdmK N (fun i => (κ i : ℕ)) := fun i => by
        have := adm_of_inv (τ0 i).1
        rwa [(τ0 i).2] at this
      refine (h _ hA).trans (le_of_eq ?_)
      have : (fun τ : OmK r N (fun i => (κ i : ℕ)) =>
          a * (1 + ∑ i, (fixCount ((τ i).1).1 : ℝ)) + b) =
          fun _ => a * lam (fun i => (κ i : ℕ)) + b := by
        funext τ
        unfold lam
        congr 3
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [(τ i).2]
      have hne' : Nonempty (OmK r N (fun i => (κ i : ℕ))) := ⟨τ0⟩
      rw [this, uniformExp_const]
    · rw [not_nonempty_iff] at hne
      unfold StrongConv.uniformExp
      simp
  refine step1.trans ?_
  rw [uniformExp_affine]
  have h2 : ∀ i : Fin r,
      StrongConv.uniformExp (fun τ : Fin r → Inv N => (fixCount (τ i).1 : ℝ)) ≤
        Real.sqrt N + 1 := fun i => by
    rw [uniformExp_coord i (fun σ : Inv N => (fixCount σ.1 : ℝ))]
    exact fixCount_exp_le N
  have h3 : ∑ i : Fin r,
      StrongConv.uniformExp (fun τ : Fin r → Inv N => (fixCount (τ i).1 : ℝ)) ≤
        r * (Real.sqrt N + 1) := by
    calc _ ≤ ∑ _i : Fin r, (Real.sqrt N + 1) := Finset.sum_le_sum fun i _ => h2 i
      _ = r * (Real.sqrt N + 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have := mul_le_mul_of_nonneg_left h3 ha
  linarith

end RandomInvolutions.Dev.PartX
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
theorem uniformProb_mono {Ω : Type*} [Fintype Ω] (A B : Ω → Prop) (h : ∀ ω, A ω → B ω) :
    StrongConv.uniformProb A ≤ StrongConv.uniformProb B := by
  unfold StrongConv.uniformProb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card fun ω hω => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
/-!
# Part C2, counting: involutions with `k` fixed points containing given fixed points and pairs

A constraint set `E : Finset (Sym2 (Fin N))` encodes fixed points as diagonal pairs `s(a, a)` and
2-cycles as off-diagonal pairs. The number `cnt N k E` of involutions with exactly `k` fixed
points satisfying the constraints is computed by a double count:
`cnt (dg A ∪ P) * [N]_{f + 2e} = #InvK * [k]_f * ∏_{l<e} (N - k - 2l)`.
-/
lemma desc_succ_real (N n : ℕ) :
    (N.descFactorial (n + 1) : ℝ) = ((N : ℝ) - n) * N.descFactorial n := by
  rw [Nat.descFactorial_succ]
  rcases Nat.lt_or_ge N n with h | h
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 h]; simp
  · rw [Nat.cast_mul, Nat.cast_sub h]

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {N k : ℕ}
/-- The involution `τ` satisfies the constraints of `E`. -/
def Cont (E : Finset (Sym2 (Fin N))) (τ : InvK N k) : Prop :=
  ∀ a b, s(a, b) ∈ E → τ.1.1 a = b

/-- The number of involutions with `k` fixed points satisfying `E`. -/
def cnt (N k : ℕ) (E : Finset (Sym2 (Fin N))) : ℕ :=
  (univ.filter fun τ : InvK N k => Cont E τ).card

lemma cnt_empty : cnt N k ∅ = Fintype.card (InvK N k) := by
  simp [cnt, Cont]

lemma cont_insert (E : Finset (Sym2 (Fin N))) (a b : Fin N) (τ : InvK N k) :
    Cont (insert s(a, b) E) τ ↔ τ.1.1 a = b ∧ Cont E τ := by
  constructor
  · intro h
    exact ⟨h a b (mem_insert_self _ _), fun x y hxy => h x y (mem_insert_of_mem hxy)⟩
  · rintro ⟨hab, h⟩ x y hxy
    rcases mem_insert.1 hxy with e | e
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · rw [← hab]; exact τ.1.2 y
    · exact h x y e

lemma cont_mono {E F : Finset (Sym2 (Fin N))} (h : E ⊆ F) (τ : InvK N k) (hτ : Cont F τ) :
    Cont E τ := fun a b hab => hτ a b (h hab)

lemma cnt_eq_sum (E : Finset (Sym2 (Fin N))) (a : Fin N) :
    cnt N k E = ∑ b, cnt N k (insert s(a, b) E) := by
  unfold cnt
  rw [card_eq_sum_card_fiberwise (f := fun τ : InvK N k => τ.1.1 a) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun b _ => ?_
  congr 1
  ext τ
  simp only [mem_filter, mem_univ, true_and, cont_insert]
  tauto

/-! ### Conjugation -/
lemma fixCount_conj (π σ : Equiv.Perm (Fin N)) : fixCount (π * σ * π⁻¹) = fixCount σ := by
  unfold fixCount
  refine card_nbij' (fun x => π⁻¹ x) (fun x => π x) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
    have := congrArg (fun y => π⁻¹ y) hx
    simpa using this
  · intro x hx
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
    simp [hx]
  · intro x _; simp
  · intro x _; simp

/-- Conjugation of an involution with `k` fixed points. -/
def conjK (π : Equiv.Perm (Fin N)) (τ : InvK N k) : InvK N k :=
  ⟨⟨π * τ.1.1 * π⁻¹, fun x => by simp [Equiv.Perm.mul_apply, τ.1.2]⟩, by
    show fixCount (π * τ.1.1 * π⁻¹) = k
    rw [fixCount_conj]; exact τ.2⟩

lemma conjK_apply (π : Equiv.Perm (Fin N)) (τ : InvK N k) (x : Fin N) :
    (conjK π τ).1.1 x = π (τ.1.1 (π⁻¹ x)) := rfl

lemma conjK_inv (π : Equiv.Perm (Fin N)) (τ : InvK N k) : conjK π⁻¹ (conjK π τ) = τ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rw [conjK_apply, conjK_apply]
  simp

lemma cont_conj (E : Finset (Sym2 (Fin N))) (π : Equiv.Perm (Fin N)) (τ : InvK N k)
    (h : Cont E τ) : Cont (E.image (Sym2.map π)) (conjK π τ) := by
  intro a b hab
  obtain ⟨p, hp, e⟩ := mem_image.1 hab
  induction p using Sym2.inductionOn with
  | hf x y =>
    rw [Sym2.map_mk, Sym2.eq_iff] at e
    rw [conjK_apply]
    rcases e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [h x y hp]
    · have : τ.1.1 y = x := by rw [← h x y hp]; exact τ.1.2 x
      simp [this]

lemma cnt_image_le (E : Finset (Sym2 (Fin N))) (π : Equiv.Perm (Fin N)) :
    cnt N k E ≤ cnt N k (E.image (Sym2.map π)) := by
  unfold cnt
  refine card_le_card_of_injOn (conjK π) ?_ ?_
  · intro τ hτ
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hτ ⊢
    exact cont_conj E π τ hτ
  · intro τ _ τ' _ h
    rw [← conjK_inv π τ, ← conjK_inv π τ', h]

lemma cnt_image (E : Finset (Sym2 (Fin N))) (π : Equiv.Perm (Fin N)) :
    cnt N k (E.image (Sym2.map π)) = cnt N k E := by
  refine le_antisymm ?_ (cnt_image_le E π)
  have h := cnt_image_le (k := k) (E.image (Sym2.map π)) π⁻¹
  have e : (E.image (Sym2.map π)).image (Sym2.map ⇑π⁻¹) = E := by
    rw [image_image]
    have : (Sym2.map ⇑π⁻¹ ∘ Sym2.map ⇑π) = id := by
      funext p
      induction p using Sym2.inductionOn with
      | hf x y => simp
    rw [this, image_id]
  rwa [e] at h

/-! ### Supports -/
/-- The points covered by `E`. -/
def supp (E : Finset (Sym2 (Fin N))) : Finset (Fin N) :=
  univ.filter fun x => ∃ y, s(x, y) ∈ E

lemma mem_supp (E : Finset (Sym2 (Fin N))) (x : Fin N) : x ∈ supp E ↔ ∃ y, s(x, y) ∈ E := by
  simp [supp]

lemma supp_insert (E : Finset (Sym2 (Fin N))) (a b : Fin N) :
    supp (insert s(a, b) E) = insert a (insert b (supp E)) := by
  ext x
  simp only [mem_supp, mem_insert]
  constructor
  · rintro ⟨y, e | e⟩
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨y, e⟩)
  · rintro (rfl | rfl | ⟨y, hy⟩)
    · exact ⟨b, Or.inl rfl⟩
    · exact ⟨a, Or.inl Sym2.eq_swap⟩
    · exact ⟨y, Or.inr hy⟩

lemma supp_union (E F : Finset (Sym2 (Fin N))) : supp (E ∪ F) = supp E ∪ supp F := by
  ext x
  simp only [mem_supp, mem_union, exists_or]

lemma image_fix (E : Finset (Sym2 (Fin N))) (π : Equiv.Perm (Fin N))
    (h : ∀ x ∈ supp E, π x = x) : E.image (Sym2.map π) = E := by
  have key : ∀ p ∈ E, Sym2.map π p = id p := by
    intro p hp
    induction p using Sym2.inductionOn with
    | hf x y =>
      rw [Sym2.map_mk, h x ((mem_supp E x).2 ⟨y, hp⟩),
        h y ((mem_supp E y).2 ⟨x, by rw [Sym2.eq_swap]; exact hp⟩)]
      rfl
  rw [image_congr key, image_id]

lemma cnt_move (E : Finset (Sym2 (Fin N))) (π : Equiv.Perm (Fin N)) (p : Sym2 (Fin N))
    (h : ∀ x ∈ supp E, π x = x) :
    cnt N k (insert (Sym2.map π p) E) = cnt N k (insert p E) := by
  rw [← cnt_image (insert p E) π, image_insert, image_fix E π h]

lemma cnt_bad (E : Finset (Sym2 (Fin N))) (a b : Fin N) (ha : a ∉ supp E) (hb : b ∈ supp E) :
    cnt N k (insert s(a, b) E) = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro τ _ h
  rw [cont_insert] at h
  obtain ⟨y, hy⟩ := (mem_supp E b).1 hb
  have h1 : τ.1.1 b = y := h.2 b y hy
  have h2 : τ.1.1 b = a := by rw [← h.1]; exact τ.1.2 a
  apply ha
  rw [mem_supp]
  refine ⟨b, ?_⟩
  have : y = a := h1.symm.trans h2
  subst this
  rw [Sym2.eq_swap]; exact hy

/-! ### The two recursions -/
/-- The number of fixed-point constraints. -/
def dcount (E : Finset (Sym2 (Fin N))) : ℕ := ((supp E).filter fun a => s(a, a) ∈ E).card

lemma cnt_diag_supp (E : Finset (Sym2 (Fin N))) (a : Fin N) (ha : a ∈ supp E) :
    cnt N k (insert s(a, a) E) = if s(a, a) ∈ E then cnt N k E else 0 := by
  split_ifs with h
  · rw [insert_eq_of_mem h]
  · unfold cnt
    rw [card_eq_zero, filter_eq_empty_iff]
    intro τ _ hτ
    rw [cont_insert] at hτ
    obtain ⟨y, hy⟩ := (mem_supp E a).1 ha
    have : y = a := by rw [← hτ.2 a y hy]; exact hτ.1
    subst this
    exact h hy

lemma sum_diag (E : Finset (Sym2 (Fin N))) :
    ∑ a : Fin N, cnt N k (insert s(a, a) E) = k * cnt N k E := by
  have h : ∀ a : Fin N, cnt N k (insert s(a, a) E) =
      ∑ τ ∈ univ.filter (fun τ : InvK N k => Cont E τ), if τ.1.1 a = a then 1 else 0 := by
    intro a
    unfold cnt
    rw [← card_filter, filter_filter]
    congr 1
    ext τ
    simp only [mem_filter, mem_univ, true_and, cont_insert]
    tauto
  simp only [h]
  rw [sum_comm, sum_congr rfl (g := fun _ => k)]
  · rw [sum_const, smul_eq_mul, mul_comm]; rfl
  · intro τ _
    rw [← card_filter]; exact τ.2

lemma fix_step_nat (E : Finset (Sym2 (Fin N))) (a : Fin N) (ha : a ∉ supp E) :
    (N - (supp E).card) * cnt N k (insert s(a, a) E) + dcount E * cnt N k E =
      k * cnt N k E := by
  rw [← sum_diag E, ← sum_sdiff (subset_univ (supp E))]
  congr 1
  · rw [sum_congr rfl (g := fun _ => cnt N k (insert s(a, a) E))]
    · rw [sum_const, smul_eq_mul, card_sdiff_of_subset (subset_univ _), card_univ,
        Fintype.card_fin]
    · intro a' ha'
      have ha' : a' ∉ supp E := (mem_sdiff.1 ha').2
      have := cnt_move (k := k) E (Equiv.swap a a') s(a, a) (fun x hx =>
        Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact ha hx) (by rintro rfl; exact ha' hx))
      rw [Sym2.map_mk, Equiv.swap_apply_left] at this
      exact this
  · rw [sum_congr rfl (fun a' ha' => cnt_diag_supp E a' ha'), sum_ite, sum_const_zero, add_zero,
      sum_const, smul_eq_mul]
    rfl

lemma pair_step_nat (E : Finset (Sym2 (Fin N))) (a b : Fin N) (ha : a ∉ supp E)
    (hb : b ∉ supp E) (hab : a ≠ b) :
    cnt N k E = cnt N k (insert s(a, a) E) +
      (N - ((supp E).card + 1)) * cnt N k (insert s(a, b) E) := by
  rw [cnt_eq_sum E a, ← sum_sdiff (subset_univ (insert a (supp E))), add_comm]
  congr 1
  · rw [sum_insert ha, sum_eq_zero (fun b' hb' => cnt_bad E a b' ha hb'), add_zero]
  · rw [sum_congr rfl (g := fun _ => cnt N k (insert s(a, b) E))]
    · rw [sum_const, smul_eq_mul, card_sdiff_of_subset (subset_univ _), card_univ,
        Fintype.card_fin, card_insert_of_notMem ha]
    · intro b' hb'
      simp only [mem_sdiff, mem_univ, true_and, mem_insert, not_or] at hb'
      have := cnt_move (k := k) E (Equiv.swap b b') s(a, b) (fun x hx =>
        Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hb hx)
          (by rintro rfl; exact hb'.2 hx))
      rw [Sym2.map_mk, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hab (Ne.symm hb'.1)] at this
      exact this

lemma fix_step (E : Finset (Sym2 (Fin N))) (a : Fin N) (ha : a ∉ supp E) :
    ((N : ℝ) - (supp E).card) * cnt N k (insert s(a, a) E) =
      ((k : ℝ) - dcount E) * cnt N k E := by
  have h := fix_step_nat (k := k) E a ha
  have hle : (supp E).card ≤ N := (card_le_univ _).trans (Fintype.card_fin N).le
  have h' : (((N - (supp E).card : ℕ) : ℝ)) * cnt N k (insert s(a, a) E) +
      (dcount E : ℝ) * cnt N k E = (k : ℝ) * cnt N k E := by exact_mod_cast h
  rw [Nat.cast_sub hle] at h'
  linarith

lemma pair_combine (E : Finset (Sym2 (Fin N))) (a b : Fin N) (ha : a ∉ supp E)
    (hb : b ∉ supp E) (hab : a ≠ b) :
    ((N : ℝ) - (supp E).card) * ((N : ℝ) - (supp E).card - 1) * cnt N k (insert s(a, b) E) =
      ((N : ℝ) - (supp E).card - k + dcount E) * cnt N k E := by
  have h := pair_step_nat (k := k) E a b ha hb hab
  have hle : (supp E).card + 1 ≤ N := by
    have : (insert a (supp E)).card ≤ N := (card_le_univ _).trans (Fintype.card_fin N).le
    rwa [card_insert_of_notMem ha] at this
  have h' : (cnt N k E : ℝ) = cnt N k (insert s(a, a) E) +
      ((N - ((supp E).card + 1) : ℕ) : ℝ) * cnt N k (insert s(a, b) E) := by exact_mod_cast h
  rw [Nat.cast_sub hle] at h'
  push_cast at h'
  have h2 := fix_step (k := k) E a ha
  linear_combination (-((N : ℝ) - (supp E).card)) * h' - h2

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
/-! ### Diagonal constraints and partial matchings -/
/-- The diagonal pairs of a set of points. -/
def dg {α : Type*} [DecidableEq α] (A : Finset α) : Finset (Sym2 α) := A.image fun a => s(a, a)

lemma mem_dg {α : Type*} [DecidableEq α] (A : Finset α) (a b : α) :
    s(a, b) ∈ dg A ↔ a = b ∧ a ∈ A := by
  unfold dg
  rw [mem_image]
  constructor
  · rintro ⟨x, hx, e⟩
    rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, hx⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {N k : ℕ}
lemma supp_dg (A : Finset (Fin N)) : supp (dg A) = A := by
  ext x
  rw [mem_supp]
  constructor
  · rintro ⟨y, hy⟩
    exact ((mem_dg A x y).1 hy).2
  · intro hx
    exact ⟨x, (mem_dg A x x).2 ⟨rfl, hx⟩⟩

lemma pmat_insert (E : Finset (Sym2 (Fin N))) (a b : Fin N) (h : PMat (insert s(a, b) E))
    (hn : s(a, b) ∉ E) : PMat E ∧ a ≠ b ∧ a ∉ supp E ∧ b ∉ supp E := by
  refine ⟨⟨fun p hp => h.1 p (mem_insert_of_mem hp), fun p hp q hq =>
    h.2 p (mem_insert_of_mem hp) q (mem_insert_of_mem hq)⟩, ?_, ?_, ?_⟩
  · intro e
    exact h.1 _ (mem_insert_self _ _) (Sym2.mk_isDiag_iff.2 e)
  · intro ha
    obtain ⟨y, hy⟩ := (mem_supp E a).1 ha
    have := h.2 _ (mem_insert_self _ _) _ (mem_insert_of_mem hy)
      ⟨a, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
    exact hn (this ▸ hy)
  · intro hb
    obtain ⟨y, hy⟩ := (mem_supp E b).1 hb
    have := h.2 _ (mem_insert_self _ _) _ (mem_insert_of_mem hy)
      ⟨b, Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
    exact hn (this ▸ hy)

lemma card_supp (E : Finset (Sym2 (Fin N))) : PMat E → (supp E).card = 2 * E.card := by
  induction E using Finset.induction_on with
  | empty => intro _; simp [supp]
  | insert p E hp ih =>
    induction p using Sym2.inductionOn with
    | hf a b =>
      intro h
      obtain ⟨hE, hab, ha, hb⟩ := pmat_insert E a b h hp
      rw [supp_insert, card_insert_of_notMem, card_insert_of_notMem hb, ih hE,
        card_insert_of_notMem hp]
      · ring
      · simp [hab, ha]

lemma disjoint_supp (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N)))
    (hAP : ∀ a ∈ A, ∀ p ∈ P, a ∉ p) : Disjoint A (supp P) := by
  rw [disjoint_left]
  intro x hx hx'
  obtain ⟨y, hy⟩ := (mem_supp P x).1 hx'
  exact hAP x hx _ hy (Sym2.mem_mk_left _ _)

lemma card_union_supp (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N))) (hP : PMat P)
    (hAP : ∀ a ∈ A, ∀ p ∈ P, a ∉ p) : (A ∪ supp P).card = A.card + 2 * P.card := by
  rw [card_union_of_disjoint (disjoint_supp A P hAP), card_supp P hP]

lemma supp_dg_union (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N))) :
    supp (dg A ∪ P) = A ∪ supp P := by
  rw [supp_union, supp_dg]

lemma dcount_dg_union (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N))) (hP : PMat P) :
    dcount (dg A ∪ P) = A.card := by
  unfold dcount
  congr 1
  ext a
  rw [mem_filter, supp_dg_union, mem_union, mem_union, mem_dg]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h.2
    · exact absurd (Sym2.mk_isDiag_iff.2 rfl) (hP.1 _ h)
  · intro ha
    exact ⟨Or.inl ha, Or.inl ⟨rfl, ha⟩⟩

/-- Fixed points only. -/
lemma cnt_dg (A : Finset (Fin N)) :
    (cnt N k (dg A) : ℝ) * (N.descFactorial A.card : ℝ) =
      (Fintype.card (InvK N k) : ℝ) * (k.descFactorial A.card : ℝ) := by
  induction A using Finset.induction_on with
  | empty => simp [dg, cnt_empty]
  | insert a A ha ih =>
    have hs : a ∉ supp (dg A) := by rw [supp_dg]; exact ha
    have h1 := fix_step (k := k) (dg A) a hs
    have hd : dcount (dg A) = A.card := by
      have := dcount_dg_union A ∅ ⟨by simp, by simp⟩
      rwa [union_empty] at this
    rw [supp_dg, hd] at h1
    have e : dg (insert a A) = insert s(a, a) (dg A) := by
      unfold dg; rw [image_insert]
    rw [e, card_insert_of_notMem ha, desc_succ_real, desc_succ_real]
    linear_combination (N.descFactorial A.card : ℝ) * h1 + ((k : ℝ) - A.card) * ih

/-- The main count, in product form. -/
lemma cnt_mul (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N))) :
    PMat P → (∀ a ∈ A, ∀ p ∈ P, a ∉ p) →
    (cnt N k (dg A ∪ P) : ℝ) * (N.descFactorial (A.card + 2 * P.card) : ℝ) =
      (Fintype.card (InvK N k) : ℝ) * (k.descFactorial A.card : ℝ) *
        ∏ l ∈ range P.card, ((N : ℝ) - k - 2 * l) := by
  induction P using Finset.induction_on with
  | empty =>
    intro _ _
    simpa using cnt_dg (k := k) A
  | insert p P hp ih =>
    induction p using Sym2.inductionOn with
    | hf a b =>
      intro h hAP
      obtain ⟨hE, hab, ha, hb⟩ := pmat_insert P a b h hp
      have hAP' : ∀ a ∈ A, ∀ p ∈ P, a ∉ p := fun x hx p hp' => hAP x hx p (mem_insert_of_mem hp')
      have ih' := ih hE hAP'
      have haA : a ∉ A := fun h' => hAP a h' _ (mem_insert_self _ _) (Sym2.mem_mk_left _ _)
      have hbA : b ∉ A := fun h' => hAP b h' _ (mem_insert_self _ _) (Sym2.mem_mk_right _ _)
      have hsa : a ∉ supp (dg A ∪ P) := by
        rw [supp_dg_union, mem_union]; tauto
      have hsb : b ∉ supp (dg A ∪ P) := by
        rw [supp_dg_union, mem_union]; tauto
      have hc := pair_combine (k := k) (dg A ∪ P) a b hsa hsb hab
      rw [supp_dg_union, card_union_supp A P hE hAP', dcount_dg_union A P hE] at hc
      push_cast at hc
      have e1 : A.card + 2 * (P.card + 1) = (A.card + 2 * P.card) + 1 + 1 := by ring
      rw [union_insert, card_insert_of_notMem hp, e1, desc_succ_real, desc_succ_real,
        prod_range_succ]
      push_cast
      linear_combination (N.descFactorial (A.card + 2 * P.card) : ℝ) * hc +
        ((N : ℝ) - k - 2 * P.card) * ih'

/-- The main count: the number of involutions with `k` fixed points fixing the points of `A`
and containing the disjoint pairs of `P`. -/
theorem cnt_formula (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N))) (hP : PMat P)
    (hAP : ∀ a ∈ A, ∀ p ∈ P, a ∉ p) :
    (cnt N k (dg A ∪ P) : ℝ) = (Fintype.card (InvK N k) : ℝ) *
      (((k.descFactorial A.card : ℝ) * ∏ l ∈ range P.card, ((N : ℝ) - k - 2 * l)) /
        (N.descFactorial (A.card + 2 * P.card) : ℝ)) := by
  have hle : A.card + 2 * P.card ≤ N := by
    rw [← card_union_supp A P hP hAP]
    exact (card_le_univ _).trans (Fintype.card_fin N).le
  have hD : (N.descFactorial (A.card + 2 * P.card) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega
  have h := cnt_mul (k := k) A P hP hAP
  rw [← mul_div_assoc, eq_div_iff hD, h]
  ring

/-- No involution contains two overlapping distinct pairs. -/
lemma cnt_not_pmat (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N)))
    (hnd : ∀ p ∈ P, ¬ p.IsDiag) (h : ¬ PMat P) : cnt N k (dg A ∪ P) = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro τ _ hτ'
  have hσ : Cont P τ := cont_mono subset_union_right τ hτ'
  apply h
  refine ⟨hnd, fun p hp q hq => ?_⟩
  induction p using Sym2.inductionOn with
  | hf a b =>
    induction q using Sym2.inductionOn with
    | hf a' b' =>
      rintro ⟨x, hx, hx'⟩
      have h1 := hσ a b hp
      have h2 := hσ a' b' hq
      have h3 : τ.1.1 b = a := by rw [← h1]; exact τ.1.2 a
      have h4 : τ.1.1 b' = a' := by rw [← h2]; exact τ.1.2 a'
      rw [Sym2.eq_iff]
      rcases Sym2.mem_iff.1 hx with rfl | rfl <;> rcases Sym2.mem_iff.1 hx' with rfl | rfl
      · exact Or.inl ⟨rfl, h1.symm.trans h2⟩
      · exact Or.inr ⟨rfl, h1.symm.trans h4⟩
      · exact Or.inr ⟨h3.symm.trans h2, rfl⟩
      · exact Or.inl ⟨h3.symm.trans h4, rfl⟩

/-- No involution fixes a point of one of its 2-cycles. -/
lemma cnt_meet (A : Finset (Fin N)) (P : Finset (Sym2 (Fin N)))
    (hnd : ∀ p ∈ P, ¬ p.IsDiag) (a : Fin N) (ha : a ∈ A) (p : Sym2 (Fin N)) (hp : p ∈ P)
    (hap : a ∈ p) : cnt N k (dg A ∪ P) = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro τ _ hτ
  have h1 : τ.1.1 a = a := hτ a a (mem_union_left _ ((mem_dg A a a).2 ⟨rfl, ha⟩))
  have hnd' := hnd p hp
  induction p using Sym2.inductionOn with
  | hf x y =>
    have h2 : τ.1.1 x = y := hτ x y (mem_union_right _ hp)
    rw [Sym2.mk_isDiag_iff] at hnd'
    rcases Sym2.mem_iff.1 hap with rfl | rfl
    · exact hnd' (h1.symm.trans h2)
    · apply hnd'
      have h3 : τ.1.1 a = x := by rw [← h2]; exact τ.1.2 x
      exact h3.symm.trans h1

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
/-! ### Existence -/
lemma nonempty_invK (N k : ℕ) (hk : k ≤ N) (hpar : k % 2 = N % 2) : Nonempty (InvK N k) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = k + (m + m) := ⟨(N - k) / 2, by omega⟩
  let e : Fin k ⊕ (Fin m ⊕ Fin m) ≃ Fin (k + (m + m)) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  let S : Equiv.Perm (Fin k ⊕ (Fin m ⊕ Fin m)) :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)
  have hSS : ∀ y, S (S y) = y := by
    rintro (i | j | j) <;> rfl
  have hS : ∀ y, S y = y ↔ ∃ i, y = Sum.inl i := by
    rintro (i | j | j) <;> simp [S]
  let σ : Equiv.Perm (Fin (k + (m + m))) := e.symm.trans (S.trans e)
  have hσ : ∀ x, σ x = e (S (e.symm x)) := fun x => rfl
  refine ⟨⟨⟨σ, fun x => by rw [hσ, hσ, e.symm_apply_apply, hSS, e.apply_symm_apply]⟩, ?_⟩⟩
  show fixCount σ = k
  unfold fixCount
  have hinj : Function.Injective fun i : Fin k => e (Sum.inl i) :=
    fun i j h => Sum.inl.inj (e.injective h)
  have : (univ.filter fun x => σ x = x) = (univ : Finset (Fin k)).image
      fun i => e (Sum.inl i) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image]
    rw [hσ]
    constructor
    · intro h
      have h' : S (e.symm x) = e.symm x := by
        apply e.injective; rw [h, e.apply_symm_apply]
      obtain ⟨i, hi⟩ := (hS _).1 h'
      exact ⟨i, by rw [← hi, e.apply_symm_apply]⟩
    · rintro ⟨i, rfl⟩
      rw [e.symm_apply_apply, (hS _).2 ⟨i, rfl⟩]
  rw [this, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {r : ℕ}
/-!
# Part C2: the counting formula with loops, and rationality along rays

Proofs of `RandomInvolutions.Dev.nonempty_omK`, `RandomInvolutions.Dev.expect_formulaK`, `RandomInvolutions.Dev.rationalK`.
-/
theorem nonempty_omK (N : ℕ) (κ : Fin r → ℕ) (hA : AdmK N κ) : Nonempty (OmK r N κ) :=
  ⟨fun i => (nonempty_invK N (κ i) (hA i).1 (hA i).2).some⟩

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-! ## Part C2: the counting formula with loops, and rationality along rays -/
alias nonempty_omK := RandomInvolutions.Dev.PartC2.nonempty_omK

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
lemma card_invK_ne_zero (N k : ℕ) (hk : k ≤ N) (hpar : k % 2 = N % 2) :
    (Fintype.card (InvK N k) : ℝ) ≠ 0 := by
  have := nonempty_invK N k hk hpar
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {r : ℕ} (u : List (Lt 0 r))
/-!
# Part C2, paths: the counting formula for the expected number of fixed points of a word in the
conditional model
-/
/-! ## Paths along a word -/
/-- `τ` realises the path `x`. -/
def Rz {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (x : Fin (u.length + 1) → Fin N) :
    Prop :=
  ∀ t : Fin u.length, x t.castSucc = letterPermI τ (u.get t) (x t.succ)

/-- The path of `y` under `τ`. -/
def path {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (y : Fin N) :
    Fin (u.length + 1) → Fin N :=
  fun t => wordPermI τ (u.drop t) y

lemma wordPermI_cons_apply {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (l : Lt 0 r)
    (ws : List (Lt 0 r)) (y : Fin N) :
    wordPermI τ (l :: ws) y = letterPermI τ l (wordPermI τ ws y) := by
  simp [wordPermI, Equiv.Perm.mul_apply]

lemma path_last {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (y : Fin N) :
    path u τ y (Fin.last _) = y := by
  simp [path, wordPermI]

lemma path_zero {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (y : Fin N) :
    path u τ y 0 = wordPermI τ u y := by
  simp [path]

lemma path_step {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (y : Fin N)
    (t : Fin u.length) :
    path u τ y t.castSucc = letterPermI τ (u.get t) (path u τ y t.succ) := by
  simp only [path, Fin.val_castSucc, Fin.val_succ]
  rw [List.drop_eq_getElem_cons t.2, wordPermI_cons_apply]
  rfl

lemma eq_path {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N)
    (x : Fin (u.length + 1) → Fin N) (hx : Rz u τ x) : x = path u τ (x (Fin.last _)) := by
  funext t
  induction t using Fin.reverseInduction with
  | last => rw [path_last]
  | cast t ih => rw [hx t, path_step, ← ih]

lemma fixCount_eq {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) :
    fixCount (wordPermI τ u) =
      (univ.filter fun x : Fin (u.length + 1) → Fin N =>
        Rz u τ x ∧ x 0 = x (Fin.last _)).card := by
  unfold fixCount
  symm
  refine card_nbij' (fun x => x (Fin.last _)) (path u τ) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
    have := eq_path u τ x hx.1
    conv_rhs => rw [← hx.2, this]
    rw [path_zero]
  · intro y hy
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hy ⊢
    exact ⟨fun t => path_step u τ y t, by rw [path_zero, path_last, hy]⟩
  · intro x hx
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hx
    exact (eq_path u τ x hx.1).symm
  · intro y _
    exact path_last u τ y

/-- The constraints of colour `i` of a path: loops as diagonal pairs, and pairs. -/
def EK {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) (i : Fin r) : Finset (Sym2 α) :=
  dg (Ls u x i) ∪ Ps u x i

lemma Ps_not_diag {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) (i : Fin r) :
    ∀ p ∈ Ps u x i, ¬ p.IsDiag := by
  intro p hp
  obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
  rw [Sym2.mk_isDiag_iff]
  exact (mem_filter.1 ht).2.2

lemma Rz_iff {N : ℕ} {κ : Fin r → ℕ} (ω : OmK r N κ) (x : Fin (u.length + 1) → Fin N) :
    Rz u (fun i => (ω i).1) x ↔ ∀ i, Cont (EK u x i) (ω i) := by
  constructor
  · intro h i a b hab
    rcases mem_union.1 hab with hab | hab
    · obtain ⟨rfl, ha⟩ := (mem_dg _ a b).1 hab
      obtain ⟨t, ht, rfl⟩ := mem_image.1 ha
      have ht := (mem_filter.1 ht).2
      have h' := h t
      rw [ht.1] at h'
      have h'' : x t.castSucc = (ω i).1.1 (x t.succ) := h'
      rw [← ht.2] at h''
      exact h''.symm
    · obtain ⟨t, ht, e⟩ := mem_image.1 hab
      have ht := (mem_filter.1 ht).2
      have h' := h t
      rw [ht.1] at h'
      have h'' : x t.castSucc = (ω i).1.1 (x t.succ) := h'
      rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [h'']; exact (ω i).1.2 _
      · exact h''.symm
  · intro h t
    rcases hl : u.get t with ⟨i, b⟩ | j
    · exact i.elim0
    · show x t.castSucc = (ω j).1.1 (x t.succ)
      by_cases hx : x t.castSucc = x t.succ
      · have hm : x t.castSucc ∈ Ls u x j :=
          mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hl, hx⟩, rfl⟩
        have := h j (x t.castSucc) (x t.castSucc)
          (mem_union_left _ ((mem_dg _ _ _).2 ⟨rfl, hm⟩))
        rw [← hx, this]
      · have hm : s(x t.castSucc, x t.succ) ∈ Ps u x j :=
          mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hl, hx⟩, rfl⟩
        have := h j (x t.castSucc) (x t.succ) (mem_union_right _ hm)
        rw [← this]; exact ((ω j).1.2 _).symm

lemma card_Rz {N : ℕ} (κ : Fin r → ℕ) (x : Fin (u.length + 1) → Fin N) :
    (univ.filter fun ω : OmK r N κ => Rz u (fun i => (ω i).1) x).card =
      ∏ i, cnt N (κ i) (EK u x i) := by
  have : (univ.filter fun ω : OmK r N κ => Rz u (fun i => (ω i).1) x) =
      Fintype.piFinset fun i => univ.filter fun τ : InvK N (κ i) => Cont (EK u x i) τ := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    exact Rz_iff u ω x
  rw [this, Fintype.card_piFinset]
  rfl

/-- The probability factor of one colour. -/
def Wf (N k f e : ℕ) : ℝ :=
  ((k.descFactorial f : ℝ) * ∏ l ∈ range e, ((N : ℝ) - k - 2 * l)) /
    (N.descFactorial (f + 2 * e) : ℝ)

/-- The weight of a path: the number of samples realising it. -/
def W (N : ℕ) (κ : Fin r → ℕ) {α : Type*} [DecidableEq α] (x : Fin (u.length + 1) → α) : ℝ :=
  if GoodL u x then
    ∏ i, ((Fintype.card (InvK N (κ i)) : ℝ) * Wf N (κ i) (Ls u x i).card (Ps u x i).card)
  else 0

lemma sum_fixCount (N : ℕ) (κ : Fin r → ℕ) :
    (∑ ω : OmK r N κ, (fixCount (wordPermI (fun i => (ω i).1) u) : ℝ)) =
      ∑ x : Fin (u.length + 1) → Fin N, W u N κ x := by
  have h0 : ∀ ω : OmK r N κ, (fixCount (wordPermI (fun i => (ω i).1) u) : ℝ) =
      ∑ x : Fin (u.length + 1) → Fin N,
        if Rz u (fun i => (ω i).1) x ∧ x 0 = x (Fin.last _) then (1 : ℝ) else 0 := by
    intro ω; rw [fixCount_eq, Finset.sum_boole]
  simp only [h0]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  by_cases hcl : x 0 = x (Fin.last _)
  · have h1 : (∑ ω : OmK r N κ,
        if Rz u (fun i => (ω i).1) x ∧ x 0 = x (Fin.last _) then (1 : ℝ) else 0) =
        ((univ.filter fun ω : OmK r N κ => Rz u (fun i => (ω i).1) x).card : ℝ) := by
      rw [← Finset.sum_boole]
      refine sum_congr rfl fun ω _ => ?_
      simp only [hcl, and_true]
    rw [h1, card_Rz]
    push_cast
    by_cases hg : GoodL u x
    · unfold W
      rw [if_pos hg]
      refine prod_congr rfl fun i _ => ?_
      exact cnt_formula _ _ (hg.1 i) (hg.2.1 i)
    · unfold W
      rw [if_neg hg]
      by_cases h1 : ∀ i, PMat (Ps u x i)
      · by_cases h2 : ∀ i, ∀ a ∈ Ls u x i, ∀ p ∈ Ps u x i, a ∉ p
        · exact absurd ⟨h1, h2, hcl⟩ hg
        · push Not at h2
          obtain ⟨i, a, ha, p, hp, hap⟩ := h2
          refine prod_eq_zero (mem_univ i) ?_
          have := cnt_meet (k := κ i) (Ls u x i) (Ps u x i) (Ps_not_diag u x i) a ha p hp hap
          unfold EK
          rw [this]; simp
      · push Not at h1
        obtain ⟨i, hi⟩ := h1
        refine prod_eq_zero (mem_univ i) ?_
        have := cnt_not_pmat (k := κ i) (Ls u x i) (Ps u x i) (Ps_not_diag u x i) hi
        unfold EK
        rw [this]; simp
  · unfold W
    rw [if_neg (fun h => hcl h.2.2)]
    simp [hcl]

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {n : ℕ} {α : Type*} [DecidableEq α]
/-! ## Canonical representatives of kernels -/
lemma canon_spec (x : Fin n → α) (t : Fin n) : x (canon x t) = x t := by
  unfold canon
  exact (mem_filter.1 (min'_mem (univ.filter fun s => x s = x t) _)).2

lemma canon_eq_of_ker {β : Type*} [DecidableEq β] (x : Fin n → α) (y : Fin n → β)
    (h : ∀ s t, x s = x t ↔ y s = y t) : canon x = canon y := by
  funext t
  simp only [canon, h]

lemma canon_ker (x : Fin n → α) (s t : Fin n) : canon x s = canon x t ↔ x s = x t := by
  constructor
  · intro h
    have := congrArg x h
    rwa [canon_spec x s, canon_spec x t] at this
  · intro h
    have : ∀ r, (x r = x s) ↔ (x r = x t) := fun r => by rw [h]
    simp only [canon, this]

lemma canon_canon (x : Fin n → α) : canon (canon x) = canon x :=
  canon_eq_of_ker _ _ (canon_ker x)

lemma canon_canon_apply (x : Fin n → α) (t : Fin n) : canon x (canon x t) = canon x t :=
  (canon_ker x _ _).2 (canon_spec x t)

lemma injOn_canon (x : Fin n → α) : Set.InjOn x (Set.range (canon x)) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
  rw [canon_spec x s, canon_spec x t] at h
  exact (canon_ker x s t).2 h

lemma comp_canon (x : Fin n → α) : x ∘ canon x = x := funext (canon_spec x)

lemma card_fiber [Fintype α] (c : Fin n → Fin n) (hc : canon c = c) :
    (univ.filter fun x : Fin n → α => canon x = c).card =
      (Fintype.card α).descFactorial (nv c) := by
  have hcc : ∀ t, c (c t) = c t := fun t => by
    have := canon_canon_apply c t; rwa [hc] at this
  have hmem : ∀ t, c t ∈ univ.image c := fun t => mem_image_of_mem _ (mem_univ _)
  rw [nv, ← Fintype.card_coe (univ.image c), ← Fintype.card_embedding_eq, ← card_univ]
  refine card_bij' (fun x hx => ⟨fun s => x s.1, ?_⟩) (fun φ _ => fun t => φ ⟨c t, hmem t⟩)
    (fun _ _ => mem_univ _) ?_ ?_ ?_
  · rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hx : canon x = c := (mem_filter.1 hx).2
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    obtain ⟨t', -, rfl⟩ := mem_image.1 hs'
    simp only at h
    apply Subtype.ext
    simp only
    rw [← hx] at h ⊢
    rw [canon_spec x t, canon_spec x t'] at h
    exact (canon_ker x t t').2 h
  · intro φ _
    simp only [mem_filter, mem_univ, true_and]
    refine Eq.trans ?_ hc
    refine canon_eq_of_ker _ _ fun s t => ?_
    rw [φ.injective.eq_iff, Subtype.mk.injEq]
  · intro x hx
    have hx : canon x = c := (mem_filter.1 hx).2
    funext t
    show x (c t) = x t
    rw [← hx]
    exact canon_spec x t
  · intro φ _
    apply Function.Embedding.ext
    rintro ⟨s, hs⟩
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    show φ ⟨c (c t), hmem (c t)⟩ = φ ⟨c t, hs⟩
    congr 2
    exact hcc t

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
/-! ## Invariance under relabelling -/
omit [DecidableEq α] [DecidableEq β] in
lemma sym2_map_inj (φ : β → α) (S : Set β) (hφ : Set.InjOn φ S) (p q : Sym2 β)
    (hp : ∀ a ∈ p, a ∈ S) (hq : ∀ a ∈ q, a ∈ S) (h : Sym2.map φ p = Sym2.map φ q) : p = q := by
  induction p using Sym2.inductionOn with
  | hf a b =>
    induction q using Sym2.inductionOn with
    | hf a' b' =>
      have ha := hp a (Sym2.mem_mk_left _ _)
      have hb := hp b (Sym2.mem_mk_right _ _)
      have ha' := hq a' (Sym2.mem_mk_left _ _)
      have hb' := hq b' (Sym2.mem_mk_right _ _)
      rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at h
      rw [Sym2.eq_iff]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hφ ha ha' h1, hφ hb hb' h2⟩
      · exact Or.inr ⟨hφ ha hb' h1, hφ hb ha' h2⟩

omit [DecidableEq β] in
lemma pmat_image (E : Finset (Sym2 β)) (φ : β → α) (S : Set β) (hφ : Set.InjOn φ S)
    (hE : ∀ p ∈ E, ∀ a ∈ p, a ∈ S) : PMat (E.image (Sym2.map φ)) ↔ PMat E := by
  unfold PMat
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine and_congr (forall₂_congr fun p hp => ?_)
    (forall₂_congr fun p hp => forall₂_congr fun q hq => ?_)
  · have := hE p hp
    induction p using Sym2.inductionOn with
    | hf a b =>
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff, Sym2.mk_isDiag_iff,
        hφ.eq_iff (this a (Sym2.mem_mk_left _ _)) (this b (Sym2.mem_mk_right _ _))]
  · constructor
    · intro H y hy hy'
      exact sym2_map_inj φ S hφ p q (hE p hp) (hE q hq)
        (H (φ y) (Sym2.mem_map.2 ⟨y, hy, rfl⟩) (Sym2.mem_map.2 ⟨y, hy', rfl⟩))
    · intro H x hx hx'
      obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.1 hx
      obtain ⟨y', hy', e⟩ := Sym2.mem_map.1 hx'
      have : y' = y := hφ (hE q hq y' hy') (hE p hp y hy) e
      subst this
      rw [H _ hy hy']

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {r : ℕ} (u : List (Lt 0 r))
lemma Ls_range (c : Fin (u.length + 1) → β) (i : Fin r) (a : β) (ha : a ∈ Ls u c i) :
    a ∈ Set.range c := by
  obtain ⟨t, -, rfl⟩ := mem_image.1 ha
  exact ⟨_, rfl⟩

lemma Ps_range (c : Fin (u.length + 1) → β) (i : Fin r) (p : Sym2 β) (hp : p ∈ Ps u c i) :
    ∀ a ∈ p, a ∈ Set.range c := by
  obtain ⟨t, -, rfl⟩ := mem_image.1 hp
  intro a ha
  rcases Sym2.mem_iff.1 ha with rfl | rfl <;> exact ⟨_, rfl⟩

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {r : ℕ} (u : List (Lt 0 r))
variable (c : Fin (u.length + 1) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ
lemma Ls_comp (i : Fin r) : Ls u (φ ∘ c) i = (Ls u c i).image φ := by
  have hf : (univ.filter fun t : Fin u.length =>
      u.get t = Sum.inr i ∧ (φ ∘ c) t.castSucc = (φ ∘ c) t.succ) =
      univ.filter fun t => u.get t = Sum.inr i ∧ c t.castSucc = c t.succ :=
    filter_congr fun t _ => and_congr Iff.rfl (hφ.eq_iff ⟨_, rfl⟩ ⟨_, rfl⟩)
  unfold Ls
  rw [hf, image_image]
  rfl

lemma Ps_comp (i : Fin r) : Ps u (φ ∘ c) i = (Ps u c i).image (Sym2.map φ) := by
  have hf : (univ.filter fun t : Fin u.length =>
      u.get t = Sum.inr i ∧ (φ ∘ c) t.castSucc ≠ (φ ∘ c) t.succ) =
      univ.filter fun t => u.get t = Sum.inr i ∧ c t.castSucc ≠ c t.succ :=
    filter_congr fun t _ => and_congr Iff.rfl (not_congr (hφ.eq_iff ⟨_, rfl⟩ ⟨_, rfl⟩))
  unfold Ps
  rw [hf, image_image]
  rfl

lemma card_Ls_comp (i : Fin r) : (Ls u (φ ∘ c) i).card = (Ls u c i).card := by
  rw [Ls_comp u c φ hφ]
  exact card_image_of_injOn fun a ha b hb hab =>
    hφ (Ls_range u c i a ha) (Ls_range u c i b hb) hab

lemma card_Ps_comp (i : Fin r) : (Ps u (φ ∘ c) i).card = (Ps u c i).card := by
  rw [Ps_comp u c φ hφ]
  exact card_image_of_injOn fun p hp q hq hpq =>
    sym2_map_inj φ _ hφ p q (Ps_range u c i p hp) (Ps_range u c i q hq) hpq

lemma good_comp : GoodL u (φ ∘ c) ↔ GoodL u c := by
  unfold GoodL
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) ?_)
  · rw [Ps_comp u c φ hφ]
    exact pmat_image _ φ _ hφ (Ps_range u c i)
  · rw [Ls_comp u c φ hφ, Ps_comp u c φ hφ]
    constructor
    · intro H a ha p hp hmem
      exact H (φ a) (mem_image_of_mem _ ha) (Sym2.map φ p) (mem_image_of_mem _ hp)
        (Sym2.mem_map.2 ⟨a, hmem, rfl⟩)
    · intro H a' ha' p' hp' hmem
      obtain ⟨a, ha, rfl⟩ := mem_image.1 ha'
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hp'
      obtain ⟨b, hb, e⟩ := Sym2.mem_map.1 hmem
      have : b = a := hφ (Ps_range u c i p hp b hb) (Ls_range u c i a ha) e
      exact H a ha p hp (this ▸ hb)
  · exact hφ.eq_iff ⟨_, rfl⟩ ⟨_, rfl⟩

lemma W_comp (N : ℕ) (κ : Fin r → ℕ) : W u N κ (φ ∘ c) = W u N κ c := by
  unfold W
  simp only [good_comp u c φ hφ, card_Ls_comp u c φ hφ, card_Ps_comp u c φ hφ]

end RandomInvolutions.Dev.PartC2
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

theorem wprod_singleton (a : Lt r s) : wprod [a] = genL a := by simp

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

theorem nf_wprod' (u : List (Lt r s)) (hu : Red u) : nf (wprod u) = u :=
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

theorem nf_injective : Function.Injective (nf : G r s → List (Lt r s)) := by
  intro g h e
  rw [← wprod_nf g, e, wprod_nf]

theorem nf_eq_nil_iff' (g : G r s) : nf g = [] ↔ g = 1 :=
  ⟨fun h => nf_injective (h.trans nf_one.symm), fun h => h ▸ nf_one⟩

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

theorem len_wprod_of_red {u : List (Lt r s)} (hu : Red u) : len (wprod u) = u.length := by
  rw [len_eq_length_nf, nf_wprod' u hu]

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## Aliases -/

theorem nf_eq_nil_iff {g : G r s} : nf g = [] ↔ g = 1 := nf_eq_nil_iff' g

/-! ## Generic group identities

(`simp`, `rw` and `group` do not see through the instance path of `G r s`, so identities are
proved in a generic group and applied with `exact`.) -/

theorem red_left {u v : List (Lt r s)} (h : Red (u ++ v)) : Red u := List.IsChain.left_of_append h

/-! ## The inverse word -/
/-- The inverse word: reversed, with `bar` applied. -/
def ibar (u : List (Lt r s)) : List (Lt r s) := (u.map bar).reverse

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}

theorem getElem_congr_idx (u : List (Lt r s)) {i j : ℕ} (hi : i < u.length) (hj : j < u.length)
    (h : i = j) : u[i] = u[j] := by subst h; rfl

/-- A reduced nonempty word whose first letter is not the inverse of its last letter is
cyclically reduced. -/
theorem cycRed_of_red (u : List (Lt r s)) (hu : Red u) (hne : u ≠ [])
    (h : u.head hne ≠ bar (u.getLast hne)) : CycRed u := by
  intro t
  have hpos : 0 < u.length := List.length_pos_iff.2 hne
  simp only [List.get_eq_getElem]
  by_cases ht : t.val + 1 < u.length
  · have := (List.isChain_iff_getElem.1 hu) t.val ht
    rw [getElem_congr_idx u (Nat.mod_lt _ hpos) ht (Nat.mod_eq_of_lt ht)]
    exact this
  · have ht' : t.val = u.length - 1 := by have := t.2; omega
    have h0 : (t.val + 1) % u.length = 0 := by
      rw [ht', Nat.sub_add_cancel hpos, Nat.mod_self]
    rw [getElem_congr_idx u (Nat.mod_lt _ hpos) hpos h0,
      getElem_congr_idx u t.2 (by omega) ht']
    rw [List.head_eq_getElem, List.getLast_eq_getElem] at h
    exact h

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
@[simp] theorem ibar_nil : ibar ([] : List (Lt r s)) = [] := rfl

theorem ibar_cons (a : Lt r s) (u : List (Lt r s)) : ibar (a :: u) = ibar u ++ [bar a] := by
  simp [ibar]

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-- A nonempty reduced word is `P ++ u ++ P⁻¹` with `u` cyclically reduced or one letter `m_j`. -/
theorem core_decomp : ∀ (n : ℕ) (w : List (Lt r s)), w.length = n → Red w → w ≠ [] →
    ∃ P u : List (Lt r s), u ≠ [] ∧ w = P ++ u ++ ibar P ∧
      (CycRed u ∨ ∃ j : Fin s, u = [Sum.inr j]) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn hred hne
    by_cases hc : w.head hne ≠ bar (w.getLast hne)
    · exact ⟨[], w, hne, by simp, Or.inl (cycRed_of_red w hred hne hc)⟩
    · rw [not_not] at hc
      obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
      rcases List.eq_nil_or_concat' t with rfl | ⟨m, c, rfl⟩
      · rcases a with ⟨i, b⟩ | j
        · simp [bar] at hc
        · exact ⟨[], [Sum.inr j], by simp, by simp, Or.inr ⟨j, rfl⟩⟩
      · have hac : a = bar c := by simpa using hc
        subst hac
        have hmne : m ≠ [] := by
          rintro rfl
          have := (red_cons_cons.1 hred).1
          exact this (bar_bar c).symm
        have hredm : Red m := hred.infix ⟨[bar c], [c], by simp⟩
        obtain ⟨P, u, hu, hm, hcu⟩ :=
          ih m.length (by simp at hn; omega) m rfl hredm hmne
        refine ⟨bar c :: P, u, hu, ?_, hcu⟩
        rw [ibar_cons, bar_bar]
        conv_lhs => rw [hm]
        simp

/-! ## Conjugates of the involutions -/

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
@[simp] theorem length_ibar (u : List (Lt r s)) : (ibar u).length = u.length := by simp [ibar]

theorem wprod_ibar (u : List (Lt r s)) : wprod (ibar u) = (wprod u)⁻¹ := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [ibar_cons, wprod_append, ih, wprod_cons a u, wprod_singleton, genL_bar]
    exact (mul_inv_rev (G := G r s) _ _).symm

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
theorem act_genL {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (a : Lt 0 r) :
    homI τ (genL a) = letterPermI τ a := by
  rcases a with ⟨i, b⟩ | j
  · exact i.elim0
  · simp only [homI, genL, letterPermI, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    show (τ j).1 ^ (1 : ZMod 2).val = _
    simp [ZMod.val_one]

theorem act_wprod {N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (u : List (Lt 0 r)) :
    homI τ (wprod u) = wordPermI τ u := by
  induction u with
  | nil => simp [wordPermI]
  | cons a t ih =>
    rw [wprod_cons, map_mul, ih, act_genL]
    simp [wordPermI]

end RandomInvolutions.Dev.PartF
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias act_wprod := RandomInvolutions.Dev.PartF.act_wprod

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-- Every nontrivial element is a reduced conjugate of a cyclically reduced word or of a letter
`m_i`. -/
theorem exists_cyc_rep (g : G 0 r) (hg : g ≠ 1) :
    ∃ (a : G 0 r) (u : List (Lt 0 r)), u ≠ [] ∧ g = a * wprod u * a⁻¹ ∧
      len g = 2 * len a + u.length ∧ (CycRed u ∨ ∃ i : Fin r, u = [Sum.inr i]) := by
  have hne : nf g ≠ [] := fun h => hg (nf_eq_nil_iff.1 h)
  obtain ⟨P, u, hu, hw, hcu⟩ := core_decomp _ (nf g) rfl (red_nf g) hne
  have hP : Red P := by
    have := red_nf g
    rw [hw] at this
    exact red_left (red_left this)
  refine ⟨wprod P, u, hu, ?_, ?_, hcu⟩
  · have h1 : wprod (P ++ u ++ ibar P) = g := by rw [← hw, wprod_nf]
    rw [← h1, wprod_append, wprod_append, wprod_ibar]
  · rw [len_eq_length_nf g, hw, len_wprod_of_red hP]
    simp
    omega

end RandomInvolutions.Dev.PartF
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias exists_cyc_rep := RandomInvolutions.Dev.PartF.exists_cyc_rep

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartK2
variable {r : ℕ}
lemma homK_mI {N : ℕ} {κ : Fin r → ℕ} (τ : OmK r N κ) (i : Fin r) :
    homK τ (mI i) = (τ i).1.1 := by
  have h := act_wprod (fun i => (τ i).1) [Sum.inr i]
  rw [wprod_single] at h
  simpa [homK, wordPermI, letterPermI] using h

lemma expFixK_torsion {N : ℕ} {κ : Fin r → ℕ} (hA : AdmK N κ) (a : G 0 r) (i : Fin r) :
    expFixK r N κ (a * mI i * a⁻¹) = κ i := by
  rw [expFixK_conj]
  unfold expFixK expFixOn
  have := nonempty_omK N κ hA
  have h : ∀ τ : OmK r N κ, (fixCount (homK τ (mI i)) : ℝ) = κ i := fun τ => by
    rw [homK_mI, (τ i).2]
  simp only [h, sum_const, card_univ, nsmul_eq_mul]
  have h0 : (Fintype.card (OmK r N κ) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma fixCount_le {N : ℕ} (p : Equiv.Perm (Fin N)) : fixCount p ≤ N := by
  unfold fixCount
  exact (card_filter_le _ _).trans_eq (by simp)

lemma expFixK_le_N (N : ℕ) (κ : Fin r → ℕ) (g : G 0 r) : expFixK r N κ g ≤ N := by
  unfold expFixK expFixOn
  rcases Nat.eq_zero_or_pos (Fintype.card (OmK r N κ)) with h | h
  · simp [h]
  · rw [div_le_iff₀ (by exact_mod_cast h)]
    calc ∑ τ : OmK r N κ, (fixCount (homK τ g) : ℝ) ≤ ∑ _τ : OmK r N κ, (N : ℝ) :=
          sum_le_sum fun τ _ => by exact_mod_cast fixCount_le _
      _ = _ := by simp [mul_comm]

/-! ## The model at `κ = 0` is the matching model -/

/-! ## The limit of the sum over colourings -/

end RandomInvolutions.Dev.PartK2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
/-! ## The counting formula -/
theorem expect_formula_aux {r : ℕ} (u : List (Lt 0 r)) (N : ℕ) (κ : Fin r → ℕ)
    (hA : AdmK N κ) :
    expFixK r N κ (wprod u) =
      ∑ c ∈ (univ.filter fun c : Fin (u.length + 1) → Fin (u.length + 1) =>
        canon c = c).filter (GoodL u), wtK u N κ c := by
  have h1 : (∑ ω : OmK r N κ, (fixCount (wordPermI (fun i => (ω i).1) u) : ℝ)) =
      ∑ c ∈ (univ.filter fun c : Fin (u.length + 1) → Fin (u.length + 1) => canon c = c),
        (N.descFactorial (nv c) : ℝ) * W u N κ c := by
    rw [sum_fixCount, ← sum_fiberwise_of_maps_to (s := univ)
      (t := univ.filter fun c : Fin (u.length + 1) → Fin (u.length + 1) => canon c = c)
      (g := canon) (fun x _ => mem_filter.2 ⟨mem_univ _, canon_canon x⟩)]
    refine sum_congr rfl fun c hc => ?_
    have hc := (mem_filter.1 hc).2
    have hG : ∀ x ∈ univ.filter fun x : Fin (u.length + 1) → Fin N => canon x = c,
        W u N κ x = W u N κ c := by
      intro x hx
      have hx := (mem_filter.1 hx).2
      rw [← hx]
      conv_lhs => rw [← comp_canon x]
      exact W_comp u (canon x) x (injOn_canon x) N κ
    rw [sum_congr rfl hG, sum_const, card_fiber c hc, Fintype.card_fin, nsmul_eq_mul]
  have hI : (∏ i, (Fintype.card (InvK N (κ i)) : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ => card_invK_ne_zero N (κ i) (hA i).1 (hA i).2
  have hcard : (Fintype.card (OmK r N κ) : ℝ) = ∏ i, (Fintype.card (InvK N (κ i)) : ℝ) := by
    rw [Fintype.card_pi, Nat.cast_prod]
  have h2 : ∀ ω : OmK r N κ, homK ω (wprod u) = wordPermI (fun i => (ω i).1) u :=
    fun ω => RandomInvolutions.Dev.act_wprod _ u
  unfold expFixK expFixOn
  simp only [h2]
  rw [h1, sum_filter (GoodL u), sum_div, hcard]
  refine sum_congr rfl fun c _ => ?_
  by_cases hg : GoodL u c
  · rw [if_pos hg]
    unfold W wtK wtF
    rw [if_pos hg, prod_mul_distrib]
    unfold Wf eK fK
    set A := (N.descFactorial (nv c) : ℝ)
    set P := ∏ i, (Fintype.card (InvK N (κ i)) : ℝ)
    field_simp
  · rw [if_neg hg]
    unfold W
    rw [if_neg hg]
    simp

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {r : ℕ}
/-- `E_{N,κ}[fix(wprod u)] = ∑_c wt(c)` over canonical good colourings with loops. -/
theorem expect_formulaK (u : List (Lt 0 r)) (N : ℕ) (κ : Fin r → ℕ) (hN : 1 ≤ N)
    (hA : AdmK N κ) (hL : u.length ≤ N) :
    expFixK r N κ (wprod u) = ∑ c ∈ CGL u, wtK u N κ c := by
  have _ := hN
  have _ := hL
  rw [expect_formula_aux u N κ hA]
  refine sum_congr ?_ fun _ _ => rfl
  ext c
  simp only [CGL, mem_filter]

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias expect_formulaK := RandomInvolutions.Dev.PartC2.expect_formulaK

end RandomInvolutions.Dev
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
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
open AccessibleMaps
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-!
# Part O, general lemmas: `AccessibleMaps.tensorOp`, `DerandSq.permOp`, `DerandSq.leftReg`,
the projection `Q` onto `1^⊥`, and `opOf` as an additive map (ported from bc214's Part O1).
-/
/-! ## `tensorOp` -/
theorem tensorOp_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) (a : Fin n) :
    (tensorOp A T x) a = ∑ b, A a b • T (x b) := by
  simp [tensorOp, inject, Pi.single_apply]

theorem op_ext {n : ℕ} (X Y : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))
    (h : ∀ x a, X x a = Y x a) : X = Y :=
  ContinuousLinearMap.ext fun x => PiLp.ext fun a => h x a

theorem tensorOp_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (S T : H →L[ℂ] H) :
    tensorOp A S * tensorOp B T = tensorOp (A * B) (S * T) := by
  refine op_ext _ _ fun x a => ?_
  simp only [mul_apply_eq_comp, tensorOp_apply, map_sum, map_smul,
    Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem tensorOp_add_left {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (A + B) T = tensorOp A T + tensorOp B T := by
  refine op_ext _ _ fun x a => ?_
  simp [tensorOp_apply, add_smul, Finset.sum_add_distrib]

theorem tensorOp_zero_left {n : ℕ} (T : H →L[ℂ] H) :
    tensorOp (0 : Matrix (Fin n) (Fin n) ℂ) T = 0 := by
  refine op_ext _ _ fun x a => ?_
  simp [tensorOp_apply]

theorem tensorOp_one_one {n : ℕ} :
    tensorOp (1 : Matrix (Fin n) (Fin n) ℂ) (1 : H →L[ℂ] H) = 1 := by
  refine op_ext _ _ fun x a => ?_
  simp [tensorOp_apply, Matrix.one_apply]

end RandomInvolutions.Dev.PartO
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
open AccessibleMaps
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
theorem star_tensorOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    star (tensorOp A T) = tensorOp A.conjTranspose (star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [tensorOp_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  simp [Matrix.conjTranspose_apply]

end RandomInvolutions.Dev.PartO
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
open AccessibleMaps
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
/-! ## Trace of a tensor operator -/
theorem trace_tensorOp_term {n : ℕ} (a b : Fin n) (T : H →L[ℂ] H) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin n => H))
      ((inject a ∘L T ∘L PiLp.proj 2 (fun _ : Fin n => H) b :
        PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) :
        PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H)) =
      if a = b then LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) else 0 := by
  set S : H →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H) :=
    ((inject a : H →L[ℂ] PiLp 2 (fun _ : Fin n => H)) : H →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H))
    with hS
  set F : PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] H :=
    ((T.comp (PiLp.proj 2 (fun _ : Fin n => H) b) : PiLp 2 (fun _ : Fin n => H) →L[ℂ] H) :
      PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] H) with hF
  have h1 : ((inject a ∘L T ∘L PiLp.proj 2 (fun _ : Fin n => H) b :
        PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) :
        PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H)) = S ∘ₗ F := by
    ext x : 1
    simp [hS, hF]
  rw [h1, LinearMap.trace_comp_comm' F S]
  by_cases hab : a = b
  · subst hab
    have : F ∘ₗ S = (T : H →ₗ[ℂ] H) := by
      ext y : 1
      simp [hS, hF, inject]
    rw [this, if_pos rfl]
  · have : F ∘ₗ S = 0 := by
      ext y : 1
      simp [hS, hF, inject, Ne.symm hab]
    rw [this, if_neg hab, map_zero]

theorem trace_tensorOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin n => H))
      ((tensorOp A T : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) :
        PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H)) =
      A.trace * LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) := by
  have hterm : ∀ i j : Fin n, (inject i ∘L (A i j • T) ∘L PiLp.proj 2 (fun _ : Fin n => H) j :
      PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) =
      A i j • (inject i ∘L T ∘L PiLp.proj 2 (fun _ : Fin n => H) j) := by
    intro i j
    ext x : 1
    simp
  unfold tensorOp
  simp only [hterm, ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul,
    map_sum, map_smul, trace_tensorOp_term, smul_eq_mul]
  simp [Matrix.trace, Finset.sum_mul, mul_ite, Finset.sum_ite_eq]

end RandomInvolutions.Dev.PartO
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
open AccessibleMaps
open DerandSq
/-! ## Permutation operators -/
theorem permOp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N))
    (j : Fin N) : permOp π x j = x (π.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

theorem permOp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOp (π * ρ) = permOp π * permOp ρ := by
  ext x j
  simp only [permOp_apply, mul_apply_eq_comp]
  rfl

theorem permOp_one {N : ℕ} : permOp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x j
  simp only [permOp_apply]
  rfl

theorem inner_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin N)) :
    inner ℂ (permOp π x) y = inner ℂ x (permOp π⁻¹ y) := by
  have : y = permOp π (permOp π⁻¹ y) := by
    rw [← mul_apply_eq_comp, ← permOp_mul, mul_inv_cancel, permOp_one]; rfl
  conv_lhs => rw [this]
  exact LinearIsometryEquiv.inner_map_map _ _ _

theorem star_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) : star (permOp π) = permOp π⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_permOp, inv_inv]

/-- A permutation representation as a monoid homomorphism into operators. -/
def permHom {M : Type*} [Monoid M] {N : ℕ} (π : M →* Equiv.Perm (Fin N)) :
    M →* (EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) where
  toFun g := permOp (π g)
  map_one' := by rw [map_one, permOp_one]
  map_mul' g h := by rw [map_mul, permOp_mul]

/-! ## The left regular representation -/

/-! ## The projection -/
/-- `1 - J` on `ℂ^N`. -/
def Qn (N : ℕ) : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - (N : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℂ)))

/-- `1 ⊗ (1 - J)` on `D` copies of `ℂ^N`. -/
def QQ (D N : ℕ) : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →L[ℂ]
    PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) :=
  tensorOp (1 : Matrix (Fin D) (Fin D) ℂ) (Qn N)

theorem Qn_apply {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    Qn N x i = x i - (N : ℂ)⁻¹ * ∑ j, x j := by
  show (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - (N : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℂ))) x).ofLp i = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib,
    Matrix.one_apply]

theorem Qn_mul_self (N : ℕ) : Qn N * Qn N = Qn N := by
  ext x i
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact i.elim0
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [mul_apply_eq_comp, Qn_apply, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem star_Qn (N : ℕ) : star (Qn N) = Qn N := by
  unfold Qn
  rw [← map_star]
  congr 1
  ext i j
  simp [Matrix.one_apply, eq_comm]

theorem Qn_permOp {N : ℕ} (σ : Equiv.Perm (Fin N)) : Qn N * permOp σ = permOp σ * Qn N := by
  ext x i
  simp only [mul_apply_eq_comp, Qn_apply, permOp_apply]
  congr 2
  exact Equiv.sum_comp σ.symm (fun j => x j)

theorem QQ_mul_self (D N : ℕ) : QQ D N * QQ D N = QQ D N := by
  unfold QQ
  rw [tensorOp_mul, Qn_mul_self, mul_one]

theorem star_QQ (D N : ℕ) : star (QQ D N) = QQ D N := by
  unfold QQ
  rw [star_tensorOp, star_Qn, Matrix.conjTranspose_one]

theorem QQ_tensorOp_permOp {D N : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin N)) :
    QQ D N * tensorOp A (permOp σ) = tensorOp A (permOp σ) * QQ D N := by
  unfold QQ
  rw [tensorOp_mul, tensorOp_mul, Qn_permOp, one_mul, mul_one]

/-- `Tr(P_σ (1 - J)) = fix σ - 1`. -/
theorem trace_permOp_Qn {N : ℕ} (hN : 1 ≤ N) (σ : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOp σ * Qn N :
      EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) = (fixCount σ : ℂ) - 1 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ (Fin N)), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, PiLp.basisFun_apply, PiLp.basisFun_repr,
    ContinuousLinearMap.coe_coe, mul_apply_eq_comp, permOp_apply, Qn_apply]
  rw [Finset.sum_sub_distrib, fixCount, Finset.card_filter, Nat.cast_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have : (σ.symm i = i) ↔ (σ i = i) := by
      rw [Equiv.symm_apply_eq, eq_comm]
    by_cases h : σ i = i
    · simp [h, this.mpr h]
    · simp [h, mt this.mp h]
  · simp [hN']

end RandomInvolutions.Dev.PartO
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
open AccessibleMaps
open DerandSq
variable {r s D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-! ## `opOf` -/
theorem opOf_eq_sum (π : G r s → H →L[ℂ] H) (x : MG D r s) :
    opOf π x = x.coeff.sum fun g A => tensorOp A (π g) := rfl

theorem opOf_zero (π : G r s → H →L[ℂ] H) : opOf π (0 : MG D r s) = 0 := by
  simp [opOf]

theorem opOf_add' (π : G r s → H →L[ℂ] H) (x y : MG D r s) :
    opOf π (x + y) = opOf π x + opOf π y := by
  rw [opOf_eq_sum, opOf_eq_sum, opOf_eq_sum, MonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun g => tensorOp_zero_left (π g))
    (fun g A B => tensorOp_add_left A B (π g))

theorem opOf_single (π : G r s → H →L[ℂ] H) (g : G r s) (A : Matrix (Fin D) (Fin D) ℂ) :
    opOf π (MonoidAlgebra.single g A) = tensorOp A (π g) := by
  rw [opOf_eq_sum, MonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (tensorOp_zero_left (π g))

/-- `opOf π` as an additive map. -/
def opHom (D : ℕ) (π : G r s → H →L[ℂ] H) : MG D r s →+
    (PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)) where
  toFun := opOf π
  map_zero' := opOf_zero π
  map_add' := opOf_add' π

theorem opHom_apply (π : G r s → H →L[ℂ] H) (x : MG D r s) : opHom D π x = opOf π x := rfl

theorem opOf_mul' (π : G r s →* (H →L[ℂ] H)) (x y : MG D r s) :
    opOf (fun g => π g) (x * y) = opOf (fun g => π g) x * opOf (fun g => π g) y := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, opOf_zero, zero_mul]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, opOf_add', opOf_add', h₁, h₂, add_mul]
  | single g A =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [mul_zero, opOf_zero, mul_zero]
    | add y₁ y₂ h₁ h₂ => rw [mul_add, opOf_add', opOf_add', h₁, h₂, mul_add]
    | single h B =>
      rw [MonoidAlgebra.single_mul_single, opOf_single, opOf_single, opOf_single, tensorOp_mul,
        map_mul]

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
set_option linter.unusedSectionVars false
open AccessibleMaps DerandSq
open scoped ComplexOrder
variable {r : ℕ}
variable {D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-!
# Part O: operators and the spectral functional (the Blueprint stubs)

Ported from bc214's Parts O1 and O2 to an arbitrary permutation representation
`π : G 0 r →* Perm (Fin N)` and an arbitrary finite sample space.
-/
/-! ## The four `opOf` stubs -/
theorem opOf_mul (π : G 0 r →* (H →L[ℂ] H)) (x y : MG D 0 r) :
    opOf (fun g => π g) (x * y) = opOf (fun g => π g) x * opOf (fun g => π g) y :=
  opOf_mul' π x y

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
variable {D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-! ## Part O: operators and the spectral functional -/
alias opOf_mul := RandomInvolutions.Dev.PartO.opOf_mul

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical InnerProductSpace
noncomputable section
namespace RandomInvolutions.Dev.PartL2
set_option linter.unusedSectionVars false
variable {r : ℕ} {D : ℕ}
lemma regOp_mul (x y : MG D 0 r) : regOp (x * y) = regOp x * regOp y :=
  RandomInvolutions.Dev.opOf_mul (lregHom (G 0 r)) x y

end RandomInvolutions.Dev.PartL2
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartT2
variable {r : ℕ}
variable {D : ℕ}
theorem regOp_mul (x y : MG D 0 r) : regOp (x * y) = regOp x * regOp y :=
  RandomInvolutions.Dev.opOf_mul (lregHom (G 0 r)) x y

end RandomInvolutions.Dev.PartT2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
open AccessibleMaps
open DerandSq
variable {r s D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem opOf_one' (π : G r s →* (H →L[ℂ] H)) :
    opOf (fun g => π g) (1 : MG D r s) = 1 := by
  rw [MonoidAlgebra.one_def, opOf_single, map_one]
  exact tensorOp_one_one

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
set_option linter.unusedSectionVars false
open AccessibleMaps DerandSq
open scoped ComplexOrder
variable {r : ℕ}
variable {D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem opOf_one (π : G 0 r →* (H →L[ℂ] H)) :
    opOf (fun g => π g) (1 : MG D 0 r) = 1 :=
  opOf_one' π

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
variable {D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
alias opOf_one := RandomInvolutions.Dev.PartO.opOf_one

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical InnerProductSpace
noncomputable section
namespace RandomInvolutions.Dev.PartL2
set_option linter.unusedSectionVars false
variable {r : ℕ} {D : ℕ}
lemma regOp_one : regOp (1 : MG D 0 r) = 1 := RandomInvolutions.Dev.opOf_one (lregHom (G 0 r))

lemma regOp_pow (x : MG D 0 r) (p : ℕ) : regOp (x ^ p) = regOp x ^ p := by
  induction p with
  | zero => rw [pow_zero, pow_zero, regOp_one]
  | succ k ih => rw [pow_succ, pow_succ, regOp_mul, ih]

end RandomInvolutions.Dev.PartL2
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
open AccessibleMaps
open DerandSq
variable {r s D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem opOf_adj' [CompleteSpace H] (π : G r s → H →L[ℂ] H) (hπ : ∀ g, star (π g) = π g⁻¹)
    (x : MG D r s) : star (opOf π x) = opOf π (adj x) := by
  have h1 : opOf π (adj x) = x.coeff.sum fun g A => opOf π (MonoidAlgebra.single g⁻¹ A.conjTranspose) := by
    rw [← opHom_apply, adj]
    exact map_finsuppSum (opHom D π) _ _
  have hsum := fun (S : Finset (G r s))
      (f : G r s → (PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H))) =>
    star_sum S f
  rw [h1, opOf_eq_sum, Finsupp.sum, Finsupp.sum, hsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [opOf_single, star_tensorOp, hπ]

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
set_option linter.unusedSectionVars false
open AccessibleMaps DerandSq
open scoped ComplexOrder
variable {r : ℕ}
variable {D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem opOf_adj (π : G 0 r → H →L[ℂ] H) (hπ : ∀ g, star (π g) = π g⁻¹) (x : MG D 0 r) :
    star (opOf π x) = opOf π (adj x) :=
  opOf_adj' π hπ x

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
variable {D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
alias opOf_adj := RandomInvolutions.Dev.PartO.opOf_adj

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
set_option linter.unusedSectionVars false
open AccessibleMaps DerandSq
open scoped ComplexOrder
variable {r : ℕ}
/-! ## The model operators -/
/-- Operators on `D` copies of `ℂ^N`. -/
abbrev Op (D N : ℕ) := PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →L[ℂ]
  PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))

/-- `x` in the permutation representation `π` (uncompressed). -/
def mOp {D N : ℕ} (π : G 0 r →* Equiv.Perm (Fin N)) (x : MG D 0 r) : Op D N :=
  opOf (fun g : G 0 r => permOp (π g)) x

theorem mOp_eq {D N : ℕ} (π : G 0 r →* Equiv.Perm (Fin N)) (x : MG D 0 r) :
    mOp π x = opOf (fun g => permHom π g) x := rfl

theorem perpOp_eq {D N : ℕ} (π : G 0 r →* Equiv.Perm (Fin N)) (x : MG D 0 r) :
    perpOp π x = QQ D N * (mOp π x * QQ D N) := rfl

theorem mOp_mul {D N : ℕ} (π : G 0 r →* Equiv.Perm (Fin N)) (x y : MG D 0 r) :
    mOp π (x * y) = mOp π x * mOp π y := by
  rw [mOp_eq, mOp_eq, mOp_eq, opOf_mul']

theorem star_mOp {D N : ℕ} (π : G 0 r →* Equiv.Perm (Fin N)) (x : MG D 0 r) :
    star (mOp π x) = mOp π (adj x) :=
  opOf_adj' _ (fun g => by
    show star (permOp (π g)) = permOp (π g⁻¹)
    rw [star_permOp, π.map_inv g]) x

theorem QQ_mOp {D N : ℕ} (π : G 0 r →* Equiv.Perm (Fin N)) (x : MG D 0 r) :
    QQ D N * mOp π x = mOp π x * QQ D N := by
  unfold mOp opOf
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun g _ => QQ_tensorOp_permOp _ _

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
set_option linter.unusedSectionVars false
open AccessibleMaps DerandSq
open scoped ComplexOrder
variable {r : ℕ}
/-- The compression is multiplicative on the model operators. -/
theorem perpOp_mul {D N : ℕ} (hN : 1 ≤ N) (π : G 0 r →* Equiv.Perm (Fin N)) (x y : MG D 0 r) :
    perpOp π (x * y) = perpOp π x * perpOp π y := by
  rw [perpOp_eq, perpOp_eq, perpOp_eq, mOp_mul]
  have hy := QQ_mOp π y
  symm
  calc QQ D N * (mOp π x * QQ D N) * (QQ D N * (mOp π y * QQ D N))
      = QQ D N * mOp π x * (QQ D N * QQ D N) * (mOp π y * QQ D N) := by
        simp only [mul_assoc]
    _ = QQ D N * mOp π x * (QQ D N * mOp π y) * QQ D N := by
        rw [QQ_mul_self]; simp only [mul_assoc]
    _ = QQ D N * mOp π x * (mOp π y * QQ D N) * QQ D N := by rw [hy]
    _ = QQ D N * (mOp π x * mOp π y * QQ D N) := by
        simp only [mul_assoc]; rw [QQ_mul_self]

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias perpOp_mul := RandomInvolutions.Dev.PartO.perpOp_mul

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
set_option linter.unusedSectionVars false
open AccessibleMaps DerandSq
open scoped ComplexOrder
variable {r : ℕ}
theorem star_perpOp {D N : ℕ} (π : G 0 r →* Equiv.Perm (Fin N)) (x : MG D 0 r) :
    star (perpOp π x) = perpOp π (adj x) := by
  rw [perpOp_eq, perpOp_eq, star_mul, star_mul, star_QQ, star_mOp, mul_assoc]

/-- The trace of the compressed model operator, in terms of fixed points. -/
theorem trace_perpOp {D N : ℕ} (hN : 1 ≤ N) (π : G 0 r →* Equiv.Perm (Fin N)) (y : MG D 0 r) :
    LinearMap.trace ℂ _ ((perpOp π y :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →L[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) =
      ∑ g ∈ y.coeff.support, Matrix.trace (y.coeff g) * ((fixCount (π g) : ℂ) - 1) := by
  have h1 : ((perpOp π y : Op D N) :
      PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) =
      ((QQ D N : Op D N) : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) *
        ((mOp π y * QQ D N : Op D N) : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) := rfl
  have h2 : ((mOp π y * QQ D N : Op D N) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) *
      ((QQ D N : Op D N) : PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) =
      ((mOp π y * QQ D N * QQ D N : Op D N) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) := rfl
  have h3 : (mOp π y * QQ D N * QQ D N : Op D N) =
      ∑ g ∈ y.coeff.support, tensorOp (y.coeff g) (permOp (π g) * Qn N) := by
    rw [mul_assoc, QQ_mul_self]
    unfold mOp opOf QQ
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [tensorOp_mul, mul_one]
  rw [h1, LinearMap.trace_mul_comm, h2, h3]
  simp only [ContinuousLinearMap.toLinearMap_sum, map_sum, trace_tensorOp, trace_permOp_Qn hN]

/-! ## The trace `τ` -/

/-! ## Word length of the support of a polynomial -/

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}

alias trace_perpOp := RandomInvolutions.Dev.PartO.trace_perpOp

alias star_perpOp := RandomInvolutions.Dev.PartO.star_perpOp

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical InnerProductSpace
noncomputable section
namespace RandomInvolutions.Dev.PartL2
set_option linter.unusedSectionVars false
variable {r : ℕ} {D : ℕ}
lemma regOp_adj (x : MG D 0 r) : regOp (adj x) = star (regOp x) :=
  (RandomInvolutions.Dev.opOf_adj (fun g : G 0 r => DerandSq.leftReg g) star_leftReg x).symm

/-- The moments are nonnegative. -/
theorem re_trTau_nonneg (x : MG D 0 r) (p : ℕ) : 0 ≤ (trTau ((adj x * x) ^ p)).re := by
  rw [trTau_eq_tauOp, regOp_pow, regOp_mul, regOp_adj]
  exact re_tauOp_nonneg _ (CStarAlgebra.pow_nonneg (star_mul_self_nonneg _) p)

/-! ## Probabilities -/
lemma uniformProb_union {Ω ι : Type*} [Fintype Ω] (S : Finset ι) (A : ι → Ω → Prop) :
    StrongConv.uniformProb (fun ω => ∃ i ∈ S, A i ω) ≤
      ∑ i ∈ S, StrongConv.uniformProb (A i) := by
  unfold StrongConv.uniformProb
  rw [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have h : (Finset.univ.filter fun ω => ∃ i ∈ S, A i ω) ⊆
      S.biUnion fun i => Finset.univ.filter (A i) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hω ⊢
    exact hω
  have h2 := (Finset.card_le_card h).trans Finset.card_biUnion_le
  have h3 := (Nat.cast_le (α := ℝ)).mpr h2
  push_cast at h3
  convert h3
  rfl

/-- Markov's inequality for the number of fixed points. -/
lemma markov {N : ℕ} {Ω : Type*} [Fintype Ω] (act : Ω → G 0 r →* Equiv.Perm (Fin N))
    (g : G 0 r) (t : ℝ) (ht : 0 < t) :
    StrongConv.uniformProb (fun ω : Ω => t < (fixCount (act ω g) : ℝ)) ≤
      expFixOn act g / t := by
  unfold StrongConv.uniformProb expFixOn
  rw [div_right_comm]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [Finset.sum_div]
  have hcard : ((Finset.univ.filter fun ω : Ω => t < (fixCount (act ω g) : ℝ)).card : ℝ) =
      ∑ ω : Ω, if t < (fixCount (act ω g) : ℝ) then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
  rw [hcard]
  refine Finset.sum_le_sum fun ω _ => ?_
  split_ifs with h
  · exact (one_le_div ht).mpr h.le
  · positivity

/-! ## The deterministic inequality -/
lemma trR_pow_le_gen {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (Y : V →L[ℂ] V) (p : ℕ) (hp : 1 ≤ p) :
    (LinearMap.trace ℂ V ((star Y * Y) ^ p).toLinearMap).re ≤
      (Module.finrank ℂ V : ℝ) * ‖Y‖ ^ (2 * p) := by
  set T := star Y * Y with hTdef
  have hT : 0 ≤ T := star_mul_self_nonneg Y
  have hsa : IsSelfAdjoint (T ^ p) := (hT.isSelfAdjoint).pow p
  have h1 : T ^ p ≤ algebraMap ℝ _ ‖T ^ p‖ := hsa.le_algebraMap_norm_self
  have hpos : 0 ≤ algebraMap ℝ (V →L[ℂ] V) ‖T ^ p‖ - T ^ p := sub_nonneg.mpr h1
  have hp' : ((algebraMap ℝ (V →L[ℂ] V) ‖T ^ p‖ - T ^ p : V →L[ℂ] V) : V →ₗ[ℂ] V).IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff _).mpr
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hpos)
  have h2 := (Complex.nonneg_iff.mp hp'.trace_nonneg).1
  have h3 : ((algebraMap ℝ (V →L[ℂ] V) ‖T ^ p‖ - T ^ p : V →L[ℂ] V) : V →ₗ[ℂ] V) =
      ((‖T ^ p‖ : ℝ) : ℂ) • (1 : V →ₗ[ℂ] V) - ((T ^ p : V →L[ℂ] V) : V →ₗ[ℂ] V) := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
    rfl
  rw [h3, map_sub, map_smul, LinearMap.trace_one, Complex.sub_re, smul_eq_mul,
    Complex.re_ofReal_mul, Complex.natCast_re] at h2
  have hTn : ‖T‖ = ‖Y‖ * ‖Y‖ := CStarRing.norm_star_mul_self
  have h4 : ‖T ^ p‖ ≤ ‖Y‖ ^ (2 * p) := by
    calc ‖T ^ p‖ ≤ ‖T‖ ^ p := norm_pow_le' T (by omega)
      _ = ‖Y‖ ^ (2 * p) := by rw [hTn, pow_mul, sq]
  have h5 : ‖T ^ p‖ * (Module.finrank ℂ V : ℝ) ≤ ‖Y‖ ^ (2 * p) * (Module.finrank ℂ V : ℝ) :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  linarith

lemma finrank_space (D N : ℕ) :
    Module.finrank ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) = D * N := by
  rw [(WithLp.linearEquiv 2 ℂ (Fin D → EuclideanSpace ℂ (Fin N))).finrank_eq,
    Module.finrank_pi_fintype]
  simp

lemma perpOp_pow {N : ℕ} (hN : 1 ≤ N) (π : G 0 r →* Equiv.Perm (Fin N)) (z : MG D 0 r)
    (k : ℕ) (hk : 1 ≤ k) : perpOp π (z ^ k) = perpOp π z ^ k := by
  induction k, hk using Nat.le_induction with
  | base => rw [pow_one, pow_one]
  | succ k _ ih => rw [pow_succ, pow_succ, RandomInvolutions.Dev.perpOp_mul hN, ih]

lemma key_ineq {N : ℕ} (hN : 1 ≤ N) (π : G 0 r →* Equiv.Perm (Fin N)) (x : MG D 0 r) (p : ℕ)
    (hp : 1 ≤ p) :
    ∑ g ∈ ((adj x * x) ^ p).coeff.support,
        (Matrix.trace (((adj x * x) ^ p).coeff g)).re * ((fixCount (π g) : ℝ) - 1) ≤
      (D : ℝ) * N * ‖perpOp π x‖ ^ (2 * p) := by
  have h := RandomInvolutions.Dev.trace_perpOp hN π ((adj x * x) ^ p)
  have hre : ∑ g ∈ ((adj x * x) ^ p).coeff.support,
        (Matrix.trace (((adj x * x) ^ p).coeff g)).re * ((fixCount (π g) : ℝ) - 1) =
      (∑ g ∈ ((adj x * x) ^ p).coeff.support,
        Matrix.trace (((adj x * x) ^ p).coeff g) * ((fixCount (π g) : ℂ) - 1)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : ((fixCount (π g) : ℂ) - 1) = (((fixCount (π g) : ℝ) - 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.re_mul_ofReal]
  rw [hre, ← h, perpOp_pow hN π _ p hp, RandomInvolutions.Dev.perpOp_mul hN, ← RandomInvolutions.Dev.star_perpOp]
  have h2 := trR_pow_le_gen (perpOp π x) p hp
  rw [finrank_space, Nat.cast_mul] at h2
  exact h2

lemma det_bound {N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) (π : G 0 r →* Equiv.Perm (Fin N))
    (x : MG D 0 r) (p : ℕ) (hp : 1 ≤ p) (b η : ℝ) (hη : 0 ≤ η)
    (hY : ‖perpOp π x‖ ^ (2 * p) ≤ b)
    (hgood : ∀ g ∈ ((adj x * x) ^ p).coeff.support.erase 1,
      (fixCount (π g) : ℝ) ≤ η * N) :
    (D : ℝ) * N * ((trTau ((adj x * x) ^ p)).re - b) ≤
      D * (trTau ((adj x * x) ^ p)).re +
        (∑ g ∈ ((adj x * x) ^ p).coeff.support.erase 1,
          |(Matrix.trace (((adj x * x) ^ p).coeff g)).re|) * (η * N + 1) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := key_ineq hN π x p hp
  have h1' : (D : ℝ) * N * ‖perpOp π x‖ ^ (2 * p) ≤ D * N * b :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  have ha : (trTau ((adj x * x) ^ p)).re =
      (Matrix.trace (((adj x * x) ^ p).coeff 1)).re / D := by
    unfold trTau
    have e : ((D : ℂ)⁻¹) = (((D : ℝ)⁻¹ : ℝ) : ℂ) := by simp
    rw [e, Complex.re_ofReal_mul]
    ring
  generalize (trTau ((adj x * x) ^ p)).re = a at ha ⊢
  generalize (adj x * x) ^ p = z at *
  set c : G 0 r → ℝ := fun g => (Matrix.trace (z.coeff g)).re with hc
  have h3 : c 1 = D * a := by
    rw [ha]; simp only [hc]; field_simp
  have hfix1 : (fixCount (π (1 : G 0 r)) : ℝ) = N := by simp [fixCount]
  have h2 : ∑ g ∈ z.coeff.support, c g * ((fixCount (π g) : ℝ) - 1) =
      c 1 * ((N : ℝ) - 1) + ∑ g ∈ z.coeff.support.erase 1,
        c g * ((fixCount (π g) : ℝ) - 1) := by
    by_cases h : (1 : G 0 r) ∈ z.coeff.support
    · rw [← Finset.add_sum_erase _ _ h, hfix1]
    · have h0 : c 1 = 0 := by
        simp only [hc]
        rw [Finsupp.notMem_support_iff.mp h]
        simp
      rw [Finset.erase_eq_of_notMem h, h0, zero_mul, zero_add]
  have h4 : -((∑ g ∈ z.coeff.support.erase 1, |c g|) * (η * N + 1)) ≤
      ∑ g ∈ z.coeff.support.erase 1, c g * ((fixCount (π g) : ℝ) - 1) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun g hg => ?_
    have hf := hgood g hg
    have hf0 : (0 : ℝ) ≤ (fixCount (π g) : ℝ) := by positivity
    have habs : |(fixCount (π g) : ℝ) - 1| ≤ η * N + 1 := by
      rw [abs_le]
      constructor
      · have : 0 ≤ η * N := by positivity
        linarith
      · linarith
    have := mul_le_mul_of_nonneg_left habs (abs_nonneg (c g))
    rw [← abs_mul] at this
    linarith [neg_abs_le (c g * ((fixCount (π g) : ℝ) - 1))]
  have h5 : (D : ℝ) * N * (a - b) = D * a * ((N : ℝ) - 1) - D * N * b + D * a := by ring
  rw [h3] at h2
  rw [h5]
  linarith

/-! ## The lower tail -/
lemma tendsto_sqrt_div (c : ℝ) :
    Tendsto (fun N : ℕ => c * (Real.sqrt N + 1) / (N : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h2 : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h3 := ((h1.add h2).const_mul c)
  simp only [add_zero, mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN'
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN'.le
  field_simp
  linear_combination (-c) * hsq

end RandomInvolutions.Dev.PartL2
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartT2
variable {r : ℕ}
variable {D : ℕ}
theorem regOp_adj (x : MG D 0 r) : regOp (adj x) = star (regOp x) :=
  (RandomInvolutions.Dev.opOf_adj (fun g : G 0 r => DerandSq.leftReg g) star_leftReg x).symm

theorem norm_star_mul_self_gen {A : Type*} [CStarAlgebra A] (y : A) :
    ‖star y * y‖ = ‖y‖ * ‖y‖ := CStarRing.norm_star_mul_self

theorem norm_regOp_sq (x : MG D 0 r) : ‖regOp (adj x * x)‖ = ‖regOp x‖ * ‖regOp x‖ := by
  have h := norm_star_mul_self_gen (regOp x)
  rw [regOp_mul, regOp_adj]
  exact h

theorem norm_perpOp_sq {N : ℕ} (hN : 1 ≤ N) (π : G 0 r →* Equiv.Perm (Fin N)) (x : MG D 0 r) :
    ‖perpOp π (adj x * x)‖ = ‖perpOp π x‖ * ‖perpOp π x‖ := by
  have h := norm_star_mul_self_gen (perpOp π x)
  rw [RandomInvolutions.Dev.perpOp_mul hN, ← RandomInvolutions.Dev.star_perpOp]
  exact h

end RandomInvolutions.Dev.PartT2
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartT2
variable {r : ℕ}
/-! ## Uniform probability -/
theorem uniformProb_le_add {Ω : Type*} [Fintype Ω] (A B C : Ω → Prop)
    (h : ∀ ω, A ω → B ω ∨ C ω) :
    StrongConv.uniformProb A ≤ StrongConv.uniformProb B + StrongConv.uniformProb C := by
  unfold StrongConv.uniformProb
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have h1 : (univ.filter A) ⊆ (univ.filter B) ∪ (univ.filter C) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and, mem_union] at hω ⊢
    exact h ω hω
  have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
  exact_mod_cast h2

end RandomInvolutions.Dev.PartT2
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

end RandomInvolutions.Dev.PartP3b.F1
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ} {α : Type*} [DecidableEq α]
/-! ## Walks -/
/-- The vertices visited at times `≤ k`. -/
def UU (x : ℕ → α) (k : ℕ) : Finset α := (range (k + 1)).image x

/-- The coloured pair of step `t`. -/
def pe (a : ℕ → Fin r) (x : ℕ → α) (t : ℕ) : Fin r × Sym2 α := (a t, s(x t, x (t + 1)))

/-- The coloured pairs of the non-loop steps `< k`. -/
def EE (a : ℕ → Fin r) (x : ℕ → α) (k : ℕ) : Finset (Fin r × Sym2 α) :=
  ((range k).filter fun t => x t ≠ x (t + 1)).image (pe a x)

/-- The coloured loops of the loop steps `< k`. -/
def LL (a : ℕ → Fin r) (x : ℕ → α) (k : ℕ) : Finset (Fin r × α) :=
  ((range k).filter fun t => x t = x (t + 1)).image fun t => (a t, x t)

/-- Step `k` is a closing step: a new pair to an old vertex. -/
def closing (a : ℕ → Fin r) (x : ℕ → α) (k : ℕ) : Prop :=
  x k ≠ x (k + 1) ∧ x (k + 1) ∈ UU x k ∧ pe a x k ∉ EE a x k

/-- `x t` was not visited before time `t`. -/
def newAt (x : ℕ → α) (t : ℕ) : Prop := ∀ s < t, x s ≠ x t

lemma mem_UU {x : ℕ → α} {k j : ℕ} (h : j ≤ k) : x j ∈ UU x k :=
  mem_image_of_mem _ (mem_range.2 (by omega))

lemma UU_succ (x : ℕ → α) (k : ℕ) : UU x (k + 1) = insert (x (k + 1)) (UU x k) := by
  simp [UU, range_add_one, image_insert]

lemma EE_succ (a : ℕ → Fin r) (x : ℕ → α) (k : ℕ) :
    EE a x (k + 1) = if x k = x (k + 1) then EE a x k else insert (pe a x k) (EE a x k) := by
  unfold EE
  rw [range_add_one, filter_insert]
  by_cases h : x k = x (k + 1)
  · rw [if_neg (not_not.2 h), if_pos h]
  · rw [if_pos h, if_neg h, image_insert]

omit [DecidableEq α] in
lemma pe_eq {a : ℕ → Fin r} {x : ℕ → α} {s t : ℕ} :
    pe a x s = pe a x t ↔ a s = a t ∧
      ((x s = x t ∧ x (s + 1) = x (t + 1)) ∨ (x s = x (t + 1) ∧ x (s + 1) = x t)) := by
  simp [pe]

lemma count (a : ℕ → Fin r) (x : ℕ → α) :
    ∀ k, (UU x k).card + ((range k).filter (closing a x)).card = (EE a x k).card + 1
  | 0 => by simp [UU, EE]
  | k + 1 => by
      have ih := count a x k
      have hk : k ∉ range k := by simp
      rw [UU_succ, EE_succ, range_add_one, filter_insert]
      by_cases hl : x k = x (k + 1)
      · have hx : x (k + 1) ∈ UU x k := hl ▸ mem_UU le_rfl
        have hc : ¬ closing a x k := fun h => h.1 hl
        rw [if_neg hc, insert_eq_of_mem hx, if_pos hl]; exact ih
      · rw [if_neg hl]
        by_cases hx : x (k + 1) ∈ UU x k
        · by_cases he : pe a x k ∈ EE a x k
          · have hc : ¬ closing a x k := fun h => h.2.2 he
            rw [if_neg hc, insert_eq_of_mem hx, insert_eq_of_mem he]; exact ih
          · have hc : closing a x k := ⟨hl, hx, he⟩
            rw [if_pos hc, insert_eq_of_mem hx, card_insert_of_notMem he,
              card_insert_of_notMem (fun h => hk (mem_filter.1 h).1)]
            omega
        · have he : pe a x k ∉ EE a x k := by
            intro h
            obtain ⟨s', hs, hse⟩ := mem_image.1 h
            have hs := mem_range.1 (mem_filter.1 hs).1
            rcases pe_eq.1 hse with ⟨-, ⟨-, h3⟩ | ⟨h3, -⟩⟩
            · exact hx (h3 ▸ mem_UU (by omega))
            · exact hx (h3 ▸ mem_UU (by omega))
          have hc : ¬ closing a x k := fun h => hx h.2.1
          rw [if_neg hc, card_insert_of_notMem hx, card_insert_of_notMem he]
          omega

/-- The pair graph is connected. -/
theorem card_UU_le (a : ℕ → Fin r) (x : ℕ → α) (k : ℕ) : (UU x k).card ≤ (EE a x k).card + 1 := by
  have := count a x k
  omega

/-! ### Periodicity -/
omit [DecidableEq α] in
lemma per_mul {β : Type*} {x : ℕ → β} {L : ℕ} (h : ∀ t, x (t + L) = x t) (t q : ℕ) :
    x (t + q * L) = x t := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, ← add_assoc, h, ih]

omit [DecidableEq α] in
lemma per_mod {β : Type*} {x : ℕ → β} {L : ℕ} (h : ∀ t, x (t + L) = x t) (t : ℕ) :
    x t = x (t % L) := by
  have := per_mul h (t % L) (t / L)
  rw [Nat.mod_add_div'] at this
  exact this

omit [DecidableEq α] in
lemma per_mod_succ {β : Type*} {x : ℕ → β} {L : ℕ} (h : ∀ t, x (t + L) = x t) (t : ℕ) :
    x (t + 1) = x (t % L + 1) := by
  have := per_mul h (t % L + 1) (t / L)
  rw [show t % L + 1 + t / L * L = t % L + t / L * L + 1 by omega, Nat.mod_add_div'] at this
  exact this

/-- A periodic, cyclically reduced walk without closing steps (from any origin): its pair graph
is a tree. -/
structure TW (L : ℕ) (a : ℕ → Fin r) (x : ℕ → α) : Prop where
  hL : 0 < L
  px : ∀ t, x (t + L) = x t
  pa : ∀ t, a (t + L) = a t
  hcr : ∀ t, a (t + 1) ≠ a t
  hnc : ∀ s k, ¬ closing (fun t => a (s + t)) (fun t => x (s + t)) k

/-- A periodic cyclically reduced walk with `v = e + 1` is a tree walk. -/
theorem TW.mk' {L : ℕ} {a : ℕ → Fin r} {x : ℕ → α} (hL : 0 < L) (px : ∀ t, x (t + L) = x t)
    (pa : ∀ t, a (t + L) = a t) (hcr : ∀ t, a (t + 1) ≠ a t)
    (hve : ((range L).image x).card = (EE a x L).card + 1) : TW L a x := by
  refine ⟨hL, px, pa, hcr, fun s k hcl => ?_⟩
  set K := k + 1 + L + s * L with hK
  have hc := count (fun t => a (s + t)) (fun t => x (s + t)) K
  have hU : UU (fun t => x (s + t)) K = (range L).image x := by
    ext y
    simp only [UU, mem_image, mem_range]
    constructor
    · rintro ⟨t, -, rfl⟩
      exact ⟨(s + t) % L, Nat.mod_lt _ hL, (per_mod px _).symm⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t + s * L - s, ?_, ?_⟩
      · have : s ≤ s * L := Nat.le_mul_of_pos_right s hL
        omega
      · have : s ≤ s * L := Nat.le_mul_of_pos_right s hL
        rw [show s + (t + s * L - s) = t + s * L by omega]
        exact per_mul px t s
  have hE : EE (fun t => a (s + t)) (fun t => x (s + t)) K = EE a x L := by
    ext e
    simp only [EE, mem_image, mem_filter, mem_range]
    constructor
    · rintro ⟨t, ⟨-, hne⟩, rfl⟩
      refine ⟨(s + t) % L, ⟨Nat.mod_lt _ hL, ?_⟩, ?_⟩
      · rw [← per_mod px, ← per_mod_succ px]; exact hne
      · simp only [pe]
        rw [← per_mod px, ← per_mod_succ px, ← per_mod pa]
        rfl
    · rintro ⟨t, ⟨ht, hne⟩, rfl⟩
      have hs : s ≤ s * L := Nat.le_mul_of_pos_right s hL
      have e1 : s + (t + s * L - s) = t + s * L := by omega
      have e2 : s + (t + s * L - s + 1) = t + 1 + s * L := by omega
      refine ⟨t + s * L - s, ⟨by omega, ?_⟩, ?_⟩
      · show x (s + (t + s * L - s)) ≠ x (s + (t + s * L - s + 1))
        rw [e1, e2, per_mul px, per_mul px]; exact hne
      · simp only [pe]
        rw [e1, e2, per_mul px, per_mul px, per_mul pa]
  rw [hU, hE, hve] at hc
  have h0 : ((range K).filter (closing (fun t => a (s + t)) (fun t => x (s + t)))).card = 0 := by
    omega
  rw [card_eq_zero, filter_eq_empty_iff] at h0
  exact h0 (mem_range.2 (by omega)) hcl

end RandomInvolutions.Dev.PartW
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ} {α : Type*} [DecidableEq α]
namespace TW
variable {L : ℕ} {a : ℕ → Fin r} {x : ℕ → α}
lemma shift (h : TW L a x) (s : ℕ) : TW L (fun t => a (s + t)) (fun t => x (s + t)) := by
  refine ⟨h.hL, fun t => ?_, fun t => ?_, fun t => ?_, fun s' k => ?_⟩
  · rw [← add_assoc]; exact h.px _
  · rw [← add_assoc]; exact h.pa _
  · exact h.hcr (s + t)
  · have e1 : (fun t => a (s + (s' + t))) = fun t => a (s + s' + t) := by
      funext t; rw [add_assoc]
    have e2 : (fun t => x (s + (s' + t))) = fun t => x (s + s' + t) := by
      funext t; rw [add_assoc]
    rw [e1, e2]
    exact h.hnc (s + s') k

lemma hnc0 (h : TW L a x) (k : ℕ) : ¬ closing a x k := by
  have := h.hnc 0 k
  simpa using this

/-- After a new vertex, a pair step leads to a new vertex. -/
lemma g1 (h : TW L a x) {t : ℕ} (hnew : newAt x t) (hl : x t ≠ x (t + 1)) : newAt x (t + 1) := by
  intro s hs heq
  have hin : x (t + 1) ∈ UU x t := heq ▸ mem_UU (by omega)
  have he : pe a x t ∈ EE a x t := by
    by_contra h'; exact h.hnc0 t ⟨hl, hin, h'⟩
  obtain ⟨s', hs', hse⟩ := mem_image.1 he
  rw [mem_filter, mem_range] at hs'
  rcases pe_eq.1 hse with ⟨h1, ⟨h2, -⟩ | ⟨h2, h3⟩⟩
  · exact hnew s' hs'.1 h2
  · by_cases h' : s' + 1 < t
    · exact hnew (s' + 1) h' h3
    · have : s' + 1 = t := by omega
      subst this
      exact h.hcr s' h1.symm

/-- From a new vertex, the walk visits new vertices up to the next loop step. -/
lemma g2 (h : TW L a x) {t0 T : ℕ} (hnew : newAt x t0) (hT : t0 ≤ T) (hTl : x T = x (T + 1)) :
    ∃ t', t0 ≤ t' ∧ t' ≤ T ∧ x t' = x (t' + 1) ∧ (∀ k, t0 ≤ k → k < t' → x k ≠ x (k + 1)) ∧
      ∀ k, t0 ≤ k → k ≤ t' → newAt x k := by
  have hex : ∃ t, t0 ≤ t ∧ x t = x (t + 1) := ⟨T, hT, hTl⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, Nat.find_min' hex ⟨hT, hTl⟩,
    (Nat.find_spec hex).2, fun k hk hk' hkl => Nat.find_min hex hk' ⟨hk, hkl⟩, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; exact hnew
  | succ k hk ih =>
    intro hk'
    exact h.g1 (ih (by omega)) (fun hkl => Nat.find_min hex (by omega) ⟨hk, hkl⟩)

lemma exists_loop (h : TW L a x) : ∃ T, x T = x (T + 1) := by
  by_contra hno
  push Not at hno
  have : ∀ k, newAt x k := by
    intro k
    induction k with
    | zero => intro s hs; omega
    | succ k ih => exact h.g1 ih (hno k)
  have h1 := this L 0 h.hL
  have h2 := h.px 0
  rw [zero_add] at h2
  exact h1 h2.symm

/-- The first loop step: the walk is injective up to it. -/
lemma first_loop (h : TW L a x) :
    ∃ D, x D = x (D + 1) ∧ (∀ k < D, x k ≠ x (k + 1)) ∧ ∀ k ≤ D, newAt x k := by
  obtain ⟨T, hT⟩ := h.exists_loop
  obtain ⟨t', -, -, h1, h2, h3⟩ := h.g2 (t0 := 0) (fun s hs => by omega) (Nat.zero_le T) hT
  exact ⟨t', h1, fun k hk => h2 k (Nat.zero_le _) hk, fun k hk => h3 k (Nat.zero_le _) hk⟩

/-- A tree walk has at least two loops. -/
theorem two_loops (h : TW L a x) (F : Finset (Fin r × α))
    (hF : ∀ t, x t = x (t + 1) → (a t, x t) ∈ F) : 2 ≤ F.card := by
  obtain ⟨D0, hD0, -, -⟩ := h.first_loop
  obtain ⟨D1, hD1, -, hn1⟩ := (h.shift (D0 + 1)).first_loop
  have m0 := hF D0 hD0
  have m1 := hF (D0 + 1 + D1) hD1
  have hne : (a D0, x D0) ≠ (a (D0 + 1 + D1), x (D0 + 1 + D1)) := by
    intro heq
    rw [Prod.mk.injEq] at heq
    rcases Nat.eq_zero_or_pos D1 with h0 | hpos
    · subst h0
      exact h.hcr D0 heq.1.symm
    · have := hn1 D1 le_rfl 0 hpos
      simp only [add_zero] at this
      exact this (hD0 ▸ heq.2)
  exact Finset.one_lt_card.2 ⟨_, m0, _, m1, hne⟩

end TW
end RandomInvolutions.Dev.PartW
end
end

section
open Finset
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ} {α : Type*} [DecidableEq α]

lemma mem_LL_of_loop {L : ℕ} {a : ℕ → Fin r} {x : ℕ → α} (hL : 0 < L)
    (px : ∀ t, x (t + L) = x t) (pa : ∀ t, a (t + L) = a t) {t : ℕ} (ht : x t = x (t + 1)) :
    (a t, x t) ∈ LL a x L := by
  refine mem_image.2 ⟨t % L, mem_filter.2 ⟨mem_range.2 (Nat.mod_lt _ hL), ?_⟩, ?_⟩
  · rw [← per_mod px, ← per_mod_succ px]; exact ht
  · rw [← per_mod px, ← per_mod pa]

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
/-! ## Letters of `Lt 0 r` -/
/-- The colour of a letter. -/
def colr : Lt 0 r → Fin r
  | Sum.inl p => p.1.elim0
  | Sum.inr j => j

lemma inr_colr (l : Lt 0 r) : Sum.inr (colr l) = l := by
  rcases l with ⟨i, _⟩ | j
  · exact i.elim0
  · rfl

lemma eq_inr_iff (l : Lt 0 r) (k : Fin r) : l = Sum.inr k ↔ colr l = k := by
  constructor
  · rintro rfl; rfl
  · rintro rfl; exact (inr_colr l).symm

lemma colr_inj {l l' : Lt 0 r} (h : colr l = colr l') : l = l' := by
  rw [← inr_colr l, ← inr_colr l', h]

lemma bar_eq (l : Lt 0 r) : bar l = l := by
  rcases l with ⟨i, _⟩ | j
  · exact i.elim0
  · rfl

/-! ## Periodic readings -/
/-- The colours of a nonempty word, read cyclically. -/
def ac (u : List (Lt 0 r)) (hne : u ≠ []) (t : ℕ) : Fin r :=
  colr (u.get ⟨t % u.length, Nat.mod_lt _ (List.length_pos_iff.2 hne)⟩)

/-- A colouring read cyclically. -/
def Xc {L : ℕ} {β : Type*} (c : Fin (L + 1) → β) (t : ℕ) : β := c ⟨min (t % L) L, by omega⟩

lemma ac_per (u : List (Lt 0 r)) (hne : u ≠ []) (t : ℕ) :
    ac u hne (t + u.length) = ac u hne t := by
  unfold ac; congr 2; exact Fin.ext (by simp)

lemma ac_get (u : List (Lt 0 r)) (hne : u ≠ []) (t : Fin u.length) :
    colr (u.get t) = ac u hne t.val := by
  unfold ac; congr 2; exact Fin.ext (by simp [Nat.mod_eq_of_lt t.2])

lemma ac_cr (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u) (t : ℕ) :
    ac u hne (t + 1) ≠ ac u hne t := by
  intro h
  have hL := List.length_pos_iff.2 hne
  refine hcr ⟨t % u.length, Nat.mod_lt _ hL⟩ ?_
  rw [bar_eq]
  apply colr_inj
  have e1 : colr (u.get ⟨(t % u.length + 1) % u.length, Nat.mod_lt _ hL⟩) = ac u hne (t + 1) := by
    unfold ac; congr 2; exact Fin.ext (by simp)
  exact e1.trans h

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
variable {L : ℕ} {β : Type*}
lemma Xc_per (c : Fin (L + 1) → β) (t : ℕ) : Xc c (t + L) = Xc c t := by
  unfold Xc; congr 1; exact Fin.ext (by simp)

lemma Xc_lt (c : Fin (L + 1) → β) {t : ℕ} (ht : t < L) : Xc c t = c ⟨t, by omega⟩ := by
  unfold Xc; congr 1; refine Fin.ext ?_
  simp only [Nat.mod_eq_of_lt ht]; omega

lemma Xc_L (c : Fin (L + 1) → β) : Xc c L = c 0 := by
  unfold Xc; congr 1; exact Fin.ext (by simp)

lemma Xc_cs (c : Fin (L + 1) → β) (t : Fin L) : c t.castSucc = Xc c t.val := by
  rw [Xc_lt c t.2]; rfl

lemma Xc_succ (c : Fin (L + 1) → β) (hcl : c 0 = c (Fin.last L)) (t : Fin L) :
    c t.succ = Xc c (t.val + 1) := by
  rcases Nat.lt_or_ge (t.val + 1) L with h | h
  · rw [Xc_lt c h]; rfl
  · have ht : t.val + 1 = L := by have := t.2; omega
    rw [ht, Xc_L, hcl]; congr 1; exact Fin.ext (by simp [ht])

lemma nv_eq [DecidableEq β] (hL : 0 < L) (c : Fin (L + 1) → β) (hcl : c 0 = c (Fin.last L)) :
    nv c = ((range L).image (Xc c)).card := by
  unfold nv
  congr 1
  ext y
  simp only [mem_image, mem_univ, true_and, mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    rcases Nat.lt_or_ge t.val L with h | h
    · exact ⟨t.val, h, Xc_lt c h⟩
    · refine ⟨0, hL, ?_⟩
      rw [Xc_lt c hL]
      have : t = Fin.last L := Fin.ext (by have := t.2; simp; omega)
      rw [this, ← hcl]; rfl
  · rintro ⟨t, -, rfl⟩; exact ⟨_, rfl⟩

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
variable {β : Type*} [DecidableEq β] (u : List (Lt 0 r)) (hne : u ≠ [])
  (c : Fin (u.length + 1) → β) (hcl : c 0 = c (Fin.last _))
/-! ## Pairs and loops of a colouring as pairs and loops of the walk -/
include hcl in
lemma mem_Ps (k : Fin r) (q : Sym2 β) :
    q ∈ Ps u c k ↔ ∃ t < u.length, ac u hne t = k ∧ Xc c t ≠ Xc c (t + 1) ∧
      q = s(Xc c t, Xc c (t + 1)) := by
  unfold Ps
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    refine ⟨t.val, t.2, ?_, ?_, ?_⟩
    · rw [← ac_get]; exact (eq_inr_iff _ _).1 h1
    · rw [← Xc_cs c t, ← Xc_succ c hcl t]; exact h2
    · rw [← Xc_cs c t, ← Xc_succ c hcl t]
  · rintro ⟨t, ht, h1, h2, rfl⟩
    refine ⟨⟨t, ht⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [eq_inr_iff, ac_get u hne ⟨t, ht⟩]; exact h1
    · rw [Xc_cs c ⟨t, ht⟩, Xc_succ c hcl ⟨t, ht⟩]; exact h2
    · rw [Xc_cs c ⟨t, ht⟩, Xc_succ c hcl ⟨t, ht⟩]

include hcl in
lemma mem_Ls (k : Fin r) (w : β) :
    w ∈ Ls u c k ↔ ∃ t < u.length, ac u hne t = k ∧ Xc c t = Xc c (t + 1) ∧ w = Xc c t := by
  unfold Ls
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    refine ⟨t.val, t.2, ?_, ?_, ?_⟩
    · rw [← ac_get]; exact (eq_inr_iff _ _).1 h1
    · rw [← Xc_cs c t, ← Xc_succ c hcl t]; exact h2
    · rw [← Xc_cs c t]
  · rintro ⟨t, ht, h1, h2, rfl⟩
    refine ⟨⟨t, ht⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [eq_inr_iff, ac_get u hne ⟨t, ht⟩]; exact h1
    · rw [Xc_cs c ⟨t, ht⟩, Xc_succ c hcl ⟨t, ht⟩]; exact h2
    · rw [Xc_cs c ⟨t, ht⟩]

include hcl in
lemma EE_fiber (k : Fin r) :
    (EE (ac u hne) (Xc c) u.length).filter (fun e => e.1 = k) =
      (Ps u c k).image (Prod.mk k) := by
  ext ⟨k', q⟩
  simp only [mem_filter, mem_image, EE, mem_range, pe, Prod.mk.injEq, mem_Ps u hne c hcl]
  constructor
  · rintro ⟨⟨t, ⟨ht, hne'⟩, h1, h2⟩, rfl⟩
    exact ⟨q, ⟨t, ht, h1, hne', h2.symm⟩, rfl, rfl⟩
  · rintro ⟨q', ⟨t, ht, h1, h2, rfl⟩, rfl, rfl⟩
    exact ⟨⟨t, ⟨ht, h2⟩, h1, rfl⟩, rfl⟩

include hcl in
lemma LL_fiber (k : Fin r) :
    (LL (ac u hne) (Xc c) u.length).filter (fun e => e.1 = k) =
      (Ls u c k).image (Prod.mk k) := by
  ext ⟨k', w⟩
  simp only [mem_filter, mem_image, LL, mem_range, Prod.mk.injEq, mem_Ls u hne c hcl]
  constructor
  · rintro ⟨⟨t, ⟨ht, hne'⟩, h1, h2⟩, rfl⟩
    exact ⟨w, ⟨t, ht, h1, hne', h2.symm⟩, rfl, rfl⟩
  · rintro ⟨w', ⟨t, ht, h1, h2, rfl⟩, rfl, rfl⟩
    exact ⟨⟨t, ⟨ht, h2⟩, h1, rfl⟩, rfl⟩

include hcl in
lemma card_Ps_eq (k : Fin r) :
    (Ps u c k).card = ((EE (ac u hne) (Xc c) u.length).filter (fun e => e.1 = k)).card := by
  rw [EE_fiber u hne c hcl, card_image_of_injective _ (Prod.mk_right_injective k)]

include hcl in
lemma card_Ls_eq (k : Fin r) :
    (Ls u c k).card = ((LL (ac u hne) (Xc c) u.length).filter (fun e => e.1 = k)).card := by
  rw [LL_fiber u hne c hcl, card_image_of_injective _ (Prod.mk_right_injective k)]

include hcl in
lemma sum_card_Ps : ∑ k, (Ps u c k).card = (EE (ac u hne) (Xc c) u.length).card := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
  exact sum_congr rfl fun k _ => card_Ps_eq u hne c hcl k

include hcl in
lemma sum_card_Ls : ∑ k, (Ls u c k).card = (LL (ac u hne) (Xc c) u.length).card := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
  exact sum_congr rfl fun k _ => card_Ls_eq u hne c hcl k

end RandomInvolutions.Dev.PartW
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
lemma mem_CGL {u : List (Lt 0 r)} {c : Fin (u.length + 1) → Fin (u.length + 1)} :
    c ∈ CGL u ↔ canon c = c ∧ GoodL u c := by
  unfold CGL
  simp only [mem_filter, mem_univ, true_and]

lemma Ecount_eq (u : List (Lt 0 r)) (hne : u ≠ [])
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hcl : c 0 = c (Fin.last _)) :
    Ecount u c = (EE (ac u hne) (Xc c) u.length).card := by
  rw [← sum_card_Ps u hne c hcl]; rfl

lemma Fcount_eq (u : List (Lt 0 r)) (hne : u ≠ [])
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hcl : c 0 = c (Fin.last _)) :
    Fcount u c = (LL (ac u hne) (Xc c) u.length).card := by
  rw [← sum_card_Ls u hne c hcl]; rfl

/-- `v ≤ e + 1` for every closed colouring. -/
theorem nv_le_succ (u : List (Lt 0 r)) (c : Fin (u.length + 1) → Fin (u.length + 1))
    (hcl : c 0 = c (Fin.last _)) : nv c ≤ Ecount u c + 1 := by
  by_cases hne : u = []
  · subst hne
    have : nv c ≤ (univ : Finset (Fin 1)).card := by
      unfold nv; exact card_le_card (subset_univ _)
    simp at this
    omega
  · have hL := List.length_pos_iff.2 hne
    rw [nv_eq hL c hcl, Ecount_eq u hne c hcl]
    refine le_trans (card_le_card ?_) (card_UU_le (ac u hne) (Xc c) u.length)
    exact image_subset_image (range_mono (by omega))

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
/-!
# Part W: colourings with loops of cyclically reduced words

* `nv_le_ecount_succ`: the pair graph is connected (`PartW_Walk`, `count`).
* `nv_le_ecount_add_fcount`, `fcount_eq_zero`: a tree walk of a cyclically reduced word has at
  least two loops (`TW.two_loops`).
* `card_second_order`: tree walks with exactly two loops go back and forth on a path
  (`TW.structure1`), so they are the fold colourings (`card_second_eq`), which correspond to the
  tuples of `C2count` by uniqueness of normal forms (`c2count_eq`).
-/
/-- The pair graph is connected: `v ≤ e + 1` (any word). -/
theorem nv_le_ecount_succ (u : List (Lt 0 r)) (c : Fin (u.length + 1) → Fin (u.length + 1))
    (hc : c ∈ CGL u) : nv c ≤ Ecount u c + 1 :=
  nv_le_succ u c (mem_CGL.1 hc).2.2.2

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-! ## Part W: colourings with loops of cyclically reduced words -/
alias nv_le_ecount_succ := RandomInvolutions.Dev.PartW.nv_le_ecount_succ

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
/-- A closed colouring of a cyclically reduced word with `v = e + 1` is a tree walk. -/
theorem tw_of_eq (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hcl : c 0 = c (Fin.last _))
    (h : nv c = Ecount u c + 1) : TW u.length (ac u hne) (Xc c) := by
  have hL := List.length_pos_iff.2 hne
  refine TW.mk' hL (Xc_per c) (ac_per u hne) (ac_cr u hne hcr) ?_
  rw [← nv_eq hL c hcl, ← Ecount_eq u hne c hcl]; exact h

/-- A tree colouring of a cyclically reduced word has at least two loops. -/
theorem two_le_fcount (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hcl : c 0 = c (Fin.last _))
    (h : nv c = Ecount u c + 1) : 2 ≤ Fcount u c := by
  have hL := List.length_pos_iff.2 hne
  rw [Fcount_eq u hne c hcl]
  exact (tw_of_eq u hne hcr c hcl h).two_loops _
    (fun t ht => mem_LL_of_loop hL (Xc_per c) (ac_per u hne) ht)

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r : ℕ}
/-- No leaves except at loops: `v ≤ e + f` for cyclically reduced words. -/
theorem nv_le_ecount_add_fcount (u : List (Lt 0 r)) (hne : u ≠ []) (hcr : CycRed u)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hc : c ∈ CGL u) :
    nv c ≤ Ecount u c + Fcount u c := by
  have hcl := (mem_CGL.1 hc).2.2.2
  have h1 := nv_le_succ u c hcl
  by_cases h : nv c = Ecount u c + 1
  · have := two_le_fcount u hne hcr c hcl h
    omega
  · omega

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias nv_le_ecount_add_fcount := RandomInvolutions.Dev.PartW.nv_le_ecount_add_fcount

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
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartK2
variable {r : ℕ}

/-! ## `tendsto_mul_expFixK_sub_first_order` -/

/-! ## `expFixK_le` -/
lemma lam_ge_one (κ : Fin r → ℕ) : 1 ≤ lam κ := by
  unfold lam
  have : 0 ≤ ∑ i, (κ i : ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
  linarith

lemma le_lam (κ : Fin r → ℕ) (i : Fin r) : (κ i : ℝ) ≤ lam κ := by
  unfold lam
  have := single_le_sum (f := fun i => (κ i : ℝ)) (fun _ _ => Nat.cast_nonneg _) (mem_univ i)
  linarith

lemma pow_le_two_pow_desc (N m : ℕ) (h : 2 * m ≤ N) :
    (N : ℝ) ^ m ≤ 2 ^ m * (N.descFactorial m : ℝ) := by
  have h1 : (N + 1 - m) ^ m ≤ N.descFactorial m := Nat.pow_sub_le_descFactorial N m
  have h2 : N ^ m ≤ 2 ^ m * (N + 1 - m) ^ m := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) m
  have h3 : N ^ m ≤ 2 ^ m * N.descFactorial m := h2.trans (Nat.mul_le_mul_left _ h1)
  exact_mod_cast h3

lemma factor_le (N k e f : ℕ) (hk : k ≤ N) (hm : 2 * (f + 2 * e) ≤ N) :
    |((k.descFactorial f : ℝ) * ∏ l ∈ range e, ((N : ℝ) - k - 2 * l)) /
        (N.descFactorial (f + 2 * e) : ℝ)| ≤
      2 ^ (f + 2 * e) * (k : ℝ) ^ f / (N : ℝ) ^ (e + f) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hf : f = 0 := by omega
    have he : e = 0 := by omega
    subst hf he
    simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hD := pow_le_two_pow_desc N (f + 2 * e) hm
  have hDpos : (0 : ℝ) < N.descFactorial (f + 2 * e) := by
    have h1 : (0 : ℝ) < (N : ℝ) ^ (f + 2 * e) := by positivity
    by_contra hc
    push Not at hc
    have h2 := mul_nonpos_of_nonneg_of_nonpos (pow_pos (two_pos (α := ℝ)) (f + 2 * e)).le hc
    linarith
  have hK : (k.descFactorial f : ℝ) ≤ (k : ℝ) ^ f := by
    exact_mod_cast Nat.descFactorial_le_pow k f
  have hP : |∏ l ∈ range e, ((N : ℝ) - k - 2 * l)| ≤ (N : ℝ) ^ e := by
    rw [abs_prod]
    calc ∏ l ∈ range e, |(N : ℝ) - k - 2 * l| ≤ ∏ _l ∈ range e, (N : ℝ) := by
          refine prod_le_prod (fun _ _ => abs_nonneg _) (fun l hl => ?_)
          have hl' : l < e := mem_range.1 hl
          rw [abs_le]
          have h1 : (k : ℝ) ≤ N := by exact_mod_cast hk
          have h2 : (2 : ℝ) * l ≤ N := by exact_mod_cast (by omega : 2 * l ≤ N)
          have h3 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
          have h4 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
          constructor <;> linarith
      _ = _ := by simp
  rw [abs_div, abs_mul, Nat.abs_cast, Nat.abs_cast, div_le_div_iff₀ hDpos (by positivity)]
  calc (k.descFactorial f : ℝ) * |∏ l ∈ range e, ((N : ℝ) - k - 2 * l)| * (N : ℝ) ^ (e + f)
      ≤ (k : ℝ) ^ f * (N : ℝ) ^ e * (N : ℝ) ^ (e + f) := by gcongr
    _ = (k : ℝ) ^ f * (N : ℝ) ^ (f + 2 * e) := by
        rw [mul_assoc, ← pow_add]; congr 2; omega
    _ ≤ (k : ℝ) ^ f * (2 ^ (f + 2 * e) * (N.descFactorial (f + 2 * e) : ℝ)) := by gcongr
    _ = _ := by ring

lemma kappa_prod_le (N : ℕ) (κ f : Fin r → ℕ) (hN : 1 ≤ N) (hκ : ∀ i, κ i ≤ N)
    (hF : 1 ≤ ∑ i, f i) :
    (N : ℝ) * ∏ i, (κ i : ℝ) ^ (f i) ≤ lam κ * (N : ℝ) ^ (∑ i, f i) := by
  have h0 : ∃ i0, f i0 ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at hF
  obtain ⟨i0, hi0⟩ := h0
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hκ' : ∀ i, (κ i : ℝ) ≤ N := fun i => by exact_mod_cast hκ i
  have hlam := lam_ge_one κ
  rw [← prod_pow_eq_pow_sum, ← mul_prod_erase univ (fun i => (κ i : ℝ) ^ (f i)) (mem_univ i0),
    ← mul_prod_erase univ (fun i => (N : ℝ) ^ (f i)) (mem_univ i0)]
  have h1 : (N : ℝ) * (κ i0 : ℝ) ^ (f i0) ≤ lam κ * (N : ℝ) ^ (f i0) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    rw [hm, pow_succ, pow_succ]
    calc (N : ℝ) * ((κ i0 : ℝ) ^ m * κ i0) ≤ (N : ℝ) * ((N : ℝ) ^ m * lam κ) := by
          gcongr
          · exact hκ i0
          · exact le_lam κ i0
      _ = _ := by ring
  have h2 : ∏ i ∈ univ.erase i0, (κ i : ℝ) ^ (f i) ≤ ∏ i ∈ univ.erase i0, (N : ℝ) ^ (f i) :=
    prod_le_prod (fun _ _ => by positivity)
      (fun i _ => pow_le_pow_left₀ (Nat.cast_nonneg _) (hκ' i) _)
  calc (N : ℝ) * ((κ i0 : ℝ) ^ (f i0) * ∏ i ∈ univ.erase i0, (κ i : ℝ) ^ (f i))
      = ((N : ℝ) * (κ i0 : ℝ) ^ (f i0)) * ∏ i ∈ univ.erase i0, (κ i : ℝ) ^ (f i) := by ring
    _ ≤ (lam κ * (N : ℝ) ^ (f i0)) * ∏ i ∈ univ.erase i0, (N : ℝ) ^ (f i) :=
        mul_le_mul h1 h2 (prod_nonneg fun _ _ => by positivity)
          (mul_nonneg (by linarith) (by positivity))
    _ = _ := by ring

lemma wtF_le (N : ℕ) (κ : Fin r → ℕ) (v : ℕ) (e f : Fin r → ℕ) (hN : 1 ≤ N)
    (hκ : ∀ i, κ i ≤ N) (hm : ∀ i, 2 * (f i + 2 * e i) ≤ N)
    (h1 : v ≤ ∑ i, e i + ∑ i, f i) (h2 : v ≤ ∑ i, e i + 1) :
    wtF N κ v e f ≤ 2 ^ (∑ i, (f i + 2 * e i)) * lam κ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlam := lam_ge_one κ
  unfold wtF
  refine (le_abs_self _).trans ?_
  rw [abs_mul, Nat.abs_cast, abs_prod]
  have hv : (N.descFactorial v : ℝ) ≤ (N : ℝ) ^ v := by
    exact_mod_cast Nat.descFactorial_le_pow N v
  have hprod := prod_le_prod (s := (univ : Finset (Fin r))) (fun _ _ => abs_nonneg _)
    (fun i _ => factor_le N (κ i) (e i) (f i) (hκ i) (hm i))
  have hrhs : ∏ i, (2 ^ (f i + 2 * e i) * (κ i : ℝ) ^ (f i) / (N : ℝ) ^ (e i + f i)) =
      2 ^ (∑ i, (f i + 2 * e i)) * (∏ i, (κ i : ℝ) ^ (f i)) /
        (N : ℝ) ^ (∑ i, e i + ∑ i, f i) := by
    rw [prod_div_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum,
      ← sum_add_distrib]
  have hPnn : (0 : ℝ) ≤ ∏ i, (κ i : ℝ) ^ (f i) := prod_nonneg fun _ _ => by positivity
  have hmain : (N : ℝ) ^ v * ∏ i, (κ i : ℝ) ^ (f i) ≤
      lam κ * (N : ℝ) ^ (∑ i, e i + ∑ i, f i) := by
    rcases Nat.eq_zero_or_pos (∑ i, f i) with hF | hF
    · have hf : ∀ i, f i = 0 := fun i => (sum_eq_zero_iff.1 hF) i (mem_univ i)
      have hv' : v ≤ ∑ i, e i := by omega
      simp only [hf, pow_zero, prod_const_one, mul_one, sum_const_zero, add_zero]
      calc (N : ℝ) ^ v ≤ (N : ℝ) ^ (∑ i, e i) := pow_le_pow_right₀ hN1 hv'
        _ ≤ _ := le_mul_of_one_le_left (by positivity) hlam
    · have h3 := kappa_prod_le N κ f hN hκ hF
      calc (N : ℝ) ^ v * ∏ i, (κ i : ℝ) ^ (f i)
          ≤ (N : ℝ) ^ (∑ i, e i + 1) * ∏ i, (κ i : ℝ) ^ (f i) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hN1 h2) hPnn
        _ = (N : ℝ) ^ (∑ i, e i) * ((N : ℝ) * ∏ i, (κ i : ℝ) ^ (f i)) := by ring
        _ ≤ (N : ℝ) ^ (∑ i, e i) * (lam κ * (N : ℝ) ^ (∑ i, f i)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by ring
  calc (N.descFactorial v : ℝ) * ∏ i, |(((κ i).descFactorial (f i) : ℝ) *
          ∏ l ∈ range (e i), ((N : ℝ) - κ i - 2 * l)) / (N.descFactorial (f i + 2 * e i) : ℝ)|
      ≤ (N : ℝ) ^ v * (2 ^ (∑ i, (f i + 2 * e i)) * (∏ i, (κ i : ℝ) ^ (f i)) /
          (N : ℝ) ^ (∑ i, e i + ∑ i, f i)) := by
        rw [← hrhs]
        exact mul_le_mul hv hprod (prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
    _ = 2 ^ (∑ i, (f i + 2 * e i)) * ((N : ℝ) ^ v * ∏ i, (κ i : ℝ) ^ (f i)) /
          (N : ℝ) ^ (∑ i, e i + ∑ i, f i) := by ring
    _ ≤ 2 ^ (∑ i, (f i + 2 * e i)) * (lam κ * (N : ℝ) ^ (∑ i, e i + ∑ i, f i)) /
          (N : ℝ) ^ (∑ i, e i + ∑ i, f i) := by gcongr
    _ = _ := by field_simp

lemma fK_le (u : List (Lt 0 r)) (c : Fin (u.length + 1) → Fin (u.length + 1)) (i : Fin r) :
    fK u c i ≤ u.length := by
  unfold fK Ls
  exact (card_image_le.trans (card_filter_le _ _)).trans_eq (by simp)

lemma eK_le (u : List (Lt 0 r)) (c : Fin (u.length + 1) → Fin (u.length + 1)) (i : Fin r) :
    eK u c i ≤ u.length := by
  unfold eK Ps
  exact (card_image_le.trans (card_filter_le _ _)).trans_eq (by simp)

/-- A bound uniform along all rays. -/
theorem expFixK_le (g : G 0 r) (hg : g ≠ 1) :
    ∃ C : ℝ, ∀ (N : ℕ) (κ : Fin r → ℕ), AdmK N κ → 1 ≤ N → expFixK r N κ g ≤ C * lam κ := by
  obtain ⟨a, u, hne, rfl, hlen, hcase⟩ := exists_cyc_rep g hg
  rcases hcase with hc | ⟨i, rfl⟩
  · refine ⟨max (6 * u.length : ℝ) ((CGL u).card * 2 ^ (r * (3 * u.length))),
      fun N κ hA hN => ?_⟩
    have hlam := lam_ge_one κ
    by_cases hbig : 6 * u.length ≤ N
    · rw [expFixK_conj, expect_formulaK u N κ hN hA (by omega)]
      have hw : ∀ c ∈ CGL u, wtK u N κ c ≤ 2 ^ (r * (3 * u.length)) * lam κ := by
        intro c hc'
        have hf := fK_le u c
        have he := eK_le u c
        refine (wtF_le N κ _ _ _ hN (fun i => (hA i).1)
          (fun i => by have := hf i; have := he i; omega)
          (nv_le_ecount_add_fcount u hne hc c hc') (nv_le_ecount_succ u c hc')).trans ?_
        have hs : ∑ i, (fK u c i + 2 * eK u c i) ≤ r * (3 * u.length) := by
          calc ∑ i, (fK u c i + 2 * eK u c i) ≤ ∑ _i : Fin r, 3 * u.length :=
                sum_le_sum fun i _ => by have := hf i; have := he i; omega
            _ = _ := by simp
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hs) (by linarith)
      calc ∑ c ∈ CGL u, wtK u N κ c ≤ ∑ _c ∈ CGL u, 2 ^ (r * (3 * u.length)) * lam κ :=
            sum_le_sum hw
        _ = ((CGL u).card * 2 ^ (r * (3 * u.length))) * lam κ := by
            rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    · calc expFixK r N κ (a * wprod u * a⁻¹) ≤ N := expFixK_le_N _ _ _
        _ ≤ 6 * u.length := by exact_mod_cast (by omega : N ≤ 6 * u.length)
        _ ≤ max (6 * u.length : ℝ) ((CGL u).card * 2 ^ (r * (3 * u.length))) := le_max_left _ _
        _ ≤ _ := le_mul_of_one_le_right (le_max_of_le_left (by positivity)) hlam
  · refine ⟨1, fun N κ hA hN => ?_⟩
    rw [wprod_single, expFixK_torsion hA, one_mul]
    exact le_lam κ i

end RandomInvolutions.Dev.PartK2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias expFixK_le := RandomInvolutions.Dev.PartK2.expFixK_le

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartX
variable {r : ℕ}
/-! ## The two consequences -/
theorem expFix_unif_le (g : G 0 r) (hg : g ≠ 1) :
    ∃ C : ℝ, ∀ N : ℕ,
      expFixOn (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N => homI τ) g ≤
        C * (Real.sqrt N + 1) := by
  obtain ⟨C, hC⟩ := RandomInvolutions.Dev.expFixK_le g hg
  refine ⟨max C 0 * (r + 1), fun N => ?_⟩
  have hs : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hC0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hE : expFixOn (fun τ : Fin r → Inv N => homI τ) g =
      StrongConv.uniformExp (fun τ : Fin r → Inv N => (fixCount (homI τ g) : ℝ)) := rfl
  rw [hE]
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    have : StrongConv.uniformExp (fun τ : Fin r → Inv 0 => (fixCount (homI τ g) : ℝ)) ≤
        StrongConv.uniformExp (fun _ : Fin r → Inv 0 => (0 : ℝ)) :=
      uniformExp_mono _ _ fun τ => by
        have := fixCount_le 0 (homI τ g)
        exact_mod_cast this
    rw [uniformExp_const] at this
    refine this.trans ?_
    positivity
  · have := mix_affine N (fun τ : Fin r → Inv N => (fixCount (homI τ g) : ℝ)) (max C 0) 0 hC0
      (fun κ hA => by
        have h1 := hC N κ hA hN
        have h2 : StrongConv.uniformExp
            (fun τ : OmK r N κ => (fixCount (homI (fun i => (τ i).1) g) : ℝ)) =
            expFixK r N κ g := rfl
        rw [h2, add_zero]
        refine h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
        unfold lam
        have : (0 : ℝ) ≤ ∑ i, (κ i : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
        linarith)
    refine this.trans ?_
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    nlinarith [mul_nonneg hC0 hs, mul_nonneg hC0 hr, mul_nonneg (mul_nonneg hC0 hr) hs]

end RandomInvolutions.Dev.PartX
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias expFix_unif_le := RandomInvolutions.Dev.PartX.expFix_unif_le

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartX
variable {r : ℕ}
theorem tail_arith (C M s L p : ℝ) (hC : 0 ≤ C) (hM : 0 < M) (hs : 1 ≤ s) (hL : 0 ≤ L)
    (hp1 : p ≤ 1) (hp2 : p ≤ C * L / s ^ 2 + C * L ^ 3 / (s ^ 2) ^ 2) :
    p ≤ 1 / (M * s) * L + C * (M + M ^ 3) / s := by
  have hs0 : 0 < s := by linarith
  have hMs : 0 < M * s := mul_pos hM hs0
  rcases le_or_gt L (M * s) with h | h
  · have e1 : C * L / s ^ 2 ≤ C * M / s := by
      rw [div_le_div_iff₀ (by positivity) hs0]
      nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg hC (mul_nonneg hs0.le hs0.le))]
    have e2 : C * L ^ 3 / (s ^ 2) ^ 2 ≤ C * M ^ 3 / s := by
      rw [div_le_div_iff₀ (by positivity) hs0]
      have h3 : L ^ 3 ≤ (M * s) ^ 3 := pow_le_pow_left₀ hL h 3
      have := mul_le_mul_of_nonneg_left h3 (mul_nonneg hC hs0.le)
      nlinarith [this]
    have e3 : 0 ≤ 1 / (M * s) * L := by positivity
    have e4 : C * (M + M ^ 3) / s = C * M / s + C * M ^ 3 / s := by ring
    linarith
  · have : 1 ≤ 1 / (M * s) * L := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hMs]
      linarith
    have e3 : 0 ≤ C * (M + M ^ 3) / s := by positivity
    linarith

theorem upper_unif {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (hz : adj z = z) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => StrongConv.uniformProb
      (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
        ‖regOp z‖ + ε ≤ ‖perpOp (homI τ) z‖)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := RandomInvolutions.Dev.prob_norm_perpOp_ge_le hD z hz ε hε
  have hC0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  -- the bound for each `M`
  have key : ∀ M : ℝ, 0 < M → ∀ N : ℕ, 1 ≤ N →
      StrongConv.uniformProb (fun τ : Fin r → Inv N => ‖regOp z‖ + ε ≤ ‖perpOp (homI τ) z‖) ≤
        (2 * r + 1) / M + max C 0 * (M + M ^ 3) / Real.sqrt N := by
    intro M hM N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hs : 1 ≤ Real.sqrt N := by
      rw [Real.one_le_sqrt]; exact hN1
    have hs0 : 0 < Real.sqrt N := by linarith
    have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by linarith)
    rw [uniformProb_eq_exp]
    have := mix_affine N (fun τ : Fin r → Inv N =>
        if ‖regOp z‖ + ε ≤ ‖perpOp (homI τ) z‖ then (1 : ℝ) else 0)
      (1 / (M * Real.sqrt N)) (max C 0 * (M + M ^ 3) / Real.sqrt N) (by positivity)
      (fun κ hA => by
        have h1 := hC N κ hA hN
        have hlam : (0 : ℝ) ≤ lam κ := by
          unfold lam
          have : (0 : ℝ) ≤ ∑ i, (κ i : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
          linarith
        have h2 : StrongConv.uniformExp (fun τ : OmK r N κ =>
            if ‖regOp z‖ + ε ≤ ‖perpOp (homI (fun i => (τ i).1)) z‖ then (1 : ℝ) else 0) =
            StrongConv.uniformProb
              (fun τ : OmK r N κ => ‖regOp z‖ + ε ≤ ‖perpOp (homK τ) z‖) :=
          (uniformProb_eq_exp _).symm
        rw [h2]
        refine tail_arith (max C 0) M (Real.sqrt N) (lam κ) _ hC0 hM hs hlam
          (uniformProb_le_one _) ?_
        rw [hsq]
        refine h1.trans (add_le_add ?_ ?_)
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hlam) (by positivity)
        · exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity))
    refine this.trans (add_le_add ?_ le_rfl)
    rw [one_div, inv_mul_eq_div, div_le_div_iff₀ (by positivity) hM]
    nlinarith [mul_nonneg hr (sub_nonneg.2 hs), mul_nonneg hM.le (sub_nonneg.2 hs),
      mul_nonneg (mul_nonneg hr hM.le) (sub_nonneg.2 hs), mul_nonneg hr hM.le]
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun N => lt_of_lt_of_le ha (uniformProb_nonneg _),
    fun η hη => ?_⟩
  set M : ℝ := 2 * (2 * r + 1) / η with hMdef
  have hM : 0 < M := by positivity
  have hlim : Tendsto (fun N : ℕ => max C 0 * (M + M ^ 3) / Real.sqrt N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hev := (tendsto_order.1 hlim).2 (η / 2) (by positivity)
  filter_upwards [hev, eventually_ge_atTop 1] with N h1 h2
  have h3 := key M hM N h2
  have h4 : (2 * (r : ℝ) + 1) / M = η / 2 := by
    rw [hMdef]; field_simp
  linarith

end RandomInvolutions.Dev.PartX
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias upper_unif := RandomInvolutions.Dev.PartX.upper_unif

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical InnerProductSpace
noncomputable section
namespace RandomInvolutions.Dev.PartL2
set_option linter.unusedSectionVars false
variable {r : ℕ} {D : ℕ}
theorem lower_unif {D : ℕ} (hD : 1 ≤ D) (x : MG D 0 r) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => StrongConv.uniformProb
      (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
        ‖perpOp (homI τ) x‖ ≤ ‖regOp x‖ - ε)) atTop (𝓝 0) := by
  set ρ := ‖regOp x‖ with hρ
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  by_cases hneg : ρ - ε < 0
  · have : (fun N : ℕ => StrongConv.uniformProb
        (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
          ‖perpOp (homI τ) x‖ ≤ ρ - ε)) = fun _ => 0 := by
      funext N
      have h : ∀ τ : Fin r → ZigZagStrong.ZigZag.Involution N,
          ¬ (‖perpOp (homI τ) x‖ ≤ ρ - ε) := fun τ hτ =>
        absurd (norm_nonneg (perpOp (homI τ) x)) (by linarith)
      simp [StrongConv.uniformProb, h]
    rw [this]
    exact tendsto_const_nhds
  push Not at hneg
  -- choose `p`
  have hfa := BordenaveCollins.tendsto_re_trTau_pow_rpow hD x
  obtain ⟨p, hp, hp1⟩ :=
    ((hfa.eventually (lt_mem_nhds (show ρ - ε < ρ by linarith))).and
      (eventually_ge_atTop 1)).exists
  set a := (trTau ((adj x * x) ^ p)).re with ha
  have ha0 : 0 ≤ a := re_trTau_nonneg x p
  set b := (ρ - ε) ^ (2 * p) with hb
  have hab : b < a := by
    by_contra hcon
    push Not at hcon
    have h2 : (1 / (2 * (p : ℝ))) = ((2 * p : ℕ) : ℝ)⁻¹ := by push_cast; ring
    have : a ^ (1 / (2 * (p : ℝ))) ≤ ρ - ε := by
      calc a ^ (1 / (2 * (p : ℝ))) ≤ b ^ (1 / (2 * (p : ℝ))) :=
            Real.rpow_le_rpow ha0 hcon (by positivity)
        _ = ρ - ε := by rw [hb, h2, Real.pow_rpow_inv_natCast hneg (by omega)]
    linarith
  set S := ((adj x * x) ^ p).coeff.support.erase 1 with hS
  set C := ∑ g ∈ S, |(Matrix.trace (((adj x * x) ^ p).coeff g)).re| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun g _ => abs_nonneg _
  set gap := a - b with hgap
  have hgap0 : 0 < gap := by linarith
  set η := gap * D / (2 * (C + 1)) with hη
  have hη0 : 0 < η := by positivity
  -- the bounds on the expected fixed points
  have hex : ∀ g : G 0 r, ∃ Cg : ℝ, g ≠ 1 → ∀ N : ℕ,
      expFixOn (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N => homI τ) g ≤
        Cg * (Real.sqrt N + 1) := by
    intro g
    by_cases hg : g = 1
    · exact ⟨0, fun h => absurd hg h⟩
    · obtain ⟨Cg, hCg⟩ := RandomInvolutions.Dev.expFix_unif_le g hg
      exact ⟨Cg, fun _ => hCg⟩
  choose Cg hCg using hex
  -- the dominating sequence
  have hlim : Tendsto (fun N : ℕ => ∑ g ∈ S, (Cg g / η) * (Real.sqrt N + 1) / (N : ℝ)) atTop
      (𝓝 0) := by
    have : Tendsto (fun N : ℕ => ∑ g ∈ S, (Cg g / η) * (Real.sqrt N + 1) / (N : ℝ)) atTop
        (𝓝 (∑ _g ∈ S, (0 : ℝ))) :=
      tendsto_finsetSum _ fun g _ => tendsto_sqrt_div _
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => RandomInvolutions.Dev.uniformProb_nonneg _) ?_
  set K := (D * a + C) / (D * gap / 2) with hK
  filter_upwards [eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop K)] with N hN hKn
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsub : ∀ τ : Fin r → ZigZagStrong.ZigZag.Involution N, ‖perpOp (homI τ) x‖ ≤ ρ - ε →
      ∃ g ∈ S, η * (N : ℝ) < (fixCount (homI τ g) : ℝ) := by
    intro τ hτ
    by_contra hcon
    push Not at hcon
    have hY : ‖perpOp (homI τ) x‖ ^ (2 * p) ≤ b := pow_le_pow_left₀ (norm_nonneg _) hτ _
    have h := det_bound hD hN (homI τ) x p hp1 b η hη0.le hY hcon
    rw [← ha, ← hC, ← hgap] at h
    have hCη : C * (η * (N : ℝ)) ≤ D * (N : ℝ) * gap / 2 := by
      have e : C * (η * (N : ℝ)) = (C / (C + 1)) * (D * (N : ℝ) * gap / 2) := by
        rw [hη]; field_simp
      rw [e]
      have h1 : C / (C + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      exact mul_le_of_le_one_left (by positivity) h1
    have hK2 : D * a + C < D * gap / 2 * (N : ℝ) := by
      rw [hK, div_lt_iff₀ (by positivity)] at hKn
      linarith
    nlinarith
  calc StrongConv.uniformProb (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
        ‖perpOp (homI τ) x‖ ≤ ρ - ε)
      ≤ StrongConv.uniformProb (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
          ∃ g ∈ S, η * (N : ℝ) < (fixCount (homI τ g) : ℝ)) :=
        RandomInvolutions.Dev.uniformProb_mono _ _ hsub
    _ ≤ ∑ g ∈ S, StrongConv.uniformProb (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
          η * (N : ℝ) < (fixCount (homI τ g) : ℝ)) := uniformProb_union S _
    _ ≤ ∑ g ∈ S, expFixOn (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N => homI τ) g /
          (η * (N : ℝ)) :=
        Finset.sum_le_sum fun g _ => markov _ g _ (by positivity)
    _ ≤ ∑ g ∈ S, (Cg g / η) * (Real.sqrt N + 1) / (N : ℝ) := by
        refine Finset.sum_le_sum fun g hg => ?_
        have hg1 : g ≠ 1 := (Finset.mem_erase.mp hg).1
        have h1 := hCg g hg1 N
        have e : (Cg g / η) * (Real.sqrt N + 1) / (N : ℝ) =
            Cg g * (Real.sqrt N + 1) / (η * (N : ℝ)) := by
          field_simp
        rw [e]
        exact div_le_div_of_nonneg_right h1 (by positivity)

end RandomInvolutions.Dev.PartL2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-! ## Part L2: the lower tail -/
alias lower_unif := RandomInvolutions.Dev.PartL2.lower_unif

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartT2
variable {r : ℕ}
/-! ## The core theorem -/
theorem tendsto_prob_abs_norm_perpOp_sub_ge {D : ℕ} (x : MG D 0 r) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => StrongConv.uniformProb
      (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
        ε ≤ |‖perpOp (homI τ) x‖ - ‖regOp x‖|)) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · subst hD0
    have h1 : ‖regOp x‖ = 0 := by
      have : regOp x = 0 := ContinuousLinearMap.ext fun v => Subsingleton.elim _ _
      rw [this, norm_zero]
    have h2 : ∀ (N : ℕ) (π : G 0 r →* Equiv.Perm (Fin N)), ‖perpOp π x‖ = 0 := by
      intro N π
      have : perpOp π x = 0 := ContinuousLinearMap.ext fun v => Subsingleton.elim _ _
      rw [this, norm_zero]
    have h3 : ∀ N : ℕ, StrongConv.uniformProb
        (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
          ε ≤ |‖perpOp (homI τ) x‖ - ‖regOp x‖|) = 0 := by
      intro N
      unfold StrongConv.uniformProb
      have : (univ.filter fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
          ε ≤ |‖perpOp (homI τ) x‖ - ‖regOp x‖|) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun τ _ => ?_
        rw [h1, h2, sub_zero, abs_zero]
        exact not_le.mpr hε
      rw [this]
      simp
    simp only [h3]
    exact tendsto_const_nhds
  · have hz : adj (adj x * x) = adj x * x := adj_adj_mul_self x
    have hup := RandomInvolutions.Dev.upper_unif hD (adj x * x) hz (ε ^ 2) (by positivity)
    have hlo := RandomInvolutions.Dev.lower_unif hD x ε hε
    have hsum := hup.add hlo
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun N => RandomInvolutions.Dev.uniformProb_nonneg _) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    refine uniformProb_le_add _ _ _ fun τ hτ => ?_
    rw [norm_regOp_sq, norm_perpOp_sq hN]
    have ha : 0 ≤ ‖regOp x‖ := norm_nonneg _
    by_cases hc : ‖perpOp (homI τ) x‖ ≤ ‖regOp x‖ - ε
    · exact Or.inr hc
    · left
      rw [not_le] at hc
      have h4 : ‖regOp x‖ + ε ≤ ‖perpOp (homI τ) x‖ := by
        rcases le_abs.mp hτ with h | h
        · linarith
        · linarith
      nlinarith

end RandomInvolutions.Dev.PartT2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-! ## Part T2: the core theorem -/
alias tendsto_prob_abs_norm_perpOp_sub_ge := RandomInvolutions.Dev.PartT2.tendsto_prob_abs_norm_perpOp_sub_ge

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
open RandomInvolutions
open RandomInvolutions.Dev
theorem solution {r : ℕ} {D : ℕ} (x : MG D 0 r) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => StrongConv.uniformProb
      (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
        ε ≤ |‖perpOp (homI τ) x‖ - ‖regOp x‖|)) atTop (𝓝 0) := by
  exact RandomInvolutions.Dev.tendsto_prob_abs_norm_perpOp_sub_ge x ε hε
end
end
