-- Prove2me | solution 1 for RandomInvolutions.prob_norm_perpOp_ge_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T11:49:31.028715+00:00
-- url     : https://prove2.me/submissions/152f9249-420b-41bc-8e73-5ee22ce4994b

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_StrongConv
import Definitions.Def_DerandSq_permOp
import Definitions.Def_ZigZagStrong_ZigZag_Models
import Definitions.Def_RandomInvolutions
import Theorems.Thm_BordenaveCollins_norm_sum_cfun_mul_trace_Bprod_le
import Theorems.Thm_BordenaveCollins_exists_linearization
import Theorems.Thm_RandomInvolutions_tail_le_of_second_order_rational_moments
import Theorems.Thm_RandomInvolutions_norm_sum_bcount_mul_trace_Bprod_le
import Theorems.Thm_RandomInvolutions_norm_sum_c2count_mul_trace_Bprod_le
import Theorems.Thm_RandomInvolutions_tendsto_mul_expFixK_sub_first_order

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

/-- The expected spectral functional `E[(1/(DN)) Re Tr f(Y_ω)]`, `Y_ω = perpOp (act ω) x`, over
a uniform `ω` in a finite sample space (`0` if it is empty); `f(Y)` is the continuous functional
calculus of `w ↦ f (re w)`. -/
def specE {r D N : ℕ} {Ω : Type*} [Fintype Ω] (act : Ω → G 0 r →* Equiv.Perm (Fin N))
    (x : MG D 0 r) (f : ℝ → ℝ) : ℝ :=
  (∑ ω : Ω, (LinearMap.trace ℂ _
      ((cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (perpOp (act ω) x) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →L[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N)))).re) /
    ((Fintype.card Ω : ℝ) * ((D : ℝ) * N))

/-- A crude bound for the norm of `x` in any unitary representation. -/
def bnd {r D : ℕ} (x : MG D 0 r) : ℝ := ∑ g ∈ x.coeff.support, ∑ a, ∑ b, ‖x.coeff g a b‖

/-- The largest word length in the support. -/
def lenmax {r D : ℕ} (x : MG D 0 r) : ℕ := x.coeff.support.sup len

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
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}

/-- `E_{N,κ}[fix g] = cfun g + 1 + ∑ κᵢ Bᵢ(g) + (C₀(g) + ∑ κᵢ C₁ᵢ(g) + ∑ κᵢ κⱼ C₂ᵢⱼ(g))/N +
o(1/N)` along admissible `N`, for `g ≠ 1`. -/
theorem tendsto_mul_expFixK_sub_first_order (r : ℕ) : ∃ (C0 : G 0 r → ℝ) (C1 : Fin r → G 0 r → ℝ),
    ∀ g : G 0 r, g ≠ 1 → ∀ κ : Fin r → ℕ,
      Tendsto (fun N : ℕ => (N : ℝ) * (expFixK r N κ g -
          ((cfun g : ℝ) + 1 + ∑ i, (κ i : ℝ) * Bcount i g))) (admF κ)
        (𝓝 (C0 g + ∑ i, (κ i : ℝ) * C1 i g +
          ∑ i, ∑ j, (κ i : ℝ) * κ j * C2count i j g)) := by
  exact RandomInvolutions.tendsto_mul_expFixK_sub_first_order r

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-- The tail bound: if the first-order coefficient is `A + ∑ κᵢ Bᵢ`, the quadratic part of the
second-order coefficient is `∑ κᵢ κⱼ C₂ᵢⱼ`, and the moments of `a`, `A`, `Bᵢ`, `C₂ᵢⱼ` grow at most
like `(ρ + δ)^p`, then the mass outside `(-ρ-ε, ρ+ε)` is `O(lam κ / N² + lam κ³ / N³)`, uniformly
in `κ`. -/
theorem tail_le_of_second_order_rational_moments (K : ℝ) (hK : 0 < K) (r : ℕ) (E : (Fin r → ℕ) → ℕ → (ℝ → ℝ) → ℝ)
    (hadd : ∀ κ N f g, E κ N (f + g) = E κ N f + E κ N g)
    (hsmul : ∀ κ N (a : ℝ) f, E κ N (a • f) = a * E κ N f)
    (hmono : ∀ κ N f g, (∀ x ∈ Set.Icc (-K) K, f x ≤ g x) → E κ N f ≤ E κ N g)
    (hone : ∀ κ N, E κ N (fun _ => 1) ≤ 1)
    (hrat : ∃ C : ℕ, 1 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∀ κ : Fin r → ℕ, ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ N : ℕ, AdmK N κ → C * q ≤ N →
          E κ N (fun x => h.eval x) = f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a A : ℕ → ℝ) (B : Fin r → ℕ → ℝ) (C2 : Fin r → Fin r → ℕ → ℝ)
    (hexp : ∃ (C0 : ℕ → ℝ) (C1 : Fin r → ℕ → ℝ), ∀ (κ : Fin r → ℕ) (p : ℕ),
      Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (E κ N (fun x => x ^ p) - a p -
          (A p + ∑ i, (κ i : ℝ) * B i p) / N)) (admF κ)
        (𝓝 (C0 p + ∑ i, (κ i : ℝ) * C1 i p + ∑ i, ∑ j, (κ i : ℝ) * κ j * C2 i j p)))
    (hagrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |a p| ≤ C * (ρ + δ) ^ p)
    (hAgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |A p| ≤ C * (ρ + δ) ^ p)
    (hBgrow : ∀ i, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |B i p| ≤ C * (ρ + δ) ^ p)
    (hC2grow : ∀ i j, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |C2 i j p| ≤ C * (ρ + δ) ^ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (κ : Fin r → ℕ) (N : ℕ), AdmK N κ → 1 ≤ N →
      E κ N (fun x => if ρ + ε ≤ |x| then 1 else 0) ≤
        C * lam κ / (N : ℝ) ^ 2 + C * lam κ ^ 3 / (N : ℝ) ^ 3 := by
  exact RandomInvolutions.tail_le_of_second_order_rational_moments K hK r E hadd hsmul hmono hone hrat ρ hρ a A B C2 hexp hagrow hAgrow hBgrow hC2grow ε hε

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartP3a
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r : ℕ}
/-!
# Part P3a: `moment_bound_of_lin` and `norm_sum_bcount_mul_trace_Bprod_le`

* `moment_bound_of_lin`: the transfer `p ↦ m = p·q` through the published Pisier linearization
  `BordenaveCollins.exists_linearization`, for a general weight `w`.
* `norm_sum_bcount_mul_trace_Bprod_le`: the "involution part" of bc214's `core_bound`: the sum over `a` of the
  first-passage expansion of `a | m_{i₀} | a⁻¹` (`shapeI`).
-/
/-- Transfer of a bound on linearized sums to the moments of `x`. -/
theorem moment_bound_of_lin {D : ℕ} (x : MG D 0 r) (w : G 0 r → ℂ)
    (hw : ∀ (L : Lin 0 r) (R : ℝ), 0 ≤ R → (∀ j, ‖Xop L j‖ ≤ R) →
      ∃ (C : ℝ) (k : ℕ), ∀ m : ℕ, 1 ≤ m →
        ‖∑ i : Fin m → Option (Lt 0 r), w (iprod i) * (Bprod L m i).trace‖ ≤
          C * (m : ℝ) ^ k * R ^ m)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (C : ℝ) (k : ℕ), ∀ p : ℕ, 1 ≤ p →
      ‖∑ g ∈ (x ^ p).coeff.support, w g * Matrix.trace ((x ^ p).coeff g)‖ ≤
        C * (p : ℝ) ^ k * (‖regOp x‖ + δ) ^ p := by
  obtain ⟨L, hX, htr⟩ := BordenaveCollins.exists_linearization x δ hδ
  have hc0 : 0 < ‖regOp x‖ + δ := by positivity
  have hR0 : 0 ≤ (‖regOp x‖ + δ) ^ (1 / (L.q : ℝ)) := Real.rpow_nonneg hc0.le _
  have hRq : ((‖regOp x‖ + δ) ^ (1 / (L.q : ℝ))) ^ L.q = ‖regOp x‖ + δ := by
    rw [one_div, Real.rpow_inv_natCast_pow hc0.le (by have := L.hq; omega)]
  obtain ⟨C, k, hC⟩ := hw L _ hR0 hX
  refine ⟨C * (L.q : ℝ) ^ k, k, fun p hp => ?_⟩
  have hm : 1 ≤ p * L.q := Nat.mul_pos hp L.hq
  set F : G 0 r → ℂ := fun g => w g * Matrix.trace ((x ^ p).coeff g) with hFdef
  set h : (Fin (p * L.q) → Option (Lt 0 r)) → ℂ := fun i =>
    w (iprod i) * (Bprod L (p * L.q) i).trace with hhdef
  have hF : ∀ g, F g = ∑ i with iprod i = g, h i := by
    intro g
    simp only [hFdef]
    rw [htr p hp g, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : iprod i = g
    · simp only [hhdef, if_pos hi]
      rw [hi]
    · simp only [if_neg hi, mul_zero]
  have key : ∑ g ∈ (x ^ p).coeff.support, F g = ∑ i, h i := by
    set S : Finset (G 0 r) := (x ^ p).coeff.support ∪ Finset.univ.image iprod with hS
    calc ∑ g ∈ (x ^ p).coeff.support, F g = ∑ g ∈ S, F g := by
          refine Finset.sum_subset Finset.subset_union_left fun g _ hg => ?_
          have h0 : (x ^ p).coeff g = 0 := Finsupp.notMem_support_iff.mp hg
          simp only [hFdef, h0, Matrix.trace_zero, mul_zero]
      _ = ∑ g ∈ S, ∑ i with iprod i = g, h i := Finset.sum_congr rfl fun g _ => hF g
      _ = ∑ i, h i :=
          Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_union_right _
            (Finset.mem_image_of_mem _ (Finset.mem_univ i))) h
  rw [key]
  refine (hC (p * L.q) hm).trans (le_of_eq ?_)
  rw [pow_mul', hRq]
  push_cast
  ring

end RandomInvolutions.Dev.PartP3a
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-! ## Part P3: growth of the coefficient moments (linearization and first passage) -/
alias moment_bound_of_lin := RandomInvolutions.Dev.PartP3a.moment_bound_of_lin

/-- The single-loop coefficient: conjugates `a m_i a⁻¹`. -/
theorem norm_sum_bcount_mul_trace_Bprod_le (L : Lin 0 r) (R : ℝ) (hR : 0 ≤ R) (hX : ∀ j, ‖Xop L j‖ ≤ R)
    (i0 : Fin r) :
    ∃ (C : ℝ) (k : ℕ), ∀ m : ℕ, 1 ≤ m →
      ‖∑ i : Fin m → Option (Lt 0 r), (Bcount i0 (iprod i) : ℂ) * (Bprod L m i).trace‖ ≤
        C * (m : ℝ) ^ k * R ^ m := by
  exact RandomInvolutions.norm_sum_bcount_mul_trace_Bprod_le L R hR hX i0

/-- The two-loop coefficient: `a (ρ m_j ρ⁻¹ σ m_i σ⁻¹)^t a⁻¹`. -/
theorem norm_sum_c2count_mul_trace_Bprod_le (L : Lin 0 r) (R : ℝ) (hR : 0 ≤ R) (hX : ∀ j, ‖Xop L j‖ ≤ R)
    (i0 j0 : Fin r) :
    ∃ (C : ℝ) (k : ℕ), ∀ m : ℕ, 1 ≤ m →
      ‖∑ i : Fin m → Option (Lt 0 r), (C2count i0 j0 (iprod i) : ℂ) * (Bprod L m i).trace‖ ≤
        C * (m : ℝ) ^ k * R ^ m := by
  exact RandomInvolutions.norm_sum_c2count_mul_trace_Bprod_le L R hR hX i0 j0

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartU2
variable {r : ℕ}
/-!
# Part U2: the upper tail in the conditional model (assembly)

`prob_norm_perpOp_ge_le` from `tail_le_of_second_order_rational_moments`, the `specE_*` stubs, `tail_le`, `rationalK`, `tendsto_mul_expFixK_sub_first_order`,
`moment_bound_of_lin`, `norm_sum_bcount_mul_trace_Bprod_le`, `norm_sum_c2count_mul_trace_Bprod_le`, `trTau_pow_le`,
`len_support_aeval` and the published `BordenaveCollins.norm_sum_cfun_mul_trace_Bprod_le`.
-/
/-! ## Small facts -/
theorem len_one : len (1 : G 0 r) = 0 := by
  unfold len
  apply Nat.eq_zero_of_le_zero
  exact Nat.sInf_le ⟨[], rfl, by simp [wprod]⟩

theorem Bcount_one (i : Fin r) : Bcount i (1 : G 0 r) = 0 := by
  unfold Bcount
  have : IsEmpty {a : G 0 r // (1 : G 0 r) = a * mI i * a⁻¹ ∧
      len (1 : G 0 r) = 2 * len a + 1} :=
    ⟨fun ⟨a, _, h⟩ => by rw [len_one] at h; omega⟩
  exact Nat.card_of_isEmpty

theorem C2count_one (i j : Fin r) : C2count i j (1 : G 0 r) = 0 := by
  unfold C2count
  have : IsEmpty {p : G 0 r × G 0 r × G 0 r × ℕ // 1 ≤ p.2.2.2 ∧
      (1 : G 0 r) =
        p.1 * (p.2.1 * mI j * p.2.1⁻¹ * (p.2.2.1 * mI i * p.2.2.1⁻¹)) ^ p.2.2.2 * p.1⁻¹ ∧
      len (1 : G 0 r) = 2 * len p.1 + p.2.2.2 * (2 * len p.2.1 + 2 * len p.2.2.1 + 2)} :=
    ⟨fun ⟨p, ht, _, h⟩ => by
      rw [len_one] at h
      have h2 := Nat.mul_le_mul ht (show 2 ≤ 2 * len p.2.1 + 2 * len p.2.2.1 + 2 by omega)
      generalize p.2.2.2 * (2 * len p.2.1 + 2 * len p.2.2.1 + 2) = y at h h2
      omega⟩
  exact Nat.card_of_isEmpty

end RandomInvolutions.Dev.PartU2
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
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {r : ℕ}
lemma mem_CGL (u : List (Lt 0 r)) (c : Fin (u.length + 1) → Fin (u.length + 1)) :
    c ∈ CGL u ↔ canon c = c ∧ GoodL u c := by
  simp only [CGL, mem_filter, mem_univ, true_and]

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartU2
variable {r : ℕ}
theorem expFixK_one (N : ℕ) (κ : Fin r → ℕ) (hA : AdmK N κ) :
    expFixK r N κ (1 : G 0 r) = (N : ℝ) := by
  have := nonempty_omK N κ hA
  unfold expFixK expFixOn
  have h : ∀ τ : OmK r N κ, (fixCount (homK τ 1) : ℝ) = (N : ℝ) := by
    intro τ
    simp [fixCount]
  have hc : (Fintype.card (OmK r N κ) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [h, sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-! ## The coefficient functionals -/
/-- The zeroth-order moments. -/
def aa {D : ℕ} (z : MG D 0 r) (p : ℕ) : ℝ := (trTau (z ^ p)).re

/-- `φ ↦ (1/D) ∑_{g ≠ 1} Re tr((z^p)_g) φ(g)`. -/
def TT {D : ℕ} (z : MG D 0 r) (p : ℕ) : (G 0 r → ℝ) →ₗ[ℝ] ℝ where
  toFun φ := ∑ g ∈ (z ^ p).coeff.support,
    if g = 1 then 0 else (Matrix.trace ((z ^ p).coeff g)).re / D * φ g
  map_add' φ ψ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs
    · simp
    · simp only [Pi.add_apply]; ring
  map_smul' c φ := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs
    · simp
    · simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem TT_apply {D : ℕ} (z : MG D 0 r) (p : ℕ) (φ : G 0 r → ℝ) :
    TT z p φ = ∑ g ∈ (z ^ p).coeff.support,
      if g = 1 then 0 else (Matrix.trace ((z ^ p).coeff g)).re / D * φ g := rfl

theorem TT_eq_div {D : ℕ} (z : MG D 0 r) (p : ℕ) (φ : G 0 r → ℝ) :
    TT z p φ = (∑ g ∈ (z ^ p).coeff.support,
      if g = 1 then 0 else (Matrix.trace ((z ^ p).coeff g)).re * φ g) / D := by
  rw [TT_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs
  · simp
  · ring

theorem TT_eq_re {D : ℕ} (z : MG D 0 r) (p : ℕ) (φ : G 0 r → ℝ) :
    TT z p φ = (∑ g ∈ (z ^ p).coeff.support,
      (((if g = 1 then 0 else φ g : ℝ)) : ℂ) * Matrix.trace ((z ^ p).coeff g)).re / D := by
  rw [TT_eq_div, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Complex.re_ofReal_mul]
  split_ifs
  · simp
  · ring

theorem TT_tendsto {D : ℕ} (z : MG D 0 r) (p : ℕ) {ι : Type*} (l : Filter ι)
    (φ : ι → G 0 r → ℝ) (ψ : G 0 r → ℝ)
    (h : ∀ g, g ≠ 1 → Tendsto (fun n => φ n g) l (𝓝 (ψ g))) :
    Tendsto (fun n => TT z p (φ n)) l (𝓝 (TT z p ψ)) := by
  simp only [TT_apply]
  refine tendsto_finsetSum _ fun g _ => ?_
  by_cases hg : g = 1
  · simp only [hg, if_true]; exact tendsto_const_nhds
  · simp only [hg, if_false]
    exact (h g hg).const_mul _

/-- The indicator of `p = 0`. -/
def i0 (p : ℕ) : ℝ := if p = 0 then 1 else 0

/-- The `κ`-free first-order moments. -/
def AA {D : ℕ} (z : MG D 0 r) (p : ℕ) : ℝ :=
  TT z p (fun g => (cfun g : ℝ)) - aa z p + i0 p

/-- The single-loop moments. -/
def BB {D : ℕ} (z : MG D 0 r) (i : Fin r) (p : ℕ) : ℝ :=
  TT z p (fun g => (Bcount i g : ℝ))

/-- The two-loop moments. -/
def CC2 {D : ℕ} (z : MG D 0 r) (i j : Fin r) (p : ℕ) : ℝ :=
  TT z p (fun g => (C2count i j g : ℝ))

/-- The functional. -/
def EE {D : ℕ} (z : MG D 0 r) (κ : Fin r → ℕ) (N : ℕ) (f : ℝ → ℝ) : ℝ :=
  specE (fun τ : OmK r N κ => homK τ) z f

theorem aa_eq {D : ℕ} (z : MG D 0 r) (p : ℕ) :
    aa z p = (Matrix.trace ((z ^ p).coeff 1)).re / D := by
  unfold aa trTau
  have : ((D : ℂ))⁻¹ = (((D : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  ring

end RandomInvolutions.Dev.PartU2
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
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}

/-! ## The stubs -/
theorem nf_exists (r : ℕ) : ∃ nf : G 0 r → List (Lt 0 r),
    (∀ g, Red (nf g)) ∧ (∀ g, wprod (nf g) = g) ∧ (∀ u, Red u → nf (wprod u) = u) ∧
      ∀ g, len g = (nf g).length :=
  ⟨nf, red_nf, wprod_nf, nf_wprod', len_eq_length_nf⟩

end RandomInvolutions.Dev.PartF
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-!
# Strong convergence of uniform random involutions: Blueprint

Every statement here is a stub (`sorry`), except the small probability lemmas at the end and
the final theorem `ZigZagStrong.ZigZag.involution_strong_convergence_dev`, which is proved from
the stubs. NEVER EDIT this file. Each Part proves its stubs in its own file
`Solutions/RandomInvolutions.Dev/Part<X>*.lean`, restating them verbatim under `namespace RandomInvolutions.Dev.Part<X>`, and may use
every other stub of this file as given.

Route (see `~/claude/p2m-standalone/missions/inv-fable/PLAN.md` and `BRIEF.md`): condition on the
fixed-point counts `κ`; in the conditional model `M(N, κ)` expected fixed points are exact
rational functions of `N` (Part C2) whose expansion to second order (Parts W, K2) has
coefficients `T₀ = τ`, `T₁ = A + ∑ κᵢ Bᵢ`, `T₂ = C₀ + ∑ κᵢ C₁ᵢ + ∑ κᵢ κⱼ C₂ᵢⱼ`; the moments of
`A`, `Bᵢ`, `C₂ᵢⱼ` grow at most like `(‖regOp z‖ + δ)^p` (Part P3), so a second-order polynomial
method uniform along rays (Part A2) gives the upper tail `O(lam κ / N + lam κ³ / N²)` (Part U2);
mixing over `κ` with `E[#fix] ≤ √N + 1` gives the upper tail for uniform involutions (Part X);
the lower tail (Part L2) and the core theorem (Part T2) follow as in Bordenave–Collins, and the
bridge (Part B) transports to the ZigZag encoding.
-/
/-! ## Part F: normal forms in `Γ_r = G 0 r` and the coefficient counts on special elements -/
alias nf_exists := RandomInvolutions.Dev.PartF.nf_exists

end RandomInvolutions.Dev
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
namespace RandomInvolutions.Dev.PartC2
variable {r : ℕ}
/-! ## Bounds on the invariants of a good colouring -/
/-- In a good closed colouring, the loops and pairs of one colour occupy at most `u.length`
vertices. -/
lemma card_le_length (u : List (Lt 0 r)) (c : Fin (u.length + 1) → Fin (u.length + 1))
    (hg : GoodL u c) (i : Fin r) : fK u c i + 2 * eK u c i ≤ u.length := by
  unfold fK eK
  rw [← card_union_supp _ _ (hg.1 i) (hg.2.1 i)]
  have hsub : Ls u c i ∪ supp (Ps u c i) ⊆
      (univ : Finset (Fin u.length)).image fun t => c t.castSucc := by
    have hsucc : ∀ t : Fin u.length, ∃ t' : Fin u.length, c t'.castSucc = c t.succ := by
      intro t
      by_cases h : t.val + 1 < u.length
      · exact ⟨⟨t.val + 1, h⟩, congrArg c (Fin.ext rfl)⟩
      · refine ⟨⟨0, by have := t.2; omega⟩, ?_⟩
        have h1 : t.succ = Fin.last _ := Fin.ext (by have := t.2; simp only [Fin.val_succ, Fin.val_last]; omega)
        have h2 : (⟨0, by have := t.2; omega⟩ : Fin u.length).castSucc = 0 := Fin.ext rfl
        rw [h1, h2, hg.2.2]
    intro a ha
    rcases mem_union.1 ha with ha | ha
    · obtain ⟨t, -, rfl⟩ := mem_image.1 ha
      exact mem_image_of_mem _ (mem_univ _)
    · obtain ⟨y, hy⟩ := (mem_supp _ a).1 ha
      obtain ⟨t, -, e⟩ := mem_image.1 hy
      rcases Sym2.eq_iff.1 e with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact mem_image_of_mem _ (mem_univ _)
      · obtain ⟨t', ht'⟩ := hsucc t
        rw [← ht']
        exact mem_image_of_mem _ (mem_univ _)
  calc (Ls u c i ∪ supp (Ps u c i)).card
      ≤ ((univ : Finset (Fin u.length)).image fun t => c t.castSucc).card := card_le_card hsub
    _ ≤ (univ : Finset (Fin u.length)).card := card_image_le
    _ = u.length := by rw [card_univ, Fintype.card_fin]

/-! ## The polynomials -/
/-- `1 - a X`. -/
def lin (a : ℝ) : ℝ[X] := 1 - C a * X

lemma natDegree_lin (a : ℝ) : (lin a).natDegree ≤ 1 :=
  (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))

lemma eval_lin (a x : ℝ) : (lin a).eval x = 1 - a * x := by simp [lin]

lemma natDegree_prod_lin (S : Finset ℕ) (a : ℕ → ℝ) :
    (∏ l ∈ S, lin (a l)).natDegree ≤ S.card :=
  (natDegree_prod_le _ _).trans ((sum_le_sum fun l _ => natDegree_lin _).trans (by simp))

/-- `∏_{l<k} (1 - l X)`. -/
def PA (k : ℕ) : ℝ[X] := ∏ l ∈ range k, lin (l : ℝ)

/-- `∏_{k≤l<q} (1 - l X)`. -/
def PA' (k q : ℕ) : ℝ[X] := ∏ l ∈ Ico k q, lin (l : ℝ)

/-- `∏_{l<e} (1 - (κ + 2l) X)`. -/
def PK (κ e : ℕ) : ℝ[X] := ∏ l ∈ range e, lin ((κ : ℝ) + 2 * l)

lemma PA_mul (k q : ℕ) (h : k ≤ q) : PA k * PA' k q = PA q :=
  prod_range_mul_prod_Ico _ h

lemma eval_PA (k : ℕ) (x : ℝ) : (PA k).eval x = ∏ l ∈ range k, (1 - (l : ℝ) * x) := by
  simp [PA, eval_prod, eval_lin]

lemma eval_PK (κ e : ℕ) (x : ℝ) :
    (PK κ e).eval x = ∏ l ∈ range e, (1 - ((κ : ℝ) + 2 * l) * x) := by
  simp [PK, eval_prod, eval_lin]

lemma natDegree_PA (k : ℕ) : (PA k).natDegree ≤ k := by
  have := natDegree_prod_lin (range k) (fun l => (l : ℝ))
  rwa [card_range] at this

lemma natDegree_PA' (k q : ℕ) : (PA' k q).natDegree ≤ q - k := by
  have := natDegree_prod_lin (Ico k q) (fun l => (l : ℝ))
  rwa [Nat.card_Ico] at this

lemma natDegree_PK (κ e : ℕ) : (PK κ e).natDegree ≤ e := by
  have := natDegree_prod_lin (range e) (fun l => (κ : ℝ) + 2 * l)
  rwa [card_range] at this

lemma desc_eq (N k : ℕ) (hN : 1 ≤ N) :
    (N.descFactorial k : ℝ) = (N : ℝ) ^ k * (PA k).eval (1 / (N : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [eval_PA]
  rcases Nat.lt_or_ge N k with h | h
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 h, prod_eq_zero (mem_range.2 h), mul_zero]
    · simp
    · field_simp; simp
  · rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod,
      show (N : ℝ) ^ k = ∏ _l ∈ range k, (N : ℝ) by simp, ← prod_mul_distrib]
    refine prod_congr rfl fun l hl => ?_
    have := mem_range.1 hl
    rw [Nat.cast_sub (by omega)]
    field_simp

lemma pair_eq (N κ e : ℕ) (hN : 1 ≤ N) :
    ∏ l ∈ range e, ((N : ℝ) - κ - 2 * l) = (N : ℝ) ^ e * (PK κ e).eval (1 / (N : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [eval_PK, show (N : ℝ) ^ e = ∏ _l ∈ range e, (N : ℝ) by simp, ← prod_mul_distrib]
  refine prod_congr rfl fun l _ => ?_
  field_simp
  ring

lemma PA_ne (N q : ℕ) (hN : 1 ≤ N) (hq : q ≤ N) : (PA q).eval (1 / (N : ℝ)) ≠ 0 := by
  intro h
  have := desc_eq N q hN
  rw [h, mul_zero, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt] at this
  omega

lemma gq_bounds (r q : ℕ) (hq : 1 ≤ q) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) (1 / (4 * ((r : ℝ) + 1) * (q : ℝ) ^ 2))) :
    1 / 2 ≤ ((PA q) ^ r).eval x ∧ ((PA q) ^ r).eval x ≤ 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hR : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  set δ : ℝ := 1 / (2 * ((r : ℝ) + 1) * q) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have h2 : 2 * (q : ℝ) * x ≤ δ := by
    calc 2 * (q : ℝ) * x ≤ 2 * q * (1 / (4 * ((r : ℝ) + 1) * (q : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hx1 (by positivity)
      _ = δ := by rw [hδ]; field_simp; ring
  have hnδ : ((q * r : ℕ) : ℝ) * δ ≤ 1 / 2 := by
    rw [hδ, mul_one_div, div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    nlinarith
  have h1δ : 0 ≤ 1 - δ := by linarith
  have hA : (1 - δ) ^ q ≤ (PA q).eval x ∧ (PA q).eval x ≤ 1 := by
    rw [eval_PA]
    have hl : ∀ l ∈ range q, 1 - δ ≤ 1 - (l : ℝ) * x ∧ 1 - (l : ℝ) * x ≤ 1 := by
      intro l hl
      have hlq : (l : ℝ) < q := by exact_mod_cast mem_range.1 hl
      have hl0 : (0 : ℝ) ≤ l := by positivity
      constructor
      · nlinarith [mul_le_mul_of_nonneg_right hlq.le hx0]
      · nlinarith [mul_nonneg hl0 hx0]
    constructor
    · calc (1 - δ) ^ q = ∏ _l ∈ range q, (1 - δ) := by simp
        _ ≤ _ := prod_le_prod (fun _ _ => h1δ) (fun l hl' => (hl l hl').1)
    · exact prod_le_one (fun l hl' => h1δ.trans (hl l hl').1) (fun l hl' => (hl l hl').2)
  have hp : 0 ≤ (1 - δ) ^ q := pow_nonneg h1δ _
  rw [eval_pow]
  constructor
  · have hb := one_add_mul_le_pow (a := -δ) (by linarith) (q * r)
    calc (1 : ℝ) / 2 ≤ 1 + ((q * r : ℕ) : ℝ) * (-δ) := by linarith
      _ ≤ (1 + -δ) ^ (q * r) := hb
      _ = ((1 - δ) ^ q) ^ r := by rw [← sub_eq_add_neg, pow_mul]
      _ ≤ _ := pow_le_pow_left₀ hp hA.1 _
  · exact pow_le_one₀ (hp.trans hA.1) hA.2

/-! ## The polynomial of a colouring -/
/-- The numerator polynomial of a colouring (for the common denominator `PA q ^ r`). -/
def fpoly (u : List (Lt 0 r)) (q : ℕ) (κ : Fin r → ℕ)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℝ[X] :=
  X ^ (Ecount u c + Fcount u c + 1 - nv c) * PA (nv c) *
    ∏ i, (C ((κ i).descFactorial (fK u c i) : ℝ) * PK (κ i) (eK u c i) *
      PA' (fK u c i + 2 * eK u c i) q)

end RandomInvolutions.Dev.PartC2
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

theorem norm_inject_apply {n : ℕ} (i : Fin n) (y : H) :
    ‖(inject i : H →L[ℂ] Composite (Fin n) H) y‖ = ‖y‖ := by
  simp [inject]

theorem norm_tensorOp_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    ‖tensorOp A T‖ ≤ (∑ a, ∑ b, ‖A a b‖) * ‖T‖ := by
  have key : ∀ i j : Fin n,
      ‖(inject i ∘L (A i j • T) ∘L PiLp.proj 2 (fun _ : Fin n => H) j :
        Composite (Fin n) H →L[ℂ] Composite (Fin n) H)‖ ≤ ‖A i j‖ * ‖T‖ := by
    intro i j
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      fun x => ?_
    have h1 : ‖(inject i ∘L (A i j • T) ∘L PiLp.proj 2 (fun _ : Fin n => H) j :
        Composite (Fin n) H →L[ℂ] Composite (Fin n) H) x‖ = ‖A i j • T (x j)‖ := by
      rw [← norm_inject_apply (n := n) i (A i j • T (x j))]
      rfl
    rw [h1, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((T.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (norm_nonneg _))) (norm_nonneg _)
  have e : tensorOp A T = ∑ i, ∑ j, (inject i ∘L (A i j • T) ∘L PiLp.proj 2 (fun _ : Fin n => H) j :
        Composite (Fin n) H →L[ℂ] Composite (Fin n) H) := rfl
  rw [e, Finset.sum_mul]
  refine norm_sum_le_of_le (E := Composite (Fin n) H →L[ℂ] Composite (Fin n) H) Finset.univ
    fun i _ => ?_
  rw [Finset.sum_mul]
  exact norm_sum_le_of_le (E := Composite (Fin n) H →L[ℂ] Composite (Fin n) H) Finset.univ
    fun j _ => key i j

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

/-- A self-adjoint idempotent has norm at most one. -/
theorem norm_le_one_of_proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (P : E →L[ℂ] E) (h1 : P * P = P) (h2 : star P = P) : ‖P‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  have e : inner ℂ (P x) (P x) = inner ℂ x (P x) := by
    rw [← ContinuousLinearMap.adjoint_inner_right P, ← ContinuousLinearMap.star_eq_adjoint, h2,
      ← mul_apply_eq_comp, h1]
  have h : ‖P x‖ * ‖P x‖ ≤ ‖x‖ * ‖P x‖ := by
    have := re_inner_le_norm (𝕜 := ℂ) x (P x)
    rw [← e, inner_self_eq_norm_sq_to_K] at this
    have h3 : (((‖P x‖ : ℝ) : ℂ) ^ 2).re = ‖P x‖ * ‖P x‖ := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re, sq]
    simpa [h3] using this
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg (P x), norm_nonneg x]

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

theorem norm_permOp_le {N : ℕ} (π : Equiv.Perm (Fin N)) : ‖permOp π‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact le_of_eq (LinearIsometryEquiv.norm_map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ π) x)

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
theorem leftReg_apply {Γ : Type*} [Group Γ] (g : Γ) (f : L2 Γ) (h : Γ) :
    leftReg g f h = f (g⁻¹ * h) := rfl

theorem leftReg_mul {Γ : Type*} [Group Γ] (g h : Γ) :
    leftReg (g * h) = leftReg g * leftReg h := by
  ext f k
  simp [leftReg_apply, mul_assoc]

theorem leftReg_one {Γ : Type*} [Group Γ] : leftReg (1 : Γ) = 1 := by
  ext f k
  simp [leftReg_apply]

/-- The left regular representation as a monoid homomorphism into operators. -/
def regHom (Γ : Type*) [Group Γ] : Γ →* (L2 Γ →L[ℂ] L2 Γ) where
  toFun g := leftReg g
  map_one' := leftReg_one
  map_mul' := leftReg_mul

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

theorem norm_QQ_le (D N : ℕ) : ‖QQ D N‖ ≤ 1 :=
  norm_le_one_of_proj _ (QQ_mul_self D N) (star_QQ D N)

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
open Finset BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartO
open AccessibleMaps
open DerandSq
variable {r s D : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem opOf_pow (π : G r s →* (H →L[ℂ] H)) (x : MG D r s) (p : ℕ) :
    opOf (fun g => π g) (x ^ p) = opOf (fun g => π g) x ^ p := by
  induction p with
  | zero => rw [pow_zero, pow_zero, opOf_one']
  | succ p ih => rw [pow_succ, pow_succ, opOf_mul', ih]

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

theorem norm_mOp_le {D N : ℕ} (π : G 0 r →* Equiv.Perm (Fin N)) (x : MG D 0 r) : ‖mOp π x‖ ≤ bnd x := by
  unfold mOp opOf bnd
  refine norm_sum_le_of_le (E := Op D N) _ fun g _ => ?_
  refine (norm_tensorOp_le _ _).trans ?_
  exact mul_le_of_le_one_right
    (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _) (norm_permOp_le _)

theorem norm_perpOp_le {D N : ℕ} (π : G 0 r →* Equiv.Perm (Fin N)) (x : MG D 0 r) : ‖perpOp π x‖ ≤ bnd x := by
  rw [perpOp_eq]
  have h1 : ‖(mOp π x * QQ D N : Op D N)‖ ≤ bnd x := by
    refine (norm_mul_le (α := Op D N) _ _).trans ?_
    calc ‖mOp π x‖ * ‖QQ D N‖ ≤ bnd x * 1 :=
          mul_le_mul (norm_mOp_le π x) (norm_QQ_le D N) (norm_nonneg _)
            ((norm_nonneg _).trans (norm_mOp_le π x))
      _ = bnd x := mul_one _
  refine (norm_mul_le (α := Op D N) _ _).trans ?_
  calc ‖QQ D N‖ * ‖(mOp π x * QQ D N : Op D N)‖ ≤ 1 * bnd x :=
        mul_le_mul (norm_QQ_le D N) h1 (norm_nonneg _) zero_le_one
    _ = bnd x := one_mul _

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
/-- `e_b ⊗ δ_1`. -/
def dvec (D r : ℕ) (b : Fin D) : PiLp 2 (fun _ : Fin D => L2 (G 0 r)) :=
  inject b (lp.single 2 (1 : G 0 r) (1 : ℂ))

theorem norm_dvec {D : ℕ} (b : Fin D) : ‖dvec D r b‖ = 1 := by
  unfold dvec
  rw [norm_inject_apply, lp.norm_single (by norm_num)]
  simp

/-- The coefficient at the identity as a matrix entry of the regular representation. -/
theorem regOp_dvec {D : ℕ} (y : MG D 0 r) (a b : Fin D) :
    (regOp y (dvec D r b)) a (1 : G 0 r) = y.coeff 1 a b := by
  have h : ∀ g : G 0 r, ((tensorOp (y.coeff g) (leftReg g)) (dvec D r b)) a (1 : G 0 r) =
      if g = 1 then y.coeff g a b else 0 := by
    intro g
    rw [tensorOp_apply]
    have hv : ∀ b' : Fin D, (dvec D r b) b' =
        if b' = b then lp.single 2 (1 : G 0 r) (1 : ℂ) else 0 := by
      intro b'
      simp [dvec, inject]
    simp only [hv, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
    rw [Finset.sum_eq_single b]
    · simp [leftReg_apply, lp.single_apply, Pi.single_apply]
    · intro b' _ hb'
      simp [hb']
    · simp
  unfold regOp opOf
  rw [_root_.sum_apply, WithLp.ofLp_sum, Finset.sum_apply, lp.coeFn_sum,
    Finset.sum_apply]
  simp only [h]
  rw [Finset.sum_ite_eq']
  split_ifs with h1
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h1]; rfl

theorem norm_trTau_le {D : ℕ} (y : MG D 0 r) : ‖trTau y‖ ≤ ‖regOp y‖ := by
  have hentry : ∀ a : Fin D, ‖y.coeff 1 a a‖ ≤ ‖regOp y‖ := by
    intro a
    rw [← regOp_dvec y a a]
    calc ‖(regOp y (dvec D r a)) a (1 : G 0 r)‖ ≤ ‖(regOp y (dvec D r a)) a‖ :=
          lp.norm_apply_le_norm (by norm_num) _ _
      _ ≤ ‖regOp y (dvec D r a)‖ := PiLp.norm_apply_le _ a
      _ ≤ ‖regOp y‖ * ‖dvec D r a‖ := (regOp y).le_opNorm _
      _ = ‖regOp y‖ := by rw [norm_dvec, mul_one]
  unfold trTau
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have : ‖Matrix.trace (y.coeff 1)‖ ≤ D * ‖regOp y‖ := by
    unfold Matrix.trace
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => hentry a).trans ?_
    simp
  rw [inv_mul_le_iff₀ hD']
  exact this

theorem regOp_pow {D : ℕ} (z : MG D 0 r) (p : ℕ) : regOp (z ^ p) = regOp z ^ p :=
  opOf_pow (regHom (G 0 r)) z p

theorem norm_pow_le_op {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X : E →L[ℂ] E)
    (p : ℕ) : ‖X ^ p‖ ≤ ‖X‖ ^ p := by
  induction p with
  | zero => rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  | succ p ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

theorem trTau_pow_le {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (p : ℕ) :
    ‖trTau (z ^ p)‖ ≤ ‖regOp z‖ ^ p := by
  refine (norm_trTau_le (z ^ p)).trans ?_
  rw [regOp_pow]
  exact norm_pow_le_op _ p

/-! ## Word length of the support of a polynomial -/
theorem len_one : len (1 : G 0 r) = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl ⟨[], rfl, by simp [wprod]⟩)

theorem len_mul_le (g h : G 0 r) : len (g * h) ≤ len g + len h := by
  obtain ⟨nf, -, h2, -, h4⟩ := RandomInvolutions.Dev.nf_exists r
  rw [h4 g, h4 h]
  refine Nat.sInf_le ⟨nf g ++ nf h, List.length_append, ?_⟩
  rw [wprod, List.map_append, List.prod_append]
  exact congrArg₂ (· * ·) (h2 g) (h2 h)

theorem len_support_pow {D : ℕ} (z : MG D 0 r) (k : ℕ) (g : G 0 r)
    (hg : g ∈ (z ^ k).coeff.support) : len g ≤ k * lenmax z := by
  induction k generalizing g with
  | zero =>
    have := MonoidAlgebra.support_coeff_one_subset (by rwa [pow_zero] at hg)
    rw [Finset.mem_one] at this
    rw [this, len_one]; simp
  | succ k ih =>
    rw [pow_succ] at hg
    have := MonoidAlgebra.support_coeff_mul_subset _ _ hg
    obtain ⟨g₁, h₁, g₂, h₂, rfl⟩ := Finset.mem_mul.mp this
    have hb : len g₂ ≤ lenmax z := Finset.le_sup (f := len) h₂
    calc len (g₁ * g₂) ≤ len g₁ + len g₂ := len_mul_le _ _
      _ ≤ k * lenmax z + lenmax z := add_le_add (ih g₁ h₁) hb
      _ = (k + 1) * lenmax z := by ring

theorem len_support_aeval {D : ℕ} (z : MG D 0 r) (h : ℝ[X]) (g : G 0 r)
    (hg : g ∈ (Polynomial.aeval z h).coeff.support) : len g ≤ h.natDegree * lenmax z := by
  rw [Polynomial.aeval_eq_sum_range, MonoidAlgebra.coeff_sum] at hg
  have := Finsupp.support_finsetSum hg
  obtain ⟨k, hk, hgk⟩ := Finset.mem_biUnion.mp this
  rw [MonoidAlgebra.coeff_smul] at hgk
  have hgk' := Finsupp.support_smul hgk
  have hk' : k ≤ h.natDegree := by
    have := Finset.mem_range.mp hk
    omega
  exact (len_support_pow z k g hgk').trans (Nat.mul_le_mul_right _ hk')

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias len_support_aeval := RandomInvolutions.Dev.PartO.len_support_aeval

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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
/-! # The spectral functional -/
/-! ## Generic facts on a finite-dimensional Hilbert space -/
/-- A real function applied to an operator (complex functional calculus of `w ↦ f (re w)`). -/
def fc (f : ℝ → ℝ) (Y : V →L[ℂ] V) : V →L[ℂ] V :=
  cfc (fun w : ℂ => ((f w.re : ℝ) : ℂ)) Y

/-- The trace as a linear functional on bounded operators. -/
def trL : (V →L[ℂ] V) →ₗ[ℂ] ℂ := (LinearMap.trace ℂ V) ∘ₗ (ContinuousLinearMap.coeLM ℂ)

/-- The real part of the trace. -/
def trR (T : V →L[ℂ] V) : ℝ := (trL T).re

lemma trR_def (T : V →L[ℂ] V) :
    trR T = (LinearMap.trace ℂ V (T : V →ₗ[ℂ] V)).re := rfl

lemma trR_add (A B : V →L[ℂ] V) : trR (A + B) = trR A + trR B := by
  unfold trR; rw [map_add, Complex.add_re]

lemma trR_sub (A B : V →L[ℂ] V) : trR (A - B) = trR A - trR B := by
  unfold trR; rw [map_sub, Complex.sub_re]

lemma trR_smul (c : ℝ) (A : V →L[ℂ] V) : trR ((c : ℂ) • A) = c * trR A := by
  unfold trR; rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma trL_one : trL (1 : V →L[ℂ] V) = (Module.finrank ℂ V : ℂ) := by
  show LinearMap.trace ℂ V (1 : V →ₗ[ℂ] V) = _
  exact LinearMap.trace_one ℂ V

lemma contOn (Y : V →L[ℂ] V) (F : ℂ → ℂ) : ContinuousOn F (spectrum ℂ Y) := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact (Module.End.finite_spectrum _).continuousOn F

lemma fc_add (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) (f g : ℝ → ℝ) :
    fc (f + g) Y = fc f Y + fc g Y := by
  have := hY.isStarNormal
  unfold fc
  rw [← cfc_add (a := Y) (fun w : ℂ => ((f w.re : ℝ) : ℂ)) (fun w : ℂ => ((g w.re : ℝ) : ℂ))
    (contOn Y _) (contOn Y _)]
  apply cfc_congr
  intro w _
  simp

lemma fc_smul (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) (a : ℝ) (f : ℝ → ℝ) :
    fc (a • f) Y = (a : ℂ) • fc f Y := by
  have := hY.isStarNormal
  unfold fc
  rw [← cfc_const_mul (a : ℂ) (fun w : ℂ => ((f w.re : ℝ) : ℂ)) Y (contOn Y _)]
  apply cfc_congr
  intro w _
  simp

lemma mem_spec (Y : V →L[ℂ] V) (_hY : IsSelfAdjoint Y) {K : ℝ} (hK : ‖Y‖ ≤ K) {w : ℂ}
    (hw : w ∈ spectrum ℂ Y) : w.re ∈ Set.Icc (-K) K := by
  rcases subsingleton_or_nontrivial (V →L[ℂ] V) with hA | hA
  · exact absurd hw (by rw [spectrum.of_subsingleton]; exact Set.notMem_empty _)
  have hn : ‖w‖ ≤ ‖Y‖ := spectrum.norm_le_norm_of_mem hw
  have h1 : |w.re| ≤ K := (Complex.abs_re_le_norm w).trans (hn.trans hK)
  exact ⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩

lemma fc_mono (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) {K : ℝ} (hK : ‖Y‖ ≤ K) (f g : ℝ → ℝ)
    (hfg : ∀ x ∈ Set.Icc (-K) K, f x ≤ g x) : fc f Y ≤ fc g Y := by
  unfold fc
  refine cfc_mono (fun w hw => ?_) (contOn Y _) (contOn Y _)
  exact Complex.real_le_real.mpr (hfg _ (mem_spec Y hY hK hw))

lemma trR_nonneg (T : V →L[ℂ] V) (hT : 0 ≤ T) : 0 ≤ trR T := by
  have hp : (T : V →ₗ[ℂ] V).IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff T).mpr
      ((ContinuousLinearMap.nonneg_iff_isPositive T).mp hT)
  exact (Complex.nonneg_iff.mp hp.trace_nonneg).1

lemma trR_fc_mono (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) {K : ℝ} (hK : ‖Y‖ ≤ K) (f g : ℝ → ℝ)
    (hfg : ∀ x ∈ Set.Icc (-K) K, f x ≤ g x) : trR (fc f Y) ≤ trR (fc g Y) := by
  have h := trR_nonneg _ (sub_nonneg.mpr (fc_mono Y hY hK f g hfg))
  rw [trR_sub] at h
  linarith

lemma fc_const_one (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) : fc (fun _ => 1) Y = 1 := by
  have := hY.isStarNormal
  unfold fc
  simpa using cfc_const_one ℂ Y

lemma fc_nonneg (Y : V →L[ℂ] V) (f : ℝ → ℝ) (h0 : ∀ x, 0 ≤ f x) : 0 ≤ fc f Y := by
  unfold fc
  exact cfc_nonneg (fun x _ => Complex.zero_le_real.mpr (h0 _))

lemma fc_poly (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) (h : ℝ[X]) :
    fc (fun x => h.eval x) Y =
      ∑ k ∈ Finset.range (h.natDegree + 1), (h.coeff k : ℂ) • Y ^ k := by
  have := hY.isStarNormal
  unfold fc
  have : cfc (fun z : ℂ => ((h.eval z.re : ℝ) : ℂ)) Y =
      cfc (fun z : ℂ => (h.map (algebraMap ℝ ℂ)).eval z) Y := by
    apply cfc_congr
    intro z hz
    have := hY.mem_spectrum_eq_re hz
    simp only
    conv_rhs => rw [this]
    simp [Polynomial.eval_map, ← Complex.coe_algebraMap, Polynomial.eval₂_at_apply]
  rw [this, cfc_polynomial (h.map (algebraMap ℝ ℂ)) Y, aeval_eq_sum_range, natDegree_map]
  simp [coeff_map]

/-- If `c ≤ ‖Y‖` then the spectral projection of `{|x| ≥ c}` has trace at least one. -/
lemma trR_ge_one [Nontrivial V] (Y : V →L[ℂ] V) (hY : IsSelfAdjoint Y) (c : ℝ)
    (hcY : c ≤ ‖Y‖) : 1 ≤ trR (fc (fun t => if c ≤ |t| then 1 else 0) Y) := by
  have := hY.isStarNormal
  set χ : ℝ → ℝ := fun t => if c ≤ |t| then 1 else 0 with hχ
  have h0 : ∀ x, 0 ≤ χ x := fun x => by simp only [hχ]; split_ifs <;> norm_num
  obtain ⟨l, hl, hn⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
    (spectrum.nonempty Y)
  rw [hY.spectralRadius_eq_nnnorm] at hn
  have hnorm : ‖l‖ = ‖Y‖ := by
    have := congrArg ENNReal.toReal hn
    simpa using this
  have hre : (l.re : ℂ) = l := (hY.mem_spectrum_eq_re hl).symm
  have habs : c ≤ |l.re| := by
    have h2 : ‖l‖ = |l.re| := by
      conv_lhs => rw [← hre]
      exact Complex.norm_real _
    linarith
  set T := fc χ Y with hTdef
  have hT0 : 0 ≤ T := fc_nonneg Y χ h0
  have hmem : (1 : ℂ) ∈ spectrum ℂ T := by
    rw [hTdef, fc, cfc_map_spectrum (hf := contOn Y _) _ Y]
    exact ⟨l, hl, by simp [hχ, habs]⟩
  have hp : (T : V →ₗ[ℂ] V).IsPositive :=
    (ContinuousLinearMap.isPositive_toLinearMap_iff T).mpr
      ((ContinuousLinearMap.nonneg_iff_isPositive T).mp hT0)
  rw [ContinuousLinearMap.spectrum_eq, ← Module.End.hasEigenvalue_iff_mem_spectrum] at hmem
  obtain ⟨i, hi⟩ := hp.isSymmetric.exists_eigenvalues_eq rfl hmem
  rw [trR_def, ← RCLike.re_to_complex, hp.isSymmetric.re_trace_eq_sum_eigenvalues rfl]
  calc (1:ℝ) = hp.isSymmetric.eigenvalues rfl i := (Complex.ofReal_eq_one.mp hi).symm
    _ ≤ _ := Finset.single_le_sum (fun j _ => hp.nonneg_eigenvalues rfl j) (Finset.mem_univ i)

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
/-! ## The model space -/
lemma finrank_space (D N : ℕ) :
    Module.finrank ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) = D * N := by
  rw [(WithLp.linearEquiv 2 ℂ (Fin D → EuclideanSpace ℂ (Fin N))).finrank_eq,
    Module.finrank_pi_fintype]
  simp

lemma nontrivial_space {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) :
    Nontrivial (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin N))) := by
  apply Module.nontrivial_of_finrank_pos (R := ℂ)
  rw [finrank_space]
  positivity

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
variable {Ω : Type*} [Fintype Ω]
lemma specE_eq {D N : ℕ} (act : Ω → G 0 r →* Equiv.Perm (Fin N)) (z : MG D 0 r) (f : ℝ → ℝ) :
    specE act z f = (∑ ω : Ω, trR (fc f (perpOp (act ω) z))) /
      ((Fintype.card Ω : ℝ) * ((D : ℝ) * N)) := rfl

lemma sa {D N : ℕ} (z : MG D 0 r) (hz : adj z = z) (π : G 0 r →* Equiv.Perm (Fin N)) :
    IsSelfAdjoint (perpOp π z) := by
  unfold IsSelfAdjoint
  rw [star_perpOp, hz]

/-! ## Linearity, positivity, mass -/
theorem specE_add {D N : ℕ} (act : Ω → G 0 r →* Equiv.Perm (Fin N)) (z : MG D 0 r)
    (hz : adj z = z) (f g : ℝ → ℝ) :
    specE act z (f + g) = specE act z f + specE act z g := by
  rw [specE_eq, specE_eq, specE_eq, ← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [fc_add _ (sa z hz (act ω)), trR_add]

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
variable {Ω : Type*} [Fintype Ω]
alias specE_add := RandomInvolutions.Dev.PartO.specE_add

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
variable {Ω : Type*} [Fintype Ω]
theorem specE_smul {D N : ℕ} (act : Ω → G 0 r →* Equiv.Perm (Fin N)) (z : MG D 0 r)
    (hz : adj z = z) (a : ℝ) (f : ℝ → ℝ) :
    specE act z (a • f) = a * specE act z f := by
  rw [specE_eq, specE_eq, mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [fc_smul _ (sa z hz (act ω)), trR_smul]

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
variable {Ω : Type*} [Fintype Ω]
alias specE_smul := RandomInvolutions.Dev.PartO.specE_smul

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
variable {Ω : Type*} [Fintype Ω]
theorem specE_mono {D N : ℕ} (act : Ω → G 0 r →* Equiv.Perm (Fin N)) (z : MG D 0 r)
    (hz : adj z = z) (f g : ℝ → ℝ) (hfg : ∀ x ∈ Set.Icc (-(bnd z)) (bnd z), f x ≤ g x) :
    specE act z f ≤ specE act z g := by
  rw [specE_eq, specE_eq]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => ?_) (by positivity)
  exact trR_fc_mono _ (sa z hz (act ω)) (norm_perpOp_le (act ω) z) f g hfg

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
variable {Ω : Type*} [Fintype Ω]
alias specE_mono := RandomInvolutions.Dev.PartO.specE_mono

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
variable {Ω : Type*} [Fintype Ω]
theorem specE_one_le {D N : ℕ} (act : Ω → G 0 r →* Equiv.Perm (Fin N)) (z : MG D 0 r)
    (hz : adj z = z) :
    specE act z (fun _ => 1) ≤ 1 := by
  rw [specE_eq]
  have h : ∀ ω : Ω, trR (fc (fun _ => 1) (perpOp (act ω) z)) = (D : ℝ) * N := by
    intro ω
    rw [fc_const_one _ (sa z hz (act ω)), trR, trL_one, finrank_space]
    simp
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact div_self_le_one _

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
variable {Ω : Type*} [Fintype Ω]
alias specE_one_le := RandomInvolutions.Dev.PartO.specE_one_le

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
/-! ## Polynomial moments -/
/-- `y ↦ ∑_g tr(y_g) c_g`. -/
def Lf {D : ℕ} (c : G 0 r → ℂ) (y : MG D 0 r) : ℂ :=
  ∑ g ∈ y.coeff.support, Matrix.trace (y.coeff g) * c g

lemma Lf_eq {D : ℕ} (c : G 0 r → ℂ) (y : MG D 0 r) :
    Lf c y = y.coeff.sum fun g A => Matrix.trace A * c g := rfl

/-- `Lf` as a real-linear map. -/
def LfL {D : ℕ} (c : G 0 r → ℂ) : MG D 0 r →ₗ[ℝ] ℂ where
  toFun := Lf c
  map_add' x y := by
    rw [Lf_eq, Lf_eq, Lf_eq, MonoidAlgebra.coeff_add]
    exact Finsupp.sum_add_index' (by simp) (by intro g A B; simp [add_mul])
  map_smul' a y := by
    rw [Lf_eq, Lf_eq, MonoidAlgebra.coeff_smul, Finsupp.sum_smul_index' (by simp)]
    simp only [Finsupp.sum, Matrix.trace_smul, RingHom.id_apply, Finset.smul_sum, smul_mul_assoc]

lemma Lf_one {D : ℕ} (c : G 0 r → ℂ) : Lf c (1 : MG D 0 r) = (D : ℂ) * c 1 := by
  rw [Lf_eq, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single,
    Finsupp.sum_single_index (by simp)]
  simp

lemma Lf_re {D N : ℕ} (π : G 0 r →* Equiv.Perm (Fin N)) (y : MG D 0 r) :
    (Lf (fun g => (fixCount (π g) : ℂ) - 1) y).re =
      ∑ g ∈ y.coeff.support, (Matrix.trace (y.coeff g)).re * ((fixCount (π g) : ℝ) - 1) := by
  unfold Lf
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [Complex.mul_re]

lemma perpOp_pow {D N : ℕ} (hN : 1 ≤ N) (π : G 0 r →* Equiv.Perm (Fin N)) (z : MG D 0 r) (k : ℕ) :
    (perpOp π z) ^ (k + 1) = perpOp π (z ^ (k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, pow_succ z (k + 1), perpOp_mul hN]

lemma trL_pow {D N : ℕ} (hN : 1 ≤ N) (π : G 0 r →* Equiv.Perm (Fin N)) (z : MG D 0 r) (k : ℕ) :
    trL ((perpOp π z) ^ k) =
      Lf (fun g => (fixCount (π g) : ℂ) - 1) (z ^ k) + if k = 0 then (D : ℂ) else 0 := by
  cases k with
  | zero =>
    rw [pow_zero, pow_zero, trL_one, finrank_space, Lf_one]
    have : fixCount (π (1 : G 0 r)) = N := by simp [fixCount]
    rw [this, if_pos rfl]
    push_cast
    ring
  | succ k =>
    rw [perpOp_pow hN]
    simp only [Nat.succ_ne_zero, if_false, add_zero]
    exact trace_perpOp hN π (z ^ (k + 1))

lemma trR_poly {D N : ℕ} (hN : 1 ≤ N) (π : G 0 r →* Equiv.Perm (Fin N)) (z : MG D 0 r) (hz : adj z = z)
    (h : ℝ[X]) :
    trR (fc (fun t => h.eval t) (perpOp π z)) =
      ∑ g ∈ (Polynomial.aeval z h).coeff.support,
        (Matrix.trace ((Polynomial.aeval z h).coeff g)).re * ((fixCount (π g) : ℝ) - 1) +
      (D : ℝ) * h.eval 0 := by
  rw [← Lf_re, fc_poly _ (sa z hz π), trR, map_sum]
  simp only [map_smul, trL_pow hN, smul_add, Finset.sum_add_distrib]
  have h1 : ∑ k ∈ Finset.range (h.natDegree + 1),
      (h.coeff k : ℂ) • (if k = 0 then (D : ℂ) else 0) = ((D : ℝ) * h.eval 0 : ℝ) := by
    rw [Finset.sum_eq_single 0 (by intro b _ hb; simp [hb]) (by simp)]
    simp [Polynomial.coeff_zero_eq_eval_zero, mul_comm]
  have h2 : ∑ k ∈ Finset.range (h.natDegree + 1),
      (h.coeff k : ℂ) • Lf (fun g => (fixCount (π g) : ℂ) - 1) (z ^ k) =
      Lf (fun g => (fixCount (π g) : ℂ) - 1) (Polynomial.aeval z h) := by
    show _ = LfL (fun g => (fixCount (π g) : ℂ) - 1) (Polynomial.aeval z h)
    rw [aeval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    simp [LfL]
  rw [h1, h2, Complex.add_re, Complex.ofReal_re]

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
variable {Ω : Type*} [Fintype Ω]
/-- The spectral functional of a polynomial, in terms of expected fixed points. -/
theorem specE_poly [Nonempty Ω] {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N)
    (act : Ω → G 0 r →* Equiv.Perm (Fin N)) (z : MG D 0 r) (hz : adj z = z) (h : ℝ[X]) :
    specE act z (fun t => h.eval t) =
      (∑ g ∈ (Polynomial.aeval z h).coeff.support,
          (Matrix.trace ((Polynomial.aeval z h).coeff g)).re * (expFixOn act g - 1)) /
        ((D : ℝ) * N) + h.eval 0 / N := by
  have hcard : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [specE_eq]
  simp only [trR_poly hN _ z hz h]
  have hE : ∀ g : G 0 r, ∑ ω : Ω, ((fixCount (act ω g) : ℝ) - 1) =
      (Fintype.card Ω : ℝ) * (expFixOn act g - 1) := by
    intro g
    unfold expFixOn
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    field_simp
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [← Finset.mul_sum, hE, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : ∑ g ∈ (Polynomial.aeval z h).coeff.support,
      (Matrix.trace ((Polynomial.aeval z h).coeff g)).re *
        ((Fintype.card Ω : ℝ) * (expFixOn act g - 1)) =
      (Fintype.card Ω : ℝ) * ∑ g ∈ (Polynomial.aeval z h).coeff.support,
        (Matrix.trace ((Polynomial.aeval z h).coeff g)).re * (expFixOn act g - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    ring
  rw [this]
  field_simp

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
variable {Ω : Type*} [Fintype Ω]
alias specE_poly := RandomInvolutions.Dev.PartO.specE_poly

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
variable {Ω : Type*} [Fintype Ω]
/-! ## The tail bound -/
/-- Markov's inequality for the norm. -/
theorem tail_le {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) (act : Ω → G 0 r →* Equiv.Perm (Fin N))
    (z : MG D 0 r) (hz : adj z = z) (ρ' : ℝ) :
    StrongConv.uniformProb (fun ω : Ω => ρ' ≤ ‖perpOp (act ω) z‖) ≤
      (D : ℝ) * N * specE act z (fun t => if ρ' ≤ |t| then 1 else 0) := by
  have := nontrivial_space hD hN
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hrhs : (D : ℝ) * N * specE act z (fun t => if ρ' ≤ |t| then 1 else 0) =
      (∑ ω : Ω, trR (fc (fun t => if ρ' ≤ |t| then 1 else 0) (perpOp (act ω) z))) /
        (Fintype.card Ω : ℝ) := by
    rw [specE_eq, ← div_div, mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)]
  rw [hrhs]
  unfold StrongConv.uniformProb
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hcard : ((Finset.univ.filter fun ω : Ω => ρ' ≤ ‖perpOp (act ω) z‖).card : ℝ) =
      ∑ ω : Ω, if ρ' ≤ ‖perpOp (act ω) z‖ then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
  rw [hcard]
  refine Finset.sum_le_sum fun (ω : Ω) _ => ?_
  split_ifs with hω
  · exact trR_ge_one _ (sa z hz (act ω)) ρ' hω
  · exact trR_nonneg _ (fc_nonneg _ _ fun x => by split_ifs <;> norm_num)

end RandomInvolutions.Dev.PartO
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
variable {Ω : Type*} [Fintype Ω]
alias tail_le := RandomInvolutions.Dev.PartO.tail_le

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias trTau_pow_le := RandomInvolutions.Dev.PartO.trTau_pow_le

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartU2
variable {r : ℕ}
/-! ## The expansion -/
theorem moment_formula {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (hz : adj z = z) (κ : Fin r → ℕ)
    (N : ℕ) (hN : 1 ≤ N) (hA : AdmK N κ) (p : ℕ) :
    (N : ℝ) * (EE z κ N (fun x => x ^ p) - aa z p) =
      TT z p (fun g => expFixK r N κ g - 1) - aa z p + i0 p := by
  have hne := nonempty_omK N κ hA
  have hfun : (fun x : ℝ => x ^ p) = fun t => (X ^ p : ℝ[X]).eval t := by
    funext t; simp
  have haev : Polynomial.aeval z (X ^ p : ℝ[X]) = z ^ p := by simp
  unfold EE
  rw [hfun, specE_poly hD hN _ z hz (X ^ p), haev, TT_eq_div]
  have hsplit : ∑ g ∈ (z ^ p).coeff.support,
        (Matrix.trace ((z ^ p).coeff g)).re *
          (expFixOn (fun τ : OmK r N κ => homK τ) g - 1) =
      (Matrix.trace ((z ^ p).coeff 1)).re * ((N : ℝ) - 1) +
        ∑ g ∈ (z ^ p).coeff.support, if g = 1 then 0 else
          (Matrix.trace ((z ^ p).coeff g)).re * (expFixK r N κ g - 1) := by
    have h1 : ∀ g ∈ (z ^ p).coeff.support,
        (Matrix.trace ((z ^ p).coeff g)).re *
            (expFixOn (fun τ : OmK r N κ => homK τ) g - 1) =
          (if g = 1 then
              (Matrix.trace ((z ^ p).coeff g)).re * (expFixK r N κ g - 1) else 0) +
            (if g = 1 then 0 else
              (Matrix.trace ((z ^ p).coeff g)).re * (expFixK r N κ g - 1)) := by
      intro g _
      split_ifs <;> simp [expFixK]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_ite_eq']
    congr 1
    split_ifs with h1s
    · rw [expFixK_one N κ hA]
    · have : (z ^ p).coeff 1 = 0 := Finsupp.notMem_support_iff.mp h1s
      simp [this]
  have h0 : (X ^ p : ℝ[X]).eval 0 = i0 p := by
    simp [zero_pow_eq, i0]
  rw [hsplit, aa_eq, h0]
  generalize (∑ g ∈ (z ^ p).coeff.support, if g = 1 then 0 else
          (Matrix.trace ((z ^ p).coeff g)).re * (expFixK r N κ g - 1)) = S
  generalize i0 p = j0
  generalize (Matrix.trace ((z ^ p).coeff 1)).re = T
  have hD' : (D : ℝ) ≠ 0 := by positivity
  have hn' : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem moment_formula2 {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (hz : adj z = z) (κ : Fin r → ℕ)
    (N : ℕ) (hN : 1 ≤ N) (hA : AdmK N κ) (p : ℕ) :
    (N : ℝ) ^ 2 * (EE z κ N (fun x => x ^ p) - aa z p -
        (AA z p + ∑ i, (κ i : ℝ) * BB z i p) / N) =
      TT z p (fun g => (N : ℝ) * (expFixK r N κ g -
        ((cfun g : ℝ) + 1 + ∑ i, (κ i : ℝ) * Bcount i g))) := by
  have hn' : (N : ℝ) ≠ 0 := by positivity
  have h1 : (N : ℝ) ^ 2 * (EE z κ N (fun x => x ^ p) - aa z p -
        (AA z p + ∑ i, (κ i : ℝ) * BB z i p) / N) =
      (N : ℝ) * ((N : ℝ) * (EE z κ N (fun x => x ^ p) - aa z p) -
        (AA z p + ∑ i, (κ i : ℝ) * BB z i p)) := by
    field_simp
  rw [h1, moment_formula hD z hz κ N hN hA p]
  have hfun : (fun g : G 0 r => (N : ℝ) * (expFixK r N κ g -
        ((cfun g : ℝ) + 1 + ∑ i, (κ i : ℝ) * Bcount i g))) =
      (N : ℝ) • ((fun g : G 0 r => expFixK r N κ g - 1) - (fun g : G 0 r => (cfun g : ℝ)) -
        ∑ i, (κ i : ℝ) • (fun g : G 0 r => (Bcount i g : ℝ))) := by
    funext g
    simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul]
    ring
  rw [hfun]
  simp only [map_smul, map_sub, map_sum, smul_eq_mul]
  unfold AA BB
  ring

theorem hexp {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (hz : adj z = z) :
    ∃ (C0 : ℕ → ℝ) (C1 : Fin r → ℕ → ℝ), ∀ (κ : Fin r → ℕ) (p : ℕ),
      Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (EE z κ N (fun x => x ^ p) - aa z p -
          (AA z p + ∑ i, (κ i : ℝ) * BB z i p) / N)) (admF κ)
        (𝓝 (C0 p + ∑ i, (κ i : ℝ) * C1 i p + ∑ i, ∑ j, (κ i : ℝ) * κ j * CC2 z i j p)) := by
  obtain ⟨C0, C1, hC⟩ := tendsto_mul_expFixK_sub_first_order r
  refine ⟨fun p => TT z p C0, fun i p => TT z p (C1 i), fun κ p => ?_⟩
  have hlim := TT_tendsto z p (admF κ)
    (fun (N : ℕ) (g : G 0 r) => (N : ℝ) * (expFixK r N κ g -
        ((cfun g : ℝ) + 1 + ∑ i, (κ i : ℝ) * Bcount i g)))
    (fun g => C0 g + ∑ i, (κ i : ℝ) * C1 i g + ∑ i, ∑ j, (κ i : ℝ) * κ j * C2count i j g)
    (fun g hg => hC g hg κ)
  have hfun : (fun g : G 0 r => C0 g + ∑ i, (κ i : ℝ) * C1 i g +
        ∑ i, ∑ j, (κ i : ℝ) * κ j * C2count i j g) =
      C0 + ∑ i, (κ i : ℝ) • C1 i +
        ∑ i, ∑ j, ((κ i : ℝ) * κ j) • (fun g : G 0 r => (C2count i j g : ℝ)) := by
    funext g
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [hfun] at hlim
  simp only [map_add, map_sum, map_smul, smul_eq_mul] at hlim
  refine hlim.congr' ?_
  have hev : ∀ᶠ N : ℕ in admF κ, 1 ≤ N ∧ AdmK N κ := by
    unfold admF
    exact (eventually_inf_principal.mpr (Eventually.of_forall fun N h => h)).and
      ((eventually_ge_atTop 1).filter_mono inf_le_left) |>.mono fun N h => ⟨h.2, h.1⟩
  filter_upwards [hev] with N hN
  exact (moment_formula2 hD z hz κ N hN.1 hN.2 p).symm

/-! ## Growth -/
theorem abs_aa_le {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (p : ℕ) :
    |aa z p| ≤ ‖regOp z‖ ^ p :=
  (Complex.abs_re_le_norm _).trans (trTau_pow_le hD z p)

theorem pow_mul_bdd (k : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∃ M : ℝ, ∀ p : ℕ, (p : ℝ) ^ k * θ ^ p ≤ M := by
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one k (r := θ)
    (by rw [abs_of_nonneg h0]; exact h1)
  obtain ⟨M, hM⟩ := h.bddAbove_range
  exact ⟨M, fun p => hM ⟨p, rfl⟩⟩

theorem grow {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (w : G 0 r → ℝ)
    (hw : ∀ (L : Lin 0 r) (R : ℝ), 0 ≤ R → (∀ j, ‖Xop L j‖ ≤ R) →
      ∃ (C : ℝ) (k : ℕ), ∀ m : ℕ, 1 ≤ m →
        ‖∑ i : Fin m → Option (Lt 0 r),
            (((if iprod i = 1 then 0 else w (iprod i) : ℝ)) : ℂ) * (Bprod L m i).trace‖ ≤
          C * (m : ℝ) ^ k * R ^ m)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ p : ℕ, |TT z p w| ≤ C * (‖regOp z‖ + δ) ^ p := by
  set ρ := ‖regOp z‖ with hρdef
  have hρ : 0 ≤ ρ := norm_nonneg _
  obtain ⟨C, k, hC⟩ := moment_bound_of_lin z
    (fun g => (((if g = 1 then 0 else w g : ℝ)) : ℂ)) hw (δ / 2) (by positivity)
  have hpos : 0 < ρ + δ := by positivity
  obtain ⟨M, hM⟩ := pow_mul_bdd k ((ρ + δ / 2) / (ρ + δ)) (by positivity)
    (by rw [div_lt_one hpos]; linarith)
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0)
  refine ⟨|C| * M + |TT z 0 w|, fun p => ?_⟩
  have hpp : 0 ≤ (ρ + δ) ^ p := by positivity
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : 0 ≤ |C| * M := by positivity
    simp only [pow_zero, mul_one]
    linarith
  · have hS : |TT z p w| ≤ |C| * M * (ρ + δ) ^ p := by
      rw [TT_eq_re, abs_div, Nat.abs_cast]
      refine (div_le_self (abs_nonneg _) (by exact_mod_cast hD)).trans ?_
      refine (Complex.abs_re_le_norm _).trans ((hC p hp).trans ?_)
      have hθ : (ρ + δ / 2) ^ p = ((ρ + δ / 2) / (ρ + δ)) ^ p * (ρ + δ) ^ p := by
        rw [← mul_pow, div_mul_cancel₀ _ hpos.ne']
      rw [hθ]
      have h1 : (p : ℝ) ^ k * ((ρ + δ / 2) / (ρ + δ)) ^ p ≤ M := hM p
      have h2 : 0 ≤ (p : ℝ) ^ k * ((ρ + δ / 2) / (ρ + δ)) ^ p := by positivity
      calc C * (p : ℝ) ^ k * (((ρ + δ / 2) / (ρ + δ)) ^ p * (ρ + δ) ^ p)
          = C * ((p : ℝ) ^ k * ((ρ + δ / 2) / (ρ + δ)) ^ p) * (ρ + δ) ^ p := by ring
        _ ≤ |C| * M * (ρ + δ) ^ p := by
            refine mul_le_mul_of_nonneg_right ?_ hpp
            exact (mul_le_mul_of_nonneg_right (le_abs_self C) h2).trans
              (mul_le_mul_of_nonneg_left h1 (abs_nonneg C))
    have hb0 : 0 ≤ |TT z 0 w| * (ρ + δ) ^ p := by positivity
    linarith

theorem hagrow {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ p : ℕ, |aa z p| ≤ C * (‖regOp z‖ + δ) ^ p :=
  ⟨1, fun p => by
    rw [one_mul]
    exact (abs_aa_le hD z p).trans (pow_le_pow_left₀ (norm_nonneg _) (by linarith) p)⟩

theorem hAgrow {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ p : ℕ, |AA z p| ≤ C * (‖regOp z‖ + δ) ^ p := by
  obtain ⟨C, hC⟩ := grow hD z (fun g => (cfun g : ℝ)) (fun L R hR hX => by
    obtain ⟨C, k, h⟩ := norm_sum_cfun_mul_trace_Bprod_le L R hR hX
    refine ⟨C, k, fun m hm => ?_⟩
    refine le_of_eq_of_le (congrArg norm (Finset.sum_congr rfl fun i _ => ?_)) (h m hm)
    split_ifs
    · simp
    · push_cast; rfl) δ hδ
  refine ⟨C + 2, fun p => ?_⟩
  have h1 := hC p
  have h2 : |aa z p| ≤ (‖regOp z‖ + δ) ^ p :=
    (abs_aa_le hD z p).trans (pow_le_pow_left₀ (norm_nonneg _) (by linarith) p)
  have h3 : |i0 p| ≤ (‖regOp z‖ + δ) ^ p := by
    unfold i0
    split_ifs with hp
    · subst hp; simp
    · rw [abs_zero]; positivity
  unfold AA
  have := abs_add_le (TT z p (fun g => (cfun g : ℝ)) - aa z p) (i0 p)
  have := abs_sub (TT z p (fun g => (cfun g : ℝ))) (aa z p)
  linarith

theorem hBgrow {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (i : Fin r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ p : ℕ, |BB z i p| ≤ C * (‖regOp z‖ + δ) ^ p :=
  grow hD z (fun g => (Bcount i g : ℝ)) (fun L R hR hX => by
    obtain ⟨C, k, h⟩ := norm_sum_bcount_mul_trace_Bprod_le L R hR hX i
    refine ⟨C, k, fun m hm => ?_⟩
    refine le_of_eq_of_le (congrArg norm (Finset.sum_congr rfl fun j _ => ?_)) (h m hm)
    split_ifs with h1
    · rw [h1, Bcount_one]; simp
    · push_cast; rfl) δ hδ

theorem hC2grow {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (i j : Fin r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ p : ℕ, |CC2 z i j p| ≤ C * (‖regOp z‖ + δ) ^ p :=
  grow hD z (fun g => (C2count i j g : ℝ)) (fun L R hR hX => by
    obtain ⟨C, k, h⟩ := norm_sum_c2count_mul_trace_Bprod_le L R hR hX i j
    refine ⟨C, k, fun m hm => ?_⟩
    refine le_of_eq_of_le (congrArg norm (Finset.sum_congr rfl fun l _ => ?_)) (h m hm)
    split_ifs with h1
    · rw [h1, C2count_one]; simp
    · push_cast; rfl) δ hδ

end RandomInvolutions.Dev.PartU2
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

/-- Step `k` is a closing step: a new pair to an old vertex. -/
def closing (a : ℕ → Fin r) (x : ℕ → α) (k : ℕ) : Prop :=
  x k ≠ x (k + 1) ∧ x (k + 1) ∈ UU x k ∧ pe a x k ∉ EE a x k

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

/-! ## Periodic readings -/
/-- The colours of a nonempty word, read cyclically. -/
def ac (u : List (Lt 0 r)) (hne : u ≠ []) (t : ℕ) : Fin r :=
  colr (u.get ⟨t % u.length, Nat.mod_lt _ (List.length_pos_iff.2 hne)⟩)

/-- A colouring read cyclically. -/
def Xc {L : ℕ} {β : Type*} (c : Fin (L + 1) → β) (t : ℕ) : β := c ⟨min (t % L) L, by omega⟩

lemma ac_get (u : List (Lt 0 r)) (hne : u ≠ []) (t : Fin u.length) :
    colr (u.get t) = ac u hne t.val := by
  unfold ac; congr 2; exact Fin.ext (by simp [Nat.mod_eq_of_lt t.2])

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
lemma card_Ps_eq (k : Fin r) :
    (Ps u c k).card = ((EE (ac u hne) (Xc c) u.length).filter (fun e => e.1 = k)).card := by
  rw [EE_fiber u hne c hcl, card_image_of_injective _ (Prod.mk_right_injective k)]

include hcl in
lemma sum_card_Ps : ∑ k, (Ps u c k).card = (EE (ac u hne) (Xc c) u.length).card := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
  exact sum_congr rfl fun k _ => card_Ps_eq u hne c hcl k

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
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartC2
variable {r : ℕ}
lemma natDegree_fpoly (u : List (Lt 0 r)) (q : ℕ) (κ : Fin r → ℕ) (hL : u.length ≤ q)
    (c : Fin (u.length + 1) → Fin (u.length + 1)) (hc : c ∈ CGL u) :
    (fpoly u q κ c).natDegree ≤ r * q + 1 := by
  have hg := ((mem_CGL u c).1 hc).2
  have hv := RandomInvolutions.Dev.nv_le_ecount_succ u c hc
  have hd : ∀ i, fK u c i + 2 * eK u c i ≤ q := fun i => (card_le_length u c hg i).trans hL
  have h1 : (X ^ (Ecount u c + Fcount u c + 1 - nv c) : ℝ[X]).natDegree ≤
      Ecount u c + Fcount u c + 1 - nv c := natDegree_X_pow_le _
  have h2 := natDegree_PA (nv c)
  have h3 : (∏ i, (C ((κ i).descFactorial (fK u c i) : ℝ) * PK (κ i) (eK u c i) *
      PA' (fK u c i + 2 * eK u c i) q)).natDegree ≤
      ∑ i, (eK u c i + (q - (fK u c i + 2 * eK u c i))) := by
    refine (natDegree_prod_le _ _).trans (sum_le_sum fun i _ => ?_)
    refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_PA' _ _))
    exact (natDegree_C_mul_le _ _).trans (natDegree_PK _ _)
  have h5 : ∑ i, (eK u c i + (q - (fK u c i + 2 * eK u c i))) + (Ecount u c + Fcount u c) =
      r * q := by
    unfold Ecount Fcount
    rw [← sum_add_distrib, ← sum_add_distrib,
      sum_congr rfl (g := fun _ => q) (fun i _ => by have := hd i; omega)]
    simp
  have h8 : (fpoly u q κ c).natDegree ≤
      (Ecount u c + Fcount u c + 1 - nv c) + nv c +
        ∑ i, (eK u c i + (q - (fK u c i + 2 * eK u c i))) := by
    unfold fpoly
    exact natDegree_mul_le.trans (add_le_add (natDegree_mul_le.trans (add_le_add h1 h2)) h3)
  omega

lemma factor_eq (N q κ f e : ℕ) (hN : 1 ≤ N) (hd : f + 2 * e ≤ q) (hq : q ≤ N) :
    (((κ.descFactorial f : ℝ) * ∏ l ∈ range e, ((N : ℝ) - κ - 2 * l)) /
        (N.descFactorial (f + 2 * e) : ℝ)) =
      (1 / (N : ℝ)) ^ (e + f) *
        ((C (κ.descFactorial f : ℝ) * PK κ e * PA' (f + 2 * e) q).eval (1 / (N : ℝ))) /
          (PA q).eval (1 / (N : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hq0 := PA_ne N q hN hq
  rw [← PA_mul _ _ hd, eval_mul] at hq0
  have ha := left_ne_zero_of_mul hq0
  have hb := right_ne_zero_of_mul hq0
  rw [pair_eq N κ e hN, desc_eq N (f + 2 * e) hN, ← PA_mul _ _ hd]
  simp only [eval_mul, eval_C]
  set x : ℝ := 1 / (N : ℝ)
  set a := (PA (f + 2 * e)).eval x
  set b := (PA' (f + 2 * e) q).eval x
  set p := (PK κ e).eval x
  have hx : x ^ (e + f) * (N : ℝ) ^ (f + 2 * e) = (N : ℝ) ^ e := by
    have hxN : x * (N : ℝ) = 1 := by simp only [x]; field_simp
    calc x ^ (e + f) * (N : ℝ) ^ (f + 2 * e)
        = (x * (N : ℝ)) ^ (e + f) * (N : ℝ) ^ e := by rw [mul_pow]; ring
      _ = (N : ℝ) ^ e := by rw [hxN, one_pow, one_mul]
  rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hN0) ha) (mul_ne_zero ha hb)]
  rw [← hx]
  ring

lemma wt_eq (u : List (Lt 0 r)) (q N : ℕ) (κ : Fin r → ℕ) (hL : u.length ≤ q) (hq : q ≤ N)
    (hN : 1 ≤ N) (c : Fin (u.length + 1) → Fin (u.length + 1)) (hc : c ∈ CGL u) :
    wtK u N κ c = N * ((fpoly u q κ c).eval (1 / (N : ℝ)) /
      ((PA q) ^ r).eval (1 / (N : ℝ))) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hg := ((mem_CGL u c).1 hc).2
  have hv := RandomInvolutions.Dev.nv_le_ecount_succ u c hc
  have hd : ∀ i, fK u c i + 2 * eK u c i ≤ q := fun i => (card_le_length u c hg i).trans hL
  unfold wtK wtF
  rw [prod_congr rfl fun i _ => factor_eq N q (κ i) (fK u c i) (eK u c i) hN (hd i) hq,
    desc_eq N (nv c) hN]
  set x : ℝ := 1 / (N : ℝ) with hx
  have ef : (fpoly u q κ c).eval x =
      x ^ (Ecount u c + Fcount u c + 1 - nv c) * (PA (nv c)).eval x *
        ∏ i, (C ((κ i).descFactorial (fK u c i) : ℝ) * PK (κ i) (eK u c i) *
          PA' (fK u c i + 2 * eK u c i) q).eval x := by
    simp only [fpoly, eval_mul, eval_pow, eval_prod, eval_X]
  rw [ef, eval_pow, prod_div_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, prod_const,
    card_univ, Fintype.card_fin]
  have hEF : ∑ i, (eK u c i + fK u c i) = Ecount u c + Fcount u c := by
    unfold Ecount Fcount; rw [sum_add_distrib]
  rw [hEF]
  set k := Ecount u c + Fcount u c + 1 - nv c with hk
  set S := Ecount u c + Fcount u c
  set a := (PA (nv c)).eval x
  set Q := ∏ i, (C ((κ i).descFactorial (fK u c i) : ℝ) * PK (κ i) (eK u c i) *
          PA' (fK u c i + 2 * eK u c i) q).eval x
  set G := (PA q).eval x ^ r
  have hkv : nv c + k = S + 1 := by omega
  have hxN : x * (N : ℝ) = 1 := by rw [hx]; field_simp
  have hK : (N : ℝ) ^ nv c * x ^ S = (N : ℝ) * x ^ k := by
    apply mul_right_cancel₀ (pow_ne_zero S hN0)
    calc (N : ℝ) ^ nv c * x ^ S * (N : ℝ) ^ S = (N : ℝ) ^ nv c * (x * (N : ℝ)) ^ S := by
          rw [mul_pow]; ring
      _ = (N : ℝ) ^ nv c := by rw [hxN, one_pow, mul_one]
      _ = (x * (N : ℝ)) ^ k * (N : ℝ) ^ nv c := by rw [hxN, one_pow, one_mul]
      _ = x ^ k * (N : ℝ) ^ (nv c + k) := by rw [mul_pow, pow_add]; ring
      _ = x ^ k * (N : ℝ) ^ (S + 1) := by rw [hkv]
      _ = (N : ℝ) * x ^ k * (N : ℝ) ^ S := by rw [pow_succ]; ring
  calc (N : ℝ) ^ nv c * a * (x ^ S * Q / G) = ((N : ℝ) ^ nv c * x ^ S) * (a * Q / G) := by ring
    _ = (N : ℝ) * x ^ k * (a * Q / G) := by rw [hK]
    _ = (N : ℝ) * (x ^ k * a * Q / G) := by ring

/-! ## Rationality -/
/-- Expected fixed points are rational in `1/N` along every ray `κ`, with a common denominator
`gq` independent of `κ`. -/
theorem rationalK (r : ℕ) : ∃ C : ℕ, 1 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X],
    gq.natDegree ≤ C * q ∧
    (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
    ∀ g : G 0 r, len g ≤ q → ∀ κ : Fin r → ℕ, ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
      ∀ N : ℕ, AdmK N κ → q ≤ N →
        expFixK r N κ g = N * (f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ))) := by
  refine ⟨4 * (r + 1), by omega, fun q hq => ⟨(PA q) ^ r, ?_, ?_, ?_⟩⟩
  · calc ((PA q) ^ r).natDegree ≤ r * (PA q).natDegree := natDegree_pow_le
      _ ≤ r * q := Nat.mul_le_mul_left _ (natDegree_PA q)
      _ ≤ 4 * (r + 1) * q := Nat.mul_le_mul_right _ (by omega)
  · intro x hx
    apply gq_bounds r q hq x
    have e : ((4 * (r + 1) : ℕ) : ℝ) = 4 * ((r : ℝ) + 1) := by push_cast; ring
    rwa [e] at hx
  · obtain ⟨nf, -, hnf, -, hlen⟩ := RandomInvolutions.Dev.nf_exists r
    intro g hg κ
    have hL : (nf g).length ≤ q := by rw [← hlen]; exact hg
    refine ⟨∑ c ∈ CGL (nf g), fpoly (nf g) q κ c, ?_, ?_⟩
    · refine natDegree_sum_le_of_forall_le _ _ fun c hc =>
        (natDegree_fpoly (nf g) q κ hL c hc).trans ?_
      nlinarith
    · intro N hA hqN
      have hN : 1 ≤ N := hq.trans hqN
      have h' : expFixK r N κ g = expFixK r N κ (wprod (nf g)) := by rw [hnf]
      rw [h', expect_formulaK (nf g) N κ hN hA (hL.trans hqN), eval_finsetSum, sum_div, mul_sum]
      exact sum_congr rfl fun c hc => wt_eq (nf g) q N κ hL hqN hN c hc

end RandomInvolutions.Dev.PartC2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias rationalK := RandomInvolutions.Dev.PartC2.rationalK

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartU2
variable {r : ℕ}
/-! ## Rationality -/
theorem hrat {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (hz : adj z = z) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∀ κ : Fin r → ℕ, ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ N : ℕ, AdmK N κ → C * q ≤ N →
          EE z κ N (fun x => h.eval x) = f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ)) := by
  obtain ⟨C0, hC0, hrat⟩ := rationalK r
  set L := lenmax z with hL
  set A := (L + 1) ^ 2 with hA
  have hLA : L + 1 ≤ A := Nat.le_self_pow (by norm_num) _
  have hA1 : 1 ≤ A := le_trans (by omega) hLA
  refine ⟨C0 * A + 1, by omega, fun q hq => ?_⟩
  have hq' : 1 ≤ q * (L + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨gq, hdeg, hint, hf⟩ := hrat (q * (L + 1)) hq'
  have hqA : q * (L + 1) ≤ q * A := Nat.mul_le_mul_left _ hLA
  have hbig : C0 * (q * (L + 1)) + 1 ≤ (C0 * A + 1) * q := by
    have : C0 * (q * (L + 1)) ≤ C0 * (q * A) := Nat.mul_le_mul_left _ hqA
    have e : (C0 * A + 1) * q = C0 * (q * A) + q := by ring
    omega
  have hq'C : q * (L + 1) ≤ (C0 * A + 1) * q := by
    have : q * (L + 1) ≤ C0 * (q * (L + 1)) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hbig' : C0 * (q * (L + 1)) ≤ (C0 * A + 1) * q := by omega
  refine ⟨gq, by omega, ?_, ?_⟩
  · intro x hx
    refine hint x ⟨hx.1, hx.2.trans ?_⟩
    have hnat : C0 * (q * (L + 1)) ^ 2 ≤ (C0 * A + 1) * q ^ 2 := by
      have e : C0 * (q * (L + 1)) ^ 2 = (C0 * A) * q ^ 2 := by
        rw [hA]; ring
      rw [e]
      exact Nat.mul_le_mul_right _ (by omega)
    have hreal : (C0 : ℝ) * ((q * (L + 1) : ℕ) : ℝ) ^ 2 ≤
        ((C0 * A + 1 : ℕ) : ℝ) * (q : ℝ) ^ 2 := by
      exact_mod_cast hnat
    have hqpos : (0 : ℝ) < ((q * (L + 1) : ℕ) : ℝ) := by exact_mod_cast hq'
    have hC0pos : (0 : ℝ) < (C0 : ℝ) := by exact_mod_cast hC0
    exact one_div_le_one_div_of_le (by positivity) hreal
  · intro h hh κ
    set y := Polynomial.aeval z h with hy
    have hlen : ∀ g ∈ y.coeff.support, len g ≤ q * (L + 1) := by
      intro g hg
      calc len g ≤ h.natDegree * L := len_support_aeval z h g hg
        _ ≤ q * (L + 1) := Nat.mul_le_mul hh (by omega)
    have hex : ∀ g : G 0 r, ∃ f : ℝ[X], len g ≤ q * (L + 1) →
        (f.natDegree ≤ C0 * (q * (L + 1)) ∧
          ∀ N : ℕ, AdmK N κ → q * (L + 1) ≤ N →
            expFixK r N κ g = N * (f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ)))) := by
      intro g
      by_cases hg : len g ≤ q * (L + 1)
      · obtain ⟨f, hf1, hf2⟩ := hf g hg κ
        exact ⟨f, fun _ => ⟨hf1, hf2⟩⟩
      · exact ⟨0, fun h' => absurd h' hg⟩
    choose f hfg using hex
    have hlen1 : len (1 : G 0 r) ≤ q * (L + 1) := by
      rw [len_one]; omega
    refine ⟨∑ g ∈ y.coeff.support,
        Polynomial.C ((Matrix.trace (y.coeff g)).re / D) * (f g - X * gq) +
          Polynomial.C (h.eval 0) * (X * gq), ?_, ?_⟩
    · have hXg : (X * gq : ℝ[X]).natDegree ≤ (C0 * A + 1) * q := by
        refine natDegree_mul_le.trans ?_
        rw [natDegree_X]
        omega
      refine (natDegree_add_le_of_degree_le ?_ ?_)
      · refine natDegree_sum_le_of_forall_le _ _ fun g hg => ?_
        refine (natDegree_C_mul_le _ _).trans ?_
        simpa using natDegree_sub_le_of_le (((hfg g (hlen g hg)).1).trans hbig') hXg
      · exact (natDegree_C_mul_le _ _).trans hXg
    · intro N hAd hn
      have hne := nonempty_omK N κ hAd
      have hq'N : q * (L + 1) ≤ N := hq'C.trans hn
      have hN : 1 ≤ N := hq'.trans hq'N
      unfold EE
      rw [specE_poly hD hN _ z hz h, ← hy]
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      -- the denominator does not vanish: use `g = 1`
      have hgq : gq.eval (1 / (N : ℝ)) ≠ 0 := by
        intro h0
        have h1 := (hfg 1 hlen1).2 N hAd hq'N
        rw [expFixK_one N κ hAd, h0, div_zero, mul_zero] at h1
        exact hNpos.ne' h1
      have hD' : (D : ℝ) ≠ 0 := by positivity
      have hterm : ∀ g ∈ y.coeff.support,
          (Matrix.trace (y.coeff g)).re *
              (expFixOn (fun τ : OmK r N κ => homK τ) g - 1) / ((D : ℝ) * N) =
            ((Matrix.trace (y.coeff g)).re / D) *
              ((f g).eval (1 / (N : ℝ)) - 1 / (N : ℝ) * gq.eval (1 / (N : ℝ))) /
                gq.eval (1 / (N : ℝ)) := by
        intro g hg
        have := (hfg g (hlen g hg)).2 N hAd hq'N
        unfold expFixK at this
        rw [this]
        generalize (f g).eval (1 / (N : ℝ)) = F at *
        generalize gq.eval (1 / (N : ℝ)) = Gv at *
        field_simp
      rw [Finset.sum_div, Finset.sum_congr rfl hterm]
      simp only [eval_add, eval_finsetSum, eval_mul, eval_C, eval_sub, eval_X]
      rw [add_div, Finset.sum_div]
      congr 1
      generalize gq.eval (1 / (N : ℝ)) = Gv at *
      field_simp

/-! ## The upper tail -/
theorem prob_norm_perpOp_ge_le {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (hz : adj z = z) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (N : ℕ) (κ : Fin r → ℕ), AdmK N κ → 1 ≤ N →
      StrongConv.uniformProb (fun τ : OmK r N κ => ‖regOp z‖ + ε ≤ ‖perpOp (homK τ) z‖) ≤
        C * lam κ / N + C * lam κ ^ 3 / (N : ℝ) ^ 2 := by
  have hbnd : 0 ≤ bnd z := by
    unfold bnd
    exact Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => norm_nonneg _
  obtain ⟨C, hC⟩ := tail_le_of_second_order_rational_moments (bnd z + 1) (by linarith) r (EE z)
    (fun κ N f g => specE_add _ z hz f g)
    (fun κ N a f => specE_smul _ z hz a f)
    (fun κ N f g hfg => specE_mono _ z hz f g fun x hx =>
      hfg x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (fun κ N => specE_one_le _ z hz)
    (hrat hD z hz)
    ‖regOp z‖ (norm_nonneg _) (aa z) (AA z) (BB z) (CC2 z)
    (hexp hD z hz)
    (hagrow hD z) (hAgrow hD z) (hBgrow hD z) (hC2grow hD z)
    ε hε
  refine ⟨D * C, fun N κ hA hN => ?_⟩
  refine (tail_le hD hN (fun τ : OmK r N κ => homK τ) z hz (‖regOp z‖ + ε)).trans ?_
  have h1 := hC κ N hA hN
  have hn' : (0 : ℝ) < N := by exact_mod_cast hN
  have hDN : (0 : ℝ) ≤ (D : ℝ) * (N : ℝ) := by positivity
  refine (mul_le_mul_of_nonneg_left h1 hDN).trans (le_of_eq ?_)
  field_simp

end RandomInvolutions.Dev.PartU2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-! ## Part U2: the upper tail in the conditional model, uniformly along rays -/
alias prob_norm_perpOp_ge_le := RandomInvolutions.Dev.PartU2.prob_norm_perpOp_ge_le

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
theorem solution {r : ℕ} {D : ℕ} (hD : 1 ≤ D) (z : MG D 0 r) (hz : adj z = z) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (N : ℕ) (κ : Fin r → ℕ), AdmK N κ → 1 ≤ N →
      StrongConv.uniformProb (fun τ : OmK r N κ => ‖regOp z‖ + ε ≤ ‖perpOp (homK τ) z‖) ≤
        C * lam κ / N + C * lam κ ^ 3 / (N : ℝ) ^ 2 := by
  exact RandomInvolutions.Dev.prob_norm_perpOp_ge_le hD z hz ε hε
end
end
