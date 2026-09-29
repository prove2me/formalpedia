-- Prove2me | solution 1 for Zeta23.Analytic.residueTheorem_finset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:37:57.732632+00:00
-- url     : https://prove2.me/submissions/bc862ddb-25d3-4932-b1a0-c42e3c46234d

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Theorems.Thm_Zeta23_IsBigO_to_BddAbove

-- from Zeta23.FromPNTPlus.Rectangle
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/Rectangle.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
@[blueprint ...] attributes).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





theorem Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))

theorem Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))

theorem Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h ↦ Set.left_not_mem_uIoo (h ▸ hc)

theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h ↦ Set.right_not_mem_uIoo (h ▸ hc)






lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩


lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩,
    fun hc ↦ h.2.1 hc.1⟩



lemma rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]





lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]





theorem not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ RectangleBorder z w := by
  refine Set.disjoint_right.mp (rectangleBorder_disjoint_singleton ?_) rfl
  have h1 := rectangle_mem_nhds_iff.mp hp
  exact ⟨Set.ne_left_of_mem_uIoo h1.1, Set.ne_right_of_mem_uIoo h1.1,
    Set.ne_left_of_mem_uIoo h1.2, Set.ne_right_of_mem_uIoo h1.2⟩




end

-- from Zeta23.FromPNTPlus.ResidueCalcOnRectangles
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes) and redirected intra-project
imports to Zeta23.FromPNTPlus.*.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}









/- An UpperUIntegral is the integral of a function over a |\_| shape. -/

/- A LowerUIntegral is the integral of a function over a |-| shape. -/







theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)

theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]




theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩


















theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]

lemma Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring

lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]

lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)

lemma integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert! (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)

lemma integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

set_option backward.isDefEq.respectTransparency false in
lemma integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]

lemma integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

lemma ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf

theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]






/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/








-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.





-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.



-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.



end

-- from Zeta23.Analytic.RectangleLogDeriv
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Residue calculus on rectangles beyond one simple pole.
Used for the weighted contour integral ∮ H·Λ'/Λ and for the Riemann–von Mangoldt count
N(T₁,T₂) = (1/2πi)∮ Λ'/Λ.

* `residueTheorem_finset`: f holomorphic on Rectangle z w minus a finite set S of interior points, with
  f − A p/(s − p) bounded near each p ∈ S  ⟹  RectangleIntegral' f z w = Σ_{p∈S} A p.
  (Induction on S: subtract one principal part, remove the singularity, recurse.)
* `rectangleIntegral'_mul_logDeriv` (the "argument principle with weight"): f, g analytic on a
  neighbourhood of each point of Rectangle z w, f ≠ 0 on the border, Z = the (finite) zero set of
  f in the rectangle  ⟹  RectangleIntegral' (g · f'/f) z w = Σ_{ρ∈Z} ord_ρ(f) · g(ρ).
* `finite_zeros_rectangle`, `rectangleIntegral'_mul_logDeriv'`: the zero set is finite; self-contained form.
-/

open Complex Set Topology Filter Asymptotics Real

noncomputable section

namespace Zeta23
namespace Analytic



/-! ## Meromorphic version: finitely many zeros AND poles inside the rectangle

Intended for f = completedRiemannZeta (simple poles at 0 and 1, residues ∓1):
(1/2πi) ∮ g·(f'/f) = Σ_{zeros ρ} ord_ρ(f)·g(ρ) − Σ_{poles p} m_p·g(p).
A pole of order m at p is witnessed elementarily by  (s − p)^m · f(s) → c ≠ 0  (s → p, s ≠ p),
which is the shape of Mathlib's `completedRiemannZeta_residue_one` (m = 1). -/





end Analytic
end Zeta23
end
open Complex Set Topology Filter Asymptotics Real
open Zeta23
open Analytic

theorem solution {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (S : Finset ℂ) (A : ℂ → ℂ)
    (hS : ∀ p ∈ S, Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ (S : Set ℂ)))
    (near : ∀ p ∈ S, (f - fun s => A p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = ∑ p ∈ S, A p := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty =>
    simp only [Finset.coe_empty, Set.diff_empty] at fHolo
    rw [Finset.sum_empty]
    show (1 / (2 * π * I)) • RectangleIntegral f z w = 0
    rw [fHolo.vanishesOnRectangle subset_rfl, smul_zero]
  | @insert p S hpS ih =>
    have hp : Rectangle z w ∈ 𝓝 p := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, Rectangle z w ∈ 𝓝 q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    -- the principal part at p, the remainder f₁, and its extension f₂ across p
    set P : ℂ → ℂ := fun s => A p / (s - p) with hP
    set f₁ : ℂ → ℂ := f - P with hf₁
    set f₂ : ℂ → ℂ := Function.update f₁ p (limUnder (𝓝[≠] p) f₁) with hf₂
    have hPdiff : ∀ s, s ≠ p → DifferentiableAt ℂ P s := by
      intro s hs
      have : s - p ≠ 0 := sub_ne_zero.mpr hs
      simp only [hP]
      fun_prop (disch := assumption)
    have hf₁holo : HolomorphicOn f₁ (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ)) := by
      refine fHolo.sub ?_
      intro s hs
      apply (hPdiff s ?_).differentiableWithinAt
      intro h
      apply hs.2
      simp [h]
    have hSclosed : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
    have hRS : Rectangle z w \ (S : Set ℂ) ∈ 𝓝 p := by
      apply Filter.inter_mem hp
      exact hSclosed.isOpen_compl.mem_nhds (by simpa using hpS)
    obtain ⟨U, hU, hbdd⟩ := Zeta23_IsBigO_to_BddAbove (near p (Finset.mem_insert_self p S))
    have hV : U ∩ (Rectangle z w \ (S : Set ℂ)) ∈ 𝓝 p := Filter.inter_mem hU hRS
    have hf₁V : DifferentiableOn ℂ f₁ ((U ∩ (Rectangle z w \ (S : Set ℂ))) \ {p}) := by
      apply hf₁holo.mono
      rintro s ⟨⟨_, hsR, hsS⟩, hsp⟩
      refine ⟨hsR, ?_⟩
      simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
      exact ⟨by simpa using hsp, by simpa using hsS⟩
    have hbddV : BddAbove (norm ∘ f₁ '' ((U ∩ (Rectangle z w \ (S : Set ℂ))) \ {p})) :=
      hbdd.mono (image_mono (Set.diff_subset_diff_left inter_subset_left))
    have hf₂V : DifferentiableOn ℂ f₂ (U ∩ (Rectangle z w \ (S : Set ℂ))) :=
      differentiableOn_update_limUnder_of_bddAbove hV hf₁V hbddV
    have hf₂eq : ∀ s, s ≠ p → f₂ s = f₁ s := fun s hs => Function.update_of_ne hs _ _
    -- f₂ is holomorphic on the rectangle minus the remaining poles
    have hf₂holo : HolomorphicOn f₂ (Rectangle z w \ (S : Set ℂ)) := by
      intro s hs
      by_cases hsp : s = p
      · rw [hsp]
        exact (hf₂V.differentiableAt hV).differentiableWithinAt
      · have h1 : DifferentiableWithinAt ℂ f₁
            (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ)) s :=
          hf₁holo s ⟨hs.1, by
            simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
            exact ⟨hsp, by simpa using hs.2⟩⟩
        have hset : (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ))
            = (Rectangle z w \ (S : Set ℂ)) ∩ {p}ᶜ := by
          ext x
          simp only [Finset.coe_insert, Set.mem_diff, mem_insert_iff, Finset.mem_coe, not_or,
            mem_inter_iff, mem_compl_iff, mem_singleton_iff]
          tauto
        rw [hset] at h1
        have hpc : {p}ᶜ ∈ 𝓝[Rectangle z w \ (S : Set ℂ)] s :=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hsp)
        rw [differentiableWithinAt_inter' hpc] at h1
        refine h1.congr_of_eventuallyEq ?_ (hf₂eq s hsp)
        filter_upwards [hpc] with x hx
        exact hf₂eq x hx
    -- the principal parts at the other poles are unchanged
    have near₂ : ∀ q ∈ S, (f₂ - fun s => A q / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
      intro q hq
      have hqp : q ≠ p := fun h => hpS (h ▸ hq)
      have hev : ((f - fun s => A q / (s - q)) - P)
          =ᶠ[𝓝[≠] q] (f₂ - fun s => A q / (s - q)) := by
        have : {p}ᶜ ∈ 𝓝[≠] q :=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hqp)
        filter_upwards [this] with s hs
        simp only [Pi.sub_apply, hf₂eq s hs, hf₁]
        ring
      have hPO : P =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
        have hc : ContinuousAt P q := (hPdiff q hqp).continuousAt
        exact (hc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
      exact ((near q (Finset.mem_insert_of_mem hq)).sub hPO).congr' hev EventuallyEq.rfl
    have ih' := ih hS' hf₂holo near₂
    -- on the border, f = f₂ + P
    have hborder : EqOn f (f₂ + P) (RectangleBorder z w) := by
      intro s hs
      have hsp : s ≠ p := fun h => not_mem_rectangleBorder_of_rectangle_mem_nhds hp (h ▸ hs)
      simp only [Pi.add_apply, hf₂eq s hsp, hf₁, Pi.sub_apply, sub_add_cancel]
    have hbS : ∀ s ∈ RectangleBorder z w, s ∈ Rectangle z w \ (S : Set ℂ) := fun s hs =>
      ⟨rectangleBorder_subset_rectangle z w hs,
        fun hsS => not_mem_rectangleBorder_of_rectangle_mem_nhds (hS' s hsS) hs⟩
    have hi₂ : RectangleBorderIntegrable f₂ z w :=
      ContinuousOn.rectangleBorder_integrable (hf₂holo.continuousOn.mono hbS)
    have hiP : RectangleBorderIntegrable P z w := by
      apply ContinuousOn.rectangleBorder_integrable
      intro s hs
      have hsp : s ≠ p := fun h => not_mem_rectangleBorder_of_rectangle_mem_nhds hp (h ▸ hs)
      exact (hPdiff s hsp).continuousAt.continuousWithinAt
    rw [RectangleIntegral'_congr hborder, Finset.sum_insert hpS]
    show (1 / (2 * π * I)) • RectangleIntegral (f₂ + P) z w = _
    rw [RectangleBorderIntegrable.add hi₂ hiP, smul_add]
    show RectangleIntegral' f₂ z w + RectangleIntegral' P z w = _
    rw [ih', ResidueTheoremInRectangle hre him hp, add_comm]
