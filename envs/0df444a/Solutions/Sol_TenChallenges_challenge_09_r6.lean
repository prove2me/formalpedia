-- Prove2me | solution 1 for TenChallenges.challenge_09_r6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T02:32:10.64852+00:00
-- url     : https://prove2.me/submissions/a3132f03-8a06-473c-806c-2490375a7c47

import Definitions.Def_TenChallenges_Challenge_09
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Union-Closed Sets at Density `3/8` (`r = 6` and `r = 1`) via Shannon Entropy

Every nondegenerate finite union-closed family `F` contains an element of density
at least `3/8 = 1/2 - 1/(6 + 2)` (Gilmer 2022; Chase–Lovett 2022; Boppana 2023;
Sawin 2022). In particular this establishes `statement_09 6` and `statement_09 1`
(and indeed `statement_09 r` for every `r ≤ 6`).

## Proof outline
1. **Boppana's one-variable inequality** (`boppana_one_var`):
   For `φ = (1 + √5)/2` and `h(p) = -p log p - (1 - p) log(1 - p)`, every
   `x ∈ [0, 1]` satisfies `φ x h(x) ≤ h(x²)`. We compute three explicit
   derivatives `f₁, f₂, f₃` of `f₀(x) = h(x²) - φ x h(x)` on `(0, 1)`; `f₃(x)` is
   rational with cubic numerator `N(x) = -φ x³ - 4 x² + 3 φ x + (2 φ - 4)`, while
   `f₀(0) = f₀(1/φ) = f₀(1) = f₁(0) = f₁(1/φ) = 0`. A hypothetical point
   `x* ∈ (0, 1)` with `f₀(x*) < 0` forces `N` to alternate signs three times via
   the Mean Value Theorem, contradicting the third divided difference of `N`
   (`cubic_no_sign_alt`).
2. **Two-variable product inequality** (`boppana_two_var`):
   The function `F(u) = e^u h(e^{-u})` has `F''(u) ≤ 0` on `(0, ∞)` by
   `Real.log_le_sub_one_of_pos`, hence is midpoint-concave. Combining midpoint
   concavity at `(u + v)/2` with `boppana_one_var` yields
   `(φ / 2) (y h(x) + x h(y)) ≤ h(x y)` for all `x, y ∈ [0, 1]`.
3. **Finite subset-projection chain rule** (`entC_ge_mul_entA`):
   For uniform independent `A, B ∈ F` and any `S : Finset U`, inducting on `S`
   via the superadditivity of `twoEnt a b = a.negMulLog + b.negMulLog - (a+b).negMulLog`
   shows `M · H(A ∩ S) ≤ H((A ∪ B) ∩ S)` whenever `φ (1 - d(x)) ≥ M` for all `x ∈ S`.
4. **Conclusion**:
   On `S = F.biUnion id`, if every `x` had `density F x < 3/8`, then for `|F| ≥ 2`
   we get `(5 φ / 8) log |F| ≤ H(A ∪ B) ≤ log |F|` with `5 φ / 8 > 1` and
   `log |F| > 0`, contradiction.
-/

set_option autoImplicit false
set_option linter.all false

namespace TenChallenges.Challenge09R6

/-! ## Section 1: Analytic Entropy Inequalities -/

/-- Binary Shannon entropy (in nats), equal to `0` at `0` and `1`. -/
noncomputable def binEnt (p : ℝ) : ℝ :=
  Real.negMulLog p + Real.negMulLog (1 - p)

@[simp] lemma binEnt_zero : binEnt 0 = 0 := by simp [binEnt]
@[simp] lemma binEnt_one : binEnt 1 = 0 := by simp [binEnt]

lemma binEnt_symm (p : ℝ) : binEnt (1 - p) = binEnt p := by
  unfold binEnt; ring_nf

lemma binEnt_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binEnt p :=
  add_nonneg (Real.negMulLog_nonneg hp0 hp1)
    (Real.negMulLog_nonneg (sub_nonneg.mpr hp1) (by linarith))

lemma continuous_binEnt : Continuous binEnt :=
  Real.continuous_negMulLog.add (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id))

/-- Golden ratio `φ = (1 + √5) / 2` and its reciprocal `r₀ = (√5 - 1) / 2`. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2
noncomputable def r0 : ℝ := (Real.sqrt 5 - 1) / 2

lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma sqrt5_bounds : (11 / 5 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 9 / 4 := by
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsq := sqrt5_sq
  constructor <;> nlinarith

lemma phi_bounds : (8 / 5 : ℝ) < phi ∧ phi < 13 / 8 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  unfold phi
  constructor <;> linarith

lemma r0_mem_Ioo : 0 < r0 ∧ r0 < 1 := by
  obtain ⟨h1, h2⟩ := sqrt5_bounds
  unfold r0
  constructor <;> linarith

lemma r0_sq_eq : r0 ^ 2 = 1 - r0 := by
  unfold r0; nlinarith [sqrt5_sq]

lemma phi_mul_r0 : phi * r0 = 1 := by
  unfold phi r0; nlinarith [sqrt5_sq]

/-- Lagrange's Mean Value Theorem deduced directly from Rolle's theorem. -/
private lemma exists_hasDerivAt_eq_slope {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a) := by
  let m : ℝ := (f b - f a) / (b - a)
  let g : ℝ → ℝ := fun x => f x - m * (x - a)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hgc : ContinuousOn g (Set.Icc a b) :=
    hfc.sub (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  have hgab : g a = g b := by
    dsimp [g, m]
    rw [sub_self, mul_zero, sub_zero, div_mul_cancel₀ _ hba]
    ring
  have hgd : ∀ x ∈ Set.Ioo a b, HasDerivAt g (f' x - m) x := by
    intro x hx
    have hlin : HasDerivAt (fun t => m * (t - a)) m x := by
      simpa using ((hasDerivAt_id x).sub_const a).const_mul m
    exact (hfd x hx).sub hlin
  obtain ⟨c, hc, hcz⟩ := exists_hasDerivAt_eq_zero hab hgc hgab hgd
  exact ⟨c, hc, sub_eq_zero.mp hcz⟩

/-- Third divided difference contradiction: a cubic `A x³ + B x² + C x + D` with `A < 0`
cannot satisfy `N(0) < 0 ≤ N(c₀)`, `N(c₁) < 0 < N(c₂)` for `0 < c₀ < c₁ < c₂`. -/
private lemma cubic_no_sign_alt {A B C D c₀ c₁ c₂ : ℝ}
    (hA : A < 0) (hc₀ : 0 < c₀) (hc₀₁ : c₀ < c₁) (hc₁₂ : c₁ < c₂)
    (h0 : D < 0)
    (h1 : 0 ≤ A * c₀ ^ 3 + B * c₀ ^ 2 + C * c₀ + D)
    (h2 : A * c₁ ^ 3 + B * c₁ ^ 2 + C * c₁ + D < 0)
    (h3 : 0 < A * c₂ ^ 3 + B * c₂ ^ 2 + C * c₂ + D) : False := by
  let N : ℝ → ℝ := fun x => A * x ^ 3 + B * x ^ 2 + C * x + D
  have d1_pos : 0 < (N c₀ - N 0) / c₀ :=
    div_pos (by dsimp [N]; linarith) hc₀
  have d2_neg : (N c₁ - N c₀) / (c₁ - c₀) < 0 :=
    div_neg_of_neg_of_pos (by dsimp [N]; linarith) (sub_pos.mpr hc₀₁)
  have d3_pos : 0 < (N c₂ - N c₁) / (c₂ - c₁) :=
    div_pos (by dsimp [N]; linarith) (sub_pos.mpr hc₁₂)
  have hd1 : (N c₀ - N 0) / c₀ = A * c₀ ^ 2 + B * c₀ + C := by
    dsimp [N]; field_simp [hc₀.ne']; ring
  have hd2 : (N c₁ - N c₀) / (c₁ - c₀) =
      A * (c₁ ^ 2 + c₁ * c₀ + c₀ ^ 2) + B * (c₁ + c₀) + C := by
    have hne : c₁ - c₀ ≠ 0 := (sub_pos.mpr hc₀₁).ne'
    dsimp [N]; field_simp [hne]; ring
  have hd3 : (N c₂ - N c₁) / (c₂ - c₁) =
      A * (c₂ ^ 2 + c₂ * c₁ + c₁ ^ 2) + B * (c₂ + c₁) + C := by
    have hne : c₂ - c₁ ≠ 0 := (sub_pos.mpr hc₁₂).ne'
    dsimp [N]; field_simp [hne]; ring
  have hc₁_pos : 0 < c₁ := hc₀.trans hc₀₁
  have hc₂₀_pos : 0 < c₂ - c₀ := sub_pos.mpr (hc₀₁.trans hc₁₂)
  have e1_neg : ((N c₁ - N c₀) / (c₁ - c₀) - (N c₀ - N 0) / c₀) / c₁ < 0 :=
    div_neg_of_neg_of_pos (by linarith) hc₁_pos
  have e2_pos : 0 < ((N c₂ - N c₁) / (c₂ - c₁) - (N c₁ - N c₀) / (c₁ - c₀)) / (c₂ - c₀) :=
    div_pos (by linarith) hc₂₀_pos
  have he1 : ((N c₁ - N c₀) / (c₁ - c₀) - (N c₀ - N 0) / c₀) / c₁ =
      A * (c₁ + c₀) + B := by
    rw [hd1, hd2]; field_simp [hc₁_pos.ne']; ring
  have he2 : ((N c₂ - N c₁) / (c₂ - c₁) - (N c₁ - N c₀) / (c₁ - c₀)) / (c₂ - c₀) =
      A * (c₂ + c₁ + c₀) + B := by
    rw [hd2, hd3]; field_simp [hc₂₀_pos.ne']; ring
  rw [he1] at e1_neg
  rw [he2] at e2_pos
  have hc₂_pos : 0 < c₂ := hc₁_pos.trans hc₁₂
  have hAc₂ : A * c₂ < 0 := mul_neg_of_neg_of_pos hA hc₂_pos
  linarith

private noncomputable def f0 (x : ℝ) : ℝ :=
  binEnt (x ^ 2) - phi * x * binEnt x

private noncomputable def f1 (x : ℝ) : ℝ :=
  (2 * phi - 4) * (x * Real.log x) + 2 * x * Real.log (1 - x ^ 2) -
    phi * (2 * x - 1) * Real.log (1 - x)

private noncomputable def f2 (x : ℝ) : ℝ :=
  (2 * phi - 4) * Real.log x + (2 - 2 * phi) * Real.log (1 - x) + 2 * Real.log (1 + x) +
    (phi - 2) * (1 - x)⁻¹ - 2 * (1 + x)⁻¹

private noncomputable def cubN (x : ℝ) : ℝ :=
  -phi * x ^ 3 - 4 * x ^ 2 + 3 * phi * x + (2 * phi - 4)

private noncomputable def f3 (x : ℝ) : ℝ :=
  cubN x / (x * (1 - x ^ 2) ^ 2)

private lemma continuous_f0 : Continuous f0 :=
  (continuous_binEnt.comp (continuous_pow 2)).sub
    ((continuous_const.mul continuous_id).mul continuous_binEnt)

private lemma continuousOn_f1_Icc {a b : ℝ} (ha : 0 ≤ a) (hb : b < 1) :
    ContinuousOn f1 (Set.Icc a b) := by
  unfold f1
  have h1 : ContinuousOn (fun x => (2 * phi - 4) * (x * Real.log x)) (Set.Icc a b) :=
    continuousOn_const.mul Real.continuous_mul_log.continuousOn
  have h2 : ContinuousOn (fun x => 2 * x * Real.log (1 - x ^ 2)) (Set.Icc a b) := by
    refine (continuousOn_const.mul continuousOn_id).mul
      ((continuousOn_const.sub (continuous_pow 2).continuousOn).log fun x hx => ?_)
    have hx0 : 0 ≤ x := ha.trans hx.1
    have hx1 : x < 1 := hx.2.trans_lt hb
    dsimp
    nlinarith
  have h3 : ContinuousOn (fun x => phi * (2 * x - 1) * Real.log (1 - x)) (Set.Icc a b) := by
    refine (continuousOn_const.mul ((continuousOn_const.mul continuousOn_id).sub continuousOn_const)).mul
      ((continuousOn_const.sub continuousOn_id).log fun x hx => ?_)
    dsimp
    linarith [hx.2, hb]
  exact (h1.add h2).sub h3

private lemma continuousOn_f2_Icc {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ContinuousOn f2 (Set.Icc a b) := by
  unfold f2
  have hx_ne : ∀ x ∈ Set.Icc a b, x ≠ 0 := fun x hx => (ha.trans_le hx.1).ne'
  have h1x_ne : ∀ x ∈ Set.Icc a b, 1 - x ≠ 0 := fun x hx => by linarith [hx.2, hb]
  have h1px_ne : ∀ x ∈ Set.Icc a b, 1 + x ≠ 0 := fun x hx => by linarith [ha, hx.1]
  have c1 : ContinuousOn (fun x => (2 * phi - 4) * Real.log x) (Set.Icc a b) :=
    continuousOn_const.mul (continuousOn_id.log hx_ne)
  have c2 : ContinuousOn (fun x => (2 - 2 * phi) * Real.log (1 - x)) (Set.Icc a b) :=
    continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).log h1x_ne)
  have c3 : ContinuousOn (fun x => 2 * Real.log (1 + x)) (Set.Icc a b) :=
    continuousOn_const.mul ((continuousOn_const.add continuousOn_id).log h1px_ne)
  have c4 : ContinuousOn (fun x => (phi - 2) * (1 - x)⁻¹) (Set.Icc a b) :=
    continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).inv₀ h1x_ne)
  have c5 : ContinuousOn (fun x => 2 * (1 + x)⁻¹) (Set.Icc a b) :=
    continuousOn_const.mul ((continuousOn_const.add continuousOn_id).inv₀ h1px_ne)
  exact (((c1.add c2).add c3).add c4).sub c5

private lemma hasDerivAt_f0 {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : HasDerivAt f0 (f1 x) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hx2_pos : 0 < x ^ 2 := sq_pos_of_pos hx0
  have h1x_pos : 0 < 1 - x := sub_pos.mpr hx1
  have h1x2_pos : 0 < 1 - x ^ 2 := by nlinarith
  have d_sq : HasDerivAt (fun t : ℝ => t ^ 2) ((2 : ℕ) * x ^ (2 - 1)) x :=
    hasDerivAt_pow 2 x
  have d_1sq : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (0 - ((2 : ℕ) * x ^ (2 - 1))) x :=
    (hasDerivAt_const x (1 : ℝ)).sub d_sq
  have d_1t : HasDerivAt (fun t : ℝ => 1 - t) (0 - 1) x :=
    (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have hnml1 : HasDerivAt Real.negMulLog (-Real.log (x ^ 2) - 1) ((fun t : ℝ => t ^ 2) x) :=
    Real.hasDerivAt_negMulLog hx2_pos.ne'
  have hnml2 : HasDerivAt Real.negMulLog (-Real.log (1 - x ^ 2) - 1) ((fun t : ℝ => 1 - t ^ 2) x) :=
    Real.hasDerivAt_negMulLog h1x2_pos.ne'
  have hnml3 : HasDerivAt Real.negMulLog (-Real.log (1 - x) - 1) ((fun t : ℝ => 1 - t) x) :=
    Real.hasDerivAt_negMulLog h1x_pos.ne'
  have d_h_sq : HasDerivAt (fun t => binEnt (t ^ 2))
      ((-Real.log (x ^ 2) - 1) * ((2 : ℕ) * x ^ (2 - 1)) +
        (-Real.log (1 - x ^ 2) - 1) * (0 - ((2 : ℕ) * x ^ (2 - 1)))) x :=
    (hnml1.comp x (h := fun t : ℝ => t ^ 2) d_sq).add
      (hnml2.comp x (h₂ := Real.negMulLog) (h := fun t : ℝ => 1 - t ^ 2) d_1sq)
  have d_h : HasDerivAt binEnt ((-Real.log x - 1) + (-Real.log (1 - x) - 1) * (0 - 1)) x :=
    (Real.hasDerivAt_negMulLog hx0.ne').add (hnml3.comp x d_1t)
  have d_phix : HasDerivAt (fun t => phi * t) (phi * 1) x :=
    (hasDerivAt_id x).const_mul phi
  have d_tot := d_h_sq.sub (d_phix.mul d_h)
  refine d_tot.congr_deriv ?_
  unfold f1 binEnt Real.negMulLog
  have hlog2 : Real.log (x ^ 2) = 2 * Real.log x := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlog2]
  push_cast
  ring

private lemma hasDerivAt_f1 {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : HasDerivAt f1 (f2 x) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have h1x_pos : 0 < 1 - x := sub_pos.mpr hx1
  have h1px_pos : 0 < 1 + x := by linarith
  have h1x2_pos : 0 < 1 - x ^ 2 := by nlinarith
  have d1 : HasDerivAt (fun t => (2 * phi - 4) * (t * Real.log t))
      ((2 * phi - 4) * (Real.log x + 1)) x :=
    (Real.hasDerivAt_mul_log hx0.ne').const_mul (2 * phi - 4)
  have d_1sq : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (0 - ((2 : ℕ) * x ^ (2 - 1))) x :=
    (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)
  have dlog_1sq : HasDerivAt Real.log (1 - x ^ 2)⁻¹ ((fun t : ℝ => 1 - t ^ 2) x) :=
    Real.hasDerivAt_log h1x2_pos.ne'
  have d2 : HasDerivAt (fun t => 2 * t * Real.log (1 - t ^ 2))
      ((2 * 1) * Real.log (1 - x ^ 2) + 2 * x * ((1 - x ^ 2)⁻¹ * (0 - ((2 : ℕ) * x ^ (2 - 1))))) x := by
    have dl := dlog_1sq.comp x d_1sq
    have dm : HasDerivAt (fun t => 2 * t) (2 * 1) x := (hasDerivAt_id x).const_mul 2
    exact dm.mul dl
  have d_1t : HasDerivAt (fun t : ℝ => 1 - t) (0 - 1) x :=
    (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have dlog_1t : HasDerivAt Real.log (1 - x)⁻¹ ((fun t : ℝ => 1 - t) x) :=
    Real.hasDerivAt_log h1x_pos.ne'
  have d3 : HasDerivAt (fun t => phi * (2 * t - 1) * Real.log (1 - t))
      ((phi * (2 * 1)) * Real.log (1 - x) + phi * (2 * x - 1) * ((1 - x)⁻¹ * (0 - 1))) x := by
    have dl := dlog_1t.comp x d_1t
    have dm : HasDerivAt (fun t => phi * (2 * t - 1)) (phi * (2 * 1)) x :=
      (((hasDerivAt_id x).const_mul 2).sub_const 1).const_mul phi
    exact dm.mul dl
  refine ((d1.add d2).sub d3).congr_deriv ?_
  unfold f2
  have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
  have hlog : Real.log (1 - x ^ 2) = Real.log (1 - x) + Real.log (1 + x) := by
    rw [hfac, Real.log_mul h1x_pos.ne' h1px_pos.ne']
  rw [hlog, hfac]
  push_cast
  field_simp [h1x_pos.ne', h1px_pos.ne']
  ring

private lemma hasDerivAt_f2 {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) : HasDerivAt f2 (f3 x) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have h1x_pos : 0 < 1 - x := sub_pos.mpr hx1
  have h1px_pos : 0 < 1 + x := by linarith
  have d_1t : HasDerivAt (fun t : ℝ => 1 - t) (0 - 1) x :=
    (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  have d_1pt : HasDerivAt (fun t : ℝ => 1 + t) (0 + 1) x :=
    (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
  have dlog_1t : HasDerivAt Real.log (1 - x)⁻¹ ((fun t : ℝ => 1 - t) x) :=
    Real.hasDerivAt_log h1x_pos.ne'
  have dlog_1pt : HasDerivAt Real.log (1 + x)⁻¹ ((fun t : ℝ => 1 + t) x) :=
    Real.hasDerivAt_log h1px_pos.ne'
  have dinv_1t : HasDerivAt Inv.inv (-((1 - x) ^ 2)⁻¹) ((fun t : ℝ => 1 - t) x) :=
    hasDerivAt_inv h1x_pos.ne'
  have dinv_1pt : HasDerivAt Inv.inv (-((1 + x) ^ 2)⁻¹) ((fun t : ℝ => 1 + t) x) :=
    hasDerivAt_inv h1px_pos.ne'
  have d1 := (Real.hasDerivAt_log hx0.ne').const_mul (2 * phi - 4)
  have d2 := (dlog_1t.comp x d_1t).const_mul (2 - 2 * phi)
  have d3 := (dlog_1pt.comp x d_1pt).const_mul 2
  have d4 := (dinv_1t.comp x d_1t).const_mul (phi - 2)
  have d5 := (dinv_1pt.comp x d_1pt).const_mul 2
  refine ((((d1.add d2).add d3).add d4).sub d5).congr_deriv ?_
  unfold f3 cubN
  have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
  rw [hfac]
  field_simp [hx0.ne', h1x_pos.ne', h1px_pos.ne']
  ring

private lemma f0_special_values : f0 0 = 0 ∧ f0 1 = 0 ∧ f0 r0 = 0 ∧ f1 0 = 0 ∧ f1 r0 = 0 := by
  refine ⟨by simp [f0], by simp [f0], ?_, by simp [f1], ?_⟩
  · unfold f0
    rw [r0_sq_eq, binEnt_symm, phi_mul_r0, one_mul, sub_self]
  · unfold f1
    have hr0_pos : 0 < r0 := r0_mem_Ioo.1
    have h1 : 1 - r0 ^ 2 = r0 := by linarith [r0_sq_eq]
    have h2 : 1 - r0 = r0 ^ 2 := r0_sq_eq.symm
    have hlog2 : Real.log (r0 ^ 2) = 2 * Real.log r0 := by
      rw [Real.log_pow]; push_cast; ring
    have hphi_sub : phi - 1 = r0 := by unfold phi r0; ring
    rw [h1, h2, hlog2]
    have hcoef : (2 * phi - 4) * r0 + 2 * r0 - phi * (2 * r0 - 1) * 2 = 0 := by
      nlinarith [phi_mul_r0, hphi_sub]
    calc (2 * phi - 4) * (r0 * Real.log r0) + 2 * r0 * Real.log r0 -
            phi * (2 * r0 - 1) * (2 * Real.log r0)
        = ((2 * phi - 4) * r0 + 2 * r0 - phi * (2 * r0 - 1) * 2) * Real.log r0 := by ring
      _ = 0 := by rw [hcoef, zero_mul]

/-- **Boppana's one-variable inequality**: `φ x h(x) ≤ h(x²)` for all `x ∈ [0, 1]`. -/
theorem boppana_one_var {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    phi * x * binEnt x ≤ binEnt (x ^ 2) := by
  suffices h : 0 ≤ f0 x by unfold f0 at h; linarith
  obtain ⟨hf0_0, hf0_1, hf0_r0, hf1_0, hf1_r0⟩ := f0_special_values
  obtain ⟨hr0_0, hr0_1⟩ := r0_mem_Ioo
  obtain ⟨hphi_lo, hphi_hi⟩ := phi_bounds
  by_contra hneg
  push Not at hneg
  have hx_pos : 0 < x := by
    rcases eq_or_lt_of_le hx0 with rfl | h
    · linarith
    · exact h
  have hx_lt1 : x < 1 := by
    rcases eq_or_lt_of_le hx1 with rfl | h
    · linarith
    · exact h
  have hx_ne_r0 : x ≠ r0 := fun e => by subst e; linarith
  -- Helper extracting sign of cubN from sign of f3 on (0, 1)
  have pos_denom : ∀ c ∈ Set.Ioo (0 : ℝ) 1, 0 < c * (1 - c ^ 2) ^ 2 := by
    intro c hc
    have h1c : 0 < 1 - c ^ 2 := by nlinarith [hc.1, hc.2]
    exact mul_pos hc.1 (sq_pos_of_pos h1c)
  rcases lt_or_gt_of_ne hx_ne_r0 with hxl | hxr
  · -- Case 1: 0 < x < r0
    obtain ⟨a₁, ha₁, ha₁_eq⟩ := exists_hasDerivAt_eq_slope hx_pos
      continuous_f0.continuousOn (fun t ht => hasDerivAt_f0 ⟨ht.1, ht.2.trans (hxl.trans hr0_1)⟩)
    obtain ⟨a₂, ha₂, ha₂_eq⟩ := exists_hasDerivAt_eq_slope hxl
      continuous_f0.continuousOn (fun t ht => hasDerivAt_f0 ⟨hx_pos.trans ht.1, ht.2.trans hr0_1⟩)
    obtain ⟨a₃, ha₃, ha₃_eq⟩ := exists_hasDerivAt_eq_slope hr0_1
      continuous_f0.continuousOn (fun t ht => hasDerivAt_f0 ⟨hr0_0.trans ht.1, ht.2⟩)
    have ha₁_neg : f1 a₁ < 0 := by
      rw [ha₁_eq, hf0_0, sub_zero, sub_zero]; exact div_neg_of_neg_of_pos hneg hx_pos
    have ha₂_pos : 0 < f1 a₂ := by
      rw [ha₂_eq, hf0_r0, zero_sub]; exact div_pos (neg_pos.mpr hneg) (sub_pos.mpr hxl)
    have ha₃_zero : f1 a₃ = 0 := by
      rw [ha₃_eq, hf0_1, hf0_r0, sub_self, zero_div]
    have ha₁₂ : a₁ < a₂ := ha₁.2.trans ha₂.1
    have ha₂r : a₂ < r0 := ha₂.2
    have hr₃ : r0 < a₃ := ha₃.1
    obtain ⟨b₀, hb₀, hb₀_eq⟩ := exists_hasDerivAt_eq_slope ha₁.1
      (continuousOn_f1_Icc le_rfl (ha₁₂.trans (ha₂r.trans hr0_1)))
      (fun t ht => hasDerivAt_f1 ⟨ht.1, ht.2.trans (ha₁₂.trans (ha₂r.trans hr0_1))⟩)
    obtain ⟨b₁, hb₁, hb₁_eq⟩ := exists_hasDerivAt_eq_slope ha₁₂
      (continuousOn_f1_Icc ha₁.1.le (ha₂r.trans hr0_1))
      (fun t ht => hasDerivAt_f1 ⟨ha₁.1.trans ht.1, ht.2.trans (ha₂r.trans hr0_1)⟩)
    obtain ⟨b₂, hb₂, hb₂_eq⟩ := exists_hasDerivAt_eq_slope ha₂r
      (continuousOn_f1_Icc (ha₁.1.trans ha₁₂).le hr0_1)
      (fun t ht => hasDerivAt_f1 ⟨(ha₁.1.trans ha₁₂).trans ht.1, ht.2.trans hr0_1⟩)
    obtain ⟨b₃, hb₃, hb₃_eq⟩ := exists_hasDerivAt_eq_slope hr₃
      (continuousOn_f1_Icc hr0_0.le ha₃.2)
      (fun t ht => hasDerivAt_f1 ⟨hr0_0.trans ht.1, ht.2.trans ha₃.2⟩)
    have hb₀_neg : f2 b₀ < 0 := by
      rw [hb₀_eq, hf1_0, sub_zero, sub_zero]; exact div_neg_of_neg_of_pos ha₁_neg ha₁.1
    have hb₁_pos : 0 < f2 b₁ := by
      rw [hb₁_eq]; exact div_pos (by linarith) (sub_pos.mpr ha₁₂)
    have hb₂_neg : f2 b₂ < 0 := by
      rw [hb₂_eq, hf1_r0]; exact div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr ha₂r)
    have hb₃_zero : f2 b₃ = 0 := by
      rw [hb₃_eq, ha₃_zero, hf1_r0, sub_self, zero_div]
    have hb₀₁ : b₀ < b₁ := hb₀.2.trans hb₁.1
    have hb₁₂ : b₁ < b₂ := hb₁.2.trans hb₂.1
    have hb₂₃ : b₂ < b₃ := hb₂.2.trans hb₃.1
    have hb₃_lt1 : b₃ < 1 := hb₃.2.trans ha₃.2
    obtain ⟨c₀, hc₀, hc₀_eq⟩ := exists_hasDerivAt_eq_slope hb₀₁
      (continuousOn_f2_Icc hb₀.1 ((hb₁₂.trans hb₂₃).trans hb₃_lt1))
      (fun t ht => hasDerivAt_f2 ⟨hb₀.1.trans ht.1, ht.2.trans ((hb₁₂.trans hb₂₃).trans hb₃_lt1)⟩)
    obtain ⟨c₁, hc₁, hc₁_eq⟩ := exists_hasDerivAt_eq_slope hb₁₂
      (continuousOn_f2_Icc (hb₀.1.trans hb₀₁) (hb₂₃.trans hb₃_lt1))
      (fun t ht => hasDerivAt_f2 ⟨(hb₀.1.trans hb₀₁).trans ht.1, ht.2.trans (hb₂₃.trans hb₃_lt1)⟩)
    obtain ⟨c₂, hc₂, hc₂_eq⟩ := exists_hasDerivAt_eq_slope hb₂₃
      (continuousOn_f2_Icc ((hb₀.1.trans hb₀₁).trans hb₁₂) hb₃_lt1)
      (fun t ht => hasDerivAt_f2 ⟨((hb₀.1.trans hb₀₁).trans hb₁₂).trans ht.1, ht.2.trans hb₃_lt1⟩)
    have hc₀_pos : 0 < f3 c₀ := by
      rw [hc₀_eq]; exact div_pos (by linarith) (sub_pos.mpr hb₀₁)
    have hc₁_neg : f3 c₁ < 0 := by
      rw [hc₁_eq]; exact div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr hb₁₂)
    have hc₂_pos : 0 < f3 c₂ := by
      rw [hc₂_eq]; exact div_pos (by linarith) (sub_pos.mpr hb₂₃)
    have hc₀_Ioo : c₀ ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hb₀.1.trans hc₀.1, hc₀.2.trans ((hb₁₂.trans hb₂₃).trans hb₃_lt1)⟩
    have hc₁_Ioo : c₁ ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨(hb₀.1.trans hb₀₁).trans hc₁.1, hc₁.2.trans (hb₂₃.trans hb₃_lt1)⟩
    have hc₂_Ioo : c₂ ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨((hb₀.1.trans hb₀₁).trans hb₁₂).trans hc₂.1, hc₂.2.trans hb₃_lt1⟩
    have hN₀ : 0 ≤ cubN c₀ := by
      unfold f3 at hc₀_pos
      exact (div_pos_iff_of_pos_right (pos_denom c₀ hc₀_Ioo)).mp hc₀_pos |>.le
    have hN₁ : cubN c₁ < 0 := by
      unfold f3 at hc₁_neg
      exact ((div_neg_iff.mp hc₁_neg).resolve_left
        (fun h => (not_lt_of_ge (pos_denom c₁ hc₁_Ioo).le) h.2)).1
    have hN₂ : 0 < cubN c₂ := by
      unfold f3 at hc₂_pos
      exact (div_pos_iff_of_pos_right (pos_denom c₂ hc₂_Ioo)).mp hc₂_pos
    exact cubic_no_sign_alt (A := -phi) (B := -4) (C := 3 * phi) (D := 2 * phi - 4)
      (by linarith) hc₀_Ioo.1 (hc₀.2.trans hc₁.1) (hc₁.2.trans hc₂.1)
      (by linarith)
      (by simpa only [cubN, sub_eq_add_neg, neg_mul] using hN₀)
      (by simpa only [cubN, sub_eq_add_neg, neg_mul] using hN₁)
      (by simpa only [cubN, sub_eq_add_neg, neg_mul] using hN₂)
  · -- Case 2: r0 < x < 1
    obtain ⟨a₁, ha₁, ha₁_eq⟩ := exists_hasDerivAt_eq_slope hr0_0
      continuous_f0.continuousOn (fun t ht => hasDerivAt_f0 ⟨ht.1, ht.2.trans hr0_1⟩)
    obtain ⟨a₂, ha₂, ha₂_eq⟩ := exists_hasDerivAt_eq_slope hxr
      continuous_f0.continuousOn (fun t ht => hasDerivAt_f0 ⟨hr0_0.trans ht.1, ht.2.trans hx_lt1⟩)
    obtain ⟨a₃, ha₃, ha₃_eq⟩ := exists_hasDerivAt_eq_slope hx_lt1
      continuous_f0.continuousOn (fun t ht => hasDerivAt_f0 ⟨hx_pos.trans ht.1, ht.2⟩)
    have ha₁_zero : f1 a₁ = 0 := by
      rw [ha₁_eq, hf0_r0, hf0_0, sub_self, zero_div]
    have ha₂_neg : f1 a₂ < 0 := by
      rw [ha₂_eq, hf0_r0, sub_zero]; exact div_neg_of_neg_of_pos hneg (sub_pos.mpr hxr)
    have ha₃_pos : 0 < f1 a₃ := by
      rw [ha₃_eq, hf0_1, zero_sub]; exact div_pos (neg_pos.mpr hneg) (sub_pos.mpr hx_lt1)
    have ha₁r : a₁ < r0 := ha₁.2
    have hr₂ : r0 < a₂ := ha₂.1
    have ha₂₃ : a₂ < a₃ := ha₂.2.trans ha₃.1
    obtain ⟨b₀, hb₀, hb₀_eq⟩ := exists_hasDerivAt_eq_slope ha₁.1
      (continuousOn_f1_Icc le_rfl (ha₁r.trans hr0_1))
      (fun t ht => hasDerivAt_f1 ⟨ht.1, ht.2.trans (ha₁r.trans hr0_1)⟩)
    obtain ⟨b₁, hb₁, hb₁_eq⟩ := exists_hasDerivAt_eq_slope ha₁r
      (continuousOn_f1_Icc ha₁.1.le hr0_1)
      (fun t ht => hasDerivAt_f1 ⟨ha₁.1.trans ht.1, ht.2.trans hr0_1⟩)
    obtain ⟨b₂, hb₂, hb₂_eq⟩ := exists_hasDerivAt_eq_slope hr₂
      (continuousOn_f1_Icc hr0_0.le (ha₂₃.trans ha₃.2))
      (fun t ht => hasDerivAt_f1 ⟨hr0_0.trans ht.1, ht.2.trans (ha₂₃.trans ha₃.2)⟩)
    obtain ⟨b₃, hb₃, hb₃_eq⟩ := exists_hasDerivAt_eq_slope ha₂₃
      (continuousOn_f1_Icc (hr0_0.trans hr₂).le ha₃.2)
      (fun t ht => hasDerivAt_f1 ⟨(hr0_0.trans hr₂).trans ht.1, ht.2.trans ha₃.2⟩)
    have hb₀_zero : f2 b₀ = 0 := by
      rw [hb₀_eq, ha₁_zero, hf1_0, sub_self, zero_div]
    have hb₁_zero : f2 b₁ = 0 := by
      rw [hb₁_eq, hf1_r0, ha₁_zero, sub_self, zero_div]
    have hb₂_neg : f2 b₂ < 0 := by
      rw [hb₂_eq, hf1_r0, sub_zero]; exact div_neg_of_neg_of_pos ha₂_neg (sub_pos.mpr hr₂)
    have hb₃_pos : 0 < f2 b₃ := by
      rw [hb₃_eq]; exact div_pos (by linarith) (sub_pos.mpr ha₂₃)
    have hb₀₁ : b₀ < b₁ := hb₀.2.trans hb₁.1
    have hb₁₂ : b₁ < b₂ := hb₁.2.trans hb₂.1
    have hb₂₃ : b₂ < b₃ := hb₂.2.trans hb₃.1
    have hb₃_lt1 : b₃ < 1 := hb₃.2.trans ha₃.2
    obtain ⟨c₀, hc₀, hc₀_eq⟩ := exists_hasDerivAt_eq_slope hb₀₁
      (continuousOn_f2_Icc hb₀.1 ((hb₁₂.trans hb₂₃).trans hb₃_lt1))
      (fun t ht => hasDerivAt_f2 ⟨hb₀.1.trans ht.1, ht.2.trans ((hb₁₂.trans hb₂₃).trans hb₃_lt1)⟩)
    obtain ⟨c₁, hc₁, hc₁_eq⟩ := exists_hasDerivAt_eq_slope hb₁₂
      (continuousOn_f2_Icc (hb₀.1.trans hb₀₁) (hb₂₃.trans hb₃_lt1))
      (fun t ht => hasDerivAt_f2 ⟨(hb₀.1.trans hb₀₁).trans ht.1, ht.2.trans (hb₂₃.trans hb₃_lt1)⟩)
    obtain ⟨c₂, hc₂, hc₂_eq⟩ := exists_hasDerivAt_eq_slope hb₂₃
      (continuousOn_f2_Icc ((hb₀.1.trans hb₀₁).trans hb₁₂) hb₃_lt1)
      (fun t ht => hasDerivAt_f2 ⟨((hb₀.1.trans hb₀₁).trans hb₁₂).trans ht.1, ht.2.trans hb₃_lt1⟩)
    have hc₀_zero : f3 c₀ = 0 := by
      rw [hc₀_eq, hb₁_zero, hb₀_zero, sub_self, zero_div]
    have hc₁_neg : f3 c₁ < 0 := by
      rw [hc₁_eq, hb₁_zero, sub_zero]; exact div_neg_of_neg_of_pos hb₂_neg (sub_pos.mpr hb₁₂)
    have hc₂_pos : 0 < f3 c₂ := by
      rw [hc₂_eq]; exact div_pos (by linarith) (sub_pos.mpr hb₂₃)
    have hc₀_Ioo : c₀ ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hb₀.1.trans hc₀.1, hc₀.2.trans ((hb₁₂.trans hb₂₃).trans hb₃_lt1)⟩
    have hc₁_Ioo : c₁ ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨(hb₀.1.trans hb₀₁).trans hc₁.1, hc₁.2.trans (hb₂₃.trans hb₃_lt1)⟩
    have hc₂_Ioo : c₂ ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨((hb₀.1.trans hb₀₁).trans hb₁₂).trans hc₂.1, hc₂.2.trans hb₃_lt1⟩
    have hN₀ : 0 ≤ cubN c₀ := by
      unfold f3 at hc₀_zero
      have hcz : cubN c₀ = 0 := (div_eq_zero_iff.mp hc₀_zero).resolve_right (pos_denom c₀ hc₀_Ioo).ne'
      linarith
    have hN₁ : cubN c₁ < 0 := by
      unfold f3 at hc₁_neg
      exact ((div_neg_iff.mp hc₁_neg).resolve_left
        (fun h => (not_lt_of_ge (pos_denom c₁ hc₁_Ioo).le) h.2)).1
    have hN₂ : 0 < cubN c₂ := by
      unfold f3 at hc₂_pos
      exact (div_pos_iff_of_pos_right (pos_denom c₂ hc₂_Ioo)).mp hc₂_pos
    exact cubic_no_sign_alt (A := -phi) (B := -4) (C := 3 * phi) (D := 2 * phi - 4)
      (by linarith) hc₀_Ioo.1 (hc₀.2.trans hc₁.1) (hc₁.2.trans hc₂.1)
      (by linarith)
      (by simpa only [cubN, sub_eq_add_neg, neg_mul] using hN₀)
      (by simpa only [cubN, sub_eq_add_neg, neg_mul] using hN₁)
      (by simpa only [cubN, sub_eq_add_neg, neg_mul] using hN₂)

/-! ### Midpoint concavity of `u ↦ e^u h(e^{-u})` and the two-variable inequality -/

private noncomputable def expEnt (u : ℝ) : ℝ :=
  u - (Real.exp u - 1) * Real.log (1 - Real.exp (-u))

private noncomputable def expEnt1 (u : ℝ) : ℝ :=
  -Real.exp u * Real.log (1 - Real.exp (-u))

private noncomputable def expEnt2 (u : ℝ) : ℝ :=
  -Real.exp u * (Real.log (1 - Real.exp (-u)) + Real.exp (-u) / (1 - Real.exp (-u)))

private lemma expEnt_eq {u : ℝ} (_hu : 0 < u) :
    expEnt u = Real.exp u * binEnt (Real.exp (-u)) := by
  unfold expEnt binEnt Real.negMulLog
  rw [Real.log_exp]
  have hexp_mul : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc u - (Real.exp u - 1) * Real.log (1 - Real.exp (-u))
      = (Real.exp u * Real.exp (-u)) * u -
          (Real.exp u - Real.exp u * Real.exp (-u)) * Real.log (1 - Real.exp (-u)) := by
        rw [hexp_mul]; ring
    _ = Real.exp u * (-Real.exp (-u) * -u + -(1 - Real.exp (-u)) * Real.log (1 - Real.exp (-u))) := by
        ring

private lemma continuousOn_expEnt {a b : ℝ} (ha : 0 < a) : ContinuousOn expEnt (Set.Icc a b) := by
  unfold expEnt
  refine continuousOn_id.sub ((Real.continuous_exp.continuousOn.sub continuousOn_const).mul ?_)
  refine (continuousOn_const.sub (Real.continuous_exp.comp continuous_neg).continuousOn).log ?_
  intro u hu
  have hlt : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith [hu.1, ha])
  dsimp
  linarith

private lemma continuousOn_expEnt1 {a b : ℝ} (ha : 0 < a) : ContinuousOn expEnt1 (Set.Icc a b) := by
  unfold expEnt1
  refine (Real.continuous_exp.neg).continuousOn.mul ?_
  refine (continuousOn_const.sub (Real.continuous_exp.comp continuous_neg).continuousOn).log ?_
  intro u hu
  have hlt : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith [hu.1, ha])
  dsimp
  linarith

private lemma hasDerivAt_expEnt {u : ℝ} (hu : 0 < u) : HasDerivAt expEnt (expEnt1 u) u := by
  have ht_lt1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1t : 0 < 1 - Real.exp (-u) := sub_pos.mpr ht_lt1
  have dn : HasDerivAt (fun w : ℝ => -w) (-1) u := (hasDerivAt_id u).neg
  have hexp_neg : HasDerivAt Real.exp (Real.exp (-u)) ((fun w : ℝ => -w) u) :=
    Real.hasDerivAt_exp (-u)
  have de : HasDerivAt (fun w : ℝ => Real.exp (-w)) (Real.exp (-u) * (-1)) u :=
    hexp_neg.comp u dn
  have d_em : HasDerivAt (fun w : ℝ => 1 - Real.exp (-w)) (0 - Real.exp (-u) * (-1)) u :=
    (hasDerivAt_const u (1 : ℝ)).sub de
  have dlog_outer : HasDerivAt Real.log (1 - Real.exp (-u))⁻¹ ((fun w : ℝ => 1 - Real.exp (-w)) u) :=
    Real.hasDerivAt_log h1t.ne'
  have d_log := dlog_outer.comp u d_em
  have d_eu1 : HasDerivAt (fun w => Real.exp w - 1) (Real.exp u) u :=
    (Real.hasDerivAt_exp u).sub_const 1
  refine ((hasDerivAt_id u).sub (d_eu1.mul d_log)).congr_deriv ?_
  unfold expEnt1
  dsimp only [Function.comp_apply]
  have hexp_mul : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  field_simp [h1t.ne']
  nlinarith only [hexp_mul]

private lemma hasDerivAt_expEnt1 {u : ℝ} (hu : 0 < u) : HasDerivAt expEnt1 (expEnt2 u) u := by
  have ht_lt1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1t : 0 < 1 - Real.exp (-u) := sub_pos.mpr ht_lt1
  have dn : HasDerivAt (fun w : ℝ => -w) (-1) u := (hasDerivAt_id u).neg
  have hexp_neg : HasDerivAt Real.exp (Real.exp (-u)) ((fun w : ℝ => -w) u) :=
    Real.hasDerivAt_exp (-u)
  have de : HasDerivAt (fun w : ℝ => Real.exp (-w)) (Real.exp (-u) * (-1)) u :=
    hexp_neg.comp u dn
  have d_em : HasDerivAt (fun w : ℝ => 1 - Real.exp (-w)) (0 - Real.exp (-u) * (-1)) u :=
    (hasDerivAt_const u (1 : ℝ)).sub de
  have dlog_outer : HasDerivAt Real.log (1 - Real.exp (-u))⁻¹ ((fun w : ℝ => 1 - Real.exp (-w)) u) :=
    Real.hasDerivAt_log h1t.ne'
  have d_log := dlog_outer.comp u d_em
  refine ((Real.hasDerivAt_exp u).neg.mul d_log).congr_deriv ?_
  unfold expEnt2
  dsimp only [Function.comp_apply, Pi.neg_apply]
  field_simp [h1t.ne']
  ring

private lemma expEnt2_nonpos {u : ℝ} (hu : 0 < u) : expEnt2 u ≤ 0 := by
  unfold expEnt2
  have ht_pos : 0 < Real.exp (-u) := Real.exp_pos (-u)
  have ht_lt1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1t : 0 < 1 - Real.exp (-u) := sub_pos.mpr ht_lt1
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr h1t)
  rw [Real.log_inv] at hlog
  have hinner : 0 ≤ Real.log (1 - Real.exp (-u)) + Real.exp (-u) / (1 - Real.exp (-u)) := by
    have hsub : (1 - Real.exp (-u))⁻¹ - 1 = Real.exp (-u) / (1 - Real.exp (-u)) := by
      field_simp [h1t.ne']; ring
    linarith
  have hexp_pos : 0 ≤ Real.exp u := (Real.exp_pos u).le
  nlinarith

private lemma expEnt_midpoint {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (expEnt u + expEnt v) / 2 ≤ expEnt ((u + v) / 2) := by
  have hord : ∀ {a b : ℝ}, 0 < a → a < b →
      (expEnt a + expEnt b) / 2 ≤ expEnt ((a + b) / 2) := by
    intro a b ha hab
    let m := (a + b) / 2
    have ham : a < m := by dsimp [m]; linarith
    have hmb : m < b := by dsimp [m]; linarith
    obtain ⟨ξ₁, hξ₁, hξ₁_eq⟩ := exists_hasDerivAt_eq_slope ham (continuousOn_expEnt ha)
      (fun w hw => hasDerivAt_expEnt (ha.trans hw.1))
    obtain ⟨ξ₂, hξ₂, hξ₂_eq⟩ := exists_hasDerivAt_eq_slope hmb (continuousOn_expEnt (ha.trans ham))
      (fun w hw => hasDerivAt_expEnt ((ha.trans ham).trans hw.1))
    have hξ₁₂ : ξ₁ < ξ₂ := hξ₁.2.trans hξ₂.1
    have hξ₁_pos : 0 < ξ₁ := ha.trans hξ₁.1
    obtain ⟨η, hη, hη_eq⟩ := exists_hasDerivAt_eq_slope hξ₁₂ (continuousOn_expEnt1 hξ₁_pos)
      (fun w hw => hasDerivAt_expEnt1 (hξ₁_pos.trans hw.1))
    have hη_np : expEnt2 η ≤ 0 := expEnt2_nonpos (hξ₁_pos.trans hη.1)
    have hanti : expEnt1 ξ₂ ≤ expEnt1 ξ₁ := by
      have hd : (expEnt1 ξ₂ - expEnt1 ξ₁) / (ξ₂ - ξ₁) ≤ 0 := hη_eq ▸ hη_np
      have hmul := mul_nonpos_of_nonpos_of_nonneg hd (sub_pos.mpr hξ₁₂).le
      rw [div_mul_cancel₀ _ (sub_pos.mpr hξ₁₂).ne'] at hmul
      linarith
    rw [hξ₁_eq, hξ₂_eq] at hanti
    have hlen : b - m = m - a := by dsimp [m]; ring
    rw [hlen] at hanti
    have hmul := mul_le_mul_of_nonneg_right hanti (sub_pos.mpr ham).le
    rw [div_mul_cancel₀ _ (sub_pos.mpr ham).ne', div_mul_cancel₀ _ (sub_pos.mpr ham).ne'] at hmul
    linarith
  rcases lt_trichotomy u v with huv | rfl | hvu
  · exact hord hu huv
  · ring_nf; exact le_rfl
  · rw [add_comm (expEnt u), add_comm u v]
    exact hord hv hvu

/-- **Boppana's two-variable entropy inequality**:
`(φ / 2) * (y * binEnt x + x * binEnt y) ≤ binEnt (x * y)` for all `x, y ∈ [0, 1]`. -/
theorem boppana_two_var {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (phi / 2) * (y * binEnt x + x * binEnt y) ≤ binEnt (x * y) := by
  have hphi_lt2 : phi < 2 := by linarith [phi_bounds.2]
  rcases eq_or_lt_of_le hx0 with rfl | hx_pos
  · simp
  rcases eq_or_lt_of_le hy0 with rfl | hy_pos
  · simp
  rcases eq_or_lt_of_le hx1 with rfl | hx_lt1
  · simp only [one_mul, binEnt_one, mul_zero, zero_add]
    nlinarith [binEnt_nonneg hy0 hy1]
  rcases eq_or_lt_of_le hy1 with rfl | hy_lt1
  · simp only [mul_one, binEnt_one, mul_zero, add_zero]
    nlinarith [binEnt_nonneg hx0 hx1]
  let u := -Real.log x
  let v := -Real.log y
  have hu : 0 < u := neg_pos.mpr (Real.log_neg hx_pos hx_lt1)
  have hv : 0 < v := neg_pos.mpr (Real.log_neg hy_pos hy_lt1)
  have hmu : Real.exp (-u) = x := by dsimp [u]; rw [neg_neg, Real.exp_log hx_pos]
  have hmv : Real.exp (-v) = y := by dsimp [v]; rw [neg_neg, Real.exp_log hy_pos]
  have heu : Real.exp u = x⁻¹ := by dsimp [u]; rw [Real.exp_neg, Real.exp_log hx_pos]
  have hev : Real.exp v = y⁻¹ := by dsimp [v]; rw [Real.exp_neg, Real.exp_log hy_pos]
  let z := Real.exp (-((u + v) / 2))
  have hz0 : 0 ≤ z := (Real.exp_pos _).le
  have hz1 : z ≤ 1 := (Real.exp_lt_one_iff.mpr (by linarith)).le
  have hz_pos : 0 < z := Real.exp_pos _
  have hz_sq : z ^ 2 = x * y := by
    dsimp [z]
    rw [← Real.exp_nat_mul]
    have hexp_eq : (2 : ℕ) * (-((u + v) / 2)) = (-u) + (-v) := by push_cast; ring
    rw [hexp_eq, Real.exp_add, hmu, hmv]
  have hmid := expEnt_midpoint hu hv
  rw [expEnt_eq hu, expEnt_eq hv, expEnt_eq (by linarith : 0 < (u + v) / 2)] at hmid
  rw [hmu, hmv, heu, hev] at hmid
  have hez : Real.exp ((u + v) / 2) = z⁻¹ := by
    dsimp [z]; rw [Real.exp_neg, inv_inv]
  rw [hez] at hmid
  have h1var := boppana_one_var hz0 hz1
  rw [hz_sq] at h1var
  -- Multiply midpoint inequality by phi * z^2 = phi * x * y > 0
  have hphi_pos : 0 < phi := by linarith [phi_bounds.1]
  have hstep1 : (phi / 2) * (y * binEnt x + x * binEnt y) =
      phi * (x * y) * ((x⁻¹ * binEnt x + y⁻¹ * binEnt y) / 2) := by
    field_simp [hx_pos.ne', hy_pos.ne']
  have hstep2 : phi * (x * y) * (z⁻¹ * binEnt z) = phi * z * binEnt z := by
    rw [← hz_sq]; field_simp [hz_pos.ne']
  calc (phi / 2) * (y * binEnt x + x * binEnt y)
      = phi * (x * y) * ((x⁻¹ * binEnt x + y⁻¹ * binEnt y) / 2) := hstep1
    _ ≤ phi * (x * y) * (z⁻¹ * binEnt z) :=
        mul_le_mul_of_nonneg_left hmid (by positivity)
    _ = phi * z * binEnt z := hstep2
    _ ≤ binEnt (x * y) := h1var

/-! ## Section 2: Finite Entropy Bounds & Superadditivity of `twoEnt` -/

/-- Shannon entropy of any probability distribution on a nonempty `Finset` is at most `log |S|`. -/
lemma entropy_le_log_card {α : Type*} {S : Finset α} (hS : S.Nonempty) {w : α → ℝ}
    (hw_nn : ∀ a ∈ S, 0 ≤ w a) (hw_sum : ∑ a ∈ S, w a = 1) :
    ∑ a ∈ S, Real.negMulLog (w a) ≤ Real.log (S.card : ℝ) := by
  let m : ℝ := S.card
  have hm_pos : 0 < m := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have hpt : ∀ a ∈ S, w a * Real.negMulLog m + m * Real.negMulLog (w a) ≤ 1 - m * w a := by
    intro a ha
    rw [← Real.negMulLog_mul m (w a)]
    exact Real.negMulLog_le_one_sub_self (mul_nonneg hm_pos.le (hw_nn a ha))
  have hsum := Finset.sum_le_sum hpt
  simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum, hw_sum] at hsum
  unfold Real.negMulLog at hsum
  have hlin : m * ∑ a ∈ S, -w a * Real.log (w a) ≤ m * Real.log m := by
    dsimp [m] at hsum ⊢; linarith
  exact le_of_mul_le_mul_left hlin hm_pos

/-- Concavity of binary entropy on `[0, 1]`. -/
lemma concaveOn_binEnt : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) binEnt := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul, binEnt]
  have h1 := Real.concaveOn_negMulLog.2 hx.1 hy.1 ha hb hab
  have hx' : (0 : ℝ) ≤ 1 - x := sub_nonneg.mpr hx.2
  have hy' : (0 : ℝ) ≤ 1 - y := sub_nonneg.mpr hy.2
  have h2 := Real.concaveOn_negMulLog.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h1 h2
  have hlin : a * (1 - x) + b * (1 - y) = 1 - (a * x + b * y) := by
    calc a * (1 - x) + b * (1 - y)
        = (a + b) - (a * x + b * y) := by ring
      _ = 1 - (a * x + b * y) := by rw [hab]
  rw [hlin] at h2
  linarith

/-- Homogeneous conditional-entropy increment `a.negMulLog + b.negMulLog - (a + b).negMulLog`. -/
noncomputable def twoEnt (a b : ℝ) : ℝ :=
  Real.negMulLog a + Real.negMulLog b - Real.negMulLog (a + b)

lemma twoEnt_mul_binEnt (u p : ℝ) :
    twoEnt (u * p) (u * (1 - p)) = u * binEnt p := by
  have hsum : u * p + u * (1 - p) = u := by ring
  unfold twoEnt binEnt
  rw [hsum, Real.negMulLog_mul, Real.negMulLog_mul]
  ring

lemma twoEnt_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ twoEnt a b := by
  by_cases hs : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [twoEnt, ha0, hb0]
  · let s := a + b
    have hs_pos : 0 < s := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
    let p := a / s
    have ha_eq : a = s * p := by dsimp [p]; field_simp [hs_pos.ne']
    have hb_eq : b = s * (1 - p) := by
      have htot : a + b = s := rfl
      linarith [ha_eq]
    have hcalc : twoEnt a b = s * binEnt p := by
      have h := twoEnt_mul_binEnt s p
      rwa [← ha_eq, ← hb_eq] at h
    rw [hcalc]
    exact mul_nonneg hs_pos.le (binEnt_nonneg (div_nonneg ha hs_pos.le)
      ((div_le_one hs_pos).mpr (by linarith [show s = a + b from rfl])))

lemma twoEnt_superadd {a₁ b₁ a₂ b₂ : ℝ}
    (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁) (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂) :
    twoEnt a₁ b₁ + twoEnt a₂ b₂ ≤ twoEnt (a₁ + a₂) (b₁ + b₂) := by
  by_cases hs₁ : a₁ + b₁ = 0
  · have h1 : a₁ = 0 := by linarith
    have h2 : b₁ = 0 := by linarith
    simp [twoEnt, h1, h2]
  by_cases hs₂ : a₂ + b₂ = 0
  · have h1 : a₂ = 0 := by linarith
    have h2 : b₂ = 0 := by linarith
    simp [twoEnt, h1, h2]
  let s₁ := a₁ + b₁
  let s₂ := a₂ + b₂
  have hs₁_pos : 0 < s₁ := lt_of_le_of_ne (add_nonneg ha₁ hb₁) (Ne.symm hs₁)
  have hs₂_pos : 0 < s₂ := lt_of_le_of_ne (add_nonneg ha₂ hb₂) (Ne.symm hs₂)
  have hs_pos : 0 < s₁ + s₂ := add_pos hs₁_pos hs₂_pos
  let p₁ := a₁ / s₁
  let p₂ := a₂ / s₂
  let w₁ := s₁ / (s₁ + s₂)
  let w₂ := s₂ / (s₁ + s₂)
  have hp₁ : p₁ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ha₁ hs₁_pos.le, (div_le_one hs₁_pos).mpr (by linarith [show s₁ = a₁ + b₁ from rfl])⟩
  have hp₂ : p₂ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ha₂ hs₂_pos.le, (div_le_one hs₂_pos).mpr (by linarith [show s₂ = a₂ + b₂ from rfl])⟩
  have hw₁ : 0 ≤ w₁ := div_nonneg hs₁_pos.le hs_pos.le
  have hw₂ : 0 ≤ w₂ := div_nonneg hs₂_pos.le hs_pos.le
  have hw_sum : w₁ + w₂ = 1 := by dsimp [w₁, w₂]; field_simp [hs_pos.ne']
  have hconc := concaveOn_binEnt.2 hp₁ hp₂ hw₁ hw₂ hw_sum
  simp only [smul_eq_mul] at hconc
  have heq1 : twoEnt a₁ b₁ = s₁ * binEnt p₁ := by
    have ha : a₁ = s₁ * p₁ := by dsimp [p₁]; field_simp [hs₁_pos.ne']
    have hb : b₁ = s₁ * (1 - p₁) := by
      have : a₁ + b₁ = s₁ := rfl
      linarith [ha]
    have h := twoEnt_mul_binEnt s₁ p₁
    rwa [← ha, ← hb] at h
  have heq2 : twoEnt a₂ b₂ = s₂ * binEnt p₂ := by
    have ha : a₂ = s₂ * p₂ := by dsimp [p₂]; field_simp [hs₂_pos.ne']
    have hb : b₂ = s₂ * (1 - p₂) := by
      have : a₂ + b₂ = s₂ := rfl
      linarith [ha]
    have h := twoEnt_mul_binEnt s₂ p₂
    rwa [← ha, ← hb] at h
  let p := w₁ * p₁ + w₂ * p₂
  have hap : a₁ + a₂ = (s₁ + s₂) * p := by
    dsimp [p, w₁, w₂, p₁, p₂]
    field_simp [hs₁_pos.ne', hs₂_pos.ne', hs_pos.ne']
  have hbp : b₁ + b₂ = (s₁ + s₂) * (1 - p) := by
    have htot : (a₁ + a₂) + (b₁ + b₂) = s₁ + s₂ := by dsimp [s₁, s₂]; ring
    linarith [hap]
  have heq12 : twoEnt (a₁ + a₂) (b₁ + b₂) = (s₁ + s₂) * binEnt p := by
    have h := twoEnt_mul_binEnt (s₁ + s₂) p
    rwa [← hap, ← hbp] at h
  rw [heq1, heq2, heq12]
  have hmul := mul_le_mul_of_nonneg_left hconc hs_pos.le
  have hlhs : (s₁ + s₂) * (w₁ * binEnt p₁ + w₂ * binEnt p₂) =
      s₁ * binEnt p₁ + s₂ * binEnt p₂ := by
    dsimp [w₁, w₂]; field_simp [hs_pos.ne']
  linarith

lemma twoEnt_sum_le {ι : Type*} (I : Finset ι) (α β : ι → ℝ)
    (hα : ∀ i ∈ I, 0 ≤ α i) (hβ : ∀ i ∈ I, 0 ≤ β i) :
    ∑ i ∈ I, twoEnt (α i) (β i) ≤ twoEnt (∑ i ∈ I, α i) (∑ i ∈ I, β i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [twoEnt]
  | @insert i₀ J hi₀ ih =>
    rw [Finset.sum_insert hi₀, Finset.sum_insert hi₀, Finset.sum_insert hi₀]
    have hαJ : ∀ j ∈ J, 0 ≤ α j := fun j hj => hα j (Finset.mem_insert_of_mem hj)
    have hβJ : ∀ j ∈ J, 0 ≤ β j := fun j hj => hβ j (Finset.mem_insert_of_mem hj)
    calc twoEnt (α i₀) (β i₀) + ∑ j ∈ J, twoEnt (α j) (β j)
        ≤ twoEnt (α i₀) (β i₀) + twoEnt (∑ j ∈ J, α j) (∑ j ∈ J, β j) := by
          linarith [ih hαJ hβJ]
      _ ≤ twoEnt (α i₀ + ∑ j ∈ J, α j) (β i₀ + ∑ j ∈ J, β j) :=
          twoEnt_superadd (hα i₀ (Finset.mem_insert_self _ _))
            (hβ i₀ (Finset.mem_insert_self _ _))
            (Finset.sum_nonneg hαJ) (Finset.sum_nonneg hβJ)

/-! ## Section 3: Subset-Projected Chain Rule over `F` -/

section ChainRule

variable {U : Type*} [DecidableEq U]

private lemma sum_powerset_insert {S₀ : Finset U} {x : U} (hx : x ∉ S₀) (g : Finset U → ℝ) :
    ∑ T ∈ (insert x S₀).powerset, g T = ∑ T ∈ S₀.powerset, (g T + g (insert x T)) := by
  rw [Finset.powerset_insert, Finset.sum_union]
  · rw [Finset.sum_image]
    · rw [Finset.sum_add_distrib]
    · intro T₁ hT₁ T₂ hT₂ heq
      have hx₁ : x ∉ T₁ := fun h => hx (Finset.mem_powerset.mp hT₁ h)
      have hx₂ : x ∉ T₂ := fun h => hx (Finset.mem_powerset.mp hT₂ h)
      have := congrArg (fun A => A.erase x) heq
      simpa [Finset.erase_insert hx₁, Finset.erase_insert hx₂] using this
  · rw [Finset.disjoint_left]
    intro T hT himg
    obtain ⟨T', _, rfl⟩ := Finset.mem_image.mp himg
    exact hx (Finset.mem_powerset.mp hT (Finset.mem_insert_self x T'))

noncomputable def probA (F : Finset (Finset U)) (S T : Finset U) : ℝ :=
  ((F.filter fun A => A ∩ S = T).card : ℝ) / (F.card : ℝ)

noncomputable def probC (F : Finset (Finset U)) (S R : Finset U) : ℝ :=
  (((F ×ˢ F).filter fun p => (p.1 ∪ p.2) ∩ S = R).card : ℝ) / (F.card : ℝ) ^ 2

noncomputable def entA (F : Finset (Finset U)) (S : Finset U) : ℝ :=
  ∑ T ∈ S.powerset, Real.negMulLog (probA F S T)

noncomputable def entC (F : Finset (Finset U)) (S : Finset U) : ℝ :=
  ∑ R ∈ S.powerset, Real.negMulLog (probC F S R)

noncomputable def occProb (F : Finset (Finset U)) (x : U) : ℝ :=
  (occurrences F x : ℝ) / (F.card : ℝ)

private lemma probA_nonneg (F : Finset (Finset U)) (S T : Finset U) : 0 ≤ probA F S T :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private lemma probC_nonneg (F : Finset (Finset U)) (S R : Finset U) : 0 ≤ probC F S R :=
  div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

private lemma filter_insert_split (F : Finset (Finset U)) {S₀ T : Finset U} {x : U}
    (hx : x ∉ S₀) (hT : T ∈ S₀.powerset) :
    (F.filter fun A => A ∩ insert x S₀ = T).card +
      (F.filter fun A => A ∩ insert x S₀ = insert x T).card =
      (F.filter fun A => A ∩ S₀ = T).card := by
  have hxT : x ∉ T := fun h => hx (Finset.mem_powerset.mp hT h)
  have hdisj : Disjoint (F.filter fun A => A ∩ insert x S₀ = T)
      (F.filter fun A => A ∩ insert x S₀ = insert x T) := by
    rw [Finset.disjoint_filter]
    intro A _ h1 h2
    have hmem : x ∈ T := by rw [← h1, h2]; exact Finset.mem_insert_self x T
    exact hxT hmem
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext A
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hAF, h1⟩ | ⟨hAF, h2⟩)
    · refine ⟨hAF, ?_⟩
      ext y
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hyA, hyS₀⟩
        have : y ∈ A ∩ insert x S₀ := Finset.mem_inter.mpr ⟨hyA, Finset.mem_insert_of_mem hyS₀⟩
        rwa [h1] at this
      · intro hyT
        have hyS₀ : y ∈ S₀ := Finset.mem_powerset.mp hT hyT
        rw [← h1] at hyT
        exact ⟨(Finset.mem_inter.mp hyT).1, hyS₀⟩
    · refine ⟨hAF, ?_⟩
      ext y
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hyA, hyS₀⟩
        have hyx : y ≠ x := fun e => hx (e ▸ hyS₀)
        have : y ∈ A ∩ insert x S₀ := Finset.mem_inter.mpr ⟨hyA, Finset.mem_insert_of_mem hyS₀⟩
        rw [h2, Finset.mem_insert] at this
        exact this.resolve_left hyx
      · intro hyT
        have hyS₀ : y ∈ S₀ := Finset.mem_powerset.mp hT hyT
        have : y ∈ insert x T := Finset.mem_insert_of_mem hyT
        rw [← h2] at this
        exact ⟨(Finset.mem_inter.mp this).1, hyS₀⟩
  · rintro ⟨hAF, hAS₀⟩
    by_cases hxA : x ∈ A
    · right; refine ⟨hAF, ?_⟩
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hyA, rfl | hyS₀⟩
        · exact Or.inl rfl
        · exact Or.inr (hAS₀ ▸ Finset.mem_inter.mpr ⟨hyA, hyS₀⟩)
      · rintro (rfl | hyT)
        · exact ⟨hxA, Or.inl rfl⟩
        · rw [← hAS₀, Finset.mem_inter] at hyT
          exact ⟨hyT.1, Or.inr hyT.2⟩
    · left; refine ⟨hAF, ?_⟩
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hyA, rfl | hyS₀⟩
        · exact absurd hyA hxA
        · exact hAS₀ ▸ Finset.mem_inter.mpr ⟨hyA, hyS₀⟩
      · intro hyT
        rw [← hAS₀, Finset.mem_inter] at hyT
        exact ⟨hyT.1, Or.inr hyT.2⟩

private lemma sum_div_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) (d : ℝ) :
    (∑ i ∈ s, f i / d) = (∑ i ∈ s, f i) / d := by
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]

private lemma probA_insert_split (F : Finset (Finset U)) {S₀ T : Finset U} {x : U}
    (hx : x ∉ S₀) (hT : T ∈ S₀.powerset) :
    probA F (insert x S₀) T + probA F (insert x S₀) (insert x T) = probA F S₀ T := by
  unfold probA
  rw [← add_div, ← Nat.cast_add, filter_insert_split F hx hT]

private lemma sum_probA_notMem_eq (F : Finset (Finset U)) (hF : F.Nonempty)
    {S₀ : Finset U} {x : U} (hx : x ∉ S₀) :
    ∑ T ∈ S₀.powerset, probA F (insert x S₀) T = 1 - occProb F x := by
  have hm_pos : (0 : ℝ) < F.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hF)
  unfold probA occProb occurrences
  rw [sum_div_eq, ← Nat.cast_sum]
  -- Partition F \ filter(x ∈ A) by A ∩ S₀ ∈ S₀.powerset
  have hpart : (∑ T ∈ S₀.powerset, (F.filter fun A => A ∩ insert x S₀ = T).card) =
      (F.filter fun A => x ∉ A).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext A
      simp only [Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_filter]
      constructor
      · rintro ⟨T, hTS₀, hAF, rfl⟩
        refine ⟨hAF, fun hxA => hx (hTS₀ (Finset.mem_inter.mpr ⟨hxA, Finset.mem_insert_self x S₀⟩))⟩
      · rintro ⟨hAF, hnxA⟩
        refine ⟨A ∩ S₀, Finset.inter_subset_right, hAF, ?_⟩
        ext y
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hyA, rfl | hyS₀⟩
          · exact absurd hyA hnxA
          · exact ⟨hyA, hyS₀⟩
        · rintro ⟨hyA, hyS₀⟩
          exact ⟨hyA, Or.inr hyS₀⟩
    · intro T₁ _ T₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro A _ h1 h2
      exact hne (h1.symm.trans h2)
  have hcompl : (F.filter fun A => x ∉ A).card + (F.filter fun A => x ∈ A).card = F.card := by
    simpa only [not_not] using Finset.card_filter_add_card_filter_not (s := F) (fun A => x ∉ A)
  rw [hpart]
  have hcast : ((F.filter fun A => x ∉ A).card : ℝ) =
      (F.card : ℝ) - ((F.filter fun A => x ∈ A).card : ℝ) := by
    have : ((F.filter fun A => x ∉ A).card : ℝ) + ((F.filter fun A => x ∈ A).card : ℝ) = F.card := by
      exact_mod_cast hcompl
    linarith
  rw [hcast, sub_div, div_self hm_pos.ne']

private lemma probC_decomp (F : Finset (Finset U)) (S R : Finset U) :
    probC F S R =
      ∑ p ∈ (S.powerset ×ˢ S.powerset).filter (fun q => q.1 ∪ q.2 = R),
        probA F S p.1 * probA F S p.2 := by
  unfold probC probA
  have hmul : ∀ q : Finset U × Finset U,
      (((F.filter fun A => A ∩ S = q.1).card : ℝ) / F.card) *
        (((F.filter fun B => B ∩ S = q.2).card : ℝ) / F.card) =
      (((F.filter fun A => A ∩ S = q.1) ×ˢ (F.filter fun B => B ∩ S = q.2)).card : ℝ) /
        (F.card : ℝ) ^ 2 := by
    intro q
    rw [Finset.card_product, Nat.cast_mul]
    ring
  simp_rw [hmul, sum_div_eq, ← Nat.cast_sum]
  congr 2
  rw [← Finset.card_biUnion]
  · congr 1
    ext ⟨A, B⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hAF, hBF⟩, hR⟩
      refine ⟨(A ∩ S, B ∩ S), ⟨⟨Finset.inter_subset_right, Finset.inter_subset_right⟩, ?_⟩,
        ⟨hAF, rfl⟩, ⟨hBF, rfl⟩⟩
      rw [← Finset.union_inter_distrib_right, hR]
    · rintro ⟨⟨T₁, T₂⟩, ⟨_, hTR⟩, ⟨hAF, hA⟩, ⟨hBF, hB⟩⟩
      refine ⟨⟨hAF, hBF⟩, ?_⟩
      rw [Finset.union_inter_distrib_right, hA, hB, hTR]
  · intro q₁ _ q₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro ⟨A, B⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_filter] at h1 h2
    exact hne (Prod.ext (h1.1.2.symm.trans h2.1.2) (h1.2.2.symm.trans h2.2.2))

private lemma probC_insert_notMem_decomp (F : Finset (Finset U)) {S₀ R : Finset U} {x : U}
    (hx : x ∉ S₀) (hR : R ∈ S₀.powerset) :
    probC F (insert x S₀) R =
      ∑ p ∈ (S₀.powerset ×ˢ S₀.powerset).filter (fun q => q.1 ∪ q.2 = R),
        probA F (insert x S₀) p.1 * probA F (insert x S₀) p.2 := by
  have hxR : x ∉ R := fun h => hx (Finset.mem_powerset.mp hR h)
  rw [probC_decomp]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hq ⊢
    exact ⟨⟨hq.1.1.trans (Finset.subset_insert x S₀),
      hq.1.2.trans (Finset.subset_insert x S₀)⟩, hq.2⟩
  · intro q hq hnq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hq hnq
    have hnot : ¬ (q.1 ⊆ S₀ ∧ q.2 ⊆ S₀) := fun h => hnq ⟨h, hq.2⟩
    exfalso; apply hnot
    have hx1 : x ∉ q.1 := fun h => hxR (hq.2 ▸ Finset.mem_union_left q.2 h)
    have hx2 : x ∉ q.2 := fun h => hxR (hq.2 ▸ Finset.mem_union_right q.1 h)
    refine ⟨fun y hy => (Finset.mem_insert.mp (hq.1.1 hy)).resolve_left (fun e => hx1 (e ▸ hy)),
      fun y hy => (Finset.mem_insert.mp (hq.1.2 hy)).resolve_left (fun e => hx2 (e ▸ hy))⟩

private lemma probC_insert_split (F : Finset (Finset U)) {S₀ R : Finset U} {x : U}
    (hx : x ∉ S₀) (hR : R ∈ S₀.powerset) :
    probC F (insert x S₀) R + probC F (insert x S₀) (insert x R) = probC F S₀ R := by
  -- Apply the same filter_insert_split logic on (F ×ˢ F) via union sets
  have hxR : x ∉ R := fun h => hx (Finset.mem_powerset.mp hR h)
  unfold probC
  rw [← add_div, ← Nat.cast_add]
  congr 2
  have hdisj : Disjoint ((F ×ˢ F).filter fun p => (p.1 ∪ p.2) ∩ insert x S₀ = R)
      ((F ×ˢ F).filter fun p => (p.1 ∪ p.2) ∩ insert x S₀ = insert x R) := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact hxR (by rw [← h1, h2]; exact Finset.mem_insert_self x R)
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext ⟨A, B⟩
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hAB, h1⟩ | ⟨hAB, h2⟩)
    · refine ⟨hAB, ?_⟩
      ext y; simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hy, hyS₀⟩
        have : y ∈ (A ∪ B) ∩ insert x S₀ :=
          Finset.mem_inter.mpr ⟨hy, Finset.mem_insert_of_mem hyS₀⟩
        rwa [h1] at this
      · intro hyR
        have hyS₀ : y ∈ S₀ := Finset.mem_powerset.mp hR hyR
        rw [← h1] at hyR
        exact ⟨(Finset.mem_inter.mp hyR).1, hyS₀⟩
    · refine ⟨hAB, ?_⟩
      ext y; simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hy, hyS₀⟩
        have hyx : y ≠ x := fun e => hx (e ▸ hyS₀)
        have : y ∈ (A ∪ B) ∩ insert x S₀ :=
          Finset.mem_inter.mpr ⟨hy, Finset.mem_insert_of_mem hyS₀⟩
        rw [h2, Finset.mem_insert] at this
        exact this.resolve_left hyx
      · intro hyR
        have hyS₀ : y ∈ S₀ := Finset.mem_powerset.mp hR hyR
        have : y ∈ insert x R := Finset.mem_insert_of_mem hyR
        rw [← h2] at this
        exact ⟨(Finset.mem_inter.mp this).1, hyS₀⟩
  · rintro ⟨hAB, hS₀⟩
    by_cases hxAB : x ∈ A ∪ B
    · right; refine ⟨hAB, ?_⟩
      ext y; simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hy, rfl | hyS₀⟩
        · exact Or.inl rfl
        · exact Or.inr (hS₀ ▸ Finset.mem_inter.mpr ⟨hy, hyS₀⟩)
      · rintro (rfl | hyR)
        · exact ⟨hxAB, Or.inl rfl⟩
        · rw [← hS₀, Finset.mem_inter] at hyR
          exact ⟨hyR.1, Or.inr hyR.2⟩
    · left; refine ⟨hAB, ?_⟩
      ext y; simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hy, rfl | hyS₀⟩
        · exact absurd hy hxAB
        · exact hS₀ ▸ Finset.mem_inter.mpr ⟨hy, hyS₀⟩
      · intro hyR
        rw [← hS₀, Finset.mem_inter] at hyR
        exact ⟨hyR.1, Or.inr hyR.2⟩

/-- One-step conditional-entropy comparison on inserting `x ∉ S₀`. -/
private lemma ent_insert_step (F : Finset (Finset U)) (hF : F.Nonempty)
    {S₀ : Finset U} {x : U} (hx : x ∉ S₀) :
    phi * (1 - occProb F x) * (entA F (insert x S₀) - entA F S₀) ≤
      entC F (insert x S₀) - entC F S₀ ∧
    0 ≤ entA F (insert x S₀) - entA F S₀ := by
  let u : Finset U → ℝ := fun T => probA F S₀ T
  let u₀ : Finset U → ℝ := fun T => probA F (insert x S₀) T
  let u₁ : Finset U → ℝ := fun T => probA F (insert x S₀) (insert x T)
  let p : Finset U → ℝ := fun T => if u T = 0 then 0 else u₀ T / u T
  have hu_split : ∀ T ∈ S₀.powerset, u₀ T + u₁ T = u T :=
    fun T hT => probA_insert_split F hx hT
  have hp_mem : ∀ T ∈ S₀.powerset, 0 ≤ p T ∧ p T ≤ 1 := by
    intro T hT
    dsimp [p]
    split_ifs with hz
    · exact ⟨le_rfl, zero_le_one⟩
    · have hu_pos : 0 < u T := lt_of_le_of_ne (probA_nonneg F S₀ T) (Ne.symm hz)
      have hu₀_le : u₀ T ≤ u T := by linarith [hu_split T hT, probA_nonneg F (insert x S₀) (insert x T)]
      exact ⟨div_nonneg (probA_nonneg F _ _) hu_pos.le, (div_le_one hu_pos).mpr hu₀_le⟩
  have hu₀_eq : ∀ T ∈ S₀.powerset, u₀ T = u T * p T := by
    intro T hT
    dsimp [p]
    split_ifs with hz
    · have : u₀ T ≤ 0 := by linarith [hu_split T hT, probA_nonneg F (insert x S₀) (insert x T)]
      linarith [probA_nonneg F (insert x S₀) T]
    · field_simp [hz]
  have hu₁_eq : ∀ T ∈ S₀.powerset, u₁ T = u T * (1 - p T) := by
    intro T hT
    linarith [hu_split T hT, hu₀_eq T hT]
  -- Compute entA increment
  have hentA_diff : entA F (insert x S₀) - entA F S₀ =
      ∑ T ∈ S₀.powerset, u T * binEnt (p T) := by
    unfold entA
    rw [sum_powerset_insert hx, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [← probA_insert_split F hx hT]
    change twoEnt (u₀ T) (u₁ T) = u T * binEnt (p T)
    rw [hu₀_eq T hT, hu₁_eq T hT, twoEnt_mul_binEnt]
  have hentA_nn : 0 ≤ entA F (insert x S₀) - entA F S₀ := by
    rw [hentA_diff]
    exact Finset.sum_nonneg fun T hT =>
      mul_nonneg (probA_nonneg F S₀ T) (binEnt_nonneg (hp_mem T hT).1 (hp_mem T hT).2)
  -- Lower bound entC increment
  have hentC_diff : ∑ q ∈ S₀.powerset ×ˢ S₀.powerset,
      u q.1 * u q.2 * binEnt (p q.1 * p q.2) ≤ entC F (insert x S₀) - entC F S₀ := by
    unfold entC
    rw [sum_powerset_insert hx, ← Finset.sum_sub_distrib]
    -- Partition S₀.powerset ×ˢ S₀.powerset by q.1 ∪ q.2 ∈ S₀.powerset
    have hpart_sum : ∑ q ∈ S₀.powerset ×ˢ S₀.powerset, u q.1 * u q.2 * binEnt (p q.1 * p q.2) =
        ∑ R ∈ S₀.powerset, ∑ q ∈ (S₀.powerset ×ˢ S₀.powerset).filter (fun q => q.1 ∪ q.2 = R),
          u q.1 * u q.2 * binEnt (p q.1 * p q.2) := by
      rw [← Finset.sum_biUnion]
      · congr 1
        ext q
        simp only [Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_filter, Finset.mem_product]
        exact ⟨fun ⟨h1, h2⟩ => ⟨q.1 ∪ q.2, Finset.union_subset h1 h2, ⟨h1, h2⟩, rfl⟩,
          fun ⟨_, _, ⟨h1, h2⟩, _⟩ => ⟨h1, h2⟩⟩
      · intro R₁ _ R₂ _ hne
        simp only [Function.onFun]
        rw [Finset.disjoint_filter]
        intro q _ h1 h2; exact hne (h1.symm.trans h2)
    rw [hpart_sum]
    refine Finset.sum_le_sum fun R hR => ?_
    let I := (S₀.powerset ×ˢ S₀.powerset).filter (fun q => q.1 ∪ q.2 = R)
    let α : Finset U × Finset U → ℝ := fun q => (u q.1 * u q.2) * (p q.1 * p q.2)
    let β : Finset U × Finset U → ℝ := fun q => (u q.1 * u q.2) * (1 - p q.1 * p q.2)
    have hα_nn : ∀ q ∈ I, 0 ≤ α q := by
      intro q hq
      have hqP := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1)
      exact mul_nonneg (mul_nonneg (probA_nonneg F S₀ q.1) (probA_nonneg F S₀ q.2))
        (mul_nonneg (hp_mem q.1 hqP.1).1 (hp_mem q.2 hqP.2).1)
    have hβ_nn : ∀ q ∈ I, 0 ≤ β q := by
      intro q hq
      have hqP := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1)
      have hprod_le : p q.1 * p q.2 ≤ 1 :=
        mul_le_one₀ (hp_mem q.1 hqP.1).2 (hp_mem q.2 hqP.2).1 (hp_mem q.2 hqP.2).2
      exact mul_nonneg (mul_nonneg (probA_nonneg F S₀ q.1) (probA_nonneg F S₀ q.2))
        (sub_nonneg.mpr hprod_le)
    have hterm : ∀ q ∈ I, u q.1 * u q.2 * binEnt (p q.1 * p q.2) = twoEnt (α q) (β q) := by
      intro q _
      exact (twoEnt_mul_binEnt (u q.1 * u q.2) (p q.1 * p q.2)).symm
    have hsum_α : ∑ q ∈ I, α q = probC F (insert x S₀) R := by
      rw [probC_insert_notMem_decomp F hx hR]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hqP := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
      change (u q.1 * u q.2) * (p q.1 * p q.2) = u₀ q.1 * u₀ q.2
      rw [hu₀_eq q.1 hqP.1, hu₀_eq q.2 hqP.2]; ring
    have hsum_αβ : (∑ q ∈ I, α q) + (∑ q ∈ I, β q) = probC F S₀ R := by
      rw [← Finset.sum_add_distrib, probC_decomp F S₀ R]
      refine Finset.sum_congr rfl fun q _ => by dsimp [α, β]; ring
    have hsum_β : ∑ q ∈ I, β q = probC F (insert x S₀) (insert x R) := by
      linarith [hsum_α, hsum_αβ, probC_insert_split F hx hR]
    calc ∑ q ∈ I, u q.1 * u q.2 * binEnt (p q.1 * p q.2)
        = ∑ q ∈ I, twoEnt (α q) (β q) := Finset.sum_congr rfl hterm
      _ ≤ twoEnt (∑ q ∈ I, α q) (∑ q ∈ I, β q) := twoEnt_sum_le I α β hα_nn hβ_nn
      _ = Real.negMulLog (probC F (insert x S₀) R) +
            Real.negMulLog (probC F (insert x S₀) (insert x R)) -
            Real.negMulLog (probC F S₀ R) := by
          rw [hsum_α, hsum_β]
          unfold twoEnt
          rw [probC_insert_split F hx hR]
  -- Apply Boppana's two-variable inequality term-by-term
  have hbopp : phi * (1 - occProb F x) * (∑ T ∈ S₀.powerset, u T * binEnt (p T)) ≤
      ∑ q ∈ S₀.powerset ×ˢ S₀.powerset, u q.1 * u q.2 * binEnt (p q.1 * p q.2) := by
    have hpt : ∀ q ∈ S₀.powerset ×ˢ S₀.powerset,
        u q.1 * u q.2 * ((phi / 2) * (p q.2 * binEnt (p q.1) + p q.1 * binEnt (p q.2))) ≤
        u q.1 * u q.2 * binEnt (p q.1 * p q.2) := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
      exact mul_le_mul_of_nonneg_left
        (boppana_two_var (hp_mem q.1 hq1).1 (hp_mem q.1 hq1).2
          (hp_mem q.2 hq2).1 (hp_mem q.2 hq2).2)
        (mul_nonneg (probA_nonneg F S₀ q.1) (probA_nonneg F S₀ q.2))
    have hsum := Finset.sum_le_sum hpt
    have hlhs : ∑ q ∈ S₀.powerset ×ˢ S₀.powerset,
        u q.1 * u q.2 * ((phi / 2) * (p q.2 * binEnt (p q.1) + p q.1 * binEnt (p q.2))) =
        phi * (1 - occProb F x) * (∑ T ∈ S₀.powerset, u T * binEnt (p T)) := by
      have hp_sum : ∑ T ∈ S₀.powerset, u T * p T = 1 - occProb F x := by
        rw [← sum_probA_notMem_eq F hF hx]
        exact Finset.sum_congr rfl fun T hT => (hu₀_eq T hT).symm
      rw [Finset.sum_product]
      have hinner : ∀ T₁ : Finset U,
          (∑ T₂ ∈ S₀.powerset,
            u T₁ * u T₂ * ((phi / 2) * (p T₂ * binEnt (p T₁) + p T₁ * binEnt (p T₂)))) =
          (u T₁ * binEnt (p T₁)) * ((phi / 2) * (∑ T₂ ∈ S₀.powerset, u T₂ * p T₂)) +
          (u T₁ * p T₁) * ((phi / 2) * (∑ T₂ ∈ S₀.powerset, u T₂ * binEnt (p T₂))) := by
        intro T₁
        have hexp : ∀ T₂ : Finset U,
            u T₁ * u T₂ * ((phi / 2) * (p T₂ * binEnt (p T₁) + p T₁ * binEnt (p T₂))) =
            ((u T₁ * binEnt (p T₁)) * (phi / 2)) * (u T₂ * p T₂) +
            ((u T₁ * p T₁) * (phi / 2)) * (u T₂ * binEnt (p T₂)) := fun _ => by ring
        simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      simp_rw [hinner, Finset.sum_add_distrib, ← Finset.sum_mul, hp_sum]
      ring
    linarith
  rw [← hentA_diff] at hbopp
  exact ⟨hbopp.trans hentC_diff, hentA_nn⟩

/-- Inductive subset-projection entropy inequality. -/
theorem entC_ge_mul_entA (F : Finset (Finset U)) (hF : F.Nonempty) (S : Finset U) (M : ℝ)
    (hM : ∀ x ∈ S, M ≤ phi * (1 - occProb F x)) :
    M * entA F S ≤ entC F S := by
  induction S using Finset.induction_on with
  | empty =>
    have hA0 : entA F ∅ = 0 := by
      unfold entA probA
      have hm_pos : (0 : ℝ) < F.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hF)
      simp [div_self hm_pos.ne']
    have hC0 : entC F ∅ = 0 := by
      unfold entC probC
      have hm2_pos : (0 : ℝ) < (F.card : ℝ) ^ 2 :=
        sq_pos_of_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hF))
      have hcard : (((F ×ˢ F).filter fun p => (p.1 ∪ p.2) ∩ ∅ = ∅).card : ℝ) = (F.card : ℝ) ^ 2 := by
        simp [Finset.card_product, sq]
      rw [Finset.powerset_empty, Finset.sum_singleton, hcard, div_self hm2_pos.ne',
        Real.negMulLog_one]
    rw [hA0, hC0, mul_zero]
  | @insert x S₀ hx ih =>
    have hMS₀ : ∀ y ∈ S₀, M ≤ phi * (1 - occProb F y) :=
      fun y hy => hM y (Finset.mem_insert_of_mem hy)
    have hMx : M ≤ phi * (1 - occProb F x) := hM x (Finset.mem_insert_self x S₀)
    have hIH := ih hMS₀
    obtain ⟨hstep, hnn⟩ := ent_insert_step F hF hx
    have hmul : M * (entA F (insert x S₀) - entA F S₀) ≤
        phi * (1 - occProb F x) * (entA F (insert x S₀) - entA F S₀) :=
      mul_le_mul_of_nonneg_right hMx hnn
    linarith

/-- On `S = F.biUnion id`, `entA F S = log |F|`. -/
lemma entA_ground_eq_log (F : Finset (Finset U)) (hF : F.Nonempty) :
    entA F (F.biUnion id) = Real.log (F.card : ℝ) := by
  let S := F.biUnion id
  have hsub : ∀ A ∈ F, A ⊆ S := fun A hA y hy =>
    Finset.mem_biUnion.mpr ⟨A, hA, hy⟩
  have hinter : ∀ A ∈ F, A ∩ S = A := fun A hA =>
    Finset.inter_eq_left.mpr (hsub A hA)
  unfold entA
  have hF_sub : F ⊆ S.powerset := fun A hA => Finset.mem_powerset.mpr (hsub A hA)
  rw [← Finset.sum_subset hF_sub]
  · have hm_pos : (0 : ℝ) < F.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hF)
    have hval : ∀ A ∈ F, probA F S A = 1 / (F.card : ℝ) := by
      intro A hAF
      unfold probA
      have hflt : (F.filter fun B => B ∩ S = A) = {A} := by
        ext B
        simp only [Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun ⟨hBF, hB⟩ => by rwa [hinter B hBF] at hB,
          fun hBA => by subst hBA; exact ⟨hAF, hinter B hAF⟩⟩
      rw [hflt, Finset.card_singleton, Nat.cast_one]
    have hsum : ∑ A ∈ F, Real.negMulLog (probA F S A) =
        ∑ _A ∈ F, Real.negMulLog (1 / (F.card : ℝ)) :=
      Finset.sum_congr rfl fun A hA => by rw [hval A hA]
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    unfold Real.negMulLog
    rw [one_div, Real.log_inv]
    field_simp [hm_pos.ne']
  · intro T _ hTF
    have hflt : (F.filter fun B => B ∩ S = T) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro B hBF hBT
      rw [hinter B hBF] at hBT
      exact hTF (hBT ▸ hBF)
    change Real.negMulLog (probA F S T) = 0
    unfold probA
    simp [hflt]

/-- On `S = F.biUnion id`, if `IsUnionClosed F`, then `entC F S ≤ log |F|`. -/
lemma entC_ground_le_log (F : Finset (Finset U)) (huc : IsUnionClosed F) (hF : F.Nonempty) :
    entC F (F.biUnion id) ≤ Real.log (F.card : ℝ) := by
  let S := F.biUnion id
  have hsub : ∀ A ∈ F, A ⊆ S := fun A hA y hy =>
    Finset.mem_biUnion.mpr ⟨A, hA, hy⟩
  have hinter : ∀ A ∈ F, A ∩ S = A := fun A hA =>
    Finset.inter_eq_left.mpr (hsub A hA)
  have hF_sub : F ⊆ S.powerset := fun A hA => Finset.mem_powerset.mpr (hsub A hA)
  have hentC_eq : entC F S = ∑ C ∈ F, Real.negMulLog (probC F S C) := by
    unfold entC
    symm
    refine Finset.sum_subset hF_sub fun R _ hRF => ?_
    have hflt : ((F ×ˢ F).filter fun p => (p.1 ∪ p.2) ∩ S = R) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro ⟨A, B⟩ hAB hR
      obtain ⟨hAF, hBF⟩ := Finset.mem_product.mp hAB
      have hCAB : A ∪ B ∈ F := huc hAF hBF
      rw [hinter (A ∪ B) hCAB] at hR
      exact hRF (hR ▸ hCAB)
    change Real.negMulLog (probC F S R) = 0
    unfold probC
    simp [hflt]
  rw [hentC_eq]
  refine entropy_le_log_card hF (fun C _ => probC_nonneg F S C) ?_
  unfold probC
  rw [sum_div_eq, ← Nat.cast_sum]
  have hm2_pos : (0 : ℝ) < (F.card : ℝ) ^ 2 :=
    sq_pos_of_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hF))
  have htot : (∑ C ∈ F, ((F ×ˢ F).filter fun p => (p.1 ∪ p.2) ∩ S = C).card) = F.card ^ 2 := by
    rw [← Finset.card_biUnion]
    · have hbi : F.biUnion (fun C => (F ×ˢ F).filter fun p => (p.1 ∪ p.2) ∩ S = C) = F ×ˢ F := by
        ext ⟨A, B⟩
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product]
        constructor
        · rintro ⟨_, _, ⟨hAF, hBF⟩, _⟩; exact ⟨hAF, hBF⟩
        · rintro ⟨hAF, hBF⟩
          have hCAB := huc hAF hBF
          exact ⟨A ∪ B, hCAB, ⟨hAF, hBF⟩, hinter (A ∪ B) hCAB⟩
      rw [hbi, Finset.card_product, sq]
    · intro C₁ _ C₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro p _ h1 h2; exact hne (h1.symm.trans h2)
  rw [htot, Nat.cast_pow, div_self hm2_pos.ne']

end ChainRule

/-! ## Section 4: Main Theorem (`density ≥ 3 / 8` and `statement_09` for `r ≤ 6`) -/

/-- Every nondegenerate finite union-closed family contains an element of density at least `3 / 8`. -/
theorem exists_density_ge_three_eighths {U : Type*} [DecidableEq U] (F : Finset (Finset U))
    (huc : IsUnionClosed F) (hnd : Nondegenerate F) :
    ∃ x : U, density F x ≥ 3 / 8 := by
  obtain ⟨hne_empty, hne_sing⟩ := hnd
  have hF_ne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne_empty
  -- First show F.biUnion id is nonempty (some member of F is nonempty)
  have hhas_nonempty : ∃ A ∈ F, A.Nonempty := by
    by_contra hall
    push Not at hall
    apply hne_sing
    ext A
    simp only [Finset.mem_singleton]
    constructor
    · intro hAF
      exact hall A hAF
    · rintro rfl
      obtain ⟨B, hBF⟩ := hF_ne
      rwa [hall B hBF] at hBF
  obtain ⟨A₀, hA₀F, ⟨x₀, hx₀A₀⟩⟩ := hhas_nonempty
  -- Handle |F| = 1 directly
  by_cases hcard1 : F.card = 1
  · refine ⟨x₀, ?_⟩
    obtain ⟨B, hFB⟩ := Finset.card_eq_one.mp hcard1
    subst hFB
    have hA₀B : A₀ = B := Finset.mem_singleton.mp hA₀F
    subst hA₀B
    have hocc : occurrences ({A₀} : Finset (Finset U)) x₀ = 1 := by
      unfold occurrences
      have : (({A₀} : Finset (Finset U)).filter fun A => x₀ ∈ A) = {A₀} := by
        ext A
        simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
        rintro rfl
        exact hx₀A₀
      rw [this, Finset.card_singleton]
    unfold density
    rw [hocc, Finset.card_singleton]
    norm_num
  · -- Main case: |F| ≥ 2
    have hcard_ge2 : 2 ≤ F.card := by
      have := Finset.card_pos.mpr hF_ne; omega
    by_contra hnone
    push Not at hnone
    let S := F.biUnion id
    have hocc_lt : ∀ x ∈ S, occProb F x < 3 / 8 := by
      intro x _
      have hrat := hnone x
      unfold density at hrat
      have hmax : max 1 F.card = F.card := max_eq_right (by omega)
      rw [hmax] at hrat
      have hreal : ((occurrences F x : ℚ) / (F.card : ℚ) : ℝ) < ((3 / 8 : ℚ) : ℝ) := by
        exact_mod_cast hrat
      simpa [occProb] using hreal
    let M : ℝ := phi * (5 / 8)
    have hphi_gt : (8 / 5 : ℝ) < phi := phi_bounds.1
    have hM_gt1 : 1 < M := by dsimp [M]; linarith
    have hM_le : ∀ x ∈ S, M ≤ phi * (1 - occProb F x) := by
      intro x hx
      have h1 := hocc_lt x hx
      dsimp [M]
      nlinarith
    have hchain := entC_ge_mul_entA F hF_ne S M hM_le
    rw [entA_ground_eq_log F hF_ne] at hchain
    have hub := entC_ground_le_log F huc hF_ne
    have hlog_pos : 0 < Real.log (F.card : ℝ) := by
      apply Real.log_pos
      exact_mod_cast hcard_ge2
    have hlt : Real.log (F.card : ℝ) < M * Real.log (F.card : ℝ) := by
      nlinarith
    linarith

/-- For every `r ≤ 6`, every nondegenerate finite union-closed family has an element of
density at least `1/2 - 1/(r + 2)`. -/
theorem statement_09_of_le_six {r : ℕ} (hr : r ≤ 6) :
    ∀ {U : Type*} [DecidableEq U] (F : Finset (Finset U)),
      IsUnionClosed F → Nondegenerate F →
        ∃ x, density F x ≥ (1 / 2 : ℚ) - 1 / ((r : ℚ) + 2) := by
  intro U _ F huc hnd
  obtain ⟨x, hx⟩ := exists_density_ge_three_eighths F huc hnd
  refine ⟨x, ?_⟩
  have hr_q : (r : ℚ) + 2 ≤ 8 := by exact_mod_cast (by omega : r + 2 ≤ 8)
  have hr_pos : (0 : ℚ) < (r : ℚ) + 2 := by positivity
  have hinv : (1 / 8 : ℚ) ≤ 1 / ((r : ℚ) + 2) :=
    one_div_le_one_div_of_le hr_pos hr_q
  linarith

end TenChallenges.Challenge09R6


set_option autoImplicit false in
theorem solution : TenChallenges.statement_09 6 :=
  TenChallenges.Challenge09R6.statement_09_of_le_six (by decide)

#print axioms solution
