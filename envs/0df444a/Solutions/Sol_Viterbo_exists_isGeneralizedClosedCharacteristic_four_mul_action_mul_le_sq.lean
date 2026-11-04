-- Prove2me | solution 1 for Viterbo.exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T18:14:07.348491+00:00
-- url     : https://prove2.me/submissions/6dfdbfde-d93b-4764-b394-ff02a9254311

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
section
/-!
Blueprint, Part M: elementary properties of `cEHZ` on convex domains, and monotonicity under
inclusion from Clarke's dual action principle in length form
(`Viterbo.exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq`).
-/

open MeasureTheory Set OAI.SymmetricPolar
open scoped ENNReal Pointwise

namespace Viterbo.CM

variable {n : ℕ}

/-- The `K`-length `∫₀¹ h_K(-J ż)` of a loop. -/
noncomputable def ell (K : Set (Phase n)) (z : ℝ → Phase n) : ℝ :=
  ∫ t in (0 : ℝ)..1, sSup ((fun x => phaseInner x (-J (deriv z t))) '' K)

/-- Absolutely continuous (as in `IsGeneralizedClosedCharacteristic`). -/
def IsAC (z : ℝ → Phase n) : Prop :=
  ∃ v : ℝ → Phase n, LocallyIntegrable v volume ∧ ∀ a b, z b - z a = ∫ s in a..b, v s

/-! ## Helpers -/

lemma pI_comm (z w : Phase n) : phaseInner z w = phaseInner w z := by
  simp [phaseInner, real_inner_comm]

lemma pI_add_left (x y w : Phase n) :
    phaseInner (x + y) w = phaseInner x w + phaseInner y w := by
  simp [phaseInner, inner_add_left]; ring

lemma pI_sub_left (x y w : Phase n) :
    phaseInner (x - y) w = phaseInner x w - phaseInner y w := by
  simp [phaseInner, inner_sub_left]; ring

lemma pI_sub_right (w x y : Phase n) :
    phaseInner w (x - y) = phaseInner w x - phaseInner w y := by
  simp [phaseInner, inner_sub_right]; ring

lemma pI_smul_left (c : ℝ) (x w : Phase n) :
    phaseInner (c • x) w = c * phaseInner x w := by
  simp [phaseInner, real_inner_smul_left]; ring

lemma pI_smul_right (c : ℝ) (w x : Phase n) :
    phaseInner w (c • x) = c * phaseInner w x := by
  simp [phaseInner, real_inner_smul_right]; ring

lemma pI_zero_right (x : Phase n) : phaseInner x 0 = 0 := by simp [phaseInner]

lemma pI_self (z : Phase n) : phaseInner z z = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  simp [phaseInner]

lemma norm_sq_le_pI (u : Phase n) : ‖u‖ ^ 2 ≤ phaseInner u u := by
  rw [pI_self, Prod.norm_def]
  rcases max_cases ‖u.1‖ ‖u.2‖ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    nlinarith [sq_nonneg ‖u.1‖, sq_nonneg ‖u.2‖]

lemma J_smul (c : ℝ) (z : Phase n) : J (c • z) = c • J z := by
  simp [J]

lemma J_add (x y : Phase n) : J (x + y) = J x + J y := by
  refine Prod.ext ?_ ?_ <;> simp [J]; abel

lemma J_sub (x y : Phase n) : J (x - y) = J x - J y := by
  refine Prod.ext ?_ ?_ <;> simp [J]; abel

lemma J_neg (x : Phase n) : J (-x) = -J x := by
  refine Prod.ext ?_ ?_ <;> simp [J]

lemma J_J (x : Phase n) : J (J x) = -x := by
  refine Prod.ext ?_ ?_ <;> simp [J]

lemma J_eq_zero {z : Phase n} (h : J z = 0) : z = 0 := by
  simp only [J, Prod.mk_eq_zero, neg_eq_zero] at h
  exact Prod.ext h.2 h.1

lemma pI_J_J (x y : Phase n) : phaseInner (J x) (J y) = phaseInner x y := by
  simp [phaseInner, J]; ring

lemma norm_negJ (x : Phase n) : ‖-J x‖ = ‖x‖ := by
  rw [norm_neg]; simp [J, Prod.norm_def, max_comm]

lemma continuous_J : Continuous (J : Phase n → Phase n) := by
  show Continuous fun z : Phase n => ((-z.2, z.1) : Phase n)
  fun_prop

lemma abs_pI_le (x y : Phase n) : |phaseInner x y| ≤ 2 * ‖x‖ * ‖y‖ := by
  unfold phaseInner
  have h1 := abs_real_inner_le_norm x.1 y.1
  have h2 := abs_real_inner_le_norm x.2 y.2
  have a1 := norm_fst_le x
  have a2 := norm_snd_le x
  have b1 := norm_fst_le y
  have b2 := norm_snd_le y
  calc |inner ℝ x.1 y.1 + inner ℝ x.2 y.2| ≤ |inner ℝ x.1 y.1| + |inner ℝ x.2 y.2| := abs_add_le _ _
    _ ≤ ‖x.1‖ * ‖y.1‖ + ‖x.2‖ * ‖y.2‖ := add_le_add h1 h2
    _ ≤ ‖x‖ * ‖y‖ + ‖x‖ * ‖y‖ := by gcongr
    _ = 2 * ‖x‖ * ‖y‖ := by ring

/-- `phaseInner · w` as a continuous linear functional. -/
noncomputable def pIL (w : Phase n) : Phase n →L[ℝ] ℝ :=
  (innerSL ℝ w.1).comp (ContinuousLinearMap.fst ℝ (Position n) (Position n)) +
    (innerSL ℝ w.2).comp (ContinuousLinearMap.snd ℝ (Position n) (Position n))

lemma pIL_apply (w z : Phase n) : pIL w z = phaseInner z w := by
  simp [pIL, phaseInner, real_inner_comm]

lemma continuous_pI : Continuous (fun p : Phase n × Phase n => phaseInner p.1 p.2) := by
  unfold phaseInner; fun_prop

/-! ### Absolutely continuous loops -/

lemma ii_of_li {v : ℝ → Phase n} (hv : LocallyIntegrable v volume) (a b : ℝ) :
    IntervalIntegrable v volume a b :=
  (hv.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

lemma eq_prim {γ v : ℝ → Phase n} (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) :
    γ = fun x => γ 0 + ∫ s in (0 : ℝ)..x, v s := by
  funext x; rw [← hf 0 x]; abel

lemma cont_of_ac {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) : Continuous γ := by
  rw [eq_prim hf]
  exact continuous_const.add (intervalIntegral.continuous_primitive (ii_of_li hv) 0)

lemma hasDeriv_ae {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) : ∀ᵐ x, HasDerivAt γ (v x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hv] with x hx
  rw [eq_prim hf]
  simpa using (hx 0).const_add (γ 0)

lemma deriv_ae {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) : ∀ᵐ x, deriv γ x = v x :=
  (hasDeriv_ae hv hf).mono fun _ hx => hx.deriv

lemma ii_pI {w v : ℝ → Phase n} (hw : Continuous w) (hv : LocallyIntegrable v volume) (a b : ℝ) :
    IntervalIntegrable (fun t => phaseInner (w t) (v t)) volume a b := by
  obtain ⟨C, hC⟩ :=
    (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn hw.continuousOn
  have hvi : IntegrableOn v (uIcc a b) volume := hv.integrableOn_isCompact isCompact_uIcc
  have : IntegrableOn (fun t => phaseInner (w t) (v t)) (uIcc a b) volume := by
    refine Integrable.mono' (hvi.norm.const_mul (2 * C)) ?_ ?_
    · have hm : AEStronglyMeasurable (fun t => (w t, v t)) (volume.restrict (uIcc a b)) :=
        hw.aestronglyMeasurable.prodMk hvi.aestronglyMeasurable
      have h4 := continuous_pI.comp_aestronglyMeasurable hm
      simpa only [Function.comp_def] using h4
    · refine (ae_restrict_iff' measurableSet_uIcc).2 (Filter.Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs]
      have hCt : 2 * ‖w t‖ ≤ 2 * C := by linarith [hC t ht]
      calc _ ≤ 2 * ‖w t‖ * ‖v t‖ := abs_pI_le _ _
        _ ≤ 2 * C * ‖v t‖ := mul_le_mul_of_nonneg_right hCt (norm_nonneg _)
  exact this.intervalIntegrable

lemma integral_pI_const {v : ℝ → Phase n} (hv : LocallyIntegrable v volume) (c : Phase n)
    (a b : ℝ) : ∫ t in a..b, phaseInner c (v t) = phaseInner c (∫ t in a..b, v t) := by
  have h : ∀ x, phaseInner c x = pIL c x := fun x => by rw [pIL_apply, pI_comm]
  simp only [h]
  exact (pIL c).intervalIntegral_comp_comm (ii_of_li hv a b)

lemma action_eq {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) :
    action γ = 1 / 2 * ∫ t in (0 : ℝ)..1, phaseInner (J (γ t)) (v t) := by
  unfold action; congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [deriv_ae hv hf] with t ht _
  rw [ht]

/-! ### Support functions -/

/-- The support function `h_K(w)`. -/
noncomputable def supp (K : Set (Phase n)) (w : Phase n) : ℝ :=
  sSup ((fun x => phaseInner x w) '' K)

lemma bdd_supp {S : Set (Phase n)} (hS : Bornology.IsBounded S) (u : Phase n) :
    BddAbove ((fun y => phaseInner y u) '' S) := by
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  refine ⟨2 * R * ‖u‖, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  calc phaseInner y u ≤ |phaseInner y u| := le_abs_self _
    _ ≤ 2 * ‖y‖ * ‖u‖ := abs_pI_le _ _
    _ ≤ 2 * R * ‖u‖ := by gcongr; exact hR y hy

lemma supp_le_add {K : Set (Phase n)} (hK : Bornology.IsBounded K) (hne : K.Nonempty) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (w w' : Phase n) :
    supp K w ≤ supp K w' + 2 * R * ‖w - w'‖ := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  have h1 : phaseInner x w' ≤ supp K w' := le_csSup (bdd_supp hK w') (mem_image_of_mem _ hx)
  have h2 : phaseInner x (w - w') ≤ 2 * R * ‖w - w'‖ :=
    (le_abs_self _).trans ((abs_pI_le _ _).trans (by gcongr; exact hR x hx))
  rw [pI_sub_right] at h2
  simp only
  linarith

lemma supp_zero {K : Set (Phase n)} (hne : K.Nonempty) : supp K 0 = 0 := by
  unfold supp
  simp only [pI_zero_right]
  rw [hne.image_const, csSup_singleton]

lemma ii_supp {K : Set (Phase n)} (hK : IsConvexDomain K) {v : ℝ → Phase n}
    (hv : LocallyIntegrable v volume) (a b : ℝ) :
    IntervalIntegrable (fun t => supp K (-J (v t))) volume a b := by
  obtain ⟨R, hR⟩ := hK.1.exists_norm_le
  have hne : K.Nonempty := hK.2.2.mono interior_subset
  obtain ⟨k0, hk0⟩ := hne
  have hR0 : 0 ≤ R := (norm_nonneg k0).trans (hR k0 hk0)
  have hlip : LipschitzWith (Real.toNNReal (2 * R)) (supp K) := by
    refine LipschitzWith.of_le_add_mul _ fun x y => ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
    exact supp_le_add hK.1 ⟨k0, hk0⟩ hR x y
  have hbd : ∀ w, |supp K w| ≤ 2 * R * ‖w‖ := fun w => by
    have h1 := supp_le_add hK.1 ⟨k0, hk0⟩ hR w 0
    have h2 := supp_le_add hK.1 ⟨k0, hk0⟩ hR 0 w
    rw [supp_zero ⟨k0, hk0⟩, sub_zero] at h1
    rw [supp_zero ⟨k0, hk0⟩, zero_sub, norm_neg] at h2
    rw [abs_le]; constructor <;> linarith
  have hvi : IntegrableOn v (uIcc a b) volume := hv.integrableOn_isCompact isCompact_uIcc
  have : IntegrableOn (fun t => supp K (-J (v t))) (uIcc a b) volume := by
    refine Integrable.mono' (hvi.norm.const_mul (2 * R)) ?_ ?_
    · exact (hlip.continuous.comp continuous_J.neg).comp_aestronglyMeasurable
        hvi.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs]
      calc _ ≤ 2 * R * ‖-J (v t)‖ := hbd _
        _ = 2 * R * ‖v t‖ := by rw [norm_negJ]
  exact this.intervalIntegrable

lemma ell_eq {z v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, z b - z a = ∫ s in a..b, v s) (K : Set (Phase n)) :
    ell K z = ∫ t in (0 : ℝ)..1, supp K (-J (v t)) := by
  unfold ell
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [deriv_ae hv hf] with t ht _
  rw [ht]; rfl

/-! ### Translation -/

/-! ### Scaling -/

lemma ftc_smul {γ v : ℝ → Phase n} (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) (α : ℝ) :
    ∀ a b, (fun t => α • γ t) b - (fun t => α • γ t) a = ∫ s in a..b, α • v s := by
  intro a b
  rw [intervalIntegral.integral_smul, ← hf a b, smul_sub]

lemma action_smul {γ v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, γ b - γ a = ∫ s in a..b, v s) (α : ℝ) :
    action (fun t => α • γ t) = α ^ 2 * action γ := by
  rw [action_eq (hv.smul α) (ftc_smul hf α), action_eq hv hf]
  have e : ∀ t, phaseInner (J (α • γ t)) (α • v t) = α ^ 2 * phaseInner (J (γ t)) (v t) := by
    intro t; rw [J_smul, pI_smul_left, pI_smul_right]; ring
  simp only [Pi.smul_apply, e, intervalIntegral.integral_const_mul]
  ring

/-! ### Positivity of the action -/

lemma cone_lower {S : Set (Phase n)} {x0 : Phase n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x0 r ⊆ S) {y u : Phase n} (hu : u ∈ normalCone phaseInner S y) :
    r / 2 * ‖u‖ ≤ phaseInner (y - x0) u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simp [pI_zero_right]
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
  set s := r / (2 * ‖u‖) with hs
  have hs0 : 0 < s := by positivity
  have hsu : s * ‖u‖ = r / 2 := by rw [hs]; field_simp
  have hz : x0 + s • u ∈ S := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs0, hsu]
    linarith)
  have h1 := hu _ hz
  have h2 := norm_sq_le_pI u
  have e : phaseInner u (x0 + s • u - y) = s * phaseInner u u - phaseInner (y - x0) u := by
    rw [show x0 + s • u - y = s • u - (y - x0) by abel, pI_sub_right, pI_smul_right,
      pI_comm u (y - x0)]
  rw [e] at h1
  have : r / 2 * ‖u‖ = s * ‖u‖ ^ 2 := by rw [← hsu]; ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left h2 hs0.le]

lemma ell_nonneg {K : Set (Phase n)} (hK : IsConvexDomain K) {z : ℝ → Phase n}
    (hz : Function.Periodic z 1) (hac : IsAC z) : 0 ≤ ell K z := by
  obtain ⟨v, hv, hf⟩ := hac
  rw [ell_eq hv hf]
  obtain ⟨k0, hk0⟩ := hK.2.2.mono interior_subset
  have hlow : ∀ t, phaseInner (J k0) (v t) ≤ supp K (-J (v t)) := fun t => by
    have := le_csSup (bdd_supp hK.1 (-J (v t))) (mem_image_of_mem _ hk0)
    rw [show phaseInner k0 (-J (v t)) = phaseInner (J k0) (v t) by
      rw [← pI_J_J, J_neg, J_J, neg_neg]] at this
    exact this
  have h0 : ∫ t in (0 : ℝ)..1, phaseInner (J k0) (v t) = 0 := by
    rw [integral_pI_const hv, ← hf 0 1, show z 1 = z 0 by simpa using hz 0, sub_self,
      pI_zero_right]
  have hm := intervalIntegral.integral_mono_on zero_le_one
    (ii_pI (w := fun _ => J k0) continuous_const hv 0 1) (ii_supp hK hv 0 1) (fun t _ => hlow t)
  linarith


end Viterbo.CM
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL
open Viterbo Viterbo.CM
variable {n : ℕ}
/-!
# Blueprint: Clarke's dual action principle in length form

Target: `Viterbo.exists_isGeneralizedClosedCharacteristic_four_mul_action_mul_le_sq`.

Route (elementary; no Sobolev spaces):
* Part P: `K`-length `ℓ` and action `A` through partition sums. `∑ h_K(-J Δz) ≤ ℓ(z)` (Jensen for
  the sublinear `h_K`), with near-equality for some partition; Riemann sums for `A`; Lipschitz
  loops are absolutely continuous.
* Part R: every loop can be reparametrized to a Lipschitz loop with the same `ℓ` and `A`, with
  Lipschitz constant `≤ κ (ℓ + ε)` for a `κ` depending only on `K`.
* Part C: `A ≤ C ℓ²` on loops, and a minimizer of `ℓ² / A` exists among Lipschitz loops (Arzelà–Ascoli;
  `ℓ` is lower semicontinuous as a sup of partition sums, `A` continuous under uniform convergence
  with a uniform Lipschitz bound).
* Part E: first variation at the minimizer `w`: for every bounded measurable `1`-periodic mean-zero `ψ`,
  `ℓ(w)/(2A(w)) ∫⟨w, ψ⟩ ≤ ∫ h_K'(-J ẇ; ψ)` (perturb `w` by `η` with `η̇ = Jψ`).
* Part F: a constant `b` (finite-dimensional separation) with `c w(t) + b ∈ ∂h_K(-J ẇ(t))` a.e.
* Part G: `γ = c w + b` is the generalized closed characteristic.
-/
/-- A loop: `1`-periodic and absolutely continuous. -/
def IsLoop (z : ℝ → Phase n) : Prop := Function.Periodic z 1 ∧ IsAC z

/-- A partition `0 = t₀ < t₁ < ⋯ < t_N = 1` of `[0, 1]`. -/
def IsPart {N : ℕ} (t : Fin (N + 1) → ℝ) : Prop :=
  t 0 = 0 ∧ t (Fin.last N) = 1 ∧ StrictMono t

/-- Mesh at most `δ`. -/
def MeshLE {N : ℕ} (t : Fin (N + 1) → ℝ) (δ : ℝ) : Prop :=
  ∀ i : Fin N, t i.succ - t i.castSucc ≤ δ

/-- Partition sum of the `K`-length. -/
noncomputable def psum (K : Set (Phase n)) (z : ℝ → Phase n) {N : ℕ} (t : Fin (N + 1) → ℝ) : ℝ :=
  ∑ i : Fin N, supp K (-J (z (t i.succ) - z (t i.castSucc)))

/-- Riemann sum of the action. -/
noncomputable def rsum (z : ℝ → Phase n) {N : ℕ} (t : Fin (N + 1) → ℝ) : ℝ :=
  1 / 2 * ∑ i : Fin N, phaseInner (J (z (t i.castSucc))) (z (t i.succ) - z (t i.castSucc))

/-- The one-sided directional derivative `h_K'(u; d)` of the support function (the difference
quotient decreases as the step decreases, so the infimum over steps `1/(k+1)` is the limit). -/
noncomputable def dd (K : Set (Phase n)) (u d : Phase n) : ℝ :=
  ⨅ k : ℕ, (supp K (u + ((1 : ℝ) / (k + 1)) • d) - supp K u) * (k + 1)

end Viterbo.CL
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartP
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
/-!
# Part P of the Clarke blueprint: partition sums for the `K`-length and the action

* `isAC_of_lipschitz`: Lipschitz curves are absolutely continuous with velocity `deriv z`
  (Rademacher plus the real Lipschitz FTC, tested against the linear functionals `⟨·, w⟩`).
* `psum_le_ell`: Jensen for the sublinear support function on each cell.
* `exists_ell_le_psum`: approximate the velocity in `L¹` by a continuous `g`; on each fine cell
  compare with the constant `g(tᵢ)`.
* `tendsto_rsum`, `abs_action_sub_rsum_le`: `A(z) - rsum = ½ Σ ∫_{Iᵢ} ⟨J(z(s) - z(tᵢ)), v(s)⟩`.
-/
/-! ### Small helpers -/
lemma pI_negJ (x y : Phase n) : phaseInner x (-J y) = phaseInner (J x) y := by
  rw [← pI_J_J, J_neg, J_J, neg_neg]

lemma norm_J (x : Phase n) : ‖J x‖ = ‖x‖ := by
  rw [← norm_neg, norm_negJ]

lemma supp_smul (K : Set (Phase n)) {c : ℝ} (hc : 0 ≤ c) (u : Phase n) :
    supp K (c • u) = c * supp K u := by
  unfold supp
  have : (fun x => phaseInner x (c • u)) '' K = c • ((fun x => phaseInner x u) '' K) := by
    rw [← Set.image_smul, Set.image_image]
    simp [pI_smul_right]
  rw [this, Real.sSup_smul_of_nonneg hc, smul_eq_mul]

lemma pI_self_eq_zero {x : Phase n} (h : phaseInner x x = 0) : x = 0 := by
  have h1 := norm_sq_le_pI x
  rw [h] at h1
  have h2 : ‖x‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

lemma ext_pI {x y : Phase n} (h : ∀ w, phaseInner x w = phaseInner y w) : x = y := by
  have h1 := h (x - y)
  have : phaseInner (x - y) (x - y) = 0 := by rw [pI_sub_left, h1, sub_self]
  exact sub_eq_zero.1 (pI_self_eq_zero this)

lemma ii_norm_sub {v g : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hg : LocallyIntegrable g volume) (a b : ℝ) :
    IntervalIntegrable (fun s => ‖v s - g s‖) volume a b :=
  (ii_of_li (hv.sub hg) a b).norm

lemma part_mem {N : ℕ} {t : Fin (N + 1) → ℝ} (ht : IsPart t) (i : Fin (N + 1)) :
    0 ≤ t i ∧ t i ≤ 1 := by
  constructor
  · rw [← ht.1]; exact ht.2.2.monotone (Fin.zero_le _)
  · rw [← ht.2.1]; exact ht.2.2.monotone (Fin.le_last _)

lemma part_le {N : ℕ} {t : Fin (N + 1) → ℝ} (ht : IsPart t) (i : Fin N) :
    t i.castSucc ≤ t i.succ :=
  ht.2.2.monotone (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le

/-- The uniform partition `i / N`. -/
lemma unif_part {N : ℕ} (hN : 0 < N) :
    IsPart (fun i : Fin (N + 1) => (i : ℝ) / N) ∧
      MeshLE (fun i : Fin (N + 1) => (i : ℝ) / N) (1 / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨⟨by simp, by simp [hN'.ne'], fun i j hij => ?_⟩, fun i => ?_⟩
  · simp only
    apply div_lt_div_of_pos_right _ hN'
    exact_mod_cast hij
  · simp only [Fin.val_succ, Fin.val_castSucc]
    push_cast
    rw [← sub_div]; simp

/-- The integrals over the cells of a partition add up. -/
lemma sum_cells {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : ∀ a b, IntervalIntegrable f volume a b) :
    ∀ (N : ℕ) (t : Fin (N + 1) → ℝ),
      ∑ i : Fin N, ∫ x in t i.castSucc..t i.succ, f x = ∫ x in t 0..t (Fin.last N), f x
  | 0, t => by simp
  | N + 1, t => by
    rw [Fin.sum_univ_castSucc]
    have ih := sum_cells hf N (fun i => t i.castSucc)
    simp only [Fin.succ_castSucc] at ih ⊢
    rw [ih, Fin.castSucc_zero, Fin.succ_last,
      intervalIntegral.integral_add_adjacent_intervals (hf _ _) (hf _ _)]

/-! ### Lipschitz curves -/
lemma lip_ftc {z : ℝ → Phase n} {M : ℝ≥0} (hL : LipschitzWith M z) :
    LocallyIntegrable (deriv z) volume ∧ ∀ a b, z b - z a = ∫ s in a..b, deriv z s := by
  have hb : ∀ t, ‖deriv z t‖ ≤ M := fun t => norm_deriv_le_of_lipschitz hL
  have hli : LocallyIntegrable (deriv z) volume := by
    refine (continuous_const (y := (M : ℝ))).locallyIntegrable.mono
      (measurable_deriv z).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    simpa using hb t
  refine ⟨hli, fun a b => ?_⟩
  refine ext_pI fun w => ?_
  have hfL : LipschitzWith (‖pIL w‖₊ * M) (fun t => phaseInner (z t) w) := by
    have := (pIL w).lipschitz.comp hL
    simpa [Function.comp_def, pIL_apply] using this
  have hftc :=
    (hfL.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hd : ∀ᵐ t, deriv (fun t => phaseInner (z t) w) t = pIL w (deriv z t) := by
    filter_upwards [hL.ae_differentiableAt_real] with t ht
    have := ((pIL w).hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt).deriv
    simpa [Function.comp_def, pIL_apply] using this
  rw [intervalIntegral.integral_congr_ae (hd.mono fun t ht _ => ht),
    (pIL w).intervalIntegral_comp_comm (ii_of_li hli a b)] at hftc
  rw [pI_sub_left, ← pIL_apply w (∫ s in a..b, deriv z s), hftc]

lemma isAC_of_lipschitz {z : ℝ → Phase n} {M : ℝ≥0} (hL : LipschitzWith M z) :
    IsAC z ∧ ∀ t, ‖deriv z t‖ ≤ M :=
  ⟨⟨deriv z, (lip_ftc hL).1, (lip_ftc hL).2⟩, fun _ => norm_deriv_le_of_lipschitz hL⟩

end Viterbo.CL.PartP
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL
open Viterbo Viterbo.CM
variable {n : ℕ}
/-! ## Part P -/
alias isAC_of_lipschitz := Viterbo.CL.PartP.isAC_of_lipschitz

end Viterbo.CL
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartP
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
/-! ### Jensen -/
lemma supp_negJ_le_integral {K : Set (Phase n)} (hK : IsConvexDomain K) {v : ℝ → Phase n}
    (hv : LocallyIntegrable v volume) {a b : ℝ} (hab : a ≤ b) :
    supp K (-J (∫ s in a..b, v s)) ≤ ∫ s in a..b, supp K (-J (v s)) := by
  obtain ⟨k0, hk0⟩ := hK.2.2.mono interior_subset
  refine csSup_le (Set.Nonempty.image _ ⟨k0, hk0⟩) ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only
  rw [pI_negJ, ← integral_pI_const hv]
  refine intervalIntegral.integral_mono_on hab (ii_pI (w := fun _ => J x) continuous_const hv a b)
    (ii_supp hK hv a b) fun s _ => ?_
  rw [← pI_negJ]
  exact le_csSup (bdd_supp hK.1 _) (mem_image_of_mem _ hx)

lemma psum_le_ell {K : Set (Phase n)} (hK : IsConvexDomain K) {z : ℝ → Phase n} (hz : IsAC z)
    {N : ℕ} {t : Fin (N + 1) → ℝ} (ht : IsPart t) : psum K z t ≤ ell K z := by
  obtain ⟨v, hv, hf⟩ := hz
  have hs := sum_cells (ii_supp hK hv) N t
  rw [ht.1, ht.2.1] at hs
  rw [ell_eq hv hf, ← hs]
  unfold psum
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hf]
  exact supp_negJ_le_integral hK hv (part_le ht i)

end Viterbo.CL.PartP
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL
open Viterbo Viterbo.CM
variable {n : ℕ}
alias psum_le_ell := Viterbo.CL.PartP.psum_le_ell

end Viterbo.CL
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartP
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
/-! ### Near-equality for fine partitions -/
lemma cell_bound {K : Set (Phase n)} (hK : IsConvexDomain K) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    {v : ℝ → Phase n} (hv : LocallyIntegrable v volume) {a b : ℝ} (hab : a ≤ b) (c : Phase n) :
    ∫ s in a..b, supp K (-J (v s)) ≤
      supp K (-J (∫ s in a..b, v s)) + 2 * (2 * R * ∫ s in a..b, ‖v s - c‖) := by
  have hne : K.Nonempty := hK.2.2.mono interior_subset
  obtain ⟨k0, hk0⟩ := hne
  have hR0 : 0 ≤ R := (norm_nonneg k0).trans (hR k0 hk0)
  have hvc : IntervalIntegrable (fun s => ‖v s - c‖) volume a b :=
    ii_norm_sub hv (locallyIntegrable_const c) a b
  have h1 : ∫ s in a..b, supp K (-J (v s)) ≤
      ∫ s in a..b, (supp K (-J c) + 2 * R * ‖v s - c‖) := by
    refine intervalIntegral.integral_mono_on hab (ii_supp hK hv a b)
      (intervalIntegrable_const.add (hvc.const_mul _)) fun s _ => ?_
    have := supp_le_add hK.1 ⟨k0, hk0⟩ hR (-J (v s)) (-J c)
    rwa [show -J (v s) - -J c = -J (v s - c) by rw [J_sub]; abel, norm_negJ] at this
  rw [intervalIntegral.integral_add intervalIntegrable_const (hvc.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul] at h1
  have h2 : supp K (-J ((b - a) • c)) = (b - a) * supp K (-J c) := by
    rw [J_smul, ← smul_neg, supp_smul K (sub_nonneg.2 hab)]
  have h3 := supp_le_add hK.1 ⟨k0, hk0⟩ hR (-J ((b - a) • c)) (-J (∫ s in a..b, v s))
  have e3 : ‖-J ((b - a) • c) - -J (∫ s in a..b, v s)‖ ≤ ∫ s in a..b, ‖v s - c‖ := by
    rw [show -J ((b - a) • c) - -J (∫ s in a..b, v s) = -J ((b - a) • c - ∫ s in a..b, v s) by
      rw [J_sub]; abel, norm_negJ, ← intervalIntegral.integral_const,
      ← intervalIntegral.integral_sub intervalIntegrable_const (ii_of_li hv a b)]
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
    congr 1; ext s; rw [norm_sub_rev]
  have h4 := mul_le_mul_of_nonneg_left e3 (by positivity : (0 : ℝ) ≤ 2 * R)
  rw [h2] at h3
  linarith

lemma exists_ell_le_psum {K : Set (Phase n)} (hK : IsConvexDomain K) {z : ℝ → Phase n}
    (hz : IsAC z) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (t : Fin (N + 1) → ℝ), IsPart t ∧ ell K z ≤ psum K z t + ε := by
  obtain ⟨v, hv, hf⟩ := hz
  obtain ⟨R, hR⟩ := hK.1.exists_norm_le
  obtain ⟨k0, hk0⟩ := hK.2.2.mono interior_subset
  have hR0 : 0 ≤ R := (norm_nonneg k0).trans (hR k0 hk0)
  set η : ℝ := ε / (2 * (4 * R + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hεη : ε = 8 * R * η + 2 * η := by rw [hη]; field_simp; ring
  have hvi : Integrable v (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hv.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  obtain ⟨g, hg, -⟩ := hvi.exists_boundedContinuous_integral_sub_le hη0
  have hgu : UniformContinuousOn g (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous g.continuous.continuousOn
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuousOn_iff.1 hgu η hη0
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  obtain ⟨hpart, hmesh⟩ := unif_part (Nat.succ_pos N)
  refine ⟨N + 1, _, hpart, ?_⟩
  set t : Fin (N + 1 + 1) → ℝ := fun i : Fin (N + 1 + 1) => (i : ℝ) / ((N + 1 : ℕ) : ℝ)
  have hvg : ∀ a b, IntervalIntegrable (fun s => ‖v s - g s‖ + η) volume a b := fun a b =>
    (ii_norm_sub hv g.continuous.locallyIntegrable a b).add intervalIntegrable_const
  have key : ∀ i : Fin (N + 1), ∫ s in t i.castSucc..t i.succ, supp K (-J (v s)) ≤
      supp K (-J (z (t i.succ) - z (t i.castSucc))) +
        4 * R * ∫ s in t i.castSucc..t i.succ, (‖v s - g s‖ + η) := by
    intro i
    set a := t i.castSucc
    set b := t i.succ
    have hab : a ≤ b := part_le hpart i
    have ha := part_mem hpart i.castSucc
    have hb := part_mem hpart i.succ
    have hba : b - a < δ := by
      have := hmesh i
      push_cast at this hN ⊢
      linarith
    have h1 := cell_bound hK hR hv hab (g a)
    have h2 : ∫ s in a..b, ‖v s - g a‖ ≤ ∫ s in a..b, (‖v s - g s‖ + η) := by
      refine intervalIntegral.integral_mono_on hab
        (ii_norm_sub hv (locallyIntegrable_const (g a)) a b) (hvg a b)
        fun s hs => ?_
      have hd := hgδ s ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩ a ha
        (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
      rw [dist_eq_norm] at hd
      calc ‖v s - g a‖ ≤ ‖v s - g s‖ + ‖g s - g a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖v s - g s‖ + η := by linarith
    rw [hf]
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * R)
    linarith
  have hs1 := sum_cells (ii_supp hK hv) (N + 1) t
  have hs2 := sum_cells hvg (N + 1) t
  rw [hpart.1, hpart.2.1] at hs1 hs2
  have hI : ∫ s in (0 : ℝ)..1, (‖v s - g s‖ + η) ≤ 2 * η := by
    rw [intervalIntegral.integral_add (ii_norm_sub hv g.continuous.locallyIntegrable 0 1)
      intervalIntegrable_const, intervalIntegral.integral_const, intervalIntegral.integral_of_le
      zero_le_one]
    simp only [sub_zero, one_smul]
    linarith
  calc ell K z = ∑ i : Fin (N + 1), ∫ s in t i.castSucc..t i.succ, supp K (-J (v s)) := by
        rw [ell_eq hv hf, hs1]
    _ ≤ ∑ i : Fin (N + 1), (supp K (-J (z (t i.succ) - z (t i.castSucc))) +
        4 * R * ∫ s in t i.castSucc..t i.succ, (‖v s - g s‖ + η)) := Finset.sum_le_sum fun i _ => key i
    _ = psum K z t + 4 * R * ∫ s in (0 : ℝ)..1, (‖v s - g s‖ + η) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs2]; rfl
    _ ≤ psum K z t + ε := by
        have := mul_le_mul_of_nonneg_left hI (by positivity : (0 : ℝ) ≤ 4 * R)
        linarith

end Viterbo.CL.PartP
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL
open Viterbo Viterbo.CM
variable {n : ℕ}
alias exists_ell_le_psum := Viterbo.CL.PartP.exists_ell_le_psum

end Viterbo.CL
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartP
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
/-! ### Riemann sums of the action -/
lemma action_sub_rsum {z v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, z b - z a = ∫ s in a..b, v s) {N : ℕ} {t : Fin (N + 1) → ℝ} (ht : IsPart t) :
    action z - rsum z t = 1 / 2 * ∑ i : Fin N,
      ∫ s in t i.castSucc..t i.succ, phaseInner (J (z s - z (t i.castSucc))) (v s) := by
  have hzc := cont_of_ac hv hf
  have hii : ∀ a b, IntervalIntegrable (fun s => phaseInner (J (z s)) (v s)) volume a b :=
    ii_pI (w := fun s => J (z s)) (continuous_J.comp hzc) hv
  have hs := sum_cells hii N t
  rw [ht.1, ht.2.1] at hs
  rw [action_eq hv hf, ← hs]
  unfold rsum
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf, ← integral_pI_const hv,
    ← intervalIntegral.integral_sub (hii _ _) (ii_pI (w := fun _ => J (z (t i.castSucc)))
      continuous_const hv _ _)]
  congr 1; ext s; rw [J_sub, pI_sub_left]

lemma abs_action_sub_rsum_le_of {z v : ℝ → Phase n} (hv : LocallyIntegrable v volume)
    (hf : ∀ a b, z b - z a = ∫ s in a..b, v s) {N : ℕ} {t : Fin (N + 1) → ℝ} (ht : IsPart t)
    {η : ℝ} (hη : ∀ i : Fin N, ∀ s ∈ Icc (t i.castSucc) (t i.succ), ‖z s - z (t i.castSucc)‖ ≤ η) :
    |action z - rsum z t| ≤ η * ∫ s in (0 : ℝ)..1, ‖v s‖ := by
  have hzc := cont_of_ac hv hf
  rw [action_sub_rsum hv hf ht]
  have hvn : ∀ a b, IntervalIntegrable (fun s => ‖v s‖) volume a b :=
    fun a b => (ii_of_li hv a b).norm
  have hs := sum_cells hvn N t
  rw [ht.1, ht.2.1] at hs
  rw [← hs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle := part_le ht i
  refine (mul_le_mul_of_nonneg_left (intervalIntegral.abs_integral_le_integral_abs hle)
    (by norm_num)).trans ?_
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hle ?_ ((hvn _ _).const_mul η) fun s hs => ?_
  · exact ((ii_pI (w := fun s => J (z s - z (t i.castSucc)))
      (continuous_J.comp (hzc.sub continuous_const)) hv _ _).abs).const_mul _
  · have h1 := abs_pI_le (J (z s - z (t i.castSucc))) (v s)
    rw [norm_J] at h1
    have h2 := hη i s hs
    have h3 := norm_nonneg (v s)
    nlinarith

lemma tendsto_rsum {z : ℝ → Phase n} (hz : IsLoop z) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (N : ℕ) (t : Fin (N + 1) → ℝ), IsPart t → MeshLE t δ →
      |action z - rsum z t| ≤ ε := by
  obtain ⟨-, v, hv, hf⟩ := hz
  have hzc := cont_of_ac hv hf
  set V := ∫ s in (0 : ℝ)..1, ‖v s‖
  have hV : 0 ≤ V := intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
  have hη : 0 < ε / (V + 1) := by positivity
  obtain ⟨δ, hδ, hzδ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).uniformContinuousOn_of_continuous hzc.continuousOn) _ hη
  refine ⟨δ / 2, by positivity, fun N t ht hm => ?_⟩
  refine (abs_action_sub_rsum_le_of hv hf ht (η := ε / (V + 1)) fun i s hs => ?_).trans ?_
  · have hi := part_mem ht i.castSucc
    have hj := part_mem ht i.succ
    have := hzδ s ⟨hi.1.trans hs.1, hs.2.trans hj.2⟩ (t i.castSucc) hi
      (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hm i, hs.1, hs.2])
    rw [dist_eq_norm] at this
    exact this.le
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith

end Viterbo.CL.PartP
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL
open Viterbo Viterbo.CM
variable {n : ℕ}
alias tendsto_rsum := Viterbo.CL.PartP.tendsto_rsum

end Viterbo.CL
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartP
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
lemma abs_action_sub_rsum_le {z : ℝ → Phase n} {M : ℝ≥0} (hz : Function.Periodic z 1)
    (hL : LipschitzWith M z) {δ : ℝ} {N : ℕ} {t : Fin (N + 1) → ℝ} (ht : IsPart t)
    (hδ : MeshLE t δ) : |action z - rsum z t| ≤ 2 * (M : ℝ) ^ 2 * δ := by
  obtain ⟨hli, hf⟩ := lip_ftc hL
  have hδ0 : 0 ≤ δ := by
    cases N with
    | zero =>
      exfalso
      have h1 := ht.2.1
      rw [show Fin.last 0 = 0 from rfl, ht.1] at h1
      exact zero_ne_one h1
    | succ N =>
      have h1 := hδ 0
      have h2 := ht.2.2 (show (0 : Fin (N + 1)).castSucc < (0 : Fin (N + 1)).succ from Fin.castSucc_lt_succ)
      linarith
  have hM : ∫ s in (0 : ℝ)..1, ‖deriv z s‖ ≤ M := by
    have := intervalIntegral.integral_mono_on zero_le_one (ii_of_li hli 0 1).norm
      (intervalIntegrable_const (c := (M : ℝ))) fun s _ => norm_deriv_le_of_lipschitz hL
    simpa using this
  refine (abs_action_sub_rsum_le_of hli hf ht (η := M * δ) fun i s hs => ?_).trans ?_
  · have := hL.dist_le_mul s (t i.castSucc)
    rw [dist_eq_norm, Real.dist_eq, abs_of_nonneg (by linarith [hs.1])] at this
    have h2 : s - t i.castSucc ≤ δ := by linarith [hs.2, hδ i]
    exact this.trans (mul_le_mul_of_nonneg_left h2 M.2)
  · have hM0 : (0 : ℝ) ≤ M := M.2
    have hint0 : 0 ≤ ∫ s in (0 : ℝ)..1, ‖deriv z s‖ :=
      intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
    nlinarith [mul_nonneg hM0 hδ0, mul_nonneg (mul_nonneg hM0 hM0) hδ0]

end Viterbo.CL.PartP
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL
open Viterbo Viterbo.CM
variable {n : ℕ}
alias abs_action_sub_rsum_le := Viterbo.CL.PartP.abs_action_sub_rsum_le

end Viterbo.CL
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartR
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
/-!
# Part R of the Clarke blueprint: Lipschitz reparametrization of loops

`exists_reparam`: every loop can be reparametrized (by an orientation-preserving homeomorphism
commuting with `t ↦ t + 1`) into a Lipschitz loop with the same `K`-length and action.
-/
/-- With a ball `B(x0, r) ⊆ K`, `h_K(u) - ⟨x0, u⟩ ≥ (r/2)‖u‖`. -/
lemma supp_lower {K : Set (Phase n)} (hK : IsConvexDomain K) {x0 : Phase n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x0 r ⊆ K) (u : Phase n) :
    r / 2 * ‖u‖ ≤ supp K u - phaseInner x0 u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [supp_zero ⟨x0, hball (Metric.mem_ball_self hr)⟩, pI_zero_right]; simp
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
  set s := r / (2 * ‖u‖) with hs
  have hs0 : 0 < s := by positivity
  have hsu : s * ‖u‖ = r / 2 := by rw [hs]; field_simp
  have hz : x0 + s • u ∈ K := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs0, hsu]
    linarith)
  have h1 : phaseInner (x0 + s • u) u ≤ supp K u :=
    le_csSup (bdd_supp hK.1 u) (mem_image_of_mem _ hz)
  rw [pI_add_left, pI_smul_left] at h1
  have h2 := norm_sq_le_pI u
  have : r / 2 * ‖u‖ = s * ‖u‖ ^ 2 := by rw [← hsu]; ring
  nlinarith [mul_le_mul_of_nonneg_left h2 hs0.le]

lemma pI_negJ (x y : Phase n) : phaseInner x (-J y) = phaseInner (J x) y := by
  rw [← pI_J_J, J_neg, J_J, neg_neg]

/-- The uniform partition `i / N`. -/
lemma unif_part {N : ℕ} (hN : 0 < N) :
    IsPart (fun i : Fin (N + 1) => (i : ℝ) / N) ∧
      MeshLE (fun i : Fin (N + 1) => (i : ℝ) / N) (1 / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨⟨by simp, by simp [hN'.ne'], fun i j hij => ?_⟩, fun i => ?_⟩
  · simp only
    apply div_lt_div_of_pos_right _ hN'
    exact_mod_cast hij
  · simp only [Fin.val_succ, Fin.val_castSucc]
    push_cast
    rw [← sub_div]; simp

/-- The abstract reparametrization step: given the homeomorphism `e` (playing `φ`). -/
lemma reparam_of_phi {K : Set (Phase n)} (hK : IsConvexDomain K) {z : ℝ → Phase n}
    (hz : IsLoop z) (e : ℝ ≃o ℝ) (he0 : e 0 = 0) (he1 : e 1 = 1)
    (hper : ∀ t, e (t + 1) = e t + 1) {Λ : ℝ}
    (hΛ : ∀ a b, a ≤ b → ‖z b - z a‖ ≤ Λ * (e b - e a)) {μ : ℝ}
    (hμ : ∀ a b, a ≤ b → b - a ≤ μ * (e b - e a)) :
    ∃ w : ℝ → Phase n, IsLoop w ∧ LipschitzWith (Real.toNNReal Λ) w ∧
      ell K w = ell K z ∧ action w = action z := by
  set ψ := e.symm with hψdef
  have hψ0 : ψ 0 = 0 := by rw [hψdef, OrderIso.symm_apply_eq, he0]
  have hψ1 : ψ 1 = 1 := by rw [hψdef, OrderIso.symm_apply_eq, he1]
  have hψper : ∀ s, ψ (s + 1) = ψ s + 1 := fun s => by
    rw [hψdef, OrderIso.symm_apply_eq, hper, OrderIso.apply_symm_apply]
  have heψ : ∀ s, e (ψ s) = s := fun s => e.apply_symm_apply s
  have hψe : ∀ t, ψ (e t) = t := fun t => e.symm_apply_apply t
  set w : ℝ → Phase n := fun s => z (ψ s) with hwdef
  have hwp : Function.Periodic w 1 := fun s => by
    simp only [hwdef, hψper]; exact hz.1 _
  have hwL : LipschitzWith (Real.toNNReal Λ) w := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have key : ∀ x y : ℝ, y ≤ x → dist (w x) (w y) ≤ (Real.toNNReal Λ : ℝ) * dist x y := by
      intro x y hxy
      have hψ : ψ y ≤ ψ x := ψ.monotone hxy
      rw [dist_eq_norm, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hxy)]
      calc ‖z (ψ x) - z (ψ y)‖ ≤ Λ * (e (ψ x) - e (ψ y)) := hΛ _ _ hψ
        _ = Λ * (x - y) := by rw [heψ, heψ]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal Λ) (sub_nonneg.2 hxy)
    rcases le_total y x with h | h
    · exact key x y h
    · rw [dist_comm, dist_comm x y]; exact key y x h
  have hwloop : IsLoop w := ⟨hwp, (isAC_of_lipschitz hwL).1⟩
  have hpartψ : ∀ {N : ℕ} {t : Fin (N + 1) → ℝ}, IsPart t → IsPart (ψ ∘ t) := by
    intro N t ht
    exact ⟨by simp [ht.1, hψ0], by simp [ht.2.1, hψ1], ψ.strictMono.comp ht.2.2⟩
  have hparte : ∀ {N : ℕ} {t : Fin (N + 1) → ℝ}, IsPart t → IsPart (e ∘ t) := by
    intro N t ht
    exact ⟨by simp [ht.1, he0], by simp [ht.2.1, he1], e.strictMono.comp ht.2.2⟩
  refine ⟨w, hwloop, hwL, ?_, ?_⟩
  · apply le_antisymm
    · refine le_of_forall_pos_le_add fun δ hδ => ?_
      obtain ⟨N, t, ht, hle⟩ := exists_ell_le_psum hK hwloop.2 hδ
      have : psum K w t = psum K z (ψ ∘ t) := rfl
      linarith [psum_le_ell hK hz.2 (hpartψ ht)]
    · refine le_of_forall_pos_le_add fun δ hδ => ?_
      obtain ⟨N, t, ht, hle⟩ := exists_ell_le_psum hK hz.2 hδ
      have : psum K z t = psum K w (e ∘ t) := by
        unfold psum; simp only [hwdef, Function.comp, hψe]
      linarith [psum_le_ell hK hwloop.2 (hparte ht)]
  · refine eq_of_forall_dist_le fun δ hδ => ?_
    obtain ⟨δw, hδw, hw⟩ := tendsto_rsum hwloop (half_pos hδ)
    obtain ⟨δz, hδz, hzr⟩ := tendsto_rsum hz (half_pos hδ)
    -- `μ ≥ 0`
    have hμ0 : 0 ≤ μ := by
      have h1 := hμ 0 1 zero_le_one
      rw [he0, he1] at h1
      linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / δw) ((μ + 1) / δz))
    have hNpos : (0 : ℝ) < N :=
      lt_of_le_of_lt (le_max_of_le_left (by positivity)) hN
    have hN0 : 0 < N := by exact_mod_cast hNpos
    obtain ⟨hpt, hmesh⟩ := unif_part hN0
    set t : Fin (N + 1) → ℝ := fun i => (i : ℝ) / N
    have hmw : MeshLE t δw := fun i => by
      refine (hmesh i).trans ?_
      rw [div_le_iff₀ hNpos]
      have := (le_max_left _ _).trans hN.le
      rw [div_le_iff₀ hδw] at this
      linarith
    have hmz : MeshLE (ψ ∘ t) δz := fun i => by
      have h1 := hμ _ _ (ψ.monotone (hpt.2.2.monotone (Fin.castSucc_le_succ i)))
      simp only [Function.comp, heψ] at h1 ⊢
      have h2 := hmesh i
      have h3 : μ * (t i.succ - t i.castSucc) ≤ μ * (1 / N) := mul_le_mul_of_nonneg_left h2 hμ0
      have h4 : μ * (1 / N) ≤ δz := by
        have := (le_max_right _ _).trans hN.le
        rw [div_le_iff₀ hδz] at this
        rw [mul_one_div, div_le_iff₀ hNpos]
        nlinarith
      linarith
    have e1 := hw N t hpt hmw
    have e2 := hzr N (ψ ∘ t) (hpartψ hpt) hmz
    have : rsum w t = rsum z (ψ ∘ t) := rfl
    rw [Real.dist_eq]
    rw [this] at e1
    calc |action w - action z| = |(action w - rsum z (ψ ∘ t)) - (action z - rsum z (ψ ∘ t))| := by
          ring_nf
      _ ≤ |action w - rsum z (ψ ∘ t)| + |action z - rsum z (ψ ∘ t)| := abs_sub _ _
      _ ≤ δ := by linarith

lemma deriv_periodic {z : ℝ → Phase n} (hz : Function.Periodic z 1) :
    Function.Periodic (deriv z) 1 := fun t => by
  have h : (fun x => z (x + 1)) = z := funext hz
  rw [← deriv_comp_add_const, h]

/-- The construction of `φ`. -/
lemma exists_phi {K : Set (Phase n)} (hK : IsConvexDomain K) {x0 : Phase n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x0 r ⊆ K) {z : ℝ → Phase n} (hz : IsLoop z) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℝ ≃o ℝ, e 0 = 0 ∧ e 1 = 1 ∧ (∀ t, e (t + 1) = e t + 1) ∧
      (∀ a b, a ≤ b → ‖z b - z a‖ ≤ 2 / r * (ell K z + ε) * (e b - e a)) ∧
      ∃ μ : ℝ, ∀ a b, a ≤ b → b - a ≤ μ * (e b - e a) := by
  obtain ⟨v', hv', hf'⟩ := hz.2
  have hv : LocallyIntegrable (deriv z) volume := hv'.congr (Filter.EventuallyEq.symm (deriv_ae hv' hf'))
  have hf : ∀ a b, z b - z a = ∫ s in a..b, deriv z s := fun a b => by
    rw [hf' a b]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [deriv_ae hv' hf'] with t ht _
    rw [ht]
  have hvp := deriv_periodic hz.1
  set g : ℝ → ℝ := fun t =>
    supp K (-J (deriv z t)) - phaseInner (J x0) (deriv z t) + ε with hgdef
  have hgp : Function.Periodic g 1 := fun t => by simp only [hgdef, hvp t]
  have hgi : ∀ a b, IntervalIntegrable g volume a b := fun a b =>
    ((ii_supp hK hv a b).sub (ii_pI (w := fun _ => J x0) continuous_const hv a b)).add
      intervalIntegrable_const
  have hρ : ∀ t, r / 2 * ‖deriv z t‖ ≤
      supp K (-J (deriv z t)) - phaseInner (J x0) (deriv z t) := fun t => by
    have h := supp_lower hK hr hball (-J (deriv z t))
    rwa [norm_negJ, pI_negJ] at h
  have hlow : ∀ t, ‖deriv z t‖ ≤ 2 / r * g t := fun t => by
    have h := hρ t
    simp only [hgdef]
    have e1 : ‖deriv z t‖ = 2 / r * (r / 2 * ‖deriv z t‖) := by field_simp
    rw [e1]
    have : 0 ≤ 2 / r := by positivity
    nlinarith
  have hgε : ∀ t, ε ≤ g t := fun t => by
    have h := hρ t
    simp only [hgdef]
    have : 0 ≤ r / 2 * ‖deriv z t‖ := by positivity
    linarith
  set c := ell K z + ε with hcdef
  have hc : 0 < c := by linarith [ell_nonneg hK hz.1 hz.2]
  have hint01 : ∫ t in (0 : ℝ)..1, g t = c := by
    simp only [hgdef]
    rw [intervalIntegral.integral_add ((ii_supp hK hv 0 1).sub
        (ii_pI (w := fun _ => J x0) continuous_const hv 0 1)) intervalIntegrable_const,
      intervalIntegral.integral_sub (ii_supp hK hv 0 1)
        (ii_pI (w := fun _ => J x0) continuous_const hv 0 1),
      integral_pI_const hv, ← hf 0 1, show z 1 = z 0 by simpa using hz.1 0, sub_self,
      pI_zero_right, intervalIntegral.integral_const]
    simp [hcdef, ell, supp]
  have hper1 : ∀ t, ∫ s in t..t + 1, g s = c := fun t => by
    rw [hgp.intervalIntegral_add_eq t 0, zero_add, hint01]
  have hmono : ∀ a b, a ≤ b → ε * (b - a) ≤ ∫ s in a..b, g s := fun a b hab => by
    have := intervalIntegral.integral_mono_on hab intervalIntegrable_const (hgi a b)
      (fun t _ => hgε t)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  set F : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, g s) / c with hFdef
  have hFsub : ∀ a b, F b - F a = (∫ s in a..b, g s) / c := fun a b => by
    simp only [hFdef]
    rw [← sub_div, intervalIntegral.integral_interval_sub_left (hgi 0 b) (hgi 0 a)]
  have hFcont : Continuous F :=
    (intervalIntegral.continuous_primitive hgi 0).div_const c
  have hFlow : ∀ a b, a ≤ b → ε / c * (b - a) ≤ F b - F a := fun a b hab => by
    rw [hFsub, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc]
    exact hmono a b hab
  have hF0 : F 0 = 0 := by simp [hFdef]
  have hFsm : StrictMono F := fun a b hab => by
    have := hFlow a b hab.le
    have : 0 < ε / c * (b - a) := by have := sub_pos.2 hab; positivity
    linarith
  have hεc : 0 < ε / c := by positivity
  have htop : Tendsto F atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id.const_mul_atTop hεc)
    filter_upwards [eventually_ge_atTop 0] with t ht
    have := hFlow 0 t ht
    simp only [hF0, sub_zero, id] at this ⊢
    exact this
  have hbot : Tendsto F atBot atBot := by
    refine tendsto_atBot_mono' atBot ?_ (tendsto_id.const_mul_atBot hεc)
    filter_upwards [eventually_le_atBot 0] with t ht
    have := hFlow t 0 ht
    simp only [hF0, zero_sub, id] at this ⊢
    linarith
  set e := StrictMono.orderIsoOfSurjective F hFsm (hFcont.surjective htop hbot)
  have he : ∀ t, e t = F t := fun t => rfl
  refine ⟨e, by rw [he, hF0], ?_, ?_, ?_, ⟨c / ε, fun a b hab => ?_⟩⟩
  · rw [he]; simp only [hFdef]; rw [hint01, div_self hc.ne']
  · intro t
    rw [he, he, ← sub_eq_iff_eq_add', hFsub, hper1, div_self hc.ne']
  · intro a b hab
    rw [he, he, hFsub, hf a b]
    calc ‖∫ s in a..b, deriv z s‖ ≤ ∫ s in a..b, ‖deriv z s‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ s in a..b, 2 / r * g s :=
          intervalIntegral.integral_mono_on hab (ii_of_li hv a b).norm
            ((hgi a b).const_mul _) (fun t _ => hlow t)
      _ = 2 / r * c * ((∫ s in a..b, g s) / c) := by
          rw [intervalIntegral.integral_const_mul]; field_simp
  · rw [he, he]
    have := hFlow a b hab
    rw [div_mul_eq_mul_div, div_le_iff₀ hc] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    linarith

lemma exists_reparam {K : Set (Phase n)} (hK : IsConvexDomain K) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ z : ℝ → Phase n, IsLoop z → ∀ ε : ℝ, 0 < ε →
      ∃ w : ℝ → Phase n, IsLoop w ∧ LipschitzWith (Real.toNNReal (κ * (ell K z + ε))) w ∧
        ell K w = ell K z ∧ action w = action z := by
  obtain ⟨x0, hx0⟩ := hK.2.2
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx0)
  refine ⟨2 / r, by positivity, fun z hz ε hε => ?_⟩
  obtain ⟨e, he0, he1, hper, hΛ, μ, hμ⟩ := exists_phi hK hr hball hz hε
  exact reparam_of_phi hK hz e he0 he1 hper hΛ hμ

end Viterbo.CL.PartR
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL
open Viterbo Viterbo.CM
variable {n : ℕ}
/-! ## Part R -/
alias exists_reparam := Viterbo.CL.PartR.exists_reparam

end Viterbo.CL
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal Real
namespace Viterbo.CL.PartC
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
/-!
# Part C of the Clarke blueprint: the isoperimetric bound and existence of a minimizer

`action_le_ell_sq`: `A(z) ≤ C ℓ(z)²` on loops.
`exists_minimizer`: maximize `A` over the set of `κ`-Lipschitz periodic `w` with `w 0 = 0` and all
partition sums `≤ 1`; that set is compact in the topology of pointwise convergence (Tychonoff),
`A` is continuous on it (uniform limit of Riemann sums), and the maximizer minimizes `ℓ² / A`.
-/
/-- With a ball `B(x0, r) ⊆ K`, `h_K(u) - ⟨x0, u⟩ ≥ (r/2)‖u‖`. -/
lemma supp_lower {K : Set (Phase n)} (hK : IsConvexDomain K) {x0 : Phase n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x0 r ⊆ K) (u : Phase n) :
    r / 2 * ‖u‖ ≤ supp K u - phaseInner x0 u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [supp_zero ⟨x0, hball (Metric.mem_ball_self hr)⟩, pI_zero_right]; simp
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
  set s := r / (2 * ‖u‖) with hs
  have hs0 : 0 < s := by positivity
  have hsu : s * ‖u‖ = r / 2 := by rw [hs]; field_simp
  have hz : x0 + s • u ∈ K := hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs0, hsu]
    linarith)
  have h1 : phaseInner (x0 + s • u) u ≤ supp K u :=
    le_csSup (bdd_supp hK.1 u) (mem_image_of_mem _ hz)
  rw [pI_add_left, pI_smul_left] at h1
  have h2 := norm_sq_le_pI u
  have : r / 2 * ‖u‖ = s * ‖u‖ ^ 2 := by rw [← hsu]; ring
  nlinarith [mul_le_mul_of_nonneg_left h2 hs0.le]

lemma pI_negJ (x y : Phase n) : phaseInner x (-J y) = phaseInner (J x) y := by
  rw [← pI_J_J, J_neg, J_J, neg_neg]

lemma norm_J (x : Phase n) : ‖J x‖ = ‖x‖ := by
  rw [← norm_neg, norm_negJ]

/-- The action is unchanged by translating a loop. -/
lemma action_sub_const {z v : ℝ → Phase n} (hz : Function.Periodic z 1)
    (hv : LocallyIntegrable v volume) (hf : ∀ a b, z b - z a = ∫ s in a..b, v s) (p : Phase n) :
    action (fun t => z t - p) = action z := by
  have hf' : ∀ a b, (fun t => z t - p) b - (fun t => z t - p) a = ∫ s in a..b, v s := by
    intro a b; simp only [sub_sub_sub_cancel_right]; exact hf a b
  have hzc := cont_of_ac hv hf
  rw [action_eq hv hf', action_eq hv hf]
  have e : ∀ t, phaseInner (J (z t - p)) (v t) =
      phaseInner (J (z t)) (v t) - phaseInner (J p) (v t) := fun t => by
    rw [J_sub, pI_sub_left]
  simp only [e]
  rw [intervalIntegral.integral_sub (ii_pI (w := fun t => J (z t)) (continuous_J.comp hzc) hv 0 1)
    (ii_pI (w := fun _ => J p) continuous_const hv 0 1), integral_pI_const hv, ← hf 0 1,
    show z 1 = z 0 by simpa using hz 0, sub_self, pI_zero_right, sub_zero]

lemma action_le_ell_sq {K : Set (Phase n)} (hK : IsConvexDomain K) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ → Phase n, IsLoop z → action z ≤ C * ell K z ^ 2 := by
  obtain ⟨x0, hx0⟩ := hK.2.2
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx0)
  refine ⟨(2 / r) ^ 2, by positivity, fun z hz => ?_⟩
  obtain ⟨v, hv, hf⟩ := hz.2
  have hzc := cont_of_ac hv hf
  set V := ∫ t in (0 : ℝ)..1, ‖v t‖ with hV
  have hV0 : 0 ≤ V := intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)
  -- `ℓ ≥ (r/2) V`
  have hell : r / 2 * V ≤ ell K z := by
    rw [ell_eq hv hf]
    have h0 : ∫ t in (0 : ℝ)..1, phaseInner (J x0) (v t) = 0 := by
      rw [integral_pI_const hv, ← hf 0 1, show z 1 = z 0 by simpa using hz.1 0, sub_self,
        pI_zero_right]
    have hm := intervalIntegral.integral_mono_on zero_le_one
      (((ii_of_li hv 0 1).norm.const_mul (r / 2)).add
        (ii_pI (w := fun _ => J x0) continuous_const hv 0 1))
      (ii_supp hK hv 0 1) (fun t _ => by
        have h := supp_lower hK hr hball (-J (v t))
        rw [norm_negJ, pI_negJ] at h
        show r / 2 * ‖v t‖ + phaseInner (J x0) (v t) ≤ supp K (-J (v t))
        linarith)
    rw [intervalIntegral.integral_add ((ii_of_li hv 0 1).norm.const_mul (r / 2))
      (ii_pI (w := fun _ => J x0) continuous_const hv 0 1), h0, add_zero,
      intervalIntegral.integral_const_mul] at hm
    exact hm
  -- `A ≤ V²`
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, ‖z t - z 0‖ ≤ V := fun t ht => by
    rw [hf 0 t]
    refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
    rw [hV, ← intervalIntegral.integral_add_adjacent_intervals ((ii_of_li hv 0 t).norm)
      ((ii_of_li hv t 1).norm)]
    have := intervalIntegral.integral_nonneg (μ := volume) ht.2 (fun s _ => norm_nonneg (v s))
    linarith
  have hA : action z ≤ V ^ 2 := by
    rw [← action_sub_const hz.1 hv hf (z 0)]
    have hf' : ∀ a b, (fun t => z t - z 0) b - (fun t => z t - z 0) a = ∫ s in a..b, v s := by
      intro a b; simp only [sub_sub_sub_cancel_right]; exact hf a b
    rw [action_eq hv hf']
    have hm := intervalIntegral.integral_mono_on zero_le_one
      (ii_pI (w := fun t => J (z t - z 0)) (continuous_J.comp (hzc.sub continuous_const)) hv 0 1)
      ((ii_of_li hv 0 1).norm.const_mul (2 * V)) (fun t ht => by
        have h1 := abs_pI_le (J (z t - z 0)) (v t)
        rw [norm_J] at h1
        have h2 : 2 * ‖z t - z 0‖ * ‖v t‖ ≤ 2 * V * ‖v t‖ := by
          have := hbd t ht
          have := norm_nonneg (v t)
          nlinarith
        exact (le_abs_self _).trans (h1.trans h2))
    rw [intervalIntegral.integral_const_mul] at hm
    nlinarith
  have hV' : V ≤ 2 / r * ell K z := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]; linarith
  calc action z ≤ V ^ 2 := hA
    _ ≤ (2 / r * ell K z) ^ 2 := pow_le_pow_left₀ hV0 hV' 2
    _ = (2 / r) ^ 2 * ell K z ^ 2 := by ring

end Viterbo.CL.PartC
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL
open Viterbo Viterbo.CM
variable {n : ℕ}
/-! ## Part C -/
alias action_le_ell_sq := Viterbo.CL.PartC.action_le_ell_sq

end Viterbo.CL
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal Real
namespace Viterbo.CL.PartC
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
/-! ## The minimizer -/
lemma supp_smul (K : Set (Phase n)) {c : ℝ} (hc : 0 ≤ c) (u : Phase n) :
    supp K (c • u) = c * supp K u := by
  unfold supp
  have : (fun x => phaseInner x (c • u)) '' K = c • ((fun x => phaseInner x u) '' K) := by
    rw [← Set.image_smul, Set.image_image]
    simp [pI_smul_right]
  rw [this, Real.sSup_smul_of_nonneg hc, smul_eq_mul]

lemma continuous_supp {K : Set (Phase n)} (hK : IsConvexDomain K) : Continuous (supp K) := by
  obtain ⟨R, hR⟩ := hK.1.exists_norm_le
  obtain ⟨k0, hk0⟩ := hK.2.2.mono interior_subset
  have hR0 : 0 ≤ R := (norm_nonneg k0).trans (hR k0 hk0)
  have hlip : LipschitzWith (Real.toNNReal (2 * R)) (supp K) := by
    refine LipschitzWith.of_le_add_mul _ fun x y => ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
    exact supp_le_add hK.1 ⟨k0, hk0⟩ hR x y
  exact hlip.continuous

/-- The compact set on which the action is maximized. -/
def SS (K : Set (Phase n)) (L : ℝ≥0) : Set (ℝ → Phase n) :=
  {w | (∀ x y, dist (w x) (w y) ≤ (L : ℝ) * dist x y) ∧ (∀ t, w (t + 1) = w t) ∧ w 0 = 0 ∧
    ∀ (N : ℕ) (t : Fin (N + 1) → ℝ), IsPart t → psum K w t ≤ 1}

lemma cont_eval (x : ℝ) : Continuous fun w : ℝ → Phase n => w x := continuous_apply x

/-- The uniform partition `i / N`. -/
lemma unif_part {N : ℕ} (hN : 0 < N) :
    IsPart (fun i : Fin (N + 1) => (i : ℝ) / N) ∧
      MeshLE (fun i : Fin (N + 1) => (i : ℝ) / N) (1 / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨⟨by simp, by simp [hN'.ne'], fun i j hij => ?_⟩, fun i => ?_⟩
  · simp only
    apply div_lt_div_of_pos_right _ hN'
    exact_mod_cast hij
  · simp only [Fin.val_succ, Fin.val_castSucc]
    push_cast
    rw [← sub_div]; simp

lemma continuous_psum {K : Set (Phase n)} (hK : IsConvexDomain K) {N : ℕ} (t : Fin (N + 1) → ℝ) :
    Continuous fun w : ℝ → Phase n => psum K w t := by
  unfold psum
  refine continuous_finsetSum _ fun i _ => (continuous_supp hK).comp ?_
  exact (continuous_J.comp ((cont_eval _).sub (cont_eval _))).neg

lemma continuous_rsum {N : ℕ} (t : Fin (N + 1) → ℝ) :
    Continuous fun w : ℝ → Phase n => rsum w t := by
  unfold rsum
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
  exact continuous_pI.comp ((continuous_J.comp (cont_eval _)).prodMk
    ((cont_eval _).sub (cont_eval _)))

lemma isCompact_SS {K : Set (Phase n)} (hK : IsConvexDomain K) (L : ℝ≥0) :
    IsCompact (SS K L) := by
  have hcl : IsClosed (SS K L) := by
    unfold SS
    simp only [ofPred_and, ofPred_forall]
    refine ((isClosed_iInter fun x => isClosed_iInter fun y => isClosed_le
      ((cont_eval x).dist (cont_eval y))
      continuous_const).inter ((isClosed_iInter fun t => isClosed_eq (cont_eval (t + 1))
      (cont_eval t)).inter ((isClosed_eq (cont_eval 0) continuous_const).inter
      (isClosed_iInter fun N => isClosed_iInter fun t => isClosed_iInter fun _ =>
        isClosed_le (continuous_psum hK t) continuous_const))))
  refine (isCompact_univ_pi fun t => isCompact_closedBall (0 : Phase n) ((L : ℝ) * |t|)).of_isClosed_subset
    hcl fun w hw => ?_
  intro t _
  have h := hw.1 t 0
  rw [hw.2.2.1, dist_zero_right, Real.dist_eq, sub_zero] at h
  simpa [mem_closedBall_zero_iff] using h

lemma lip_of_SS {K : Set (Phase n)} {L : ℝ≥0} {w : ℝ → Phase n} (hw : w ∈ SS K L) :
    LipschitzWith L w := LipschitzWith.of_dist_le_mul hw.1

lemma per_of_SS {K : Set (Phase n)} {L : ℝ≥0} {w : ℝ → Phase n} (hw : w ∈ SS K L) :
    Function.Periodic w 1 := hw.2.1

lemma continuousOn_action_SS (K : Set (Phase n)) (L : ℝ≥0) :
    ContinuousOn (action (n := n)) (SS K L) := by
  set tN : (N : ℕ) → Fin (N + 1) → ℝ := fun N i => (i : ℝ) / N
  have hU : TendstoUniformlyOn (fun N (w : ℝ → Phase n) => rsum w (tN N)) action atTop
      (SS K L) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * (L : ℝ) ^ 2 / ε)
    filter_upwards [eventually_ge_atTop (N0 + 1)] with N hN w hw
    have hNpos : 0 < N := by omega
    have hNr : (N0 : ℝ) + 1 ≤ N := by exact_mod_cast hN
    obtain ⟨hpt, hmesh⟩ := unif_part hNpos
    have h := abs_action_sub_rsum_le (per_of_SS hw) (lip_of_SS hw) hpt hmesh
    rw [Real.dist_eq]
    refine h.trans_lt ?_
    have hNp : (0 : ℝ) < N := by positivity
    rw [div_lt_iff₀ hε] at hN0
    rw [mul_one_div, div_lt_iff₀ hNp]
    nlinarith
  exact hU.continuousOn (Eventually.of_forall fun N => (continuous_rsum (tN N)).continuousOn).frequently

lemma zero_mem_SS {K : Set (Phase n)} (hK : IsConvexDomain K) (L : ℝ≥0) :
    (fun _ => (0 : Phase n)) ∈ SS K L := by
  refine ⟨fun x y => by simp; positivity, fun t => rfl, rfl, fun N t _ => ?_⟩
  have hJ : J (0 : Phase n) = 0 := Prod.ext (by simp [J]) (by simp [J])
  unfold psum
  simp [hJ, supp_zero (hK.2.2.mono interior_subset)]

/-- Every loop, reparametrized, scaled and translated, lands in `SS K κ`. -/
lemma embed_SS {K : Set (Phase n)} (hK : IsConvexDomain K) {κ : ℝ} (hκ : 0 < κ)
    (hrep : ∀ z : ℝ → Phase n, IsLoop z → ∀ ε : ℝ, 0 < ε →
      ∃ w : ℝ → Phase n, IsLoop w ∧ LipschitzWith (Real.toNNReal (κ * (ell K z + ε))) w ∧
        ell K w = ell K z ∧ action w = action z)
    {z : ℝ → Phase n} (hz : IsLoop z) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ SS K (Real.toNNReal κ), action w * (ell K z + ε) ^ 2 = action z := by
  obtain ⟨w, hwl, hwL, hwe, hwa⟩ := hrep z hz ε hε
  have hℓ := ell_nonneg hK hz.1 hz.2
  have hpos : 0 < ell K z + ε := by linarith
  set c := (ell K z + ε)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 hpos
  obtain ⟨v, hv, hf⟩ := hwl.2
  have hf' : ∀ a b, (fun t => w t - w 0) b - (fun t => w t - w 0) a = ∫ s in a..b, v s := by
    intro a b; simp only [sub_sub_sub_cancel_right]; exact hf a b
  refine ⟨fun t => c • (w t - w 0), ⟨fun x y => ?_, fun t => ?_, ?_, fun N t ht => ?_⟩, ?_⟩
  · rw [dist_smul₀, dist_sub_right, Real.norm_eq_abs, abs_of_pos hc0,
      Real.coe_toNNReal _ hκ.le]
    have h := hwL.dist_le_mul x y
    rw [Real.coe_toNNReal _ (by positivity)] at h
    calc c * dist (w x) (w y) ≤ c * (κ * (ell K z + ε) * dist x y) :=
          mul_le_mul_of_nonneg_left h hc0.le
      _ = κ * dist x y := by rw [hc]; field_simp
  · simp only [hwl.1 t]
  · simp
  · have e : psum K (fun t => c • (w t - w 0)) t = c * psum K w t := by
      unfold psum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← smul_sub, sub_sub_sub_cancel_right, J_smul, ← smul_neg, supp_smul K hc0.le]
    rw [e]
    have h1 := psum_le_ell hK hwl.2 ht
    rw [hwe] at h1
    calc c * psum K w t ≤ c * ell K z := mul_le_mul_of_nonneg_left h1 hc0.le
      _ ≤ 1 := by rw [hc, inv_mul_le_iff₀ hpos]; linarith
  · have h := action_smul hv hf' c
    rw [h, action_sub_const hwl.1 hv hf, hwa, hc]
    field_simp

/-- A circle in the `(q₁, p₁)` plane: a loop of positive action. -/
lemma exists_loop_pos (hn : 1 ≤ n) : ∃ z : ℝ → Phase n, IsLoop z ∧ 0 < action z := by
  set e : Position n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ) with he
  have hen : ‖e‖ = 1 := by simp [he]
  set z0 : ℝ → Phase n := fun t => (Real.cos (2 * π * t) • e, Real.sin (2 * π * t) • e) with hz0
  set v0 : ℝ → Phase n := fun t => ((-Real.sin (2 * π * t) * (2 * π * 1)) • e,
    (Real.cos (2 * π * t) * (2 * π * 1)) • e) with hv0
  have hd : ∀ t, HasDerivAt z0 (v0 t) t := fun t => by
    have hc := ((hasDerivAt_id' t).const_mul (2 * π)).cos
    have hs := ((hasDerivAt_id' t).const_mul (2 * π)).sin
    exact (hc.smul_const e).prodMk (hs.smul_const e)
  have hvc : Continuous v0 := by
    simp only [hv0]; fun_prop
  have hv : LocallyIntegrable v0 volume := hvc.locallyIntegrable
  have hf : ∀ a b, z0 b - z0 a = ∫ s in a..b, v0 s := fun a b => by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hvc.intervalIntegrable a b)]
  have hper : Function.Periodic z0 1 := fun t => by
    simp only [hz0]
    rw [show 2 * π * (t + 1) = 2 * π * t + 2 * π by ring, Real.cos_add_two_pi, Real.sin_add_two_pi]
  refine ⟨z0, ⟨hper, v0, hv, hf⟩, ?_⟩
  rw [action_eq hv hf]
  have key : ∀ t, phaseInner (J (z0 t)) (v0 t) = 2 * π := fun t => by
    simp only [hz0, hv0, J, phaseInner, inner_neg_left, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hen]
    have := Real.sin_sq_add_cos_sq (2 * π * t)
    linear_combination (2 * π) * this
  simp only [key, intervalIntegral.integral_const, smul_eq_mul]
  have := Real.pi_pos
  norm_num
  positivity

lemma exists_minimizer (hn : 1 ≤ n) {K : Set (Phase n)} (hK : IsConvexDomain K) :
    ∃ (w : ℝ → Phase n) (M : ℝ≥0), Function.Periodic w 1 ∧ LipschitzWith M w ∧ 0 < action w ∧
      ∀ z : ℝ → Phase n, IsLoop z → 0 < action z →
        ell K w ^ 2 * action z ≤ ell K z ^ 2 * action w := by
  obtain ⟨κ, hκ, hrep⟩ := exists_reparam hK
  set L := Real.toNNReal κ
  obtain ⟨w, hwS, hmax⟩ := (isCompact_SS hK L).exists_isMaxOn ⟨_, zero_mem_SS hK L⟩
    (continuousOn_action_SS K L)
  have key : ∀ z, IsLoop z → ∀ ε : ℝ, 0 < ε → action z ≤ action w * (ell K z + ε) ^ 2 := by
    intro z hz ε hε
    obtain ⟨w', hw'S, he⟩ := embed_SS hK hκ hrep hz hε
    rw [← he]
    have := isMaxOn_iff.1 hmax w' hw'S
    nlinarith [sq_nonneg (ell K z + ε)]
  obtain ⟨z0, hz0, hA0⟩ := exists_loop_pos hn
  have hA : 0 < action w := by
    have h := key z0 hz0 1 one_pos
    by_contra hc
    push Not at hc
    nlinarith [sq_nonneg (ell K z0 + 1)]
  have hac := (isAC_of_lipschitz (lip_of_SS hwS)).1
  have hell : ell K w ≤ 1 := le_of_forall_pos_le_add fun ε hε => by
    obtain ⟨N, t, ht, h⟩ := exists_ell_le_psum hK hac hε
    linarith [hwS.2.2.2 N t ht]
  have hell0 : 0 ≤ ell K w := ell_nonneg hK (per_of_SS hwS) hac
  refine ⟨w, L, per_of_SS hwS, lip_of_SS hwS, hA, fun z hz hAz => ?_⟩
  have h1 : action z ≤ action w * ell K z ^ 2 := by
    have hc : Continuous fun ε : ℝ => action w * (ell K z + ε) ^ 2 := by fun_prop
    have ht : Tendsto (fun ε : ℝ => action w * (ell K z + ε) ^ 2) (𝓝[>] 0)
        (𝓝 (action w * ell K z ^ 2)) := by
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto ht (eventually_mem_nhdsWithin.mono fun ε hε => key z hz ε hε)
  have h2 : ell K w ^ 2 ≤ 1 := pow_le_one₀ hell0 hell
  calc ell K w ^ 2 * action z ≤ 1 * action z := mul_le_mul_of_nonneg_right h2 hAz.le
    _ ≤ ell K z ^ 2 * action w := by linarith

end Viterbo.CL.PartC
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL
open Viterbo Viterbo.CM
variable {n : ℕ}
alias exists_minimizer := Viterbo.CL.PartC.exists_minimizer

end Viterbo.CL
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartE
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
variable {K : Set (Phase n)} (hb : Bornology.IsBounded K) (hne : K.Nonempty)
include hb hne
/-!
# Part E of the Clarke blueprint: the first variation (`first_variation`)

Perturb the minimizer `w` by `s η` with `η(t) = ∫₀ᵗ J ψ`; the action is a quadratic polynomial in `s`
(integration by parts for absolutely continuous functions), and the `K`-length has one-sided
derivative `∫ dd K (-J ẇ) ψ` at `s = 0⁺` (dominated convergence for the monotone difference quotients).
-/
/-! ### Sublinearity of the support function -/
lemma supp_add_le (x y : Phase n) : supp K (x + y) ≤ supp K x + supp K y := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨k, hk, rfl⟩
  have h1 : phaseInner k x ≤ supp K x := le_csSup (bdd_supp hb x) (mem_image_of_mem _ hk)
  have h2 : phaseInner k y ≤ supp K y := le_csSup (bdd_supp hb y) (mem_image_of_mem _ hk)
  have : phaseInner k (x + y) = phaseInner k x + phaseInner k y := by
    rw [pI_comm, pI_add_left, pI_comm x, pI_comm y]
  simp only [this]; linarith

lemma supp_smul_le {a : ℝ} (ha : 0 ≤ a) (x : Phase n) : supp K (a • x) ≤ a * supp K x := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨k, hk, rfl⟩
  have h1 : phaseInner k x ≤ supp K x := le_csSup (bdd_supp hb x) (mem_image_of_mem _ hk)
  simp only [pI_smul_right]
  exact mul_le_mul_of_nonneg_left h1 ha

lemma supp_convex {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (x y : Phase n) :
    supp K (a • x + c • y) ≤ a * supp K x + c * supp K y :=
  (supp_add_le hb hne _ _).trans (add_le_add (supp_smul_le hb hne ha x) (supp_smul_le hb hne hc y))

end Viterbo.CL.PartE
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartE
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
/-! ### Difference quotients -/
/-- The difference quotient of `supp K` at `u` in direction `d` with step `s`. -/
noncomputable def Q (K : Set (Phase n)) (u d : Phase n) (s : ℝ) : ℝ :=
  (supp K (u + s • d) - supp K u) / s

end Viterbo.CL.PartE
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartE
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
variable {K : Set (Phase n)} (hb : Bornology.IsBounded K) (hne : K.Nonempty)
include hb hne
lemma Q_mono (u d : Phase n) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') : Q K u d s ≤ Q K u d s' := by
  have hs' : 0 < s' := hs.trans_le hss
  have e : u + s • d = (1 - s / s') • u + (s / s') • (u + s' • d) := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ hs'.ne', sub_smul, one_smul]; abel
  have h1 := supp_convex hb hne (a := 1 - s / s') (c := s / s')
    (by rw [sub_nonneg, div_le_one hs']; exact hss) (by positivity) u (u + s' • d)
  rw [← e] at h1
  have H : supp K (u + s • d) - supp K u ≤ s / s' * (supp K (u + s' • d) - supp K u) := by
    linarith
  unfold Q
  rw [div_le_div_iff₀ hs hs']
  have := mul_le_mul_of_nonneg_right H hs'.le
  have e2 : s / s' * (supp K (u + s' • d) - supp K u) * s' =
      (supp K (u + s' • d) - supp K u) * s := by field_simp
  linarith

lemma Q_bound {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u d : Phase n) {s : ℝ} (hs : 0 < s) :
    -(2 * R * ‖d‖) ≤ Q K u d s ∧ Q K u d s ≤ 2 * R * ‖d‖ := by
  have h1 := supp_le_add hb hne hR (u + s • d) u
  have h2 := supp_le_add hb hne hR u (u + s • d)
  have e1 : ‖u + s • d - u‖ = s * ‖d‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
  have e2 : ‖u - (u + s • d)‖ = s * ‖d‖ := by
    rw [norm_sub_rev, e1]
  rw [e1] at h1; rw [e2] at h2
  unfold Q
  constructor
  · rw [le_div_iff₀ hs]; nlinarith
  · rw [div_le_iff₀ hs]; nlinarith

omit hb hne in
lemma dd_term (u d : Phase n) (k : ℕ) :
    (supp K (u + ((1 : ℝ) / (k + 1)) • d) - supp K u) * (k + 1) = Q K u d (1 / (k + 1)) := by
  unfold Q; rw [div_div_eq_mul_div, div_one]

lemma bdd_terms {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u d : Phase n) :
    BddBelow (range fun k : ℕ => (supp K (u + ((1 : ℝ) / (k + 1)) • d) - supp K u) * (k + 1)) := by
  refine ⟨-(2 * R * ‖d‖), ?_⟩
  rintro _ ⟨k, rfl⟩
  dsimp only
  rw [dd_term]
  exact (Q_bound hb hne hR u d (by positivity)).1

end Viterbo.CL.PartE
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartE
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
lemma pI_add_right (w x y : Phase n) :
    phaseInner w (x + y) = phaseInner w x + phaseInner w y := by
  rw [pI_comm, pI_add_left, pI_comm x, pI_comm y]

lemma pI_neg_left (x y : Phase n) : phaseInner (-x) y = -phaseInner x y := by
  simpa using pI_smul_left (-1) x y

lemma norm_J (x : Phase n) : ‖J x‖ = ‖x‖ := by
  have := norm_negJ x; rwa [norm_neg] at this

/-- `J` as a continuous linear map. -/
noncomputable def Jl : Phase n →L[ℝ] Phase n :=
  (-(ContinuousLinearMap.snd ℝ (Position n) (Position n))).prod (ContinuousLinearMap.fst ℝ _ _)

lemma Jl_apply (x : Phase n) : Jl x = J x := by
  simp [Jl, J]

lemma hasDerivAt_pI {a b : ℝ → Phase n} {a' b' : Phase n} {t : ℝ} (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) :
    HasDerivAt (fun t => phaseInner (a t) (b t)) (phaseInner a' (b t) + phaseInner (a t) b') t := by
  unfold phaseInner
  have f1 : HasDerivAt (fun t => (a t).1) a'.1 t :=
    (ContinuousLinearMap.fst ℝ (Position n) (Position n)).hasFDerivAt.comp_hasDerivAt t ha
  have f2 : HasDerivAt (fun t => (a t).2) a'.2 t :=
    (ContinuousLinearMap.snd ℝ (Position n) (Position n)).hasFDerivAt.comp_hasDerivAt t ha
  have g1 : HasDerivAt (fun t => (b t).1) b'.1 t :=
    (ContinuousLinearMap.fst ℝ (Position n) (Position n)).hasFDerivAt.comp_hasDerivAt t hb
  have g2 : HasDerivAt (fun t => (b t).2) b'.2 t :=
    (ContinuousLinearMap.snd ℝ (Position n) (Position n)).hasFDerivAt.comp_hasDerivAt t hb
  have h := (f1.inner ℝ g1).add (f2.inner ℝ g2)
  refine h.congr_deriv ?_
  ring

lemma hasDerivAt_J {a : ℝ → Phase n} {a' : Phase n} {t : ℝ} (ha : HasDerivAt a a' t) :
    HasDerivAt (fun t => J (a t)) (J a') t := by
  have h := Jl.hasFDerivAt.comp_hasDerivAt t ha
  rw [Jl_apply] at h
  have e : (fun t => J (a t)) = (Jl : Phase n → Phase n) ∘ a := funext fun t => by
    simp [Jl_apply]
  rw [e]; exact h

lemma negJ_add_smul_J (v p : Phase n) (s : ℝ) : -J (v + s • J p) = -J v + s • p := by
  rw [J_add, J_smul, J_J, smul_neg, neg_add, neg_neg]

theorem first_variation {K : Set (Phase n)} (hK : IsConvexDomain K) {w : ℝ → Phase n} {M : ℝ≥0}
    (hw : Function.Periodic w 1) (hL : LipschitzWith M w) (hA : 0 < action w)
    (hmin : ∀ z : ℝ → Phase n, IsLoop z → 0 < action z →
      ell K w ^ 2 * action z ≤ ell K z ^ 2 * action w)
    {ψ : ℝ → Phase n} (hψp : Function.Periodic ψ 1) (hψm : AEStronglyMeasurable ψ volume)
    (hψb : ∃ B : ℝ, ∀ t, ‖ψ t‖ ≤ B) (hψ0 : ∫ t in (0 : ℝ)..1, ψ t = 0) :
    ell K w / (2 * action w) * ∫ t in (0 : ℝ)..1, phaseInner (w t) (ψ t) ≤
      ∫ t in (0 : ℝ)..1, dd K (-J (deriv w t)) (ψ t) := by
  obtain ⟨R, hR⟩ := hK.1.exists_norm_le
  have hb := hK.1
  have hne : K.Nonempty := hK.2.2.mono interior_subset
  obtain ⟨B, hB⟩ := hψb
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨hwAC, hvM⟩ := isAC_of_lipschitz hL
  have hwloop : IsLoop w := ⟨hw, hwAC⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ → Phase n, v = deriv w := ⟨_, rfl⟩
  rw [← hvdef]
  rw [← hvdef] at hvM
  have hwc : Continuous w := hL.continuous
  obtain ⟨v', hv', hf'⟩ := hwAC
  have hv : LocallyIntegrable v volume := by
    rw [hvdef]; exact hv'.congr (Filter.EventuallyEq.symm (deriv_ae hv' hf'))
  have hf : ∀ a b, w b - w a = ∫ s in a..b, v s := fun a b => by
    rw [hf' a b, hvdef]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [deriv_ae hv' hf'] with t ht _
    rw [ht]
  -- `ψ` and `J ψ`
  have hψi : LocallyIntegrable ψ volume :=
    (locallyIntegrable_const B).mono hψm
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact (hB t).trans (le_abs_self B))
  have hJψi : LocallyIntegrable (fun t => J (ψ t)) volume :=
    (locallyIntegrable_const B).mono (continuous_J.comp_aestronglyMeasurable hψm)
      (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, norm_J]; exact (hB t).trans (le_abs_self B))
  have hJψp : Function.Periodic (fun t => J (ψ t)) 1 := fun t => by
    show J (ψ (t + 1)) = J (ψ t); rw [hψp t]
  have hJψ0 : ∫ s in (0 : ℝ)..1, J (ψ s) = 0 := by
    have : ∫ s in (0 : ℝ)..1, J (ψ s) = Jl (∫ s in (0 : ℝ)..1, ψ s) := by
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ (ii_of_li hψi 0 1)]
      simp [Jl_apply]
    rw [this, hψ0, map_zero]
  -- `η`
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ → Phase n, η = fun t => ∫ s in (0 : ℝ)..t, J (ψ s) := ⟨_, rfl⟩
  have hηf : ∀ a b, η b - η a = ∫ s in a..b, J (ψ s) := fun a b => by
    rw [hηdef]
    exact intervalIntegral.integral_interval_sub_left (ii_of_li hJψi 0 b) (ii_of_li hJψi 0 a)
  have hηp : Function.Periodic η 1 := fun t => by
    have h1 := hηf t (t + 1)
    rw [hJψp.intervalIntegral_add_eq t 0, zero_add, hJψ0] at h1
    exact sub_eq_zero.1 h1
  have hηc : Continuous η := cont_of_ac hJψi hηf
  -- the perturbed loops
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ → ℝ → Phase n, ∀ s t, z s t = w t + s • η t := ⟨_, fun _ _ => rfl⟩
  have hzv : ∀ s : ℝ, LocallyIntegrable (fun t => v t + s • J (ψ t)) volume :=
    fun s => hv.add (hJψi.smul s)
  have hzf : ∀ s : ℝ, ∀ a b, z s b - z s a = ∫ t in a..b, (v t + s • J (ψ t)) := by
    intro s a b
    rw [intervalIntegral.integral_add (f := v) (g := fun t => s • J (ψ t)) (ii_of_li hv a b)
      ((ii_of_li hJψi a b).smul s), intervalIntegral.integral_smul, ← hf, ← hηf, hzdef, hzdef,
      smul_sub]
    abel
  have hzloop : ∀ s, IsLoop (z s) := fun s =>
    ⟨fun t => by rw [hzdef, hzdef, hw t, hηp t], fun t => v t + s • J (ψ t), hzv s, hzf s⟩
  -- action of the perturbed loops
  set I := ∫ t in (0 : ℝ)..1, phaseInner (w t) (ψ t) with hIdef
  have hIBP : ∫ t in (0 : ℝ)..1, phaseInner (J (η t)) (v t) = I := by
    set f : ℝ → ℝ := fun t => phaseInner (η t) (J (w t)) with hfdef
    have hηL : ∀ x y, ‖η x - η y‖ ≤ B * |x - y| := fun x y => by
      rw [hηf y x]
      exact intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => by
        rw [norm_J]; exact hB t
    have hwL : ∀ x y, ‖w x - w y‖ ≤ M * |x - y| := fun x y => by
      have := hL.dist_le_mul x y
      rwa [dist_eq_norm, Real.dist_eq] at this
    have hη0 : η 0 = 0 := by rw [hηdef]; simp
    set W := ‖w 0‖ + M with hWdef
    have hwb : ∀ x ∈ uIcc (0 : ℝ) 1, ‖w x‖ ≤ W := fun x hx => by
      rw [uIcc_of_le zero_le_one] at hx
      have h1 := hwL x 0
      rw [sub_zero, abs_of_nonneg hx.1] at h1
      have h2 : ‖w x‖ ≤ ‖w 0‖ + ‖w x - w 0‖ := by
        have := norm_add_le (w 0) (w x - w 0); rwa [add_sub_cancel] at this
      have h3 : (M : ℝ) * x ≤ M := mul_le_of_le_one_right M.2 hx.2
      linarith
    have hηb : ∀ x ∈ uIcc (0 : ℝ) 1, ‖η x‖ ≤ B := fun x hx => by
      rw [uIcc_of_le zero_le_one] at hx
      have h1 := hηL x 0
      rw [hη0, sub_zero, sub_zero, abs_of_nonneg hx.1] at h1
      have h3 : B * x ≤ B := mul_le_of_le_one_right hB0 hx.2
      linarith
    have hW0 : 0 ≤ W := by positivity
    have hlip : LipschitzOnWith (Real.toNNReal (2 * B * W + 2 * B * M)) f (uIcc 0 1) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq]
      have e : f x - f y = phaseInner (η x - η y) (J (w x)) + phaseInner (η y) (J (w x - w y)) := by
        simp only [hfdef, pI_sub_left, J_sub, pI_sub_right]; ring
      rw [e]
      have a1 := abs_pI_le (η x - η y) (J (w x))
      have a2 := abs_pI_le (η y) (J (w x - w y))
      rw [norm_J] at a1 a2
      have b1 : 2 * ‖η x - η y‖ * ‖w x‖ ≤ 2 * (B * |x - y|) * W := by
        gcongr
        · exact hηL x y
        · exact hwb x hx
      have b2 : 2 * ‖η y‖ * ‖w x - w y‖ ≤ 2 * B * (M * |x - y|) := by
        gcongr
        · exact hηb y hy
        · exact hwL x y
      calc |phaseInner (η x - η y) (J (w x)) + phaseInner (η y) (J (w x - w y))|
          ≤ |phaseInner (η x - η y) (J (w x))| + |phaseInner (η y) (J (w x - w y))| :=
            abs_add_le _ _
        _ ≤ 2 * (B * |x - y|) * W + 2 * B * (M * |x - y|) := by linarith
        _ = (2 * B * W + 2 * B * M) * |x - y| := by ring
    have hint := hlip.absolutelyContinuousOnInterval.integral_deriv_eq_sub
    have hf10 : f 1 - f 0 = 0 := by
      simp only [hfdef]
      rw [show (1 : ℝ) = 0 + 1 by norm_num, hηp 0, hw 0, sub_self]
    rw [hf10] at hint
    have hderiv : ∀ᵐ t, deriv f t = phaseInner (w t) (ψ t) - phaseInner (J (η t)) (v t) := by
      filter_upwards [hasDeriv_ae hv hf, hasDeriv_ae hJψi hηf] with t h1 h2
      rw [(hasDerivAt_pI h2 (hasDerivAt_J h1)).deriv, pI_J_J, pI_comm (ψ t)]
      have : phaseInner (η t) (J (v t)) = -phaseInner (J (η t)) (v t) := by
        rw [← pI_J_J (J (η t)) (v t), J_J, pI_neg_left, neg_neg]
      rw [this]; ring
    rw [intervalIntegral.integral_congr_ae (hderiv.mono fun t ht _ => ht),
      intervalIntegral.integral_sub (ii_pI hwc hψi 0 1)
        (ii_pI (w := fun t => J (η t)) (continuous_J.comp hηc) hv 0 1)] at hint
    linarith
  have hAz : ∀ s, action (z s) = action w + s * I + s ^ 2 * action η := by
    intro s
    rw [action_eq (hzv s) (hzf s), action_eq hv hf, action_eq hJψi hηf]
    have e : ∀ t, phaseInner (J (z s t)) (v t + s • J (ψ t)) =
        phaseInner (J (w t)) (v t) + s * phaseInner (w t) (ψ t) +
          s * phaseInner (J (η t)) (v t) + s ^ 2 * phaseInner (J (η t)) (J (ψ t)) := by
      intro t
      simp only [hzdef, J_add, J_smul, pI_add_left, pI_add_right, pI_smul_left, pI_smul_right,
        pI_J_J]
      ring
    simp only [e]
    have i1 : IntervalIntegrable (fun t => phaseInner (J (w t)) (v t)) volume 0 1 :=
      ii_pI (w := fun t => J (w t)) (continuous_J.comp hwc) hv 0 1
    have i2 : IntervalIntegrable (fun t => phaseInner (w t) (ψ t)) volume 0 1 :=
      ii_pI hwc hψi 0 1
    have i3 : IntervalIntegrable (fun t => phaseInner (J (η t)) (v t)) volume 0 1 :=
      ii_pI (w := fun t => J (η t)) (continuous_J.comp hηc) hv 0 1
    have i4 : IntervalIntegrable (fun t => phaseInner (J (η t)) (J (ψ t))) volume 0 1 :=
      ii_pI (w := fun t => J (η t)) (continuous_J.comp hηc) hJψi 0 1
    rw [intervalIntegral.integral_add ((i1.add (i2.const_mul s)).add (i3.const_mul s))
        (i4.const_mul (s ^ 2)),
      intervalIntegral.integral_add (i1.add (i2.const_mul s)) (i3.const_mul s),
      intervalIntegral.integral_add i1 (i2.const_mul s),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hIBP, ← hIdef]
    ring
  -- `K`-length of the perturbed loops
  set L := ell K w with hLdef
  set D := ∫ t in (0 : ℝ)..1, dd K (-J (v t)) (ψ t) with hDdef
  obtain ⟨q, hq, hqlim⟩ : ∃ q : ℕ → ℝ, (∀ k : ℕ, ell K (z (1 / ((k : ℝ) + 1))) =
      L + 1 / ((k : ℝ) + 1) * q k) ∧ Tendsto q atTop (𝓝 D) := by
    have hR0 : 0 ≤ R := by obtain ⟨k0, hk0⟩ := hne; exact (norm_nonneg k0).trans (hR k0 hk0)
    set u : ℝ → Phase n := fun t => -J (v t) with hudef
    have hellz : ∀ s : ℝ, ell K (z s) = ∫ t in (0 : ℝ)..1, supp K (u t + s • ψ t) := by
      intro s; rw [ell_eq (hzv s) (hzf s)]; simp only [negJ_add_smul_J, hudef]
    have hiiz : ∀ s : ℝ, IntervalIntegrable (fun t => supp K (u t + s • ψ t)) volume 0 1 := by
      intro s; have := ii_supp hK (hzv s) 0 1; simpa only [negJ_add_smul_J] using this
    have hellw : L = ∫ t in (0 : ℝ)..1, supp K (u t) := ell_eq hv hf K
    have hiiw : IntervalIntegrable (fun t => supp K (u t)) volume 0 1 := ii_supp hK hv 0 1
    set F : ℕ → ℝ → ℝ := fun k t =>
      (supp K (u t + ((1 : ℝ) / (k + 1)) • ψ t) - supp K (u t)) * (k + 1) with hFdef
    have hFi : ∀ k, IntervalIntegrable (F k) volume 0 1 := fun k =>
      ((hiiz _).sub hiiw).mul_const _
    refine ⟨fun k => ∫ t in (0 : ℝ)..1, F k t, fun k => ?_, ?_⟩
    · rw [hellz, hellw]
      simp only [hFdef]
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub (hiiz _) hiiw]
      field_simp
      ring
    · refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ => 2 * R * B) ?_ ?_ intervalIntegrable_const ?_
      · exact Eventually.of_forall fun k =>
          ((intervalIntegrable_iff).1 (hFi k)).aestronglyMeasurable
      · refine Eventually.of_forall fun k => ae_of_all _ fun t _ => ?_
        simp only [hFdef]
        rw [Real.norm_eq_abs, dd_term]
        have := Q_bound hb hne hR (u t) (ψ t) (s := 1 / ((k : ℝ) + 1)) (by positivity)
        have hRB : 2 * R * ‖ψ t‖ ≤ 2 * R * B := by gcongr; exact hB t
        rw [abs_le]; constructor <;> linarith [this.1, this.2]
      · refine ae_of_all _ fun t _ => ?_
        show Tendsto (fun k => F k t) atTop (𝓝 (dd K (u t) (ψ t)))
        unfold dd
        refine tendsto_atTop_ciInf ?_ (bdd_terms hb hne hR _ _)
        intro k k' hkk'
        simp only [hFdef]
        rw [dd_term, dd_term]
        refine Q_mono hb hne _ _ (by positivity) (one_div_le_one_div_of_le (by positivity) ?_)
        exact_mod_cast Nat.add_le_add_right hkk' 1
  -- `ℓ(w) > 0`
  have hLpos : 0 < L := by
    obtain ⟨C, hC, hCle⟩ := action_le_ell_sq hK
    have h1 := hCle w hwloop
    have h0 : 0 ≤ L := ell_nonneg hK hw hwloop.2
    rcases h0.lt_or_eq with h | h
    · exact h
    · rw [← hLdef, ← h] at h1; simp at h1; linarith
  -- the limit
  set Aη := action η
  set A := action w
  have hs : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hApos : ∀ᶠ k : ℕ in atTop, 0 < A + 1 / ((k : ℝ) + 1) * I + (1 / ((k : ℝ) + 1)) ^ 2 * Aη := by
    have h : Tendsto (fun k : ℕ => A + 1 / ((k : ℝ) + 1) * I + (1 / ((k : ℝ) + 1)) ^ 2 * Aη)
        atTop (𝓝 (A + 0 * I + 0 ^ 2 * Aη)) :=
      ((tendsto_const_nhds.add (hs.mul_const I)).add ((hs.pow 2).mul_const Aη))
    rw [zero_mul, zero_pow two_ne_zero, zero_mul, add_zero, add_zero] at h
    exact h.eventually (lt_mem_nhds hA)
  have hg : Tendsto (fun k : ℕ => 2 * L * A * q k + 1 / ((k : ℝ) + 1) * (q k ^ 2 * A - L ^ 2 * Aη))
      atTop (𝓝 (2 * L * A * D + 0 * (D ^ 2 * A - L ^ 2 * Aη))) :=
    (tendsto_const_nhds.mul hqlim).add (hs.mul (((hqlim.pow 2).mul_const A).sub tendsto_const_nhds))
  rw [zero_mul, add_zero] at hg
  have hmain : L ^ 2 * I ≤ 2 * L * A * D := by
    refine ge_of_tendsto hg ?_
    filter_upwards [hApos] with k hk
    set s := 1 / ((k : ℝ) + 1) with hsdef
    have hs0 : 0 < s := by positivity
    have H := hmin (z s) (hzloop s) (by rw [hAz]; exact hk)
    rw [hAz, hq k, ← hsdef] at H
    have e : s * (2 * L * A * q k + s * (q k ^ 2 * A - L ^ 2 * Aη) - L ^ 2 * I) =
        (L + s * q k) ^ 2 * A - L ^ 2 * (A + s * I + s ^ 2 * Aη) := by ring
    have h2 : 0 ≤ s * (2 * L * A * q k + s * (q k ^ 2 * A - L ^ 2 * Aη) - L ^ 2 * I) := by
      rw [e]; linarith
    have := (mul_nonneg_iff_of_pos_left hs0).1 h2
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h3 : L * (L * I) ≤ L * (D * (2 * A)) := by
    have e1 : L * (L * I) = L ^ 2 * I := by ring
    have e2 : L * (D * (2 * A)) = 2 * L * A * D := by ring
    rw [e1, e2]; exact hmain
  exact le_of_mul_le_mul_left h3 hLpos

end Viterbo.CL.PartE
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL
open Viterbo Viterbo.CM
variable {n : ℕ}
/-! ## Part E -/
alias first_variation := Viterbo.CL.PartE.first_variation

end Viterbo.CL
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartF
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
/-!
# Part F: the multiplier `b` (`exists_subgradient`)
-/
lemma le_of_eps {a b : ℝ} (h : ∀ ε : ℝ, 0 < ε → a < b + ε) : a ≤ b := by
  by_contra hc
  push Not at hc
  have := h ((a - b) / 2) (by linarith)
  linarith

end Viterbo.CL.PartF
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartF
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
variable {K : Set (Phase n)} (hb : Bornology.IsBounded K) (hne : K.Nonempty)
include hb hne
/-! ### Sublinearity of the support function -/
lemma supp_add_le (x y : Phase n) : supp K (x + y) ≤ supp K x + supp K y := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨k, hk, rfl⟩
  have h1 : phaseInner k x ≤ supp K x := le_csSup (bdd_supp hb x) (mem_image_of_mem _ hk)
  have h2 : phaseInner k y ≤ supp K y := le_csSup (bdd_supp hb y) (mem_image_of_mem _ hk)
  have : phaseInner k (x + y) = phaseInner k x + phaseInner k y := by
    rw [pI_comm, pI_add_left, pI_comm x, pI_comm y]
  simp only [this]; linarith

lemma supp_smul_le {a : ℝ} (ha : 0 ≤ a) (x : Phase n) : supp K (a • x) ≤ a * supp K x := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨k, hk, rfl⟩
  have h1 : phaseInner k x ≤ supp K x := le_csSup (bdd_supp hb x) (mem_image_of_mem _ hk)
  simp only [pI_smul_right]
  exact mul_le_mul_of_nonneg_left h1 ha

lemma supp_convex {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (x y : Phase n) :
    supp K (a • x + c • y) ≤ a * supp K x + c * supp K y :=
  (supp_add_le hb hne _ _).trans (add_le_add (supp_smul_le hb hne ha x) (supp_smul_le hb hne hc y))

end Viterbo.CL.PartF
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartF
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
/-! ### Difference quotients -/
/-- The difference quotient of `supp K` at `u` in direction `d` with step `s`. -/
noncomputable def Q (K : Set (Phase n)) (u d : Phase n) (s : ℝ) : ℝ :=
  (supp K (u + s • d) - supp K u) / s

end Viterbo.CL.PartF
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartF
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
variable {K : Set (Phase n)} (hb : Bornology.IsBounded K) (hne : K.Nonempty)
include hb hne
lemma Q_mono (u d : Phase n) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') : Q K u d s ≤ Q K u d s' := by
  have hs' : 0 < s' := hs.trans_le hss
  have e : u + s • d = (1 - s / s') • u + (s / s') • (u + s' • d) := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ hs'.ne', sub_smul, one_smul]; abel
  have h1 := supp_convex hb hne (a := 1 - s / s') (c := s / s')
    (by rw [sub_nonneg, div_le_one hs']; exact hss) (by positivity) u (u + s' • d)
  rw [← e] at h1
  have H : supp K (u + s • d) - supp K u ≤ s / s' * (supp K (u + s' • d) - supp K u) := by
    linarith
  unfold Q
  rw [div_le_div_iff₀ hs hs']
  have := mul_le_mul_of_nonneg_right H hs'.le
  have e2 : s / s' * (supp K (u + s' • d) - supp K u) * s' =
      (supp K (u + s' • d) - supp K u) * s := by field_simp
  linarith

lemma Q_bound {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u d : Phase n) {s : ℝ} (hs : 0 < s) :
    -(2 * R * ‖d‖) ≤ Q K u d s ∧ Q K u d s ≤ 2 * R * ‖d‖ := by
  have h1 := supp_le_add hb hne hR (u + s • d) u
  have h2 := supp_le_add hb hne hR u (u + s • d)
  have e1 : ‖u + s • d - u‖ = s * ‖d‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
  have e2 : ‖u - (u + s • d)‖ = s * ‖d‖ := by
    rw [norm_sub_rev, e1]
  rw [e1] at h1; rw [e2] at h2
  unfold Q
  constructor
  · rw [le_div_iff₀ hs]; nlinarith
  · rw [div_le_iff₀ hs]; nlinarith

omit hb hne in
lemma dd_term (u d : Phase n) (k : ℕ) :
    (supp K (u + ((1 : ℝ) / (k + 1)) • d) - supp K u) * (k + 1) = Q K u d (1 / (k + 1)) := by
  unfold Q; rw [div_div_eq_mul_div, div_one]

lemma bdd_terms {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u d : Phase n) :
    BddBelow (range fun k : ℕ => (supp K (u + ((1 : ℝ) / (k + 1)) • d) - supp K u) * (k + 1)) := by
  refine ⟨-(2 * R * ‖d‖), ?_⟩
  rintro _ ⟨k, rfl⟩
  dsimp only
  rw [dd_term]
  exact (Q_bound hb hne hR u d (by positivity)).1

lemma dd_le_Q {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u d : Phase n) {s : ℝ} (hs : 0 < s) :
    dd K u d ≤ Q K u d s := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hs
  calc dd K u d ≤ (supp K (u + ((1 : ℝ) / (k + 1)) • d) - supp K u) * (k + 1) :=
        ciInf_le (bdd_terms hb hne hR u d) k
    _ = Q K u d (1 / (k + 1)) := dd_term u d k
    _ ≤ Q K u d s := Q_mono hb hne u d (by positivity) hk.le

omit hb hne in
lemma exists_Q_lt (u d : Phase n) {ε : ℝ} (hε : 0 < ε) :
    ∃ s, 0 < s ∧ Q K u d s < dd K u d + ε := by
  have : dd K u d < dd K u d + ε := by linarith
  obtain ⟨k, hk⟩ := exists_lt_of_ciInf_lt this
  exact ⟨1 / (k + 1), by positivity, by rwa [← dd_term]⟩

lemma dd_ge {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u d : Phase n) : -(2 * R * ‖d‖) ≤ dd K u d := by
  refine le_ciInf fun k => ?_
  rw [dd_term]
  exact (Q_bound hb hne hR u d (by positivity)).1

lemma dd_le_one {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u d : Phase n) :
    dd K u d ≤ supp K (u + d) - supp K u := by
  have := dd_le_Q hb hne hR u d one_pos
  simpa [Q] using this

lemma dd_le_bound {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u d : Phase n) : dd K u d ≤ 2 * R * ‖d‖ :=
  (dd_le_Q hb hne hR u d one_pos).trans (Q_bound hb hne hR u d one_pos).2

lemma abs_dd_le {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u d : Phase n) : |dd K u d| ≤ 2 * R * ‖d‖ :=
  abs_le.2 ⟨dd_ge hb hne hR u d, dd_le_bound hb hne hR u d⟩

omit hb hne in
lemma dd_zero (u : Phase n) : dd K u 0 = 0 := by
  unfold dd; simp

omit hb hne in
lemma Q_smul (u d : Phase n) {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    Q K u (c • d) s = c * Q K u d (s * c) := by
  unfold Q
  rw [smul_smul]
  field_simp

lemma dd_smul_le {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u d : Phase n) {c : ℝ} (hc : 0 < c) :
    dd K u (c • d) ≤ c * dd K u d := by
  refine le_of_eps fun ε hε => ?_
  obtain ⟨s, hs, hQ⟩ := exists_Q_lt (K := K) u d (ε := ε / c) (by positivity)
  have h1 := dd_le_Q hb hne hR u (c • d) (s := s / c) (by positivity)
  rw [Q_smul u d hc (by positivity), div_mul_cancel₀ _ hc.ne'] at h1
  have : c * Q K u d s < c * (dd K u d + ε / c) := mul_lt_mul_of_pos_left hQ hc
  rw [mul_add, mul_div_cancel₀ _ hc.ne'] at this
  linarith

lemma dd_smul {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u d : Phase n) {c : ℝ} (hc : 0 < c) :
    dd K u (c • d) = c * dd K u d := by
  refine le_antisymm (dd_smul_le hb hne hR u d hc) ?_
  have h := dd_smul_le hb hne hR u (c • d) (inv_pos.2 hc)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h
  have := mul_le_mul_of_nonneg_left h hc.le
  rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this

lemma Q_add_le (u d₁ d₂ : Phase n) {s : ℝ} (hs : 0 < s) :
    Q K u (d₁ + d₂) s ≤ Q K u d₁ (2 * s) + Q K u d₂ (2 * s) := by
  have e : u + s • (d₁ + d₂) = (1 / 2 : ℝ) • (u + (2 * s) • d₁) + (1 / 2 : ℝ) • (u + (2 * s) • d₂) := by
    module
  have h := supp_convex hb hne (a := 1 / 2) (c := 1 / 2) (by norm_num) (by norm_num)
    (u + (2 * s) • d₁) (u + (2 * s) • d₂)
  rw [← e] at h
  unfold Q
  rw [← add_div, div_le_div_iff₀ hs (by positivity)]
  nlinarith

lemma dd_add_le {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u d₁ d₂ : Phase n) :
    dd K u (d₁ + d₂) ≤ dd K u d₁ + dd K u d₂ := by
  refine le_of_eps fun ε hε => ?_
  obtain ⟨s₁, hs₁, h₁⟩ := exists_Q_lt (K := K) u d₁ (ε := ε / 2) (by positivity)
  obtain ⟨s₂, hs₂, h₂⟩ := exists_Q_lt (K := K) u d₂ (ε := ε / 2) (by positivity)
  set s := min s₁ s₂ / 2 with hsdef
  have hs : 0 < s := by positivity
  have h2s : 2 * s = min s₁ s₂ := by rw [hsdef]; ring
  have a1 := dd_le_Q hb hne hR u (d₁ + d₂) hs
  have a2 := Q_add_le hb hne u d₁ d₂ hs
  have a3 := Q_mono hb hne u d₁ (by positivity) (h2s ▸ min_le_left s₁ s₂ : 2 * s ≤ s₁)
  have a4 := Q_mono hb hne u d₂ (by positivity) (h2s ▸ min_le_right s₁ s₂ : 2 * s ≤ s₂)
  linarith

end Viterbo.CL.PartF
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartF
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
lemma pI_add_right (w x y : Phase n) :
    phaseInner w (x + y) = phaseInner w x + phaseInner w y := by
  rw [pI_comm, pI_add_left, pI_comm x, pI_comm y]

lemma continuous_supp {K : Set (Phase n)} (hb : Bornology.IsBounded K) (hne : K.Nonempty) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) : Continuous (supp K) := by
  obtain ⟨k0, hk0⟩ := hne
  have hR0 : 0 ≤ R := (norm_nonneg k0).trans (hR k0 hk0)
  have hlip : LipschitzWith (Real.toNNReal (2 * R)) (supp K) := by
    refine LipschitzWith.of_le_add_mul _ fun x y => ?_
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
    exact supp_le_add hb ⟨k0, hk0⟩ hR x y
  exact hlip.continuous

lemma measurable_dd {K : Set (Phase n)} (hb : Bornology.IsBounded K) (hne : K.Nonempty) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) : Measurable (fun p : Phase n × Phase n => dd K p.1 p.2) := by
  unfold dd
  refine Measurable.iInf fun k => ?_
  have hc := continuous_supp hb hne hR
  have : Continuous (fun p : Phase n × Phase n =>
      (supp K (p.1 + ((1 : ℝ) / (k + 1)) • p.2) - supp K p.1) * (k + 1)) := by fun_prop
  exact this.measurable

/-- Bounded measurable `1`-periodic functions. -/
def AdmSub (n : ℕ) : Submodule ℝ (ℝ → Phase n) where
  carrier := {ψ | Function.Periodic ψ 1 ∧ AEStronglyMeasurable ψ volume ∧ ∃ B : ℝ, ∀ t, ‖ψ t‖ ≤ B}
  add_mem' := by
    rintro ψ₁ ψ₂ ⟨p₁, m₁, B₁, h₁⟩ ⟨p₂, m₂, B₂, h₂⟩
    refine ⟨p₁.add p₂, m₁.add m₂, B₁ + B₂, fun t => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (h₁ t) (h₂ t))
  zero_mem' := ⟨fun _ => rfl, aestronglyMeasurable_const, 0, fun t => by simp⟩
  smul_mem' := by
    rintro c ψ ⟨p, m, B, h⟩
    refine ⟨fun t => by simp [p t], m.const_smul c, ‖c‖ * B, fun t => ?_⟩
    simp only [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (h t) (norm_nonneg _)

lemma li_of_mem {ψ : ℝ → Phase n} (h : ψ ∈ AdmSub n) : LocallyIntegrable ψ volume := by
  obtain ⟨-, m, B, hB⟩ := h
  exact (locallyIntegrable_const B).mono m
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact (hB t).trans (le_abs_self B))

lemma ae_of_periodic {α : Type*} {f : ℝ → α} (hf : Function.Periodic f 1) {p : α → Prop}
    (h : ∀ᵐ t : ℝ, t ∈ Ioc (0 : ℝ) 1 → p (f t)) : ∀ᵐ t : ℝ, p (f t) := by
  have hm : ∀ m : ℤ, ∀ᵐ t : ℝ, t - m ∈ Ioc (0 : ℝ) 1 → p (f t) := by
    intro m
    have hfm : ∀ t, f (t - m) = f t := fun t => by simpa using hf.sub_int_mul_eq (x := t) m
    rw [ae_iff] at h ⊢
    have e : {t : ℝ | ¬(t - m ∈ Ioc (0 : ℝ) 1 → p (f t))} =
        (fun t => t + (-(m : ℝ))) ⁻¹' {t | ¬(t ∈ Ioc (0 : ℝ) 1 → p (f t))} := by
      ext t; simp only [mem_setOf_eq, mem_preimage, ← sub_eq_add_neg, hfm]
    rw [e, measure_preimage_add_right]; exact h
  filter_upwards [ae_all_iff.2 hm] with t ht
  apply ht (⌈t⌉ - 1)
  constructor <;> push_cast <;> linarith [Int.ceil_lt_add_one t, Int.le_ceil t]

lemma exists_rep (ℓ : Phase n →ₗ[ℝ] ℝ) : ∃ β : Phase n, ∀ a : Phase n, phaseInner β a = ℓ a := by
  let ℓc : Phase n →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ℓ
  refine ⟨((InnerProductSpace.toDual ℝ (Position n)).symm (ℓc.comp (ContinuousLinearMap.inl ℝ _ _)),
      (InnerProductSpace.toDual ℝ (Position n)).symm (ℓc.comp (ContinuousLinearMap.inr ℝ _ _))),
    fun a => ?_⟩
  simp only [phaseInner, InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  rw [← map_add]
  simp [ℓc]

theorem exists_subgradient {K : Set (Phase n)} (hK : IsConvexDomain K) {w : ℝ → Phase n} {M : ℝ≥0}
    (hw : Function.Periodic w 1) (hL : LipschitzWith M w) {c : ℝ}
    (hvar : ∀ ψ : ℝ → Phase n, Function.Periodic ψ 1 → AEStronglyMeasurable ψ volume →
      (∃ B : ℝ, ∀ t, ‖ψ t‖ ≤ B) → ∫ t in (0 : ℝ)..1, ψ t = 0 →
      c * ∫ t in (0 : ℝ)..1, phaseInner (w t) (ψ t) ≤
        ∫ t in (0 : ℝ)..1, dd K (-J (deriv w t)) (ψ t)) :
    ∃ b : Phase n, ∀ᵐ t, ∀ y : Phase n,
      supp K (-J (deriv w t)) + phaseInner (c • w t + b) (y - -J (deriv w t)) ≤ supp K y := by
  obtain ⟨R, hR⟩ := hK.1.exists_norm_le
  have hb := hK.1
  have hne : K.Nonempty := hK.2.2.mono interior_subset
  have hR0 : 0 ≤ R := by obtain ⟨k0, hk0⟩ := hne; exact (norm_nonneg k0).trans (hR k0 hk0)
  set u : ℝ → Phase n := fun t => -J (deriv w t) with hu_def
  have hwc : Continuous w := hL.continuous
  have hum : Measurable u := (continuous_J.neg).measurable.comp (measurable_deriv w)
  have hup : Function.Periodic u 1 := by
    intro t
    have : deriv w (t + 1) = deriv w t := by
      rw [← deriv_comp_add_const]; congr 1; funext x; exact hw x
    simp only [hu_def, this]
  have hG := measurable_dd hb hne hR
  have hii_dd : ∀ ψ ∈ AdmSub n, IntervalIntegrable (fun t => dd K (u t) (ψ t)) volume 0 1 := by
    rintro ψ ⟨-, m, B, hB⟩
    have hli : LocallyIntegrable (fun t => dd K (u t) (ψ t)) volume :=
      (locallyIntegrable_const (2 * R * B)).mono
        ((hG.comp_aemeasurable (hum.aemeasurable.prodMk m.aemeasurable)).aestronglyMeasurable)
        (ae_of_all _ fun t => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]
          calc |dd K (u t) (ψ t)| ≤ 2 * R * ‖ψ t‖ := abs_dd_le hb hne hR _ _
            _ ≤ 2 * R * B := by gcongr; exact hB t
            _ ≤ |2 * R * B| := le_abs_self _)
    exact (hli.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  let N : AdmSub n → ℝ := fun ψ => (∫ t in (0 : ℝ)..1, dd K (u t) ((ψ : ℝ → Phase n) t)) -
      c * ∫ t in (0 : ℝ)..1, phaseInner (w t) ((ψ : ℝ → Phase n) t)
  have N_hom : ∀ a : ℝ, 0 < a → ∀ x : AdmSub n, N (a • x) = a * N x := by
    intro a ha x
    simp only [N, Submodule.coe_smul, Pi.smul_apply, dd_smul hb hne hR _ _ ha, pI_smul_right,
      intervalIntegral.integral_const_mul]
    ring
  have N_add : ∀ x y : AdmSub n, N (x + y) ≤ N x + N y := by
    intro x y
    simp only [N, Submodule.coe_add, Pi.add_apply]
    have e1 : ∫ t in (0 : ℝ)..1, phaseInner (w t) ((x : ℝ → Phase n) t + (y : ℝ → Phase n) t) =
        (∫ t in (0 : ℝ)..1, phaseInner (w t) ((x : ℝ → Phase n) t)) +
          ∫ t in (0 : ℝ)..1, phaseInner (w t) ((y : ℝ → Phase n) t) := by
      rw [← intervalIntegral.integral_add (ii_pI hwc (li_of_mem x.2) 0 1)
        (ii_pI hwc (li_of_mem y.2) 0 1)]
      simp only [pI_add_right]
    have e2 : ∫ t in (0 : ℝ)..1, dd K (u t) ((x : ℝ → Phase n) t + (y : ℝ → Phase n) t) ≤
        (∫ t in (0 : ℝ)..1, dd K (u t) ((x : ℝ → Phase n) t)) +
          ∫ t in (0 : ℝ)..1, dd K (u t) ((y : ℝ → Phase n) t) := by
      rw [← intervalIntegral.integral_add (hii_dd _ x.2) (hii_dd _ y.2)]
      exact intervalIntegral.integral_mono_on zero_le_one
        (hii_dd _ (Submodule.add_mem _ x.2 y.2)) ((hii_dd _ x.2).add (hii_dd _ y.2))
        fun t _ => dd_add_le hb hne hR _ _ _
    rw [e1]; linarith
  let D : Submodule ℝ (AdmSub n) :=
    { carrier := {ψ | ∫ t in (0 : ℝ)..1, (ψ : ℝ → Phase n) t = 0}
      add_mem' := by
        intro x y hx hy
        simp only [mem_setOf_eq, Submodule.coe_add, Pi.add_apply] at hx hy ⊢
        rw [intervalIntegral.integral_add (ii_of_li (li_of_mem x.2) 0 1)
          (ii_of_li (li_of_mem y.2) 0 1), hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := by
        intro a x hx
        simp only [mem_setOf_eq, Submodule.coe_smul, Pi.smul_apply] at hx ⊢
        rw [intervalIntegral.integral_smul, hx, smul_zero] }
  let f : AdmSub n →ₗ.[ℝ] ℝ := { domain := D, toFun := 0 }
  obtain ⟨g, hg0, hgN⟩ := exists_extension_of_le_sublinear f N N_hom N_add (by
    intro x
    show (0 : D →ₗ[ℝ] ℝ) x ≤ N x
    rw [LinearMap.zero_apply]
    have hx : ∫ t in (0 : ℝ)..1, ((x : AdmSub n) : ℝ → Phase n) t = 0 := x.2
    have := hvar _ (x : AdmSub n).2.1 (x : AdmSub n).2.2.1 (x : AdmSub n).2.2.2 hx
    simp only [N]; linarith)
  have hconst : ∀ a : Phase n, (fun _ : ℝ => a) ∈ AdmSub n :=
    fun a => ⟨fun _ => rfl, aestronglyMeasurable_const, ‖a‖, fun _ => le_rfl⟩
  let C : Phase n →ₗ[ℝ] AdmSub n :=
    { toFun := fun a => ⟨fun _ => a, hconst a⟩
      map_add' := fun a b => rfl
      map_smul' := fun a b => rfl }
  let ℓ : Phase n →ₗ[ℝ] ℝ := g.comp C
  obtain ⟨β, hβ⟩ := exists_rep ℓ
  have hgψ : ∀ ψ : AdmSub n, g ψ = ℓ (∫ t in (0 : ℝ)..1, (ψ : ℝ → Phase n) t) := by
    intro ψ
    set a := ∫ t in (0 : ℝ)..1, (ψ : ℝ → Phase n) t with ha
    have hmem : ψ - C a ∈ D := by
      show ∫ t in (0 : ℝ)..1, ((ψ : ℝ → Phase n) t - a) = 0
      rw [intervalIntegral.integral_sub (ii_of_li (li_of_mem ψ.2) 0 1) intervalIntegrable_const]
      simp [← ha]
    have h1 := hg0 ⟨ψ - C a, hmem⟩
    have h2 : g (ψ - C a) = 0 := h1
    rw [map_sub] at h2
    show g ψ = g (C a)
    linarith
  have KI : ∀ ψ ∈ AdmSub n, ∫ t in (0 : ℝ)..1, phaseInner (c • w t + β) (ψ t) ≤
      ∫ t in (0 : ℝ)..1, dd K (u t) (ψ t) := by
    intro ψ hψ
    have h1 := hgN ⟨ψ, hψ⟩
    rw [hgψ] at h1
    simp only [N] at h1
    rw [← hβ, ← integral_pI_const (li_of_mem hψ)] at h1
    have e : ∫ t in (0 : ℝ)..1, phaseInner (c • w t + β) (ψ t) =
        c * (∫ t in (0 : ℝ)..1, phaseInner (w t) (ψ t)) +
          ∫ t in (0 : ℝ)..1, phaseInner β (ψ t) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        ((ii_pI hwc (li_of_mem hψ) 0 1).const_mul c) (ii_pI continuous_const (li_of_mem hψ) 0 1)]
      simp only [pI_add_left, pI_smul_left]
    linarith
  have hxc : Continuous (fun t => c • w t + β) := (hwc.const_smul c).add continuous_const
  have hxp : Function.Periodic (fun t => c • w t + β) 1 := fun t => by simp only [hw t]
  have point : ∀ d : Phase n, ∀ᵐ t, ¬ (dd K (u t) d < phaseInner (c • w t + β) d) := by
    intro d
    set S := {t : ℝ | dd K (u t) d < phaseInner (c • w t + β) d} with hS
    have hm1 : Measurable (fun t => dd K (u t) d) := by
      have := hG.comp (hum.prodMk (measurable_const (a := d)))
      exact this
    have hm2 : Measurable (fun t => phaseInner (c • w t + β) d) := by
      have := (continuous_pI.comp (hxc.prodMk (continuous_const (y := d)))).measurable
      exact this
    have hSm : MeasurableSet S := measurableSet_lt hm1 hm2
    let ψ : ℝ → Phase n := S.indicator (fun _ => d)
    have hψ : ψ ∈ AdmSub n := by
      refine ⟨fun t => ?_, aestronglyMeasurable_const.indicator hSm, ‖d‖,
        fun t => norm_indicator_le_norm_self _ _⟩
      have : (t + 1 ∈ S) ↔ (t ∈ S) := by
        simp only [hS, Set.mem_setOf_eq, hup t]
        rw [hw t]
      simp only [ψ, Set.indicator, this]
    let F : ℝ → ℝ := S.indicator (fun t => phaseInner (c • w t + β) d - dd K (u t) d)
    have hF : ∀ t, F t = phaseInner (c • w t + β) (ψ t) - dd K (u t) (ψ t) := by
      intro t
      by_cases ht : t ∈ S
      · simp [F, ψ, ht]
      · simp [F, ψ, ht, dd_zero, pI_zero_right]
    have hF0 : ∀ t, 0 ≤ F t :=
      fun t => Set.indicator_nonneg (fun t ht => sub_nonneg.2 (le_of_lt ht)) t
    have hFeq : F = fun t => phaseInner (c • w t + β) (ψ t) - dd K (u t) (ψ t) := funext hF
    have hFi : IntervalIntegrable F volume 0 1 := by
      rw [hFeq]; exact (ii_pI hxc (li_of_mem hψ) 0 1).sub (hii_dd ψ hψ)
    have hint : ∫ t in (0 : ℝ)..1, F t = 0 := by
      have h := KI ψ hψ
      have : ∫ t in (0 : ℝ)..1, F t ≤ 0 := by
        rw [hFeq, intervalIntegral.integral_sub (ii_pI hxc (li_of_mem hψ) 0 1) (hii_dd ψ hψ)]
        linarith
      exact le_antisymm this (intervalIntegral.integral_nonneg zero_le_one fun t _ => hF0 t)
    rw [intervalIntegral.integral_of_le zero_le_one,
      setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hF0) hFi.1] at hint
    have h2 : ∀ᵐ t, t ∈ Ioc (0 : ℝ) 1 → ¬ (dd K (u t) d < phaseInner (c • w t + β) d) := by
      rw [← ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hint] with t ht hlt
      have : 0 < F t := by
        simp only [F, Set.indicator_of_mem (show t ∈ S from hlt)]; linarith
      rw [ht] at this; exact lt_irrefl _ this
    exact ae_of_periodic (f := fun t => (u t, c • w t + β))
      (p := fun q => ¬ (dd K q.1 d < phaseInner q.2 d))
      (fun t => by simp only [hup t, hxp t]) h2
  refine ⟨β, ?_⟩
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense (Phase n)
  have hall : ∀ᵐ t, ∀ d ∈ s, phaseInner (c • w t + β) d ≤ dd K (u t) d :=
    (ae_ball_iff hsc).2 fun d _ => (point d).mono fun t ht => not_lt.1 ht
  filter_upwards [hall] with t ht y
  have hcl : IsClosed
      {d : Phase n | phaseInner (c • w t + β) d ≤ supp K (u t + d) - supp K (u t)} :=
    isClosed_le (continuous_pI.comp (continuous_const.prodMk continuous_id))
      (((continuous_supp hb hne hR).comp (continuous_const.add continuous_id)).sub continuous_const)
  have hsub : s ⊆ {d : Phase n | phaseInner (c • w t + β) d ≤ supp K (u t + d) - supp K (u t)} :=
    fun d hd => (ht d hd).trans (dd_le_one hb hne hR _ _)
  have hmem := hcl.closure_subset_iff.2 hsub (hsd.closure_eq.symm ▸ mem_univ (y - u t))
  simp only [Set.mem_setOf_eq, add_sub_cancel] at hmem
  show supp K (u t) + phaseInner (c • w t + β) (y - u t) ≤ supp K y
  linarith

end Viterbo.CL.PartF
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL
open Viterbo Viterbo.CM
variable {n : ℕ}
/-! ## Part F -/
alias exists_subgradient := Viterbo.CL.PartF.exists_subgradient

end Viterbo.CL
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL.PartG
open Viterbo Viterbo.CM Viterbo.CL
variable {n : ℕ}
/-!
# Part G of the Clarke blueprint: the generalized closed characteristic `γ = c w + b`
-/
lemma supp_add_le {K : Set (Phase n)} (hb : Bornology.IsBounded K) (hne : K.Nonempty)
    (x y : Phase n) : supp K (x + y) ≤ supp K x + supp K y := by
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨k, hk, rfl⟩
  have h1 : phaseInner k x ≤ supp K x := le_csSup (bdd_supp hb x) (mem_image_of_mem _ hk)
  have h2 : phaseInner k y ≤ supp K y := le_csSup (bdd_supp hb y) (mem_image_of_mem _ hk)
  have : phaseInner k (x + y) = phaseInner k x + phaseInner k y := by
    rw [pI_comm, pI_add_left, pI_comm x, pI_comm y]
  simp only [this]; linarith

lemma exists_rep (ℓ : Phase n →ₗ[ℝ] ℝ) : ∃ β : Phase n, ∀ a : Phase n, phaseInner β a = ℓ a := by
  let ℓc : Phase n →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ℓ
  refine ⟨((InnerProductSpace.toDual ℝ (Position n)).symm (ℓc.comp (ContinuousLinearMap.inl ℝ _ _)),
      (InnerProductSpace.toDual ℝ (Position n)).symm (ℓc.comp (ContinuousLinearMap.inr ℝ _ _))),
    fun a => ?_⟩
  simp only [phaseInner, InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
  rw [← map_add]
  simp [ℓc]

/-- A subgradient of `h_K` at `u` lies in `closure K`, has `u` in its normal cone, and lies on the
boundary when `u ≠ 0`. -/
lemma subgrad {K : Set (Phase n)} (hK : IsConvexDomain K) {x u : Phase n}
    (h : ∀ y, supp K u + phaseInner x (y - u) ≤ supp K y) :
    x ∈ closure K ∧ u ∈ normalCone phaseInner K x ∧ (u ≠ 0 → x ∉ interior K) := by
  have hne : K.Nonempty := hK.2.2.mono interior_subset
  -- `⟨x, u⟩ = h(u)`
  have hxu : phaseInner x u = supp K u := by
    have h0 := h 0
    have h2 := h ((2 : ℝ) • u)
    rw [supp_zero hne, zero_sub, show -u = (-1 : ℝ) • u by simp, pI_smul_right] at h0
    have h2' := supp_add_le hK.1 hne u u
    rw [show (2 : ℝ) • u - u = u by rw [two_smul]; abel, two_smul] at h2
    linarith
  have hcone : u ∈ normalCone phaseInner K x := by
    intro k hk
    have h1 : phaseInner k u ≤ supp K u := le_csSup (bdd_supp hK.1 u) (mem_image_of_mem _ hk)
    rw [pI_sub_right, pI_comm u k, pI_comm u x]
    linarith
  refine ⟨?_, hcone, ?_⟩
  · by_contra hx
    obtain ⟨f, s, hfs, hsx⟩ := geometric_hahn_banach_closed_point hK.2.1.closure isClosed_closure hx
    obtain ⟨β, hβ⟩ := exists_rep (f : Phase n →L[ℝ] ℝ).toLinearMap
    have hβ' : ∀ a, f a = phaseInner a β := fun a => by
      rw [pI_comm]; exact (hβ a).symm
    have hsupp : supp K β ≤ s := by
      refine csSup_le (hne.image _) ?_
      rintro _ ⟨k, hk, rfl⟩
      have := hfs k (subset_closure hk)
      rw [hβ'] at this
      exact this.le
    have h3 := h (u + β)
    rw [add_sub_cancel_left] at h3
    have h4 := supp_add_le hK.1 hne u β
    rw [hβ'] at hsx
    linarith
  · intro hu0 hint
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
    have := cone_lower hr hball hcone
    rw [sub_self] at this
    have e : phaseInner (0 : Phase n) u = 0 := by simp [phaseInner]
    rw [e] at this
    have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
    have : 0 < r / 2 * ‖u‖ := by positivity
    linarith

lemma cone_smul {K : Set (Phase n)} {x u : Phase n} {c : ℝ} (hc : 0 ≤ c)
    (hu : u ∈ normalCone phaseInner K x) : c • u ∈ normalCone phaseInner K x := by
  intro k hk
  rw [pI_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos hc (hu k hk)

/-- The action is unchanged by translating a loop. -/
lemma action_add_const {z v : ℝ → Phase n} (hz : Function.Periodic z 1)
    (hv : LocallyIntegrable v volume) (hf : ∀ a b, z b - z a = ∫ s in a..b, v s) (p : Phase n) :
    action (fun t => z t + p) = action z := by
  have hf' : ∀ a b, (fun t => z t + p) b - (fun t => z t + p) a = ∫ s in a..b, v s := by
    intro a b; simp only [add_sub_add_right_eq_sub]; exact hf a b
  have hzc := cont_of_ac hv hf
  rw [action_eq hv hf', action_eq hv hf]
  have e : ∀ t, phaseInner (J (z t + p)) (v t) =
      phaseInner (J (z t)) (v t) + phaseInner (J p) (v t) := fun t => by
    rw [J_add, pI_add_left]
  simp only [e]
  rw [intervalIntegral.integral_add (ii_pI (w := fun t => J (z t)) (continuous_J.comp hzc) hv 0 1)
    (ii_pI (w := fun _ => J p) continuous_const hv 0 1), integral_pI_const hv, ← hf 0 1,
    show z 1 = z 0 by simpa using hz 0, sub_self, pI_zero_right, add_zero]

theorem main (n : ℕ) (hn : 1 ≤ n) (K : Set (Phase n)) (hK : IsConvexDomain K) :
    ∃ γ : ℝ → Phase n, IsGeneralizedClosedCharacteristic K γ ∧
      (∃ s t, γ s ≠ γ t) ∧
      ∀ z : ℝ → Phase n, Function.Periodic z 1 →
        (∃ v : ℝ → Phase n, LocallyIntegrable v volume ∧
          ∀ a b, z b - z a = ∫ s in a..b, v s) →
        0 < action z →
        4 * action γ * action z ≤
          (∫ t in (0 : ℝ)..1, sSup ((fun x => phaseInner x (-J (deriv z t))) '' K)) ^ 2 := by
  obtain ⟨w, M, hw, hL, hA, hmin⟩ := exists_minimizer hn hK
  obtain ⟨⟨vw, hvw, hfw⟩, -⟩ := isAC_of_lipschitz hL
  have hwc : Continuous w := hL.continuous
  have hloop : IsLoop w := ⟨hw, vw, hvw, hfw⟩
  obtain ⟨C, hC, hCb⟩ := action_le_ell_sq hK
  have hℓ0 : 0 ≤ ell K w := ell_nonneg hK hw ⟨vw, hvw, hfw⟩
  have hℓ : 0 < ell K w := by
    have := hCb w hloop
    rcases hℓ0.lt_or_eq with h | h
    · exact h
    · rw [← h] at this; nlinarith
  obtain ⟨c, hcdef⟩ : ∃ c, c = ell K w / (2 * action w) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  have hvar : ∀ ψ : ℝ → Phase n, Function.Periodic ψ 1 → AEStronglyMeasurable ψ volume →
      (∃ B : ℝ, ∀ t, ‖ψ t‖ ≤ B) → ∫ t in (0 : ℝ)..1, ψ t = 0 →
      c * ∫ t in (0 : ℝ)..1, phaseInner (w t) (ψ t) ≤
        ∫ t in (0 : ℝ)..1, dd K (-J (deriv w t)) (ψ t) := by
    intro ψ hp hm hb h0
    rw [hcdef]
    exact first_variation hK hw hL hA hmin hp hm hb h0
  obtain ⟨b, hb⟩ := exists_subgradient hK hw hL hvar
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Phase n, γ = fun t => c • w t + b := ⟨_, rfl⟩
  have hγt : ∀ t, γ t = c • w t + b := fun t => by rw [hγ]
  have hγc : Continuous γ := by rw [hγ]; exact (hwc.const_smul c).add continuous_const
  have hfγ : ∀ a b', γ b' - γ a = ∫ s in a..b', c • vw s := by
    intro a b'; rw [hγt, hγt, add_sub_add_right_eq_sub]; exact ftc_smul hfw c a b'
  have hae : ∀ᵐ t, deriv w t = vw t ∧ (γ t ∈ closure K ∧
      (-J (deriv w t)) ∈ normalCone phaseInner K (γ t) ∧
      (-J (deriv w t) ≠ 0 → γ t ∉ interior K)) := by
    filter_upwards [deriv_ae hvw hfw, hb] with t h1 h2
    exact ⟨h1, by rw [hγt]; exact subgrad hK h2⟩
  have hconst : ¬ ∀ s, γ s = γ 0 := by
    intro h
    have hw0 : w = fun _ => w 0 := funext fun s =>
      smul_right_injective (Phase n) hc.ne' (add_right_cancel ((hγt s).symm.trans
        ((h s).trans (hγt 0))))
    have : action w = 0 := by rw [hw0]; simp [action, pI_zero_right]
    linarith
  have hcl : ∀ t, γ t ∈ closure K := by
    by_contra h
    push Not at h
    obtain ⟨t0, ht0⟩ := h
    have hopen : IsOpen {t | γ t ∉ closure K} := isClosed_closure.isOpen_compl.preimage hγc
    have hpos := hopen.measure_pos (volume : Measure ℝ) ⟨t0, ht0⟩
    have hnull : volume {t | ¬ γ t ∈ closure K} = 0 := ae_iff.1 (hae.mono fun t ht => ht.2.1)
    rw [hnull] at hpos
    exact lt_irrefl _ hpos
  have hint : ∀ t, γ t ∉ interior K := by
    intro t0 ht0
    apply hconst
    have hcl' : IsClosed {t | γ t = γ t0} := isClosed_eq hγc continuous_const
    have hop : IsOpen {t | γ t = γ t0} := by
      rw [Metric.isOpen_iff]
      intro t ht
      have hU : IsOpen (γ ⁻¹' interior K) := isOpen_interior.preimage hγc
      have htU : t ∈ γ ⁻¹' interior K := by
        show γ t ∈ interior K; rw [show γ t = γ t0 from ht]; exact ht0
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU t htU
      refine ⟨ε, hε, fun s hs => ?_⟩
      show γ s = γ t0
      rw [← show γ t = γ t0 from ht, ← sub_eq_zero, hfγ t s]
      have hsub : uIcc t s ⊆ Metric.ball t ε := by
        rw [Real.ball_eq_Ioo]
        refine (ordConnected_Ioo).uIcc_subset ?_ ?_
        · rw [← Real.ball_eq_Ioo]; exact Metric.mem_ball_self hε
        · rw [← Real.ball_eq_Ioo]; exact hs
      rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : Phase n)) ?_,
        intervalIntegral.integral_zero]
      filter_upwards [hae] with τ hτa hτ
      obtain ⟨h1, -, -, h4⟩ := hτa
      have hτU : γ τ ∈ interior K := hball (hsub (uIoc_subset_uIcc hτ))
      have : -J (deriv w τ) = 0 := by
        by_contra hne; exact h4 hne hτU
      have h5 : deriv w τ = 0 := J_eq_zero (neg_eq_zero.1 this)
      rw [← h1, h5, smul_zero]
    have := IsClopen.eq_univ ⟨hcl', hop⟩ ⟨t0, rfl⟩
    intro s
    have h1 : γ s = γ t0 := by
      have : s ∈ {t | γ t = γ t0} := by rw [this]; trivial
      exact this
    have h2 : γ 0 = γ t0 := by
      have : (0 : ℝ) ∈ {t | γ t = γ t0} := by rw [this]; trivial
      exact this
    rw [h1, h2]
  have hγA : action γ = c ^ 2 * action w := by
    have hzp : Function.Periodic (fun t => c • w t) 1 := fun t => by simp only [hw t]
    have h1 := action_add_const hzp (hvw.smul c) (ftc_smul hfw c) b
    rw [hγ, h1, action_smul hvw hfw c]
  refine ⟨γ, ⟨fun t => by rw [hγt, hγt, hw t], fun t => ⟨hcl t, hint t⟩, fun t => c • vw t,
    hvw.smul c, hfγ, ?_⟩, ?_, ?_⟩
  · filter_upwards [hae] with t ht
    obtain ⟨h1, -, h3, -⟩ := ht
    refine ⟨c • -J (deriv w t), cone_smul hc.le h3, ?_⟩
    rw [J_smul, J_neg, J_J, neg_neg, h1]
  · by_contra h
    push Not at h
    exact hconst fun s => h s 0
  · rintro z hz ⟨vz, hvz, hfz⟩ hAz
    have hm := hmin z ⟨hz, vz, hvz, hfz⟩ hAz
    show 4 * action γ * action z ≤ ell K z ^ 2
    rw [hγA, hcdef]
    have e : 4 * ((ell K w / (2 * action w)) ^ 2 * action w) * action z =
        ell K w ^ 2 * action z / action w := by
      field_simp; ring
    rw [e, div_le_iff₀ hA]
    linarith

end Viterbo.CL.PartG
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
namespace Viterbo.CL
open Viterbo Viterbo.CM
variable {n : ℕ}
/-! ## Part G -/
alias main := Viterbo.CL.PartG.main

end Viterbo.CL
end

section
open MeasureTheory Set OAI.SymmetricPolar Filter Topology
open scoped ENNReal Pointwise NNReal
open Viterbo in
theorem solution (n : ℕ) (hn : 1 ≤ n) (K : Set (OAI.SymmetricPolar.Phase n)) (hK : IsConvexDomain K) :
    ∃ γ : ℝ → OAI.SymmetricPolar.Phase n, IsGeneralizedClosedCharacteristic K γ ∧
      (∃ s t, γ s ≠ γ t) ∧
      ∀ z : ℝ → OAI.SymmetricPolar.Phase n, Function.Periodic z 1 →
        (∃ v : ℝ → OAI.SymmetricPolar.Phase n, LocallyIntegrable v volume ∧
          ∀ a b, z b - z a = ∫ s in a..b, v s) →
        0 < action z →
        4 * action γ * action z ≤
          (∫ t in (0 : ℝ)..1, sSup ((fun x => phaseInner x (-J (deriv z t))) '' K)) ^ 2 :=
  Viterbo.CL.main n hn K hK

end
