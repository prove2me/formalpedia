-- Prove2me | solution 1 for TaoBR.parabolicBochnerRieszConjecture_of_parabolicRestrictionConjecture
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T14:11:31.526406+00:00
-- url     : https://prove2.me/submissions/555e36c9-36da-4929-b408-df46fefd2dee

import Mathlib
import Definitions.Def_TaoBR

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
/-!
# Blueprint: Carbery — parabolic restriction ⟹ parabolic Bochner–Riesz (Tao, p. 9, [4])

Target (published, frozen), stated verbatim at the end:
`TaoBR.parabolicBochnerRieszConjecture_of_parabolicRestrictionConjecture (m) (hm : 1 ≤ m) :
  ParabolicRestrictionConjecture m → ParabolicBochnerRieszConjecture m`.

Carbery's paper (Math. Proc. Cambridge Philos. Soc. 111 (1992) 525–529) is paywalled; this is a
reconstruction of the standard argument, using the projective change of variables that Tao (p. 11)
calls "an analogue of the argument in [4]". Notation: `n = m + 1`, `z̲ = horiz z`, `zₙ = vert z`,
`e(t) = exp(2πit)` (`ex`), `p_c = 2(m+1)/(m+2)` (`pc`), `critE m p = (m+1)/p - (m+2)/2`
(`= δ(p)` for `p ≤ 2`).

1. **Kernel** (`kernel_rep`). Write `η(ξ)(ξₙ - |ξ̲|²/2)₊^δ = a₀(ξ) · σ(ξ)` with
   `a₀ = η e^{2πξₙ}` (smooth, compact support) and `σ(ξ) = e^{-2πξₙ}(ξₙ - |ξ̲|²/2)₊^δ`
   (integrable). Then `S̃f = ǎ * (K * f)` with `ǎ = 𝓕⁻ a₀` (Schwartz) and `K = 𝓕⁻ σ`; the shear
   `ξ = (v, s + |v|²/2)` gives `K(z) = B(zₙ) E(z̲, zₙ)` exactly, with
   `B(t) = ∫ e^{-2πs} s₊^δ e(ts) ds = Γ(δ+1)(2π(1 - it))^{-δ-1}` (`Bc`) and the complex Gaussian
   `E(d, τ) = ∫ e^{-π|v|²} e(⟨d,v⟩ + τ|v|²/2) dv = (1 - iτ)^{-m/2} exp(-π|d|²/(1 - iτ))` (`Eg`).
2. **Dyadic pieces** `K_j(z) = 1_{|zₙ| ∼ 2^j} K(z)` (`sh j`). For `1 ≤ p < p_c` (`piece_bound`):
   `‖K_j * f‖_p ≲ (j+1)^m 2^{j(critE m p - δ)} ‖f‖_p`. Average over centres `c` of `x̲`-balls of
   radius `L = 2^j`; split `f` into the part with `y̲ ∈ B(c, (j+2)L)` (near) and the rest (far:
   Gaussian decay of `E`, Young). Near (`near_bound`): `E(·, τ)` is a superposition
   `c(τ) ∫ e^{-π|ξ|²} e(-|· - ξ|²/(2τ)) dξ`, `|c(τ)| = |τ|^{-m/2}` (`Eg_superpos`); for fixed
   `xₙ` the pure kernel `b(τ) e(-|x̲ - y̲|²/(2τ))`, `τ = xₙ - yₙ`, becomes, under the projective
   change `w = (-y̲/τ, 1/τ)`, exactly `x̲ ↦ Ĥ(x̲, |x̲|²/2)` (`frozen_eq`), and the restriction
   hypothesis, Galilean-translated and parabolically rescaled to the ball `B(c', L)`
   (`restr_ball`), bounds it.
3. **Duality** (`dual_bound`, with `K(-z) = conj K(z)`) gives the same piece bounds at `p' > p_c'`,
   and the layer-cake **interpolation** (`interp_bound`) between `p₀ < p_c` and `p₀'` covers
   `[p_c, p_c']`, where `δ(p) = 0` and `critE m p₀ → 0` as `p₀ → p_c`.
4. `p = ∞`: `δ > m/2` makes `K` integrable (`bound_infty`).

Every lemma below whose proof is `sorry` is a stub, proved in `Part<X>.lean`.
-/
/-! ## Objects -/
/-- `e(t) = exp(2πit)`. -/
noncomputable def ex (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

/-- The critical exponent `p_c = 2(m+1)/(m+2)` of Conjecture 4.4. -/
noncomputable def pc (m : ℕ) : ℝ := 2 * ((m : ℝ) + 1) / ((m : ℝ) + 2)

/-- `critE m p = (m+1)/p - (m+2)/2`, the critical index `δ(p)` of `ℝ^{m+1}` for `p ≤ 2`. -/
noncomputable def critE (m : ℕ) (p : ℝ) : ℝ := ((m : ℝ) + 1) / p - ((m : ℝ) + 2) / 2

/-- Convolution `(k * f)(x) = ∫ k(x - y) f(y) dy`. -/
noncomputable def conv {n : ℕ} (k f : E n → ℂ) (x : E n) : ℂ := ∫ y, k (x - y) * f y

/-- The vertical factor `B(t) = ∫ e^{-2πs} s₊^δ e(ts) ds`. -/
noncomputable def Bc (δ t : ℝ) : ℂ :=
  ∫ s : ℝ, ((Real.exp (-(2 * Real.pi * s)) * plusPow δ s : ℝ) : ℂ) * ex (t * s)

/-- The horizontal factor `E(d, τ) = ∫ e^{-π|v|²} e(⟨d, v⟩ + τ|v|²/2) dv`. -/
noncomputable def Eg (m : ℕ) (d : E m) (τ : ℝ) : ℂ :=
  ∫ v : E m, (Real.exp (-(Real.pi * ‖v‖ ^ 2)) : ℂ) * ex (⟪d, v⟫ + τ * ‖v‖ ^ 2 / 2)

/-- A kernel `z ↦ b(zₙ) E(z̲, zₙ)`. -/
noncomputable def kb (m : ℕ) (b : ℝ → ℂ) (z : E (m + 1)) : ℂ :=
  b (vert z) * Eg m (horiz z) (vert z)

/-- The kernel `K = 𝓕⁻ σ`, `K(z) = B(zₙ) E(z̲, zₙ)`. -/
noncomputable def Kc (m : ℕ) (δ : ℝ) : E (m + 1) → ℂ := kb m (Bc δ)

/-- The dyadic shells: `sh 0 = 1_{|t| ≤ 1}`, `sh j = 1_{2^{j-1} < |t| ≤ 2^j}` for `j ≥ 1`. -/
noncomputable def sh (j : ℕ) (t : ℝ) : ℝ :=
  if j = 0 then (if |t| ≤ 1 then 1 else 0)
  else (if (2 : ℝ) ^ (j - 1) < |t| ∧ |t| ≤ (2 : ℝ) ^ j then 1 else 0)

/-- The dyadic piece `K_j = sh j (zₙ) K(z)`. -/
noncomputable def Kj (m : ℕ) (δ : ℝ) (j : ℕ) : E (m + 1) → ℂ :=
  kb m (fun t => (sh j t : ℂ) * Bc δ t)

/-- Per-piece `L^q` bounds `‖K_j * f‖_q ≤ A_j ‖f‖_q`. -/
def PieceBd (m : ℕ) (δ q : ℝ) (A : ℕ → ℝ) : Prop :=
  ∀ (j : ℕ) (f : E (m + 1) → ℂ), MemLp f (ENNReal.ofReal q) volume →
    eLpNorm (conv (Kj m δ j) f) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (A j) * eLpNorm f (ENNReal.ofReal q) volume

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartK
variable {m : ℕ}
/-! ## Coordinates (copied from `proofs/pbr/PartK.lean`) -/
@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

end TaoBR.Carb.PartK
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartS
open Filter Topology
/-! ## `e(t)` -/
theorem conj_ex (t : ℝ) : conj (ex t) = ex (-t) := by
  rw [ex, ex, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-! ## The Gamma integral with a complex rate (copied from `proofs/pbr/PartB.lean`) -/
/-- `L(r) = ∫_0^∞ s^δ e^{-rs} ds`. -/
noncomputable def Lint (δ : ℝ) (r : ℂ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), ((s ^ δ : ℝ) : ℂ) * Complex.exp (-(r * s))

theorem norm_Lint_integrand (δ : ℝ) (r : ℂ) {s : ℝ} (hs : 0 < s) :
    ‖((s ^ δ : ℝ) : ℂ) * Complex.exp (-(r * s))‖ = s ^ δ * Real.exp (-r.re * s) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hs.le _),
    Complex.norm_exp]
  congr 2; simp [neg_mul]

theorem integ_rpow_exp {β c : ℝ} (hβ : -1 < β) (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => s ^ β * Real.exp (-c * s)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hβ one_pos hc
  simpa [Real.rpow_one] using this

theorem Lint_integrand_continuous (δ : ℝ) (hδ : 0 < δ) (r : ℂ) :
    Continuous (fun s : ℝ => ((s ^ δ : ℝ) : ℂ) * Complex.exp (-(r * s))) :=
  (Complex.continuous_ofReal.comp (Real.continuous_rpow_const hδ.le)).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg)

theorem Lint_integrable (δ : ℝ) (hδ : 0 < δ) {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (fun s : ℝ => ((s ^ δ : ℝ) : ℂ) * Complex.exp (-(r * s))) (Ioi 0) := by
  refine Integrable.mono' (integ_rpow_exp (β := δ) (by linarith) hr)
    (Lint_integrand_continuous δ hδ r).aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2
    (ae_of_all _ fun s hs => (norm_Lint_integrand δ r hs).le)

theorem Lint_ofReal (δ : ℝ) (hδ : 0 < δ) {r : ℝ} (hr : 0 < r) :
    Lint δ r = (1 / (r : ℂ)) ^ ((δ + 1 : ℝ) : ℂ) * Complex.Gamma ((δ + 1 : ℝ) : ℂ) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := ((δ + 1 : ℝ) : ℂ))
    (by simp; linarith) hr
  rw [← h, Lint]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  rw [Complex.ofReal_cpow (le_of_lt hs)]
  congr 2; push_cast; ring

theorem Lint_differentiableOn (δ : ℝ) (hδ : 0 < δ) :
    DifferentiableOn ℂ (Lint δ) {r : ℂ | 0 < r.re} := by
  intro r0 hr0
  have hr0' : 0 < r0.re := hr0
  set c := r0.re / 2 with hc_def
  have hc : 0 < c := by positivity
  have hball : ∀ r ∈ ball r0 c, c < r.re := fun r hr => by
    rw [mem_ball, dist_eq_norm] at hr
    have h1 := Complex.abs_re_le_norm (r - r0)
    rw [Complex.sub_re] at h1
    have h2 := (abs_lt.1 (h1.trans_lt hr)).1
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (r : ℂ) (s : ℝ) => ((s ^ δ : ℝ) : ℂ) * Complex.exp (-(r * s)))
    (F' := fun (r : ℂ) (s : ℝ) => ((s ^ δ : ℝ) : ℂ) * (Complex.exp (-(r * s)) * -(1 * (s : ℂ))))
    (bound := fun s => s ^ (δ + 1) * Real.exp (-c * s)) (x₀ := r0)
    (ball_mem_nhds r0 hc)
    (Eventually.of_forall fun r => (Lint_integrand_continuous δ hδ r).aestronglyMeasurable)
    (Lint_integrable δ hδ hr0')
    (by
      refine Continuous.aestronglyMeasurable ?_
      exact (Complex.continuous_ofReal.comp (Real.continuous_rpow_const hδ.le)).mul
        ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).mul
          (continuous_const.mul Complex.continuous_ofReal).neg))
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs r hr => by
      have hs' : (0 : ℝ) < s := hs
      rw [show ((s ^ δ : ℝ) : ℂ) * (Complex.exp (-(r * s)) * -(1 * (s : ℂ))) =
          -(((s ^ δ : ℝ) : ℂ) * Complex.exp (-(r * s)) * (s : ℂ)) by ring,
        norm_neg, norm_mul, norm_Lint_integrand δ r hs', Complex.norm_real,
        Real.norm_of_nonneg hs'.le, Real.rpow_add_one hs'.ne', mul_right_comm]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
      have := hball r hr
      nlinarith))
    (integ_rpow_exp (by linarith) hc)
    (ae_of_all _ fun s r _ =>
      (((hasDerivAt_id' r).mul_const (s : ℂ)).neg.cexp.const_mul _))
  exact key.2.differentiableAt.differentiableWithinAt

theorem Lint_eq (δ : ℝ) (hδ : 0 < δ) {r : ℂ} (hr : 0 < r.re) :
    Lint δ r = (1 / r) ^ ((δ + 1 : ℝ) : ℂ) * Complex.Gamma ((δ + 1 : ℝ) : ℂ) := by
  set U : Set ℂ := {r : ℂ | 0 < r.re} with hU_def
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (Lint δ) U := (Lint_differentiableOn δ hδ).analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun r : ℂ => (1 / r) ^ ((δ + 1 : ℝ) : ℂ) *
      Complex.Gamma ((δ + 1 : ℝ) : ℂ)) U := by
    refine DifferentiableOn.analyticOnNhd (fun r hr => ?_) hU
    have hr' : 0 < r.re := hr
    have hr0 : r ≠ 0 := fun h => by simp [h] at hr'
    refine (DifferentiableAt.mul_const ?_ _).differentiableWithinAt
    refine ((differentiableAt_const _).div differentiableAt_id hr0).cpow_const ?_
    show (1 : ℂ) / r ∈ Complex.slitPlane
    rw [Complex.mem_slitPlane_iff]; left
    rw [one_div, Complex.inv_re]; exact div_pos hr' (Complex.normSq_pos.2 hr0)
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h1 : (1 : ℂ) ∈ U := by simp [U]
  have ht : Tendsto (fun n : ℕ => (((1 + 1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at this
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 1).comp this
    · rw [mem_compl_singleton_iff]
      intro h
      have h' := Complex.ofReal_injective (h.trans Complex.ofReal_one.symm)
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), Lint δ z = (1 / z) ^ ((δ + 1 : ℝ) : ℂ) *
      Complex.Gamma ((δ + 1 : ℝ) : ℂ) :=
    ht.frequently (Eventually.of_forall fun n => Lint_ofReal δ hδ (by positivity)).frequently
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hpre h1 hfreq hr

/-! ## The factor `B` -/
/-- The rate `r(t) = 2π(1 - it)`. -/
noncomputable def rB (t : ℝ) : ℂ := 2 * Real.pi * (1 - Complex.I * t)

theorem rB_re (t : ℝ) : (rB t).re = 2 * Real.pi := by simp [rB]

theorem rB_ne (t : ℝ) : rB t ≠ 0 := fun h => by
  have := rB_re t; rw [h] at this; norm_num at this; try linarith [Real.pi_pos]

theorem Bc_eq_Lint (δ : ℝ) (_hδ : 0 < δ) (t : ℝ) : Bc δ t = Lint δ (rB t) := by
  have hw : (fun s : ℝ => ((Real.exp (-(2 * Real.pi * s)) * plusPow δ s : ℝ) : ℂ) * ex (t * s)) =
      (Ioi (0 : ℝ)).indicator
        (fun s : ℝ => ((s ^ δ : ℝ) : ℂ) * Complex.exp (-(rB t * s))) := by
    funext s
    by_cases hs : 0 < s
    · rw [indicator_of_mem (mem_Ioi.2 hs), plusPow, if_pos hs, Complex.ofReal_mul, mul_comm
        ((Real.exp _ : ℝ) : ℂ), mul_assoc, Complex.ofReal_exp, ex, ← Complex.exp_add, rB]
      congr 2; push_cast; ring
    · rw [indicator_of_notMem (by simpa using hs), plusPow, if_neg hs]; simp
  rw [Bc, hw, integral_indicator measurableSet_Ioi, Lint]

theorem Bc_eq (δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    Bc δ t = (1 / rB t) ^ ((δ + 1 : ℝ) : ℂ) * Complex.Gamma ((δ + 1 : ℝ) : ℂ) := by
  rw [Bc_eq_Lint δ hδ, Lint_eq δ hδ (by rw [rB_re]; positivity)]

theorem one_div_rB_re (t : ℝ) : 0 < (1 / rB t).re := by
  rw [one_div, Complex.inv_re, rB_re]
  exact div_pos (by positivity) (Complex.normSq_pos.2 (rB_ne t))

theorem one_add_abs_le_norm_rB (t : ℝ) : 1 + |t| ≤ ‖rB t‖ := by
  have hsq : ‖rB t‖ ^ 2 = 4 * Real.pi ^ 2 * (1 + t ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [rB]; ring
  have h3 := Real.pi_gt_three
  have h1 : (1 + |t|) ^ 2 ≤ ‖rB t‖ ^ 2 := by
    have h2 : 2 ≤ 4 * Real.pi ^ 2 := by nlinarith
    have h4 : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
      nlinarith [sq_abs t, sq_nonneg (|t| - 1), abs_nonneg t]
    rw [hsq]; nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ 1 + t ^ 2)]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h1

/-- **S1.** `|B(t)| ≲ (1 + |t|)^{-δ-1}` (`B(t) = Γ(δ+1)(2π(1 - it))^{-δ-1}`). -/
theorem Bc_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖Bc δ t‖ ≤ C * (1 + |t|) ^ (-(δ + 1)) := by
  refine ⟨‖Complex.Gamma ((δ + 1 : ℝ) : ℂ)‖, norm_nonneg _, fun t => ?_⟩
  rw [Bc_eq δ hδ, norm_mul, Complex.norm_cpow_real, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 : 0 < 1 + |t| := by positivity
  rw [norm_div, norm_one, Real.rpow_neg h1.le, ← Real.inv_rpow h1.le, ← one_div]
  exact Real.rpow_le_rpow (by positivity)
    (one_div_le_one_div_of_le h1 (one_add_abs_le_norm_rB t)) (by linarith)

end TaoBR.Carb.PartS
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
/-! ## Part S: the factors `B` and `E` -/
alias Bc_bound := TaoBR.Carb.PartS.Bc_bound

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartS
open Filter Topology
/-- **S2.** -/
theorem Bc_continuous (δ : ℝ) (hδ : 0 < δ) : Continuous (Bc δ) := by
  have hfun : Bc δ = fun t => (1 / rB t) ^ ((δ + 1 : ℝ) : ℂ) * Complex.Gamma ((δ + 1 : ℝ) : ℂ) :=
    funext (Bc_eq δ hδ)
  rw [hfun]
  refine Continuous.mul ?_ continuous_const
  refine Continuous.cpow ?_ continuous_const fun t => ?_
  · exact continuous_const.div (by unfold rB; fun_prop) rB_ne
  · exact Complex.mem_slitPlane_iff.2 (Or.inl (one_div_rB_re t))

end TaoBR.Carb.PartS
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
alias Bc_continuous := TaoBR.Carb.PartS.Bc_continuous

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartS
open Filter Topology
/-- **S3.** -/
theorem Bc_neg (δ t : ℝ) : Bc δ (-t) = conj (Bc δ t) := by
  rw [Bc, Bc, ← integral_conj]
  congr 1; funext s
  rw [map_mul, Complex.conj_ofReal, conj_ex, neg_mul]

end TaoBR.Carb.PartS
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
alias Bc_neg := TaoBR.Carb.PartS.Bc_neg

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartS
open Filter Topology
/-! ## The factor `E` -/
/-- `b(τ) = π(1 - iτ)`. -/
noncomputable def bE (τ : ℝ) : ℂ := Real.pi * (1 - Complex.I * τ)

theorem bE_re (τ : ℝ) : (bE τ).re = Real.pi := by simp [bE]

theorem one_sub_ne (τ : ℝ) : (1 - Complex.I * τ) ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this

theorem integrand_eq (m : ℕ) (d v : E m) (τ : ℝ) :
    (Real.exp (-(Real.pi * ‖v‖ ^ 2)) : ℂ) * ex (⟪d, v⟫ + τ * ‖v‖ ^ 2 / 2) =
      Complex.exp (-bE τ * (‖v‖ : ℂ) ^ 2 + (2 * Real.pi * Complex.I) * (⟪d, v⟫ : ℂ)) := by
  rw [Complex.ofReal_exp, ex, ← Complex.exp_add, bE]
  congr 1; push_cast; ring

theorem Eg_eq (m : ℕ) (d : E m) (τ : ℝ) :
    Eg m d τ = (1 / (1 - Complex.I * τ)) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ) *
      Complex.exp (-(Real.pi * ‖d‖ ^ 2) / (1 - Complex.I * τ)) := by
  rw [Eg]
  simp_rw [integrand_eq]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by rw [bE_re]; exact Real.pi_pos),
    finrank_euclideanSpace_fin]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have h1 := one_sub_ne τ
  congr 1
  · congr 1
    · rw [bE]; field_simp
    · push_cast; ring
  · congr 1
    rw [bE]; field_simp
    linear_combination (4 * (‖d‖ : ℂ) ^ 2) * Complex.I_sq

theorem one_div_re (τ : ℝ) : (1 / (1 - Complex.I * τ)).re = 1 / (1 + τ ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]; simp; ring

theorem norm_one_div (τ : ℝ) : ‖1 / (1 - Complex.I * τ)‖ = (1 + τ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  rw [norm_div, norm_one, Complex.norm_def, Complex.normSq_apply]
  simp
  rw [Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]
  congr 2 <;> ring

theorem Eg_norm_eq (m : ℕ) (d : E m) (τ : ℝ) :
    ‖Eg m d τ‖ = (1 + τ ^ 2) ^ (-((m : ℝ) / 4)) * Real.exp (-(Real.pi * ‖d‖ ^ 2 / (1 + τ ^ 2))) := by
  rw [Eg_eq, norm_mul, Complex.norm_cpow_real, norm_one_div, Complex.norm_exp,
    ← Real.rpow_mul (by positivity)]
  congr 1
  · congr 1; ring
  · congr 1
    rw [show -((Real.pi : ℂ) * (‖d‖ : ℂ) ^ 2) = ((-(Real.pi * ‖d‖ ^ 2) : ℝ) : ℂ) by push_cast; ring,
      div_eq_mul_one_div, Complex.re_ofReal_mul, one_div_re]
    ring

/-- **S4.** `|E(d, τ)| = (1 + τ²)^{-m/4} exp(-π|d|²/(1 + τ²))`. -/
theorem Eg_norm (m : ℕ) (d : E m) (τ : ℝ) :
    ‖Eg m d τ‖ ≤ (1 + τ ^ 2) ^ (-((m : ℝ) / 4)) * Real.exp (-(Real.pi * ‖d‖ ^ 2 / (1 + τ ^ 2))) :=
  (Eg_norm_eq m d τ).le

end TaoBR.Carb.PartS
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
alias Eg_norm := TaoBR.Carb.PartS.Eg_norm

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartS
open Filter Topology
/-- **S5.** -/
theorem Eg_continuous (m : ℕ) : Continuous (fun q : E m × ℝ => Eg m q.1 q.2) := by
  simp_rw [Eg_eq]
  have hc : Continuous fun q : E m × ℝ => (1 - Complex.I * (q.2 : ℂ)) := by fun_prop
  refine Continuous.mul ?_ ?_
  · refine Continuous.cpow (continuous_const.div hc fun q => one_sub_ne q.2) continuous_const
      fun q => ?_
    exact Complex.mem_slitPlane_iff.2 (Or.inl (by rw [one_div_re]; positivity))
  · exact Complex.continuous_exp.comp
      ((by fun_prop : Continuous fun q : E m × ℝ => -((Real.pi : ℂ) * (‖q.1‖ : ℂ) ^ 2)).div hc
        fun q => one_sub_ne q.2)

end TaoBR.Carb.PartS
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
alias Eg_continuous := TaoBR.Carb.PartS.Eg_continuous

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartS
open Filter Topology
/-- **S6.** -/
theorem Eg_neg (m : ℕ) (d : E m) (τ : ℝ) : Eg m (-d) (-τ) = conj (Eg m d τ) := by
  rw [Eg, Eg, ← integral_conj]
  congr 1; funext v
  rw [map_mul, Complex.conj_ofReal, conj_ex, inner_neg_left]
  congr 2; ring

end TaoBR.Carb.PartS
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
alias Eg_neg := TaoBR.Carb.PartS.Eg_neg

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartS
open Filter Topology
/-! ## Superposition -/
/-- `a(τ) = π + iπ/τ`. -/
noncomputable def aE (τ : ℝ) : ℂ := Real.pi + Real.pi * Complex.I / τ

theorem aE_re (τ : ℝ) : (aE τ).re = Real.pi := by
  simp [aE, Complex.div_re]

theorem aE_ne (τ : ℝ) : aE τ ≠ 0 := fun h => by
  have := aE_re τ; rw [h] at this; simp at this; exact Real.pi_ne_zero this.symm

theorem sup_integrand (m : ℕ) (d ξ : E m) (τ : ℝ) (hτ : τ ≠ 0) :
    (Real.exp (-(Real.pi * ‖ξ‖ ^ 2)) : ℂ) * ex (-(‖d - ξ‖ ^ 2 / (2 * τ))) =
      Complex.exp (-aE τ * (‖ξ‖ : ℂ) ^ 2 + (2 * Real.pi * Complex.I / τ) * (⟪d, ξ⟫ : ℂ)) *
        Complex.exp (-(Real.pi * Complex.I * (‖d‖ : ℂ) ^ 2 / τ)) := by
  have hτ' : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hτ
  rw [Complex.ofReal_exp, ex, ← Complex.exp_add, ← Complex.exp_add, norm_sub_sq_real, aE]
  congr 1; push_cast; field_simp; ring

theorem sup_integral (m : ℕ) (d : E m) (τ : ℝ) (hτ : τ ≠ 0) :
    ∫ ξ : E m, (Real.exp (-(Real.pi * ‖ξ‖ ^ 2)) : ℂ) * ex (-(‖d - ξ‖ ^ 2 / (2 * τ))) =
      (Real.pi / aE τ) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ) *
        Complex.exp (-(Real.pi * ‖d‖ ^ 2) / (1 - Complex.I * τ)) := by
  simp_rw [sup_integrand m d _ τ hτ]
  rw [integral_mul_const,
    GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by rw [aE_re]; exact Real.pi_pos),
    finrank_euclideanSpace_fin, mul_assoc]
  have hτ' : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hτ
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have h1 := one_sub_ne τ
  have ha := aE_ne τ
  congr 1
  · congr 1; push_cast; ring
  · rw [← Complex.exp_add]
    congr 1
    have hτI : (τ : ℂ) + Complex.I ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp at this
    rw [aE] at ha ⊢
    rw [show (Real.pi : ℂ) + Real.pi * Complex.I / τ = Real.pi * (τ + Complex.I) / τ by
      field_simp] at ha ⊢
    field_simp
    linear_combination (4 * (‖d‖ : ℂ) ^ 2 * (τ : ℂ) ^ 2) * Complex.I_sq

theorem pi_div_aE (τ : ℝ) (hτ : τ ≠ 0) :
    (Real.pi : ℂ) / aE τ = (-Complex.I * τ) * (1 / (1 - Complex.I * τ)) := by
  have hτ' : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hτ
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have h1 := one_sub_ne τ
  have ha := aE_ne τ
  have hτI : (τ : ℂ) + Complex.I ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this
  rw [aE] at ha ⊢
  rw [show (Real.pi : ℂ) + Real.pi * Complex.I / τ = Real.pi * (τ + Complex.I) / τ by
    field_simp] at ha ⊢
  rw [mul_one_div, div_eq_div_iff ha h1]
  field_simp
  linear_combination Complex.I_sq

/-- The prefactor `c(τ)`. -/
noncomputable def cS (m : ℕ) (τ : ℝ) : ℂ :=
  (1 / (1 - Complex.I * τ)) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ) /
    ((Real.pi : ℂ) / aE τ) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ)

theorem cS_measurable (m : ℕ) : Measurable (cS m) := by
  unfold cS aE; fun_prop

theorem norm_cS (m : ℕ) (τ : ℝ) (hτ : τ ≠ 0) : ‖cS m τ‖ = |τ| ^ (-((m : ℝ) / 2)) := by
  rw [cS, norm_div, Complex.norm_cpow_real, Complex.norm_cpow_real, pi_div_aE τ hτ, norm_mul,
    norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
  have hA : 0 < ‖1 / (1 - Complex.I * τ)‖ ^ ((m : ℝ) / 2) :=
    Real.rpow_pos_of_pos (norm_pos_iff.2 (one_div_ne_zero (one_sub_ne τ))) _
  rw [Real.rpow_neg (abs_nonneg _)]
  field_simp

/-- **S7 (superposition).** For `τ ≠ 0`, `E(·, τ)` is the Gaussian `e^{-π|·|²}` convolved with the
pure Fresnel kernel `c(τ) e(-|·|²/(2τ))`, `|c(τ)| = |τ|^{-m/2}`. -/
theorem Eg_superpos (m : ℕ) :
    ∃ c : ℝ → ℂ, Measurable c ∧ (∀ τ : ℝ, τ ≠ 0 → ‖c τ‖ = |τ| ^ (-((m : ℝ) / 2))) ∧
      ∀ τ : ℝ, τ ≠ 0 → ∀ d : E m, Eg m d τ =
        c τ * ∫ ξ : E m, (Real.exp (-(Real.pi * ‖ξ‖ ^ 2)) : ℂ) * ex (-(‖d - ξ‖ ^ 2 / (2 * τ))) := by
  refine ⟨cS m, cS_measurable m, norm_cS m, fun τ hτ d => ?_⟩
  rw [sup_integral m d τ hτ, Eg_eq, cS]
  have hne : ((Real.pi : ℂ) / aE τ) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left
    exact div_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) (aE_ne τ)
  field_simp

end TaoBR.Carb.PartS
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
alias Eg_superpos := TaoBR.Carb.PartS.Eg_superpos

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartS
open Filter Topology
variable {m : ℕ}
/-! ## Integrability of `kb` -/
@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

end TaoBR.Carb.PartS
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartYU
/-- Measurability of the convolution integrand on the product. -/
theorem young_meas {n : ℕ} (k f : E n → ℂ) (hk : AEStronglyMeasurable k volume)
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun p : E n × E n => k (p.1 - p.2) * f p.2)
      ((volume : Measure (E n)).prod volume) := by
  have h1 : AEStronglyMeasurable (fun p : E n × E n => k (p.1 - p.2))
      ((volume : Measure (E n)).prod volume) :=
    (hk.mono_ac (quasiMeasurePreserving_sub_of_right_invariant
      (volume : Measure (E n)) volume).absolutelyContinuous).comp_measurable measurable_sub
  exact h1.mul hf.comp_snd

/-- The majorant `G(x) = ∫⁻ |k(x-y)| |f(y)| dy` is a.e.-measurable. -/
theorem G_aemeas {n : ℕ} (k f : E n → ℂ) (hk : AEStronglyMeasurable k volume)
    (hf : AEStronglyMeasurable f volume) :
    AEMeasurable (fun x : E n => ∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ) volume := by
  have := (young_meas k f hk hf).enorm.lintegral_prod_right'
  simpa [enorm_mul] using this

/-- Pointwise Hölder: `(∫ a b)^r ≤ (∫ a)^{r-1} ∫ a b^r`. -/
theorem holder_weight {α : Type*} [MeasurableSpace α] (μ : Measure α) (a b : α → ℝ≥0∞)
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) (r : ℝ) (hr : 1 ≤ r) :
    (∫⁻ y, a y * b y ∂μ) ^ r ≤ (∫⁻ y, a y ∂μ) ^ (r - 1) * ∫⁻ y, a y * b y ^ r ∂μ := by
  have hr0 : 0 < r := by linarith
  have hri : 0 ≤ r⁻¹ := inv_nonneg.2 hr0.le
  have hri1 : 0 ≤ 1 - r⁻¹ := by
    have : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
    linarith
  have key := ENNReal.lintegral_mul_norm_pow_le (μ := μ) (g := fun y => a y * b y ^ r) ha
    (ha.mul (hb.pow_const r)) hri1 hri
    (by ring)
  have heq : ∀ y, a y ^ (1 - r⁻¹) * (a y * b y ^ r) ^ r⁻¹ = a y * b y := by
    intro y
    rw [ENNReal.mul_rpow_of_nonneg _ _ hri, ENNReal.rpow_rpow_inv hr0.ne', ← mul_assoc,
      ← ENNReal.rpow_add_of_nonneg _ _ hri1 hri]
    simp
  simp_rw [heq] at key
  calc (∫⁻ y, a y * b y ∂μ) ^ r
      ≤ ((∫⁻ y, a y ∂μ) ^ (1 - r⁻¹) * (∫⁻ y, a y * b y ^ r ∂μ) ^ r⁻¹) ^ r :=
        ENNReal.rpow_le_rpow key hr0.le
    _ = (∫⁻ y, a y ∂μ) ^ (r - 1) * ∫⁻ y, a y * b y ^ r ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one]
        congr 2
        field_simp

/-- Young, finite exponent, lintegral form. -/
theorem young_rpow {n : ℕ} (k f : E n → ℂ) (hk : Integrable k)
    (hf : AEStronglyMeasurable f volume) (r : ℝ) (hr : 1 ≤ r) :
    ∫⁻ x, (∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ) ^ r ≤
      (∫⁻ z, ‖k z‖ₑ) ^ r * ∫⁻ y, ‖f y‖ₑ ^ r := by
  set K := ∫⁻ z, ‖k z‖ₑ with hKdef
  have hK : K ≠ ⊤ := (hasFiniteIntegral_iff_enorm.1 hk.2).ne
  have hkx : ∀ x : E n, ∫⁻ y, ‖k (x - y)‖ₑ = K := fun x =>
    lintegral_sub_left_eq_self (fun z => ‖k z‖ₑ) x
  have hky : ∀ y : E n, ∫⁻ x, ‖k (x - y)‖ₑ = K := fun y =>
    lintegral_sub_right_eq_self (fun z => ‖k z‖ₑ) y
  have step1 : ∀ x : E n, (∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ) ^ r ≤
      K ^ (r - 1) * ∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ ^ r := by
    intro x
    have := holder_weight volume (fun y => ‖k (x - y)‖ₑ) (fun y => ‖f y‖ₑ)
      (hk.comp_sub_left x).aestronglyMeasurable.enorm hf.enorm r hr
    rwa [hkx x] at this
  have hmeas : AEMeasurable (Function.uncurry fun (x y : E n) => ‖k (x - y)‖ₑ * ‖f y‖ₑ ^ r)
      ((volume : Measure (E n)).prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : E n × E n => k (p.1 - p.2))
        ((volume : Measure (E n)).prod volume) :=
      (hk.aestronglyMeasurable.mono_ac (quasiMeasurePreserving_sub_of_right_invariant
        (volume : Measure (E n)) volume).absolutelyContinuous).comp_measurable measurable_sub
    exact h1.enorm.mul (hf.comp_snd.enorm.pow_const r)
  calc ∫⁻ x, (∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ) ^ r
      ≤ ∫⁻ x, K ^ (r - 1) * ∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ ^ r := lintegral_mono step1
    _ = K ^ (r - 1) * ∫⁻ x, ∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ ^ r :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hK)
    _ = K ^ (r - 1) * ∫⁻ y, ∫⁻ x, ‖k (x - y)‖ₑ * ‖f y‖ₑ ^ r := by
        rw [lintegral_lintegral_swap hmeas]
    _ = K ^ (r - 1) * ∫⁻ y, K * ‖f y‖ₑ ^ r := by
        congr 1
        refine lintegral_congr fun y => ?_
        rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) enorm_ne_top),
          hky y]
    _ = K ^ r * ∫⁻ y, ‖f y‖ₑ ^ r := by
        rw [lintegral_const_mul' _ _ hK, ← mul_assoc]
        congr 1
        conv_rhs => rw [show r = (r - 1) + 1 by ring]
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]

/-- Young, `q = ∞`, pointwise. -/
theorem young_top {n : ℕ} (k f : E n → ℂ) (hk : Integrable k) (x : E n) :
    ∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ ≤ (∫⁻ z, ‖k z‖ₑ) * eLpNormEssSup f volume := by
  calc ∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ ≤ ∫⁻ y, ‖k (x - y)‖ₑ * eLpNormEssSup f volume := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := volume)] with y hy
        gcongr
    _ = (∫⁻ y, ‖k (x - y)‖ₑ) * eLpNormEssSup f volume :=
        lintegral_mul_const'' _ (hk.comp_sub_left x).aestronglyMeasurable.enorm
    _ = (∫⁻ z, ‖k z‖ₑ) * eLpNormEssSup f volume := by
        rw [lintegral_sub_left_eq_self (fun z => ‖k z‖ₑ) x]

/-- Young for the majorant `G`. -/
theorem young_G {n : ℕ} (k f : E n → ℂ) (hk : Integrable k)
    (hf : AEStronglyMeasurable f volume) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    eLpNorm (fun x : E n => ∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ) q volume ≤
      eLpNorm k 1 volume * eLpNorm f q volume := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  rcases eq_or_ne q ⊤ with rfl | hqt
  · rw [eLpNorm_exponent_top, eLpNorm_exponent_top]
    refine eLpNormEssSup_le_of_ae_enorm_bound (Filter.Eventually.of_forall fun x => ?_)
    rw [enorm_eq_self]
    exact young_top k f hk x
  · have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq).ne'
    have hr : 1 ≤ q.toReal := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono hqt hq
    have hr0 : 0 < q.toReal := by linarith
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt]
    simp only [enorm_eq_self]
    calc (∫⁻ x, (∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ) ^ q.toReal) ^ (1 / q.toReal)
        ≤ ((∫⁻ z, ‖k z‖ₑ) ^ q.toReal * ∫⁻ y, ‖f y‖ₑ ^ q.toReal) ^ (1 / q.toReal) :=
          ENNReal.rpow_le_rpow (young_rpow k f hk hf _ hr) (by positivity)
      _ = (∫⁻ z, ‖k z‖ₑ) * (∫⁻ y, ‖f y‖ₑ ^ q.toReal) ^ (1 / q.toReal) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hr0.ne', ENNReal.rpow_one]

/-- The majorant is finite a.e. when `f ∈ L^q`. -/
theorem G_ae_lt_top {n : ℕ} (k f : E n → ℂ) (hk : Integrable k) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (hf : MemLp f q volume) :
    ∀ᵐ x, ∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ < ⊤ := by
  have hK : eLpNorm k 1 volume < ⊤ := (memLp_one_iff_integrable.2 hk).eLpNorm_lt_top
  have hG := (young_G k f hk hf.1 q hq).trans_lt (ENNReal.mul_lt_top hK hf.eLpNorm_lt_top)
  rcases eq_or_ne q ⊤ with rfl | hqt
  · exact Filter.Eventually.of_forall fun x =>
      (young_top k f hk x).trans_lt (ENNReal.mul_lt_top
        (by rw [← eLpNorm_one_eq_lintegral_enorm]; exact hK)
        (by rw [← eLpNorm_exponent_top]; exact hf.eLpNorm_lt_top))
  · have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one hq).ne'
    have hr0 : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt] at hG
    simp only [enorm_eq_self] at hG
    have hI : ∫⁻ x, (∫⁻ y, ‖k (x - y)‖ₑ * ‖f y‖ₑ) ^ q.toReal ≠ ⊤ := by
      intro h
      rw [h, ENNReal.top_rpow_of_pos (by positivity)] at hG
      exact lt_irrefl _ hG
    filter_upwards [ae_lt_top' ((G_aemeas k f hk.1 hf.1).pow_const q.toReal) hI] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos hr0).1 hx

/-- **Y.** -/
theorem conv_basic {n : ℕ} (k : E n → ℂ) (hk : Integrable k) (q : ℝ≥0∞) (hq : 1 ≤ q)
    (f : E n → ℂ) (hf : AEStronglyMeasurable f volume) :
    (MemLp f q volume → ∀ᵐ x, Integrable (fun y => k (x - y) * f y)) ∧
      AEStronglyMeasurable (conv k f) volume ∧
      eLpNorm (conv k f) q volume ≤ eLpNorm k 1 volume * eLpNorm f q volume := by
  refine ⟨fun hfq => ?_, ?_, ?_⟩
  · filter_upwards [G_ae_lt_top k f hk q hq hfq] with x hx
    refine ⟨(hk.comp_sub_left x).aestronglyMeasurable.mul hf, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simpa [enorm_mul] using hx
  · exact (young_meas k f hk.1 hf).integral_prod_right'
  · refine le_trans (eLpNorm_mono_enorm fun x => ?_) (young_G k f hk hf q hq)
    rw [enorm_eq_self]
    refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
    simp [enorm_mul]

end TaoBR.Carb.PartYU
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
/-! ## Part Y: Young's inequality with an integrable kernel -/
alias conv_basic := TaoBR.Carb.PartYU.conv_basic

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartYU
/-- Hölder in `eLpNorm` form, for conjugate real exponents. -/
theorem holder_eLp {n : ℕ} {p r : ℝ} (hpr : p.HolderConjugate r) (u : E n → ℂ)
    {ε : Type*} [ENorm ε] (v : E n → ε) (hu : AEStronglyMeasurable u volume)
    (hv : AEMeasurable (fun x => ‖v x‖ₑ) volume) :
    ∫⁻ x, ‖u x‖ₑ * ‖v x‖ₑ ≤ eLpNorm u (ENNReal.ofReal p) volume * eLpNorm v (ENNReal.ofReal r) volume := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp [hpr.pos]
  have hr0 : ENNReal.ofReal r ≠ 0 := by simp [hpr.symm.pos]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hpr.nonneg, ENNReal.toReal_ofReal hpr.symm.nonneg]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpr hu.enorm hv

/-- **U.** An `L^q` bound for `k *` gives the same `L^{q'}` bound for the reflected kernel. -/
theorem dual_bound {n : ℕ} (k : E n → ℂ) (hk : Integrable k) (q : ℝ) (hq : 1 < q) (A : ℝ≥0∞)
    (h : ∀ f : E n → ℂ, MemLp f (ENNReal.ofReal q) volume →
      eLpNorm (conv k f) (ENNReal.ofReal q) volume ≤ A * eLpNorm f (ENNReal.ofReal q) volume) :
    ∀ g : E n → ℂ, MemLp g (ENNReal.ofReal (q / (q - 1))) volume →
      eLpNorm (conv (fun z => k (-z)) g) (ENNReal.ofReal (q / (q - 1))) volume ≤
        A * eLpNorm g (ENNReal.ofReal (q / (q - 1))) volume := by
  intro g hg
  have hpq : (q / (q - 1)).HolderConjugate q :=
    ((Real.holderConjugate_iff_eq_conjExponent hq).2 rfl).symm
  set q' := q / (q - 1) with hq'def
  have hq'0 : 0 < q' := hpq.pos
  have hq0 : 0 < q := by linarith
  have hk' : Integrable (fun z => k (-z)) := hk.comp_neg
  have hqE : 1 ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq.le
  set hh := conv (fun z => k (-z)) g with hhdef
  obtain ⟨-, hhm, hhY⟩ := conv_basic (fun z => k (-z)) hk' (ENNReal.ofReal q')
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hpq.lt.le) g hg.1
  have hhL : MemLp hh (ENNReal.ofReal q') volume :=
    ⟨hhm, hhY.trans_lt (ENNReal.mul_lt_top (memLp_one_iff_integrable.2 hk').eLpNorm_lt_top
      hg.eLpNorm_lt_top)⟩
  by_cases hN : eLpNorm hh (ENNReal.ofReal q') volume = 0
  · rw [hN]; exact zero_le
  set I := ∫⁻ x, ‖hh x‖ₑ ^ q' with hIdef
  have hNI : eLpNorm hh (ENNReal.ofReal q') volume = I ^ (1 / q') := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hq'0]) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq'0.le]
  have hI0 : I ≠ 0 := by
    intro h0; apply hN; rw [hNI, h0, ENNReal.zero_rpow_of_pos (by positivity)]
  have hIt : I ≠ ⊤ := by
    intro h0
    have := hhL.eLpNorm_lt_top
    rw [hNI, h0, ENNReal.top_rpow_of_pos (by positivity)] at this
    exact lt_irrefl _ this
  -- the extremal function
  set f : E n → ℂ := fun x => conj (hh x) * ((‖hh x‖ ^ (q' - 2) : ℝ) : ℂ) with hfdef
  have hfr : ∀ x, ‖f x‖ ^ q = ‖hh x‖ ^ q' := by
    intro x
    by_cases h0 : hh x = 0
    · simp [hfdef, h0, Real.zero_rpow hq0.ne', Real.zero_rpow hq'0.ne']
    · have hpos : 0 < ‖hh x‖ := norm_pos_iff.2 h0
      have : ‖f x‖ = ‖hh x‖ ^ (q' - 1) := by
        rw [hfdef]
        simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        conv_lhs => arg 1; rw [← Real.rpow_one ‖hh x‖]
        rw [← Real.rpow_add hpos]; ring_nf
      rw [this, ← Real.rpow_mul hpos.le]
      congr 1
      have hq1 : q - 1 ≠ 0 := sub_ne_zero.2 hq.ne'
      rw [hq'def]; field_simp; ring
  have hhf : ∀ x, hh x * f x = ((‖hh x‖ ^ q' : ℝ) : ℂ) := by
    intro x
    by_cases h0 : hh x = 0
    · simp [hfdef, h0, Real.zero_rpow hq'0.ne']
    · have hpos : 0 < ‖hh x‖ := norm_pos_iff.2 h0
      rw [hfdef, ← mul_assoc, Complex.mul_conj']
      have : ‖hh x‖ ^ q' = ‖hh x‖ ^ (2 : ℝ) * ‖hh x‖ ^ (q' - 2) := by
        rw [← Real.rpow_add hpos]; ring_nf
      rw [this, Real.rpow_two]; push_cast; ring
  have hfm : AEStronglyMeasurable f volume := by
    have hφ : Measurable (fun z : ℂ => conj z * ((‖z‖ ^ (q' - 2) : ℝ) : ℂ)) := by
      fun_prop
    exact (hφ.comp_aemeasurable hhm.aemeasurable).aestronglyMeasurable
  have hfe : ∀ x, ‖f x‖ₑ ^ q = ‖hh x‖ₑ ^ q' := by
    intro x
    rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg
      (norm_nonneg _) hq0.le, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq'0.le, hfr]
  have hF : eLpNorm f (ENNReal.ofReal q) volume = I ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hq0]) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le]
    simp_rw [hfe]
    rfl
  have hfL : MemLp f (ENNReal.ofReal q) volume :=
    ⟨hfm, by rw [hF]; exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hIt⟩
  -- the bound for `k * f`
  have hkf := h f hfL
  rw [hF] at hkf
  -- Fubini
  set F : E n → E n → ℂ := fun y x => g y * (k (y - x) * f x) with hFdef
  have hFm : AEStronglyMeasurable (Function.uncurry F) ((volume : Measure (E n)).prod volume) :=
    hg.1.comp_fst.mul (young_meas k f hk.1 hfm)
  have hGm := G_aemeas k f hk.1 hfm
  have hFi : Integrable (Function.uncurry F) ((volume : Measure (E n)).prod volume) := by
    refine ⟨hFm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hFm.enorm]
    have : ∫⁻ y, ∫⁻ x, ‖Function.uncurry F (y, x)‖ₑ =
        ∫⁻ y, ‖g y‖ₑ * ‖(∫⁻ x, ‖k (y - x)‖ₑ * ‖f x‖ₑ)‖ₑ := by
      refine lintegral_congr fun y => ?_
      simp only [Function.uncurry_apply_pair, hFdef, enorm_mul, enorm_eq_self]
      exact lintegral_const_mul' _ _ enorm_ne_top
    rw [this]
    refine (holder_eLp hpq g (fun y => ∫⁻ x, ‖k (y - x)‖ₑ * ‖f x‖ₑ) hg.1
      (by simpa only [enorm_eq_self] using hGm)).trans_lt ?_
    exact ENNReal.mul_lt_top hg.eLpNorm_lt_top
      ((young_G k f hk hfm _ hqE).trans_lt (ENNReal.mul_lt_top (memLp_one_iff_integrable.2 hk).eLpNorm_lt_top
          hfL.eLpNorm_lt_top))
  have hswap := integral_integral_swap hFi
  have hL : ∫ x, hh x * f x = ∫ x, ∫ y, F y x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hhdef, conv, hFdef]
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [neg_sub]; ring
  have hR : ∫ y, ∫ x, F y x = ∫ y, g y * conv k f y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hFdef, conv]
    exact integral_const_mul _ _
  -- the value of the pairing
  have hval : ‖∫ x, hh x * f x‖ₑ = I := by
    simp_rw [hhf]
    rw [integral_complex_ofReal, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg
      (integral_nonneg fun x => by positivity)]
    have hint : Integrable (fun x => ‖hh x‖ ^ q') volume := by
      have := hhL.integrable_norm_rpow (by simp [hq'0]) ENNReal.ofReal_ne_top
      rwa [ENNReal.toReal_ofReal hq'0.le] at this
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by
      positivity)]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq'0.le, ofReal_norm]
  have hmain : I ≤ eLpNorm g (ENNReal.ofReal q') volume * (A * I ^ (1 / q)) := by
    refine le_trans (le_of_eq hval.symm) ?_
    rw [hL, ← hswap, hR]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    simp only [enorm_mul]
    refine (holder_eLp hpq g (conv k f) hg.1 ?_).trans ?_
    · exact (conv_basic k hk _ hqE f hfm).2.1.enorm
    · gcongr
  rw [hNI]
  have hsplit : I = I ^ (1 / q') * I ^ (1 / q) := by
    rw [← ENNReal.rpow_add _ _ hI0 hIt, one_div, one_div, hpq.inv_add_inv_eq_one,
      ENNReal.rpow_one]
  have hc0 : I ^ (1 / q) ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hI0, hIt, hq0]
  have hct : I ^ (1 / q) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hIt
  rw [← ENNReal.mul_le_mul_iff_left hc0 hct, ← hsplit]
  calc I ≤ eLpNorm g (ENNReal.ofReal q') volume * (A * I ^ (1 / q)) := hmain
    _ = A * eLpNorm g (ENNReal.ofReal q') volume * I ^ (1 / q) := by ring

end TaoBR.Carb.PartYU
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
/-! ## Part U: duality -/
alias dual_bound := TaoBR.Carb.PartYU.dual_bound

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartI
variable {n : ℕ}
/-! ## One-dimensional power integrals -/
theorem lint_Ioo_rpow (a r : ℝ) (ha : 0 < a) (hr : -1 < r) :
    ∫⁻ t in Ioo 0 a, ENNReal.ofReal (t ^ r) = ENNReal.ofReal (a ^ (r + 1) / (r + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha.le,
      integral_rpow (Or.inl hr), Real.zero_rpow (by linarith), sub_zero]
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).1
      (intervalIntegral.intervalIntegrable_rpow' hr)).mono_set Ioo_subset_Ioc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using Real.rpow_nonneg ht.1.le _

theorem lint_Ici_rpow (a r : ℝ) (ha : 0 < a) (hr : r < -1) :
    ∫⁻ t in Ici a, ENNReal.ofReal (t ^ r) = ENNReal.ofReal (-a ^ (r + 1) / (r + 1)) := by
  rw [← setLIntegral_congr Ioi_ae_eq_Ici,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hr ha),
    integral_Ioi_rpow_of_lt hr ha]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using Real.rpow_nonneg (ha.trans ht).le _

/-- The inner integral of the high part. -/
theorem inner_hi (p p₀ a : ℝ) (hp₀ : 0 < p₀) (h01 : p₀ < p) (ha : 0 ≤ a) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - 1 - p₀)) *
      (if t < a then ENNReal.ofReal (a ^ p₀) else 0) = ENNReal.ofReal (a ^ p / (p - p₀)) := by
  have hfun : (fun t : ℝ => ENNReal.ofReal (t ^ (p - 1 - p₀)) *
      (if t < a then ENNReal.ofReal (a ^ p₀) else 0)) =
      (Iio a).indicator (fun t => ENNReal.ofReal (t ^ (p - 1 - p₀)) * ENNReal.ofReal (a ^ p₀)) := by
    funext t
    by_cases h : t < a <;> simp [Set.indicator, h]
  rw [hfun, setLIntegral_indicator measurableSet_Iio, inter_comm, Ioi_inter_Iio,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  rcases ha.eq_or_lt with rfl | ha'
  · simp [Real.zero_rpow (by linarith : p ≠ 0)]
  rw [lint_Ioo_rpow a _ ha' (by linarith), ← ENNReal.ofReal_mul (by
    have : 0 < p - 1 - p₀ + 1 := by linarith
    positivity)]
  congr 1
  have he : p - 1 - p₀ + 1 = p - p₀ := by ring
  rw [he, div_mul_eq_mul_div, ← Real.rpow_add ha']
  congr 2; ring

/-- The inner integral of the low part. -/
theorem inner_lo (p p₁ a : ℝ) (hp : 0 < p) (h12 : p < p₁) (ha : 0 ≤ a) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (p - 1 - p₁)) *
      (if a ≤ t then ENNReal.ofReal (a ^ p₁) else 0) = ENNReal.ofReal (a ^ p / (p₁ - p)) := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp [Real.zero_rpow (by linarith : p₁ ≠ 0), Real.zero_rpow hp.ne']
  have hfun : (fun t : ℝ => ENNReal.ofReal (t ^ (p - 1 - p₁)) *
      (if a ≤ t then ENNReal.ofReal (a ^ p₁) else 0)) =
      (Ici a).indicator (fun t => ENNReal.ofReal (t ^ (p - 1 - p₁)) * ENNReal.ofReal (a ^ p₁)) := by
    funext t
    by_cases h : a ≤ t <;> simp [Set.indicator, h]
  rw [hfun, setLIntegral_indicator measurableSet_Ici,
    inter_eq_left.2 (Ici_subset_Ioi.2 ha'),
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lint_Ici_rpow a _ ha' (by linarith),
    ← ENNReal.ofReal_mul (by
      have : p - 1 - p₁ + 1 < 0 := by linarith
      rw [neg_div, ← div_neg]
      exact div_nonneg (Real.rpow_nonneg ha'.le _) (by linarith))]
  congr 1
  have he : p - 1 - p₁ + 1 = p - p₁ := by ring
  rw [he, neg_div, ← div_neg, div_mul_eq_mul_div, ← Real.rpow_add ha']
  congr 1
  · congr 1; ring
  · ring

/-! ## Splitting `f` at height `t` -/
/-- `f^t = f 1_{|f| > t}`. -/
noncomputable def fhi (f : E n → ℂ) (t : ℝ) : E n → ℂ := {y | t < ‖f y‖}.indicator f

/-- `f_t = f 1_{|f| ≤ t}`. -/
noncomputable def flo (f : E n → ℂ) (t : ℝ) : E n → ℂ := {y | ‖f y‖ ≤ t}.indicator f

theorem fhi_add_flo (f : E n → ℂ) (t : ℝ) (y : E n) : fhi f t y + flo f t y = f y := by
  by_cases h : t < ‖f y‖
  · simp [fhi, flo, Set.indicator, h, not_le.2 h]
  · simp [fhi, flo, Set.indicator, h, not_lt.1 h]

theorem enorm_fhi (f : E n → ℂ) (t q : ℝ) (hq : 0 < q) (y : E n) :
    ‖fhi f t y‖ₑ ^ q = if t < ‖f y‖ then ENNReal.ofReal (‖f y‖ ^ q) else 0 := by
  by_cases h : t < ‖f y‖
  · rw [fhi, Set.indicator_of_mem (show y ∈ {y | t < ‖f y‖} from h), if_pos h,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le, ofReal_norm]
  · rw [fhi, Set.indicator_of_notMem (show y ∉ {y | t < ‖f y‖} from h), if_neg h, enorm_zero,
      ENNReal.zero_rpow_of_pos hq]

theorem enorm_flo (f : E n → ℂ) (t q : ℝ) (hq : 0 < q) (y : E n) :
    ‖flo f t y‖ₑ ^ q = if ‖f y‖ ≤ t then ENNReal.ofReal (‖f y‖ ^ q) else 0 := by
  by_cases h : ‖f y‖ ≤ t
  · rw [flo, Set.indicator_of_mem (show y ∈ {y | ‖f y‖ ≤ t} from h), if_pos h,
      ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le, ofReal_norm]
  · rw [flo, Set.indicator_of_notMem (show y ∉ {y | ‖f y‖ ≤ t} from h), if_neg h, enorm_zero,
      ENNReal.zero_rpow_of_pos hq]

/-- `MemLp` from a pointwise power bound. -/
theorem memLp_of_pt (g f : E n → ℂ) (hg : AEStronglyMeasurable g volume) (q p c : ℝ) (hq : 0 < q)
    (hp : 0 < p) (hc : 0 ≤ c) (hf : MemLp f (ENNReal.ofReal p) volume)
    (h : ∀ y, ‖g y‖ ^ q ≤ c * ‖f y‖ ^ p) : MemLp g (ENNReal.ofReal q) volume := by
  refine ⟨hg, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simpa using hq) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le]
  have hfi := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by simpa using hp)
    ENNReal.ofReal_ne_top hf.2
  rw [ENNReal.toReal_ofReal hp.le] at hfi
  calc ∫⁻ y, ‖g y‖ₑ ^ q ≤ ∫⁻ y, ENNReal.ofReal c * ‖f y‖ₑ ^ p := by
        refine lintegral_mono fun y => ?_
        rw [← ofReal_norm, ← ofReal_norm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le, ← ENNReal.ofReal_mul hc]
        exact ENNReal.ofReal_le_ofReal (h y)
    _ = ENNReal.ofReal c * ∫⁻ y, ‖f y‖ₑ ^ p := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfi

theorem memLp_fhi (f : E n → ℂ) (hfm : Measurable f) (p₀ p : ℝ) (hp₀ : 0 < p₀) (h01 : p₀ < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) (t : ℝ) (ht : 0 < t) :
    MemLp (fhi f t) (ENNReal.ofReal p₀) volume := by
  refine memLp_of_pt _ f ((hfm.indicator (measurableSet_lt measurable_const hfm.norm)).aestronglyMeasurable)
    p₀ p (t ^ (p₀ - p)) hp₀ (by linarith) (by positivity) hf fun y => ?_
  by_cases h : t < ‖f y‖
  · simp only [Set.indicator, Set.mem_ofPred_eq, h, if_true]
    have ha : 0 < ‖f y‖ := ht.trans h
    calc ‖f y‖ ^ p₀ = ‖f y‖ ^ (p₀ - p) * ‖f y‖ ^ p := by
          rw [← Real.rpow_add ha]; congr 1; ring
      _ ≤ t ^ (p₀ - p) * ‖f y‖ ^ p := by
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos ht h.le (by linarith : p₀ - p ≤ 0)) (by positivity)
  · simp only [Set.indicator, Set.mem_ofPred_eq, h, if_false, norm_zero,
      Real.zero_rpow hp₀.ne']
    positivity

theorem memLp_flo (f : E n → ℂ) (hfm : Measurable f) (p p₁ : ℝ) (hp : 0 < p) (h12 : p < p₁)
    (hf : MemLp f (ENNReal.ofReal p) volume) (t : ℝ) (ht : 0 < t) :
    MemLp (flo f t) (ENNReal.ofReal p₁) volume := by
  refine memLp_of_pt _ f ((hfm.indicator (measurableSet_le hfm.norm measurable_const)).aestronglyMeasurable)
    p₁ p (t ^ (p₁ - p)) (by linarith) hp (by positivity) hf fun y => ?_
  by_cases h : ‖f y‖ ≤ t
  · simp only [Set.indicator, Set.mem_ofPred_eq, h, if_true]
    calc ‖f y‖ ^ p₁ = ‖f y‖ ^ (p₁ - p) * ‖f y‖ ^ p := by
          rw [← Real.rpow_add' (norm_nonneg _) (by linarith)]; congr 1; ring
      _ ≤ t ^ (p₁ - p) * ‖f y‖ ^ p := by
          gcongr
  · simp only [Set.indicator, Set.mem_ofPred_eq, h, if_false, norm_zero,
      Real.zero_rpow (by linarith : p₁ ≠ 0)]
    positivity

/-! ## Chebyshev at one endpoint -/
theorem cheb (G g : E n → ℂ) (hG : AEStronglyMeasurable G volume) (q : ℝ) (hq : 0 < q) (A : ℝ)
    (hA : 0 ≤ A)
    (hb : eLpNorm G (ENNReal.ofReal q) volume ≤ ENNReal.ofReal A * eLpNorm g (ENNReal.ofReal q) volume)
    (p t : ℝ) (ht : 0 < t) :
    volume {x | ENNReal.ofReal (t / 2) ≤ ‖G x‖ₑ} * ENNReal.ofReal (t ^ (p - 1)) ≤
      ENNReal.ofReal (2 ^ q * A ^ q) * (ENNReal.ofReal (t ^ (p - 1 - q)) * ∫⁻ x, ‖g x‖ₑ ^ q) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  have hcheb := mul_meas_ge_le_pow_eLpNorm' volume hq0 ENNReal.ofReal_ne_top hG
    (ENNReal.ofReal (t / 2))
  rw [ENNReal.toReal_ofReal hq.le] at hcheb
  have hg : eLpNorm g (ENNReal.ofReal q) volume ^ q = ∫⁻ x, ‖g x‖ₑ ^ q := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le,
      ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
  have h1 : eLpNorm G (ENNReal.ofReal q) volume ^ q ≤ ENNReal.ofReal (A ^ q) * ∫⁻ x, ‖g x‖ₑ ^ q := by
    calc _ ≤ (ENNReal.ofReal A * eLpNorm g (ENNReal.ofReal q) volume) ^ q :=
          ENNReal.rpow_le_rpow hb hq.le
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.ofReal_rpow_of_nonneg hA hq.le, hg]
  have hsplit : ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (t / 2) ^ q * ENNReal.ofReal (2 ^ q * t ^ (p - 1 - q)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have htq : t ^ (p - 1) = t ^ q * t ^ (p - 1 - q) := by
      rw [← Real.rpow_add ht]; congr 1; ring
    rw [Real.div_rpow ht.le (by norm_num), htq]
    have : 0 < t ^ q := by positivity
    have : 0 < (2 : ℝ) ^ q := by positivity
    field_simp
  calc _ = ENNReal.ofReal (t / 2) ^ q * volume {x | ENNReal.ofReal (t / 2) ≤ ‖G x‖ₑ} *
        ENNReal.ofReal (2 ^ q * t ^ (p - 1 - q)) := by rw [hsplit]; ring
    _ ≤ (ENNReal.ofReal (A ^ q) * ∫⁻ x, ‖g x‖ₑ ^ q) * ENNReal.ofReal (2 ^ q * t ^ (p - 1 - q)) := by
        exact mul_le_mul_of_nonneg_right (hcheb.trans h1) (zero_le)
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ q),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ q)]
        ring

/-! ## The level-set bound -/
theorem level_bound (p₀ p p₁ : ℝ) (h0 : 1 ≤ p₀) (h01 : p₀ < p) (h12 : p < p₁)
    (k : E n → ℂ) (hk : Integrable k) (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (H0 : ∀ f : E n → ℂ, MemLp f (ENNReal.ofReal p₀) volume →
        eLpNorm (conv k f) (ENNReal.ofReal p₀) volume ≤
          ENNReal.ofReal A₀ * eLpNorm f (ENNReal.ofReal p₀) volume)
    (H1 : ∀ f : E n → ℂ, MemLp f (ENNReal.ofReal p₁) volume →
        eLpNorm (conv k f) (ENNReal.ofReal p₁) volume ≤
          ENNReal.ofReal A₁ * eLpNorm f (ENNReal.ofReal p₁) volume)
    (f : E n → ℂ) (hfm : Measurable f) (hf : MemLp f (ENNReal.ofReal p) volume) (t : ℝ)
    (ht : 0 < t) :
    volume {x | t < ‖conv k f x‖} * ENNReal.ofReal (t ^ (p - 1)) ≤
      ENNReal.ofReal (2 ^ p₀ * A₀ ^ p₀) *
          (ENNReal.ofReal (t ^ (p - 1 - p₀)) * ∫⁻ x, ‖fhi f t x‖ₑ ^ p₀) +
        ENNReal.ofReal (2 ^ p₁ * A₁ ^ p₁) *
          (ENNReal.ofReal (t ^ (p - 1 - p₁)) * ∫⁻ x, ‖flo f t x‖ₑ ^ p₁) := by
  have hp₀ : 0 < p₀ := by linarith
  have hhi := memLp_fhi f hfm p₀ p hp₀ h01 hf t ht
  have hlo := memLp_flo f hfm p p₁ (by linarith) h12 hf t ht
  have Y0 := conv_basic k hk (ENNReal.ofReal p₀) (ENNReal.one_le_ofReal.2 h0) _ hhi.1
  have Y1 := conv_basic k hk (ENNReal.ofReal p₁) (ENNReal.one_le_ofReal.2 (by linarith)) _ hlo.1
  have hae : ∀ᵐ x, conv k f x = conv k (fhi f t) x + conv k (flo f t) x := by
    filter_upwards [Y0.1 hhi, Y1.1 hlo] with x h0' h1'
    rw [conv, conv, conv, ← integral_add h0' h1']
    congr 1; funext y; rw [← mul_add, fhi_add_flo]
  have hsub : volume {x | t < ‖conv k f x‖} ≤
      volume ({x | ENNReal.ofReal (t / 2) ≤ ‖conv k (fhi f t) x‖ₑ} ∪
        {x | ENNReal.ofReal (t / 2) ≤ ‖conv k (flo f t) x‖ₑ}) := by
    refine measure_mono_ae (hae.mono fun x hx hxt => ?_)
    have hxt' : t < ‖conv k f x‖ := hxt
    rw [hx] at hxt'
    have htri := norm_add_le (conv k (fhi f t) x) (conv k (flo f t) x)
    by_cases ha : t / 2 ≤ ‖conv k (fhi f t) x‖
    · refine Or.inl ?_
      show ENNReal.ofReal (t / 2) ≤ ‖conv k (fhi f t) x‖ₑ
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal ha
    · refine Or.inr ?_
      show ENNReal.ofReal (t / 2) ≤ ‖conv k (flo f t) x‖ₑ
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (by linarith)
  calc volume {x | t < ‖conv k f x‖} * ENNReal.ofReal (t ^ (p - 1))
      ≤ (volume {x | ENNReal.ofReal (t / 2) ≤ ‖conv k (fhi f t) x‖ₑ} +
          volume {x | ENNReal.ofReal (t / 2) ≤ ‖conv k (flo f t) x‖ₑ}) *
            ENNReal.ofReal (t ^ (p - 1)) :=
        mul_le_mul_of_nonneg_right (hsub.trans (measure_union_le _ _)) zero_le
    _ ≤ _ := by
        rw [add_mul]
        exact add_le_add (cheb _ _ Y0.2.1 p₀ hp₀ A₀ hA₀ (H0 _ hhi) p t ht)
          (cheb _ _ Y1.2.1 p₁ (by linarith) A₁ hA₁ (H1 _ hlo) p t ht)

/-! ## Tonelli -/
/-- The integrand of the high part as a function of `(t, x)`. -/
noncomputable def Phi0 (f : E n → ℂ) (p p₀ t : ℝ) (x : E n) : ℝ≥0∞ :=
  ENNReal.ofReal (t ^ (p - 1 - p₀)) * (if t < ‖f x‖ then ENNReal.ofReal (‖f x‖ ^ p₀) else 0)

/-- The integrand of the low part as a function of `(t, x)`. -/
noncomputable def Phi1 (f : E n → ℂ) (p p₁ t : ℝ) (x : E n) : ℝ≥0∞ :=
  ENNReal.ofReal (t ^ (p - 1 - p₁)) * (if ‖f x‖ ≤ t then ENNReal.ofReal (‖f x‖ ^ p₁) else 0)

theorem Phi0_meas (f : E n → ℂ) (hfm : Measurable f) (p p₀ : ℝ) :
    Measurable (Function.uncurry (Phi0 f p p₀)) := by
  have hfn : Measurable fun q : ℝ × E n => ‖f q.2‖ := hfm.norm.comp measurable_snd
  exact (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul
    (Measurable.ite (measurableSet_lt measurable_fst hfn)
      (ENNReal.measurable_ofReal.comp (hfn.pow_const _)) measurable_const)

theorem Phi1_meas (f : E n → ℂ) (hfm : Measurable f) (p p₁ : ℝ) :
    Measurable (Function.uncurry (Phi1 f p p₁)) := by
  have hfn : Measurable fun q : ℝ × E n => ‖f q.2‖ := hfm.norm.comp measurable_snd
  exact (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul
    (Measurable.ite (measurableSet_le hfn measurable_fst)
      (ENNReal.measurable_ofReal.comp (hfn.pow_const _)) measurable_const)

theorem tonelli0 (f : E n → ℂ) (hfm : Measurable f) (p p₀ : ℝ) (hp₀ : 0 < p₀) (h01 : p₀ < p) :
    ∫⁻ t in Ioi 0, ∫⁻ x, Phi0 f p p₀ t x =
      ENNReal.ofReal (1 / (p - p₀)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  rw [lintegral_lintegral_swap (Phi0_meas f hfm p p₀).aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1; funext x
  simp only [Phi0]
  rw [inner_hi p p₀ ‖f x‖ hp₀ h01 (norm_nonneg _), ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith),
    ← ENNReal.ofReal_mul (by have := sub_pos.2 h01; positivity), one_div, div_eq_inv_mul]

theorem tonelli1 (f : E n → ℂ) (hfm : Measurable f) (p p₁ : ℝ) (hp : 0 < p) (h12 : p < p₁) :
    ∫⁻ t in Ioi 0, ∫⁻ x, Phi1 f p p₁ t x =
      ENNReal.ofReal (1 / (p₁ - p)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  rw [lintegral_lintegral_swap (Phi1_meas f hfm p p₁).aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1; funext x
  simp only [Phi1]
  rw [inner_lo p p₁ ‖f x‖ hp h12 (norm_nonneg _), ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
    ← ENNReal.ofReal_mul (by have := sub_pos.2 h12; positivity), one_div, div_eq_inv_mul]

/-! ## The `Lᵖ` integral bound for measurable `f` -/
theorem main_meas (p₀ p p₁ : ℝ) (h0 : 1 ≤ p₀) (h01 : p₀ < p) (h12 : p < p₁)
    (k : E n → ℂ) (hk : Integrable k) (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (H0 : ∀ f : E n → ℂ, MemLp f (ENNReal.ofReal p₀) volume →
        eLpNorm (conv k f) (ENNReal.ofReal p₀) volume ≤
          ENNReal.ofReal A₀ * eLpNorm f (ENNReal.ofReal p₀) volume)
    (H1 : ∀ f : E n → ℂ, MemLp f (ENNReal.ofReal p₁) volume →
        eLpNorm (conv k f) (ENNReal.ofReal p₁) volume ≤
          ENNReal.ofReal A₁ * eLpNorm f (ENNReal.ofReal p₁) volume)
    (f : E n → ℂ) (hfm : Measurable f) (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∫⁻ x, ‖conv k f x‖ₑ ^ p ≤
      ENNReal.ofReal (p * (2 ^ p₀ * A₀ ^ p₀ / (p - p₀) + 2 ^ p₁ * A₁ ^ p₁ / (p₁ - p))) *
        ∫⁻ x, ‖f x‖ₑ ^ p := by
  have hp₀ : 0 < p₀ := by linarith
  have hp : 0 < p := by linarith
  have hFm := (conv_basic k hk (ENNReal.ofReal p) (ENNReal.one_le_ofReal.2 (by linarith)) f hf.1).2.1
  have e0 : ∀ t, ENNReal.ofReal (t ^ (p - 1 - p₀)) * ∫⁻ x, ‖fhi f t x‖ₑ ^ p₀ =
      ∫⁻ x, Phi0 f p p₀ t x := by
    intro t
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext x; rw [enorm_fhi f t p₀ hp₀, Phi0]
  have e1 : ∀ t, ENNReal.ofReal (t ^ (p - 1 - p₁)) * ∫⁻ x, ‖flo f t x‖ₑ ^ p₁ =
      ∫⁻ x, Phi1 f p p₁ t x := by
    intro t
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext x; rw [enorm_flo f t p₁ (by linarith), Phi1]
  have hlhs : ∫⁻ x, ‖conv k f x‖ₑ ^ p = ∫⁻ x, ENNReal.ofReal (‖conv k f x‖ ^ p) := by
    congr 1; funext x; rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  have hm0 := (Phi0_meas f hfm p p₀).lintegral_prod_right (ν := volume)
  have hm1 := (Phi1_meas f hfm p p₁).lintegral_prod_right (ν := volume)
  have hX : 0 ≤ 2 ^ p₀ * A₀ ^ p₀ / (p - p₀) := by have := sub_pos.2 h01; positivity
  have hY : 0 ≤ 2 ^ p₁ * A₁ ^ p₁ / (p₁ - p) := by have := sub_pos.2 h12; positivity
  rw [hlhs, lintegral_rpow_eq_lintegral_meas_lt_mul volume (ae_of_all _ fun x => norm_nonneg _)
    hFm.norm.aemeasurable hp]
  calc ENNReal.ofReal p * ∫⁻ t in Ioi 0, volume {a | t < ‖conv k f a‖} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal p * ∫⁻ t in Ioi 0, ((ENNReal.ofReal (2 ^ p₀ * A₀ ^ p₀) * ∫⁻ x, Phi0 f p p₀ t x) +
          ENNReal.ofReal (2 ^ p₁ * A₁ ^ p₁) * ∫⁻ x, Phi1 f p p₁ t x) := by
        refine mul_le_mul_of_nonneg_left (lintegral_mono_ae
          ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => ?_))) zero_le
        have hl := level_bound p₀ p p₁ h0 h01 h12 k hk A₀ A₁ hA₀ hA₁ H0 H1 f hfm hf t ht
        rw [e0 t, e1 t] at hl
        exact hl
    _ = ENNReal.ofReal p * (ENNReal.ofReal (2 ^ p₀ * A₀ ^ p₀) *
          (ENNReal.ofReal (1 / (p - p₀)) * ∫⁻ x, ‖f x‖ₑ ^ p) +
          ENNReal.ofReal (2 ^ p₁ * A₁ ^ p₁) * (ENNReal.ofReal (1 / (p₁ - p)) * ∫⁻ x, ‖f x‖ₑ ^ p)) := by
        have hadd := lintegral_add_left (μ := volume.restrict (Ioi 0))
          (hm0.const_mul (ENNReal.ofReal (2 ^ p₀ * A₀ ^ p₀)))
          (fun t => ENNReal.ofReal (2 ^ p₁ * A₁ ^ p₁) * ∫⁻ x, Phi1 f p p₁ t x)
        rw [hadd, lintegral_const_mul _ hm0,
          lintegral_const_mul _ hm1, tonelli0 f hfm p p₀ hp₀ h01, tonelli1 f hfm p p₁ hp h12]
    _ = _ := by
        rw [ENNReal.ofReal_mul hp.le, ENNReal.ofReal_add hX hY,
          div_eq_mul_one_div (2 ^ p₀ * A₀ ^ p₀), div_eq_mul_one_div (2 ^ p₁ * A₁ ^ p₁),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ p₀ * A₀ ^ p₀),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ p₁ * A₁ ^ p₁)]
        ring

/-- **I.** `‖k * f‖_p^p ≤ C^p (A₀^{p₀} + A₁^{p₁}) ‖f‖_p^p` for `p₀ < p < p₁` (split `f` at height
`α`, Chebyshev at each endpoint, Tonelli). -/
theorem interp_bound (p₀ p p₁ : ℝ) (h0 : 1 ≤ p₀) (h01 : p₀ < p) (h12 : p < p₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (k : E n → ℂ), Integrable k → ∀ A₀ A₁ : ℝ, 0 ≤ A₀ → 0 ≤ A₁ →
      (∀ f : E n → ℂ, MemLp f (ENNReal.ofReal p₀) volume →
        eLpNorm (conv k f) (ENNReal.ofReal p₀) volume ≤
          ENNReal.ofReal A₀ * eLpNorm f (ENNReal.ofReal p₀) volume) →
      (∀ f : E n → ℂ, MemLp f (ENNReal.ofReal p₁) volume →
        eLpNorm (conv k f) (ENNReal.ofReal p₁) volume ≤
          ENNReal.ofReal A₁ * eLpNorm f (ENNReal.ofReal p₁) volume) →
      ∀ f : E n → ℂ, MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (conv k f) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * (A₀ ^ p₀ + A₁ ^ p₁) ^ (1 / p)) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp : 0 < p := by linarith
  have ha : 0 ≤ 2 ^ p₀ / (p - p₀) := by have := sub_pos.2 h01; positivity
  have hb : 0 ≤ 2 ^ p₁ / (p₁ - p) := by have := sub_pos.2 h12; positivity
  have hD0 : 0 ≤ p * (2 ^ p₀ / (p - p₀) + 2 ^ p₁ / (p₁ - p)) := by positivity
  refine ⟨(p * (2 ^ p₀ / (p - p₀) + 2 ^ p₁ / (p₁ - p))) ^ (1 / p), by positivity, ?_⟩
  intro n k hk A₀ A₁ hA₀ hA₁ H0 H1 f hf
  obtain ⟨g, hgm, hfg⟩ : ∃ g : E n → ℂ, Measurable g ∧ f =ᵐ[volume] g :=
    ⟨_, hf.1.stronglyMeasurable_mk.measurable, hf.1.ae_eq_mk⟩
  have hg : MemLp g (ENNReal.ofReal p) volume := hf.ae_eq hfg
  have hconv : conv k f = conv k g := by
    funext x; unfold conv
    exact integral_congr_ae (by filter_upwards [hfg] with y hy; rw [hy])
  rw [hconv, eLpNorm_congr_ae hfg]
  have hmain := main_meas p₀ p p₁ h0 h01 h12 k hk A₀ A₁ hA₀ hA₁ H0 H1 _ hgm hg
  have hX : 0 ≤ A₀ ^ p₀ := by positivity
  have hY : 0 ≤ A₁ ^ p₁ := by positivity
  have hle : p * (2 ^ p₀ * A₀ ^ p₀ / (p - p₀) + 2 ^ p₁ * A₁ ^ p₁ / (p₁ - p)) ≤
      p * (2 ^ p₀ / (p - p₀) + 2 ^ p₁ / (p₁ - p)) * (A₀ ^ p₀ + A₁ ^ p₁) := by
    have e : p * (2 ^ p₀ * A₀ ^ p₀ / (p - p₀) + 2 ^ p₁ * A₁ ^ p₁ / (p₁ - p)) =
        p * (2 ^ p₀ / (p - p₀) * A₀ ^ p₀ + 2 ^ p₁ / (p₁ - p) * A₁ ^ p₁) := by ring
    rw [e, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hp.le
    nlinarith [mul_nonneg ha hY, mul_nonneg hb hX]
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  calc (∫⁻ x, ‖conv k g x‖ₑ ^ p) ^ (1 / p)
      ≤ (ENNReal.ofReal (p * (2 ^ p₀ / (p - p₀) + 2 ^ p₁ / (p₁ - p)) * (A₀ ^ p₀ + A₁ ^ p₁)) *
          ∫⁻ x, ‖g x‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (hmain.trans (mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal hle) zero_le)) (by positivity)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), Real.mul_rpow hD0 (by positivity)]

end TaoBR.Carb.PartI
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
/-! ## Part I: interpolation (layer cake, strong-type endpoints) -/
alias interp_bound := TaoBR.Carb.PartI.interp_bound

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartF1
open TaoBR.Carb Filter
open scoped Topology
variable {m : ℕ}
/-! # Part F1: `restr_ball` -/
/-! ## Coordinates -/
@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

end TaoBR.Carb.PartF1
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartF2
variable {m : ℕ}
/-! # Part F2: `frozen_eq` -/
@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

end TaoBR.Carb.PartF2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartN
open TaoBR.Carb
variable {m : ℕ}
/-! # Part N: `near_bound` -/
/-! ## Coordinates (copied from `proofs/pbr/PartK.lean`) -/
@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

end TaoBR.Carb.PartN
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartS
open Filter Topology
variable {m : ℕ}
theorem norm_sq_hv (y : E (m + 1)) : ‖y‖ ^ 2 = ‖horiz y‖ ^ 2 + vert y ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [vert]

theorem continuous_horiz : Continuous (horiz : E (m + 1) → E m) := by
  unfold horiz; fun_prop

theorem continuous_vert : Continuous (vert : E (m + 1) → ℝ) := by
  unfold vert; fun_prop

end TaoBR.Carb.PartS
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartS
open Filter Topology
theorem integrable_gauss (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun z : E n => Real.exp (-c * ‖z‖ ^ 2)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := (c : ℂ)) (by rw [Complex.ofReal_re]; exact hc) 0 (0 : E n)).re
  refine this.congr (ae_of_all _ fun u => ?_)
  simp only [zero_mul, add_zero]
  rw [show (-(c : ℂ) * (‖u‖ : ℂ) ^ 2) = ((-c * ‖u‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_exp]; exact Complex.ofReal_re _

theorem kb_pointwise (m : ℕ) (b : ℝ → ℂ) (M L : ℝ)
    (hbM : ∀ t, ‖b t‖ ≤ M) (hbs : ∀ t, b t ≠ 0 → |t| ≤ L) (z : E (m + 1)) :
    ‖kb m b z‖ ≤ M * Real.exp (Real.pi / (1 + L ^ 2) * L ^ 2) *
      Real.exp (-(Real.pi / (1 + L ^ 2)) * ‖z‖ ^ 2) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbM 0)
  by_cases h0 : b (vert z) = 0
  · rw [kb, h0, zero_mul, norm_zero]; positivity
  have hL := hbs _ h0
  set t := vert z
  set D := ‖horiz z‖
  have ht2 : t ^ 2 ≤ L ^ 2 := sq_le_sq' (abs_le.1 hL).1 (abs_le.1 hL).2
  rw [kb, norm_mul, mul_assoc]
  refine mul_le_mul (hbM _) ?_ (norm_nonneg _) hM
  refine (Eg_norm m _ _).trans ?_
  have h1 : (1 + t ^ 2) ^ (-((m : ℝ) / 4)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
  rw [← Real.exp_add]
  refine (mul_le_of_le_one_left (Real.exp_pos _).le h1).trans (Real.exp_le_exp.2 ?_)
  rw [norm_sq_hv z]
  have hD : 0 ≤ D ^ 2 := sq_nonneg _
  have hc : Real.pi * D ^ 2 / (1 + L ^ 2) ≤ Real.pi * D ^ 2 / (1 + t ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hc2 : Real.pi / (1 + L ^ 2) * t ^ 2 ≤ Real.pi / (1 + L ^ 2) * L ^ 2 :=
    mul_le_mul_of_nonneg_left ht2 (by positivity)
  have : Real.pi * D ^ 2 / (1 + L ^ 2) = Real.pi / (1 + L ^ 2) * D ^ 2 := by ring
  nlinarith

/-- **S8.** A bounded measurable `b` with bounded support gives an integrable kernel. -/
theorem kb_integrable (m : ℕ) (b : ℝ → ℂ) (hb : Measurable b) (M L : ℝ)
    (hbM : ∀ t, ‖b t‖ ≤ M) (hbs : ∀ t, b t ≠ 0 → |t| ≤ L) : Integrable (kb m b) := by
  have hmeas : AEStronglyMeasurable (kb m b) volume := by
    refine (Measurable.mul (hb.comp continuous_vert.measurable)
      ((Eg_continuous m).measurable.comp
        (continuous_horiz.prodMk continuous_vert).measurable)).aestronglyMeasurable
  refine Integrable.mono' (((integrable_gauss (m + 1) (c := Real.pi / (1 + L ^ 2))
    (by positivity)).const_mul (M * Real.exp (Real.pi / (1 + L ^ 2) * L ^ 2)))) hmeas
    (ae_of_all _ fun z => ?_)
  exact kb_pointwise m b M L hbM hbs z

end TaoBR.Carb.PartS
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
alias kb_integrable := TaoBR.Carb.PartS.kb_integrable

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartN
open TaoBR.Carb
variable {m : ℕ}
theorem norm_sq_hv (y : E (m + 1)) : ‖y‖ ^ 2 = ‖horiz y‖ ^ 2 + vert y ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [vert]

theorem norm_le_horiz_add_vert (y : E (m + 1)) : ‖y‖ ≤ ‖horiz y‖ + |vert y| := by
  have := norm_sq_hv y
  have h : ‖y‖ ^ 2 ≤ (‖horiz y‖ + |vert y|) ^ 2 := by
    rw [this]; nlinarith [norm_nonneg (horiz y), abs_nonneg (vert y), sq_abs (vert y)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

theorem horiz_continuous : Continuous (fun ξ : E (m + 1) => horiz ξ) := by
  have h : Continuous (fun ξ : E (m + 1) => fun i : Fin m => ξ (Fin.castSucc i)) :=
    continuous_pi fun i => (EuclideanSpace.proj (𝕜 := ℝ) (Fin.castSucc i)).continuous
  exact (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp h

theorem vert_continuous : Continuous (fun ξ : E (m + 1) => vert ξ) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous

@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

end TaoBR.Carb.PartN
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartK
variable {m : ℕ}
@[simp] theorem horiz_mkPoint (u : E m) (t : ℝ) : horiz (mkPoint u t) = u := by
  ext i; simp [horiz]

end TaoBR.Carb.PartK
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartN
open TaoBR.Carb
variable {m : ℕ}
@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

end TaoBR.Carb.PartN
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartK
variable {m : ℕ}
@[simp] theorem vert_mkPoint (u : E m) (t : ℝ) : vert (mkPoint u t) = t := by
  simp [vert]

theorem ext_hv {y y' : E (m + 1)} (h1 : horiz y = horiz y') (h2 : vert y = vert y') : y = y' := by
  ext i
  induction i using Fin.lastCases with
  | last => exact h2
  | cast j => have := congrArg (fun z : E m => z j) h1; simpa [horiz] using this

end TaoBR.Carb.PartK
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartF2
variable {m : ℕ}
@[simp] theorem vert_mkPoint (u : E m) (t : ℝ) : vert (mkPoint u t) = t := by
  simp [vert]

@[simp] theorem horiz_mkPoint (u : E m) (t : ℝ) : horiz (mkPoint u t) = u := by
  ext i; simp [horiz]

@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

theorem ext_hv {y y' : E (m + 1)} (h1 : horiz y = horiz y') (h2 : vert y = vert y') : y = y' := by
  ext i
  induction i using Fin.lastCases with
  | last => exact h2
  | cast j => have := congrArg (fun z : E m => z j) h1; simpa using this

end TaoBR.Carb.PartF2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartN
open TaoBR.Carb
variable {m : ℕ}
@[simp] theorem horiz_mkPoint (u : E m) (t : ℝ) : horiz (mkPoint u t) = u := by
  ext i; simp

end TaoBR.Carb.PartN
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartF1
open TaoBR.Carb Filter
open scoped Topology
variable {m : ℕ}
@[simp] theorem horiz_mkPoint (u : E m) (t : ℝ) : horiz (mkPoint u t) = u := by
  ext i; simp

@[simp] theorem vert_mkPoint (u : E m) (t : ℝ) : vert (mkPoint u t) = t := by
  simp [vert]

end TaoBR.Carb.PartF1
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartN
open TaoBR.Carb
variable {m : ℕ}
@[simp] theorem vert_mkPoint (u : E m) (t : ℝ) : vert (mkPoint u t) = t := by
  simp [vert]

theorem ext_hv {y y' : E (m + 1)} (h1 : horiz y = horiz y') (h2 : vert y = vert y') : y = y' := by
  ext i
  induction i using Fin.lastCases with
  | last => exact h2
  | cast j => have := congrArg (fun z : E m => z j) h1; simpa using this

theorem mkPoint_horiz_vert (y : E (m + 1)) : mkPoint (horiz y) (vert y) = y :=
  ext_hv (by simp) (by simp)

theorem continuous_mkPoint : Continuous fun q : E m × ℝ => mkPoint q.1 q.2 := by
  unfold mkPoint
  apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  induction i using Fin.lastCases with
  | last => simp; fun_prop
  | cast j => simp; fun_prop

theorem measurePreserving_mkPoint (m : ℕ) :
    MeasurePreserving (fun q : E m × ℝ => mkPoint q.1 q.2) (volume.prod volume) volume := by
  have h1 : MeasurePreserving (Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ))
      ((volume : Measure (E m)).prod (volume : Measure ℝ)) (volume.prod volume) :=
    (PiLp.volume_preserving_ofLp (Fin m)).prod (MeasurePreserving.id volume)
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin m → ℝ)))
    (ν := (volume : Measure ℝ)))
  have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
  have h4 := PiLp.volume_preserving_toLp (Fin (m + 1))
  have h := h4.comp (h3.comp (h2.comp h1))
  have heq : (fun q : E m × ℝ => mkPoint q.1 q.2) = (WithLp.toLp 2 ∘
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm ∘
        Prod.swap ∘ Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ)) := by
    funext q
    apply ext_hv
    · ext i; simp [Function.comp]
    · simp [vert, Function.comp]
  rw [heq]; exact h

/-! ## Small facts -/
theorem horiz_sub (x y : E (m + 1)) : horiz (x - y) = horiz x - horiz y := by
  ext i; simp

theorem vert_sub (x y : E (m + 1)) : vert (x - y) = vert x - vert y := by
  simp [vert]

theorem norm_ex (t : ℝ) : ‖ex t‖ = 1 := by
  unfold ex
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_fourier_of_integrable {n : ℕ} {H : E n → ℂ} (hH : Integrable H) :
    Continuous (𝓕 H) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simpa using continuous_inner) hH

/-- The Gaussian `e^{-π|ξ|²}` has integral `1`. -/
theorem integral_gauss (m : ℕ) : ∫ ξ : E m, Real.exp (-(Real.pi * ‖ξ‖ ^ 2)) = 1 := by
  have := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E m) Real.pi_pos
  simp only [neg_mul] at this
  rw [this, div_self Real.pi_ne_zero, Real.one_rpow]

theorem integrable_gauss (m : ℕ) : Integrable (fun ξ : E m => Real.exp (-(Real.pi * ‖ξ‖ ^ 2))) :=
  Integrable.of_integral_ne_zero (by rw [integral_gauss]; exact one_ne_zero)

theorem lintegral_gauss (m : ℕ) :
    ∫⁻ ξ : E m, ENNReal.ofReal (Real.exp (-(Real.pi * ‖ξ‖ ^ 2))) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gauss m)
    (ae_of_all _ fun _ => (Real.exp_pos _).le), integral_gauss, ENNReal.ofReal_one]

/-- Jensen for a probability density `g`. -/
theorem jensen {α : Type*} [MeasurableSpace α] (μ : Measure α) {g F : α → ℝ≥0∞}
    (hg : Measurable g) (hF : Measurable F) (hg1 : ∫⁻ a, g a ∂μ = 1) (p : ℝ) (hp : 1 ≤ p) :
    (∫⁻ a, g a * F a ∂μ) ^ p ≤ ∫⁻ a, g a * F a ^ p ∂μ := by
  have e1 := lintegral_withDensity_eq_lintegral_mul μ hg hF
  have e2 := lintegral_withDensity_eq_lintegral_mul μ hg (hF.pow_const p)
  simp only [Pi.mul_apply] at e1 e2
  rw [← e1, ← e2]
  have : IsProbabilityMeasure (μ.withDensity g) := ⟨by simp [withDensity_apply, hg1]⟩
  rcases hp.eq_or_lt with rfl | hp1
  · simp
  have hpq := Real.HolderConjugate.conjExponent hp1
  have := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.withDensity g) hpq hF.aemeasurable
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at this
  have hp0 : 0 < p := by linarith
  calc (∫⁻ a, F a ∂μ.withDensity g) ^ p
      ≤ ((∫⁻ a, F a ^ p ∂μ.withDensity g) ^ (1 / p)) ^ p := by
        simpa using ENNReal.rpow_le_rpow this hp0.le
    _ = ∫⁻ a, F a ^ p ∂μ.withDensity g := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]

/-- The `x̲`-slab integral is bounded by the iterated integral (no measurability needed). -/
theorem lintegral_slab_le (c : E m) (L : ℝ) (F : E (m + 1) → ℝ≥0∞) :
    ∫⁻ x in {x : E (m + 1) | horiz x ∈ ball c L}, F x ≤
      ∫⁻ xn : ℝ, ∫⁻ u in ball c L, F (mkPoint u xn) := by
  have hmeasS : MeasurableSet {x : E (m + 1) | horiz x ∈ ball c L} :=
    measurableSet_ball.preimage horiz_continuous.measurable
  have hmp : MeasurePreserving (fun q : ℝ × E m => mkPoint q.2 q.1) (volume.prod volume) volume :=
    (measurePreserving_mkPoint m).comp (Measure.measurePreserving_swap)
  have hemb : MeasurableEmbedding (fun q : ℝ × E m => mkPoint q.2 q.1) := by
    refine MeasurableEmbedding.of_measurable_inverse hmp.measurable ?_
      (g := fun x => (vert x, horiz x)) ?_ ?_
    · have : range (fun q : ℝ × E m => mkPoint q.2 q.1) = univ :=
        eq_univ_of_forall fun x => ⟨(vert x, horiz x), mkPoint_horiz_vert x⟩
      rw [this]; exact MeasurableSet.univ
    · exact (vert_continuous.prodMk horiz_continuous).measurable
    · intro q; simp
  rw [← lintegral_indicator hmeasS, ← hmp.lintegral_comp_emb hemb]
  refine (lintegral_prod_le _).trans (le_of_eq ?_)
  refine lintegral_congr fun xn => ?_
  rw [← lintegral_indicator measurableSet_ball]
  refine lintegral_congr fun u => ?_
  by_cases hu : u ∈ ball c L
  · rw [indicator_of_mem (show mkPoint u xn ∈ {x : E (m + 1) | horiz x ∈ ball c L} by simpa using hu),
      indicator_of_mem hu]
  · rw [indicator_of_notMem
      (show mkPoint u xn ∉ {x : E (m + 1) | horiz x ∈ ball c L} by simpa using hu),
      indicator_of_notMem hu]

/-- Translation of a ball integral. -/
theorem lintegral_ball_sub (c ξ : E m) (L : ℝ) (F : E m → ℝ≥0∞) :
    ∫⁻ u in ball c L, F (u - ξ) = ∫⁻ u in ball (c - ξ) L, F u := by
  have hpre : (fun u => u - ξ) ⁻¹' ball (c - ξ) L = ball c L := by
    ext u; simp
  rw [← hpre]
  exact (measurePreserving_sub_right volume ξ).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.subRight ξ).measurableEmbedding F _

end TaoBR.Carb.PartN
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartP
open Filter
variable {m : ℕ}
@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

@[simp] theorem vert_mkPoint (u : E m) (t : ℝ) : vert (mkPoint u t) = t := by
  simp [vert]

@[simp] theorem horiz_mkPoint (u : E m) (t : ℝ) : horiz (mkPoint u t) = u := by
  ext i; simp [horiz]

@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

theorem ext_hv {y y' : E (m + 1)} (h1 : horiz y = horiz y') (h2 : vert y = vert y') : y = y' := by
  ext i
  induction i using Fin.lastCases with
  | last => exact h2
  | cast j => have := congrArg (fun z : E m => z j) h1; simpa using this

@[simp] theorem mkPoint_horiz_vert (y : E (m + 1)) : mkPoint (horiz y) (vert y) = y :=
  ext_hv (by simp) (by simp)

end TaoBR.Carb.PartP
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartK
variable {m : ℕ}
theorem mkPoint_horiz_vert (y : E (m + 1)) : mkPoint (horiz y) (vert y) = y :=
  ext_hv (by simp) (by simp)

theorem inner_mkPoint (u u' : E m) (t t' : ℝ) :
    ⟪mkPoint u t, mkPoint u' t'⟫ = ⟪u, u'⟫ + t * t' := by
  simp only [PiLp.inner_apply, Fin.sum_univ_castSucc, mkPoint_castSucc, mkPoint_last]
  simp [mul_comm]

theorem measurePreserving_mkPoint (m : ℕ) :
    MeasurePreserving (fun q : E m × ℝ => mkPoint q.1 q.2) (volume.prod volume) volume := by
  have h1 : MeasurePreserving (Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ))
      ((volume : Measure (E m)).prod (volume : Measure ℝ)) (volume.prod volume) :=
    (PiLp.volume_preserving_ofLp (Fin m)).prod (MeasurePreserving.id volume)
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin m → ℝ)))
    (ν := (volume : Measure ℝ)))
  have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
  have h4 := PiLp.volume_preserving_toLp (Fin (m + 1))
  have h := h4.comp (h3.comp (h2.comp h1))
  have heq : (fun q : E m × ℝ => mkPoint q.1 q.2) = (WithLp.toLp 2 ∘
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm ∘
        Prod.swap ∘ Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ)) := by
    funext q
    apply ext_hv
    · ext i; simp [Function.comp, horiz]
    · simp [vert, Function.comp]
  rw [heq]; exact h

/-- The shear `(v, s) ↦ mkPoint v (s + |v|²/2)` is measure preserving. -/
theorem measurePreserving_shear (m : ℕ) :
    MeasurePreserving (fun q : E m × ℝ => mkPoint q.1 (q.2 + ‖q.1‖ ^ 2 / 2))
      (volume.prod volume) volume := by
  have hs : MeasurePreserving (fun q : E m × ℝ => (q.1, q.2 + ‖q.1‖ ^ 2 / 2))
      ((volume : Measure (E m)).prod (volume : Measure ℝ)) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure (E m))).skew_product
      (g := fun (v : E m) (s : ℝ) => s + ‖v‖ ^ 2 / 2) (by fun_prop) ?_
    exact ae_of_all _ fun v => map_add_right_eq_self _ _
  exact (measurePreserving_mkPoint m).comp hs

theorem horiz_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : E (m + 1) => horiz ξ) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : E (m + 1) => fun i : Fin m => ξ (Fin.castSucc i)) :=
    contDiff_pi.2 fun i => (EuclideanSpace.proj (𝕜 := ℝ) (Fin.castSucc i)).contDiff
  exact (EuclideanSpace.equiv (Fin m) ℝ).symm.contDiff.comp h

theorem vert_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : E (m + 1) => vert ξ) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).contDiff

lemma plusPow_measurable (δ : ℝ) : Measurable (fun t : ℝ => plusPow δ t) := by
  unfold plusPow
  exact Measurable.ite measurableSet_Ioi (measurable_id.pow_const δ) measurable_const

/-! ## The symbol `σ` -/
/-- `σ(ξ) = e^{-2πξₙ} (ξₙ - |ξ̲|²/2)₊^δ`. -/
noncomputable def sig (δ : ℝ) (ξ : E (m + 1)) : ℂ :=
  ((Real.exp (-(2 * Real.pi * vert ξ)) * plusPow δ (vert ξ - ‖horiz ξ‖ ^ 2 / 2) : ℝ) : ℂ)

lemma sig_measurable (δ : ℝ) : Measurable (sig (m := m) δ) := by
  unfold sig
  have h2 : Measurable (fun ξ : E (m + 1) => plusPow δ (vert ξ - ‖horiz ξ‖ ^ 2 / 2)) :=
    (plusPow_measurable δ).comp (horiz_contDiff.continuous.measurable |> fun h =>
      (vert_contDiff.continuous.measurable).sub ((h.norm.pow_const 2).div_const 2))
  have h1 : Measurable (fun ξ : E (m + 1) => Real.exp (-(2 * Real.pi * vert ξ))) :=
    (Real.continuous_exp.comp (by have := vert_contDiff (m := m).continuous; fun_prop)).measurable
  exact Complex.measurable_ofReal.comp (h1.mul h2)

lemma sig_shear (δ : ℝ) (v : E m) (s : ℝ) :
    sig δ (mkPoint v (s + ‖v‖ ^ 2 / 2)) =
      ((Real.exp (-(Real.pi * ‖v‖ ^ 2)) : ℝ) : ℂ) *
        ((Real.exp (-(2 * Real.pi * s)) * plusPow δ s : ℝ) : ℂ) := by
  have hs : s + ‖v‖ ^ 2 / 2 - ‖v‖ ^ 2 / 2 = s := by ring
  simp only [sig, horiz_mkPoint, vert_mkPoint, hs]
  have : Real.exp (-(2 * Real.pi * (s + ‖v‖ ^ 2 / 2))) =
      Real.exp (-(Real.pi * ‖v‖ ^ 2)) * Real.exp (-(2 * Real.pi * s)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; push_cast; ring

lemma gauss_integrable : Integrable (fun v : E m => Real.exp (-(Real.pi * ‖v‖ ^ 2))) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E m) (b := (Real.pi : ℂ))
    (by simp [Real.pi_pos]) 0 0).norm
  refine h.congr (ae_of_all _ fun v => ?_)
  simp only [zero_mul, add_zero]
  rw [Complex.norm_exp, show (-(Real.pi : ℂ)) * ((‖v‖ : ℂ)) ^ 2 =
    ((-(Real.pi * ‖v‖ ^ 2) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

lemma vfac_integrable (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun s : ℝ => Real.exp (-(2 * Real.pi * s)) * plusPow δ s) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := δ) (b := 2 * Real.pi)
    (by linarith) one_pos (by positivity)
  have h' : IntegrableOn (fun s : ℝ => Real.exp (-(2 * Real.pi * s)) * plusPow δ s) (Ioi 0) := by
    refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
    simp only [plusPow, if_pos (show (0 : ℝ) < s from hs), Real.rpow_one]
    ring_nf
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h'
  intro s hs
  by_contra hc
  apply hs
  simp only [mem_Ioi, not_lt] at hc
  simp [plusPow, not_lt.2 hc]

lemma sig_integrable (δ : ℝ) (hδ : 0 < δ) : Integrable (sig (m := m) δ) := by
  have hΦ := measurePreserving_shear m
  rw [← hΦ.integrable_comp (sig_measurable δ).aestronglyMeasurable]
  have h := ((gauss_integrable (m := m)).ofReal (𝕜 := ℂ)).mul_prod ((vfac_integrable δ hδ).ofReal (𝕜 := ℂ))
  refine h.congr (ae_of_all _ fun q => ?_)
  rw [Function.comp_apply, sig_shear]; rfl

/-! ## `𝓕⁻ σ = K` -/
lemma fourierChar_eq_ex (x : ℝ) : ((𝐞 x : Circle) : ℂ) = ex x := by
  rw [Real.fourierChar_apply, ex]; congr 1; push_cast; ring

lemma ex_add (a b : ℝ) : ex (a + b) = ex a * ex b := by
  rw [ex, ex, ex, ← Complex.exp_add]; congr 1; push_cast; ring

lemma integrand_shear (δ : ℝ) (z : E (m + 1)) (v : E m) (s : ℝ) :
    𝐞 ⟪mkPoint v (s + ‖v‖ ^ 2 / 2), z⟫ • sig δ (mkPoint v (s + ‖v‖ ^ 2 / 2)) =
      ((Real.exp (-(Real.pi * ‖v‖ ^ 2)) : ℂ) * ex (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2)) *
        (((Real.exp (-(2 * Real.pi * s)) * plusPow δ s : ℝ) : ℂ) * ex (vert z * s)) := by
  have hz : ⟪mkPoint v (s + ‖v‖ ^ 2 / 2), z⟫ =
      (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2) + vert z * s := by
    conv_lhs => rw [← mkPoint_horiz_vert z]
    rw [inner_mkPoint, real_inner_comm]; ring
  rw [Circle.smul_def, hz, fourierChar_eq_ex, ex_add, smul_eq_mul, sig_shear]
  ring

theorem sig_factor (δ : ℝ) (z : E (m + 1)) : 𝓕⁻ (sig (m := m) δ) z = Kc m δ z := by
  have hΦ := measurePreserving_shear m
  have hgm : Measurable (fun ξ : E (m + 1) => 𝐞 ⟪ξ, z⟫ • sig δ ξ) := by
    have h1 : Measurable (fun ξ : E (m + 1) => ((𝐞 ⟪ξ, z⟫ : Circle) : ℂ)) :=
      (Real.continuous_fourierChar.subtype_val.comp (by fun_prop)).measurable
    simp_rw [Circle.smul_def]
    exact h1.mul (sig_measurable δ)
  rw [Real.fourierInv_eq, ← hΦ.map_eq,
    integral_map hΦ.measurable.aemeasurable (hgm.aestronglyMeasurable)]
  simp_rw [integrand_shear]
  rw [integral_prod_mul (μ := (volume : Measure (E m))) (ν := (volume : Measure ℝ))
    (fun v : E m => (Real.exp (-(Real.pi * ‖v‖ ^ 2)) : ℂ) *
      ex (⟪horiz z, v⟫ + vert z * ‖v‖ ^ 2 / 2))
    (fun s : ℝ => ((Real.exp (-(2 * Real.pi * s)) * plusPow δ s : ℝ) : ℂ) * ex (vert z * s)),
    Kc, kb, Bc, Eg, mul_comm]

/-! ## The multiplier with an integrable symbol is a convolution -/
lemma fourier_bound (f : 𝓢(E (m + 1), ℂ)) (ξ : E (m + 1)) :
    ‖𝓕 (f : E (m + 1) → ℂ) ξ‖ ≤ ∫ y, ‖f y‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext y; rw [Circle.norm_smul]

lemma symb_fourier_integrable (s : E (m + 1) → ℂ) (hs : Integrable s) (f : 𝓢(E (m + 1), ℂ)) :
    Integrable (fun ξ => s ξ * 𝓕 (f : E (m + 1) → ℂ) ξ) := by
  have hc : Continuous (𝓕 (f : E (m + 1) → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).continuous
  exact hs.mul_bdd hc.aestronglyMeasurable (ae_of_all _ (fourier_bound f))

theorem mult_eq_conv (s : E (m + 1) → ℂ) (hs : Integrable s) (hmm : Measurable s)
    (g : 𝓢(E (m + 1), ℂ)) (x : E (m + 1)) :
    multiplier s (g : E (m + 1) → ℂ) x = ∫ y, 𝓕⁻ s (x - y) * g y := by
  have hg : Integrable (g : E (m + 1) → ℂ) volume := g.integrable
  simp only [multiplier, Real.fourierInv_eq', Real.fourier_eq', smul_eq_mul]
  set F : E (m + 1) → E (m + 1) → ℂ := fun ξ y =>
    Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) * s ξ *
      (Complex.exp (↑(-2 * Real.pi * ⟪y, ξ⟫) * Complex.I) * g y) with hF
  have hint : Integrable (Function.uncurry F) ((volume : Measure (E (m + 1))).prod volume) := by
    refine Integrable.mono' (hs.norm.mul_prod hg.norm) ?_ ?_
    · apply Measurable.aestronglyMeasurable
      simp only [hF, Function.uncurry_def]
      have : Measurable (fun p : E (m + 1) × E (m + 1) => (g p.2 : ℂ)) :=
        g.continuous.measurable.comp measurable_snd
      have h2 : Measurable (fun p : E (m + 1) × E (m + 1) => s p.1) :=
        hmm.comp measurable_fst
      fun_prop
    · refine ae_of_all _ fun p => ?_
      simp only [hF, Function.uncurry_def, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_rfl
  have h1 : ∀ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) *
      (s ξ * ∫ y, Complex.exp (↑(-2 * Real.pi * ⟪y, ξ⟫) * Complex.I) * g y) =
      ∫ y, F ξ y := by
    intro ξ
    simp only [hF]
    rw [← integral_const_mul, ← integral_const_mul]; congr 1; funext y; ring
  simp_rw [h1]
  rw [integral_integral_swap hint]
  congr 1; funext y
  rw [← integral_mul_const]
  congr 1; funext ξ
  simp only [hF]
  have : Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) *
      Complex.exp (↑(-2 * Real.pi * ⟪y, ξ⟫) * Complex.I) =
      Complex.exp (↑(2 * Real.pi * ⟪ξ, x - y⟫) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1
    rw [inner_sub_right, real_inner_comm y ξ]; push_cast; ring
  rw [← this]; ring

theorem mult_sig (δ : ℝ) (hδ : 0 < δ) (f : 𝓢(E (m + 1), ℂ)) (z : E (m + 1)) :
    multiplier (sig (m := m) δ) (f : E (m + 1) → ℂ) z = conv (Kc m δ) f z := by
  rw [mult_eq_conv _ (sig_integrable δ hδ) (sig_measurable δ), conv]
  simp_rw [sig_factor]

/-! ## Factoring off a symbol `A = 𝓕 a` -/
theorem mult_comp (A a σ : E (m + 1) → ℂ) (ha : Integrable a) (hac : Continuous a)
    (hA : ∀ ξ, 𝓕 a ξ = A ξ) (hσ : Integrable σ) (hσm : Measurable σ)
    (f : 𝓢(E (m + 1), ℂ)) (x : E (m + 1)) :
    multiplier (fun ξ => A ξ * σ ξ) (f : E (m + 1) → ℂ) x =
      ∫ u, a u * multiplier σ (f : E (m + 1) → ℂ) (x - u) := by
  have hσf := symb_fourier_integrable σ hσ f
  have hFc : Continuous (𝓕 (f : E (m + 1) → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).continuous
  simp only [multiplier, Real.fourierInv_eq', smul_eq_mul]
  set F : E (m + 1) → E (m + 1) → ℂ := fun ξ u =>
    a u * (Complex.exp (↑(2 * Real.pi * ⟪ξ, x - u⟫) * Complex.I) *
      (σ ξ * 𝓕 (f : E (m + 1) → ℂ) ξ)) with hF
  have hint : Integrable (Function.uncurry F) ((volume : Measure (E (m + 1))).prod volume) := by
    refine Integrable.mono' (hσf.norm.mul_prod ha.norm) ?_ ?_
    · apply Measurable.aestronglyMeasurable
      simp only [hF, Function.uncurry_def]
      have h1 : Measurable (fun p : E (m + 1) × E (m + 1) => a p.2) :=
        hac.measurable.comp measurable_snd
      have h2 : Measurable (fun p : E (m + 1) × E (m + 1) => σ p.1) :=
        hσm.comp measurable_fst
      have h3 : Measurable (fun p : E (m + 1) × E (m + 1) => 𝓕 (f : E (m + 1) → ℂ) p.1) :=
        hFc.measurable.comp measurable_fst
      fun_prop
    · refine ae_of_all _ fun p => ?_
      simp only [hF, Function.uncurry_def, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_of_eq (by ring)
  have h1 : ∀ ξ, Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) *
      (A ξ * σ ξ * 𝓕 (f : E (m + 1) → ℂ) ξ) = ∫ u, F ξ u := by
    intro ξ
    rw [← hA ξ, Real.fourier_eq']
    simp only [hF, smul_eq_mul]
    rw [← integral_mul_const, ← integral_mul_const, ← integral_const_mul]
    congr 1; funext u
    have : Complex.exp (↑(2 * Real.pi * ⟪ξ, x⟫) * Complex.I) *
        Complex.exp (↑(-2 * Real.pi * ⟪u, ξ⟫) * Complex.I) =
        Complex.exp (↑(2 * Real.pi * ⟪ξ, x - u⟫) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1
      rw [inner_sub_right, real_inner_comm u ξ]; push_cast; ring
    rw [← this]; ring
  simp_rw [h1]
  rw [integral_integral_swap hint]
  congr 1; funext u
  simp only [hF]
  rw [integral_const_mul]

/-- **K.** -/
theorem kernel_rep (m : ℕ) (η : E (m + 1) → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (δ : ℝ) (hδ : 0 < δ) :
    ∃ a : E (m + 1) → ℂ, Integrable a ∧ ∀ (f : 𝓢(E (m + 1), ℂ)) (x : E (m + 1)),
      parabolicBochnerRiesz η δ (f : E (m + 1) → ℂ) x = conv a (conv (Kc m δ) f) x := by
  set a₀ : E (m + 1) → ℂ := fun ξ => ((η ξ * Real.exp (2 * Real.pi * vert ξ) : ℝ) : ℂ) with ha₀
  have hc0 : HasCompactSupport (fun ξ => η ξ * Real.exp (2 * Real.pi * vert ξ)) :=
    hηc.mul_right
  have hc : HasCompactSupport a₀ := hc0.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ (⊤ : ℕ∞) a₀ :=
    Complex.ofRealCLM.contDiff.comp
      (hη.mul (Real.contDiff_exp.comp (contDiff_const.mul vert_contDiff)))
  set A₀ : 𝓢(E (m + 1), ℂ) := hc.toSchwartzMap hs with hA₀
  set a : E (m + 1) → ℂ := ((𝓕⁻ A₀ : 𝓢(E (m + 1), ℂ)) : E (m + 1) → ℂ) with ha
  have hFa : ∀ ξ, 𝓕 a ξ = a₀ ξ := by
    intro ξ
    have h := congrArg (fun g : 𝓢(E (m + 1), ℂ) => (g : E (m + 1) → ℂ) ξ)
      (FourierInvPair.fourier_fourierInv_eq (F := 𝓢(E (m + 1), ℂ)) A₀)
    simp only [SchwartzMap.fourier_coe] at h
    rw [ha, h, hA₀]; rfl
  refine ⟨a, (𝓕⁻ A₀).integrable, fun f x => ?_⟩
  have hsym : (fun ξ : E (m + 1) =>
      ((η ξ * plusPow δ (vert ξ - ‖horiz ξ‖ ^ 2 / 2) : ℝ) : ℂ)) =
      fun ξ => a₀ ξ * sig δ ξ := by
    funext ξ
    simp only [ha₀, sig]
    have : Real.exp (2 * Real.pi * vert ξ) * Real.exp (-(2 * Real.pi * vert ξ)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [← Complex.ofReal_mul]; congr 1
    calc η ξ * plusPow δ (vert ξ - ‖horiz ξ‖ ^ 2 / 2)
        = η ξ * (Real.exp (2 * Real.pi * vert ξ) * Real.exp (-(2 * Real.pi * vert ξ))) *
          plusPow δ (vert ξ - ‖horiz ξ‖ ^ 2 / 2) := by rw [this, mul_one]
      _ = _ := by ring
  rw [parabolicBochnerRiesz, hsym,
    mult_comp a₀ a (sig δ) (𝓕⁻ A₀).integrable (𝓕⁻ A₀).continuous hFa (sig_integrable δ hδ)
      (sig_measurable δ) f x, conv]
  simp_rw [mult_sig δ hδ f]
  rw [← integral_sub_left_eq_self (fun u => a (x - u) * conv (Kc m δ) f u) volume x]
  simp only [sub_sub_cancel]

end TaoBR.Carb.PartK
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
/-! ## Part K: the kernel -/
alias kernel_rep := TaoBR.Carb.PartK.kernel_rep

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartF1
open TaoBR.Carb Filter
open scoped Topology
variable {m : ℕ}
theorem mkPoint_horiz_vert (ξ : E (m + 1)) : mkPoint (horiz ξ) (vert ξ) = ξ := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [vert]
  | cast j => simp

theorem inner_mkPoint (u u' : E m) (t t' : ℝ) :
    ⟪mkPoint u t, mkPoint u' t'⟫ = ⟪u, u'⟫ + t * t' := by
  simp only [PiLp.inner_apply, Fin.sum_univ_castSucc, mkPoint_castSucc, mkPoint_last]
  simp [mul_comm]

theorem inner_hv (x y : E (m + 1)) : ⟪x, y⟫ = ⟪horiz x, horiz y⟫ + vert x * vert y := by
  conv_lhs => rw [← mkPoint_horiz_vert x, ← mkPoint_horiz_vert y]
  rw [inner_mkPoint]

theorem continuous_mkPoint : Continuous fun q : E m × ℝ => mkPoint q.1 q.2 := by
  unfold mkPoint
  apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  induction i using Fin.lastCases with
  | last => simp; fun_prop
  | cast j => simp; fun_prop

theorem continuous_parab : Continuous fun u : E m => mkPoint u (‖u‖ ^ 2 / 2) :=
  continuous_mkPoint.comp (continuous_id.prodMk (by fun_prop))

theorem enorm_circle (z : Circle) : ‖(z : ℂ)‖ₑ = 1 := by
  rw [← ofReal_norm, Circle.norm_coe, ENNReal.ofReal_one]

end TaoBR.Carb.PartF1
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartF1
open TaoBR.Carb Filter
open scoped Topology
/-! ## Generalities -/
lemma continuous_fourier_of_integrable {n : ℕ} {f : E n → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar
    (by simpa using (continuous_inner : Continuous fun p : E n × E n => ⟪p.1, p.2⟫)) hf

lemma enorm_fourier_sub_le {n : ℕ} {f g : E n → ℂ} (hf : Integrable f) (hg : Integrable g)
    (ξ : E n) :
    ‖𝓕 f ξ - 𝓕 g ξ‖ₑ ≤ ∫⁻ y, ‖f y - g y‖ₑ := by
  simp only [Real.fourier_eq]
  rw [← integral_sub ((Real.fourierIntegral_convergent_iff _).2 hf)
    ((Real.fourierIntegral_convergent_iff _).2 hg)]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1; funext y
  rw [← smul_sub, Circle.smul_def, enorm_smul, ← ofReal_norm (𝐞 _ : ℂ), Circle.norm_coe,
    ENNReal.ofReal_one, one_mul]

lemma eLpNorm_rpow_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ} (hp : 0 < p)
    (f : α → ℂ) : eLpNorm f (ENNReal.ofReal p) μ ^ p = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-! ## Step 1: density -/
/-- Simultaneous `Lᵖ` and `L¹` approximation of a boundedly supported `Lᵖ` function by Schwartz
functions. -/
lemma exists_schwartz_approx {n : ℕ} {q : ℝ} (hq : 1 ≤ q) {H : E n → ℂ}
    (hH : MemLp H (ENNReal.ofReal q) volume) {R : ℝ} (hR : ∀ w, R < ‖w‖ → H w = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓢(E n, ℂ), eLpNorm (fun y => f y - H y) (ENNReal.ofReal q) volume ≤ ENNReal.ofReal ε ∧
      ∫⁻ y, ‖f y - H y‖ₑ ≤ ENNReal.ofReal ε := by
  set R' : ℝ := |R| + 1 with hR'
  have hR'0 : 0 < R' := by positivity
  let θb : ContDiffBump (0 : E n) := ⟨R', R' + 1, hR'0, by linarith⟩
  have hθ1 : ∀ y, H y ≠ 0 → θb y = 1 := by
    intro y hy
    refine θb.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    push Not at h
    have h' : |R| + 1 < ‖y‖ := h
    exact hy (hR y (lt_of_le_of_lt (le_abs_self R) (by linarith)))
  set K₂ : Set (E n) := closedBall (0 : E n) (R' + 1)
  have hK₂m : MeasurableSet K₂ := measurableSet_closedBall
  set V := volume K₂ with hV
  have hVtop : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hq0 : 0 < q := by linarith
  set e : ℝ := 1 - 1 / q
  have he0 : 0 ≤ e := by simp only [e]; rw [sub_nonneg, div_le_one hq0]; exact hq
  set ε₁ : ℝ := ε / (1 + V.toReal ^ e)
  have hε₁ : 0 < ε₁ := div_pos hε (by positivity)
  obtain ⟨g, hgc, hgs, hgε⟩ := hH.exist_eLpNorm_sub_le ENNReal.ofReal_ne_top
    (by rw [ENNReal.one_le_ofReal]; exact hq) hε₁
  set F : E n → ℂ := fun y => (θb y : ℂ) * g y
  have hFs := (Complex.ofRealCLM.contDiff.comp θb.contDiff).mul hgs
  have hFc : HasCompactSupport F := hgc.mul_left
  let f : 𝓢(E n, ℂ) := hFc.toSchwartzMap hFs
  have hfF : ∀ y, f y = F y := fun y => rfl
  have hdiff : ∀ y, f y - H y = (θb y : ℂ) * (g y - H y) := by
    intro y
    rw [hfF]
    by_cases hy : H y = 0
    · simp [F, hy]
    · simp [F, hθ1 y hy]
  have hpt : ∀ y, ‖f y - H y‖ₑ ≤ ‖(H - g) y‖ₑ := by
    intro y
    rw [hdiff, enorm_mul, Pi.sub_apply, ← enorm_neg (H y - g y), neg_sub]
    calc ‖(θb y : ℂ)‖ₑ * ‖g y - H y‖ₑ ≤ 1 * ‖g y - H y‖ₑ := by
          gcongr
          rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg θb.nonneg]
          simpa using θb.le_one
      _ = _ := one_mul _
  have hLq : eLpNorm (fun y => f y - H y) (ENNReal.ofReal q) volume ≤ ENNReal.ofReal ε₁ :=
    (eLpNorm_mono_enorm hpt).trans hgε
  have hsupp : Function.support (fun y => f y - H y) ⊆ K₂ := by
    intro y hy
    rw [Function.mem_support, hdiff] at hy
    have : θb y ≠ 0 := fun h => hy (by simp [h])
    have hy' : y ∈ Function.support θb := this
    rw [θb.support_eq] at hy'
    exact ball_subset_closedBall hy'
  refine ⟨f, hLq.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · exact div_le_self hε.le (le_add_of_nonneg_right (by positivity))
  · have hrest : eLpNorm (fun y => f y - H y) 1 volume =
        eLpNorm (fun y => f y - H y) 1 (volume.restrict K₂) :=
      (eLpNorm_restrict_eq_of_support_subset hsupp).symm
    have hrestq : eLpNorm (fun y => f y - H y) (ENNReal.ofReal q) (volume.restrict K₂) =
        eLpNorm (fun y => f y - H y) (ENNReal.ofReal q) volume :=
      eLpNorm_restrict_eq_of_support_subset hsupp
    have hm : AEStronglyMeasurable (fun y => f y - H y) (volume.restrict K₂) :=
      (f.continuous.aestronglyMeasurable.sub hH.aestronglyMeasurable).restrict
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict K₂) (p := 1)
      (q := ENNReal.ofReal q) (by rw [ENNReal.one_le_ofReal]; exact hq) hm
    rw [← hrest, hrestq, Measure.restrict_apply_univ, ENNReal.toReal_one,
      ENNReal.toReal_ofReal hq0.le, eLpNorm_one_eq_lintegral_enorm] at h1
    refine h1.trans ?_
    calc eLpNorm (fun y => f y - H y) (ENNReal.ofReal q) volume * V ^ (1 / 1 - 1 / q)
        ≤ ENNReal.ofReal ε₁ * ENNReal.ofReal (V.toReal ^ e) := by
          gcongr
          rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg he0,
            ENNReal.ofReal_toReal hVtop]
          simp [e]
      _ = ENNReal.ofReal (ε₁ * V.toReal ^ e) := (ENNReal.ofReal_mul hε₁.le).symm
      _ ≤ ENNReal.ofReal ε := by
          apply ENNReal.ofReal_le_ofReal
          simp only [ε₁]
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [show 0 ≤ V.toReal ^ e by positivity]

/-- **Density.** The restriction estimate for Schwartz functions extends to boundedly supported
`L¹ ∩ Lᵖ` functions. -/
lemma density {m : ℕ} {p : ℝ} (hp : 1 ≤ p) (C₀ : ℝ≥0)
    (hC : ∀ f : 𝓢(E (m + 1), ℂ),
      eLpNorm (paraboloidRestriction (f : E (m + 1) → ℂ)) (ENNReal.ofReal p)
        (volume.restrict (closedBall (0 : E m) 1)) ≤ C₀ * eLpNorm f (ENNReal.ofReal p) volume)
    (H : E (m + 1) → ℂ) (h1 : MemLp H 1 volume) (hpH : MemLp H (ENNReal.ofReal p) volume)
    (hs : ∃ R : ℝ, ∀ w, R < ‖w‖ → H w = 0) :
    ∫⁻ u in closedBall (0 : E m) 1, ‖𝓕 H (mkPoint u (‖u‖ ^ 2 / 2))‖ₑ ^ p ≤
      (C₀ : ℝ≥0∞) ^ p * ∫⁻ w, ‖H w‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have h1p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by rw [ENNReal.one_le_ofReal]; exact hp
  have hint : Integrable H := memLp_one_iff_integrable.mp h1
  obtain ⟨R, hR⟩ := hs
  have hε : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  choose φ hφp hφ1 using fun k : ℕ => exists_schwartz_approx hp hpH hR (hε k)
  have hlim : ∀ u : E m, Tendsto (fun k => 𝓕 (φ k : E (m + 1) → ℂ) (mkPoint u (‖u‖ ^ 2 / 2)))
      atTop (𝓝 (𝓕 H (mkPoint u (‖u‖ ^ 2 / 2)))) := by
    intro u
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h := (enorm_fourier_sub_le (φ k).integrable hint (mkPoint u (‖u‖ ^ 2 / 2))).trans (hφ1 k)
    rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (hε k).le] at h
    exact h
  have hmeas : ∀ k, AEStronglyMeasurable
      (fun u : E m => 𝓕 (φ k : E (m + 1) → ℂ) (mkPoint u (‖u‖ ^ 2 / 2)))
      (volume.restrict (closedBall (0 : E m) 1)) := fun k =>
    ((continuous_fourier_of_integrable (φ k).integrable).comp continuous_parab).aestronglyMeasurable
  have hLim := MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (μ := volume.restrict (closedBall (0 : E m) 1)) hmeas _ (ae_of_all _ hlim)
  have hbd : ∀ k : ℕ, eLpNorm (fun u : E m => 𝓕 (φ k : E (m + 1) → ℂ) (mkPoint u (‖u‖ ^ 2 / 2)))
      (ENNReal.ofReal p) (volume.restrict (closedBall (0 : E m) 1)) ≤
      C₀ * (eLpNorm H (ENNReal.ofReal p) volume + ENNReal.ofReal (1 / ((k : ℝ) + 1))) := by
    intro k
    refine (hC (φ k)).trans ?_
    gcongr
    have : (φ k : E (m + 1) → ℂ) = H + fun y => φ k y - H y := by funext y; simp
    rw [this]
    exact (eLpNorm_add_le hpH.aestronglyMeasurable
      ((φ k).continuous.aestronglyMeasurable.sub hpH.aestronglyMeasurable) h1p).trans
      (add_le_add le_rfl (hφp k))
  have htend : Tendsto (fun k : ℕ => (C₀ : ℝ≥0∞) *
      (eLpNorm H (ENNReal.ofReal p) volume + ENNReal.ofReal (1 / ((k : ℝ) + 1)))) atTop
      (𝓝 ((C₀ : ℝ≥0∞) * eLpNorm H (ENNReal.ofReal p) volume)) := by
    have h0 : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat)
      simpa using this
    have := ENNReal.Tendsto.const_mul (a := (C₀ : ℝ≥0∞)) ((tendsto_const_nhds (x := eLpNorm H (ENNReal.ofReal p) volume)).add h0)
      (Or.inr ENNReal.coe_ne_top)
    simpa using this
  have hE : eLpNorm (fun u : E m => 𝓕 H (mkPoint u (‖u‖ ^ 2 / 2))) (ENNReal.ofReal p)
      (volume.restrict (closedBall (0 : E m) 1)) ≤ C₀ * eLpNorm H (ENNReal.ofReal p) volume := by
    refine hLim.trans ?_
    rw [← htend.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall hbd)
  have := ENNReal.rpow_le_rpow hE hp0.le
  rwa [eLpNorm_rpow_eq hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, eLpNorm_rpow_eq hp0] at this

/-! ## Step 2: Galilean transformation and parabolic scaling -/
/-- The diagonal part of the inverse transpose. -/
noncomputable def dv (m : ℕ) (L : ℝ) : Fin (m + 1) → ℝ := Fin.snoc (fun _ => L⁻¹) (L⁻¹ ^ 2)

/-- The last column (off the diagonal). -/
noncomputable def wv {m : ℕ} (L : ℝ) (c : E m) : Fin (m + 1) → ℝ :=
  Fin.snoc (fun i => -(L⁻¹ ^ 2 * c i)) 0

/-- The matrix of `B(y) = (y̲/L - (yₙ/L²) c, yₙ/L²)`. -/
noncomputable def BM {m : ℕ} (L : ℝ) (c : E m) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.of fun i j => (if i = j then dv m L i else 0) + (if j = Fin.last m then wv L c i else 0)

/-- `B`, the inverse transpose of the frequency map `ζ ↦ (L ζ̲, L⟨c, ζ̲⟩ + L² ζₙ)`. -/
noncomputable def BL {m : ℕ} (L : ℝ) (c : E m) : E (m + 1) →ₗ[ℝ] E (m + 1) :=
  Matrix.toLpLin 2 2 (BM L c)

lemma BL_apply {m : ℕ} (L : ℝ) (c : E m) (y : E (m + 1)) (i : Fin (m + 1)) :
    BL L c y i = dv m L i * y i + wv L c i * y (Fin.last m) := by
  simp [BL, BM, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib,
    ite_mul]

lemma horiz_BL {m : ℕ} (L : ℝ) (c : E m) (y : E (m + 1)) :
    horiz (BL L c y) = L⁻¹ • horiz y - (L⁻¹ ^ 2 * vert y) • c := by
  ext i
  rw [horiz_apply, BL_apply]
  simp [dv, wv, vert]
  ring

lemma vert_BL {m : ℕ} (L : ℝ) (c : E m) (y : E (m + 1)) :
    vert (BL L c y) = L⁻¹ ^ 2 * vert y := by
  simp [vert, BL_apply, dv, wv]

lemma det_BL {m : ℕ} (L : ℝ) (c : E m) : LinearMap.det (BL L c) = L⁻¹ ^ (m + 2) := by
  rw [BL, Matrix.toLpLin_eq_toLin, LinearMap.det_toLin, Matrix.det_of_isUpperTriangular]
  · rw [Fin.prod_univ_castSucc]
    simp [BM, dv, wv]
    ring
  · intro i j hij
    have h1 : i ≠ j := ne_of_gt hij
    have h2 : j ≠ Fin.last m := Fin.ne_last_of_lt hij
    simp [BM, h1, h2]

lemma mp_BL {m : ℕ} {L : ℝ} (hL : 0 < L) (c : E m) :
    MeasurePreserving (BL L c) volume (ENNReal.ofReal (L ^ (m + 2)) • volume) := by
  refine ⟨(BL L c).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [det_BL]; positivity), det_BL,
    abs_of_pos (by positivity), inv_pow, inv_inv]

/-- `B` as a continuous linear equivalence. -/
noncomputable def BE {m : ℕ} {L : ℝ} (hL : 0 < L) (c : E m) : E (m + 1) ≃L[ℝ] E (m + 1) :=
  ((BL L c).equivOfDetNeZero (by rw [det_BL]; positivity)).toContinuousLinearEquiv

lemma BE_apply {m : ℕ} {L : ℝ} (hL : 0 < L) (c : E m) (y : E (m + 1)) : BE hL c y = BL L c y :=
  rfl

/-- The phase identity: `⟪B y, P(c + Lη)⟫ = ⟪y, P η⟫ + ⟪B y, P c⟫`. -/
lemma inner_BL {m : ℕ} {L : ℝ} (hL : 0 < L) (c η : E m) (y : E (m + 1)) :
    ⟪BL L c y, mkPoint (c + L • η) (‖c + L • η‖ ^ 2 / 2)⟫ =
      ⟪y, mkPoint η (‖η‖ ^ 2 / 2)⟫ + ⟪BL L c y, mkPoint c (‖c‖ ^ 2 / 2)⟫ := by
  rw [inner_hv, inner_hv, inner_hv]
  simp only [horiz_BL, vert_BL, horiz_mkPoint, vert_mkPoint]
  simp only [inner_add_right, inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- The transformed function `H'(y) = L^{-(m+2)} e(-⟪By, P c⟫) H(By)`. -/
noncomputable def Hp {m : ℕ} (L : ℝ) (c : E m) (H : E (m + 1) → ℂ) (y : E (m + 1)) : ℂ :=
  (((L ^ (m + 2))⁻¹ : ℝ) : ℂ) * ((𝐞 (-⟪BL L c y, mkPoint c (‖c‖ ^ 2 / 2)⟫) : Circle) : ℂ) *
    H (BL L c y)

lemma fourier_Hp {m : ℕ} {L : ℝ} (hL : 0 < L) (c : E m) (H : E (m + 1) → ℂ) (η : E m) :
    𝓕 H (mkPoint (c + L • η) (‖c + L • η‖ ^ 2 / 2)) = 𝓕 (Hp L c H) (mkPoint η (‖η‖ ^ 2 / 2)) := by
  have hMP := mp_BL hL c
  have hME : MeasurableEmbedding (BL L c) := (BE hL c).toHomeomorph.measurableEmbedding
  have h1 : ∫ y, 𝐞 (-⟪BL L c y, mkPoint (c + L • η) (‖c + L • η‖ ^ 2 / 2)⟫) • H (BL L c y) =
      (L ^ (m + 2)) • ∫ x, 𝐞 (-⟪x, mkPoint (c + L • η) (‖c + L • η‖ ^ 2 / 2)⟫) • H x := by
    have := hMP.integral_comp hME
      (fun x => 𝐞 (-⟪x, mkPoint (c + L • η) (‖c + L • η‖ ^ 2 / 2)⟫) • H x)
    rw [this, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
  rw [Real.fourier_eq, Real.fourier_eq]
  have h2 : ∀ y, 𝐞 (-⟪y, mkPoint η (‖η‖ ^ 2 / 2)⟫) • Hp L c H y = ((L ^ (m + 2))⁻¹ : ℝ) •
      (𝐞 (-⟪BL L c y, mkPoint (c + L • η) (‖c + L • η‖ ^ 2 / 2)⟫) • H (BL L c y)) := by
    intro y
    simp only [Hp, inner_BL hL c η y, neg_add, AddChar.map_add_eq_mul, Circle.smul_def,
      smul_eq_mul, Circle.coe_mul, Complex.real_smul]
    ring
  simp_rw [h2]
  rw [integral_smul, h1, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

lemma lintegral_Hp {m : ℕ} {L : ℝ} (hL : 0 < L) (c : E m) (H : E (m + 1) → ℂ) {p : ℝ}
    (hp : 0 ≤ p) :
    ∫⁻ y, ‖Hp L c H y‖ₑ ^ p =
      ENNReal.ofReal (((L ^ (m + 2))⁻¹) ^ p * L ^ (m + 2)) * ∫⁻ w, ‖H w‖ₑ ^ p := by
  have hMP := mp_BL hL c
  have hME : MeasurableEmbedding (BL L c) := (BE hL c).toHomeomorph.measurableEmbedding
  have hpt : ∀ y, ‖Hp L c H y‖ₑ ^ p =
      ENNReal.ofReal (((L ^ (m + 2))⁻¹) ^ p) * ‖H (BL L c y)‖ₑ ^ p := by
    intro y
    rw [Hp, enorm_mul, enorm_mul, enorm_circle, mul_one, ENNReal.mul_rpow_of_nonneg _ _ hp,
      ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    hMP.lintegral_comp_emb hME (fun w => ‖H w‖ₑ ^ p), lintegral_smul_measure, smul_eq_mul,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

lemma memLp_Hp {m : ℕ} {L : ℝ} (hL : 0 < L) (c : E m) {H : E (m + 1) → ℂ} {q : ℝ≥0∞}
    (hH : MemLp H q volume) : MemLp (Hp L c H) q volume := by
  have hMP := mp_BL hL c
  have h1 : MemLp (H ∘ BL L c) q volume :=
    (hH.smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving hMP
  have h2 : MemLp (fun y => (((L ^ (m + 2))⁻¹ : ℝ) : ℂ) * (H ∘ BL L c) y) q volume :=
    h1.const_mul _
  refine h2.of_le ?_ (Eventually.of_forall fun y => ?_)
  · have hB : Continuous (BL L c) := (BL L c).continuous_of_finiteDimensional
    have hc : Continuous fun y : E (m + 1) =>
        ((𝐞 (-⟪BL L c y, mkPoint c (‖c‖ ^ 2 / 2)⟫) : Circle) : ℂ) :=
      continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp ((hB.inner continuous_const).neg))
    exact (aestronglyMeasurable_const.mul hc.aestronglyMeasurable).mul h1.aestronglyMeasurable
  · simp only [Hp, norm_mul, Circle.norm_coe, mul_one, Function.comp_apply, le_refl]

lemma support_Hp {m : ℕ} {L : ℝ} (hL : 0 < L) (c : E m) {H : E (m + 1) → ℂ}
    (hs : ∃ R : ℝ, ∀ w, R < ‖w‖ → H w = 0) : ∃ R : ℝ, ∀ w, R < ‖w‖ → Hp L c H w = 0 := by
  obtain ⟨R, hR⟩ := hs
  set K := ‖((BE hL c).symm : E (m + 1) →L[ℝ] E (m + 1))‖
  refine ⟨K * |R|, fun w hw => ?_⟩
  have hz : H (BL L c w) = 0 := by
    apply hR
    by_contra hle
    push Not at hle
    have h3 : ‖w‖ ≤ K * ‖BE hL c w‖ := by
      have := ((BE hL c).symm : E (m + 1) →L[ℝ] E (m + 1)).le_opNorm (BE hL c w)
      rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at this
      exact this
    have h4 : ‖BL L c w‖ ≤ |R| := hle.trans (le_abs_self R)
    rw [BE_apply] at h3
    nlinarith [norm_nonneg ((BE hL c).symm : E (m + 1) →L[ℝ] E (m + 1))]
  simp [Hp, hz]

/-! ## Step 3: the ball `B(c, L)` as a rescaled unit ball -/
lemma lint_ball {m : ℕ} (F : E m → ℝ≥0∞) (hF : Measurable F) {L : ℝ} (hL : 0 < L) (c : E m) :
    ∫⁻ ξ in ball c L, F ξ = ENNReal.ofReal (L ^ m) * ∫⁻ η in ball (0 : E m) 1, F (c + L • η) := by
  have hG : Measurable ((ball c L).indicator F) := hF.indicator measurableSet_ball
  have hm : Measurable (fun y : E m => L • y) := measurable_const_smul _
  have hG' : Measurable (fun x : E m => (ball c L).indicator F (x + c)) :=
    hG.comp (measurable_add_const c)
  have key := lintegral_map hG' hm (μ := (volume : Measure (E m)))
  rw [Measure.map_addHaar_smul volume hL.ne', lintegral_smul_measure,
    lintegral_add_right_eq_self ((ball c L).indicator F) c, finrank_euclideanSpace_fin] at key
  have hiff : ∀ y : E m, L • y + c ∈ ball c L ↔ y ∈ ball (0 : E m) 1 := by
    intro y
    rw [mem_ball, mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul,
      Real.norm_of_nonneg hL.le, dist_zero_right, mul_lt_iff_lt_one_right hL]
  have hpt : (ball (0 : E m) 1).indicator (fun η => F (c + L • η)) =
      fun y => (ball c L).indicator F (L • y + c) := by
    funext y
    by_cases hy : y ∈ ball (0 : E m) 1
    · rw [indicator_of_mem hy, indicator_of_mem ((hiff y).2 hy), add_comm]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy ((hiff y).1 h))]
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball, hpt,
    ← key, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

lemma exp_id (m : ℕ) {L : ℝ} (hL : 0 < L) (p : ℝ) :
    L ^ m * (((L ^ (m + 2))⁻¹) ^ p * L ^ (m + 2)) = L ^ ((m : ℝ) - ((m : ℝ) + 2) * (p - 1)) := by
  rw [← Real.rpow_natCast L m, ← Real.rpow_natCast L (m + 2), ← Real.rpow_neg hL.le,
    ← Real.rpow_mul hL.le, ← Real.rpow_add hL, ← Real.rpow_add hL]
  congr 1
  push_cast
  ring

/-! ## The target -/
/-- **F1.** -/
theorem restr_ball (m : ℕ) (hm : 1 ≤ m) (hR : ParabolicRestrictionConjecture m) (p : ℝ)
    (hp : 1 ≤ p) (hpc : p < pc m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ c : E m, ∀ H : E (m + 1) → ℂ, MemLp H 1 volume →
      MemLp H (ENNReal.ofReal p) volume → (∃ R : ℝ, ∀ w, R < ‖w‖ → H w = 0) →
      ∫⁻ ξ in ball c L, ‖𝓕 H (mkPoint ξ (‖ξ‖ ^ 2 / 2))‖ₑ ^ p ≤
        ENNReal.ofReal (C * L ^ ((m : ℝ) - ((m : ℝ) + 2) * (p - 1))) * ∫⁻ w, ‖H w‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by rw [ENNReal.one_le_ofReal]; exact hp
  have h2 : ENNReal.ofReal p < ENNReal.ofReal (2 * (m + 1) / (m + 2)) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]; simpa [pc] using hpc
  obtain ⟨C₀, hC₀⟩ := hR (ENNReal.ofReal p) h1 h2
  refine ⟨(C₀ : ℝ) ^ p, by positivity, fun L hL c H h1H hpH hsH => ?_⟩
  have hint : Integrable H := memLp_one_iff_integrable.mp h1H
  have hmeas : Measurable fun ξ : E m => ‖𝓕 H (mkPoint ξ (‖ξ‖ ^ 2 / 2))‖ₑ ^ p :=
    (((continuous_fourier_of_integrable hint).comp continuous_parab).measurable.enorm).pow_const p
  rw [lint_ball _ hmeas hL c]
  simp_rw [fourier_Hp hL c H]
  calc ENNReal.ofReal (L ^ m) *
        ∫⁻ η in ball (0 : E m) 1, ‖𝓕 (Hp L c H) (mkPoint η (‖η‖ ^ 2 / 2))‖ₑ ^ p
      ≤ ENNReal.ofReal (L ^ m) *
        ∫⁻ η in closedBall (0 : E m) 1, ‖𝓕 (Hp L c H) (mkPoint η (‖η‖ ^ 2 / 2))‖ₑ ^ p := by
        gcongr
        exact ball_subset_closedBall
    _ ≤ ENNReal.ofReal (L ^ m) * ((C₀ : ℝ≥0∞) ^ p * ∫⁻ y, ‖Hp L c H y‖ₑ ^ p) := by
        gcongr
        exact density hp C₀ hC₀ _ (memLp_Hp hL c h1H) (memLp_Hp hL c hpH) (support_Hp hL c hsH)
    _ = ENNReal.ofReal ((C₀ : ℝ) ^ p * L ^ ((m : ℝ) - ((m : ℝ) + 2) * (p - 1))) *
          ∫⁻ w, ‖H w‖ₑ ^ p := by
        rw [lintegral_Hp hL c H hp0.le, ← exp_id m hL p, ← ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_rpow_of_nonneg NNReal.zero_le_coe hp0.le, ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end TaoBR.Carb.PartF1
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
/-! ## Part F1: the restriction hypothesis on any ball, for `L¹ ∩ Lᵖ` functions -/
alias restr_ball := TaoBR.Carb.PartF1.restr_ball

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartF2
variable {m : ℕ}
@[simp] theorem mkPoint_horiz_vert (y : E (m + 1)) : mkPoint (horiz y) (vert y) = y :=
  ext_hv (by simp) (by simp)

theorem norm_sq_hv (y : E (m + 1)) : ‖y‖ ^ 2 = ‖horiz y‖ ^ 2 + vert y ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [vert]

theorem norm_le_horiz_add_vert (y : E (m + 1)) : ‖y‖ ≤ ‖horiz y‖ + |vert y| := by
  have := norm_sq_hv y
  have h : ‖y‖ ^ 2 ≤ (‖horiz y‖ + |vert y|) ^ 2 := by
    rw [this]; nlinarith [norm_nonneg (horiz y), abs_nonneg (vert y), sq_abs (vert y)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

theorem continuous_horiz : Continuous (horiz : E (m + 1) → E m) := by
  unfold horiz; fun_prop

theorem continuous_vert : Continuous (vert : E (m + 1) → ℝ) := by
  unfold vert; fun_prop

@[fun_prop] theorem measurable_horiz : Measurable (horiz : E (m + 1) → E m) :=
  continuous_horiz.measurable

@[fun_prop] theorem measurable_vert : Measurable (vert : E (m + 1) → ℝ) :=
  continuous_vert.measurable

theorem continuous_mkPoint : Continuous fun q : E m × ℝ => mkPoint q.1 q.2 := by
  unfold mkPoint
  apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  induction i using Fin.lastCases with
  | last => simp; fun_prop
  | cast j => simp; fun_prop

theorem measurable_mkPoint : Measurable fun q : E m × ℝ => mkPoint q.1 q.2 :=
  continuous_mkPoint.measurable

theorem inner_mkPoint (u u' : E m) (t t' : ℝ) :
    ⟪mkPoint u t, mkPoint u' t'⟫ = ⟪u, u'⟫ + t * t' := by
  simp only [PiLp.inner_apply, Fin.sum_univ_castSucc, mkPoint_castSucc, mkPoint_last]
  simp [mul_comm]

end TaoBR.Carb.PartF2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartF2
theorem measurePreserving_mkPoint (m : ℕ) :
    MeasurePreserving (fun q : E m × ℝ => mkPoint q.1 q.2) (volume.prod volume) volume := by
  have h1 : MeasurePreserving (Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ))
      ((volume : Measure (E m)).prod (volume : Measure ℝ)) (volume.prod volume) :=
    (PiLp.volume_preserving_ofLp (Fin m)).prod (MeasurePreserving.id volume)
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin m → ℝ)))
    (ν := (volume : Measure ℝ)))
  have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
  have h4 := PiLp.volume_preserving_toLp (Fin (m + 1))
  have h := h4.comp (h3.comp (h2.comp h1))
  have heq : (fun q : E m × ℝ => mkPoint q.1 q.2) = (WithLp.toLp 2 ∘
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm ∘
        Prod.swap ∘ Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ)) := by
    funext q
    apply ext_hv
    · ext i; simp [Function.comp]
    · simp [vert, Function.comp]
  rw [heq]; exact h

theorem lintegral_mkPoint (m : ℕ) (F : E (m + 1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ u, ∫⁻ h, F (mkPoint u h) := by
  rw [← (measurePreserving_mkPoint m).lintegral_comp hF]
  exact lintegral_prod _ (hF.comp measurable_mkPoint).aemeasurable

/-! ## `ex` -/
theorem norm_ex (t : ℝ) : ‖ex t‖ = 1 := by
  unfold ex
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem enorm_ex (t : ℝ) : ‖ex t‖ₑ = 1 := by
  rw [← ofReal_norm, norm_ex, ENNReal.ofReal_one]

theorem fourierChar_eq_ex (x : ℝ) : ((𝐞 x : Circle) : ℂ) = ex x := by
  rw [Real.fourierChar_apply, ex]; congr 1; push_cast; ring

theorem ex_add (a b : ℝ) : ex (a + b) = ex a * ex b := by
  rw [ex, ex, ex, ← Complex.exp_add]; congr 1; push_cast; ring

theorem continuous_ex : Continuous ex := by unfold ex; fun_prop

@[fun_prop] theorem measurable_ex : Measurable ex := continuous_ex.measurable

/-! ## The projective change of variables -/
/-- The Jacobian `|wₙ|^{-(m+2)}` (`0` at `wₙ = 0`). -/
noncomputable def rho (m : ℕ) (w : E (m + 1)) : ℝ := |vert w|⁻¹ ^ (m + 2)

/-- `Ψ(w) = (-w̲/wₙ, xₙ - 1/wₙ)`. -/
noncomputable def Psi (m : ℕ) (xn : ℝ) (w : E (m + 1)) : E (m + 1) :=
  mkPoint (-(vert w)⁻¹ • horiz w) (xn - (vert w)⁻¹)

end TaoBR.Carb.PartF2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartF2
variable {m : ℕ}
theorem rho_nonneg (w : E (m + 1)) : 0 ≤ rho m w := by unfold rho; positivity

theorem rho_of_vert (w : E (m + 1)) (h : vert w = 0) : rho m w = 0 := by simp [rho, h]

theorem measurable_rho : Measurable (rho m) := by
  unfold rho; fun_prop

theorem measurable_Psi (xn : ℝ) : Measurable (Psi m xn) := by
  unfold Psi
  exact measurable_mkPoint.comp ((((measurable_vert.inv).neg).smul measurable_horiz).prodMk
    (measurable_const.sub measurable_vert.inv))

theorem vert_Psi (xn : ℝ) (w : E (m + 1)) : xn - vert (Psi m xn w) = (vert w)⁻¹ := by
  simp [Psi]

theorem lint_inv (xn : ℝ) (G : ℝ → ℝ≥0∞) :
    ∫⁻ t, ENNReal.ofReal |(t ^ 2)⁻¹| * G (xn - t⁻¹) = ∫⁻ s, G s := by
  have hs : MeasurableSet ({0}ᶜ : Set ℝ) := (measurableSet_singleton 0).compl
  have hder : ∀ t ∈ ({0}ᶜ : Set ℝ),
      HasDerivWithinAt (fun t : ℝ => xn - t⁻¹) ((t ^ 2)⁻¹) {0}ᶜ t := by
    intro t ht
    have := (hasDerivAt_inv (show t ≠ 0 from ht)).const_sub xn
    simpa using this.hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => xn - t⁻¹) {0}ᶜ := by
    intro a _ b _ hab; simpa using hab
  have himg : (fun t : ℝ => xn - t⁻¹) '' {0}ᶜ = {xn}ᶜ := by
    ext s; simp only [mem_image, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro ⟨t, ht, rfl⟩; simpa using ht
    · intro hs
      exact ⟨(xn - s)⁻¹, by simpa [sub_eq_zero] using (Ne.symm hs), by simp⟩
  have := lintegral_image_eq_lintegral_abs_deriv_mul hs hder hinj G
  rw [himg, restrict_compl_singleton, restrict_compl_singleton] at this
  exact this.symm

theorem lint_smul (r : ℝ) (hr : r ≠ 0) (g : E m → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ u, g (r • u) = ENNReal.ofReal |(r ^ m)⁻¹| * ∫⁻ u, g u := by
  have := Measure.map_addHaar_smul (volume : Measure (E m)) hr
  rw [finrank_euclideanSpace_fin] at this
  rw [← lintegral_map hg (measurable_const_smul r), this, lintegral_smul_measure, smul_eq_mul]

theorem lint_cv (xn : ℝ) (F : E (m + 1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w, ENNReal.ofReal (rho m w) * F (Psi m xn w) = ∫⁻ y, F y := by
  have hmeas : Measurable (fun w => ENNReal.ofReal (rho m w) * F (Psi m xn w)) :=
    (ENNReal.measurable_ofReal.comp measurable_rho).mul (hF.comp (measurable_Psi xn))
  have hs1 := lintegral_lintegral_swap (μ := (volume : Measure (E m))) (ν := (volume : Measure ℝ))
    (f := fun (u : E m) (t : ℝ) => ENNReal.ofReal (rho m (mkPoint u t)) * F (Psi m xn (mkPoint u t)))
    (hmeas.comp measurable_mkPoint).aemeasurable
  have hs2 := lintegral_lintegral_swap (μ := (volume : Measure (E m))) (ν := (volume : Measure ℝ))
    (f := fun (u : E m) (t : ℝ) => F (mkPoint u t)) (hF.comp measurable_mkPoint).aemeasurable
  rw [lintegral_mkPoint m _ hmeas, lintegral_mkPoint m F hF, hs1, hs2,
    ← lint_inv xn (fun s => ∫⁻ u, F (mkPoint u s))]
  congr 1; funext t
  simp only [rho, Psi, vert_mkPoint, horiz_mkPoint]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have hFt : Measurable (fun u : E m => F (mkPoint u (xn - t⁻¹))) :=
      hF.comp (measurable_mkPoint.comp (measurable_id.prodMk measurable_const))
    have hsm := lint_smul (-t⁻¹) (by simpa using ht) _ hFt
    rw [lintegral_const_mul (f := fun x : E m => F (mkPoint (-t⁻¹ • x) (xn - t⁻¹))) _
      (hFt.comp (measurable_const_smul (-t⁻¹))), hsm, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [abs_inv, abs_pow, abs_neg, abs_inv, abs_inv, abs_pow]
    have : 0 < |t| := abs_pos.2 ht
    field_simp
    have h2 : |t| ^ 2 * (1 / |t|) ^ 2 = 1 := by field_simp
    rw [pow_add, ← mul_assoc, mul_comm (|t| ^ 2), mul_assoc, h2, mul_one]

theorem map_Psi (xn : ℝ) :
    Measure.map (Psi m xn) (volume.withDensity (fun w => ENNReal.ofReal (rho m w))) = volume := by
  ext s hs
  rw [Measure.map_apply (measurable_Psi xn) hs, withDensity_apply _ (measurable_Psi xn hs)]
  have := lint_cv (m := m) xn (s.indicator 1) (measurable_one.indicator hs)
  rw [← lintegral_indicator_one hs, ← this, ← lintegral_indicator (measurable_Psi xn hs)]
  congr 1; funext w
  by_cases hw : Psi m xn w ∈ s <;> simp [indicator, hw]

theorem phase (x : E m) (w : E (m + 1)) (hv : vert w ≠ 0) (xn : ℝ) :
    -(‖x - horiz (Psi m xn w)‖ ^ 2 / (2 * (xn - vert (Psi m xn w)))) =
      -⟪w, mkPoint x (‖x‖ ^ 2 / 2)⟫ + -(‖horiz w‖ ^ 2 / (2 * vert w)) := by
  have hw : ⟪w, mkPoint x (‖x‖ ^ 2 / 2)⟫ = ⟪horiz w, x⟫ + vert w * (‖x‖ ^ 2 / 2) := by
    conv_lhs => rw [← mkPoint_horiz_vert w]
    rw [inner_mkPoint]
  rw [hw, vert_Psi]
  simp only [Psi, horiz_mkPoint]
  have hn : ‖x - -(vert w)⁻¹ • horiz w‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * (vert w)⁻¹ * ⟪horiz w, x⟫ + (vert w)⁻¹ ^ 2 * ‖horiz w‖ ^ 2 := by
    simp only [neg_smul, sub_neg_eq_add]
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm]
    ring
  rw [hn]
  field_simp
  ring

/-- The function `H`. -/
noncomputable def Hf (m : ℕ) (xn : ℝ) (b : ℝ → ℂ) (g : E (m + 1) → ℂ) (w : E (m + 1)) : ℂ :=
  (rho m w : ℂ) * b ((vert w)⁻¹) * ex (-(‖horiz w‖ ^ 2 / (2 * vert w))) * g (Psi m xn w)

theorem fourier_integrand (x : E m) (w : E (m + 1)) (xn : ℝ) (b : ℝ → ℂ) (g : E (m + 1) → ℂ) :
    𝐞 (-⟪w, mkPoint x (‖x‖ ^ 2 / 2)⟫) • Hf m xn b g w =
      (rho m w : ℂ) * (b (xn - vert (Psi m xn w)) *
        ex (-(‖x - horiz (Psi m xn w)‖ ^ 2 / (2 * (xn - vert (Psi m xn w))))) * g (Psi m xn w)) := by
  rcases eq_or_ne (vert w) 0 with hv | hv
  · simp [Hf, rho_of_vert w hv]
  · rw [phase x w hv xn, ex_add, Circle.smul_def, fourierChar_eq_ex, smul_eq_mul, vert_Psi]
    simp only [Hf]
    ring

theorem rho_rpow (w : E (m + 1)) (hv : vert w ≠ 0) (p : ℝ) :
    rho m w ^ p = rho m w * |(vert w)⁻¹| ^ (((m : ℝ) + 2) * (p - 1)) := by
  have ha : 0 < |vert w|⁻¹ := by positivity
  rw [rho, abs_inv, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, ← Real.rpow_add ha]
  congr 1; push_cast; ring

theorem enorm_Hf (p : ℝ) (hp : 1 ≤ p) (xn : ℝ) (b : ℝ → ℂ) (g : E (m + 1) → ℂ) (w : E (m + 1)) :
    ‖Hf m xn b g w‖ₑ ^ p = ENNReal.ofReal (rho m w) *
      (‖b (xn - vert (Psi m xn w))‖ₑ ^ p *
        ENNReal.ofReal (|xn - vert (Psi m xn w)| ^ (((m : ℝ) + 2) * (p - 1))) *
        ‖g (Psi m xn w)‖ₑ ^ p) := by
  have hp0 : 0 < p := by linarith
  rcases eq_or_ne (vert w) 0 with hv | hv
  · simp [Hf, rho_of_vert w hv, ENNReal.zero_rpow_of_pos hp0]
  · rw [vert_Psi]
    simp only [Hf]
    have hr : ‖((rho m w : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (rho m w) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (rho_nonneg w)]
    rw [enorm_mul, enorm_mul, enorm_mul, enorm_ex, hr, mul_one,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ENNReal.ofReal_rpow_of_nonneg (rho_nonneg w) hp0.le, rho_rpow w hv,
      ENNReal.ofReal_mul (rho_nonneg w)]
    ring

theorem Hf_support (xn : ℝ) (b : ℝ → ℂ) (g : E (m + 1) → ℂ) (L : ℝ) (hL : 0 < L)
    (hbs : ∀ t, b t ≠ 0 → L / 2 ≤ |t| ∧ |t| ≤ L) (R : ℝ) (hgR : ∀ y, g y ≠ 0 → ‖horiz y‖ ≤ R)
    (w : E (m + 1)) (hw : (|R| + 1) * (2 / L) < ‖w‖) : Hf m xn b g w = 0 := by
  by_contra hne
  have hv : vert w ≠ 0 := fun hv => hne (by simp [Hf, rho_of_vert w hv])
  have hb : b ((vert w)⁻¹) ≠ 0 := fun h0 => hne (by simp [Hf, h0])
  have hg : g (Psi m xn w) ≠ 0 := fun h0 => hne (by simp [Hf, h0])
  obtain ⟨h1, -⟩ := hbs _ hb
  have h3 := hgR _ hg
  simp only [Psi, horiz_mkPoint] at h3
  rw [norm_smul, norm_neg, norm_inv, Real.norm_eq_abs] at h3
  have hva : 0 < |vert w| := abs_pos.2 hv
  rw [abs_inv] at h1
  have h1' : L / 2 * |vert w| ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h1 hva.le
    rwa [inv_mul_cancel₀ hva.ne'] at this
  have hv2 : |vert w| ≤ 2 / L := by rw [le_div_iff₀ hL]; linarith
  have h3' : ‖horiz w‖ ≤ R * |vert w| := by
    have := mul_le_mul_of_nonneg_left h3 hva.le
    rwa [← mul_assoc, mul_inv_cancel₀ hva.ne', one_mul, mul_comm] at this
  have h4 : R * |vert w| ≤ |R| * (2 / L) :=
    (mul_le_mul_of_nonneg_right (le_abs_self R) hva.le).trans
      (mul_le_mul_of_nonneg_left hv2 (abs_nonneg R))
  have := norm_le_horiz_add_vert w
  nlinarith

theorem measurable_Hf (xn : ℝ) (b : ℝ → ℂ) (hb : Measurable b) (g : E (m + 1) → ℂ)
    (hg : Measurable g) : Measurable (Hf m xn b g) := by
  unfold Hf
  refine (((Complex.measurable_ofReal.comp measurable_rho).mul
    (hb.comp measurable_vert.inv)).mul (measurable_ex.comp ?_)).mul (hg.comp (measurable_Psi xn))
  fun_prop

theorem frozen_eq (m : ℕ) (p : ℝ) (hp : 1 ≤ p) (L : ℝ) (hL : 0 < L) (xn : ℝ) (b : ℝ → ℂ)
    (hb : Measurable b) (M : ℝ) (hbM : ∀ t, ‖b t‖ ≤ M) (hbs : ∀ t, b t ≠ 0 → L / 2 ≤ |t| ∧ |t| ≤ L)
    (h : E (m + 1) → ℂ) (hh : MemLp h (ENNReal.ofReal p) volume)
    (hhs : ∃ R : ℝ, ∀ y, R < ‖horiz y‖ → h y = 0) :
    ∃ H : E (m + 1) → ℂ, MemLp H 1 volume ∧ MemLp H (ENNReal.ofReal p) volume ∧
      (∃ R : ℝ, ∀ w, R < ‖w‖ → H w = 0) ∧
      (∀ x : E m, ∫ y, b (xn - vert y) * ex (-(‖x - horiz y‖ ^ 2 / (2 * (xn - vert y)))) * h y =
          𝓕 H (mkPoint x (‖x‖ ^ 2 / 2))) ∧
      ∫⁻ w, ‖H w‖ₑ ^ p = ∫⁻ y, ‖b (xn - vert y)‖ₑ ^ p *
        ENNReal.ofReal (|xn - vert y| ^ (((m : ℝ) + 2) * (p - 1))) * ‖h y‖ₑ ^ p := by
  obtain ⟨R, hR⟩ := hhs
  have hp0 : 0 < p := by linarith
  set g₁ := hh.1.mk h
  have hg₁ : StronglyMeasurable g₁ := hh.1.stronglyMeasurable_mk
  have hhg₁ : h =ᵐ[volume] g₁ := hh.1.ae_eq_mk
  set g : E (m + 1) → ℂ := fun y => if ‖horiz y‖ ≤ R then g₁ y else 0 with hg_def
  have hgm : Measurable g :=
    Measurable.ite (measurableSet_le measurable_horiz.norm measurable_const) hg₁.measurable
      measurable_const
  have hhg : h =ᵐ[volume] g := by
    filter_upwards [hhg₁] with y hy
    by_cases hy' : ‖horiz y‖ ≤ R
    · simp [g, hy', hy]
    · simp [g, hy', hR y (lt_of_not_ge hy')]
  have hgR : ∀ y, g y ≠ 0 → ‖horiz y‖ ≤ R := by
    intro y hy; by_contra h'; simp [g, h'] at hy
  have hHm := measurable_Hf (m := m) xn b hb g hgm
  set e : ℝ := ((m : ℝ) + 2) * (p - 1) with he
  have he0 : 0 ≤ e := by rw [he]; have : 0 ≤ p - 1 := by linarith
                         positivity
  have hFm : Measurable (fun y : E (m + 1) => ‖b (xn - vert y)‖ₑ ^ p *
      ENNReal.ofReal (|xn - vert y| ^ e) * ‖g y‖ₑ ^ p) := by
    refine ((((hb.comp (measurable_const.sub measurable_vert)).enorm).pow_const p).mul
      (ENNReal.measurable_ofReal.comp ?_)).mul (hgm.enorm.pow_const p)
    exact (measurable_const.sub measurable_vert).abs.pow_const e
  have hlint : ∫⁻ w, ‖Hf m xn b g w‖ₑ ^ p = ∫⁻ y, ‖b (xn - vert y)‖ₑ ^ p *
      ENNReal.ofReal (|xn - vert y| ^ e) * ‖g y‖ₑ ^ p := by
    refine Eq.trans ?_ (lint_cv xn _ hFm)
    exact lintegral_congr fun w => enorm_Hf p hp xn b g w
  have hlint' : ∫⁻ y, ‖b (xn - vert y)‖ₑ ^ p * ENNReal.ofReal (|xn - vert y| ^ e) * ‖g y‖ₑ ^ p =
      ∫⁻ y, ‖b (xn - vert y)‖ₑ ^ p * ENNReal.ofReal (|xn - vert y| ^ e) * ‖h y‖ₑ ^ p :=
    lintegral_congr_ae (by filter_upwards [hhg] with y hy; rw [hy])
  have hgfin : ∫⁻ y, ‖g y‖ₑ ^ p < ∞ := by
    have h1 : ∫⁻ y, ‖g y‖ₑ ^ p = ∫⁻ y, ‖h y‖ₑ ^ p :=
      lintegral_congr_ae (by filter_upwards [hhg] with y hy; rw [hy])
    have h2 : ∫⁻ y, ‖h y‖ₑ ^ p = eLpNorm h (ENNReal.ofReal p) volume ^ p := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul]
      rw [show 1 / p * p = 1 by field_simp, ENNReal.rpow_one]
    rw [h1, h2]
    exact ENNReal.rpow_lt_top_of_nonneg hp0.le hh.2.ne
  have hHfin : ∫⁻ w, ‖Hf m xn b g w‖ₑ ^ p < ∞ := by
    rw [hlint]
    calc ∫⁻ y, ‖b (xn - vert y)‖ₑ ^ p * ENNReal.ofReal (|xn - vert y| ^ e) * ‖g y‖ₑ ^ p
        ≤ ∫⁻ y, (ENNReal.ofReal M ^ p * ENNReal.ofReal (L ^ e)) * ‖g y‖ₑ ^ p := by
          refine lintegral_mono fun y => ?_
          by_cases hb0 : b (xn - vert y) = 0
          · simp [hb0, ENNReal.zero_rpow_of_pos hp0]
          · obtain ⟨-, h2⟩ := hbs _ hb0
            gcongr
            · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hbM _)
      _ = (ENNReal.ofReal M ^ p * ENNReal.ofReal (L ^ e)) * ∫⁻ y, ‖g y‖ₑ ^ p :=
          lintegral_const_mul _ (hgm.enorm.pow_const p)
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg hp0.le ENNReal.ofReal_ne_top) ENNReal.ofReal_lt_top) hgfin
  have hHp : MemLp (Hf m xn b g) (ENNReal.ofReal p) volume := by
    refine ⟨hHm.aestronglyMeasurable, ?_⟩
    have h2 : ∫⁻ w, ‖Hf m xn b g w‖ₑ ^ p = eLpNorm (Hf m xn b g) (ENNReal.ofReal p) volume ^ p := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul]
      rw [show 1 / p * p = 1 by field_simp, ENNReal.rpow_one]
    rw [h2] at hHfin
    exact (ENNReal.rpow_lt_top_iff_of_pos hp0).1 hHfin
  have hsupp : ∀ w, (|R| + 1) * (2 / L) < ‖w‖ → Hf m xn b g w = 0 :=
    fun w hw => Hf_support xn b g L hL hbs R hgR w hw
  refine ⟨Hf m xn b g, ?_, hHp, ⟨_, hsupp⟩, ?_, hlint.trans hlint'⟩
  · refine hHp.mono_exponent_of_measure_support_ne_top (s := closedBall 0 ((|R| + 1) * (2 / L)))
      (fun w hw => hsupp w ?_) measure_closedBall_lt_top.ne (ENNReal.one_le_ofReal.2 hp)
    simpa [mem_closedBall_zero_iff] using hw
  · intro x
    set G : E (m + 1) → ℂ := fun y =>
      b (xn - vert y) * ex (-(‖x - horiz y‖ ^ 2 / (2 * (xn - vert y)))) * g y with hG
    have hGm : Measurable G := by
      refine ((hb.comp (measurable_const.sub measurable_vert)).mul (measurable_ex.comp ?_)).mul hgm
      fun_prop
    have h1 : ∫ y, b (xn - vert y) * ex (-(‖x - horiz y‖ ^ 2 / (2 * (xn - vert y)))) * h y =
        ∫ y, G y := integral_congr_ae (by filter_upwards [hhg] with y hy; rw [hy])
    have key : ∫ w, G (Psi m xn w) ∂(volume.withDensity (fun w => ENNReal.ofReal (rho m w))) =
        ∫ y, G y := by
      rw [← integral_map (measurable_Psi xn).aemeasurable
        (by rw [map_Psi]; exact hGm.aestronglyMeasurable), map_Psi]
    have key2 : ∫ w, G (Psi m xn w) ∂(volume.withDensity (fun w => ENNReal.ofReal (rho m w))) =
        ∫ w, (rho m w : ℂ) * G (Psi m xn w) := by
      have := integral_withDensity_eq_integral_smul (μ := (volume : Measure (E (m + 1))))
        (measurable_rho (m := m)).real_toNNReal (fun w => G (Psi m xn w))
      change ∫ w, G (Psi m xn w) ∂(volume.withDensity
        (fun w => ((rho m w).toNNReal : ℝ≥0∞))) = _
      rw [this]
      congr 1; funext w
      rw [NNReal.smul_def, Real.coe_toNNReal _ (rho_nonneg w), Complex.real_smul]
    rw [h1, ← key, key2, Real.fourier_eq]
    congr 1; funext w
    rw [fourier_integrand]

end TaoBR.Carb.PartF2
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
/-! ## Part F2: the projective change of variables -/
alias frozen_eq := TaoBR.Carb.PartF2.frozen_eq

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartN
open TaoBR.Carb
variable {m : ℕ}
/-! ## Part N -/
/-- **N.** For `b` supported in `L/2 ≤ |τ| ≤ L`, `|b| ≤ M`, and `h` with bounded horizontal support,
`∫_{x̲ ∈ B(c, L)} |(kb b) * h|^p ≲ M^p L^{m+1-mp/2} ‖h‖_p^p` (superposition `Eg_superpos`, Minkowski in
`ξ`, `frozen_eq` and `restr_ball` for each `xₙ`, then `∫ dxₙ`). -/
theorem near_bound (m : ℕ) (hm : 1 ≤ m) (hR : ParabolicRestrictionConjecture m) (p : ℝ)
    (hp : 1 ≤ p) (hpc : p < pc m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ∀ M : ℝ, 0 ≤ M → ∀ b : ℝ → ℂ, Measurable b →
      (∀ t, ‖b t‖ ≤ M) → (∀ t, b t ≠ 0 → L / 2 ≤ |t| ∧ |t| ≤ L) →
      ∀ c : E m, ∀ h : E (m + 1) → ℂ, MemLp h (ENNReal.ofReal p) volume →
        (∃ R : ℝ, ∀ y, R < ‖horiz y‖ → h y = 0) →
        ∫⁻ x in {x : E (m + 1) | horiz x ∈ ball c L}, ‖conv (kb m b) h x‖ₑ ^ p ≤
          ENNReal.ofReal (C * M ^ p * L ^ ((m : ℝ) + 1 - (m : ℝ) * p / 2)) * ∫⁻ y, ‖h y‖ₑ ^ p := by
  obtain ⟨cf, hcf_meas, hcf_norm, hcf_eq⟩ := Eg_superpos m
  obtain ⟨C₁, hC₁, hrestr⟩ := restr_ball m hm hR p hp hpc
  refine ⟨C₁ * 2 * 2 ^ ((m : ℝ) * p / 2), by positivity, ?_⟩
  intro L hL M hM b hb hbM hbs c h hh hhs
  have hL0 : 0 < L := by linarith
  have hp0 : 0 < p := by linarith
  set e : ℝ := ((m : ℝ) + 2) * (p - 1) with he_def
  have he0 : 0 ≤ e := mul_nonneg (by positivity) (by linarith)
  set b' : ℝ → ℂ := fun t => b t * cf t with hb'_def
  set M' : ℝ := M * (L / 2) ^ (-((m : ℝ) / 2)) with hM'_def
  have hM'0 : 0 ≤ M' := by positivity
  have hb'meas : Measurable b' := hb.mul hcf_meas
  have hb's : ∀ t, b' t ≠ 0 → L / 2 ≤ |t| ∧ |t| ≤ L := fun t ht =>
    hbs t (left_ne_zero_of_mul ht)
  have hb'M : ∀ t, ‖b' t‖ ≤ M' := by
    intro t
    by_cases ht : b t = 0
    · simp [b', ht, hM'0]
    obtain ⟨h1, -⟩ := hbs t ht
    have hτ : t ≠ 0 := by
      intro h0; rw [h0, abs_zero] at h1; linarith
    simp only [b', norm_mul, hcf_norm t hτ]
    exact mul_le_mul (hbM t) (Real.rpow_le_rpow_of_nonpos (by positivity) h1
      (by have : (0 : ℝ) ≤ m := by positivity
          linarith)) (by positivity) hM
  have hvertm : Measurable (fun y : E (m + 1) => vert y) := vert_continuous.measurable
  have hhorm : Measurable (fun y : E (m + 1) => horiz y) := horiz_continuous.measurable
  -- the per-`xₙ` estimate
  have key : ∀ xn : ℝ, ∫⁻ u in ball c L, ‖conv (kb m b) h (mkPoint u xn)‖ₑ ^ p ≤
      ENNReal.ofReal (C₁ * L ^ ((m : ℝ) - ((m : ℝ) + 2) * (p - 1))) *
        ∫⁻ y, ‖b' (xn - vert y)‖ₑ ^ p * ENNReal.ofReal (|xn - vert y| ^ e) * ‖h y‖ₑ ^ p := by
    intro xn
    obtain ⟨H, hH1, hHp, hHs, hHeq, hHnorm⟩ :=
      frozen_eq m p hp L hL0 xn b' hb'meas M' hb'M hb's h hh hhs
    set G : E m → ℂ := fun u => ∫ y, b' (xn - vert y) *
      ex (-(‖u - horiz y‖ ^ 2 / (2 * (xn - vert y)))) * h y with hG_def
    have hGF : ∀ u, G u = 𝓕 H (mkPoint u (‖u‖ ^ 2 / 2)) := hHeq
    have hGc : Continuous G := by
      have : G = fun u => 𝓕 H (mkPoint u (‖u‖ ^ 2 / 2)) := funext hGF
      rw [this]
      exact (continuous_fourier_of_integrable (memLp_one_iff_integrable.1 hH1)).comp
        (continuous_mkPoint.comp (continuous_id.prodMk ((continuous_norm.pow 2).div_const 2)))
    set A := ENNReal.ofReal (C₁ * L ^ ((m : ℝ) - ((m : ℝ) + 2) * (p - 1))) with hA_def
    have hball : ∀ c' : E m, ∫⁻ u in ball c' L, ‖G u‖ₑ ^ p ≤ A * ∫⁻ w, ‖H w‖ₑ ^ p := by
      intro c'
      simpa only [hGF] using hrestr L hL0 c' H hH1 hHp hHs
    set gR : E m → ℝ := fun ξ => Real.exp (-(Real.pi * ‖ξ‖ ^ 2)) with hgR
    have hgRc : Continuous gR := by fun_prop
    have hgm : Measurable (fun ξ : E m => ENNReal.ofReal (gR ξ)) :=
      hgRc.measurable.ennreal_ofReal
    have hgen : ∀ ξ, ‖(gR ξ : ℂ)‖ₑ = ENNReal.ofReal (gR ξ) := by
      intro ξ
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hexc : Continuous ex := by unfold ex; fun_prop
    -- `b' (xn - vert ·) h` is integrable
    have hk : Integrable (fun y : E (m + 1) => b' (xn - vert y) * h y) := by
      obtain ⟨R, hR⟩ := hhs
      set ρ := max R 0 + |xn| + L
      have hhint : IntegrableOn h (closedBall (0 : E (m + 1)) ρ) := by
        have h1 : MemLp h (ENNReal.ofReal p) (volume.restrict (closedBall 0 ρ)) := hh.restrict _
        have : IsFiniteMeasure (volume.restrict (closedBall (0 : E (m + 1)) ρ)) :=
          isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
        exact h1.integrable (ENNReal.one_le_ofReal.2 hp)
      refine Integrable.mono' ((hhint.integrable_indicator measurableSet_closedBall).norm.const_mul M')
        ((hb'meas.comp (measurable_const.sub hvertm)).aestronglyMeasurable.mul hh.1)
        (ae_of_all _ fun y => ?_)
      by_cases hy : y ∈ closedBall (0 : E (m + 1)) ρ
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_right (hb'M _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, norm_zero, mul_zero]
        have h0 : b' (xn - vert y) = 0 ∨ h y = 0 := by
          by_contra hc
          push Not at hc
          apply hy
          have h1 := (hb's _ hc.1).2
          have h2 : ‖horiz y‖ ≤ R := not_lt.1 (fun hlt => hc.2 (hR y hlt))
          rw [mem_closedBall, dist_zero_right]
          have h3 := norm_le_horiz_add_vert y
          have h4 := abs_sub_abs_le_abs_sub (vert y) xn
          rw [abs_sub_comm] at h4
          linarith [le_max_left R 0]
        rcases h0 with h0 | h0 <;> simp [h0]
    have hrep : ∀ u, conv (kb m b) h (mkPoint u xn) = ∫ ξ, (gR ξ : ℂ) * G (u - ξ) := by
      intro u
      have hpt : ∀ y, kb m b (mkPoint u xn - y) * h y = ∫ ξ, (gR ξ : ℂ) *
          (b' (xn - vert y) * ex (-(‖(u - ξ) - horiz y‖ ^ 2 / (2 * (xn - vert y)))) * h y) := by
        intro y
        simp only [kb, vert_sub, horiz_sub, vert_mkPoint, horiz_mkPoint]
        by_cases hz : b (xn - vert y) = 0
        · simp [b', hz]
        have hτ : xn - vert y ≠ 0 := by
          intro h0; have := (hbs _ hz).1; rw [h0, abs_zero] at this; linarith
        rw [hcf_eq _ hτ]
        have hre : ∀ I : ℂ, b (xn - vert y) * (cf (xn - vert y) * I) * h y =
            (b' (xn - vert y) * h y) * I := fun I => by simp only [b']; ring
        rw [hre, ← integral_const_mul]
        congr 1; funext ξ
        rw [sub_right_comm u ξ (horiz y)]; ring
      have hint : Integrable (Function.uncurry fun (y : E (m + 1)) (ξ : E m) => (gR ξ : ℂ) *
          (b' (xn - vert y) * ex (-(‖(u - ξ) - horiz y‖ ^ 2 / (2 * (xn - vert y)))) * h y))
          ((volume : Measure (E (m + 1))).prod volume) := by
        refine Integrable.mono' (hk.norm.mul_prod (integrable_gauss m)) ?_ (ae_of_all _ fun q => ?_)
        · have hm1 : Measurable (fun q : E (m + 1) × E m => (gR q.2 : ℂ) *
              (b' (xn - vert q.1) * ex (-(‖(u - q.2) - horiz q.1‖ ^ 2 / (2 * (xn - vert q.1)))))) := by
            have ha : Measurable (fun q : E (m + 1) × E m =>
                -(‖(u - q.2) - horiz q.1‖ ^ 2 / (2 * (xn - vert q.1)))) := by
              have : Measurable (fun q : E (m + 1) × E m => horiz q.1) := hhorm.comp measurable_fst
              have : Measurable (fun q : E (m + 1) × E m => vert q.1) := hvertm.comp measurable_fst
              fun_prop
            exact (Complex.measurable_ofReal.comp (hgRc.measurable.comp measurable_snd)).mul
              ((hb'meas.comp (measurable_const.sub (hvertm.comp measurable_fst))).mul
                (hexc.measurable.comp ha))
          have := hm1.aestronglyMeasurable.mul
            (hh.1.comp_fst (ν := (volume : Measure (E m))))
          refine this.congr (ae_of_all _ fun q => ?_)
          rcases q with ⟨y, ξ⟩
          simp only [Function.uncurry, Pi.mul_apply]
          ring
        · obtain ⟨y, ξ⟩ := q
          simp only [Function.uncurry_apply_pair, norm_mul, norm_ex, Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le, mul_one, gR]
          apply le_of_eq; ring
      calc conv (kb m b) h (mkPoint u xn)
          = ∫ y, ∫ ξ, (gR ξ : ℂ) * (b' (xn - vert y) *
              ex (-(‖(u - ξ) - horiz y‖ ^ 2 / (2 * (xn - vert y)))) * h y) :=
            integral_congr_ae (ae_of_all _ hpt)
        _ = ∫ ξ, ∫ y, (gR ξ : ℂ) * (b' (xn - vert y) *
              ex (-(‖(u - ξ) - horiz y‖ ^ 2 / (2 * (xn - vert y)))) * h y) :=
            integral_integral_swap hint
        _ = ∫ ξ, (gR ξ : ℂ) * G (u - ξ) := by
            refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
            simp only [hG_def]
            rw [integral_const_mul]
    have hGm : ∀ ξ : E m, Measurable (fun u : E m => ‖G (u - ξ)‖ₑ) := fun ξ =>
      (hGc.comp (continuous_id.sub continuous_const)).measurable.enorm
    calc ∫⁻ u in ball c L, ‖conv (kb m b) h (mkPoint u xn)‖ₑ ^ p
        ≤ ∫⁻ u in ball c L, ∫⁻ ξ, ENNReal.ofReal (gR ξ) * ‖G (u - ξ)‖ₑ ^ p := by
          refine lintegral_mono fun u => ?_
          rw [hrep u]
          calc ‖∫ ξ, (gR ξ : ℂ) * G (u - ξ)‖ₑ ^ p
              ≤ (∫⁻ ξ, ENNReal.ofReal (gR ξ) * ‖G (u - ξ)‖ₑ) ^ p := by
                refine ENNReal.rpow_le_rpow ((enorm_integral_le_lintegral_enorm _).trans
                  (le_of_eq ?_)) hp0.le
                refine lintegral_congr fun ξ => ?_
                rw [enorm_mul, hgen]
            _ ≤ _ := jensen volume hgm
                ((hGc.comp (continuous_const.sub continuous_id)).measurable.enorm)
                (lintegral_gauss m) p hp
      _ = ∫⁻ ξ, ENNReal.ofReal (gR ξ) * ∫⁻ u in ball c L, ‖G (u - ξ)‖ₑ ^ p := by
          rw [lintegral_lintegral_swap]
          · refine lintegral_congr fun ξ => ?_
            rw [lintegral_const_mul _ ((hGm ξ).pow_const p)]
          · exact ((hgm.comp measurable_snd).mul
              ((hGc.comp (continuous_fst.sub continuous_snd)).measurable.enorm.pow_const p)).aemeasurable
      _ ≤ ∫⁻ ξ, ENNReal.ofReal (gR ξ) * (A * ∫⁻ w, ‖H w‖ₑ ^ p) := by
          gcongr with ξ
          have := lintegral_ball_sub c ξ L (fun v => ‖G v‖ₑ ^ p)
          rw [this]; exact hball _
      _ = A * ∫⁻ w, ‖H w‖ₑ ^ p := by
          rw [lintegral_mul_const _ hgm, lintegral_gauss, one_mul]
      _ = _ := by rw [hHnorm]
  -- the vertical integral
  have hvert : ∀ t : ℝ, ∫⁻ xn : ℝ, ‖b' (xn - t)‖ₑ ^ p * ENNReal.ofReal (|xn - t| ^ e) ≤
      ENNReal.ofReal (M' ^ p * L ^ e * (2 * L)) := by
    intro t
    calc ∫⁻ xn : ℝ, ‖b' (xn - t)‖ₑ ^ p * ENNReal.ofReal (|xn - t| ^ e)
        ≤ ∫⁻ xn : ℝ, (Icc (t - L) (t + L)).indicator
            (fun _ => ENNReal.ofReal (M' ^ p * L ^ e)) xn := by
          refine lintegral_mono fun xn => ?_
          by_cases hz : b' (xn - t) = 0
          · simp [hz, ENNReal.zero_rpow_of_pos hp0]
          obtain ⟨-, h2⟩ := hb's _ hz
          have hmem : xn ∈ Icc (t - L) (t + L) := by
            rw [abs_le] at h2; constructor <;> linarith [h2.1, h2.2]
          rw [indicator_of_mem hmem, ENNReal.ofReal_mul (by positivity)]
          refine mul_le_mul' ?_ ?_
          · rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
            exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) (hb'M _) hp0.le)
          · exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) h2 he0)
      _ = ENNReal.ofReal (M' ^ p * L ^ e * (2 * L)) := by
          rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  have hmeas2 : AEMeasurable (Function.uncurry fun (xn : ℝ) (y : E (m + 1)) =>
      ‖b' (xn - vert y)‖ₑ ^ p * ENNReal.ofReal (|xn - vert y| ^ e) * ‖h y‖ₑ ^ p)
      ((volume : Measure ℝ).prod volume) := by
    have hs : Measurable (fun q : ℝ × E (m + 1) => q.1 - vert q.2) :=
      measurable_fst.sub (hvertm.comp measurable_snd)
    have h1 : Measurable (fun q : ℝ × E (m + 1) =>
        ‖b' (q.1 - vert q.2)‖ₑ ^ p * ENNReal.ofReal (|q.1 - vert q.2| ^ e)) :=
      ((hb'meas.comp hs).enorm.pow_const p).mul ((hs.abs.pow_const e).ennreal_ofReal)
    exact h1.aemeasurable.mul ((hh.1.enorm.pow_const p).comp_snd)
  have hA : ENNReal.ofReal (C₁ * L ^ ((m : ℝ) - ((m : ℝ) + 2) * (p - 1))) *
      ENNReal.ofReal (M' ^ p * L ^ e * (2 * L)) =
      ENNReal.ofReal (C₁ * 2 * 2 ^ ((m : ℝ) * p / 2) * M ^ p *
        L ^ ((m : ℝ) + 1 - (m : ℝ) * p / 2)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hL1 : L ^ ((m : ℝ) - e) * L ^ e * L * L ^ (-((m : ℝ) / 2) * p) =
        L ^ ((m : ℝ) + 1 - (m : ℝ) * p / 2) := by
      rw [show L ^ ((m : ℝ) - e) * L ^ e * L * L ^ (-((m : ℝ) / 2) * p) =
          L ^ ((m : ℝ) - e) * L ^ e * L ^ (1 : ℝ) * L ^ (-((m : ℝ) / 2) * p) by
        rw [Real.rpow_one]]
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
      congr 1; ring
    have h2 : ((2 : ℝ) ^ (-((m : ℝ) / 2) * p))⁻¹ = 2 ^ ((m : ℝ) * p / 2) := by
      rw [← Real.rpow_neg (by norm_num)]; congr 1; ring
    rw [hM'_def, Real.mul_rpow hM (by positivity), ← Real.rpow_mul (by positivity),
      Real.div_rpow hL0.le (by norm_num), ← hL1, ← h2]
    rw [div_eq_mul_inv]; ring
  calc ∫⁻ x in {x : E (m + 1) | horiz x ∈ ball c L}, ‖conv (kb m b) h x‖ₑ ^ p
      ≤ ∫⁻ xn : ℝ, ∫⁻ u in ball c L, ‖conv (kb m b) h (mkPoint u xn)‖ₑ ^ p :=
        lintegral_slab_le c L _
    _ ≤ ∫⁻ xn : ℝ, ENNReal.ofReal (C₁ * L ^ ((m : ℝ) - ((m : ℝ) + 2) * (p - 1))) *
        ∫⁻ y, ‖b' (xn - vert y)‖ₑ ^ p * ENNReal.ofReal (|xn - vert y| ^ e) * ‖h y‖ₑ ^ p :=
        lintegral_mono key
    _ = ENNReal.ofReal (C₁ * L ^ ((m : ℝ) - ((m : ℝ) + 2) * (p - 1))) *
        ∫⁻ y, (∫⁻ xn : ℝ, ‖b' (xn - vert y)‖ₑ ^ p * ENNReal.ofReal (|xn - vert y| ^ e)) *
          ‖h y‖ₑ ^ p := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hmeas2]
        congr 1
        refine lintegral_congr fun y => ?_
        rw [lintegral_mul_const]
        exact ((hb'meas.comp (measurable_id.sub_const _)).enorm.pow_const p).mul
          (((measurable_id.sub_const _).abs.pow_const e).ennreal_ofReal)
    _ ≤ ENNReal.ofReal (C₁ * L ^ ((m : ℝ) - ((m : ℝ) + 2) * (p - 1))) *
        ∫⁻ y, ENNReal.ofReal (M' ^ p * L ^ e * (2 * L)) * ‖h y‖ₑ ^ p := by
        gcongr with y
        exact hvert (vert y)
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, hA]

end TaoBR.Carb.PartN
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
/-! ## Part N: the near estimate -/
alias near_bound := TaoBR.Carb.PartN.near_bound

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartP
open Filter
variable {m : ℕ}
@[simp] theorem horiz_add (y y' : E (m + 1)) : horiz (y + y') = horiz y + horiz y' := by
  ext i; simp

@[simp] theorem horiz_sub (y y' : E (m + 1)) : horiz (y - y') = horiz y - horiz y' := by
  ext i; simp

@[simp] theorem horiz_smul (r : ℝ) (y : E (m + 1)) : horiz (r • y) = r • horiz y := by
  ext i; simp

@[simp] theorem vert_add (y y' : E (m + 1)) : vert (y + y') = vert y + vert y' := by
  simp [vert]

@[simp] theorem vert_sub (y y' : E (m + 1)) : vert (y - y') = vert y - vert y' := by
  simp [vert]

@[simp] theorem vert_smul (r : ℝ) (y : E (m + 1)) : vert (r • y) = r * vert y := by
  simp [vert]

theorem continuous_horiz : Continuous (horiz : E (m + 1) → E m) := by
  unfold horiz; fun_prop

theorem continuous_vert : Continuous (vert : E (m + 1) → ℝ) := by
  unfold vert; fun_prop

theorem continuous_mkPoint : Continuous fun q : E m × ℝ => mkPoint q.1 q.2 := by
  unfold mkPoint
  apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  induction i using Fin.lastCases with
  | last => simp; fun_prop
  | cast j => simp; fun_prop

theorem measurable_mkPoint : Measurable fun q : E m × ℝ => mkPoint q.1 q.2 :=
  continuous_mkPoint.measurable

end TaoBR.Carb.PartP
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartP
open Filter
/-! ## Fubini in `ℝ^{m+1} = ℝ^m × ℝ` -/
theorem measurePreserving_mkPoint (m : ℕ) :
    MeasurePreserving (fun q : E m × ℝ => mkPoint q.1 q.2) (volume.prod volume) volume := by
  have h1 : MeasurePreserving (Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ))
      ((volume : Measure (E m)).prod (volume : Measure ℝ)) (volume.prod volume) :=
    (PiLp.volume_preserving_ofLp (Fin m)).prod (MeasurePreserving.id volume)
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin m → ℝ)))
    (ν := (volume : Measure ℝ)))
  have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
  have h4 := PiLp.volume_preserving_toLp (Fin (m + 1))
  have h := h4.comp (h3.comp (h2.comp h1))
  have heq : (fun q : E m × ℝ => mkPoint q.1 q.2) = (WithLp.toLp 2 ∘
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm ∘
        Prod.swap ∘ Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ)) := by
    funext q
    apply ext_hv
    · ext i; simp [Function.comp]
    · simp [vert, Function.comp]
  rw [heq]; exact h

/-- (Part B1) Fubini in the coordinates `ℝ^{m+1} = ℝ^m × ℝ`. -/
theorem lintegral_mkPoint (m : ℕ) (F : E (m + 1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ u, ∫⁻ h, F (mkPoint u h) := by
  rw [← (measurePreserving_mkPoint m).lintegral_comp hF]
  exact lintegral_prod _ (hF.comp measurable_mkPoint).aemeasurable

/-! ## Averaging over centres of horizontal balls -/
theorem avg_eq (m : ℕ) (F : E (m + 1) → ℝ≥0∞) (hF : AEMeasurable F) (R : ℝ) :
    AEMeasurable (fun c : E m => ∫⁻ x in {x : E (m + 1) | horiz x ∈ ball c R}, F x) ∧
    ∫⁻ c : E m, ∫⁻ x in {x : E (m + 1) | horiz x ∈ ball c R}, F x =
      volume (ball (0 : E m) R) * ∫⁻ x, F x := by
  set S : Set (E m × E (m + 1)) := {q | dist (horiz q.2) q.1 < R} with hS
  have hSm : MeasurableSet S :=
    (isOpen_lt (continuous_dist.comp ((continuous_horiz.comp continuous_snd).prodMk
      continuous_fst)) continuous_const).measurableSet
  set g : E m × E (m + 1) → ℝ≥0∞ := S.indicator (fun q => F q.2) with hg
  have hgm : AEMeasurable g ((volume : Measure (E m)).prod volume) :=
    (hF.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).indicator hSm
  have key : ∀ c : E m, ∫⁻ x in {x : E (m + 1) | horiz x ∈ ball c R}, F x =
      ∫⁻ x, g (c, x) := by
    intro c
    have hm : MeasurableSet {x : E (m + 1) | horiz x ∈ ball c R} :=
      (isOpen_ball.preimage continuous_horiz).measurableSet
    rw [← lintegral_indicator hm]
    rfl
  simp_rw [key]
  refine ⟨hgm.lintegral_prod_right', ?_⟩
  rw [lintegral_lintegral_swap (f := fun c x => g (c, x)) hgm]
  have inner : ∀ x : E (m + 1), ∫⁻ c, g (c, x) = F x * volume (ball (0 : E m) R) := by
    intro x
    have : (fun c => g (c, x)) = (ball (horiz x) R).indicator (fun _ => F x) := by
      funext c; simp only [hg, Set.indicator, hS, Set.mem_ofPred_eq, mem_ball, dist_comm]
    rw [this, lintegral_indicator_const measurableSet_ball, Measure.addHaar_ball_center]
  simp_rw [inner]
  rw [lintegral_mul_const' _ _ measure_ball_lt_top.ne, mul_comm]

/-! ## `L¹` norms of truncated kernels -/
theorem gauss_lint (m : ℕ) (T : ℝ) (hT : 0 < T) :
    ∫⁻ u : E m, ENNReal.ofReal (Real.exp (-(Real.pi / (4 * T ^ 2)) * ‖u‖ ^ 2)) =
      ENNReal.ofReal ((2 * T) ^ m) := by
  have ha : (0 : ℝ) < Real.pi / (4 * T ^ 2) := by positivity
  have hI : Integrable (fun u : E m => Real.exp (-(Real.pi / (4 * T ^ 2)) * ‖u‖ ^ 2)) := by
    have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := ((Real.pi / (4 * T ^ 2) : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; exact ha) 0 (0 : E m)).re
    refine this.congr (ae_of_all _ fun u => ?_)
    simp only [zero_mul, add_zero]
    rw [show (-((Real.pi / (4 * T ^ 2) : ℝ) : ℂ) * (‖u‖ : ℂ) ^ 2) =
      ((-(Real.pi / (4 * T ^ 2)) * ‖u‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_exp]; exact Complex.ofReal_re _
  rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun u => (Real.exp_pos _).le),
    GaussianFourier.integral_rexp_neg_mul_sq_norm ha, finrank_euclideanSpace_fin]
  congr 1
  have h4 : Real.pi / (Real.pi / (4 * T ^ 2)) = (2 * T) ^ (2 : ℝ) := by
    rw [Real.rpow_two]; field_simp; ring
  rw [h4, ← Real.rpow_mul (by positivity)]
  rw [show (2 : ℝ) * ((m : ℝ) / 2) = (m : ℝ) by ring, Real.rpow_natCast]

theorem kern_L1 (m : ℕ) (b : ℝ → ℂ) (_hb : Measurable b) (B T ρ : ℝ) (hB : 0 ≤ B) (hT : 1 ≤ T)
    (hρ : 0 ≤ ρ) (hbB : ∀ t, ‖b t‖ ≤ B) (hbs : ∀ t, b t ≠ 0 → |t| ≤ T) :
    ∫⁻ z, {z : E (m + 1) | ρ ≤ ‖horiz z‖}.indicator (fun z => ‖kb m b z‖ₑ) z ≤
      ENNReal.ofReal (B * Real.exp (-(Real.pi * ρ ^ 2 / (4 * T ^ 2))) * (2 * T) * (2 * T) ^ m) := by
  have hT0 : 0 < T := by linarith
  set a : ℝ := Real.pi / (4 * T ^ 2) with ha_def
  set eρ : ℝ := Real.exp (-(Real.pi * ρ ^ 2 / (4 * T ^ 2))) with heρ
  set D : E (m + 1) → ℝ≥0∞ := fun z => ENNReal.ofReal (B * eρ) *
     ((Icc (-T) T).indicator (fun _ => (1 : ℝ≥0∞)) (vert z) *
       ENNReal.ofReal (Real.exp (-a * ‖horiz z‖ ^ 2))) with hD
  have hDm : Measurable D := by
    refine measurable_const.mul (Measurable.mul ?_ ?_)
    · exact (measurable_const.indicator measurableSet_Icc).comp continuous_vert.measurable
    · exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
        ((continuous_norm.comp continuous_horiz).measurable.pow_const 2)))
  have hpt : ∀ z, {z : E (m + 1) | ρ ≤ ‖horiz z‖}.indicator (fun z => ‖kb m b z‖ₑ) z ≤ D z := by
    intro z
    by_cases hz : ρ ≤ ‖horiz z‖
    swap
    · rw [Set.indicator_of_notMem (s := {z : E (m + 1) | ρ ≤ ‖horiz z‖}) hz]; exact zero_le
    rw [Set.indicator_of_mem (s := {z : E (m + 1) | ρ ≤ ‖horiz z‖}) hz]
    by_cases hb0 : b (vert z) = 0
    · simp [kb, hb0]
    have ht := hbs _ hb0
    have hmem : vert z ∈ Icc (-T) T := abs_le.1 ht
    simp only [hD, Set.indicator_of_mem hmem, one_mul]
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    set t := vert z
    set d := horiz z
    have hE := Eg_norm m d t
    have h1 : (1 + t ^ 2) ^ (-((m : ℝ) / 4)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by
        have : (0:ℝ) ≤ m := Nat.cast_nonneg m
        linarith)
    have ht2 : t ^ 2 ≤ T ^ 2 := by
      have := abs_le.1 ht
      nlinarith
    have h2 : Real.exp (-(Real.pi * ‖d‖ ^ 2 / (1 + t ^ 2))) ≤ eρ * Real.exp (-a * ‖d‖ ^ 2) := by
      rw [heρ, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have hρd : ρ ^ 2 ≤ ‖d‖ ^ 2 := pow_le_pow_left₀ hρ hz 2
      have hden : 1 + t ^ 2 ≤ 2 * T ^ 2 := by nlinarith
      have h3 : Real.pi * ‖d‖ ^ 2 / (2 * T ^ 2) ≤ Real.pi * ‖d‖ ^ 2 / (1 + t ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      have h4 : Real.pi * ρ ^ 2 / (4 * T ^ 2) ≤ Real.pi * ‖d‖ ^ 2 / (4 * T ^ 2) := by gcongr
      have h5 : Real.pi * ‖d‖ ^ 2 / (2 * T ^ 2) =
          Real.pi * ‖d‖ ^ 2 / (4 * T ^ 2) + a * ‖d‖ ^ 2 := by
        rw [ha_def]; field_simp; ring
      have h6 : -a * ‖d‖ ^ 2 = -(a * ‖d‖ ^ 2) := by ring
      rw [h6]
      linarith
    calc ‖kb m b z‖ = ‖b t‖ * ‖Eg m d t‖ := by simp [kb, t, d]
      _ ≤ B * ((1 + t ^ 2) ^ (-((m : ℝ) / 4)) * Real.exp (-(Real.pi * ‖d‖ ^ 2 / (1 + t ^ 2)))) :=
          mul_le_mul (hbB _) hE (norm_nonneg _) hB
      _ ≤ B * (1 * (eρ * Real.exp (-a * ‖d‖ ^ 2))) := by
          gcongr
      _ = B * eρ * Real.exp (-a * ‖d‖ ^ 2) := by ring
  have hin : ∀ u : E m, ∫⁻ t : ℝ, ENNReal.ofReal (B * eρ) *
      ((Icc (-T) T).indicator (fun _ => (1 : ℝ≥0∞)) t *
        ENNReal.ofReal (Real.exp (-a * ‖u‖ ^ 2))) =
      ENNReal.ofReal (B * eρ) * ENNReal.ofReal (Real.exp (-a * ‖u‖ ^ 2)) *
        ENNReal.ofReal (2 * T) := by
    intro u
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      lintegral_indicator_const measurableSet_Icc, one_mul, Real.volume_Icc,
      show T - -T = 2 * T by ring]
    ring
  calc _ ≤ ∫⁻ z, D z := lintegral_mono hpt
    _ = _ := by
      rw [lintegral_mkPoint m D hDm]
      simp only [hD, horiz_mkPoint, vert_mkPoint]
      simp_rw [hin]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, gauss_lint m T hT0,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-! ## `Lᵖ` bookkeeping -/
theorem lint_eLp {n : ℕ} (p : ℝ) (hp : 1 ≤ p) (g : E n → ℂ) :
    ∫⁻ x, ‖g x‖ₑ ^ p = eLpNorm g (ENNReal.ofReal p) volume ^ p := by
  have hp0 : 0 < p := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul]
  rw [show 1 / p * p = 1 by field_simp, ENNReal.rpow_one]

theorem eLp_of_lint {n : ℕ} (p : ℝ) (hp : 1 ≤ p) (g f : E n → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (h : ∫⁻ x, ‖g x‖ₑ ^ p ≤ ENNReal.ofReal A * ∫⁻ x, ‖f x‖ₑ ^ p) :
    eLpNorm g (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (A ^ (1 / p)) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  rw [lint_eLp p hp, lint_eLp p hp] at h
  rw [← ENNReal.rpow_le_rpow_iff hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, ← Real.rpow_mul hA,
    show 1 / p * p = 1 by field_simp, Real.rpow_one]
  exact h

theorem lintegral_enorm_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} (g : α → ℝ)
    (hg0 : ∀ a, 0 ≤ g a) (hg : Integrable (fun a => (g a : ℂ)) μ) :
    ∫⁻ a, ‖(g a : ℂ)‖ₑ ∂μ = ‖∫ a, (g a : ℂ) ∂μ‖ₑ := by
  have hgi : Integrable g μ := by simpa using hg.re
  have h1 : ∀ r : ℝ, 0 ≤ r → ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
    intro r hr
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr]
  rw [integral_complex_ofReal, h1 _ (integral_nonneg hg0),
    ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0)]
  exact lintegral_congr fun a => h1 _ (hg0 a)

/-! ## The core estimate for one dyadic piece -/
theorem core (m : ℕ) (p : ℝ) (hp : 1 ≤ p) (CN : ℝ) (hCN : 0 ≤ CN)
    (hN : ∀ L : ℝ, 1 ≤ L → ∀ M : ℝ, 0 ≤ M → ∀ b : ℝ → ℂ, Measurable b →
      (∀ t, ‖b t‖ ≤ M) → (∀ t, b t ≠ 0 → L / 2 ≤ |t| ∧ |t| ≤ L) →
      ∀ c : E m, ∀ h : E (m + 1) → ℂ, MemLp h (ENNReal.ofReal p) volume →
        (∃ R : ℝ, ∀ y, R < ‖horiz y‖ → h y = 0) →
        ∫⁻ x in {x : E (m + 1) | horiz x ∈ ball c L}, ‖conv (kb m b) h x‖ₑ ^ p ≤
          ENNReal.ofReal (CN * M ^ p * L ^ ((m : ℝ) + 1 - (m : ℝ) * p / 2)) * ∫⁻ y, ‖h y‖ₑ ^ p)
    (L K M : ℝ) (hL : 1 ≤ L) (hK : 1 ≤ K) (hM : 0 ≤ M) (b : ℝ → ℂ) (hb : Measurable b)
    (hbM : ∀ t, ‖b t‖ ≤ M) (hbs : ∀ t, b t ≠ 0 → L / 2 ≤ |t| ∧ |t| ≤ L)
    (f : E (m + 1) → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∫⁻ x, ‖conv (kb m b) f x‖ₑ ^ p ≤
      ENNReal.ofReal (2 ^ (p - 1) * (CN * M ^ p * L ^ ((m : ℝ) + 1 - (m : ℝ) * p / 2) * K ^ m +
        (M * Real.exp (-(Real.pi * ((K - 1) * L) ^ 2 / (4 * L ^ 2))) * (2 * L) * (2 * L) ^ m)
          ^ p)) * ∫⁻ y, ‖f y‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have h1p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have hL0 : 0 < L := by linarith
  set e : ℝ := (m : ℝ) + 1 - (m : ℝ) * p / 2 with he
  set A : ℝ := CN * M ^ p * L ^ e with hA
  set ρ : ℝ := (K - 1) * L with hρ
  have hρ0 : 0 ≤ ρ := mul_nonneg (by linarith) hL0.le
  set Kf : ℝ := M * Real.exp (-(Real.pi * ρ ^ 2 / (4 * L ^ 2))) * (2 * L) * (2 * L) ^ m with hKf
  have hkI : Integrable (kb m b) := kb_integrable m b hb M L hbM (fun t ht => (hbs t ht).2)
  have hρm : MeasurableSet {z : E (m + 1) | ρ ≤ ‖horiz z‖} :=
    (isClosed_le continuous_const (continuous_norm.comp continuous_horiz)).measurableSet
  set kfr : E (m + 1) → ℝ :=
    {z : E (m + 1) | ρ ≤ ‖horiz z‖}.indicator (fun z => ‖kb m b z‖) with hkfr
  have hkfr0 : ∀ z, 0 ≤ kfr z := fun z => Set.indicator_nonneg (fun z _ => norm_nonneg _) z
  set kf : E (m + 1) → ℂ := fun z => ((kfr z : ℝ) : ℂ) with hkf
  set F : E (m + 1) → ℂ := fun y => ((‖f y‖ : ℝ) : ℂ) with hF
  have hFm : MemLp F (ENNReal.ofReal p) volume := hf.norm.ofReal
  have hkfI : Integrable kf := (hkI.norm.indicator hρm).ofReal
  have hkf1 : eLpNorm kf 1 volume ≤ ENNReal.ofReal Kf := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine le_trans (le_of_eq (lintegral_congr fun z => ?_))
      (kern_L1 m b hb M L ρ hM hL hρ0 hbM (fun t ht => (hbs t ht).2))
    by_cases hz : z ∈ {z : E (m + 1) | ρ ≤ ‖horiz z‖}
    · simp only [hkf, hkfr, Set.indicator_of_mem hz, ← ofReal_norm, Complex.norm_real, norm_norm]
    · simp only [hkf, hkfr, Set.indicator_of_notMem hz, Complex.ofReal_zero, enorm_zero]
  obtain ⟨hYae, hYm, hYb⟩ := conv_basic kf hkfI (ENNReal.ofReal p) h1p F hFm.1
  have hYae' := hYae hFm
  set G : E (m + 1) → ℝ≥0∞ := fun x => ‖conv kf F x‖ₑ with hG
  have hGm : AEMeasurable (fun x => G x ^ p) := hYm.enorm.pow_const p
  have hGb : ∫⁻ x, G x ^ p ≤ ENNReal.ofReal Kf ^ p * ∫⁻ y, ‖f y‖ₑ ^ p := by
    have hFn : eLpNorm F (ENNReal.ofReal p) volume = eLpNorm f (ENNReal.ofReal p) volume :=
      eLpNorm_congr_norm_ae (ae_of_all _ fun y => by simp [hF])
    rw [lint_eLp p hp (conv kf F), lint_eLp p hp f, ← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    refine ENNReal.rpow_le_rpow (hYb.trans ?_) hp0.le
    rw [hFn]
    gcongr
  have h2top : (2 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  have hc : ∀ c : E m, ∫⁻ x in {x : E (m + 1) | horiz x ∈ ball c L}, ‖conv (kb m b) f x‖ₑ ^ p ≤
      2 ^ (p - 1) * (ENNReal.ofReal A *
        (∫⁻ y in {y : E (m + 1) | horiz y ∈ ball c (K * L)}, ‖f y‖ₑ ^ p) +
        ∫⁻ x in {x : E (m + 1) | horiz x ∈ ball c L}, G x ^ p) := by
    intro c
    set s := {x : E (m + 1) | horiz x ∈ ball c L} with hs
    set n := {y : E (m + 1) | horiz y ∈ ball c (K * L)} with hn
    have hsm : MeasurableSet s := (isOpen_ball.preimage continuous_horiz).measurableSet
    have hnm : MeasurableSet n := (isOpen_ball.preimage continuous_horiz).measurableSet
    set fN := n.indicator f with hfN
    set fF := nᶜ.indicator f with hfF
    have hfNm : MemLp fN (ENNReal.ofReal p) volume := hf.indicator hnm
    have hfFm : MemLp fF (ENNReal.ofReal p) volume := hf.indicator hnm.compl
    have ae1 := (conv_basic (kb m b) hkI _ h1p fN hfNm.1).1 hfNm
    have ae2 := (conv_basic (kb m b) hkI _ h1p fF hfFm.1).1 hfFm
    have hpt : ∀ᵐ x ∂(volume.restrict s), ‖conv (kb m b) f x‖ₑ ^ p ≤
        2 ^ (p - 1) * (‖conv (kb m b) fN x‖ₑ ^ p + G x ^ p) := by
      rw [ae_restrict_iff' hsm]
      filter_upwards [ae1, ae2, hYae'] with x h1 h2 h3 hx
      have hsplit : conv (kb m b) f x = conv (kb m b) fN x + conv (kb m b) fF x := by
        simp only [conv]
        rw [← integral_add h1 h2]
        congr 1; funext y
        rw [← mul_add]
        simp only [hfN, hfF, Set.indicator_self_add_compl_apply]
      have hptw : ∀ y, ‖kb m b (x - y) * fF y‖ₑ ≤ ‖((kfr (x - y) * ‖f y‖ : ℝ) : ℂ)‖ₑ := by
        intro y
        by_cases hy : y ∈ n
        · simp [hfF, hy]
        · have hmem : x - y ∈ {z : E (m + 1) | ρ ≤ ‖horiz z‖} := by
            have hx' : dist (horiz x) c < L := hx
            have hy' : K * L ≤ dist (horiz y) c := by
              simpa [hn, mem_ball] using hy
            have htri := dist_triangle (horiz y) (horiz x) c
            show ρ ≤ ‖horiz (x - y)‖
            rw [horiz_sub, ← dist_eq_norm, dist_comm, hρ]
            nlinarith
          rw [hfF, Set.indicator_of_mem (show y ∈ nᶜ from hy), hkfr,
            Set.indicator_of_mem (s := {z : E (m + 1) | ρ ≤ ‖horiz z‖}) hmem]
          simp only [Complex.ofReal_mul, enorm_mul]
          apply le_of_eq
          simp only [← ofReal_norm, Complex.norm_real, norm_norm]
      have h3' : Integrable (fun y => ((kfr (x - y) * ‖f y‖ : ℝ) : ℂ)) := by
        refine h3.congr (ae_of_all _ fun y => ?_)
        simp [hkf, hF]
      have hfar : ‖conv (kb m b) fF x‖ₑ ≤ G x := by
        calc ‖conv (kb m b) fF x‖ₑ ≤ ∫⁻ y, ‖kb m b (x - y) * fF y‖ₑ :=
              enorm_integral_le_lintegral_enorm _
          _ ≤ ∫⁻ y, ‖((kfr (x - y) * ‖f y‖ : ℝ) : ℂ)‖ₑ := lintegral_mono hptw
          _ = ‖∫ y, ((kfr (x - y) * ‖f y‖ : ℝ) : ℂ)‖ₑ :=
              lintegral_enorm_ofReal _ (fun y => mul_nonneg (hkfr0 _) (norm_nonneg _)) h3'
          _ = G x := by
              simp only [hG, conv, hkf, hF]
              congr 2
              funext y
              push_cast
              ring
      calc ‖conv (kb m b) f x‖ₑ ^ p = ‖conv (kb m b) fN x + conv (kb m b) fF x‖ₑ ^ p := by
            rw [hsplit]
        _ ≤ (‖conv (kb m b) fN x‖ₑ + G x) ^ p :=
            ENNReal.rpow_le_rpow ((enorm_add_le _ _).trans (add_le_add le_rfl hfar)) hp0.le
        _ ≤ _ := ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
    have hsupp : ∀ y, ‖c‖ + K * L < ‖horiz y‖ → fN y = 0 := by
      intro y hy
      have : y ∉ n := by
        simp only [hn, Set.mem_ofPred_eq, mem_ball, not_lt]
        rw [dist_eq_norm]
        linarith [norm_sub_norm_le (horiz y) c]
      simp [hfN, this]
    have hnear := hN L hL M hM b hb hbM hbs c fN hfNm ⟨‖c‖ + K * L, hsupp⟩
    have hfNint : ∫⁻ y, ‖fN y‖ₑ ^ p = ∫⁻ y in n, ‖f y‖ₑ ^ p := by
      rw [← lintegral_indicator hnm]
      congr 1; funext y
      simp only [hfN, Set.indicator]
      split_ifs <;> simp [ENNReal.zero_rpow_of_pos hp0]
    calc ∫⁻ x in s, ‖conv (kb m b) f x‖ₑ ^ p
        ≤ ∫⁻ x in s, 2 ^ (p - 1) * (‖conv (kb m b) fN x‖ₑ ^ p + G x ^ p) := lintegral_mono_ae hpt
      _ = 2 ^ (p - 1) * ((∫⁻ x in s, ‖conv (kb m b) fN x‖ₑ ^ p) + ∫⁻ x in s, G x ^ p) := by
          rw [lintegral_const_mul' _ _ h2top, lintegral_add_right' _ hGm.restrict]
      _ ≤ _ := by
          rw [← hfNint]
          gcongr
  have hconvm : AEMeasurable (fun x => ‖conv (kb m b) f x‖ₑ ^ p) :=
    (conv_basic (kb m b) hkI _ h1p f hf.1).2.1.enorm.pow_const p
  have hfm : AEMeasurable (fun y => ‖f y‖ₑ ^ p) := hf.1.enorm.pow_const p
  obtain ⟨-, hav1⟩ := avg_eq m _ hconvm L
  obtain ⟨hav2m, hav2⟩ := avg_eq m _ hfm (K * L)
  obtain ⟨-, hav3⟩ := avg_eq m _ hGm L
  have hball : volume (ball (0 : E m) (K * L)) =
      ENNReal.ofReal (K ^ m) * volume (ball (0 : E m) L) := by
    rw [Measure.addHaar_ball_mul_of_pos _ _ (by linarith : (0 : ℝ) < K), finrank_euclideanSpace_fin]
  have hB0 : volume (ball (0 : E m) L) ≠ 0 := (measure_ball_pos _ _ hL0).ne'
  have hBt : volume (ball (0 : E m) L) ≠ ⊤ := measure_ball_lt_top.ne
  have key : volume (ball (0 : E m) L) * ∫⁻ x, ‖conv (kb m b) f x‖ₑ ^ p ≤
      volume (ball (0 : E m) L) * (ENNReal.ofReal (2 ^ (p - 1) * (A * K ^ m + Kf ^ p)) *
        ∫⁻ y, ‖f y‖ₑ ^ p) := by
    rw [← hav1]
    calc _ ≤ ∫⁻ c : E m, 2 ^ (p - 1) * (ENNReal.ofReal A *
          (∫⁻ y in {y : E (m + 1) | horiz y ∈ ball c (K * L)}, ‖f y‖ₑ ^ p) +
          ∫⁻ x in {x : E (m + 1) | horiz x ∈ ball c L}, G x ^ p) := lintegral_mono hc
      _ = 2 ^ (p - 1) * (ENNReal.ofReal A * (∫⁻ c : E m,
          ∫⁻ y in {y : E (m + 1) | horiz y ∈ ball c (K * L)}, ‖f y‖ₑ ^ p) +
          ∫⁻ c : E m, ∫⁻ x in {x : E (m + 1) | horiz x ∈ ball c L}, G x ^ p) := by
          rw [lintegral_const_mul' _ _ h2top, lintegral_add_left' (hav2m.const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ 2 ^ (p - 1) * (ENNReal.ofReal A * (ENNReal.ofReal (K ^ m) *
          volume (ball (0 : E m) L) * (∫⁻ y, ‖f y‖ₑ ^ p)) +
          volume (ball (0 : E m) L) * (ENNReal.ofReal Kf ^ p * ∫⁻ y, ‖f y‖ₑ ^ p)) := by
          rw [hav2, hav3, hball]
          gcongr
      _ = _ := by
          rw [ENNReal.ofReal_mul (p := (2 : ℝ) ^ (p - 1)) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (p := A) (by positivity),
            ← ENNReal.ofReal_rpow_of_nonneg (x := Kf) (by positivity) hp0.le,
            ← ENNReal.ofReal_rpow_of_pos (x := 2) (by norm_num)]
          simp only [ENNReal.ofReal_ofNat]
          ring
  exact (ENNReal.mul_le_mul_iff_right hB0 hBt).1 key

/-! ## The constants -/
theorem const_bound (m : ℕ) (p δ : ℝ) (hp : 1 ≤ p) (_hδ : 0 ≤ δ) (hc : 0 ≤ critE m p)
    (CN : ℝ) (hCN : 0 ≤ CN) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (M : ℝ), 0 ≤ M →
      (2 ^ (p - 1) * (CN * (M * 2 ^ (δ + 1) * ((2 : ℝ) ^ j) ^ (-(δ + 1))) ^ p *
          ((2 : ℝ) ^ j) ^ ((m : ℝ) + 1 - (m : ℝ) * p / 2) * ((j : ℝ) + 2) ^ m +
        (M * 2 ^ (δ + 1) * ((2 : ℝ) ^ j) ^ (-(δ + 1)) *
          Real.exp (-(Real.pi * (((j : ℝ) + 2 - 1) * (2 : ℝ) ^ j) ^ 2 / (4 * ((2 : ℝ) ^ j) ^ 2))) *
          (2 * (2 : ℝ) ^ j) * (2 * (2 : ℝ) ^ j) ^ m) ^ p)) ^ (1 / p) ≤
        C * M * ((j : ℝ) + 1) ^ m * (2 : ℝ) ^ ((j : ℝ) * (critE m p - δ)) := by
  have hp0 : 0 < p := by linarith
  set c := critE m p with hc_def
  set C1 : ℝ := CN * (2 : ℝ) ^ ((δ + 1) * p) * 2 ^ m with hC1
  set C2 : ℝ := (2 : ℝ) ^ (δ + 1) * 2 ^ (m + 1) * Real.exp ((m : ℝ) ^ 2) with hC2
  have hC1n : 0 ≤ C1 := by positivity
  have hC2n : 0 ≤ C2 := by positivity
  refine ⟨(2 ^ (p - 1) * (C1 + C2 ^ p)) ^ (1 / p), by positivity, ?_⟩
  intro j M hM
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h2L : (2 : ℝ) ^ ((j : ℝ) * (c - δ)) = ((2 : ℝ) ^ j) ^ (c - δ) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [h2L]
  set L : ℝ := (2 : ℝ) ^ j with hL
  have hL1 : 1 ≤ L := one_le_pow₀ (by norm_num)
  have hL0 : 0 < L := by positivity
  set Q : ℝ := M * ((j : ℝ) + 1) ^ m * L ^ (c - δ) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hj1 : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ m := one_le_pow₀ (by linarith)
  set Mj : ℝ := M * 2 ^ (δ + 1) * L ^ (-(δ + 1)) with hMj
  have hMj0 : 0 ≤ Mj := by positivity
  -- near part
  have hNb : CN * Mj ^ p * L ^ ((m : ℝ) + 1 - (m : ℝ) * p / 2) * ((j : ℝ) + 2) ^ m ≤
      C1 * Q ^ p := by
    have hexp : -(δ + 1) * p + ((m : ℝ) + 1 - (m : ℝ) * p / 2) = (c - δ) * p := by
      rw [hc_def]; unfold critE; field_simp; ring
    have hK : ((j : ℝ) + 2) ^ m ≤ 2 ^ m * (((j : ℝ) + 1) ^ m) ^ p := by
      calc ((j : ℝ) + 2) ^ m ≤ (2 * ((j : ℝ) + 1)) ^ m := by gcongr; linarith
        _ = 2 ^ m * ((j : ℝ) + 1) ^ m := by rw [mul_pow]
        _ ≤ 2 ^ m * (((j : ℝ) + 1) ^ m) ^ p := by
          gcongr
          calc ((j : ℝ) + 1) ^ m = (((j : ℝ) + 1) ^ m) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hj1 hp
    have hMjp : Mj ^ p = M ^ p * (2 : ℝ) ^ ((δ + 1) * p) * L ^ (-(δ + 1) * p) := by
      rw [hMj, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hL0.le]
    have hQp : Q ^ p = M ^ p * (((j : ℝ) + 1) ^ m) ^ p * L ^ ((c - δ) * p) := by
      rw [hQ, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hL0.le]
    have hLL : L ^ (-(δ + 1) * p) * L ^ ((m : ℝ) + 1 - (m : ℝ) * p / 2) = L ^ ((c - δ) * p) := by
      rw [← Real.rpow_add hL0, hexp]
    rw [hMjp, hQp]
    calc CN * (M ^ p * (2 : ℝ) ^ ((δ + 1) * p) * L ^ (-(δ + 1) * p)) *
          L ^ ((m : ℝ) + 1 - (m : ℝ) * p / 2) * ((j : ℝ) + 2) ^ m
        = CN * M ^ p * (2 : ℝ) ^ ((δ + 1) * p) *
          (L ^ (-(δ + 1) * p) * L ^ ((m : ℝ) + 1 - (m : ℝ) * p / 2)) * ((j : ℝ) + 2) ^ m := by
          ring
      _ = CN * M ^ p * (2 : ℝ) ^ ((δ + 1) * p) * L ^ ((c - δ) * p) * ((j : ℝ) + 2) ^ m := by
          rw [hLL]
      _ ≤ CN * M ^ p * (2 : ℝ) ^ ((δ + 1) * p) * L ^ ((c - δ) * p) *
          (2 ^ m * (((j : ℝ) + 1) ^ m) ^ p) := by gcongr
      _ = _ := by rw [hC1]; ring
  -- far part
  have hFb : Mj * Real.exp (-(Real.pi * (((j : ℝ) + 2 - 1) * L) ^ 2 / (4 * L ^ 2))) *
      (2 * L) * (2 * L) ^ m ≤ C2 * Q := by
    have he : Real.pi * (((j : ℝ) + 2 - 1) * L) ^ 2 / (4 * L ^ 2) =
        Real.pi * ((j : ℝ) + 1) ^ 2 / 4 := by
      field_simp; ring
    rw [he]
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h1 : L ^ m ≤ Real.exp ((j : ℝ) * m) := by
      have : L ^ m ≤ Real.exp 1 ^ (j * m) := by
        rw [hL, ← pow_mul]; exact pow_le_pow_left₀ (by norm_num) h2e _
      rw [← Real.exp_nat_mul] at this
      simpa using this
    have hLm : L ^ m * Real.exp (-(Real.pi * ((j : ℝ) + 1) ^ 2 / 4)) ≤
        Real.exp ((m : ℝ) ^ 2) := by
      have hpij : (j : ℝ) ^ 2 ≤ Real.pi * ((j : ℝ) + 1) ^ 2 := by
        nlinarith [Real.pi_gt_three]
      calc L ^ m * Real.exp (-(Real.pi * ((j : ℝ) + 1) ^ 2 / 4))
          ≤ Real.exp ((j : ℝ) * m) * Real.exp (-(Real.pi * ((j : ℝ) + 1) ^ 2 / 4)) := by gcongr
        _ = Real.exp ((j : ℝ) * m + -(Real.pi * ((j : ℝ) + 1) ^ 2 / 4)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp ((m : ℝ) ^ 2) := by
          apply Real.exp_le_exp.2
          nlinarith [sq_nonneg ((m : ℝ) - (j : ℝ) / 2)]
    have hLd : L ^ (-(δ + 1)) * (2 * L) * (2 * L) ^ m = 2 ^ (m + 1) * L ^ (-δ) * L ^ m := by
      have : L ^ (-(δ + 1)) * L = L ^ (-δ) := by
        conv_lhs => rw [show L ^ (-(δ + 1)) * L = L ^ (-(δ + 1)) * L ^ (1 : ℝ) by
          rw [Real.rpow_one]]
        rw [← Real.rpow_add hL0]; ring_nf
      calc _ = 2 ^ (m + 1) * (L ^ (-(δ + 1)) * L) * L ^ m := by ring
        _ = _ := by rw [this]
    have hcd : L ^ (-δ) ≤ ((j : ℝ) + 1) ^ m * L ^ (c - δ) := by
      rw [sub_eq_add_neg, Real.rpow_add hL0]
      have h1c := one_le_mul_of_one_le_of_one_le hj1 (Real.one_le_rpow hL1 hc)
      have h0 : 0 ≤ L ^ (-δ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h1c h0]
    calc Mj * Real.exp (-(Real.pi * ((j : ℝ) + 1) ^ 2 / 4)) * (2 * L) * (2 * L) ^ m
        = M * 2 ^ (δ + 1) * (L ^ (-(δ + 1)) * (2 * L) * (2 * L) ^ m) *
          Real.exp (-(Real.pi * ((j : ℝ) + 1) ^ 2 / 4)) := by rw [hMj]; ring
      _ = M * 2 ^ (δ + 1) * 2 ^ (m + 1) * L ^ (-δ) *
          (L ^ m * Real.exp (-(Real.pi * ((j : ℝ) + 1) ^ 2 / 4))) := by rw [hLd]; ring
      _ ≤ M * 2 ^ (δ + 1) * 2 ^ (m + 1) * L ^ (-δ) * Real.exp ((m : ℝ) ^ 2) := by gcongr
      _ ≤ M * 2 ^ (δ + 1) * 2 ^ (m + 1) * (((j : ℝ) + 1) ^ m * L ^ (c - δ)) *
          Real.exp ((m : ℝ) ^ 2) := by gcongr
      _ = C2 * Q := by rw [hC2, hQ]; ring
  set N := CN * Mj ^ p * L ^ ((m : ℝ) + 1 - (m : ℝ) * p / 2) * ((j : ℝ) + 2) ^ m with hN
  set Kf := Mj * Real.exp (-(Real.pi * (((j : ℝ) + 2 - 1) * L) ^ 2 / (4 * L ^ 2))) *
      (2 * L) * (2 * L) ^ m with hKf
  have hKf0 : 0 ≤ Kf := by positivity
  have hN0 : 0 ≤ N := by positivity
  have hX : 2 ^ (p - 1) * (N + Kf ^ p) ≤ (2 ^ (p - 1) * (C1 + C2 ^ p)) * Q ^ p := by
    have h := Real.rpow_le_rpow hKf0 hFb hp0.le
    rw [Real.mul_rpow hC2n hQ0] at h
    calc 2 ^ (p - 1) * (N + Kf ^ p) ≤ 2 ^ (p - 1) * (C1 * Q ^ p + C2 ^ p * Q ^ p) := by
          gcongr
      _ = _ := by ring
  calc (2 ^ (p - 1) * (N + Kf ^ p)) ^ (1 / p)
      ≤ ((2 ^ (p - 1) * (C1 + C2 ^ p)) * Q ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (by positivity) hX (by positivity)
    _ = (2 ^ (p - 1) * (C1 + C2 ^ p)) ^ (1 / p) * Q := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hQ0,
          show p * (1 / p) = 1 by field_simp, Real.rpow_one]
    _ = _ := by rw [hQ]; ring

/-! ## `j = 0` -/
theorem piece_zero (m : ℕ) (p : ℝ) (hp : 1 ≤ p) (M : ℝ) (hM : 0 ≤ M) (b : ℝ → ℂ)
    (hb : Measurable b) (hbM : ∀ t, ‖b t‖ ≤ M) (hbs : ∀ t, b t ≠ 0 → |t| ≤ 1)
    (f : E (m + 1) → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (conv (kb m b) f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (M * (2 * 2 ^ m)) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hkI := kb_integrable m b hb M 1 hbM hbs
  have hY := (conv_basic (kb m b) hkI (ENNReal.ofReal p) (ENNReal.one_le_ofReal.2 hp) f
    hf.1).2.2
  refine hY.trans ?_
  gcongr
  rw [eLpNorm_one_eq_lintegral_enorm]
  have := kern_L1 m b hb M 1 0 hM le_rfl le_rfl hbM hbs
  have heq : ∀ z, {z : E (m + 1) | (0 : ℝ) ≤ ‖horiz z‖}.indicator (fun z => ‖kb m b z‖ₑ) z =
      ‖kb m b z‖ₑ := fun z =>
    Set.indicator_of_mem (s := {z : E (m + 1) | (0 : ℝ) ≤ ‖horiz z‖}) (norm_nonneg (horiz z)) _
  simp only [heq] at this
  refine this.trans (le_of_eq ?_)
  congr 1
  simp
  ring

theorem critE_nonneg (m : ℕ) (p : ℝ) (hp : 1 ≤ p) (hpc : p < pc m) : 0 ≤ critE m p := by
  unfold critE
  unfold pc at hpc
  have hp0 : 0 < p := by linarith
  rw [lt_div_iff₀ (by positivity)] at hpc
  rw [sub_nonneg, le_div_iff₀ hp0]
  nlinarith

/-- **P.** Averaging over centres `c ∈ ℝᵐ` of `x̲`-balls of radius `L = 2^j`, near part
(`near_bound`, `y̲ ∈ B(c, (j+2)L)`) plus far part (`Eg_norm`: Gaussian tail `e^{-π(j+1)²/4}`, Young);
`j = 0` by Young alone. -/
theorem piece_bound (m : ℕ) (hm : 1 ≤ m) (hR : ParabolicRestrictionConjecture m) (p : ℝ)
    (hp : 1 ≤ p) (hpc : p < pc m) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (M : ℝ), 0 ≤ M → ∀ b : ℝ → ℂ, Measurable b →
      (∀ t, ‖b t‖ ≤ M * sh j t * (1 + |t|) ^ (-(δ + 1))) →
      ∀ f : E (m + 1) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (conv (kb m b) f) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * M * ((j : ℝ) + 1) ^ m * (2 : ℝ) ^ ((j : ℝ) * (critE m p - δ))) *
            eLpNorm f (ENNReal.ofReal p) volume := by
  have hcrit := critE_nonneg m p hp hpc
  obtain ⟨CN, hCN, hN⟩ := near_bound m hm hR p hp hpc
  obtain ⟨C', hC', hC'b⟩ := const_bound m p δ hp hδ hcrit CN hCN
  refine ⟨max (2 * 2 ^ m) C', le_max_of_le_right hC', ?_⟩
  intro j M hM b hb hbb f hf
  have hδ1 : -(δ + 1) ≤ 0 := by linarith
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hbM : ∀ t, ‖b t‖ ≤ M := by
      intro t
      refine (hbb t).trans ?_
      by_cases ht : |t| ≤ 1
      · have hsh : sh 0 t = 1 := by simp [sh, ht]
        rw [hsh, mul_one]
        exact mul_le_of_le_one_right hM
          (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) hδ1)
      · have hsh : sh 0 t = 0 := by simp [sh, ht]
        rw [hsh, mul_zero, zero_mul]; exact hM
    have hbs : ∀ t, b t ≠ 0 → |t| ≤ 1 := by
      intro t hbt
      by_contra ht
      apply hbt
      have hsh : sh 0 t = 0 := by simp [sh, ht]
      have := hbb t
      rw [hsh, mul_zero, zero_mul] at this
      exact norm_le_zero_iff.1 this
    have hle : M * (2 * 2 ^ m) ≤ max (2 * 2 ^ m) C' * M * (((0 : ℕ) : ℝ) + 1) ^ m *
        (2 : ℝ) ^ (((0 : ℕ) : ℝ) * (critE m p - δ)) := by
      simp only [Nat.cast_zero, zero_add, one_pow, mul_one, zero_mul, Real.rpow_zero]
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hM
    refine (piece_zero m p hp M hM b hb hbM hbs f hf).trans ?_
    gcongr
  · set L : ℝ := (2 : ℝ) ^ j with hL
    have hL1 : 1 ≤ L := one_le_pow₀ (by norm_num)
    have hL0 : 0 < L := by positivity
    have hL2 : (2 : ℝ) ^ (j - 1) = L / 2 := by
      rw [hL, eq_div_iff (by norm_num), ← pow_succ, Nat.sub_add_cancel hj]
    have hsh0 : ∀ t, ¬ (L / 2 < |t| ∧ |t| ≤ L) → sh j t = 0 := by
      intro t ht
      rw [sh, if_neg hj.ne', if_neg (by rwa [hL2])]
    have hsh1 : ∀ t, L / 2 < |t| ∧ |t| ≤ L → sh j t = 1 := by
      intro t ht
      rw [sh, if_neg hj.ne', if_pos (by rwa [hL2])]
    have hsupp : ∀ t, b t ≠ 0 → L / 2 < |t| ∧ |t| ≤ L := by
      intro t hbt
      by_contra hc
      apply hbt
      have := hbb t
      rw [hsh0 t hc, mul_zero, zero_mul] at this
      exact norm_le_zero_iff.1 this
    set Mj : ℝ := M * 2 ^ (δ + 1) * L ^ (-(δ + 1)) with hMj
    have hMj0 : 0 ≤ Mj := by positivity
    have hbM : ∀ t, ‖b t‖ ≤ Mj := by
      intro t
      by_cases hbt : b t = 0
      · rw [hbt, norm_zero]; exact hMj0
      have ht := hsupp t hbt
      refine (hbb t).trans ?_
      rw [hsh1 t ht, mul_one]
      have h1 : (1 + |t|) ^ (-(δ + 1)) ≤ (L / 2) ^ (-(δ + 1)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [ht.1]) hδ1
      have h2 : (L / 2) ^ (-(δ + 1)) = 2 ^ (δ + 1) * L ^ (-(δ + 1)) := by
        rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
      rw [hMj, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1.trans_eq h2) hM
    have hcore := core m p hp CN hCN hN L ((j : ℝ) + 2) Mj hL1 (by linarith) hMj0 b hb hbM
      (fun t ht => ⟨(hsupp t ht).1.le, (hsupp t ht).2⟩) f hf
    have h2 := eLp_of_lint p hp _ f _ (by positivity) hcore
    refine h2.trans ?_
    gcongr
    refine (hC'b j M hM).trans ?_
    gcongr
    exact le_max_right _ _

end TaoBR.Carb.PartP
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
/-! ## Part P: one dyadic piece, `1 ≤ p < p_c` -/
alias piece_bound := TaoBR.Carb.PartP.piece_bound

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartZa
/-! ## Shells and the pieces -/
theorem sh_nonneg (j : ℕ) (t : ℝ) : 0 ≤ sh j t := by
  unfold sh; split_ifs <;> norm_num

theorem sh_le_one (j : ℕ) (t : ℝ) : sh j t ≤ 1 := by
  unfold sh; split_ifs <;> norm_num

theorem sh_neg (j : ℕ) (t : ℝ) : sh j (-t) = sh j t := by
  simp only [sh, abs_neg]

theorem sh_supp (j : ℕ) (t : ℝ) (h : sh j t ≠ 0) : |t| ≤ (2 : ℝ) ^ j := by
  by_cases hj : j = 0
  · subst hj
    simp only [sh, if_true] at h
    split_ifs at h with h2
    · simpa using h2
    · simp at h
  · simp only [sh, hj, if_false] at h
    split_ifs at h with h2
    · exact h2.2
    · simp at h

theorem sh_meas (j : ℕ) : Measurable (sh j) := by
  unfold sh
  by_cases hj : j = 0
  · simp only [hj, if_true]
    exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
      measurable_const measurable_const
  · simp only [hj, if_false]
    exact Measurable.ite ((measurableSet_lt measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const)) measurable_const measurable_const

theorem b_meas (δ : ℝ) (hδ : 0 < δ) (j : ℕ) : Measurable (fun t => (sh j t : ℂ) * Bc δ t) :=
  (Complex.measurable_ofReal.comp (sh_meas j)).mul (Bc_continuous δ hδ).measurable

theorem horiz_neg {m : ℕ} (z : E (m + 1)) : horiz (-z) = -horiz z := by
  ext i; simp [horiz]

theorem vert_neg {m : ℕ} (z : E (m + 1)) : vert (-z) = -vert z := by
  simp [vert]

theorem Kj_neg (m : ℕ) (δ : ℝ) (j : ℕ) (z : E (m + 1)) :
    Kj m δ j (-z) = conj (Kj m δ j z) := by
  simp only [Kj, kb, vert_neg, horiz_neg, sh_neg, Bc_neg, Eg_neg, map_mul, Complex.conj_ofReal]

theorem Kj_integrable (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (j : ℕ) : Integrable (Kj m δ j) := by
  obtain ⟨CB, hCB0, hCB⟩ := Bc_bound δ hδ
  refine kb_integrable m _ (b_meas δ hδ j) CB ((2 : ℝ) ^ j) (fun t => ?_) (fun t ht => ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sh_nonneg j t)]
    have h1 : (1 + |t|) ^ (-(δ + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by linarith)
    calc sh j t * ‖Bc δ t‖ ≤ 1 * (CB * 1) := by
          gcongr
          · exact sh_le_one j t
          · exact (hCB t).trans (mul_le_mul_of_nonneg_left h1 hCB0)
      _ = CB := by ring
  · apply sh_supp
    intro h0; apply ht; simp [h0]

/-! ## Z1 -/
theorem piece_low (m : ℕ) (hm : 1 ≤ m) (hR : ParabolicRestrictionConjecture m) (p : ℝ)
    (hp : 1 ≤ p) (hpc : p < pc m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ PieceBd m δ p
      (fun j => C * ((j : ℝ) + 1) ^ m * (2 : ℝ) ^ ((j : ℝ) * (critE m p - δ))) := by
  obtain ⟨CP, hCP0, hCP⟩ := piece_bound m hm hR p hp hpc δ hδ.le
  obtain ⟨CB, hCB0, hCB⟩ := Bc_bound δ hδ
  refine ⟨CP * CB, mul_nonneg hCP0 hCB0, fun j f hf => ?_⟩
  have := hCP j CB hCB0 (fun t => (sh j t : ℂ) * Bc δ t) (b_meas δ hδ j) (fun t => ?_) f hf
  · exact this
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sh_nonneg j t)]
    calc sh j t * ‖Bc δ t‖ ≤ sh j t * (CB * (1 + |t|) ^ (-(δ + 1))) :=
          mul_le_mul_of_nonneg_left (hCB t) (sh_nonneg j t)
      _ = CB * sh j t * (1 + |t|) ^ (-(δ + 1)) := by ring

end TaoBR.Carb.PartZa
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
/-! ## Part Z: assembly lemmas -/
alias piece_low := TaoBR.Carb.PartZa.piece_low

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartZa
/-! ## Z2 -/
theorem conv_reflect (m : ℕ) (δ : ℝ) (j : ℕ) (f : E (m + 1) → ℂ) :
    conv (fun z => Kj m δ j (-z)) f = fun x => conj (conv (Kj m δ j) (fun y => conj (f y)) x) := by
  funext x
  simp only [conv, ← integral_conj, map_mul, Complex.conj_conj]
  congr 1; funext y
  rw [← neg_sub, Kj_neg]

theorem piece_dual (m : ℕ) (hm : 1 ≤ m) (hR : ParabolicRestrictionConjecture m) (q : ℝ)
    (hq : 1 < q) (hqc : q < pc m) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ PieceBd m δ (q / (q - 1))
      (fun j => C * ((j : ℝ) + 1) ^ m * (2 : ℝ) ^ ((j : ℝ) * (critE m q - δ))) := by
  obtain ⟨C, hC0, hC⟩ := piece_low m hm hR q hq.le hqc δ hδ
  refine ⟨C, hC0, fun j g hg => ?_⟩
  have hK : Integrable (fun z => Kj m δ j (-z)) := (Kj_integrable m δ hδ j).comp_neg
  have key := dual_bound (fun z => Kj m δ j (-z)) hK q hq
    (ENNReal.ofReal (C * ((j : ℝ) + 1) ^ m * (2 : ℝ) ^ ((j : ℝ) * (critE m q - δ))))
    (fun f hf => ?_) g hg
  · simpa only [neg_neg] using key
  · have hcf : MemLp (fun y => conj (f y)) (ENNReal.ofReal q) volume :=
      (memLp_congr_norm hf.1 (Complex.continuous_conj.comp_aestronglyMeasurable hf.1)
        (ae_of_all _ fun y => (Complex.norm_conj _).symm)).1 hf
    have e1 : eLpNorm (fun y => conj (f y)) (ENNReal.ofReal q) volume =
        eLpNorm f (ENNReal.ofReal q) volume :=
      eLpNorm_congr_norm_ae (ae_of_all _ fun y => Complex.norm_conj _)
    rw [conv_reflect, eLpNorm_congr_norm_ae (g := conv (Kj m δ j) (fun y => conj (f y)))
      (ae_of_all _ fun y => Complex.norm_conj _), ← e1]
    exact hC j _ hcf

end TaoBR.Carb.PartZa
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
alias piece_dual := TaoBR.Carb.PartZa.piece_dual

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartZa
/-! ## Z3 -/
theorem summable_piece (m : ℕ) (C e δ : ℝ) (he : e < δ) :
    Summable (fun j : ℕ => C * ((j : ℝ) + 1) ^ m * (2 : ℝ) ^ ((j : ℝ) * (e - δ))) := by
  set r : ℝ := (2 : ℝ) ^ (e - δ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow : ∀ j : ℕ, (2 : ℝ) ^ ((j : ℝ) * (e - δ)) = r ^ j := by
    intro j
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  have h0 : Summable (fun n : ℕ => ((n : ℝ)) ^ m * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one m (by rw [Real.norm_of_nonneg hr0.le]; exact hr1)
  have h1 : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ)) ^ m * r ^ (n + 1))) :=
    (summable_nat_add_iff 1).2 h0
  have h2 := h1.mul_left (C / r)
  refine h2.congr (fun j => ?_)
  rw [hpow, pow_succ]
  push_cast
  field_simp

end TaoBR.Carb.PartZa
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
alias summable_piece := TaoBR.Carb.PartZa.summable_piece

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartZa
/-! ## Z4 -/
theorem rpow_add_le (a b s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (a + b) ^ s ≤ a ^ s + b ^ s := by
  have := NNReal.rpow_add_le_add_rpow ⟨a, ha⟩ ⟨b, hb⟩ hs0 hs1
  exact_mod_cast this

theorem term_le (m N : ℕ) (C ε δ s : ℝ) (hC : 0 ≤ C) (_hs : 0 < s) (hN : (m : ℝ) * s ≤ N)
    (j : ℕ) :
    (C * ((j : ℝ) + 1) ^ m * (2 : ℝ) ^ ((j : ℝ) * ε)) ^ s ≤
      C ^ s * ((j : ℝ) + 1) ^ N * (2 : ℝ) ^ ((j : ℝ) * (ε * s + δ - δ)) := by
  have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC (by positivity),
    ← Real.rpow_natCast ((j : ℝ) + 1) m, ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by norm_num)]
  have e1 : ((j : ℝ) + 1) ^ ((m : ℝ) * s) ≤ ((j : ℝ) + 1) ^ N := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hj hN
  have e2 : (j : ℝ) * ε * s = (j : ℝ) * (ε * s + δ - δ) := by ring
  rw [e2]
  gcongr

theorem piece_mid (m : ℕ) (hm : 1 ≤ m) (hR : ParabolicRestrictionConjecture m) (p : ℝ)
    (hp : pc m ≤ p) (hp' : p ≤ pc m / (pc m - 1)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ → ℝ, (∀ j, 0 ≤ A j) ∧ Summable A ∧ PieceBd m δ p A := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpc1 : 1 < pc m := by
    unfold pc; rw [lt_div_iff₀ (by positivity)]; linarith
  set a : ℝ := 2 * ((m : ℝ) + 1) / ((m : ℝ) + 2 + 2 * δ) with ha
  have hapc : a < pc m := by
    unfold pc
    exact div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
  obtain ⟨p₀, hlo, hhi⟩ := exists_between (max_lt hpc1 hapc)
  have hp₀1 : 1 < p₀ := lt_of_le_of_lt (le_max_left _ _) hlo
  have hap₀ : a < p₀ := lt_of_le_of_lt (le_max_right _ _) hlo
  have hcrit : critE m p₀ < δ := by
    unfold critE
    have h2 : 2 * ((m : ℝ) + 1) < p₀ * ((m : ℝ) + 2 + 2 * δ) := by
      rw [ha, div_lt_iff₀ (by positivity)] at hap₀; linarith
    have h3 : ((m : ℝ) + 1) / p₀ < δ + ((m : ℝ) + 2) / 2 := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  set p₁ : ℝ := p₀ / (p₀ - 1) with hp₁
  have hp₀p : p₀ < p := lt_of_lt_of_le hhi hp
  have hpp₁ : p < p₁ := by
    refine lt_of_le_of_lt hp' ?_
    rw [hp₁, div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hp0 : 0 < p := by linarith
  obtain ⟨C₀, hC₀0, hC₀⟩ := piece_low m hm hR p₀ hp₀1.le hhi δ hδ
  obtain ⟨C₁, hC₁0, hC₁⟩ := piece_dual m hm hR p₀ hp₀1 hhi δ hδ
  obtain ⟨CI, hCI0, hCI⟩ := interp_bound p₀ p p₁ hp₀1.le hp₀p hpp₁
  set ε : ℝ := critE m p₀ - δ with hε
  have hεneg : ε < 0 := by rw [hε]; linarith
  set A₀ : ℕ → ℝ := fun j => C₀ * ((j : ℝ) + 1) ^ m * (2 : ℝ) ^ ((j : ℝ) * ε) with hA₀
  set A₁ : ℕ → ℝ := fun j => C₁ * ((j : ℝ) + 1) ^ m * (2 : ℝ) ^ ((j : ℝ) * ε) with hA₁
  have hA₀0 : ∀ j, 0 ≤ A₀ j := fun j => by positivity
  have hA₁0 : ∀ j, 0 ≤ A₁ j := fun j => by positivity
  refine ⟨fun j => CI * (A₀ j ^ p₀ + A₁ j ^ p₁) ^ (1 / p), fun j => by positivity, ?_, ?_⟩
  · -- summability
    have hp₁0 : 0 < p₁ := by linarith
    have hs₀ : 0 < p₀ * (1 / p) := by positivity
    have hs₁ : 0 < p₁ * (1 / p) := by positivity
    have S₀ := summable_piece ⌈(m : ℝ) * (p₀ * (1 / p))⌉₊ (C₀ ^ (p₀ * (1 / p)))
      (ε * (p₀ * (1 / p)) + δ) δ (by nlinarith)
    have S₁ := summable_piece ⌈(m : ℝ) * (p₁ * (1 / p))⌉₊ (C₁ ^ (p₁ * (1 / p)))
      (ε * (p₁ * (1 / p)) + δ) δ (by nlinarith)
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      ((S₀.add S₁).mul_left CI)
    apply mul_le_mul_of_nonneg_left _ hCI0
    calc (A₀ j ^ p₀ + A₁ j ^ p₁) ^ (1 / p)
        ≤ (A₀ j ^ p₀) ^ (1 / p) + (A₁ j ^ p₁) ^ (1 / p) :=
          rpow_add_le _ _ _ (by have := hA₀0 j; positivity) (by have := hA₁0 j; positivity)
            (by positivity) (by rw [div_le_one hp0]; linarith)
      _ = A₀ j ^ (p₀ * (1 / p)) + A₁ j ^ (p₁ * (1 / p)) := by
          rw [← Real.rpow_mul (hA₀0 j), ← Real.rpow_mul (hA₁0 j)]
      _ ≤ _ := add_le_add
          (term_le m _ C₀ ε δ _ hC₀0 hs₀ (Nat.le_ceil _) j)
          (term_le m _ C₁ ε δ _ hC₁0 hs₁ (Nat.le_ceil _) j)
  · intro j f hf
    exact hCI (m + 1) (Kj m δ j) (Kj_integrable m δ hδ j) (A₀ j) (A₁ j) (hA₀0 j) (hA₁0 j)
      (fun g hg => hC₀ j g hg) (fun g hg => hC₁ j g hg) f hf

end TaoBR.Carb.PartZa
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
alias piece_mid := TaoBR.Carb.PartZa.piece_mid

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartZb
open Filter Topology
variable {m : ℕ}
@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

@[simp] theorem vert_mkPoint (u : E m) (t : ℝ) : vert (mkPoint u t) = t := by
  simp [vert]

@[simp] theorem horiz_mkPoint (u : E m) (t : ℝ) : horiz (mkPoint u t) = u := by
  ext i; simp [horiz]

@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

theorem ext_hv {y y' : E (m + 1)} (h1 : horiz y = horiz y') (h2 : vert y = vert y') : y = y' := by
  ext i
  induction i using Fin.lastCases with
  | last => exact h2
  | cast j => have := congrArg (fun z : E m => z j) h1; simpa using this

@[simp] theorem mkPoint_horiz_vert (y : E (m + 1)) : mkPoint (horiz y) (vert y) = y :=
  ext_hv (by simp) (by simp)

@[simp] theorem horiz_add (y y' : E (m + 1)) : horiz (y + y') = horiz y + horiz y' := by
  ext i; simp

@[simp] theorem horiz_sub (y y' : E (m + 1)) : horiz (y - y') = horiz y - horiz y' := by
  ext i; simp

@[simp] theorem horiz_smul (r : ℝ) (y : E (m + 1)) : horiz (r • y) = r • horiz y := by
  ext i; simp

@[simp] theorem vert_add (y y' : E (m + 1)) : vert (y + y') = vert y + vert y' := by
  simp [vert]

@[simp] theorem vert_sub (y y' : E (m + 1)) : vert (y - y') = vert y - vert y' := by
  simp [vert]

@[simp] theorem vert_smul (r : ℝ) (y : E (m + 1)) : vert (r • y) = r * vert y := by
  simp [vert]

theorem continuous_horiz : Continuous (horiz : E (m + 1) → E m) := by
  unfold horiz; fun_prop

theorem continuous_vert : Continuous (vert : E (m + 1) → ℝ) := by
  unfold vert; fun_prop

theorem continuous_mkPoint : Continuous fun q : E m × ℝ => mkPoint q.1 q.2 := by
  unfold mkPoint
  apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  induction i using Fin.lastCases with
  | last => simp; fun_prop
  | cast j => simp; fun_prop

theorem measurable_mkPoint : Measurable fun q : E m × ℝ => mkPoint q.1 q.2 :=
  continuous_mkPoint.measurable

end TaoBR.Carb.PartZb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb.PartZb
open Filter Topology
/-! ## Fubini in `ℝ^{m+1} = ℝ^m × ℝ` -/
theorem measurePreserving_mkPoint (m : ℕ) :
    MeasurePreserving (fun q : E m × ℝ => mkPoint q.1 q.2) (volume.prod volume) volume := by
  have h1 : MeasurePreserving (Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ))
      ((volume : Measure (E m)).prod (volume : Measure ℝ)) (volume.prod volume) :=
    (PiLp.volume_preserving_ofLp (Fin m)).prod (MeasurePreserving.id volume)
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin m → ℝ)))
    (ν := (volume : Measure ℝ)))
  have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
  have h4 := PiLp.volume_preserving_toLp (Fin (m + 1))
  have h := h4.comp (h3.comp (h2.comp h1))
  have heq : (fun q : E m × ℝ => mkPoint q.1 q.2) = (WithLp.toLp 2 ∘
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm ∘
        Prod.swap ∘ Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ)) := by
    funext q
    apply ext_hv
    · ext i; simp [Function.comp]
    · simp [vert, Function.comp]
  rw [heq]; exact h

/-- (Part B1) Fubini in the coordinates `ℝ^{m+1} = ℝ^m × ℝ`. -/
theorem lintegral_mkPoint (m : ℕ) (F : E (m + 1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ u, ∫⁻ h, F (mkPoint u h) := by
  rw [← (measurePreserving_mkPoint m).lintegral_comp hF]
  exact lintegral_prod _ (hF.comp measurable_mkPoint).aemeasurable

/-! ## Basic facts on the kernels -/
theorem Kc_continuous (m : ℕ) (δ : ℝ) (hδ : 0 < δ) : Continuous (Kc m δ) := by
  have h1 : Continuous (fun z : E (m + 1) => Bc δ (vert z)) :=
    (Bc_continuous δ hδ).comp (continuous_vert (m := m))
  have h2 : Continuous (fun z : E (m + 1) => Eg m (horiz z) (vert z)) :=
    (Eg_continuous m).comp₂ (continuous_horiz (m := m)) (continuous_vert (m := m))
  have h3 : Kc m δ = fun z : E (m + 1) => Bc δ (vert z) * Eg m (horiz z) (vert z) := by
    funext z; simp only [Kc, kb]
  rw [h3]
  exact h1.mul h2

theorem Eg_le_one (m : ℕ) (d : E m) (τ : ℝ) : ‖Eg m d τ‖ ≤ 1 := by
  refine (Eg_norm m d τ).trans ?_
  have h1 : (1 + τ ^ 2) ^ (-((m : ℝ) / 4)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith) (by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)
  have h2 : Real.exp (-(Real.pi * ‖d‖ ^ 2 / (1 + τ ^ 2))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by
      have : 0 ≤ Real.pi * ‖d‖ ^ 2 / (1 + τ ^ 2) := by positivity
      linarith)
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
    _ = 1 := one_mul 1

theorem Bc_bdd (δ : ℝ) (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖Bc δ t‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := Bc_bound δ hδ
  refine ⟨C, hC0, fun t => (hC t).trans ?_⟩
  have : (1 + |t|) ^ (-(δ + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by linarith)
  calc C * (1 + |t|) ^ (-(δ + 1)) ≤ C * 1 := mul_le_mul_of_nonneg_left this hC0
    _ = C := mul_one C

theorem Kc_bdd (m : ℕ) (δ : ℝ) (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖Kc m δ z‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := Bc_bdd δ hδ
  refine ⟨C, hC0, fun z => ?_⟩
  rw [Kc, kb, norm_mul]
  calc _ ≤ C * 1 := mul_le_mul (hC _) (Eg_le_one _ _ _) (norm_nonneg _) hC0
    _ = C := mul_one C

theorem sh_measurable (j : ℕ) : Measurable (sh j) := by
  unfold sh
  by_cases hj : j = 0
  · simp only [hj, if_true]
    exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
      measurable_const measurable_const
  · simp only [hj, if_false]
    exact Measurable.ite ((measurableSet_lt measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const)) measurable_const
      measurable_const

theorem sh_zero_or_one (j : ℕ) (t : ℝ) : sh j t = 0 ∨ sh j t = 1 := by
  unfold sh; split_ifs <;> simp

theorem sh_support (j : ℕ) (t : ℝ) (h : sh j t ≠ 0) : |t| ≤ 2 ^ j := by
  unfold sh at h
  split_ifs at h with h1 h2 h3
  · simp [h1]; exact h2
  · simp at h
  · exact h3.2
  · simp at h

theorem sum_sh (N : ℕ) (t : ℝ) :
    ∑ j ∈ Finset.range (N + 1), sh j t = if |t| ≤ 2 ^ N then 1 else 0 := by
  induction N with
  | zero => simp [sh]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hmono : (2 : ℝ) ^ N ≤ 2 ^ (N + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    simp only [sh, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    by_cases h1 : |t| ≤ 2 ^ N
    · have h2 : |t| ≤ 2 ^ (N + 1) := h1.trans hmono
      simp [h1, h2]
    · by_cases h2 : |t| ≤ 2 ^ (N + 1)
      · simp [h1, h2, lt_of_not_ge h1]
      · simp [h1, h2]

theorem Kj_eq (m : ℕ) (δ : ℝ) (j : ℕ) (z : E (m + 1)) :
    Kj m δ j z = (sh j (vert z) : ℂ) * Kc m δ z := by
  simp [Kj, Kc, kb, mul_assoc]

theorem Kj_integrable (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (j : ℕ) : Integrable (Kj m δ j) := by
  obtain ⟨C, hC0, hC⟩ := Bc_bdd δ hδ
  refine kb_integrable m _ ((Complex.measurable_ofReal.comp (sh_measurable j)).mul
    (Bc_continuous δ hδ).measurable) C (2 ^ j) (fun t => ?_) (fun t ht => ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rcases sh_zero_or_one j t with h | h <;> rw [h] <;> simp [hC0, hC t]
  · apply sh_support j t
    intro h; apply ht; simp [h]

theorem Kj_measurable (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (j : ℕ) : Measurable (Kj m δ j) := by
  have : Kj m δ j = fun z => (sh j (vert z) : ℂ) * Kc m δ z := funext (Kj_eq m δ j)
  rw [this]
  exact (Complex.measurable_ofReal.comp ((sh_measurable j).comp continuous_vert.measurable)).mul
    (Kc_continuous m δ hδ).measurable

/-! ## Z8 -/
/-- **Z8.** -/
theorem conv_Kc_aesm (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (f : 𝓢(E (m + 1), ℂ)) :
    AEStronglyMeasurable (conv (Kc m δ) f) volume := by
  have hc : Continuous (fun q : E (m + 1) × E (m + 1) => Kc m δ (q.1 - q.2) * f q.2) :=
    ((Kc_continuous m δ hδ).comp (continuous_fst.sub continuous_snd)).mul
      (f.continuous.comp continuous_snd)
  exact hc.aestronglyMeasurable.integral_prod_right'

/-! ## Z7 -/
/-- **Z7.** The cases of `δ > δ(p)`. -/
theorem crit_cases (m : ℕ) (hm : 1 ≤ m) (p : ℝ≥0∞) (hp : 1 ≤ p) (δ : ℝ)
    (hδ : critIndex (m + 1) p < δ) :
    0 < δ ∧
    ((p = ⊤ ∧ (m : ℝ) / 2 < δ) ∨
      (∃ q : ℝ, p = ENNReal.ofReal q ∧ 1 ≤ q ∧ q < pc m ∧ critE m q < δ) ∨
      (∃ q : ℝ, p = ENNReal.ofReal q ∧ pc m ≤ q ∧ q ≤ pc m / (pc m - 1)) ∨
      (∃ q : ℝ, 1 < q ∧ q < pc m ∧ p = ENNReal.ofReal (q / (q - 1)) ∧ critE m q < δ)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ0 : 0 < δ := lt_of_le_of_lt (le_max_right _ _) hδ
  have hδ1 : ((m : ℝ) + 1) * |p⁻¹.toReal - 1 / 2| - 1 / 2 < δ := by
    have := lt_of_le_of_lt (le_max_left _ _) hδ
    push_cast at this; linarith
  refine ⟨hδ0, ?_⟩
  by_cases htop : p = ⊤
  · left
    subst htop
    refine ⟨rfl, ?_⟩
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, zero_sub] at hδ1
    rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hδ1
    linarith
  right
  set q := p.toReal with hqdef
  have hpq : p = ENNReal.ofReal q := (ENNReal.ofReal_toReal htop).symm
  have hq1 : 1 ≤ q := by
    have := ENNReal.toReal_mono htop hp; simpa using this
  have hq0 : 0 < q := by linarith
  have hinv : p⁻¹.toReal = 1 / q := by rw [ENNReal.toReal_inv, one_div]
  rw [hinv] at hδ1
  have hpc2 : pc m < 2 := by
    unfold pc; rw [div_lt_iff₀ (by positivity)]; linarith
  have hpcpc : pc m / (pc m - 1) = 2 * ((m : ℝ) + 1) / m := by
    have h1 : (m : ℝ) + 2 ≠ 0 := by positivity
    have h2 : (m : ℝ) ≠ 0 := by positivity
    have hpc1 : pc m - 1 = (m : ℝ) / ((m : ℝ) + 2) := by
      unfold pc; field_simp; ring
    rw [hpc1]; unfold pc
    rw [div_div_div_cancel_right₀ h1]
  by_cases h1 : q < pc m
  · left
    refine ⟨q, hpq, hq1, h1, ?_⟩
    have : 1 / 2 < 1 / q := by
      rw [div_lt_div_iff₀ (by norm_num) hq0]; linarith
    rw [abs_of_pos (by linarith)] at hδ1
    have : ((m : ℝ) + 1) / q - ((m : ℝ) + 2) / 2 = ((m : ℝ) + 1) * (1 / q - 1 / 2) - 1 / 2 := by
      ring
    unfold critE; linarith
  right
  by_cases h2 : q ≤ pc m / (pc m - 1)
  · left; exact ⟨q, hpq, not_lt.1 h1, h2⟩
  right
  rw [hpcpc, not_le, div_lt_iff₀ (by positivity)] at h2
  have hq2 : 2 < q := by nlinarith
  have hq1' : 0 < q - 1 := by linarith
  refine ⟨q / (q - 1), ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hq1']; linarith
  · unfold pc
    rw [div_lt_div_iff₀ hq1' (by positivity)]
    nlinarith
  · rw [hpq]; congr 1
    field_simp
    ring
  · have : 1 / q < 1 / 2 := by
      rw [div_lt_div_iff₀ hq0 (by norm_num)]; linarith
    rw [abs_of_neg (by linarith)] at hδ1
    unfold critE
    have : ((m : ℝ) + 1) / (q / (q - 1)) - ((m : ℝ) + 2) / 2 =
        ((m : ℝ) + 1) * -(1 / q - 1 / 2) - 1 / 2 := by
      field_simp; ring
    linarith

/-! ## Z6: `p = ∞` -/
theorem integrable_gauss (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun z : E n => Real.exp (-c * ‖z‖ ^ 2)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (b := (c : ℂ)) (by rw [Complex.ofReal_re]; exact hc) 0 (0 : E n)).re
  refine this.congr (ae_of_all _ fun u => ?_)
  simp only [zero_mul, add_zero]
  rw [show (-(c : ℂ) * (‖u‖ : ℂ) ^ 2) = ((-c * ‖u‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_exp]; exact Complex.ofReal_re _

theorem gauss_int (m : ℕ) (s : ℝ) (hs : 0 < s) :
    ∫⁻ u : E m, ENNReal.ofReal (Real.exp (-(Real.pi * ‖u‖ ^ 2 / s))) =
      ENNReal.ofReal (s ^ ((m : ℝ) / 2)) := by
  have ha : 0 < Real.pi / s := by positivity
  have hI : Integrable (fun u : E m => Real.exp (-(Real.pi / s) * ‖u‖ ^ 2)) :=
    integrable_gauss m ha
  have heq : (fun u : E m => ENNReal.ofReal (Real.exp (-(Real.pi * ‖u‖ ^ 2 / s)))) =
      fun u => ENNReal.ofReal (Real.exp (-(Real.pi / s) * ‖u‖ ^ 2)) := by
    funext u; congr 2; ring
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun u => (Real.exp_pos _).le),
    GaussianFourier.integral_rexp_neg_mul_sq_norm ha, finrank_euclideanSpace_fin]
  congr 2
  field_simp

/-- The weight `C (1 + |t|)^{-δ-1} (1 + t²)^{-m/4}`. -/
noncomputable def Aw (C δ : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  C * (1 + |t|) ^ (-(δ + 1)) * (1 + t ^ 2) ^ (-((m : ℝ) / 4))

theorem Aw_nonneg (C δ : ℝ) (m : ℕ) (hC : 0 ≤ C) (t : ℝ) : 0 ≤ Aw C δ m t := by
  unfold Aw; positivity

theorem Aw_continuous (C δ : ℝ) (m : ℕ) : Continuous (Aw C δ m) := by
  unfold Aw
  refine (continuous_const.mul ?_).mul ?_
  · exact (continuous_const.add continuous_abs).rpow_const
      (fun t => Or.inl (by simp only [Pi.add_apply]; positivity))
  · exact (continuous_const.add (continuous_pow 2)).rpow_const
      (fun t => Or.inl (by simp only [Pi.add_apply]; positivity))

theorem Aw_bound (C δ : ℝ) (m : ℕ) (hC : 0 ≤ C) (t : ℝ) :
    ENNReal.ofReal (Aw C δ m t) * ENNReal.ofReal ((1 + t ^ 2) ^ ((m : ℝ) / 2)) ≤
      ENNReal.ofReal (C * (1 + ‖t‖) ^ (-(δ + 1 - (m : ℝ) / 2))) := by
  rw [← ENNReal.ofReal_mul (Aw_nonneg C δ m hC t)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.norm_eq_abs]
  have hs : 0 < 1 + t ^ 2 := by positivity
  have hu : 0 < 1 + |t| := by positivity
  have e1 : (1 + t ^ 2) ^ (-((m : ℝ) / 4)) * (1 + t ^ 2) ^ ((m : ℝ) / 2) =
      (1 + t ^ 2) ^ ((m : ℝ) / 4) := by
    rw [← Real.rpow_add hs]; ring_nf
  have e2 : (1 + t ^ 2) ^ ((m : ℝ) / 4) ≤ (1 + |t|) ^ ((m : ℝ) / 2) := by
    calc (1 + t ^ 2) ^ ((m : ℝ) / 4) ≤ ((1 + |t|) ^ (2 : ℝ)) ^ ((m : ℝ) / 4) := by
          apply Real.rpow_le_rpow hs.le _ (by positivity)
          rw [Real.rpow_two]; nlinarith [abs_nonneg t, sq_abs t]
      _ = (1 + |t|) ^ ((m : ℝ) / 2) := by rw [← Real.rpow_mul hu.le]; ring_nf
  have e3 : (1 + |t|) ^ (-(δ + 1)) * (1 + |t|) ^ ((m : ℝ) / 2) =
      (1 + |t|) ^ (-(δ + 1 - (m : ℝ) / 2)) := by
    rw [← Real.rpow_add hu]; ring_nf
  calc Aw C δ m t * (1 + t ^ 2) ^ ((m : ℝ) / 2) = C * (1 + |t|) ^ (-(δ + 1)) *
        ((1 + t ^ 2) ^ (-((m : ℝ) / 4)) * (1 + t ^ 2) ^ ((m : ℝ) / 2)) := by
        unfold Aw; ring
    _ = C * (1 + |t|) ^ (-(δ + 1)) * (1 + t ^ 2) ^ ((m : ℝ) / 4) := by rw [e1]
    _ ≤ C * (1 + |t|) ^ (-(δ + 1)) * (1 + |t|) ^ ((m : ℝ) / 2) := by gcongr
    _ = C * (1 + |t|) ^ (-(δ + 1 - (m : ℝ) / 2)) := by rw [mul_assoc, e3]

theorem Kc_integrable (m : ℕ) (δ : ℝ) (hδ : (m : ℝ) / 2 < δ) : Integrable (Kc m δ) := by
  have hδ0 : 0 < δ := lt_of_le_of_lt (by positivity) hδ
  obtain ⟨C, hC0, hC⟩ := Bc_bound δ hδ0
  refine ⟨(Kc_continuous m δ hδ0).aestronglyMeasurable, ?_⟩
  set G : E (m + 1) → ℝ≥0∞ := fun z => ENNReal.ofReal (Aw C δ m (vert z)) *
      ENNReal.ofReal (Real.exp (-(Real.pi * ‖horiz z‖ ^ 2 / (1 + vert z ^ 2)))) with hG
  have hGm : Measurable G := by
    refine (ENNReal.measurable_ofReal.comp
      ((Aw_continuous C δ m).measurable.comp continuous_vert.measurable)).mul ?_
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    refine Real.continuous_exp.comp (Continuous.neg ?_)
    exact (continuous_const.mul ((continuous_norm.comp continuous_horiz).pow 2)).div
      (continuous_const.add (continuous_vert.pow 2)) (fun z => by positivity)
  have hpt : ∀ z, ‖Kc m δ z‖ₑ ≤ G z := by
    intro z
    simp only [hG]
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (Aw_nonneg C δ m hC0 _)]
    apply ENNReal.ofReal_le_ofReal
    calc ‖Kc m δ z‖ = ‖Bc δ (vert z)‖ * ‖Eg m (horiz z) (vert z)‖ := by
          rw [Kc, kb, norm_mul]
      _ ≤ (C * (1 + |vert z|) ^ (-(δ + 1))) * ((1 + vert z ^ 2) ^ (-((m : ℝ) / 4)) *
            Real.exp (-(Real.pi * ‖horiz z‖ ^ 2 / (1 + vert z ^ 2)))) :=
          mul_le_mul (hC _) (Eg_norm _ _ _) (norm_nonneg _) (by positivity)
      _ = _ := by unfold Aw; ring
  have hfin : ∫⁻ z, G z < ⊤ := by
    rw [lintegral_mkPoint m G hGm]
    have hm2 : Measurable (Function.uncurry fun (u : E m) (t : ℝ) => G (mkPoint u t)) :=
      hGm.comp measurable_mkPoint
    rw [lintegral_lintegral_swap hm2.aemeasurable]
    have hin : ∀ t : ℝ, ∫⁻ u : E m, G (mkPoint u t) =
        ENNReal.ofReal (Aw C δ m t) * ENNReal.ofReal ((1 + t ^ 2) ^ ((m : ℝ) / 2)) := by
      intro t
      simp only [hG, horiz_mkPoint, vert_mkPoint]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, gauss_int m _ (by positivity)]
    simp_rw [hin]
    refine lt_of_le_of_lt (lintegral_mono (Aw_bound C δ m hC0)) ?_
    exact ((integrable_one_add_norm (E := ℝ) (μ := volume) (r := δ + 1 - (m : ℝ) / 2)
      (by simp; linarith)).const_mul C).lintegral_lt_top
  exact (lintegral_mono hpt).trans_lt hfin

/-- **Z6.** `p = ∞`: for `δ > m/2` the kernel is integrable. -/
theorem bound_infty (m : ℕ) (δ : ℝ) (hδ : (m : ℝ) / 2 < δ) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E (m + 1), ℂ),
      eLpNorm (conv (Kc m δ) f) ⊤ volume ≤ C * eLpNorm f ⊤ volume := by
  have hK := Kc_integrable m δ hδ
  refine ⟨(eLpNorm (Kc m δ) 1 volume).toNNReal, fun f => ?_⟩
  rw [ENNReal.coe_toNNReal (memLp_one_iff_integrable.2 hK).eLpNorm_ne_top]
  exact (conv_basic (Kc m δ) hK ⊤ le_top f f.continuous.aestronglyMeasurable).2.2

/-! ## Z5: summing the pieces -/
theorem conv_sum_eq (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (f : 𝓢(E (m + 1), ℂ)) (N : ℕ)
    (x : E (m + 1)) :
    (∑ j ∈ Finset.range (N + 1), conv (Kj m δ j) f) x =
      ∫ y, ((if |vert (x - y)| ≤ (2 : ℝ) ^ N then 1 else 0 : ℝ) : ℂ) *
        (Kc m δ (x - y) * f y) := by
  rw [Finset.sum_apply]
  unfold conv
  rw [← integral_finsetSum]
  · congr 1; funext y
    rw [← sum_sh N, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Kj_eq, mul_assoc]
  · intro j _
    obtain ⟨C, hC0, hC⟩ := Kc_bdd m δ hδ
    refine (f.integrable).bdd_mul (c := C) ?_ (ae_of_all _ fun y => ?_)
    · exact ((Kj_measurable m δ hδ j).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · rw [Kj_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rcases sh_zero_or_one j (vert (x - y)) with h | h <;> rw [h] <;> simp [hC0, hC]

theorem conv_sum_tendsto (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (f : 𝓢(E (m + 1), ℂ))
    (x : E (m + 1)) :
    Tendsto (fun N => (∑ j ∈ Finset.range (N + 1), conv (Kj m δ j) f) x) atTop
      (𝓝 (conv (Kc m δ) f x)) := by
  simp_rw [conv_sum_eq m δ hδ f _ x]
  obtain ⟨C, hC0, hC⟩ := Kc_bdd m δ hδ
  unfold conv
  refine tendsto_integral_of_dominated_convergence (fun y => C * ‖f y‖) (fun N => ?_)
    (f.integrable.norm.const_mul C) (fun N => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    refine (Complex.measurable_ofReal.comp (Measurable.ite ?_ measurable_const
      measurable_const)).mul ?_
    · exact measurableSet_le (continuous_abs.comp (continuous_vert.comp
        (continuous_const.sub continuous_id))).measurable measurable_const
    · exact ((Kc_continuous m δ hδ).comp (continuous_const.sub continuous_id)).measurable.mul
        f.continuous.measurable
  · rw [norm_mul, norm_mul]
    split_ifs
    · simp only [Complex.ofReal_one, norm_one, one_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    · simp only [Complex.ofReal_zero, norm_zero, zero_mul]; positivity
  · obtain ⟨N0, hN0⟩ := pow_unbounded_of_one_lt |vert (x - y)| (by norm_num : (1 : ℝ) < 2)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N0, fun N hN => ?_⟩)
    have : |vert (x - y)| ≤ (2 : ℝ) ^ N :=
      hN0.le.trans (pow_le_pow_right₀ (by norm_num) hN)
    show _ = _ * _
    rw [if_pos this]; simp

/-- **Z5.** Summing the pieces (`K = ∑ K_j` pointwise; Minkowski for the series). -/
theorem bound_of_summable (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (q : ℝ) (hq : 1 ≤ q) (A : ℕ → ℝ)
    (hA0 : ∀ j, 0 ≤ A j) (hA : Summable A) (hb : PieceBd m δ q A) (f : 𝓢(E (m + 1), ℂ)) :
    eLpNorm (conv (Kc m δ) f) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (∑' j, A j) * eLpNorm f (ENNReal.ofReal q) volume := by
  set F : ℕ → E (m + 1) → ℂ := fun N => ∑ j ∈ Finset.range (N + 1), conv (Kj m δ j) f with hF
  have hq' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hq
  have haesm : ∀ j, AEStronglyMeasurable (conv (Kj m δ j) f) volume := fun j =>
    (conv_basic _ (Kj_integrable m δ hδ j) _ hq' _ f.continuous.aestronglyMeasurable).2.1
  have hFm : ∀ N, AEStronglyMeasurable (F N) volume := fun N =>
    Finset.aestronglyMeasurable_sum _ fun j _ => haesm j
  have hbd : ∀ N, eLpNorm (F N) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (∑' j, A j) * eLpNorm f (ENNReal.ofReal q) volume := by
    intro N
    calc eLpNorm (F N) (ENNReal.ofReal q) volume
        ≤ ∑ j ∈ Finset.range (N + 1), eLpNorm (conv (Kj m δ j) f) (ENNReal.ofReal q) volume :=
          eLpNorm_sum_le (fun j _ => haesm j) hq'
      _ ≤ ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (A j) *
            eLpNorm f (ENNReal.ofReal q) volume :=
          Finset.sum_le_sum fun j _ => hb j f (f.memLp _)
      _ = ENNReal.ofReal (∑ j ∈ Finset.range (N + 1), A j) *
            eLpNorm f (ENNReal.ofReal q) volume := by
          rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun j _ => hA0 j)]
      _ ≤ _ := by
          gcongr
          exact hA.sum_le_tsum _ (fun j _ => hA0 j)
  calc eLpNorm (conv (Kc m δ) f) (ENNReal.ofReal q) volume
      ≤ atTop.liminf fun N => eLpNorm (F N) (ENNReal.ofReal q) volume :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm hFm _
          (ae_of_all _ fun x => conv_sum_tendsto m δ hδ f x)
    _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hbd)

end TaoBR.Carb.PartZb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR.Carb
alias bound_of_summable := TaoBR.Carb.PartZb.bound_of_summable

alias bound_infty := TaoBR.Carb.PartZb.bound_infty

alias crit_cases := TaoBR.Carb.PartZb.crit_cases

alias conv_Kc_aesm := TaoBR.Carb.PartZb.conv_Kc_aesm

/-- The `L^q` bound for `K * f`, `q < ∞`, from summable piece bounds. -/
theorem Kc_bound_of (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (q : ℝ) (hq : 1 ≤ q) (A : ℕ → ℝ)
    (hA0 : ∀ j, 0 ≤ A j) (hA : Summable A) (hb : PieceBd m δ q A) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E (m + 1), ℂ),
      eLpNorm (conv (Kc m δ) f) (ENNReal.ofReal q) volume ≤
        C * eLpNorm f (ENNReal.ofReal q) volume :=
  ⟨⟨∑' j, A j, tsum_nonneg hA0⟩, fun f => by
    have := bound_of_summable m δ hδ q hq A hA0 hA hb f
    rwa [ENNReal.ofReal_eq_coe_nnreal (tsum_nonneg hA0)] at this⟩

/-- The `Lᵖ` bound for `K * f` in every case. -/
theorem Kc_bound (m : ℕ) (hm : 1 ≤ m) (hR : ParabolicRestrictionConjecture m) (p : ℝ≥0∞)
    (hp : 1 ≤ p) (δ : ℝ) (hδ : critIndex (m + 1) p < δ) :
    ∃ C : ℝ≥0, ∀ f : 𝓢(E (m + 1), ℂ),
      eLpNorm (conv (Kc m δ) f) p volume ≤ C * eLpNorm f p volume := by
  obtain ⟨hδ0, hc⟩ := crit_cases m hm p hp δ hδ
  rcases hc with ⟨rfl, hδ'⟩ | ⟨q, rfl, hq1, hqc, hqδ⟩ | ⟨q, rfl, hq1, hq2⟩ | ⟨q, hq1, hqc, rfl, hqδ⟩
  · exact bound_infty m δ hδ'
  · obtain ⟨C, hC0, hC⟩ := piece_low m hm hR q hq1 hqc δ hδ0
    exact Kc_bound_of m δ hδ0 q hq1 _
      (fun j => by positivity) (summable_piece m C _ δ hqδ) hC
  · obtain ⟨A, hA0, hA, hb⟩ := piece_mid m hm hR q hq1 hq2 δ hδ0
    have h1 : 1 ≤ q := le_trans (by unfold pc; rw [le_div_iff₀ (by positivity)]; linarith) hq1
    exact Kc_bound_of m δ hδ0 q h1 A hA0 hA hb
  · obtain ⟨C, hC0, hC⟩ := piece_dual m hm hR q hq1 hqc δ hδ0
    have h1 : 1 ≤ q / (q - 1) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    exact Kc_bound_of m δ hδ0 (q / (q - 1)) h1 _
      (fun j => by positivity) (summable_piece m C _ δ hqδ) hC

/-- **Carbery's theorem.** -/
theorem carbery (m : ℕ) (hm : 1 ≤ m) :
    ParabolicRestrictionConjecture m → ParabolicBochnerRieszConjecture m := by
  intro hR η hη hηc p hp δ hδ
  have hδ0 : 0 < δ := lt_of_le_of_lt (le_max_right _ _) hδ
  obtain ⟨a, ha, hrep⟩ := kernel_rep m η hη hηc δ hδ0
  obtain ⟨C, hC⟩ := Kc_bound m hm hR p hp δ hδ
  refine ⟨(eLpNorm a 1 volume).toNNReal * C, fun f => ?_⟩
  have hfun : parabolicBochnerRiesz η δ (f : E (m + 1) → ℂ) = conv a (conv (Kc m δ) f) :=
    funext (hrep f)
  rw [hfun]
  have hmeas := conv_Kc_aesm m δ hδ0 f
  have hY := (conv_basic a ha p hp (conv (Kc m δ) f) hmeas).2.2
  calc eLpNorm (conv a (conv (Kc m δ) f)) p volume
      ≤ eLpNorm a 1 volume * eLpNorm (conv (Kc m δ) f) p volume := hY
    _ ≤ eLpNorm a 1 volume * (C * eLpNorm f p volume) := by gcongr; exact hC f
    _ = ((eLpNorm a 1 volume).toNNReal * C : ℝ≥0) * eLpNorm f p volume := by
      rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (memLp_one_iff_integrable.2 ha).eLpNorm_ne_top,
        mul_assoc]

end TaoBR.Carb
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
namespace TaoBR
theorem parabolicBochnerRieszConjecture_of_parabolicRestrictionConjecture_dev (m : ℕ) (hm : 1 ≤ m) :
    ParabolicRestrictionConjecture m → ParabolicBochnerRieszConjecture m :=
  Carb.carbery m hm

end TaoBR
end

section
open MeasureTheory Metric Set
open scoped FourierTransform ENNReal NNReal SchwartzMap RealInnerProductSpace ComplexConjugate
open TaoBR
theorem solution (m : ℕ) (hm : 1 ≤ m) :
    ParabolicRestrictionConjecture m → ParabolicBochnerRieszConjecture m := by
  exact TaoBR.parabolicBochnerRieszConjecture_of_parabolicRestrictionConjecture_dev m hm
end
