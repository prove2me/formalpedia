-- Prove2me | solution 1 for ThreeSigma.Upper.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T17:10:23.326557+00:00
-- url     : https://prove2.me/submissions/10d5fa79-0eb6-4ba9-b7fe-3a46571dd50d

import Mathlib
import Definitions.Def_ThreeSigma_Upper_Scalar
import Theorems.Thm_ThreeSigma_Upper_lemma_C_1

section
/-!
# Spencer's discrepancy theorem: complete upper and lower bounds

Self-contained (relative to Mathlib) combination of the original
`SpencerUpperBound.lean` and `SpencerLowerBound.lean` sources.

Requested toolchain: `leanprover/lean4:v4.36.0-rc2`.
The sources were originally developed against Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The final two theorem declarations are:
* `Stoc393.theorem_1_1 : Stoc393.LowerBoundClaim`
* `Stoc393.theorem_1_2 : Stoc393.UpperBoundClaim`

The proofs needed by earlier corollaries are named
`Stoc393.lowerBoundClaim_proof` and `Stoc393.upperBoundClaim_proof`.
-/

/- BEGIN original module: Stoc393.Basic -/
section

/-! Definitions and the nearest-sign rounding argument (Lemma 3.2).
The norm on `Fin d → ℝ` is the maximum absolute coordinate norm.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.Basic -/

/- BEGIN original module: Stoc393.Targets -/
section

/-! Exact main targets. `UpperBound.lean` proves `UpperBoundClaim`;
`LowerBound.lean` proves `LowerBoundClaim`.
The lower-bound probability is represented by exact uniform counting of all
random replacement matrices. The all-signings event is the meaning of
`disc(A) > threshold`, without needing to choose a minimizer.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.Targets -/

/- BEGIN original module: Stoc393.CappedTrace -/
section

/-! The capped trace argument underlying Lemma 3.4.
The orthonormal-basis construction follows the proof in the PDF, with the
heavy/light decomposition also used in the earlier local Spencer3.lean file.
-/

open scoped BigOperators
open Module
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.CappedTrace -/

/- BEGIN original module: Stoc393.ScalarReduction -/
section

/-! Algebraic implications surrounding the scalar inequality.
The comparison is an explicit hypothesis in this abstract reduction.
`ScalarBarrier.lean` proves it for the paper's concrete function.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

/-- Positive-input formula only. Its value at zero is NOT the paper's infinity. -/
noncomputable def phi (t : ℝ) : ℝ := 5 / Real.sinh (t ^ 2 / 3)

noncomputable def psi (t : ℝ) : ℝ := -t * deriv phi t - 2 * phi t

theorem phi_pos {t : ℝ} (ht : 0 < t) : 0 < phi t := by
  exact div_pos (by norm_num) (Real.sinh_pos_iff.mpr (by positivity))

/-- The two-case reduction in Appendix C, with comparison as an explicit input. -/
theorem cap_of_scalar_comparison {p q r θ : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hc : (1 - p / 4) * r ≤ 3 / 4 * q) :
    min r θ ≤ 3 / 4 * q + θ * p / 4 := by
  by_cases hp4 : 4 ≤ p
  · have hmul := mul_le_mul_of_nonneg_left hp4 hθ
    have hm := min_le_right r θ
    nlinarith
  · have hp4' : p < 4 := lt_of_not_ge hp4
    have hleft := mul_le_mul_of_nonneg_left (min_le_left r θ)
      (show 0 ≤ 1 - p / 4 by linarith)
    have hright := mul_le_mul_of_nonneg_left (min_le_right r θ)
      (show 0 ≤ p / 4 by positivity)
    nlinarith

end Stoc393

end
/- END original module: Stoc393.ScalarReduction -/

/- BEGIN original module: Stoc393.ScalarCalculus -/
section

/-! Elementary scalar calculus from Appendix C.
No assertion of the unproved equation (27) is made in this module.
-/

set_option autoImplicit false

namespace Stoc393

open scoped Topology

noncomputable def phiD (t : ℝ) : ℝ :=
  -10 * t * Real.cosh (t ^ 2 / 3) / (3 * Real.sinh (t ^ 2 / 3) ^ 2)

theorem hasDerivAt_phi {t : ℝ} (ht : 0 < t) : HasDerivAt phi (phiD t) t := by
  have hs : Real.sinh (t ^ 2 / 3) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
  have hu := ((hasDerivAt_id t).pow 2).div_const 3
  convert (hasDerivAt_const t (5 : ℝ)).div hu.sinh hs using 1
  all_goals try rfl
  · dsimp [phiD]
    ring

theorem deriv_phi {t : ℝ} (ht : 0 < t) : deriv phi t = phiD t :=
  (hasDerivAt_phi ht).deriv

theorem deriv_phi_neg {t : ℝ} (ht : 0 < t) : deriv phi t < 0 := by
  rw [deriv_phi ht, phiD]
  apply div_neg_of_neg_of_pos
  · have hc := Real.cosh_pos (t ^ 2 / 3)
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) ht) hc
  · have hs := Real.sinh_pos_iff.mpr (show 0 < t ^ 2 / 3 by positivity)
    positivity

theorem mul_cosh_sub_sinh_pos {u : ℝ} (hu : 0 < u) :
    0 < u * Real.cosh u - Real.sinh u := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x * Real.cosh x - Real.sinh x)
      (x * Real.sinh x) x := by
    convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x) using 1
    all_goals try rfl
    · dsimp
      ring
  have hm : StrictMonoOn (fun x : ℝ => x * Real.cosh x - Real.sinh x)
      (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hd x).deriv]
    exact mul_pos hx (Real.sinh_pos_iff.mpr hx)
  simpa using hm (show 0 ∈ Set.Ici (0 : ℝ) by simp) (show u ∈ Set.Ici (0 : ℝ) from hu.le) hu

theorem psi_formula {t : ℝ} (ht : 0 < t) :
    psi t = 10 / Real.sinh (t ^ 2 / 3) ^ 2 *
      ((t ^ 2 / 3) * Real.cosh (t ^ 2 / 3) - Real.sinh (t ^ 2 / 3)) := by
  have hs : Real.sinh (t ^ 2 / 3) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
  rw [psi, deriv_phi ht, phiD, phi]
  field_simp
  ring

theorem psi_pos {t : ℝ} (ht : 0 < t) : 0 < psi t := by
  rw [psi_formula ht]
  have hu : 0 < t ^ 2 / 3 := by positivity
  have hs := Real.sinh_pos_iff.mpr hu
  exact mul_pos (div_pos (by norm_num) (sq_pos_of_pos hs)) (mul_cosh_sub_sinh_pos hu)

noncomputable def phiDD (t : ℝ) : ℝ :=
  10 / (3 * Real.sinh (t ^ 2 / 3)) *
    (-Real.cosh (t ^ 2 / 3) / Real.sinh (t ^ 2 / 3) +
      2 * (t ^ 2 / 3) * (1 + 2 / Real.sinh (t ^ 2 / 3) ^ 2))

theorem hasDerivAt_phiD {t : ℝ} (ht : 0 < t) : HasDerivAt phiD (phiDD t) t := by
  have hs : Real.sinh (t ^ 2 / 3) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))
  have hu := ((hasDerivAt_id t).pow 2).div_const 3
  have hnum := ((hasDerivAt_id t).const_mul (-10)).mul hu.cosh
  have hden := (hu.sinh.pow 2).const_mul 3
  convert hnum.div hden (by exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)) using 1
  all_goals try rfl
  · dsimp [phiDD]
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq (t ^ 2 / 3)]

theorem second_deriv_phi {t : ℝ} (ht : 0 < t) : deriv (deriv phi) t = phiDD t := by
  have heq : deriv phi =ᶠ[𝓝 t] phiD := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    exact deriv_phi hx
  rw [heq.deriv_eq]
  exact (hasDerivAt_phiD ht).deriv

theorem curvature_numerator_pos {u : ℝ} (hu : 0 < u) :
    0 < 2 * u * (Real.sinh u ^ 2 + 2) - Real.sinh u * Real.cosh u := by
  let f : ℝ → ℝ := fun x =>
    2 * x * (Real.sinh x ^ 2 + 2) - Real.sinh x * Real.cosh x
  have hd (x : ℝ) : HasDerivAt f (3 + 4 * x * Real.sinh x * Real.cosh x) x := by
    convert (((hasDerivAt_id x).const_mul 2).mul
      (((Real.hasDerivAt_sinh x).pow 2).add_const 2)).sub
      ((Real.hasDerivAt_sinh x).mul (Real.hasDerivAt_cosh x)) using 1
    all_goals try rfl
    · dsimp
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
  have hm : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by dsimp [f]; fun_prop)
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hd x).deriv]
    have hs := Real.sinh_pos_iff.mpr hx
    have hc := Real.cosh_pos x
    positivity
  have h := hm (show 0 ∈ Set.Ici (0 : ℝ) by simp) hu.le hu
  simpa [f] using h

theorem second_deriv_phi_pos {t : ℝ} (ht : 0 < t) : 0 < deriv (deriv phi) t := by
  rw [second_deriv_phi ht, phiDD]
  have hu : 0 < t ^ 2 / 3 := by positivity
  have hs := Real.sinh_pos_iff.mpr hu
  apply mul_pos (div_pos (by norm_num) (mul_pos (by norm_num) hs))
  have h := curvature_numerator_pos hu
  have hid : -Real.cosh (t ^ 2 / 3) / Real.sinh (t ^ 2 / 3) +
      2 * (t ^ 2 / 3) * (1 + 2 / Real.sinh (t ^ 2 / 3) ^ 2) =
      (2 * (t ^ 2 / 3) * (Real.sinh (t ^ 2 / 3) ^ 2 + 2) -
        Real.sinh (t ^ 2 / 3) * Real.cosh (t ^ 2 / 3)) /
        Real.sinh (t ^ 2 / 3) ^ 2 := by
    field_simp
    ring
  rw [hid]
  exact div_pos h (sq_pos_of_pos hs)

/-- Equation (28), the scale derivative. -/
theorem hasDerivAt_scaled_phi {D s : ℝ} (hD : 0 < D) (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => (1 / s) * phi (D / Real.sqrt s))
      (psi (D / Real.sqrt s) / (2 * s ^ 2)) s := by
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have ht : 0 < D / Real.sqrt s := div_pos hD hsqrt
  have hT := (hasDerivAt_const s D).div (Real.hasDerivAt_sqrt hs.ne') hsqrt.ne'
  convert ((hasDerivAt_const s (1 : ℝ)).div (hasDerivAt_id s) hs.ne').mul
    ((hasDerivAt_phi ht).comp s hT) using 1
  all_goals try rfl
  · dsimp
    rw [psi, deriv_phi ht]
    field_simp
    rw [pow_succ (Real.sqrt s) 2, Real.sq_sqrt hs.le]
    ring

/-- Lemma 3.3(d), including strictness on the full positive half-line. -/
theorem scaled_phi_strictMonoOn {D : ℝ} (hD : 0 < D) :
    StrictMonoOn (fun s : ℝ => (1 / s) * phi (D / Real.sqrt s)) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro s hs
    exact (hasDerivAt_scaled_phi hD hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioi, Set.mem_Ioi] at hs
    rw [(hasDerivAt_scaled_phi hD hs).deriv]
    exact div_pos (psi_pos (div_pos hD (Real.sqrt_pos.mpr hs))) (by positivity)

theorem phi_at_c : phi (Real.sqrt (3 * Real.arsinh 10)) = 1 / 2 := by
  have ha : 0 < Real.arsinh 10 := Real.arsinh_pos_iff.mpr (by norm_num)
  unfold phi
  rw [Real.sq_sqrt (by positivity)]
  have heq : (3 * Real.arsinh 10) / 3 = Real.arsinh 10 := by ring
  rw [heq, Real.sinh_arsinh]
  norm_num

theorem phi_tendsto_atTop_zero : Filter.Tendsto phi (𝓝[>] (0 : ℝ)) Filter.atTop := by
  have h0 : Filter.Tendsto (fun t : ℝ => Real.sinh (t^2/3))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h : Continuous (fun t : ℝ => Real.sinh (t^2/3)) := by fun_prop
    simpa using (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < Real.sinh (t^2/3) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply Real.sinh_pos_iff.mpr
    have ht' : 0 < t := ht
    positivity
  have hgt : Filter.Tendsto (fun t : ℝ => Real.sinh (t^2/3))
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨h0, hpos⟩
  change Filter.Tendsto (fun t : ℝ => 5 / Real.sinh (t^2/3)) _ _
  simpa only [Function.comp_def, div_eq_mul_inv] using
    (tendsto_inv_nhdsGT_zero.comp hgt).const_mul_atTop (show (0 : ℝ) < 5 by norm_num)

end Stoc393

end
/- END original module: Stoc393.ScalarCalculus -/

/- BEGIN original module: Stoc393.ScalarPQ -/
section

/-! Analytic proof supplied by the user on 2026-10-30: the P + Q estimates. -/

open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.ScalarPQ -/

/- BEGIN original module: Stoc393.ScalarBarrier -/
section

/-! Equation (27), completing the analytic argument supplied by the user.
The proof uses exact real inequalities and algebra, not sampled values.
-/

set_option autoImplicit false
namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.ScalarBarrier -/

/- BEGIN original module: Stoc393.SecondVariation -/
section

/-! The second variation of the reciprocal-sinh potential, Lemma 3.5.
The abstract curve rule adapts the checked local Spencer3.lean construction.
-/

open scoped Topology BigOperators
open Filter
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.SecondVariation -/

/- BEGIN original module: Stoc393.PotentialCompact -/
section

/-! The extended-real barrier, including its infinite boundary values, and compact minimization. -/

open scoped Topology BigOperators ENNReal
open Filter Set
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.PotentialCompact -/

/- BEGIN original module: Stoc393.FaceTrace -/
section

/-! Capped trace after imposing the single orthogonality constraint on a cube face. -/

open scoped BigOperators
open Module
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.FaceTrace -/

/- BEGIN original module: Stoc393.MinimizerGeometry -/
section

/-! Feasible variations on cube faces and the contradiction at an interior minimizer. -/

open scoped Topology BigOperators ENNReal
open Filter Set Module
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.MinimizerGeometry -/

/- BEGIN original module: Stoc393.UpperBound -/
section

/-! Proposition 3.6 and the full upper bound (Theorems 1.2 and 3.1). -/

open scoped Topology BigOperators ENNReal
open Filter Set
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.UpperBound -/

/- BEGIN original module: Stoc393.UpperCorollaries -/
section

/-! Discrepancy, the square-matrix bound, and its explicit numerical constants. -/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

end Stoc393
end
end

section
namespace ThreeSigma.Upper

theorem Dev33.phi_eq : ThreeSigma.Upper.phi = Stoc393.phi := rfl

theorem Dev33.psi_eq : ThreeSigma.Upper.psi = Stoc393.psi := by
  funext t; simp only [ThreeSigma.Upper.psi, Stoc393.psi, Dev33.phi_eq]

theorem chk_lemma_3_3 :
    ((∀ t : ℝ, 0 < t → 0 < phi t ∧ deriv phi t < 0 ∧ 0 < deriv (deriv phi) t) ∧
      phi c = (1 / 2 : ℝ) ∧
      Filter.Tendsto phi (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop) ∧
    (∀ t : ℝ, 0 < t → 0 < psi t) ∧
    (∀ t θ : ℝ, 0 < t → 0 < θ →
      min (deriv (deriv phi) t) θ ≤ (3 / 4 : ℝ) * psi t + (1 / 4 : ℝ) * θ * phi t) ∧
    (∀ Δ : ℝ, 0 < Δ →
      StrictMonoOn (fun u : ℝ => u⁻¹ * phi (Δ / Real.sqrt u)) (Set.Ioi 0)) := by
  refine ⟨⟨fun t ht => ?_, ?_, ?_⟩, fun t ht => ?_, fun t θ ht hθ => ?_, fun Δ hΔ => ?_⟩
  · rw [Dev33.phi_eq]
    exact ⟨Stoc393.phi_pos ht, Stoc393.deriv_phi_neg ht, Stoc393.second_deriv_phi_pos ht⟩
  · rw [Dev33.phi_eq]; exact Stoc393.phi_at_c
  · rw [Dev33.phi_eq]; exact Stoc393.phi_tendsto_atTop_zero
  · rw [Dev33.psi_eq]; exact Stoc393.psi_pos ht
  · -- Appendix C's two-case reduction, applied to Lemma C.1.
    have h := Stoc393.cap_of_scalar_comparison (r := deriv (deriv phi) t)
      (Stoc393.phi_pos ht).le (Stoc393.psi_pos ht).le hθ.le
      (by rw [← Dev33.phi_eq, ← Dev33.psi_eq]; exact lemma_C_1 t ht)
    rw [← Dev33.phi_eq, ← Dev33.psi_eq] at h
    linarith
  · have h := Stoc393.scaled_phi_strictMonoOn hΔ
    simpa only [one_div, ← Dev33.phi_eq] using h

end ThreeSigma.Upper
end

theorem solution : type_of% @ThreeSigma.Upper.chk_lemma_3_3 := @ThreeSigma.Upper.chk_lemma_3_3
