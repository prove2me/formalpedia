-- Prove2me | solution 1 for ThreeSigma.Upper.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T17:10:23.331563+00:00
-- url     : https://prove2.me/submissions/28a62606-bde6-470a-8654-ab05b5fe688c

import Mathlib
import Definitions.Def_ThreeSigma_Upper_Scalar

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

end Stoc393

end
/- END original module: Stoc393.ScalarCalculus -/

/- BEGIN original module: Stoc393.ScalarPQ -/
section

/-! Analytic proof supplied by the user on 2026-10-30: the P + Q estimates. -/

open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

noncomputable def scalarP (u : ℝ) : ℝ := (u-5)*Real.exp u + 20*u-10
noncomputable def scalarQ (u : ℝ) : ℝ :=
  -(49*u-23)*Real.exp (-u) + 120*u*Real.exp (-2*u)
noncomputable def scalarW (u : ℝ) : ℝ :=
  (u-5)*Real.exp u + 76/5*u-10 + (23-u)*(3-u)*Real.exp (-2)
noncomputable def scalarWD (u : ℝ) : ℝ :=
  (u-4)*Real.exp u + 76/5 + (2*u-26)*Real.exp (-2)

theorem exp_one_bounds : 8/3 < Real.exp 1 ∧ Real.exp 1 < 68/25 := by
  have hl := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 5
  have hr := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
    (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hl hr
  constructor <;> linarith

theorem exp_two_eq : Real.exp 2 = Real.exp 1 ^ 2 := by
  rw [← Real.exp_nat_mul]
  norm_num

theorem exp_neg_two_lower : (625 : ℝ)/4624 ≤ Real.exp (-2) := by
  have hp : Real.exp 1 ^ 2 * Real.exp (-2) = 1 := by
    rw [← exp_two_eq, ← Real.exp_add]
    norm_num
  have he := exp_one_bounds.2
  have he0 := Real.exp_pos (1 : ℝ)
  have he2 : Real.exp 1 ^ 2 ≤ (68/25 : ℝ)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right he2 (Real.exp_nonneg (-2))
  nlinarith

theorem hasDerivAt_scalarP (u : ℝ) :
    HasDerivAt scalarP (20+(u-4)*Real.exp u) u := by
  convert (((hasDerivAt_id u).sub_const 5).mul (Real.hasDerivAt_exp u)).add
    ((hasDerivAt_id u).const_mul 20) |>.sub_const 10 using 1
  all_goals try rfl
  · dsimp
    ring

theorem hasDerivAt_scalarW (u : ℝ) : HasDerivAt scalarW (scalarWD u) u := by
  convert ((((hasDerivAt_id u).sub_const 5).mul (Real.hasDerivAt_exp u)).add
    ((hasDerivAt_id u).const_mul (76/5)) |>.sub_const 10).add
    ((((hasDerivAt_id u).const_sub 23).mul
      ((hasDerivAt_id u).const_sub 3)).mul_const (Real.exp (-2))) using 1
  all_goals try rfl
  · dsimp [scalarWD]
    ring

theorem hasDerivAt_scalarWD (u : ℝ) :
    HasDerivAt scalarWD ((u-3)*Real.exp u + 2*Real.exp (-2)) u := by
  convert ((((hasDerivAt_id u).sub_const 4).mul (Real.hasDerivAt_exp u)).add_const
    (76/5)).add ((((hasDerivAt_id u).const_mul 2).sub_const 26).mul_const
      (Real.exp (-2))) using 1
  all_goals try rfl
  · dsimp
    ring

theorem scalarW_concave : ConcaveOn ℝ (Set.Icc 1 2) scalarW := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 1 2)
    (by unfold scalarW; fun_prop)
    (fun x _ => (hasDerivAt_scalarW x).hasDerivWithinAt)
    (fun x _ => (hasDerivAt_scalarWD x).hasDerivWithinAt)
  intro x hx
  rw [interior_Icc] at hx
  have he : 8/3 < Real.exp x :=
    exp_one_bounds.1.trans_le (Real.exp_le_exp.mpr hx.1.le)
  have hn : Real.exp (-2) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have hp := mul_le_mul_of_nonneg_right (show x-3 ≤ -1 by linarith [hx.2])
    (Real.exp_nonneg x)
  nlinarith

theorem scalarW_endpoints : 1/4 < scalarW 1 ∧ 1 < scalarW 2 := by
  have he := exp_one_bounds.2
  have he0 := Real.exp_pos (1 : ℝ)
  have he2 : Real.exp 1 ^ 2 ≤ (68/25 : ℝ)^2 := by nlinarith
  have hn := exp_neg_two_lower
  unfold scalarW
  rw [exp_two_eq]
  constructor <;> nlinarith

theorem scalarW_pos {u : ℝ} (hu : u ∈ Set.Icc 1 2) : 0 < scalarW u := by
  have h := scalarW_concave.min_le_of_mem_Icc
    (show (1 : ℝ) ∈ Set.Icc 1 2 by norm_num)
    (show (2 : ℝ) ∈ Set.Icc 1 2 by norm_num) hu
  have hl : 0 < min (scalarW 1) (scalarW 2) :=
    lt_min (by linarith [scalarW_endpoints.1]) (by linarith [scalarW_endpoints.2])
  exact hl.trans_le h

theorem scalarPQ_ge_W {u : ℝ} (hu : u ∈ Set.Icc 1 2) :
    scalarW u ≤ scalarP u + scalarQ u := by
  have hs : Real.exp (-2*u) = Real.exp (-u)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsq := mul_nonneg (show 0 ≤ 120*u by linarith [hu.1])
    (sq_nonneg (Real.exp (-u) - 1/5))
  have ht := Real.add_one_le_exp (2-u)
  have hmul := mul_le_mul_of_nonneg_right ht (Real.exp_nonneg (-2))
  have hexp : Real.exp (2-u) * Real.exp (-2) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hmul
  have hmul' := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 23-u by linarith [hu.2])
  unfold scalarW scalarP scalarQ
  rw [hs]
  nlinarith

theorem scalarPQ_pos_small {u : ℝ} (hu : u ∈ Set.Icc 1 2) :
    0 < scalarP u + scalarQ u :=
  (scalarW_pos hu).trans_le (scalarPQ_ge_W hu)

theorem scalarP_derivative_lower (u : ℝ) : -1/8 < 20+(u-4)*Real.exp u := by
  have ht := Real.add_one_le_exp (3-u)
  have hm := mul_le_mul_of_nonneg_right ht (Real.exp_nonneg u)
  have heq : Real.exp (3-u) * Real.exp u = Real.exp 1 ^ 3 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq] at hm
  have he0 := Real.exp_pos (1 : ℝ)
  have he := exp_one_bounds.2.le
  have he3 := pow_le_pow_left₀ he0.le he 3
  nlinarith

theorem scalarP_lower_two_four {u : ℝ} (hu : u ∈ Set.Icc 2 4) :
    15/2 < scalarP u := by
  have hm : Monotone (fun x : ℝ => scalarP x + x/8) := by
    apply monotone_of_hasDerivAt_nonneg
      (fun x => (hasDerivAt_scalarP x).add ((hasDerivAt_id x).div_const 8))
    intro x
    dsimp
    linarith [scalarP_derivative_lower x]
  have h := hm hu.1
  have he := exp_one_bounds.2.le
  have he2 := pow_le_pow_left₀ (Real.exp_nonneg 1) he 2
  unfold scalarP at h ⊢
  dsimp at h
  rw [exp_two_eq] at h
  nlinarith [hu.2]

theorem scalarP_lower {u : ℝ} (hu : 2 ≤ u) : 15/2 < scalarP u := by
  by_cases h4 : u ≤ 4
  · exact scalarP_lower_two_four ⟨hu, h4⟩
  · have hm : MonotoneOn scalarP (Set.Ici 4) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 4)
        (by unfold scalarP; fun_prop)
        (fun x _ => (hasDerivAt_scalarP x).hasDerivWithinAt)
      intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      have hp : 0 ≤ (x-4)*Real.exp x :=
        mul_nonneg (by linarith [hx]) (Real.exp_nonneg x)
      linarith
    exact (scalarP_lower_two_four (show (4 : ℝ) ∈ Set.Icc 2 4 by norm_num)).trans_le
      (hm (by simp) (le_of_not_ge h4) (le_of_not_ge h4))

theorem scalarQ_algebra {u r : ℝ} (hr : 0 ≤ r) (hur : u*r ≤ 3/4)
    (hc : 0 ≤ 49-120*r^2) :
    -7 < -(49*u-23)*r^2 + 120*u*r^4 := by
  have hm := mul_le_mul_of_nonneg_right hur (mul_nonneg hc hr)
  have hsq := mul_nonneg (sq_nonneg (r-3/10)) (show 0 ≤ 90*r+77 by linarith)
  nlinarith

theorem scalarQ_lower {u : ℝ} (hu : 2 ≤ u) : -7 < scalarQ u := by
  let r := Real.exp (-u/2)
  have hr : 0 < r := Real.exp_pos _
  have he := exp_one_bounds.1
  have hp : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have hn0 := Real.exp_pos (-1)
  have hn : Real.exp (-1) < 3/8 := by nlinarith
  have hrle : r ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have ht := Real.add_one_le_exp (u/2-1)
  have hm := mul_le_mul_of_nonneg_right ht hr.le
  have heq : Real.exp (u/2-1)*r = Real.exp (-1) := by
    dsimp [r]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hm
  have hur : u*r ≤ 3/4 := by nlinarith
  have hc : 0 ≤ 49-120*r^2 := by nlinarith
  have h := scalarQ_algebra hr.le hur hc
  have h2 : Real.exp (-u) = r^2 := by
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h4 : Real.exp (-2*u) = r^4 := by
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [scalarQ, h2, h4] using h

theorem scalarPQ_pos {u : ℝ} (hu : 1 ≤ u) : 0 < scalarP u + scalarQ u := by
  by_cases h2 : u ≤ 2
  · exact scalarPQ_pos_small ⟨hu, h2⟩
  · have hp := scalarP_lower (le_of_not_ge h2)
    have hq := scalarQ_lower (le_of_not_ge h2)
    linarith

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

theorem sinh_one_bound : Real.sinh 1 ≤ 5/4 := by
  have he := exp_one_bounds.2
  have hp : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have hz := Real.exp_pos (-1)
  have hneg : 1/4 ≤ Real.exp (-1) := by nlinarith
  rw [Real.sinh_eq]
  linarith

theorem scalar_gap_identity {t : ℝ} (ht : 0 < t) :
    (48 * Real.exp (-2*(t^2/3)) * Real.sinh (t^2/3)^4 / 5) *
      (3/4*psi t - (1-phi t/4)*deriv (deriv phi) t) =
    scalarP (t^2/3) + scalarQ (t^2/3) +
      31*(t^2/3-1)*Real.exp (-3*(t^2/3)) +
      (20*(t^2/3)+10)*Real.exp (-4*(t^2/3)) +
      (17*(t^2/3)+13)*Real.exp (-5*(t^2/3)) := by
  let u := t^2/3
  have hs : Real.sinh u ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr (by dsimp [u]; positivity))
  have he : Real.exp (-u) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hscale (k : ℕ) : Real.exp (-(k : ℝ)*u) = Real.exp (-u)^k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hinv : Real.exp u = (Real.exp (-u))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  rw [psi_formula ht, second_deriv_phi ht]
  unfold scalarP scalarQ phi phiDD
  change (48 * Real.exp (-2*u) * Real.sinh u^4 / 5) *
      (3/4*(10/Real.sinh u^2*(u*Real.cosh u-Real.sinh u)) -
       (1-(5/Real.sinh u)/4) *
         (10/(3*Real.sinh u)*(-Real.cosh u/Real.sinh u+2*u*(1+2/Real.sinh u^2)))) =
    (u-5)*Real.exp u+20*u-10 +
    (-(49*u-23)*Real.exp (-u)+120*u*Real.exp (-2*u)) +
    31*(u-1)*Real.exp (-3*u)+(20*u+10)*Real.exp (-4*u)+(17*u+13)*Real.exp (-5*u)
  have h2 := hscale 2
  have h3 := hscale 3
  have h4 := hscale 4
  have h5 := hscale 5
  norm_num only [Nat.cast_ofNat] at h2 h3 h4 h5
  rw [h2, h3, h4, h5]
  field_simp
  rw [Real.sinh_eq, Real.cosh_eq, hinv]
  field_simp
  ring

/-- The scalar-barrier inequality, equation (27), with no added hypotheses. -/
theorem scalar_barrier_inequality {t : ℝ} (ht : 0 < t) :
    (1-phi t/4)*deriv (deriv phi) t ≤ 3/4*psi t := by
  by_cases hp : 4 ≤ phi t
  · have hl : (1-phi t/4)*deriv (deriv phi) t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (second_deriv_phi_pos ht).le
    exact hl.trans (mul_nonneg (by norm_num) (psi_pos ht).le)
  · have hu : 1 < t^2/3 := by
      by_contra hu
      have hs : Real.sinh (t^2/3) ≤ 5/4 :=
        (Real.sinh_le_sinh.mpr (le_of_not_gt hu)).trans sinh_one_bound
      have hs0 : 0 < Real.sinh (t^2/3) := Real.sinh_pos_iff.mpr (by positivity)
      have hp' : 4 ≤ phi t := by
        unfold phi
        apply (le_div_iff₀ hs0).mpr
        linarith
      exact hp hp'
    have hPQ := scalarPQ_pos hu.le
    have h1 : 0 ≤ 31*(t^2/3-1)*Real.exp (-3*(t^2/3)) :=
      mul_nonneg (by linarith) (Real.exp_nonneg _)
    have h2 : 0 ≤ (20*(t^2/3)+10)*Real.exp (-4*(t^2/3)) :=
      mul_nonneg (by linarith) (Real.exp_nonneg _)
    have h3 : 0 ≤ (17*(t^2/3)+13)*Real.exp (-5*(t^2/3)) :=
      mul_nonneg (by linarith) (Real.exp_nonneg _)
    have hid := scalar_gap_identity ht
    have hscale : 0 < 48*Real.exp (-2*(t^2/3))*Real.sinh (t^2/3)^4/5 := by
      have hs : 0 < Real.sinh (t^2/3) := Real.sinh_pos_iff.mpr (by positivity)
      positivity
    have hgap : 0 < 3/4*psi t-(1-phi t/4)*deriv (deriv phi) t := by
      apply (mul_pos_iff_of_pos_left hscale).mp
      rw [hid]
      linarith
    linarith

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

theorem Dev.phi_eq : ThreeSigma.Upper.phi = Stoc393.phi := rfl

theorem Dev.psi_eq : ThreeSigma.Upper.psi = Stoc393.psi := by
  funext t; simp only [ThreeSigma.Upper.psi, Stoc393.psi, Dev.phi_eq]

theorem chk_lemma_C_1 (t : ℝ) (ht : 0 < t) :
    (1 - phi t / 4) * deriv (deriv phi) t ≤ (3 / 4 : ℝ) * psi t := by
  rw [Dev.psi_eq, Dev.phi_eq]
  exact Stoc393.scalar_barrier_inequality ht

end ThreeSigma.Upper
end

theorem solution : type_of% @ThreeSigma.Upper.chk_lemma_C_1 := @ThreeSigma.Upper.chk_lemma_C_1
