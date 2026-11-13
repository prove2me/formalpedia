-- Prove2me | solution 1 for ThreeSigma.Upper.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T17:10:23.196334+00:00
-- url     : https://prove2.me/submissions/143ab739-6b53-4294-a6c6-f0bb81dbb1d8

import Mathlib
import Definitions.Def_ThreeSigma_Upper_Potential

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

noncomputable def residual {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  n - ∑ j, z j ^ 2

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

theorem contDiffAt_phi {t : ℝ} (ht : 0 < t) : ContDiffAt ℝ 2 phi t := by
  unfold phi
  apply ContDiffAt.div (by fun_prop) (by fun_prop)
  exact ne_of_gt (Real.sinh_pos_iff.mpr (by positivity))

theorem second_comp_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {p pd : ℝ → E} {v a : E}
    (hF : ContDiffAt ℝ 2 F (p 0)) (hp : HasDerivAt p v 0)
    (hevent : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt p (pd t) t)
    (hpd0 : pd 0 = v) (hpd : HasDerivAt pd a 0) :
    HasDerivAt (deriv (fun t => F (p t)))
      ((fderiv ℝ (fderiv ℝ F) (p 0) v) v + fderiv ℝ F (p 0) a) 0 := by
  have hf2 : DifferentiableAt ℝ (fderiv ℝ F) (p 0) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have houter := hf2.hasFDerivAt.comp_hasDerivAt 0 hp
  have hd := houter.clm_apply hpd
  have hlocal : deriv (fun t => F (p t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => fderiv ℝ F (p t) (pd t)) := by
    have hsmooth := hp.continuousAt.tendsto.eventually (hF.eventually (by norm_num))
    filter_upwards [hsmooth, hevent] with t ht hpt
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hpt).deriv
  simpa only [hpd0, Function.comp_apply] using hd.congr_of_eventuallyEq hlocal

theorem quadratic_scale_second {F : ℝ × ℝ → ℝ} {s a b w : ℝ}
    (hF : ContDiffAt ℝ 2 F (s, a)) :
    HasDerivAt (deriv (fun t : ℝ => F (s-b*t^2, a+t*w)))
      (deriv (deriv (fun t : ℝ => F (s, a+t*w))) 0 -
        2*b*deriv (fun r : ℝ => F (r,a)) s) 0 := by
  let p : ℝ → ℝ × ℝ := fun t => (s-b*t^2,a+t*w)
  let pd : ℝ → ℝ × ℝ := fun t => (-2*b*t,w)
  have hp (t : ℝ) : HasDerivAt p (pd t) t := by
    apply HasDerivAt.prodMk
    · convert (((hasDerivAt_id t).pow 2).const_mul b).const_sub s using 1
      all_goals dsimp [pd, id]
      all_goals ring
    · simpa using ((hasDerivAt_id t).mul_const w).const_add a
  have hpd : HasDerivAt pd (-2*b,0) 0 := by
    simpa [pd] using
      ((hasDerivAt_id (0 : ℝ)).const_mul (-2*b)).prodMk (hasDerivAt_const 0 w)
  have hp0 : p 0 = (s,a) := by simp [p]
  have hpd0 : pd 0 = (0,w) := by simp [pd]
  have hpath := second_comp_curve (hp0.symm ▸ hF) (hpd0 ▸ hp 0)
    (Eventually.of_forall hp) hpd0 hpd
  have hq (t : ℝ) : HasDerivAt (fun t : ℝ => (s,a+t*w)) (0,w) t :=
    (hasDerivAt_const t s).prodMk (by simpa using ((hasDerivAt_id t).mul_const w).const_add a)
  have hfixed := second_comp_curve (by simpa using hF) (hq 0)
    (Eventually.of_forall hq) rfl (hasDerivAt_const (0 : ℝ) ((0 : ℝ),w))
  have hfixed' : deriv (deriv (fun t : ℝ => F (s,a+t*w))) 0 =
      (fderiv ℝ (fderiv ℝ F) (s,a) (0,w)) (0,w) := by
    simpa using hfixed.deriv
  have hpartial : deriv (fun r : ℝ => F (r,a)) s = fderiv ℝ F (s,a) (1,0) :=
    ((hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s a))).deriv
  have hacc : ((-2*b : ℝ),(0 : ℝ)) = (-2*b) • ((1 : ℝ),(0 : ℝ)) := by simp
  have hcoef : (fderiv ℝ (fderiv ℝ F) (s,a) (0,w)) (0,w) +
      fderiv ℝ F (s,a) (-2*b,0) =
      deriv (deriv (fun t : ℝ => F (s,a+t*w))) 0 -
        2*b*deriv (fun r : ℝ => F (r,a)) s := by
    rw [hfixed', hpartial, hacc, map_smul]
    simp only [smul_eq_mul]
    ring
  rw [← hcoef]
  simpa [p, pd] using hpath

noncomputable def rowPotential (q : ℝ × ℝ) : ℝ := (1/q.1)*phi (q.2/Real.sqrt q.1)

theorem rowPotential_contDiffAt {s a : ℝ} (hs : 0 < s) (ha : 0 < a) :
    ContDiffAt ℝ 2 rowPotential (s,a) := by
  have hsqrt : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  have hgap : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.2 / Real.sqrt q.1) (s,a) :=
    ContDiffAt.div (by fun_prop) ((by fun_prop : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1) (s,a)).sqrt hs.ne') hsqrt
  have hcomp := (contDiffAt_phi (div_pos ha (Real.sqrt_pos.mpr hs))).comp (s,a) hgap
  exact (ContDiffAt.div (by fun_prop) (by fun_prop) hs.ne').mul hcomp

theorem fixed_scale_second {s a w : ℝ} (hs : 0 < s) (ha : 0 < a) :
    HasDerivAt (deriv (fun t : ℝ => rowPotential (s,a+t*w)))
      (phiDD (a/Real.sqrt s)*w^2/s^2) 0 := by
  have hsqrt := Real.sqrt_pos.mpr hs
  have ht : 0 < a/Real.sqrt s := div_pos ha hsqrt
  have hgap (t : ℝ) : HasDerivAt (fun t : ℝ => (a+t*w)/Real.sqrt s) (w/Real.sqrt s) t := by
    simpa using (((hasDerivAt_id t).mul_const w).const_add a).div_const (Real.sqrt s)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (a+t*w)/Real.sqrt s := by
    exact (by fun_prop : Continuous (fun t : ℝ => (a+t*w)/Real.sqrt s)).continuousAt.eventually
      (lt_mem_nhds (by simpa using ht))
  have heq : deriv (fun t : ℝ => rowPotential (s,a+t*w)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => (1/s)*(phiD ((a+t*w)/Real.sqrt s)*(w/Real.sqrt s))) := by
    filter_upwards [hnear] with t ht'
    exact (((hasDerivAt_phi ht').comp t (hgap t)).const_mul (1/s)).deriv
  have hd := (((hasDerivAt_phiD ht).comp_of_eq 0 (hgap 0) (by simp)).const_mul (1/s))
    |>.mul_const (w/Real.sqrt s)
  simp only [Function.comp_apply] at hd
  have heqfun : (fun t => (1/s)*phiD ((a+t*w)/Real.sqrt s)*(w/Real.sqrt s)) =
      (fun t => (1/s)*(phiD ((a+t*w)/Real.sqrt s)*(w/Real.sqrt s))) := by funext t; ring
  rw [heqfun] at hd
  have hcoef : (1/s)*(phiDD (a/Real.sqrt s)*(w/Real.sqrt s))*(w/Real.sqrt s) =
      phiDD (a/Real.sqrt s)*w^2/s^2 := by
    field_simp
    rw [Real.sq_sqrt hs.le]
  rw [hcoef] at hd
  exact hd.congr_of_eventuallyEq heq

theorem row_potential_second {s a b w : ℝ} (hs : 0 < s) (ha : 0 < a) :
    HasDerivAt (deriv (fun t : ℝ => rowPotential (s-b*t^2,a+t*w)))
      ((phiDD (a/Real.sqrt s)*w^2-psi (a/Real.sqrt s)*b)/s^2) 0 := by
  have h := quadratic_scale_second (b := b) (w := w) (rowPotential_contDiffAt hs ha)
  rw [(fixed_scale_second (w := w) hs ha).deriv] at h
  have hpartial : deriv (fun r : ℝ => rowPotential (r,a)) s = psi (a/Real.sqrt s)/(2*s^2) :=
    (hasDerivAt_scaled_phi ha hs).deriv
  rw [hpartial] at h
  convert h using 1
  ring

noncomputable def residualScale {n : ℕ} (z : Fin n → ℝ) : ℝ := residual z-4

noncomputable def smoothPotential {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ i, rowPotential (residualScale z, D-A.mulVec z i)

theorem residualScale_line {n : ℕ} (z v : Fin n → ℝ)
    (hv : (∑ j, z j*v j) = 0) (t : ℝ) :
    residualScale (fun j => z j+t*v j) = residualScale z-t^2*(∑ j, v j^2) := by
  have heq : (∑ j, (z j+t*v j)^2) =
      (∑ j, z j^2)+2*t*(∑ j, z j*v j)+t^2*(∑ j, v j^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold residualScale residual
  rw [heq, hv]
  ring

theorem mulVec_line {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (z v : Fin n → ℝ) (t : ℝ) (i : Fin m) :
    A.mulVec (fun j => z j+t*v j) i = A.mulVec z i+t*A.mulVec v i := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem second_deriv_finite_sum {ι : Type*} [Fintype ι] (f : ι → ℝ → ℝ)
    (c : ι → ℝ) (hf : ∀ i, ContDiffAt ℝ 2 (f i) 0)
    (hd : ∀ i, HasDerivAt (deriv (f i)) (c i) 0) :
    HasDerivAt (deriv (fun t => ∑ i, f i t)) (∑ i, c i) 0 := by
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, ContDiffAt ℝ 2 (f i) t :=
    eventually_all.mpr (fun i => (hf i).eventually (by norm_num))
  have heq : deriv (fun t => ∑ i, f i t) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∑ i, deriv (f i) t) := by
    filter_upwards [hnear] with t ht
    exact deriv_fun_sum (fun i _ => (ht i).differentiableAt (by norm_num))
  exact (HasDerivAt.fun_sum (fun i _ => hd i)).congr_of_eventuallyEq heq

/-- Lemma 3.5, with Euclidean squared norms written as sums of squares. -/
theorem lemma_3_5 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z v : Fin n → ℝ)
    (hs : 0 < residualScale z) (hg : ∀ i, 0 < D-A.mulVec z i)
    (hv : (∑ j, z j*v j) = 0) :
    residualScale z^2 * deriv (deriv (fun t : ℝ =>
      smoothPotential A D (fun j => z j+t*v j))) 0 =
      (∑ i, deriv (deriv phi) ((D-A.mulVec z i)/Real.sqrt (residualScale z)) *
        (A.mulVec v i)^2) -
      (∑ i, psi ((D-A.mulVec z i)/Real.sqrt (residualScale z))) * (∑ j, v j^2) := by
  let s := residualScale z
  let b := ∑ j, v j^2
  let a := fun i => D-A.mulVec z i
  let w := fun i => -(A.mulVec v i)
  let f := fun i (t : ℝ) => rowPotential (s-b*t^2,a i+t*w i)
  have hf : ∀ i, ContDiffAt ℝ 2 (f i) 0 := by
    intro i
    have h := rowPotential_contDiffAt hs (hg i)
    have hp : ContDiffAt ℝ 2 (fun t : ℝ => (s-b*t^2,a i+t*w i)) 0 := by fun_prop
    have hh : ContDiffAt ℝ 2 rowPotential (s-b*0^2,a i+0*w i) := by simpa [s,a] using h
    exact ContDiffAt.comp (g := rowPotential)
      (f := fun t : ℝ => (s-b*t^2,a i+t*w i)) 0 hh hp
  have hd := second_deriv_finite_sum f
    (fun i => (phiDD (a i/Real.sqrt s)*(w i)^2-psi (a i/Real.sqrt s)*b)/s^2)
    hf (fun i => row_potential_second hs (hg i))
  have hline : (fun t : ℝ => smoothPotential A D (fun j => z j+t*v j)) =
      (fun t => ∑ i, f i t) := by
    funext t
    unfold smoothPotential
    apply Finset.sum_congr rfl
    intro i _
    rw [residualScale_line z v hv, mulVec_line]
    dsimp [f,s,b,a,w]
    congr 1
    ext <;> ring
  rw [hline, hd.deriv]
  have hdd (i : Fin m) : deriv (deriv phi) (a i/Real.sqrt s) = phiDD (a i/Real.sqrt s) :=
    second_deriv_phi (div_pos (hg i) (Real.sqrt_pos.mpr hs))
  change s^2*(∑ i, (phiDD (a i/Real.sqrt s)*(w i)^2-psi (a i/Real.sqrt s)*b)/s^2) =
    (∑ i, deriv (deriv phi) (a i/Real.sqrt s)*(A.mulVec v i)^2) -
      (∑ i, psi (a i/Real.sqrt s))*b
  simp_rw [hdd]
  rw [← Finset.sum_div, mul_div_cancel₀ _ (pow_ne_zero 2 hs.ne')]
  simp only [Finset.sum_sub_distrib, Finset.sum_mul, w, neg_sq]

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

theorem Dev35.inner_eq {n : ℕ} (x y : E n) : inner ℝ x y = ∑ j, x j * y j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem Dev35.s_eq {n : ℕ} (z : E n) : s z = Stoc393.residualScale (WithLp.ofLp z) := by
  simp [s, R, Stoc393.residualScale, Stoc393.residual, EuclideanSpace.real_norm_sq_eq]

theorem Dev35.Phi_line {m n : ℕ} (a : Fin m → E n) (Δ : ℝ) (z v : E n) (l : ℝ) :
    Phi a Δ (z + l • v) = Stoc393.smoothPotential (Matrix.of fun i j => a i j) Δ
      (fun j => WithLp.ofLp z j + l * WithLp.ofLp v j) := by
  have hzl : WithLp.ofLp (z + l • v) = fun j => WithLp.ofLp z j + l * WithLp.ofLp v j := by
    funext j; simp
  unfold Phi Stoc393.smoothPotential Stoc393.rowPotential
  rw [Dev35.s_eq, hzl, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Dev35.inner_eq, one_div]
  congr 3

theorem chk_lemma_3_5 {m n : ℕ} (a : Fin m → E n) (Δ : ℝ) (hΔ : 0 < Δ)
    (z : E n) (hz : z ∈ U a Δ) (v : E n) (hv : inner ℝ z v = 0) :
    (s z) ^ 2 * deriv (deriv (fun l : ℝ => Phi a Δ (z + l • v))) 0 =
      (∑ i, deriv (deriv phi) ((Δ - inner ℝ (a i) z) / Real.sqrt (s z)) *
        (inner ℝ (a i) v) ^ 2) -
      (∑ i, psi ((Δ - inner ℝ (a i) z) / Real.sqrt (s z)) * ‖v‖ ^ 2) := by
  set A : Matrix (Fin m) (Fin n) ℝ := Matrix.of fun i j => a i j with hA
  have hAz (x : E n) (i : Fin m) : inner ℝ (a i) x = A.mulVec (WithLp.ofLp x) i := by
    rw [Dev35.inner_eq]; simp [A, Matrix.mulVec, dotProduct]
  have hfun : (fun l : ℝ => Phi a Δ (z + l • v)) = fun l : ℝ =>
      Stoc393.smoothPotential A Δ (fun j => WithLp.ofLp z j + l * WithLp.ofLp v j) := by
    funext l; exact Dev35.Phi_line a Δ z v l
  have hs : 0 < Stoc393.residualScale (WithLp.ofLp z) := by rw [← Dev35.s_eq]; exact hz.1
  have hg : ∀ i, 0 < Δ - A.mulVec (WithLp.ofLp z) i := fun i => by
    rw [← hAz]; exact sub_pos.mpr (hz.2 i)
  have hv' : (∑ j, WithLp.ofLp z j * WithLp.ofLp v j) = 0 := by
    rw [← hv, Dev35.inner_eq]
  have h := Stoc393.lemma_3_5 A Δ (WithLp.ofLp z) (WithLp.ofLp v) hs hg hv'
  have hnv : ‖v‖ ^ 2 = ∑ j, WithLp.ofLp v j ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  rw [hfun, Dev35.s_eq, h, hnv, ← Finset.sum_mul]
  simp only [hAz]
  rfl

end ThreeSigma.Upper
end

theorem solution : type_of% @ThreeSigma.Upper.chk_lemma_3_5 := @ThreeSigma.Upper.chk_lemma_3_5
