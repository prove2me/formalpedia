-- Prove2me | solution 1 for ThreeSigma.Upper.proposition_3_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T17:15:03.91326+00:00
-- url     : https://prove2.me/submissions/93835e73-7304-4b34-93b7-c772222d1192

import Mathlib
import Definitions.Def_ThreeSigma_Upper_Geometry
import Definitions.Def_ThreeSigma_Upper_Potential
import Theorems.Thm_ThreeSigma_Upper_lemma_3_3
import Theorems.Thm_ThreeSigma_Upper_lemma_3_4
import Theorems.Thm_ThreeSigma_Upper_lemma_3_5

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

def InCube {n : ℕ} (z : Fin n → ℝ) : Prop := ∀ j, |z j| ≤ 1

def EntryBounded {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) : Prop :=
  ∀ i j, |A i j| ≤ 1

noncomputable def residual {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  n - ∑ j, z j ^ 2

theorem sq_le_abs_of_abs_le_one {t : ℝ} (ht : |t| ≤ 1) : t ^ 2 ≤ |t| := by
  have h := mul_le_mul_of_nonneg_left ht (abs_nonneg t)
  nlinarith [sq_abs t]

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

/-- The last dimension-count contradiction on page 9, with every bound explicit. -/
theorem dimension_contradiction {ι : Type*} [Fintype ι]
    (w p q : ι → ℝ) (J L D : ℝ)
    (hJ : 0 < J) (hL : 0 < L) (hq : ∑ i, q i = L)
    (hdim : J - 1 ≤ D)
    (htrace : D ≤ J / L * ∑ i, min (w i) (L / J))
    (hcap : ∀ i, min (w i) (L / J) ≤ 3 / 4 * q i + (L / J) * p i / 4)
    (hpotential : (∑ i, p i) < J - 4) : False := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hcap i)
  have hsum' : (∑ i, min (w i) (L / J)) ≤
      3 / 4 * L + (L / J) * (∑ i, p i) / 4 := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, hq] using hsum
  have hscaled := mul_le_mul_of_nonneg_left hsum' (div_pos hJ hL).le
  have heq : J / L * (3 / 4 * L + (L / J) * (∑ i, p i) / 4) =
      3 * J / 4 + (∑ i, p i) / 4 := by
    field_simp
  rw [heq] at hscaled
  linarith

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

noncomputable def rowPotential (q : ℝ × ℝ) : ℝ := (1/q.1)*phi (q.2/Real.sqrt q.1)

theorem rowPotential_contDiffAt {s a : ℝ} (hs : 0 < s) (ha : 0 < a) :
    ContDiffAt ℝ 2 rowPotential (s,a) := by
  have hsqrt : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  have hgap : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.2 / Real.sqrt q.1) (s,a) :=
    ContDiffAt.div (by fun_prop) ((by fun_prop : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1) (s,a)).sqrt hs.ne') hsqrt
  have hcomp := (contDiffAt_phi (div_pos ha (Real.sqrt_pos.mpr hs))).comp (s,a) hgap
  exact (ContDiffAt.div (by fun_prop) (by fun_prop) hs.ne').mul hcomp

noncomputable def residualScale {n : ℕ} (z : Fin n → ℝ) : ℝ := residual z-4

noncomputable def smoothPotential {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ i, rowPotential (residualScale z, D-A.mulVec z i)

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

noncomputable def barrierDenom (s a : ℝ) : ℝ := s / 5 * Real.sinh (a^2/(3*s))

noncomputable def extendedPotential {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z : Fin n → ℝ) : ℝ≥0∞ :=
  if 0 < residualScale z then
    ∑ i, (ENNReal.ofReal (barrierDenom (residualScale z) (D-A.mulVec z i)))⁻¹
  else 0

def feasibleSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ) : Set (Fin n → ℝ) :=
  {z | InCube z ∧ 0 ≤ residualScale z ∧ ∀ i, A.mulVec z i ≤ D}

theorem continuous_residualScale {n : ℕ} : Continuous (residualScale (n := n)) := by
  unfold residualScale residual
  fun_prop

theorem continuous_rowAction {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Continuous (fun z : Fin n → ℝ => A.mulVec z i) := by
  unfold Matrix.mulVec dotProduct
  fun_prop

theorem barrierDenom_pos {s a : ℝ} (hs : 0 < s) (ha : 0 < a) : 0 < barrierDenom s a := by
  unfold barrierDenom
  exact mul_pos (by positivity) (Real.sinh_pos_iff.mpr (by positivity))

theorem rowPotential_eq_inv_denom {s a : ℝ} (hs : 0 < s) :
    rowPotential (s,a) = (barrierDenom s a)⁻¹ := by
  unfold rowPotential phi barrierDenom
  dsimp
  rw [div_pow, Real.sq_sqrt hs.le]
  field_simp

theorem extendedPotential_eq_ofReal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z : Fin n → ℝ) (hs : 0 < residualScale z)
    (hg : ∀ i, 0 < D-A.mulVec z i) :
    extendedPotential A D z = ENNReal.ofReal (smoothPotential A D z) := by
  unfold extendedPotential smoothPotential
  rw [if_pos hs, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro i _
    rw [rowPotential_eq_inv_denom hs, ENNReal.ofReal_inv_of_pos (barrierDenom_pos hs (hg i))]
  · intro i _
    rw [rowPotential_eq_inv_denom hs]
    exact (inv_pos.mpr (barrierDenom_pos hs (hg i))).le

theorem extendedPotential_continuousAt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z : Fin n → ℝ) (hs : 0 < residualScale z) :
    ContinuousAt (extendedPotential A D) z := by
  have hden (i : Fin m) : ContinuousAt
      (fun y : Fin n → ℝ => barrierDenom (residualScale y) (D-A.mulVec y i)) z := by
    unfold barrierDenom
    exact (continuous_residualScale.continuousAt.div_const 5).mul
      (Real.continuous_sinh.continuousAt.comp
        (((continuous_const.sub (continuous_rowAction A i)).pow 2).continuousAt.div
          (continuous_const.mul continuous_residualScale).continuousAt (by positivity)))
  have hc : ContinuousAt (fun y => ∑ i,
      (ENNReal.ofReal (barrierDenom (residualScale y) (D-A.mulVec y i)))⁻¹) z := by
    apply tendsto_finsetSum
    intro i _
    exact (ENNReal.continuous_ofReal.continuousAt.comp (hden i)).inv
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_residualScale.continuousAt.eventually (lt_mem_nhds hs)] with y hy
  exact if_pos hy

theorem extendedPotential_lowerSemicontinuous {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ) : LowerSemicontinuous (extendedPotential A D) := by
  intro z
  by_cases hs : 0 < residualScale z
  · exact (extendedPotential_continuousAt A D z hs).lowerSemicontinuousAt
  · intro b hb
    simp [extendedPotential, hs] at hb

theorem feasibleSet_compact {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ) :
    IsCompact (feasibleSet A D) := by
  have hcube : IsCompact {z : Fin n → ℝ | InCube z} := by
    have hc := isCompact_pi_infinite (fun _ : Fin n =>
      (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)))
    simpa only [InCube, abs_le, mem_Icc] using hc
  have hclosed : IsClosed {z : Fin n → ℝ |
      0 ≤ residualScale z ∧ ∀ i, A.mulVec z i ≤ D} := by
    change IsClosed ({z : Fin n → ℝ | 0 ≤ residualScale z} ∩
      {z : Fin n → ℝ | ∀ i, A.mulVec z i ≤ D})
    apply (isClosed_le continuous_const continuous_residualScale).inter
    change IsClosed {z | ∀ i, A.mulVec z i ≤ D}
    rw [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le (continuous_rowAction A i) continuous_const)
  exact hcube.inter_right hclosed

theorem zero_mem_feasibleSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ)
    (hn : 4 ≤ n) (hD : 0 ≤ D) : (0 : Fin n → ℝ) ∈ feasibleSet A D := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simp
  · simp only [residualScale, residual, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, sub_zero]
    exact_mod_cast (show 0 ≤ (n : ℤ)-4 by omega)
  · intro i
    simpa using hD

theorem extendedPotential_exists_min {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ)
    (hn : 4 ≤ n) (hD : 0 ≤ D) :
    ∃ z ∈ feasibleSet A D, IsMinOn (extendedPotential A D) (feasibleSet A D) z := by
  exact LowerSemicontinuousOn.exists_isMinOn ⟨0, zero_mem_feasibleSet A D hn hD⟩
    (feasibleSet_compact A D) ((extendedPotential_lowerSemicontinuous A D).lowerSemicontinuousOn _)

theorem finite_extendedPotential_positive_gaps {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ) (z : Fin n → ℝ)
    (hs : 0 < residualScale z) (hg : ∀ i, A.mulVec z i ≤ D)
    (hfinite : extendedPotential A D z < ∞) : ∀ i, 0 < D-A.mulVec z i := by
  intro i
  have hrow : (ENNReal.ofReal (barrierDenom (residualScale z) (D-A.mulVec z i)))⁻¹ < ∞ := by
    apply ENNReal.sum_lt_top.mp (show
      (∑ i, (ENNReal.ofReal (barrierDenom (residualScale z) (D-A.mulVec z i)))⁻¹) < ∞ from
      (by simpa [extendedPotential, hs] using hfinite)) i (Finset.mem_univ i)
  have hnonzero : D-A.mulVec z i ≠ 0 := by
    intro heq
    simp [heq, barrierDenom] at hrow
  exact lt_of_le_of_ne (sub_nonneg.mpr (hg i)) (Ne.symm hnonzero)

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

noncomputable def activeCoords {n : ℕ} (z : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => |z j| < 1)

theorem residual_le_active_card {n : ℕ} {z : Fin n → ℝ} (hz : InCube z) :
    residual z ≤ ((activeCoords z).card : ℝ) := by
  classical
  have heq : residual z = ∑ j, (1-z j^2) := by
    simp [residual, Finset.sum_sub_distrib]
  rw [heq]
  calc
    ∑ j, (1-z j^2) ≤ ∑ j, if |z j| < 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hj
      · linarith [sq_nonneg (z j)]
      · have habs : |z j| = 1 := le_antisymm (hz j) (le_of_not_gt hj)
        have hsq : z j^2 = 1 := by nlinarith [sq_abs (z j)]
        simp [hsq]
    _ = _ := by simp [activeCoords]

theorem line_eventually_inCube {n : ℕ} {z : Fin n → ℝ} (hz : InCube z)
    (v : Fin n → ℝ) (hsupport : ∀ j ∉ activeCoords z, v j = 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), InCube (fun j => z j+t*v j) := by
  apply eventually_all.mpr
  intro j
  by_cases hj : |z j| < 1
  · have hc : ContinuousAt (fun t : ℝ => |z j+t*v j|) 0 := by fun_prop
    exact (hc.eventually (gt_mem_nhds (by simpa using hj))).mono (fun _ ht => ht.le)
  · have hv : v j = 0 := hsupport j (by simpa [activeCoords] using hj)
    simpa [hv] using (Eventually.of_forall (fun _ : ℝ => hz j) :
      ∀ᶠ _t in 𝓝 (0 : ℝ), |z j| ≤ 1)

theorem line_eventually_feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) {z : Fin n → ℝ} (hz : InCube z) (hs : 0 < residualScale z)
    (hg : ∀ i, 0 < D-A.mulVec z i) (v : Fin n → ℝ)
    (hsupport : ∀ j ∉ activeCoords z, v j = 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (fun j => z j+t*v j) ∈ feasibleSet A D ∧
      0 < residualScale (fun j => z j+t*v j) ∧
      ∀ i, 0 < D-A.mulVec (fun j => z j+t*v j) i := by
  have hsnear : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < residualScale (fun j => z j+t*v j) := by
    have hc := continuous_residualScale.comp
      (by fun_prop : Continuous (fun t : ℝ => fun j => z j+t*v j))
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hs))
  have hgnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < D-A.mulVec (fun j => z j+t*v j) i := by
    apply eventually_all.mpr
    intro i
    have hc := ((continuous_const (y := D)).sub (continuous_rowAction A i)).comp
      (by fun_prop : Continuous (fun t : ℝ => fun j => z j+t*v j))
    exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hg i))
  filter_upwards [line_eventually_inCube hz v hsupport, hsnear, hgnear] with t ht hs' hg'
  exact ⟨⟨ht, hs'.le, fun i => (sub_pos.mp (hg' i)).le⟩, hs', hg'⟩

theorem smoothPotential_contDiffAt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (z : Fin n → ℝ) (hs : 0 < residualScale z)
    (hg : ∀ i, 0 < D-A.mulVec z i) : ContDiffAt ℝ 2 (smoothPotential A D) z := by
  apply ContDiffAt.sum
  intro i _
  have hp : ContDiffAt ℝ 2 (fun y : Fin n → ℝ => (residualScale y,D-A.mulVec y i)) z := by
    unfold residualScale residual Matrix.mulVec dotProduct
    fun_prop
  exact ContDiffAt.comp (g := rowPotential)
    (f := fun y : Fin n → ℝ => (residualScale y,D-A.mulVec y i)) z
    (rowPotential_contDiffAt hs (hg i)) hp

theorem second_deriv_nonneg_of_local_min {f : ℝ → ℝ} {a : ℝ}
    (hmin : IsLocalMin f a) (hc : ContinuousAt f a) : 0 ≤ deriv (deriv f) a := by
  by_contra h
  have hneg : deriv (deriv f) a < 0 := lt_of_not_ge h
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [hmin,hmax] with x h₁ h₂
    exact le_antisymm h₂ h₁
  have hh := heq.deriv.deriv_eq
  have hconst : deriv (fun _ : ℝ => f a) = fun _ => 0 := by
    funext t
    exact deriv_const t (f a)
  rw [hconst, deriv_const] at hh
  linarith

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

noncomputable def discrepancyRadius (d n : ℕ) : ℝ :=
  Real.sqrt (3*(n : ℝ)*Real.arsinh (10*(d : ℝ)/(n : ℝ)))

def symmetricRows {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) :
    Matrix (Fin (d+d)) (Fin n) ℝ := Fin.append (fun i j => A i j) (fun i j => -A i j)

theorem discrepancyRadius_pos {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    0 < discrepancyRadius d n := by
  unfold discrepancyRadius
  apply Real.sqrt_pos.mpr
  have ha : 0 < Real.arsinh (10*(d : ℝ)/(n : ℝ)) := Real.arsinh_pos_iff.mpr (by positivity)
  positivity

theorem symmetricRows_entryBounded {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : EntryBounded A) : EntryBounded (symmetricRows A) := by
  intro i j
  refine Fin.addCases ?_ ?_ i
  · intro k
    change |Fin.append (α := Fin n → ℝ) (fun i j => A i j) (fun i j => -A i j) _ j| ≤ 1
    simpa only [Fin.append_left, Fin.append_right, abs_neg] using hA k j
  · intro k
    change |Fin.append (α := Fin n → ℝ) (fun i j => A i j) (fun i j => -A i j) _ j| ≤ 1
    simpa only [Fin.append_left, Fin.append_right, abs_neg] using hA k j

theorem symmetricRows_feasible_norm {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (D : ℝ) (hD : 0 ≤ D) {z : Fin n → ℝ} (hz : z ∈ feasibleSet (symmetricRows A) D) :
    ‖A.mulVec z‖ ≤ D := by
  apply (pi_norm_le_iff_of_nonneg hD).mpr
  intro i
  have hpos := hz.2.2 (Fin.castAdd d i)
  have hneg := hz.2.2 (Fin.natAdd d i)
  change (∑ j, Fin.append (α := Fin n → ℝ) (fun i j => A i j) (fun i j => -A i j) (Fin.castAdd d i) j*z j) ≤ D at hpos
  change (∑ j, Fin.append (α := Fin n → ℝ) (fun i j => A i j) (fun i j => -A i j) (Fin.natAdd d i) j*z j) ≤ D at hneg
  rw [Fin.append_left] at hpos
  rw [Fin.append_right] at hneg
  change |A.mulVec z i| ≤ D
  apply abs_le.mpr
  constructor
  · have hn : -(A.mulVec z i) ≤ D := by
      simpa only [symmetricRows, Matrix.mulVec, dotProduct, Fin.append_right, neg_mul, Finset.sum_neg_distrib] using hneg
    linarith
  · simpa only [symmetricRows, Matrix.mulVec, dotProduct, Fin.append_left] using hpos

theorem full_scale_potential_eq_one {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    ((d+d : ℕ) : ℝ)*((1/(n : ℝ))*phi (discrepancyRadius d n/Real.sqrt n)) = 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have ha : 0 < Real.arsinh (10*(d : ℝ)/(n : ℝ)) := Real.arsinh_pos_iff.mpr (by positivity)
  have hid : (discrepancyRadius d n/Real.sqrt n)^2/3 =
      Real.arsinh (10*(d : ℝ)/(n : ℝ)) := by
    unfold discrepancyRadius
    rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hnR.le]
    field_simp
  unfold phi
  rw [hid, Real.sinh_arsinh]
  push_cast
  field_simp
  ring

theorem initial_potential_lt_one {d n : ℕ} (A : Matrix (Fin (d+d)) (Fin n) ℝ)
    (hd : 0 < d) (hn : 4 < n) :
    extendedPotential A (discrepancyRadius d n) 0 < 1 := by
  have hnR : (4 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < residualScale (0 : Fin n → ℝ) := by
    simpa [residualScale,residual] using sub_pos.mpr hnR
  have hD := discrepancyRadius_pos hd (by omega : 0 < n)
  have hg (i : Fin (d+d)) : 0 < discrepancyRadius d n-A.mulVec 0 i := by simpa using hD
  rw [extendedPotential_eq_ofReal A (discrepancyRadius d n) 0 hs hg, ← ENNReal.ofReal_one]
  apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
  have hmono := scaled_phi_strictMonoOn hD
    (show (n : ℝ)-4 ∈ Ioi 0 from sub_pos.mpr hnR)
    (show (n : ℝ) ∈ Ioi 0 by simp only [mem_Ioi]; linarith)
    (show (n : ℝ)-4 < n by linarith)
  have hmult := mul_lt_mul_of_pos_left hmono (show (0 : ℝ) < ((d+d : ℕ) : ℝ) by positivity)
  rw [full_scale_potential_eq_one hd (by omega)] at hmult
  simpa [smoothPotential,rowPotential,residualScale,residual] using hmult

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
/-! Proposition 3.6 by the authors' minimizer argument (Song–Reis, SpencerCombined.lean),
with its three uses of Lemmas 3.3(c), 3.4 and 3.5 taken from the published statements. -/

open scoped Topology BigOperators ENNReal
open Filter Set Module

namespace Stoc393.Q351

/-- The weighted capped trace, from the published Lemma 3.4 (rows rescaled by `√(w i / L)`,
transported to coordinates by an orthonormal basis). -/
theorem capped_trace_of_lemma_3_4 {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (a : Fin m → E) (w : Fin m → ℝ) (K L : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hK : 0 < K) (hL : 0 < L)
    (ha : ∀ i, ‖a i‖ ^ 2 ≤ K)
    (hq : ∀ v : V, L * ‖v‖ ^ 2 ≤ ∑ i, w i * (inner ℝ (a i) (v : E)) ^ 2) :
    (finrank ℝ V : ℝ) ≤ K / L * ∑ i, min (w i) (L / K) := by
  let f := (stdOrthonormalBasis ℝ E).repr
  let b : Fin m → EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    fun i => Real.sqrt (w i / L) • f (a i)
  let V' := V.map f.toLinearEquiv.toLinearMap
  have hsq (i : Fin m) : Real.sqrt (w i / L) ^ 2 = w i / L :=
    Real.sq_sqrt (div_nonneg (hw i) hL.le)
  have hV : ∀ v ∈ V', ‖v‖ ^ 2 ≤ ∑ i, (inner ℝ (b i) v) ^ 2 := by
    rintro _ ⟨u, hu, rfl⟩
    have h : L * ‖u‖ ^ 2 ≤ ∑ i, w i * inner ℝ (a i) u ^ 2 := hq ⟨u, hu⟩
    change ‖f u‖ ^ 2 ≤ ∑ i, (inner ℝ (b i) (f u)) ^ 2
    have hnorm : ‖f u‖ = ‖u‖ := f.norm_map u
    have hin (i : Fin m) : inner ℝ (b i) (f u) ^ 2 =
        w i / L * inner ℝ (a i) u ^ 2 := by
      have : inner ℝ (f (a i)) (f u) = inner ℝ (a i) u := f.inner_map_map _ _
      simp only [b, inner_smul_left, RCLike.conj_to_real]
      change (Real.sqrt (w i / L) * inner ℝ (f (a i)) (f u)) ^ 2 = _
      rw [this, mul_pow, hsq]
    rw [hnorm, Finset.sum_congr rfl (fun i _ => hin i)]
    have : ∑ i, w i / L * inner ℝ (a i) u ^ 2 = (∑ i, w i * inner ℝ (a i) u ^ 2) / L := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, le_div_iff₀ hL]
    linarith
  have h34 := ThreeSigma.Upper.lemma_3_4 b V' hV
  have hdim : finrank ℝ V' = finrank ℝ V := LinearEquiv.finrank_map_eq _ _
  rw [hdim] at h34
  refine h34.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hb : ‖b i‖ ^ 2 = w i / L * ‖a i‖ ^ 2 := by
    simp only [b, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      hsq, LinearIsometryEquiv.norm_map]
  rw [hb]
  have hKL : K / L * min (w i) (L / K) = min (w i * K / L) 1 := by
    rw [mul_min_of_nonneg _ _ (div_nonneg hK.le hL.le)]
    congr 1
    · ring
    · field_simp
  rw [hKL]
  apply min_le_min_right
  have := mul_le_mul_of_nonneg_left (ha i) (div_nonneg (hw i) hL.le)
  calc w i / L * ‖a i‖ ^ 2 ≤ w i / L * K := this
    _ = w i * K / L := by ring

theorem face_capped_trace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : EntryBounded A) (z : Fin n → ℝ) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (w : Fin m → ℝ) (L : ℝ) (hw : ∀ i, 0 ≤ w i) (hL : 0 < L)
    (hq : ∀ v : Fin n → ℝ, (∑ j, z j*v j) = 0 → (∀ j ∉ J, v j = 0) →
      L*(∑ j, v j^2) ≤ ∑ i, w i*(A.mulVec v i)^2) :
    (J.card : ℝ)-1 ≤ J.card/L*(∑ i, min (w i) (L/J.card)) := by
  classical
  let restrict (a : Fin n → ℝ) : EuclideanSpace ℝ J := WithLp.toLp 2 (fun j => a j)
  let S : Submodule ℝ (EuclideanSpace ℝ J) := Submodule.span ℝ {restrict z}
  let W := Sᗮ
  have hSdim : finrank ℝ S ≤ 1 := by
    simpa [S] using! finrank_span_finset_le_card (R := ℝ) ({restrict z} : Finset (EuclideanSpace ℝ J))
  have hdim_sum : finrank ℝ S+finrank ℝ W = J.card := by
    simpa using S.finrank_add_finrank_orthogonal
  have hdim : (J.card : ℝ)-1 ≤ (finrank ℝ W : ℝ) := by
    have h : J.card ≤ 1+finrank ℝ W := by omega
    have h' : (J.card : ℝ) ≤ 1+(finrank ℝ W : ℝ) := by exact_mod_cast h
    linarith
  have ha (i : Fin m) : ‖restrict (A i)‖^2 ≤ (J.card : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ j : J, (restrict (A i) j)^2) ≤ ∑ _j : J, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        exact (sq_le_abs_of_abs_le_one (hA i j)).trans (hA i j)
      _ = _ := by simp
  have hbound := capped_trace_of_lemma_3_4 W (fun i => restrict (A i)) w J.card L
    hw (by exact_mod_cast hJ.card_pos) hL ha
  apply hdim.trans
  apply hbound
  intro u
  let v : Fin n → ℝ := fun j => if hj : j ∈ J then (u : EuclideanSpace ℝ J) ⟨j,hj⟩ else 0
  have hvout (j : Fin n) (hj : j ∉ J) : v j = 0 := by simp [v,hj]
  have hsum (a : Fin n → ℝ) :
      (∑ j, a j*v j) = inner ℝ (restrict a) (u : EuclideanSpace ℝ J) := by
    calc
      (∑ j, a j*v j) = ∑ j ∈ J, a j*v j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ J)
        intro j _ hj
        simp [hvout j hj]
      _ = ∑ j : J, a j*(u : EuclideanSpace ℝ J) j := by
        rw [← Finset.sum_coe_sort J]
        simp [v]
      _ = _ := by
        change (∑ j : J, a j*(u : EuclideanSpace ℝ J) j) =
          ∑ j : J, (u : EuclideanSpace ℝ J) j*a j
        apply Finset.sum_congr rfl
        intro j _
        ring
  have horth : (∑ j, z j*v j) = 0 := by
    rw [hsum]
    exact S.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_singleton (restrict z))) u.property
  have hnorm : (∑ j, v j^2) = ‖u‖^2 := by
    have h := hsum v
    have hrestrict : restrict v = (u : EuclideanSpace ℝ J) := by
      ext j
      simp [restrict,v]
    rw [hrestrict, real_inner_self_eq_norm_sq] at h
    simpa only [pow_two] using! h
  have h := hq v horth hvout
  simpa only [hnorm, Matrix.mulVec, dotProduct, hsum] using h

theorem inner_toLp {n : ℕ} (x y : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y) =
      ∑ j, x j * y j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- The authors' matrix form of Lemma 3.5, from the published Lemma 3.5. -/
theorem lemma_3_5_matrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (hD : 0 < D) (z v : Fin n → ℝ)
    (hs : 0 < residualScale z) (hg : ∀ i, 0 < D-A.mulVec z i)
    (hv : (∑ j, z j*v j) = 0) :
    residualScale z^2 * deriv (deriv (fun t : ℝ =>
      smoothPotential A D (fun j => z j+t*v j))) 0 =
      (∑ i, deriv (deriv phi) ((D-A.mulVec z i)/Real.sqrt (residualScale z)) *
        (A.mulVec v i)^2) -
      (∑ i, psi ((D-A.mulVec z i)/Real.sqrt (residualScale z))) * (∑ j, v j^2) := by
  let a : Fin m → ThreeSigma.Upper.E n := fun i => WithLp.toLp 2 (A i)
  let z' : ThreeSigma.Upper.E n := WithLp.toLp 2 z
  let v' : ThreeSigma.Upper.E n := WithLp.toLp 2 v
  have hAx (x : Fin n → ℝ) (i : Fin m) :
      inner ℝ (a i) (WithLp.toLp 2 x : ThreeSigma.Upper.E n) = A.mulVec x i := by
    rw [inner_toLp]; rfl
  have hsz : ThreeSigma.Upper.s z' = residualScale z := by
    simp [ThreeSigma.Upper.s, ThreeSigma.Upper.R, residualScale, residual,
      EuclideanSpace.real_norm_sq_eq, z']
  have hline (l : ℝ) : ThreeSigma.Upper.Phi a D (z' + l • v') =
      smoothPotential A D (fun j => z j + l * v j) := by
    have hzl : z' + l • v' = WithLp.toLp 2 (fun j => z j + l * v j) := by
      ext j; simp [z', v']
    have hs' : ThreeSigma.Upper.s (z' + l • v') = residualScale (fun j => z j + l * v j) := by
      rw [hzl]
      simp [ThreeSigma.Upper.s, ThreeSigma.Upper.R, residualScale, residual,
        EuclideanSpace.real_norm_sq_eq]
    unfold ThreeSigma.Upper.Phi smoothPotential rowPotential
    rw [hs', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hzl, hAx, one_div]
    rfl
  have hU : z' ∈ ThreeSigma.Upper.U a D := by
    refine ⟨by rw [hsz]; exact hs, fun i => ?_⟩
    rw [hAx]; linarith [hg i]
  have hv' : inner ℝ z' v' = 0 := by rw [inner_toLp]; exact hv
  have h := ThreeSigma.Upper.lemma_3_5 a D hD z' hU v' hv'
  have hfun : (fun l : ℝ => ThreeSigma.Upper.Phi a D (z' + l • v')) =
      fun t : ℝ => smoothPotential A D (fun j => z j + t * v j) := funext hline
  rw [hfun, hsz] at h
  rw [h, ← Finset.sum_mul]
  have hnv : ‖v'‖ ^ 2 = ∑ j, v j ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
  simp only [hAx, hnv]
  rfl

theorem minimizer_quadratic_form {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (D : ℝ) (hD : 0 < D) {z : Fin n → ℝ} (hz : InCube z) (hs : 0 < residualScale z)
    (hg : ∀ i, 0 < D-A.mulVec z i)
    (hmin : IsMinOn (extendedPotential A D) (feasibleSet A D) z)
    (v : Fin n → ℝ) (horth : (∑ j, z j*v j) = 0)
    (hsupport : ∀ j ∉ activeCoords z, v j = 0) :
    (∑ i, psi ((D-A.mulVec z i)/Real.sqrt (residualScale z))) * (∑ j, v j^2) ≤
      ∑ i, deriv (deriv phi) ((D-A.mulVec z i)/Real.sqrt (residualScale z)) *
        (A.mulVec v i)^2 := by
  have hlocal : IsLocalMin (fun t : ℝ => smoothPotential A D (fun j => z j+t*v j)) 0 := by
    filter_upwards [line_eventually_feasible A D hz hs hg v hsupport] with t ht
    have h := hmin ht.1
    change extendedPotential A D z ≤ extendedPotential A D (fun j => z j+t*v j) at h
    rw [extendedPotential_eq_ofReal A D z hs hg,
      extendedPotential_eq_ofReal A D _ ht.2.1 ht.2.2] at h
    have hnonneg : 0 ≤ smoothPotential A D (fun j => z j+t*v j) := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (one_div_nonneg.mpr ht.2.1.le)
        (phi_pos (div_pos (ht.2.2 i) (Real.sqrt_pos.mpr ht.2.1))).le
    simpa using (ENNReal.ofReal_le_ofReal_iff hnonneg).mp h
  have hc : ContinuousAt (fun t : ℝ => smoothPotential A D (fun j => z j+t*v j)) 0 := by
    have hh : ContinuousAt (smoothPotential A D) (fun j => z j+0*v j) := by
      simpa using (smoothPotential_contDiffAt A D z hs hg).continuousAt
    have hcomp := hh.comp (by fun_prop : ContinuousAt (fun t : ℝ => fun j => z j+t*v j) 0)
    exact hcomp
  have hsecond := second_deriv_nonneg_of_local_min hlocal hc
  have hidentity := lemma_3_5_matrix A D hD z v hs hg horth
  nlinarith [mul_nonneg (sq_nonneg (residualScale z)) hsecond]

/-- Lemma 3.3(c) in the authors' form, from the published Lemma 3.3. -/
theorem lemma_3_3_c {t θ : ℝ} (ht : 0 < t) (hθ : 0 < θ) :
    min (deriv (deriv phi) t) θ ≤ 3/4*psi t + θ*phi t/4 := by
  have h := ThreeSigma.Upper.lemma_3_3.2.2.1 t θ ht hθ
  have hphi : ThreeSigma.Upper.phi = phi := rfl
  have hpsi : ThreeSigma.Upper.psi = psi := by
    funext x; simp only [ThreeSigma.Upper.psi, psi, hphi]
  rw [hphi, hpsi] at h
  linarith

theorem minimizer_residualScale_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : EntryBounded A) (hm : 0 < m) (D : ℝ) (hD : 0 < D) {z : Fin n → ℝ}
    (hz : z ∈ feasibleSet A D)
    (hmin : IsMinOn (extendedPotential A D) (feasibleSet A D) z)
    (hvalue : extendedPotential A D z < 1) : residualScale z = 0 := by
  classical
  by_contra hzero
  have hs : 0 < residualScale z := lt_of_le_of_ne hz.2.1 (Ne.symm hzero)
  have hg := finite_extendedPotential_positive_gaps A D z hs hz.2.2
    (hvalue.trans (by simp))
  have hpotential : smoothPotential A D z < 1 := by
    rw [extendedPotential_eq_ofReal A D z hs hg, ← ENNReal.ofReal_one] at hvalue
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp hvalue
  let J := activeCoords z
  let t := fun i => (D-A.mulVec z i)/Real.sqrt (residualScale z)
  let w := fun i => deriv (deriv phi) (t i)
  let p := fun i => phi (t i)
  let q := fun i => psi (t i)
  let L := ∑ i, q i
  have ht (i : Fin m) : 0 < t i := div_pos (hg i) (Real.sqrt_pos.mpr hs)
  have hL : 0 < L := by
    let : NeZero m := ⟨by omega⟩
    exact Finset.sum_pos (fun i _ => psi_pos (ht i)) Finset.univ_nonempty
  have hres := residual_le_active_card hz.1
  have hJ : 0 < (J.card : ℝ) := by
    dsimp [residualScale] at hs
    dsimp [J]
    linarith
  have htrace := face_capped_trace A hA z J
    (Finset.card_pos.mp (by exact_mod_cast hJ)) w L
    (fun i => (second_deriv_phi_pos (ht i)).le) hL
    (fun v horth hsupport => minimizer_quadratic_form A D hD hz.1 hs hg hmin v horth hsupport)
  have hsum : (∑ i, p i) < (J.card : ℝ)-4 := by
    have hid : residualScale z*smoothPotential A D z = ∑ i, p i := by
      unfold smoothPotential rowPotential
      simp only [← Finset.mul_sum, p, t]
      field_simp
    have hh : (∑ i, p i) < residualScale z := by nlinarith
    exact hh.trans_le (sub_le_sub_right hres 4)
  exact dimension_contradiction w p q J.card L (J.card-1)
    hJ hL rfl le_rfl htrace
    (fun i => lemma_3_3_c (ht i) (div_pos hL hJ)) hsum

/-- The authors' Proposition 3.6 (doubled rows), existence half. -/
theorem proposition_3_6 {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : EntryBounded A) (hd : 0 < d) (hn : 4 < n) :
    ∃ z ∈ feasibleSet (symmetricRows A) (discrepancyRadius d n),
      ‖A.mulVec z‖ ≤ discrepancyRadius d n ∧ residual z = 4 := by
  have hD := discrepancyRadius_pos hd (by omega : 0 < n)
  have hinitial := initial_potential_lt_one (symmetricRows A) hd hn
  have hzero := zero_mem_feasibleSet (symmetricRows A) (discrepancyRadius d n) (by omega) hD.le
  obtain ⟨z,hz,hmin⟩ := extendedPotential_exists_min (symmetricRows A)
    (discrepancyRadius d n) (by omega) hD.le
  have hval : extendedPotential (symmetricRows A) (discrepancyRadius d n) z < 1 :=
    (hmin hzero).trans_lt hinitial
  refine ⟨z, hz, symmetricRows_feasible_norm A _ hD.le hz, ?_⟩
  exact sub_eq_zero.mp (minimizer_residualScale_zero (symmetricRows A)
    (symmetricRows_entryBounded A hA) (by omega) _ hD hz hmin hval)

end Stoc393.Q351

namespace ThreeSigma.Upper

theorem chk_proposition_3_6 {n d : ℕ} (hn : 4 < n) (A : Fin d → Fin n → ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    ∃ z : E n, z ∈ K A ∧ R z ≤ 4 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨WithLp.toLp 2 (fun _ => 1), ⟨fun j => by simp, fun i => i.elim0⟩, ?_⟩
    simp [R, EuclideanSpace.real_norm_sq_eq]
  · obtain ⟨z, hz, hnorm, hres⟩ :=
      Stoc393.Q351.proposition_3_6 (Matrix.of A) (fun i j => hA i j) hd hn
    refine ⟨WithLp.toLp 2 z, ⟨fun j => hz.1 j, fun i => ?_⟩, ?_⟩
    · have h := (norm_le_pi_norm ((Matrix.of A).mulVec z) i).trans hnorm
      rw [Real.norm_eq_abs] at h
      simpa [rowProduct, delta, Stoc393.discrepancyRadius, Matrix.mulVec, dotProduct] using h
    · have : R (WithLp.toLp 2 z : E n) = Stoc393.residual z := by
        simp [R, Stoc393.residual, EuclideanSpace.real_norm_sq_eq]
      rw [this, hres]

end ThreeSigma.Upper
end

theorem solution : type_of% @ThreeSigma.Upper.chk_proposition_3_6 := @ThreeSigma.Upper.chk_proposition_3_6
