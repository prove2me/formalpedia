-- Prove2me | solution 1 for PolarInequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:19:18.501855+00:00
-- url     : https://prove2.me/submissions/60cab238-b8f7-4e84-82b2-427832965f00

module
public import Definitions.Def_PHarmonicPoly_TangentialLaplacianBound
public import Definitions.Def_PHarmonicPoly_EpOpEvalPoly
public import Definitions.Def_PHarmonicPoly_EpAlg
public import Definitions.Def_PHarmonicPoly_AdaptedPlanarFrame
public import Definitions.Def_PHarmonicPoly_PolarInequality
public import Theorems.Thm_AdaptedPlanarFrame
public import Theorems.Thm_EpOpEvalPoly
public import Theorems.Thm_FrameHessian
public import Theorems.Thm_MvPolyContDiff
public import Theorems.Thm_MvPolyHessian
public import Theorems.Thm_TangentialLaplacianBound


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial Real
theorem _root_.solution {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) {p : ℝ}
    (hp : (n : ℝ) - 1 / 13 ≤ p)
    {P : MvPolynomial (Fin n) ℝ} (hhom : P.IsHomogeneous m)
    {e v₀ : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hv : ‖v₀‖ = 1)
    (hev : inner ℝ e v₀ = (0 : ℝ))
    (hmax : MvPolynomial.eval (fun i => e i) P = 1)
    (hbd : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 →
      |MvPolynomial.eval (fun i => y i) P| ≤ 1)
    (hE : EpAlg p P = 0)
    (hv0max : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → inner ℝ e v = (0 : ℝ) →
      MvPolynomial.eval (fun i => (Real.cos (π / m) • e + Real.sin (π / m) • v :
          EuclideanSpace ℝ (Fin n)) i) P
        ≤ MvPolynomial.eval (fun i => (Real.cos (π / m) • e + Real.sin (π / m) • v₀ :
          EuclideanSpace ℝ (Fin n)) i) P)
    (a b c q : ℝ)
    (hadef : MvPolynomial.eval (fun i => (Real.cos (π / m) • e + Real.sin (π / m) • v₀ :
      EuclideanSpace ℝ (Fin n)) i) P = -a)
    (hbdef : deriv (fun s : ℝ => MvPolynomial.eval
      (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (π / m)
        = (m : ℝ) * b)
    (hcdef : iteratedDeriv 2 (fun s : ℝ => MvPolynomial.eval
      (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (π / m)
        = (m : ℝ) ^ 2 * c)
    (hqdef : q = a ^ 2 + b ^ 2) (hq0 : 0 < q) :
    0 ≤ c - (p - 1 + ((n : ℝ) - p) / m) * a
        + ((n : ℝ) - 2) * (Real.cos (π / m) / (Real.sin (π / m) * m)) * b
        + (p - 2) * (b ^ 2 * (c - a) / q) := by
  classical
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hp2 : (2 : ℝ) < p := by
    have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hthpos : 0 < Real.pi / m := div_pos Real.pi_pos hmpos
  have hthlt : Real.pi / m < Real.pi := by
    rw [div_lt_iff₀ hmpos]
    nlinarith [Real.pi_pos]
  have hspos : 0 < Real.sin (Real.pi / m) := Real.sin_pos_of_pos_of_lt_pi hthpos hthlt
  have hsne : Real.sin (Real.pi / m) ≠ 0 := ne_of_gt hspos
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hcssq : Real.cos (Real.pi / m) ^ 2 + Real.sin (Real.pi / m) ^ 2 = 1 := by
    rw [add_comm]
    exact Real.sin_sq_add_cos_sq _
  have hee : (inner ℝ e e : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, he]
    norm_num
  have hvv : (inner ℝ v₀ v₀ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hve : (inner ℝ v₀ e : ℝ) = 0 := by
    rw [real_inner_comm]
    exact hev
  -- the adapted orthonormal frame, from `AdaptedPlanarFrame`
  obtain ⟨i0, i1, fb, hi01, hb0, hb1, hperp0⟩ :=
    AdaptedPlanarFrame (show 2 ≤ n by omega) he hv hev (Real.pi / m)
  have hx0x0 : (inner ℝ ((Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) ((Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← hb0, fb.orthonormal.1 i0]
    norm_num
  have hetet : (inner ℝ ((-Real.sin (Real.pi / m) • e + Real.cos (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) ((-Real.sin (Real.pi / m) • e + Real.cos (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← hb1, fb.orthonormal.1 i1]
    norm_num
  have hx0et : (inner ℝ ((Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) ((-Real.sin (Real.pi / m) • e + Real.cos (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) : ℝ) = 0 := by
    rw [← hb0, ← hb1]
    exact fb.orthonormal.2 hi01
  have hetx0 : (inner ℝ ((-Real.sin (Real.pi / m) • e + Real.cos (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) ((Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) : ℝ) = 0 := by
    rw [real_inner_comm]
    exact hx0et
  obtain ⟨htan1, htan2, htan3⟩ := TangentialLaplacianBound hn hm hhom he hv hev hv0max
  -- the gradient has no component outside the plane
  have hperp : ∀ i ∈ (Finset.univ.erase i0).erase i1,
      (inner ℝ (fb i) (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)) : ℝ) = 0 := by
    intro i hi
    have hne1 : i ≠ i1 := (Finset.mem_erase.mp hi).1
    have hne0 : i ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hbn : ‖fb i‖ = 1 := fb.orthonormal.1 i
    obtain ⟨hei, hvi⟩ := hperp0 i hne0 hne1
    rw [real_inner_comm]
    exact htan1 (fb i) hbn hei hvi
  have hfr := FrameHessian (show 1 ≤ m by omega) hhom e v₀ (Real.pi / m)
  have hgx0 : (inner ℝ ((Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)) : ℝ) = -((m : ℝ) * a) := by
    rw [real_inner_comm, hfr.1, hadef]
    ring
  have hget : (inner ℝ ((-Real.sin (Real.pi / m) • e + Real.cos (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)) : ℝ) = (m : ℝ) * b := by
    rw [real_inner_comm, hfr.2.1, hbdef]
  have hgrad : (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)) = (-((m : ℝ) * a)) • ((Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) + ((m : ℝ) * b) • ((-Real.sin (Real.pi / m) • e + Real.cos (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) := by
    have hsr := fb.sum_repr (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀))
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)] at hsr
    rw [← Finset.add_sum_erase _ _
      (Finset.mem_erase.mpr ⟨Ne.symm hi01, Finset.mem_univ i1⟩)] at hsr
    have hrest0 : ∑ i ∈ (Finset.univ.erase i0).erase i1,
        (fb.repr (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀))).ofLp i • fb i = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [OrthonormalBasis.repr_apply_apply, hperp i hi, zero_smul]
    rw [hrest0, add_zero, OrthonormalBasis.repr_apply_apply,
      OrthonormalBasis.repr_apply_apply, hb0, hb1, hgx0, hget] at hsr
    exact hsr.symm
  -- bilinearity of the Hessian in each slot
  have hlin1 : ∀ (α β : ℝ) (z z' w : EuclideanSpace ℝ (Fin n)),
      iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![α • z + β • z', w] = α * iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![z, w] + β * iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![z', w] := by
    intro α β z z' w
    rw [MvPolyHessian P _ _ _, MvPolyHessian P _ _ _, MvPolyHessian P _ _ _,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hc : ((α • z + β • z' : EuclideanSpace ℝ (Fin n)) i) = α * z i + β * z' i := rfl
    rw [hc]
    ring
  have hlin2 : ∀ (α β : ℝ) (w z z' : EuclideanSpace ℝ (Fin n)),
      iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![w, α • z + β • z'] = α * iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![w, z] + β * iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![w, z'] := by
    intro α β w z z'
    rw [MvPolyHessian P _ _ _, MvPolyHessian P _ _ _, MvPolyHessian P _ _ _,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hc : ((α • z + β • z' : EuclideanSpace ℝ (Fin n)) j) = α * z j + β * z' j := rfl
    rw [hc]
    ring
  -- symmetry of the second derivative (pm-0014)
  have hsymm : IsSymmSndFDerivAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) ((Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) :=
    (MvPolyContDiff P (⊤ : WithTop ℕ∞)).contDiffAt.isSymmSndFDerivAt le_top
  have hsym : ∀ z z' : EuclideanSpace ℝ (Fin n), iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![z, z'] = iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![z', z] :=
    fun z z' => IsSymmSndFDerivAt.iteratedFDeriv_cons (hf := hsymm)
  -- orthonormal expansion of a planar vector's squared norm
  have hexp2 : ∀ X Y : EuclideanSpace ℝ (Fin n), (inner ℝ X X : ℝ) = 1 → (inner ℝ Y Y : ℝ) = 1 →
      (inner ℝ X Y : ℝ) = 0 → (inner ℝ Y X : ℝ) = 0 →
      ∀ α β : ℝ, (inner ℝ (α • X + β • Y) (α • X + β • Y) : ℝ) = α ^ 2 + β ^ 2 := by
    intro X Y hXX hYY hXY hYX α β
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hXX, hYY, hXY, hYX]
    ring
  have hquad : ∀ (X Y : EuclideanSpace ℝ (Fin n)) (α β : ℝ),
      iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![α • X + β • Y, α • X + β • Y]
        = α ^ 2 * iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![X, X] + α * β * iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![X, Y]
          + β * α * iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![Y, X] + β ^ 2 * iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![Y, Y] := by
    intro X Y α β
    rw [hlin1, hlin2, hlin2]
    ring
  have hnorm2 : ‖(gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀))‖ ^ 2 = (m : ℝ) ^ 2 * q := by
    rw [← real_inner_self_eq_norm_sq, hgrad,
      hexp2 ((Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) ((-Real.sin (Real.pi / m) • e + Real.cos (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) hx0x0 hetet hx0et hetx0, hqdef]
    ring
  have hHgg : iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![(gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)), (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀))] = (m : ℝ) ^ 3 * ((m : ℝ) * b ^ 2 * c - ((m : ℝ) - 1) * a ^ 3 - (2 * (m : ℝ) - 1) * a * b ^ 2) := by
    rw [hgrad, hquad, hsym ((-Real.sin (Real.pi / m) • e + Real.cos (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) ((Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)),
      hfr.2.2.1, hfr.2.2.2.1, hfr.2.2.2.2, hadef, hbdef, hcdef]
    ring
  have hEp : ‖(gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀))‖ ^ 2 * Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) ((Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n))
      + (p - 2) * iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![(gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)), (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀))] = 0 := by
    have h := EpOpEvalPoly p P ((Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n))
    rw [hE, map_zero] at h
    simp only [EpOp] at h
    exact h
  rw [hnorm2, hHgg] at hEp
  -- substitute the Laplacian bound
  rw [hadef, hbdef, hcdef] at htan3
  have hposq : (0 : ℝ) < (m : ℝ) ^ 2 * q := by positivity
  have hprod : (0 : ℝ) ≤ (m : ℝ) ^ 2 * q
      * (((m : ℝ) * ((m : ℝ) + (n : ℝ) - 2) * (-a) + (m : ℝ) ^ 2 * c + ((n : ℝ) - 2) * ((m : ℝ) * b) * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m))) - Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) ((Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n))) :=
    mul_nonneg (le_of_lt hposq) (sub_nonneg.mpr htan3)
  have hineq : (0 : ℝ) ≤ (m : ℝ) ^ 2 * q * ((m : ℝ) * ((m : ℝ) + (n : ℝ) - 2) * (-a) + (m : ℝ) ^ 2 * c + ((n : ℝ) - 2) * ((m : ℝ) * b) * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m))) + (p - 2) * ((m : ℝ) ^ 3 * ((m : ℝ) * b ^ 2 * c - ((m : ℝ) - 1) * a ^ 3 - (2 * (m : ℝ) - 1) * a * b ^ 2)) := by
    linarith [hEp, hprod]
  have hqq : a ^ 2 + b ^ 2 ≠ 0 := by
    rw [← hqdef]
    exact hqne
  have hm4q : (0 : ℝ) < (m : ℝ) ^ 4 * q := by positivity
  have hfac : c - (p - 1 + ((n : ℝ) - p) / m) * a
      + ((n : ℝ) - 2) * (Real.cos (Real.pi / m) / (Real.sin (Real.pi / m) * m)) * b + (p - 2) * (b ^ 2 * (c - a) / q)
      = ((m : ℝ) ^ 2 * q * ((m : ℝ) * ((m : ℝ) + (n : ℝ) - 2) * (-a) + (m : ℝ) ^ 2 * c + ((n : ℝ) - 2) * ((m : ℝ) * b) * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m))) + (p - 2) * ((m : ℝ) ^ 3 * ((m : ℝ) * b ^ 2 * c - ((m : ℝ) - 1) * a ^ 3 - (2 * (m : ℝ) - 1) * a * b ^ 2))) / ((m : ℝ) ^ 4 * q) := by
    rw [hqdef]
    field_simp
    ring
  rw [hfac]
  exact div_nonneg hineq (le_of_lt hm4q)
