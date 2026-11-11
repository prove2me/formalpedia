-- Prove2me | solution 1 for SurrogateOps.theorem_19
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T11:18:40.717195+00:00
-- url     : https://prove2.me/submissions/0c56a238-faea-4a61-9dbf-e8acfbf06001

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_SurrogateOps_GradAccAt
import Definitions.Def_SurrogateOps_HessAccAt

namespace SurrogateOps.S09Derivative

open scoped Topology BigOperators ContDiff
open Filter
attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι]

/-- The second derivative of a finite product, retaining each first-derivative
sum inside `smulRight`. Only local `C²` regularity at the evaluation point is used. -/
theorem hessian_finset_prod (s : Finset ι) (f : ι → E → ℝ) (x : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    fderiv ℝ (fderiv ℝ (fun y => ∏ i ∈ s, f i y)) x =
      ∑ i ∈ s,
        ((∏ j ∈ s.erase i, f j x) • fderiv ℝ (fderiv ℝ (f i)) x +
          (∑ j ∈ s.erase i,
            (∏ k ∈ (s.erase i).erase j, f k x) • fderiv ℝ (f j) x).smulRight
              (fderiv ℝ (f i) x)) := by
  have hnear : ∀ᶠ y in 𝓝 x, ∀ i ∈ s, DifferentiableAt ℝ (f i) y := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact ((hf i hi).eventually (by norm_num)).mono fun y hy =>
      hy.differentiableAt (by norm_num)
  have hEq : fderiv ℝ (fun y => ∏ i ∈ s, f i y) =ᶠ[𝓝 x]
      (fun y => ∑ i ∈ s, (∏ j ∈ s.erase i, f j y) • fderiv ℝ (f i) y) := by
    filter_upwards [hnear] with y hy
    exact fderiv_finsetProd hy
  rw [hEq.fderiv_eq]
  apply HasFDerivAt.fderiv
  apply HasFDerivAt.fun_sum
  intro i hi
  have hc : HasFDerivAt (fun y => ∏ j ∈ s.erase i, f j y)
      (∑ j ∈ s.erase i,
        (∏ k ∈ (s.erase i).erase j, f k x) • fderiv ℝ (f j) x) x :=
    HasFDerivAt.finsetProd fun j hj =>
      ((hf j (Finset.mem_of_mem_erase hj)).differentiableAt (by norm_num)).hasFDerivAt
  have hd : DifferentiableAt ℝ (fderiv ℝ (f i)) x :=
    ((hf i hi).fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  exact hc.smul hd.hasFDerivAt

/-- The finite-product Hessian with one term per factor and one term per
ordered pair of distinct factors. -/
theorem hessian_finset_prod_expanded (s : Finset ι) (f : ι → E → ℝ) (x : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    fderiv ℝ (fderiv ℝ (fun y => ∏ i ∈ s, f i y)) x =
      (∑ i ∈ s, (∏ j ∈ s.erase i, f j x) • fderiv ℝ (fderiv ℝ (f i)) x) +
      ∑ i ∈ s, ∑ j ∈ s.erase i,
        (∏ k ∈ (s.erase i).erase j, f k x) •
          (fderiv ℝ (f j) x).smulRight (fderiv ℝ (f i) x) := by
  rw [hessian_finset_prod s f x hf, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ext v w
  simp [ContinuousLinearMap.smulRight_apply, Finset.sum_mul, mul_assoc]

/-- The exact two-factor Hessian formula under local `C²` hypotheses. -/
theorem hessian_mul (f g : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x =
      f x • fderiv ℝ (fderiv ℝ g) x +
      g x • fderiv ℝ (fderiv ℝ f) x +
      (fderiv ℝ f x).smulRight (fderiv ℝ g x) +
      (fderiv ℝ g x).smulRight (fderiv ℝ f x) := by
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y ∧ DifferentiableAt ℝ g y := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    exact ⟨hfy.differentiableAt (by norm_num), hgy.differentiableAt (by norm_num)⟩
  have hEq : fderiv ℝ (fun y => f y * g y) =ᶠ[𝓝 x]
      (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) := by
    filter_upwards [hnear] with y hy
    exact fderiv_fun_mul hy.1 hy.2
  have hdf := hf.differentiableAt (by norm_num)
  have hdg := hg.differentiableAt (by norm_num)
  have hddf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hddg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  rw [hEq.fderiv_eq]
  calc
    _ = (f x • fderiv ℝ (fderiv ℝ g) x +
          (fderiv ℝ f x).smulRight (fderiv ℝ g x)) +
        (g x • fderiv ℝ (fderiv ℝ f) x +
          (fderiv ℝ g x).smulRight (fderiv ℝ f x)) := by
      exact ((hdf.hasFDerivAt.smul hddg.hasFDerivAt).add
        (hdg.hasFDerivAt.smul hddf.hasFDerivAt)).fderiv
    _ = _ := by abel

/-- The tensor error splits into one error in each factor. -/
theorem norm_smulRight_sub_le (a a' b b' : E →L[ℝ] ℝ) :
    ‖a.smulRight b - a'.smulRight b'‖ ≤
      ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ := by
  have heq : a.smulRight b - a'.smulRight b' =
      (a - a').smulRight b + a'.smulRight (b - b') := by
    ext v w
    simp only [sub_apply, add_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
    ring
  rw [heq]
  simpa only [ContinuousLinearMap.norm_smulRight_apply] using
    norm_add_le ((a - a').smulRight b) (a'.smulRight (b - b'))

/-- Swap the ordered pair in the first error term. This is why the gradient
coefficient is `M j + Mt j`, without an additional factor two. -/
theorem pair_error_reindex (s : Finset ι) (c : ι → ι → ℝ) (e M Mt : ι → ℝ)
    (hc : ∀ i j, c i j = c j i) :
    (∑ i ∈ s, ∑ j ∈ s.erase i,
      |c i j| * (e j * M i + Mt j * e i)) =
    ∑ i ∈ s, (∑ j ∈ s.erase i, |c i j| * (M j + Mt j)) * e i := by
  have hswap :
      (∑ i ∈ s, ∑ j ∈ s.erase i, |c i j| * (e j * M i)) =
      ∑ j ∈ s, ∑ i ∈ s.erase j, |c i j| * (e j * M i) := by
    apply Finset.sum_comm'
    intro i j
    simp only [Finset.mem_erase]
    tauto
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hswap, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hc j i]
  ring

/-- An operator-norm bound for the algebraic expression in a product Hessian.
The coefficient of every gradient error has the required symmetric form. -/
theorem hessian_expression_error (s : Finset ι) (c : ι → ℝ) (d : ι → ι → ℝ)
    (a b : ι → E →L[ℝ] ℝ) (A B : ι → E →L[ℝ] E →L[ℝ] ℝ)
    (eg eh M Mt : ι → ℝ)
    (hd : ∀ i j, d i j = d j i)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ M i) (hb : ∀ i ∈ s, ‖b i‖ ≤ Mt i)
    (hg : ∀ i ∈ s, ‖a i - b i‖ ≤ eg i)
    (hh : ∀ i ∈ s, ‖A i - B i‖ ≤ eh i) :
    ‖((∑ i ∈ s, c i • A i) + ∑ i ∈ s, ∑ j ∈ s.erase i, d i j • (a j).smulRight (a i)) -
      ((∑ i ∈ s, c i • B i) + ∑ i ∈ s, ∑ j ∈ s.erase i, d i j • (b j).smulRight (b i))‖ ≤
      (∑ i ∈ s, (∑ j ∈ s.erase i, |d i j| * (M j + Mt j)) * eg i) +
      ∑ i ∈ s, |c i| * eh i := by
  have hsingle : ‖(∑ i ∈ s, c i • A i) - ∑ i ∈ s, c i • B i‖ ≤
      ∑ i ∈ s, |c i| * eh i := by
    rw [← Finset.sum_sub_distrib (fun i => c i • A i) (fun i => c i • B i)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [← smul_sub (c i) (A i) (B i)]
    refine (ContinuousLinearMap.opNorm_smul_le (c i) (A i - B i)).trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hh i hi) (abs_nonneg _)
  have hpair (i j : ι) (hi : i ∈ s) (hj : j ∈ s) :
      ‖(a j).smulRight (a i) - (b j).smulRight (b i)‖ ≤
        eg j * M i + Mt j * eg i := by
    refine (norm_smulRight_sub_le (a j) (b j) (a i) (b i)).trans ?_
    apply add_le_add
    · exact mul_le_mul (hg j hj) (ha i hi) (norm_nonneg _) ((norm_nonneg _).trans (hg j hj))
    · exact mul_le_mul (hb j hj) (hg i hi) (norm_nonneg _) ((norm_nonneg _).trans (hb j hj))
  have hpairs :
      ‖(∑ i ∈ s, ∑ j ∈ s.erase i, d i j • (a j).smulRight (a i)) -
        ∑ i ∈ s, ∑ j ∈ s.erase i, d i j • (b j).smulRight (b i)‖ ≤
      ∑ i ∈ s, ∑ j ∈ s.erase i, |d i j| * (eg j * M i + Mt j * eg i) := by
    rw [← Finset.sum_sub_distrib
      (fun i => ∑ j ∈ s.erase i, d i j • (a j).smulRight (a i))
      (fun i => ∑ j ∈ s.erase i, d i j • (b j).smulRight (b i))]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [← Finset.sum_sub_distrib
      (fun j => d i j • (a j).smulRight (a i))
      (fun j => d i j • (b j).smulRight (b i))]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [← smul_sub (d i j) ((a j).smulRight (a i)) ((b j).smulRight (b i))]
    refine (ContinuousLinearMap.opNorm_smul_le (d i j)
      ((a j).smulRight (a i) - (b j).smulRight (b i))).trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hpair i j hi (Finset.mem_of_mem_erase hj)) (abs_nonneg _)
  rw [add_sub_add_comm
    (∑ i ∈ s, c i • A i)
    (∑ i ∈ s, ∑ j ∈ s.erase i, d i j • (a j).smulRight (a i))
    (∑ i ∈ s, c i • B i)
    (∑ i ∈ s, ∑ j ∈ s.erase i, d i j • (b j).smulRight (b i))]
  refine (norm_add_le
    ((∑ i ∈ s, c i • A i) - (∑ i ∈ s, c i • B i))
    ((∑ i ∈ s, ∑ j ∈ s.erase i, d i j • (a j).smulRight (a i)) -
      (∑ i ∈ s, ∑ j ∈ s.erase i, d i j • (b j).smulRight (b i)))).trans
      ((add_le_add hsingle hpairs).trans_eq ?_)
  rw [pair_error_reindex s d eg M Mt hd, add_comm]

/-- Product Hessian error with exact factor values. The estimate holds in any
real normed space and on any finite set of factors, including the empty set. -/
theorem hessian_finset_prod_error (s : Finset ι) (f g : ι → E → ℝ) (x : E)
    (eg eh M Mt : ι → ℝ)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x)
    (hg : ∀ i ∈ s, ContDiffAt ℝ 2 (g i) x)
    (he : ∀ i ∈ s, g i x = f i x)
    (hM : ∀ i ∈ s, ‖fderiv ℝ (f i) x‖ ≤ M i)
    (hMt : ∀ i ∈ s, ‖fderiv ℝ (g i) x‖ ≤ Mt i)
    (hgrad : ∀ i ∈ s, ‖fderiv ℝ (f i) x - fderiv ℝ (g i) x‖ ≤ eg i)
    (hhess : ∀ i ∈ s,
      ‖fderiv ℝ (fderiv ℝ (f i)) x - fderiv ℝ (fderiv ℝ (g i)) x‖ ≤ eh i) :
    ‖fderiv ℝ (fderiv ℝ (fun y => ∏ i ∈ s, f i y)) x -
      fderiv ℝ (fderiv ℝ (fun y => ∏ i ∈ s, g i y)) x‖ ≤
      (∑ i ∈ s,
        (∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, |f k x|) * (M j + Mt j)) * eg i) +
      ∑ i ∈ s, |∏ j ∈ s.erase i, f j x| * eh i := by
  have hc : ∀ i, (∏ j ∈ s.erase i, g j x) = ∏ j ∈ s.erase i, f j x := by
    intro i
    exact Finset.prod_congr rfl fun j hj => he j (Finset.mem_of_mem_erase hj)
  have hd : ∀ i j, (∏ k ∈ (s.erase i).erase j, g k x) =
      ∏ k ∈ (s.erase i).erase j, f k x := by
    intro i j
    exact Finset.prod_congr rfl fun k hk =>
      he k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk))
  rw [hessian_finset_prod_expanded s f x hf, hessian_finset_prod_expanded s g x hg]
  simp_rw [hc, hd]
  have h := hessian_expression_error s
    (fun i => ∏ j ∈ s.erase i, f j x)
    (fun i j => ∏ k ∈ (s.erase i).erase j, f k x)
    (fun i => fderiv ℝ (f i) x) (fun i => fderiv ℝ (g i) x)
    (fun i => fderiv ℝ (fderiv ℝ (f i)) x) (fun i => fderiv ℝ (fderiv ℝ (g i)) x)
    eg eh M Mt (fun i j => by rw [Finset.erase_right_comm]) hM hMt hgrad hhess
  simpa only [Finset.abs_prod] using h

end SurrogateOps.S09Derivative

namespace SurrogateOps.S09Accuracy

/-- Compare two accuracy orders uniformly on a positive bounded radius interval. -/
theorem radius_power_le {Δ Δbar N NF : ℝ}
    (hΔ : 0 < Δ) (hbar : Δ ≤ Δbar) (hN : NF ≤ N) :
    Δ ^ N ≤ Δbar ^ (N - NF) * Δ ^ NF := by
  calc
    Δ ^ N = Δ ^ (N - NF) * Δ ^ NF := by
      rw [← Real.rpow_add hΔ]
      congr 1
      ring
    _ ≤ Δbar ^ (N - NF) * Δ ^ NF :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hΔ.le hbar (sub_nonneg.mpr hN))
        (Real.rpow_nonneg hΔ.le _)

/-- Scale each term to the least order before summing the error constants. -/
theorem scaled_sum {ι : Type*} [Fintype ι]
    (C κ N : ι → ℝ) (Δ Δbar NF : ℝ)
    (hC : ∀ i, 0 ≤ C i) (hκ : ∀ i, 0 ≤ κ i)
    (hN : ∀ i, NF ≤ N i) (hΔ : 0 < Δ) (hbar : Δ ≤ Δbar) :
    (∑ i, C i * (κ i * Δ ^ N i)) ≤
      (∑ i, C i * κ i * Δbar ^ (N i - NF)) * Δ ^ NF := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  calc
    C i * (κ i * Δ ^ N i) = (C i * κ i) * Δ ^ N i := by ring
    _ ≤ (C i * κ i) * (Δbar ^ (N i - NF) * Δ ^ NF) :=
      mul_le_mul_of_nonneg_left (radius_power_le hΔ hbar (hN i))
        (mul_nonneg (hC i) (hκ i))
    _ = (C i * κ i * Δbar ^ (N i - NF)) * Δ ^ NF := by ring

/-- Complete the exact accuracy predicate after the finite-product Hessian
estimate is available. All positivity requirements follow from the original
accuracy and gradient-bound hypotheses. -/
theorem finish_product_accuracy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (f : Fin n → E → ℝ) (fm : Fin n → ℝ → E → ℝ) (x0 : E)
    (Δbar NF K : ℝ) (Ng Nh κg κh Mg Mgt : Fin n → ℝ)
    (hΔbar : 0 < Δbar)
    (hg : ∀ i, GradAccAt (f i) (fm i) x0 Δbar (Ng i) (κg i))
    (hh : ∀ i, HessAccAt (f i) (fm i) x0 Δbar (Nh i) (κh i))
    (hMg : ∀ i, ∀ x ∈ Metric.closedBall x0 Δbar, ‖fderiv ℝ (f i) x‖ ≤ Mg i)
    (hMgt : ∀ i, ∀ Δ ∈ Set.Ioc 0 Δbar, ‖fderiv ℝ (fm i Δ) x0‖ ≤ Mgt i)
    (hNF : IsLeast (Set.range Ng ∪ Set.range Nh) NF)
    (hK : K =
      ∑ i : Fin n,
        (∑ j ∈ Finset.univ.erase i,
          (∏ k ∈ (Finset.univ.erase i).erase j, |f k x0|) * (Mg j + Mgt j))
          * κg i * Δbar ^ (Ng i - NF)
      + ∑ i : Fin n,
        |∏ j ∈ Finset.univ.erase i, f j x0| * κh i * Δbar ^ (Nh i - NF))
    (herror : ∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fderiv ℝ (fun x => ∏ i, f i x)) x0
          - fderiv ℝ (fderiv ℝ (fun x => ∏ i, fm i Δ x)) x0‖ ≤
        (∑ i : Fin n,
          (∑ j ∈ Finset.univ.erase i,
            (∏ k ∈ (Finset.univ.erase i).erase j, |f k x0|) * (Mg j + Mgt j))
            * (κg i * Δ ^ Ng i))
        + ∑ i : Fin n,
          |∏ j ∈ Finset.univ.erase i, f j x0| * (κh i * Δ ^ Nh i)) :
    (∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fderiv ℝ (fun x => ∏ i, f i x)) x0
          - fderiv ℝ (fderiv ℝ (fun x => ∏ i, fm i Δ x)) x0‖
        ≤ K * Δ ^ NF) ∧
    ∃ κ, HessAccAt (fun x => ∏ i, f i x) (fun Δ x => ∏ i, fm i Δ x) x0 Δbar NF κ := by
  classical
  let Cg : Fin n → ℝ := fun i =>
    ∑ j ∈ Finset.univ.erase i,
      (∏ k ∈ (Finset.univ.erase i).erase j, |f k x0|) * (Mg j + Mgt j)
  let Ch : Fin n → ℝ := fun i => |∏ j ∈ Finset.univ.erase i, f j x0|
  have hMg0 (i : Fin n) : 0 ≤ Mg i :=
    (norm_nonneg _).trans (hMg i x0 (Metric.mem_closedBall_self hΔbar.le))
  have hMgt0 (i : Fin n) : 0 ≤ Mgt i :=
    (norm_nonneg _).trans (hMgt i Δbar ⟨hΔbar, le_rfl⟩)
  have hCg (i : Fin n) : 0 ≤ Cg i := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
      (add_nonneg (hMg0 j) (hMgt0 j))
  have hCh (i : Fin n) : 0 ≤ Ch i := abs_nonneg _
  have hNg (i : Fin n) : NF ≤ Ng i := hNF.2 (Or.inl (Set.mem_range_self i))
  have hNh (i : Fin n) : NF ≤ Nh i := hNF.2 (Or.inr (Set.mem_range_self i))
  have hNF0 : 0 ≤ NF := by
    rcases hNF.1 with (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact (hg i).1
    · exact (hh i).1
  have hKeq : K =
      (∑ i, Cg i * κg i * Δbar ^ (Ng i - NF)) +
      ∑ i, Ch i * κh i * Δbar ^ (Nh i - NF) := hK
  have hK0 : 0 ≤ K := by
    rw [hKeq]
    apply add_nonneg
    · exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (hCg i) (hg i).2.1) (Real.rpow_nonneg hΔbar.le _)
    · exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (hCh i) (hh i).2.1) (Real.rpow_nonneg hΔbar.le _)
  have hbound : ∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fderiv ℝ (fun x => ∏ i, f i x)) x0
          - fderiv ℝ (fderiv ℝ (fun x => ∏ i, fm i Δ x)) x0‖ ≤ K * Δ ^ NF := by
    intro Δ hΔ
    refine (herror Δ hΔ).trans ?_
    change (∑ i, Cg i * (κg i * Δ ^ Ng i)) +
      (∑ i, Ch i * (κh i * Δ ^ Nh i)) ≤ K * Δ ^ NF
    rw [hKeq, add_mul]
    exact add_le_add
      (scaled_sum Cg κg Ng Δ Δbar NF hCg (fun i => (hg i).2.1) hNg hΔ.1 hΔ.2)
      (scaled_sum Ch κh Nh Δ Δbar NF hCh (fun i => (hh i).2.1) hNh hΔ.1 hΔ.2)
  exact ⟨hbound, K, hNF0, hK0, hbound⟩

end SurrogateOps.S09Accuracy

open SurrogateOps

theorem solution {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (fm : Fin n → ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar NF K : ℝ) (Ng Nh κg κh Mg Mgt : Fin n → ℝ)
    (hΔbar : 0 < Δbar) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hm : ∀ i, ∀ Δ ∈ Set.Ioc 0 Δbar, ContDiffAt ℝ 2 (fm i Δ) x0)
    (he : ∀ i, ∀ Δ ∈ Set.Ioc 0 Δbar, fm i Δ x0 = f i x0)
    (hg : ∀ i, GradAccAt (f i) (fm i) x0 Δbar (Ng i) (κg i))
    (hh : ∀ i, HessAccAt (f i) (fm i) x0 Δbar (Nh i) (κh i))
    (hMg : ∀ i, ∀ x ∈ Metric.closedBall x0 Δbar, ‖fderiv ℝ (f i) x‖ ≤ Mg i)
    (hMgt : ∀ i, ∀ Δ ∈ Set.Ioc 0 Δbar, ‖fderiv ℝ (fm i Δ) x0‖ ≤ Mgt i)
    (hNF : IsLeast (Set.range Ng ∪ Set.range Nh) NF)
    (hK : K =
      ∑ i : Fin n,
        (∑ j ∈ Finset.univ.erase i,
          (∏ k ∈ (Finset.univ.erase i).erase j, |f k x0|) * (Mg j + Mgt j))
          * κg i * Δbar ^ (Ng i - NF)
      + ∑ i : Fin n,
        |∏ j ∈ Finset.univ.erase i, f j x0| * κh i * Δbar ^ (Nh i - NF)) :
    (∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fderiv ℝ (fun x => ∏ i, f i x)) x0
          - fderiv ℝ (fderiv ℝ (fun x => ∏ i, fm i Δ x)) x0‖
        ≤ K * Δ ^ NF) ∧
    ∃ κ, HessAccAt (fun x => ∏ i, f i x) (fun Δ x => ∏ i, fm i Δ x) x0 Δbar NF κ := by
  apply SurrogateOps.S09Accuracy.finish_product_accuracy
    f fm x0 Δbar NF K Ng Nh κg κh Mg Mgt hΔbar hg hh hMg hMgt hNF hK
  intro Δ hΔ
  simpa only using SurrogateOps.S09Derivative.hessian_finset_prod_error
    (Finset.univ : Finset (Fin n)) f (fun i => fm i Δ) x0
    (fun i => κg i * Δ ^ Ng i) (fun i => κh i * Δ ^ Nh i) Mg Mgt
    (fun i _ => (hf i).contDiffAt)
    (fun i _ => hm i Δ hΔ)
    (fun i _ => he i Δ hΔ)
    (fun i _ => hMg i x0 (Metric.mem_closedBall_self hΔbar.le))
    (fun i _ => hMgt i Δ hΔ)
    (fun i _ => (hg i).2.2 Δ hΔ)
    (fun i _ => (hh i).2.2 Δ hΔ)

#print axioms solution
