-- Prove2me | solution 1 for OAI.Yau.Geometry.constructed_coordinate_wave_estimates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:25:03.253074+00:00
-- url     : https://prove2.me/submissions/faf3aa1a-40f6-444a-9614-4b90eff6ac83

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_OAIQ237Ny002
import Theorems.Thm_OAI_Yau_Geometry_compact_actual_metric_wave_jets

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PolynomialEvaluation
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma reval_contDiff (p : CPoly) : ContDiff ℝ ∞ (reval p) := by
  change ContDiff ℝ ∞ (fun x ↦ reval p x)
  induction p using MvPolynomial.induction_on with
  | C a => simpa [reval] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Coord ↦ a))
  | add p q hp hq => simpa [reval] using hp.add hq
  | mul_X p i hp =>
    simpa [reval, coordCLM] using hp.mul (coordCLM i).contDiff

theorem fderiv_reval (p : CPoly) (x v : Coord) :
    fderiv ℝ (reval p) x v = ∑ i, reval (pderiv i p) x * (v i : ℂ) := by
  have hd (p : CPoly) : DifferentiableAt ℝ (reval p) x :=
    (reval_contDiff p).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  induction p using MvPolynomial.induction_on with
  | C a =>
    have he : reval (C a) = fun _ ↦ a := by ext; simp [reval]
    rw [he]
    simp [reval]
  | add p q hp hq =>
    have he : reval (p + q) = fun x ↦ reval p x + reval q x := by ext; simp [reval]
    rw [he]
    change (fderiv ℝ (reval p + reval q) x) v = _
    rw [fderiv_add (hd p) (hd q)]
    simp only [add_apply, hp, hq, map_add, reval, add_mul,
      Finset.sum_add_distrib]
  | mul_X p j hp =>
    have he : reval (p * X j) = fun x ↦ reval p x * coordCLM j x := by
      ext; simp [reval, coordCLM]
    rw [he]
    change (fderiv ℝ (reval p * ⇑(coordCLM j)) x) v = _
    rw [fderiv_mul (hd p) (coordCLM j).differentiableAt]
    simp [hp, reval, coordCLM, pderiv_X, Finset.sum_add_distrib,
      Finset.mul_sum, mul_add, mul_comm, mul_left_comm, Pi.single_apply, apply_ite]

lemma coordPartial_reval (i : Fin 4) (p : CPoly) : coordPartial i (reval p) = reval (pderiv i p) := by
  funext x
  simp [coordPartial, fderiv_reval, Pi.single_apply, apply_ite]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma coordPartial_contDiff {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    ContDiff ℝ ∞ (coordPartial i f) :=
  (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformPolynomial
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section
variable {T ι : Type*} [TopologicalSpace T] [Fintype ι]

omit [TopologicalSpace T] in
lemma polynomialFamily_contDiff (p : ι → CPoly) (c : T → ι → ℂ) (t : T) :
    ContDiff ℝ ∞ (polynomialFamily p c t) := by
  exact ContDiff.sum (fun i _ ↦ (reval_contDiff (p i)).const_smul (c t i))

omit [TopologicalSpace T] in
lemma polynomialFamily_iteratedFDeriv (p : ι → CPoly) (c : T → ι → ℂ) (t : T)
    (k : ℕ) (x : Coord) :
    iteratedFDeriv ℝ k (polynomialFamily p c t) x =
      ∑ i, c t i • iteratedFDeriv ℝ k (reval (p i)) x := by
  unfold polynomialFamily
  rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
    (((reval_contDiff (p i)).const_smul (c t i)).of_le
      (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
  apply Finset.sum_congr rfl
  intro i _
  exact iteratedFDeriv_const_smul_apply'
    ((reval_contDiff (p i)).of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt

theorem polynomialFamily_derivative_continuous (p : ι → CPoly) (c : T → ι → ℂ)
    (hc : ∀ i, Continuous (fun t ↦ c t i)) (k : ℕ) :
    Continuous (fun tx : T × Coord ↦ iteratedFDeriv ℝ k (polynomialFamily p c tx.1) tx.2) := by
  simp_rw [polynomialFamily_iteratedFDeriv]
  apply continuous_finsetSum
  intro i _
  exact ((hc i).comp continuous_fst).smul
    (((reval_contDiff (p i)).continuous_iteratedFDeriv (by
      exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).comp continuous_snd)

theorem polynomialFamily_uniform_derivative_bound (p : ι → CPoly) (c : T → ι → ℂ)
    (hc : ∀ i, Continuous (fun t ↦ c t i)) (s : Set T) (hs : IsCompact s)
    (R : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k (polynomialFamily p c t) x‖ ≤ C := by
  have hcompact := hs.prod (isCompact_closedBall (0 : Coord) R)
  have hbounded := (hcompact.image (polynomialFamily_derivative_continuous p c hc k)).isBounded
  obtain ⟨C, hC, hbound⟩ := hbounded.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro t ht x hx
  apply hbound
  exact ⟨(t, x), ⟨ht, by simpa using hx⟩, rfl⟩

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_ContinuousPolynomialFamily
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma polynomial_sum_of_support_subset (p : CPoly) (s : Finset (Fin 4 →₀ ℕ))
    (hs : p.support ⊆ s) : p = ∑ d ∈ s, p.coeff d • monomial d (1 : ℂ) := by
  simp only [smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [p.as_sum]
  exact Finset.sum_subset hs (fun d _ hd ↦ by simp [notMem_support_iff.mp hd])

lemma ContinuousPolyFamily.const (p : CPoly) : ContinuousPolyFamily (fun _ : T ↦ p) :=
  ⟨fun _ ↦ continuous_const, ⟨p.support, fun _ ↦ Finset.Subset.refl _⟩⟩

lemma ContinuousPolyFamily.add {P Q : T → CPoly}
    (hp : ContinuousPolyFamily P) (hq : ContinuousPolyFamily Q) :
    ContinuousPolyFamily (fun t ↦ P t + Q t) := by
  obtain ⟨s, hs⟩ := hp.2
  obtain ⟨r, hr⟩ := hq.2
  refine ⟨fun d ↦ by
    convert (hp.1 d).add (hq.1 d) using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    simp, s ∪ r, ?_⟩
  intro t d hd
  have h := support_add hd
  rcases Finset.mem_union.mp h with h | h
  · exact Finset.mem_union_left _ (hs t h)
  · exact Finset.mem_union_right _ (hr t h)

lemma ContinuousPolyFamily.smul {P : T → CPoly} (hp : ContinuousPolyFamily P)
    {c : T → ℂ} (hc : Continuous c) : ContinuousPolyFamily (fun t ↦ c t • P t) := by
  obtain ⟨s, hs⟩ := hp.2
  refine ⟨fun d ↦ by
    convert hc.mul (hp.1 d) using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    rw [coeff_smul]
    rfl, s, ?_⟩
  intro t d hd
  apply hs t
  rw [mem_support_iff] at hd ⊢
  simp only [coeff_smul, smul_eq_mul] at hd
  exact right_ne_zero_of_mul hd

lemma ContinuousPolyFamily.sum {ι : Type*} (s : Finset ι) {P : ι → T → CPoly}
    (hp : ∀ i ∈ s, ContinuousPolyFamily (P i)) :
    ContinuousPolyFamily (fun t ↦ ∑ i ∈ s, P i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (ContinuousPolyFamily.const (T := T) 0)
  | @insert i s hi ih =>
    simpa [Finset.sum_insert, hi] using (hp i (by simp)).add
      (ih (fun j hj ↦ hp j (by simp [hj])))

theorem ContinuousPolyFamily.uniform_derivative_bound {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (s : Set T) (hs : IsCompact s) (R : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k (reval (P t)) x‖ ≤ C := by
  obtain ⟨r, hr⟩ := hp.2
  have he (t : T) : reval (P t) = polynomialFamily
      (fun d : r ↦ monomial d.val (1 : ℂ)) (fun t d ↦ (P t).coeff d.val) t := by
    funext x
    rw [polynomial_sum_of_support_subset (P t) r (hr t)]
    simp [polynomialFamily, reval, Algebra.smul_def]
    exact (Finset.sum_attach r (fun d ↦ (P t).coeff d *
      eval (fun i ↦ (x i : ℂ)) (monomial d (1 : ℂ)))).symm
  obtain ⟨C, hC, hb⟩ := polynomialFamily_uniform_derivative_bound
    (fun d : r ↦ monomial d.val (1 : ℂ)) (fun t d ↦ (P t).coeff d.val)
    (fun d ↦ hp.1 d.val) s hs R k
  refine ⟨C, hC, ?_⟩
  intro t ht x hx
  rw [he t]
  exact hb t ht x hx

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_WaveEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Waves
open Set Filter
open scoped Topology ContDiff
noncomputable section
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma iteratedDeriv_line {f : E → F} {n k : ℕ} (hf : ContDiff ℝ n f)
    (hk : k ≤ n) (y z : E) (t : ℝ) :
    iteratedDeriv k (fun s : ℝ ↦ f (y + s • z)) t =
      iteratedFDeriv ℝ k f (y + t • z) (fun _ ↦ z) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight z
  have hshift : ContDiff ℝ n (fun x ↦ f (y + x)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ k ((fun x ↦ f (y + x)) ∘ L) t (fun _ ↦ 1) = _
  rw [L.iteratedFDeriv_comp_right hshift t (by exact_mod_cast hk)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_left]
  simp [L]

theorem vanishing_jet_taylor_bound {f : E → F} {n : ℕ} (hf : ContDiff ℝ (n + 1) f)
    (y z : E) (C : ℝ)
    (hzero : ∀ k, k ≤ n → iteratedFDeriv ℝ k f y = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (y + t • z)‖ ≤ C) :
    ‖f (y + z)‖ ≤ C * ‖z‖ ^ (n + 1) / (n.factorial : ℝ) := by
  let g : ℝ → F := fun t ↦ f (y + t • z)
  have hg : ContDiff ℝ (n + 1) g :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hi (k : ℕ) (hk : k ≤ n + 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin k g (Icc (0 : ℝ) 1) t =
        iteratedFDeriv ℝ k f (y + t • z) (fun _ ↦ z) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
      (hg.of_le (by exact_mod_cast hk)).contDiffAt ht]
    exact iteratedDeriv_line hf hk y z t
  have htaylor : taylorWithinEval g n (Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro k hk
    rw [hi k (by have := Finset.mem_range.mp hk; omega) 0 (by constructor <;> norm_num)]
    simp [hzero k (by have := Finset.mem_range.mp hk; omega)]
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (n + 1) g (Icc (0 : ℝ) 1) t‖ ≤ C * ‖z‖ ^ (n + 1) := by
    intro t ht
    rw [hi (n + 1) le_rfl t ht]
    calc
      _ ≤ ‖iteratedFDeriv ℝ (n + 1) f (y + t • z)‖ * ∏ _ : Fin (n + 1), ‖z‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ C * ‖z‖ ^ (n + 1) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_right (hbound t ht) (pow_nonneg (norm_nonneg _) _)
  have h := taylor_mean_remainder_bound (by norm_num : (0 : ℝ) ≤ 1)
    hg.contDiffOn (by constructor <;> norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) hderiv
  simpa [htaylor, g] using h

theorem vanishing_jet_derivative_bound {f : E → F} {m l : ℕ}
    (hf : ContDiff ℝ ∞ f) (hl : l ≤ m) (y z : E) (C : ℝ)
    (hzero : ∀ k, k ≤ m → iteratedFDeriv ℝ k f y = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (m + 1) f (y + t • z)‖ ≤ C) :
    ‖iteratedFDeriv ℝ l f (y + z)‖ ≤
      C * ‖z‖ ^ (m + 1 - l) / ((m - l).factorial : ℝ) := by
  induction l generalizing F m with
  | zero =>
    have hf0 : ContDiff ℝ (m + 1 : ℕ) f := hf.of_le (by
      exact_mod_cast (show (m + 1 : ℕ∞) ≤ ⊤ from le_top))
    simpa [norm_iteratedFDeriv_zero] using
      vanishing_jet_taylor_bound (n := m) hf0 y z C hzero hbound
  | succ l ih =>
    cases m with
    | zero => omega
    | succ m =>
      have hf' : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      have hz' : ∀ k, k ≤ m → iteratedFDeriv ℝ k (fderiv ℝ f) y = 0 := by
        intro k hk
        apply norm_eq_zero.mp
        rw [norm_iteratedFDeriv_fderiv, hzero (k + 1) (by omega), norm_zero]
      have hb' : ∀ t ∈ Icc (0 : ℝ) 1,
          ‖iteratedFDeriv ℝ (m + 1) (fderiv ℝ f) (y + t • z)‖ ≤ C := by
        intro t ht
        rw [norm_iteratedFDeriv_fderiv]
        exact hbound t ht
      have h := ih hf' (by omega : l ≤ m) hz' hb'
      simpa [norm_iteratedFDeriv_fderiv] using h

theorem gaussian_absorbs_power (c : ℝ) (hc : 0 < c) (p K : ℝ) :
    ∀ᶠ N : ℝ in atTop,
      N ^ p * Real.exp (-c * N ^ (1 / 3 : ℝ)) ≤ N ^ (-K) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (3 * (p + K)) c hc).comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3))
  have he : ∀ᶠ N : ℝ in atTop,
      (N ^ (1 / 3 : ℝ)) ^ (3 * (p + K)) * Real.exp (-c * N ^ (1 / 3 : ℝ)) ≤ 1 :=
    ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with N hN hpos
  have heq : (N ^ (1 / 3 : ℝ)) ^ (3 * (p + K)) = N ^ (p + K) := by
    rw [← Real.rpow_mul hpos.le]
    congr 1
    ring
  rw [heq] at hN
  rw [Real.rpow_neg hpos.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hpos K)]
  simpa [Real.rpow_add hpos, mul_assoc, mul_left_comm, mul_comm] using hN

theorem gaussian_cutoff_bound (c b : ℝ) (hc : 0 < c) (hb : 0 < b) (p K : ℝ) :
    ∀ᶠ N : ℝ in atTop, ∀ S r A : ℝ, 0 ≤ A →
      b * N ^ (1 / 3 : ℝ) ≤ N * r ^ 2 →
      A * N ^ p * Real.exp (N * S - c * N * r ^ 2) ≤
        A * N ^ (-K) * Real.exp (N * S) := by
  filter_upwards [gaussian_absorbs_power (c * b) (mul_pos hc hb) p K,
    eventually_gt_atTop (0 : ℝ)] with N hN hpos
  intro S r A hA hann
  have hexp : Real.exp (-c * N * r ^ 2) ≤ Real.exp (-(c * b) * N ^ (1 / 3 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hann hc.le
    nlinarith
  have hcost : N ^ p * Real.exp (-c * N * r ^ 2) ≤ N ^ (-K) :=
    (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hpos.le _)).trans hN
  have h := mul_le_mul_of_nonneg_left hcost hA
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (N * S)).le
  rw [show N * S - c * N * r ^ 2 = N * S + (-c * N * r ^ 2) by ring,
    Real.exp_add]
  nlinarith [h']

end
end Yau.Waves

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothOperatorJet
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma smoothSecondOrder_contDiff {g : Fin 4 → Fin 4 → Coord → ℂ}
    {b : Fin 4 → Coord → ℂ} {f : Coord → ℂ}
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (smoothSecondOrder g b f) := by
  apply ContDiff.add
  · apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact (hg i j).mul (coordPartial_contDiff (coordPartial_contDiff hf j) i)
  · apply ContDiff.sum
    intro i _
    exact (hb i).mul (coordPartial_contDiff hf i)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_FiniteAmplitude
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma finiteAmplitude_contDiff (A : ℕ → CPoly) (J : ℕ) (N : ℝ) :
    ContDiff ℝ ∞ (finiteAmplitude A J N) := polynomialFamily_contDiff _ _ _

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformTransportPolynomial
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma ContinuousPolyFamily.comp {S : Type*} [TopologicalSpace S]
    {P : T → CPoly} (hp : ContinuousPolyFamily P) {f : S → T} (hf : Continuous f) :
    ContinuousPolyFamily (fun s ↦ P (f s)) := by
  obtain ⟨r, hr⟩ := hp.2
  exact ⟨fun d ↦ (hp.1 d).comp hf, r, fun s ↦ hr (f s)⟩

lemma finiteAmplitude_reval (A : ℕ → CPoly) (J : ℕ) (N : ℝ) :
    finiteAmplitude A J N = reval (∑ j : Fin (J + 1), ((N⁻¹ : ℝ) : ℂ)^j.val • A j.val) := by
  funext x
  simp [finiteAmplitude, polynomialFamily, reval, Algebra.smul_def]

theorem finiteAmplitude_parameter_uniform_derivative_bound
    (A : ℕ → T → CPoly) (hA : ∀ j, ContinuousPolyFamily (A j))
    (J k : ℕ) (s : Set T) (hs : IsCompact s) (R : ℝ) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k (finiteAmplitude (fun j ↦ A j t) J N) x‖ ≤ C := by
  let P : T × ℝ → CPoly := fun z ↦
    ∑ j : Fin (J + 1), (z.2 : ℂ)^j.val • A j.val z.1
  have hP : ContinuousPolyFamily P := by
    apply ContinuousPolyFamily.sum
    intro j _
    exact ((hA j.val).comp continuous_fst).smul
      ((Complex.continuous_ofReal.comp continuous_snd).pow j.val)
  obtain ⟨C, hC, hb⟩ := hP.uniform_derivative_bound
    (s ×ˢ Set.Icc (0 : ℝ) 1) (hs.prod isCompact_Icc) R k
  refine ⟨C, hC, ?_⟩
  intro t ht N hN x hx
  rw [finiteAmplitude_reval]
  exact hb (t, N⁻¹) ⟨ht, inv_nonneg.mpr (le_trans zero_le_one hN), inv_le_one_of_one_le₀ hN⟩ x hx

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Waves
open scoped ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_dilate_translate {beta : E → F} (hb : ContDiff ℝ ∞ beta)
    (s : ℝ) (y x : E) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z ↦ beta (s • (z - y))) x =
      s ^ k • iteratedFDeriv ℝ k beta (s • (x - y)) := by
  rw [iteratedFDeriv_comp_sub (f := fun z ↦ beta (s • z))]
  exact congrFun (iteratedFDeriv_comp_const_smul s
    (hb.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)))) (x - y)

theorem compact_smooth_derivative_bound {beta : E → F} (hb : ContDiff ℝ ∞ beta)
    (hs : HasCompactSupport beta) (k : ℕ) :
    ∃ C > 0, ∀ x, ‖iteratedFDeriv ℝ k beta x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hs.iteratedFDeriv k).exists_bound_of_continuous
    (hb.continuous_iteratedFDeriv (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)))
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  exact (hC x).trans (le_max_left _ _)

theorem scaled_compact_derivative_bound {beta : E → F} (hb : ContDiff ℝ ∞ beta)
    (hs : HasCompactSupport beta) (k : ℕ) :
    ∃ C > 0, ∀ N : ℝ, 0 < N → ∀ y x : E,
      ‖iteratedFDeriv ℝ k (fun z ↦ beta (N ^ (1 / 3 : ℝ) • (z - y))) x‖ ≤
        C * N ^ ((k : ℝ) / 3) := by
  obtain ⟨C, hC, hbound⟩ := compact_smooth_derivative_bound hb hs k
  refine ⟨C, hC, ?_⟩
  intro N hN y x
  rw [iteratedFDeriv_dilate_translate hb, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.rpow_nonneg hN.le _) _)]
  have he : (N ^ (1 / 3 : ℝ)) ^ k = N ^ ((k : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    ring
  rw [he, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hbound _) (Real.rpow_nonneg hN.le _)

variable [FiniteDimensional ℝ E]

lemma scaledCutoff_contDiff (N : ℝ) (y : E) : ContDiff ℝ ∞ (scaledCutoff N y) :=
  (baseCutoff (E := E)).contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _)

lemma scaledCutoff_eq_one {N : ℝ} (hN : 0 < N) (y x : E)
    (hx : ‖x - y‖ ≤ N ^ (-1 / 3 : ℝ)) : scaledCutoff N y x = 1 := by
  apply (baseCutoff (E := E)).one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hN _)]
  change N ^ (1 / 3 : ℝ) * ‖x - y‖ ≤ 1
  calc
    _ ≤ N ^ (1 / 3 : ℝ) * N ^ (-1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hN.le _)
    _ = 1 := by rw [← Real.rpow_add hN]; norm_num

theorem scaledCutoff_support {N : ℝ} (hN : 0 < N) (y : E) :
    Function.support (scaledCutoff N y) = Metric.ball y (2 * N ^ (-1 / 3 : ℝ)) := by
  ext x
  change (baseCutoff (E := E)) (N ^ (1 / 3 : ℝ) • (x - y)) ≠ 0 ↔ _
  rw [← Function.mem_support, (baseCutoff (E := E)).support_eq]
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hN _)]
  change N ^ (1 / 3 : ℝ) * ‖x - y‖ < 2 ↔ ‖x - y‖ < 2 * N ^ (-1 / 3 : ℝ)
  rw [mul_comm, ← lt_div_iff₀ (Real.rpow_pos_of_pos hN _)]
  have he : N ^ (-1 / 3 : ℝ) = (N ^ (1 / 3 : ℝ))⁻¹ := by
    rw [show (-1 / 3 : ℝ) = -(1 / 3 : ℝ) by ring, Real.rpow_neg hN.le]
  rw [he, div_eq_mul_inv]

theorem scaledCutoff_derivative_bound (k : ℕ) :
    ∃ C > 0, ∀ N : ℝ, 0 < N → ∀ y x : E,
      ‖iteratedFDeriv ℝ k (scaledCutoff N y) x‖ ≤ C * N ^ ((k : ℝ) / 3) :=
  scaled_compact_derivative_bound (baseCutoff (E := E)).contDiff (baseCutoff (E := E)).hasCompactSupport k

end
end Yau.Waves

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CutoffProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Waves
open scoped ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smul_derivative_power_bound {beta : E → ℝ} {u : E → F}
    (hb : ContDiff ℝ ∞ beta) (hu : ContDiff ℝ ∞ u)
    (k : ℕ) (x : E) {B A N w : ℝ} (hB : 0 ≤ B) (_ : 0 ≤ A)
    (hN : 0 ≤ N) (_ : 0 ≤ w)
    (hbeta : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j beta x‖ ≤ B * N ^ j)
    (hwave : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j u x‖ ≤ A * N ^ j * w) :
    ‖iteratedFDeriv ℝ k (fun z ↦ beta z • u z) x‖ ≤
      (2 : ℝ) ^ k * B * A * N ^ k * w := by
  have hle := norm_iteratedFDeriv_smul_le hb hu x (n := k)
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  calc
    _ ≤ _ := hle
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (B * A * N ^ k * w) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
      have hm := mul_le_mul (hbeta j hjk) (hwave (k - j) (Nat.sub_le _ _))
        (norm_nonneg _) (mul_nonneg hB (pow_nonneg hN _))
      have he : (B * N ^ j) * (A * N ^ (k - j) * w) = B * A * N ^ k * w := by
        rw [show (B * N ^ j) * (A * N ^ (k - j) * w) =
          B * A * (N ^ j * N ^ (k - j)) * w by ring, ← pow_add, Nat.add_sub_of_le hjk]
      rw [he] at hm
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (k.choose j))
    _ = _ := by
      rw [← Finset.sum_mul]
      have he : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = (2 : ℝ) ^ k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [he]
      ring

variable [FiniteDimensional ℝ E]

theorem scaledCutoff_all_derivatives (k : ℕ) :
    ∃ B > 0, ∀ j, j ≤ k → ∀ N : ℝ, 1 ≤ N → ∀ y x : E,
      ‖iteratedFDeriv ℝ j (scaledCutoff N y) x‖ ≤ B * N ^ j := by
  choose C hC hbound using (fun j ↦ scaledCutoff_derivative_bound (E := E) j)
  let B := ∑ j ∈ Finset.range (k + 1), C j
  have hjB (j : ℕ) (hj : j ≤ k) : C j ≤ B :=
    Finset.single_le_sum (fun i _ ↦ (hC i).le) (Finset.mem_range.mpr (by omega))
  refine ⟨B, (hC 0).trans_le (hjB 0 (Nat.zero_le _)), ?_⟩
  intro j hj N hN y x
  have hpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    _ ≤ C j * N ^ ((j : ℝ) / 3) := hbound j N hpos y x
    _ ≤ B * N ^ ((j : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right (hjB j hj) (Real.rpow_nonneg hpos.le _)
    _ ≤ B * N ^ j := by
      rw [← Real.rpow_natCast]
      apply mul_le_mul_of_nonneg_left _ ((hC 0).trans_le (hjB 0 (Nat.zero_le _))).le
      exact Real.rpow_le_rpow_of_exponent_le hN (by have := Nat.cast_nonneg (α := ℝ) j; linarith)

theorem cutoff_preserves_derivative_exponent (k : ℕ) :
    ∃ B > 0, ∀ N : ℝ, 1 ≤ N → ∀ y x : E, ∀ u : E → F,
      ContDiff ℝ ∞ u → ∀ A w : ℝ, 0 ≤ A → 0 ≤ w →
      (∀ j, j ≤ k → ‖iteratedFDeriv ℝ j u x‖ ≤ A * N ^ j * w) →
      ‖iteratedFDeriv ℝ k (fun z ↦ scaledCutoff N y z • u z) x‖ ≤
        (2 : ℝ) ^ k * B * A * N ^ k * w := by
  obtain ⟨B, hB, hb⟩ := scaledCutoff_all_derivatives (E := E) k
  refine ⟨B, hB, ?_⟩
  intro N hN y x u hu A w hA hw hbound
  exact smul_derivative_power_bound (scaledCutoff_contDiff N y) hu k x hB.le hA
    (le_trans zero_le_one hN) hw (fun j hj ↦ hb j hj N hN y x) hbound

end
end Yau.Waves

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_SmoothWaveOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma coordPartial_add {f u : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (i : Fin 4) : coordPartial i (fun x ↦ f x + u x) =
      fun x ↦ coordPartial i f x + coordPartial i u x := by
  funext x
  unfold coordPartial
  rw [fderiv_fun_add (hf.differentiable (by simp) x) (hu.differentiable (by simp) x)]
  rfl

lemma coordPartial_mul {f u : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (i : Fin 4) : coordPartial i (fun x ↦ f x * u x) =
      fun x ↦ coordPartial i f x * u x + f x * coordPartial i u x := by
  funext x
  unfold coordPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hu.differentiable (by simp) x)]
  simp [smul_eq_mul]
  ring

lemma coordPartial_const_mul {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (a : ℂ) (i : Fin 4) :
    coordPartial i (fun x ↦ a * f x) = fun x ↦ a * coordPartial i f x := by
  rw [coordPartial_mul contDiff_const hf]
  ext x
  simp [coordPartial]

lemma coordPartial_exp {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    coordPartial i (fun x ↦ Complex.exp (f x)) =
      fun x ↦ coordPartial i f x * Complex.exp (f x) := by
  funext x
  unfold coordPartial
  rw [((hf.differentiable (by simp) x).hasFDerivAt.cexp).fderiv]
  simp [smul_eq_mul, mul_comm]

lemma coordPartial_twice_mul {f u : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (i j : Fin 4) : coordPartial i (coordPartial j (fun x ↦ f x * u x)) = fun x ↦
      coordPartial i (coordPartial j f) x * u x +
      coordPartial j f x * coordPartial i u x +
      coordPartial i f x * coordPartial j u x +
      f x * coordPartial i (coordPartial j u) x := by
  rw [coordPartial_mul hf hu j,
    coordPartial_add ((coordPartial_contDiff hf j).mul hu) (hf.mul (coordPartial_contDiff hu j)),
    coordPartial_mul (coordPartial_contDiff hf j) hu i,
    coordPartial_mul hf (coordPartial_contDiff hu j) i]
  ext x
  ring

theorem smoothSecondOrder_mul (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    {f u : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) (x : Coord) :
    smoothSecondOrder g b (fun z ↦ f z * u z) x =
      f x * smoothSecondOrder g b u x + u x * smoothSecondOrder g b f x +
      ∑ i, ∑ j, g i j x *
        (coordPartial i f x * coordPartial j u x + coordPartial j f x * coordPartial i u x) := by
  simp only [smoothSecondOrder]
  simp_rw [coordPartial_twice_mul hf hu]
  simp only [coordPartial_mul hf hu,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [mul_left_comm, mul_comm]
  ring

lemma waveExp_contDiff {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi) (N : ℝ) :
    ContDiff ℝ ∞ (waveExp phi N) := (contDiff_const.mul hp).cexp

lemma coordPartial_waveExp {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi) (N : ℝ) (i : Fin 4) :
    coordPartial i (waveExp phi N) =
      fun x ↦ (N : ℂ) * coordPartial i phi x * waveExp phi N x := by
  unfold waveExp
  rw [coordPartial_exp (contDiff_const.mul hp), coordPartial_const_mul hp]

lemma coordPartial_twice_waveExp {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi)
    (N : ℝ) (i j : Fin 4) : coordPartial i (coordPartial j (waveExp phi N)) =
      fun x ↦ ((N : ℂ) * coordPartial i (coordPartial j phi) x +
        (N : ℂ) ^ 2 * coordPartial i phi x * coordPartial j phi x) * waveExp phi N x := by
  rw [coordPartial_waveExp hp N j,
    coordPartial_mul (contDiff_const.mul (coordPartial_contDiff hp j)) (waveExp_contDiff hp N) i,
    coordPartial_const_mul (coordPartial_contDiff hp j), coordPartial_waveExp hp N i]
  ext x
  ring

theorem smoothSecondOrder_waveExp (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi)
    (N : ℝ) (x : Coord) :
    smoothSecondOrder g b (waveExp phi N) x =
      ((N : ℂ) * smoothSecondOrder g b phi x +
        (N : ℂ) ^ 2 * (smoothEikonal g phi x - 4)) * waveExp phi N x := by
  simp only [smoothSecondOrder]
  simp_rw [coordPartial_twice_waveExp hp N]
  simp only [coordPartial_waveExp hp N, smoothEikonal, add_sub_cancel_right,
    mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
  simp only [mul_assoc, mul_left_comm]
  ring

lemma symmetric_cross_sum (G : Fin 4 → Fin 4 → ℂ) (hG : ∀ i j, G i j = G j i)
    (a q : Fin 4 → ℂ) :
    (∑ i, ∑ j, G i j * (a i * q j + a j * q i)) =
      ∑ i, (2 * ∑ j, G i j * q j) * a i := by
  have hs : (∑ i, ∑ j, G i j * a j * q i) = ∑ i, ∑ j, G i j * a i * q j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hG j i]
  calc
    _ = (∑ i, ∑ j, G i j * a i * q j) + (∑ i, ∑ j, G i j * a j * q i) := by
      simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib]
    _ = 2 * (∑ i, ∑ j, G i j * a i * q j) := by rw [hs]; ring
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem smooth_wave_residual_identity (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (hg : ∀ i j x, g i j x = g j i x)
    {phi a : Coord → ℂ} (hp : ContDiff ℝ ∞ phi) (ha : ContDiff ℝ ∞ a)
    (N : ℝ) (x : Coord) :
    smoothSecondOrder g b (fun z ↦ a z * waveExp phi N z) x +
        ((4 : ℂ) * (N : ℂ) ^ 2 + 6 * (N : ℂ)) * (a x * waveExp phi N x) =
      waveExp phi N x *
        ((N : ℂ) ^ 2 * smoothEikonal g phi x * a x +
          (N : ℂ) * smoothTransport (smoothBeamVector g phi) (smoothBeamScalar g b phi)
            (fun _ ↦ 0) a x + smoothSecondOrder g b a x) := by
  rw [smoothSecondOrder_mul g b ha (waveExp_contDiff hp N), smoothSecondOrder_waveExp g b hp,
    symmetric_cross_sum (fun i j ↦ g i j x) (fun i j ↦ hg i j x)]
  simp only [coordPartial_waveExp hp N, smoothTransport, smoothBeamVector, smoothBeamScalar,
    sub_zero]
  have he : (∑ i, (2 * ∑ j, g i j x * ((N : ℂ) * coordPartial j phi x * waveExp phi N x)) *
      coordPartial i a x) =
      (N : ℂ) * waveExp phi N x *
        (∑ i, (2 * ∑ j, g i j x * coordPartial j phi x) * coordPartial i a x) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_ExponentialWaveBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma norm_iteratedFDeriv_complex_exp (k : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k Complex.exp z‖ = Real.exp z.re := by
  have he := (Complex.contDiff_exp (𝕜 := ℂ) (n := k)).contDiffAt.restrictScalars_iteratedFDeriv
    (𝕜 := ℝ) (x := z)
  rw [← he]
  simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hd : iteratedDeriv k Complex.exp z = Complex.exp z := by
    simpa using congrFun (iteratedDeriv_cexp_const_mul k 1) z
  rw [hd, Complex.norm_exp]

theorem waveExp_derivative_bound {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi)
    (k : ℕ) (x : Coord) {D N : ℝ} (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hphi : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i phi x‖ ≤ D) :
    ‖iteratedFDeriv ℝ k (waveExp phi N) x‖ ≤
      (k.factorial : ℝ) * D ^ k * N ^ k * Real.exp (N * (phi x).re) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hDN : 1 ≤ D * N := one_le_mul_of_one_le_of_one_le hD hN
  have hb : ∀ i, 1 ≤ i → i ≤ k →
      ‖iteratedFDeriv ℝ i (fun z ↦ (N : ℂ) * phi z) x‖ ≤ (D * N) ^ i := by
    intro i hi hik
    change ‖iteratedFDeriv ℝ i (fun z ↦ (N : ℂ) • phi z) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hp.of_le (by
      exact_mod_cast (show (i : ℕ∞) ≤ ⊤ from le_top))).contDiffAt, norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNp]
    calc
      _ ≤ N * D := mul_le_mul_of_nonneg_left (hphi i hi hik) hNp.le
      _ = (D * N) ^ 1 := by ring
      _ ≤ _ := pow_le_pow_right₀ hDN hi
  have he := norm_iteratedFDeriv_comp_le
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)) (contDiff_const.mul hp) (n := k)
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)) x
    (fun i _ ↦ le_of_eq (norm_iteratedFDeriv_complex_exp i ((N : ℂ) * phi x))) hb
  change ‖iteratedFDeriv ℝ k (fun z ↦ Complex.exp ((N : ℂ) * phi z)) x‖ ≤ _
  simpa [Function.comp_def, mul_pow, mul_assoc, mul_left_comm, mul_comm] using he

theorem waveExp_gaussian_derivative_bound {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi)
    (k : ℕ) (x : Coord) {D N S c r : ℝ} (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hphi : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i phi x‖ ≤ D)
    (hgap : (phi x).re - S ≤ -c * r ^ 2) :
    ‖iteratedFDeriv ℝ k (waveExp phi N) x‖ ≤
      (k.factorial : ℝ) * D ^ k * N ^ k * Real.exp (N * S - c * N * r ^ 2) := by
  apply (waveExp_derivative_bound hp k x hD hN hphi).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hgap (le_trans zero_le_one hN)
  nlinarith

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_WaveSize
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma mul_derivative_power_bound {f u : Coord → ℂ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) (k : ℕ) (x : Coord)
    {A B N w : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hfa : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j f x‖ ≤ A * N ^ j)
    (hub : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j u x‖ ≤ B * N ^ j * w) :
    ‖iteratedFDeriv ℝ k (fun z ↦ f z * u z) x‖ ≤ (2 : ℝ) ^ k * A * B * N ^ k * w := by
  have h := norm_iteratedFDeriv_mul_le hf hu x (n := k)
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  calc
    _ ≤ _ := h
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (A * B * N ^ k * w) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
      have hm := mul_le_mul (hfa j hjk) (hub (k - j) (Nat.sub_le _ _))
        (norm_nonneg _) (mul_nonneg hA (pow_nonneg hN _))
      have he : (A * N ^ j) * (B * N ^ (k - j) * w) = A * B * N ^ k * w := by
        rw [show (A * N ^ j) * (B * N ^ (k - j) * w) =
          A * B * (N ^ j * N ^ (k - j)) * w by ring, ← pow_add, Nat.add_sub_of_le hjk]
      rw [he] at hm
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (k.choose j))
    _ = _ := by
      rw [← Finset.sum_mul]
      have he : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = (2 : ℝ) ^ k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [he]
      ring

theorem cutoff_wave_size (k : ℕ) : ∃ B > 0, ∀ (phi a : Coord → ℂ),
    ContDiff ℝ ∞ phi → ContDiff ℝ ∞ a → ∀ (y x : Coord) (N A D S c : ℝ),
    1 ≤ N → 0 ≤ A → 1 ≤ D →
    (∀ j, j ≤ k → ‖iteratedFDeriv ℝ j a x‖ ≤ A) →
    (∀ j, 1 ≤ j → j ≤ k → ‖iteratedFDeriv ℝ j phi x‖ ≤ D) →
    (phi x).re - S ≤ -c * ‖x - y‖ ^ 2 →
    ‖iteratedFDeriv ℝ k (fun z ↦ Yau.Waves.scaledCutoff N y z •
      (a z * waveExp phi N z)) x‖ ≤
      B * A * (k.factorial : ℝ) * D ^ k * N ^ k *
        Real.exp (N * S - c * N * ‖x - y‖ ^ 2) := by
  obtain ⟨B, hB, hcut⟩ := Yau.Waves.cutoff_preserves_derivative_exponent (E := Coord) (F := ℂ) k
  refine ⟨(2 : ℝ) ^ k * B * (2 : ℝ) ^ k, by positivity, ?_⟩
  intro phi a hp ha y x N A D S c hN hA hD hamp hphase hgap
  let w := Real.exp (N * S - c * N * ‖x - y‖ ^ 2)
  let Q := (k.factorial : ℝ) * D ^ k
  have hQ : 0 ≤ Q := by dsimp [Q] <;> positivity
  have hw : 0 ≤ w := (Real.exp_pos _).le
  have he (j : ℕ) (hj : j ≤ k) : ‖iteratedFDeriv ℝ j (waveExp phi N) x‖ ≤ Q * N ^ j * w := by
    apply (waveExp_gaussian_derivative_bound hp j x hD hN
      (fun i hi hij ↦ hphase i hi (hij.trans hj)) hgap).trans
    have hfact : (j.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hj
    have hpow : D ^ j ≤ D ^ k := pow_le_pow_right₀ hD hj
    dsimp [Q, w]
    gcongr
  have hau (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (fun z ↦ a z * waveExp phi N z) x‖ ≤
        ((2 : ℝ) ^ k * A * Q) * N ^ j * w := by
    apply (mul_derivative_power_bound ha (waveExp_contDiff hp N) j x hA
      (le_trans zero_le_one hN) _ (fun i hi ↦ he i (hi.trans hj))).trans
    · have hp2 : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
      gcongr
    · intro i hi
      exact (hamp i (hi.trans hj)).trans (le_mul_of_one_le_right hA (one_le_pow₀ hN))
  have h := hcut N hN y x (fun z ↦ a z * waveExp phi N z) (ha.mul (waveExp_contDiff hp N))
    ((2 : ℝ) ^ k * A * Q) w (by positivity) hw hau
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [Q, w]
  ring

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformSmoothBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma DerivativeBound.mono {k l : ℕ} {f : Coord → ℂ} {x : Coord} {C : ℝ}
    (h : DerivativeBound k f x C) (hl : l ≤ k) : DerivativeBound l f x C :=
  fun j hj ↦ h j (hj.trans hl)

lemma DerivativeBound.add {k : ℕ} {f g : Coord → ℂ} {x : Coord} {A B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (ha : DerivativeBound k f x A) (hb : DerivativeBound k g x B) :
    DerivativeBound k (fun z ↦ f z + g z) x (A + B) := by
  intro j hj
  change ‖iteratedFDeriv ℝ j (f + g) x‖ ≤ A + B
  rw [iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    (hg.of_le (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (ha j hj) (hb j hj))

lemma DerivativeBound.mul {k : ℕ} {f g : Coord → ℂ} {x : Coord} {A B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : DerivativeBound k f x A) (hb : DerivativeBound k g x B) :
    DerivativeBound k (fun z ↦ f z * g z) x (2 ^ k * A * B) := by
  intro j hj
  have h := mul_derivative_power_bound hf hg j x hA (by norm_num : (0:ℝ) ≤ 1)
    (N := 1) (w := 1) (fun i hi ↦ by simpa using ha i (hi.trans hj))
    (fun i hi ↦ by simpa using hb i (hi.trans hj))
  simp only [one_pow, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hB)

lemma DerivativeBound.sum {ι : Type*} (s : Finset ι) {k : ℕ}
    {f : ι → Coord → ℂ} {x : Coord} {C : ι → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ s, DerivativeBound k (f i) x (C i)) :
    DerivativeBound k (fun z ↦ ∑ i ∈ s, f i z) x (∑ i ∈ s, C i) := by
  intro j hj
  rw [iteratedFDeriv_fun_sum_apply (fun i hi ↦ ((hf i hi).of_le
    (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi ↦ hb i hi j hj))

lemma coordPartial_derivative_norm_le (f : Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    (i : Fin 4) (k : ℕ) (x : Coord) :
    ‖iteratedFDeriv ℝ k (coordPartial i f) x‖ ≤ ‖iteratedFDeriv ℝ (k+1) f x‖ := by
  let L : (Coord →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (Pi.single i 1)
  have he : coordPartial i f = L ∘ fderiv ℝ f := rfl
  have hf' : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [he, L.iteratedFDeriv_comp_left hf'.contDiffAt
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖ := ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖ := by
      gcongr
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro v
      have h := v.le_opNorm (Pi.single i (1 : ℝ))
      have hn : ‖(Pi.single i (1 : ℝ) : Coord)‖ ≤ 1 := by
        apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
        intro j
        by_cases hij : j = i <;> simp [hij]
      exact h.trans (by simpa using mul_le_mul_of_nonneg_left hn (norm_nonneg v))
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

lemma DerivativeBound.coordPartial {k : ℕ} {f : Coord → ℂ} {x : Coord} {C : ℝ}
    (hf : ContDiff ℝ ∞ f) (h : DerivativeBound (k+1) f x C) (i : Fin 4) :
    DerivativeBound k (coordPartial i f) x C := by
  intro j hj
  exact (coordPartial_derivative_norm_le f hf i j x).trans (h (j+1) (by omega))

variable {T : Type*} [TopologicalSpace T]

theorem compact_smooth_derivative_bound (f : T → Coord → ℂ) (k : ℕ)
    (hc : ∀ j, j ≤ k → Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ j (f z.1) z.2))
    (s : Set T) (hs : IsCompact s) (R : ℝ) :
    ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R → DerivativeBound k (f t) x C := by
  have hb (j : Fin (k+1)) : ∃ C > 0, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ j.val (f t) x‖ ≤ C := by
    obtain ⟨C, hC, h⟩ := ((hs.prod (isCompact_closedBall (0 : Coord) R)).image
      (hc j.val (by omega))).isBounded.exists_pos_norm_le
    refine ⟨C, hC, fun t ht x hx ↦ h _ ?_⟩
    exact ⟨(t,x), ⟨ht, by simpa using hx⟩, rfl⟩
  choose C hC h using hb
  refine ⟨∑ j, C j, ?_, ?_⟩
  · exact (hC ⟨0, by omega⟩).trans_le (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))
  · intro t ht x hx j hj
    exact (h ⟨j, by omega⟩ t ht x hx).trans
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothDefectBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma uniformSmoothBounded_of_continuous_derivatives (s : Set T) (hs : IsCompact s)
    (R : ℝ) (f : T → Coord → ℂ) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hc : ∀ j, Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ j (f z.1) z.2)) :
    UniformSmoothBounded s R f :=
  ⟨hf, fun k ↦ compact_smooth_derivative_bound f k (fun j _ ↦ hc j) s hs R⟩

lemma ContinuousPolyFamily.derivative_continuous {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (k : ℕ) :
    Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k (reval (P z.1)) z.2) := by
  obtain ⟨r, hr⟩ := hp.2
  have he (t : T) : reval (P t) = polynomialFamily
      (fun d : r ↦ monomial d.val (1 : ℂ)) (fun t d ↦ (P t).coeff d.val) t := by
    funext x
    rw [polynomial_sum_of_support_subset (P t) r (hr t)]
    simp [polynomialFamily, reval, Algebra.smul_def]
    exact (Finset.sum_attach r (fun d ↦ (P t).coeff d *
      eval (fun i ↦ (x i : ℂ)) (monomial d (1 : ℂ)))).symm
  simp_rw [he]
  exact polynomialFamily_derivative_continuous
    (fun d : r ↦ monomial d.val (1 : ℂ)) (fun t d ↦ (P t).coeff d.val)
    (fun d ↦ hp.1 d.val) k

lemma ContinuousPolyFamily.uniformSmoothBounded {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (s : Set T) (hs : IsCompact s) (R : ℝ) :
    UniformSmoothBounded s R (fun t ↦ reval (P t)) := by
  apply uniformSmoothBounded_of_continuous_derivatives s hs R _ (fun t ↦ reval_contDiff _)
  exact hp.derivative_continuous

omit [TopologicalSpace T]

lemma UniformSmoothBounded.const (s : Set T) (R : ℝ) (c : ℂ) :
    UniformSmoothBounded s R (fun _ _ ↦ c) := by
  refine ⟨fun _ ↦ contDiff_const, fun k ↦ ⟨‖c‖ + 1, by positivity, ?_⟩⟩
  intro t ht x hx j hj
  cases j with
  | zero => simp [norm_iteratedFDeriv_zero]
  | succ j => simp [iteratedFDeriv_succ_const] <;> positivity

lemma UniformSmoothBounded.add {s : Set T} {R : ℝ} {f g : T → Coord → ℂ}
    (hf : UniformSmoothBounded s R f) (hg : UniformSmoothBounded s R g) :
    UniformSmoothBounded s R (fun t x ↦ f t x + g t x) := by
  refine ⟨fun t ↦ (hf.1 t).add (hg.1 t), ?_⟩
  intro k
  obtain ⟨A, hA, ha⟩ := hf.2 k
  obtain ⟨B, hB, hb⟩ := hg.2 k
  exact ⟨A+B, add_pos hA hB, fun t ht x hx ↦
    (ha t ht x hx).add (hf.1 t) (hg.1 t) (hb t ht x hx)⟩

lemma UniformSmoothBounded.mul {s : Set T} {R : ℝ} {f g : T → Coord → ℂ}
    (hf : UniformSmoothBounded s R f) (hg : UniformSmoothBounded s R g) :
    UniformSmoothBounded s R (fun t x ↦ f t x * g t x) := by
  refine ⟨fun t ↦ (hf.1 t).mul (hg.1 t), ?_⟩
  intro k
  obtain ⟨A, hA, ha⟩ := hf.2 k
  obtain ⟨B, hB, hb⟩ := hg.2 k
  exact ⟨2^k*A*B, by positivity, fun t ht x hx ↦
    (ha t ht x hx).mul (hf.1 t) (hg.1 t) hA.le hB.le (hb t ht x hx)⟩

lemma UniformSmoothBounded.sum {ι : Type*} (r : Finset ι) {s : Set T} {R : ℝ}
    {f : ι → T → Coord → ℂ} (hf : ∀ i ∈ r, UniformSmoothBounded s R (f i)) :
    UniformSmoothBounded s R (fun t x ↦ ∑ i ∈ r, f i t x) := by
  classical
  induction r using Finset.induction_on with
  | empty => simpa using UniformSmoothBounded.const s R 0
  | @insert i r hi ih =>
    simpa [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self i r)).add
      (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

lemma UniformSmoothBounded.coordPartial {s : Set T} {R : ℝ} {f : T → Coord → ℂ}
    (hf : UniformSmoothBounded s R f) (i : Fin 4) :
    UniformSmoothBounded s R (fun t ↦ coordPartial i (f t)) := by
  refine ⟨fun t ↦ coordPartial_contDiff (hf.1 t) i, ?_⟩
  intro k
  obtain ⟨C, hC, hc⟩ := hf.2 (k+1)
  exact ⟨C, hC, fun t ht x hx ↦ (hc t ht x hx).coordPartial (hf.1 t) i⟩

lemma uniformSmoothBounded_secondOrder {s : Set T} {R : ℝ}
    {g : T → Fin 4 → Fin 4 → Coord → ℂ} {b : T → Fin 4 → Coord → ℂ}
    {f : T → Coord → ℂ}
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hb : ∀ i, UniformSmoothBounded s R (fun t ↦ b t i))
    (hf : UniformSmoothBounded s R f) :
    UniformSmoothBounded s R (fun t ↦ smoothSecondOrder (g t) (b t) (f t)) := by
  exact (UniformSmoothBounded.sum Finset.univ (fun i _ ↦
    UniformSmoothBounded.sum Finset.univ (fun j _ ↦
      (hg i j).mul ((hf.coordPartial j).coordPartial i)))).add
    (UniformSmoothBounded.sum Finset.univ (fun i _ ↦ (hb i).mul (hf.coordPartial i)))

lemma uniformSmoothBounded_eikonal {s : Set T} {R : ℝ}
    {g : T → Fin 4 → Fin 4 → Coord → ℂ} {phi : T → Coord → ℂ}
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hp : UniformSmoothBounded s R phi) :
    UniformSmoothBounded s R (fun t ↦ smoothEikonal (g t) (phi t)) := by
  exact (UniformSmoothBounded.sum Finset.univ (fun i _ ↦
    UniformSmoothBounded.sum Finset.univ (fun j _ ↦
      ((hg i j).mul (hp.coordPartial i)).mul (hp.coordPartial j)))).add
    (UniformSmoothBounded.const s R 4)

lemma uniformSmoothBounded_beamVector {s : Set T} {R : ℝ}
    {g : T → Fin 4 → Fin 4 → Coord → ℂ} {phi : T → Coord → ℂ}
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hp : UniformSmoothBounded s R phi) (i : Fin 4) :
    UniformSmoothBounded s R (fun t ↦ smoothBeamVector (g t) (phi t) i) :=
  (UniformSmoothBounded.const s R 2).mul (UniformSmoothBounded.sum Finset.univ
    (fun j _ ↦ (hg i j).mul (hp.coordPartial j)))

lemma uniformSmoothBounded_beamScalar {s : Set T} {R : ℝ}
    {g : T → Fin 4 → Fin 4 → Coord → ℂ} {b : T → Fin 4 → Coord → ℂ}
    {phi : T → Coord → ℂ}
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hb : ∀ i, UniformSmoothBounded s R (fun t ↦ b t i))
    (hp : UniformSmoothBounded s R phi) :
    UniformSmoothBounded s R (fun t ↦ smoothBeamScalar (g t) (b t) (phi t)) :=
  (uniformSmoothBounded_secondOrder hg hb hp).add (UniformSmoothBounded.const s R 6)

lemma uniformSmoothBounded_transport_defect {s : Set T} {R : ℝ}
    {g : T → Fin 4 → Fin 4 → Coord → ℂ} {b : T → Fin 4 → Coord → ℂ}
    {phi a prev : T → Coord → ℂ}
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hb : ∀ i, UniformSmoothBounded s R (fun t ↦ b t i))
    (hp : UniformSmoothBounded s R phi) (ha : UniformSmoothBounded s R a)
    (hprev : UniformSmoothBounded s R prev) :
    UniformSmoothBounded s R (fun t x ↦
      smoothTransport (smoothBeamVector (g t) (phi t)) (smoothBeamScalar (g t) (b t) (phi t))
        (fun _ ↦ 0) (a t) x + smoothSecondOrder (g t) (b t) (prev t) x) := by
  have h := ((UniformSmoothBounded.sum Finset.univ (fun i _ ↦
    (uniformSmoothBounded_beamVector hg hp i).mul (ha.coordPartial i))).add
    ((uniformSmoothBounded_beamScalar hg hb hp).mul ha)).add
      (uniformSmoothBounded_secondOrder hg hb hprev)
  simpa [smoothTransport] using h

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_ResidualTaylor
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Yau.Waves

theorem scaled_taylor_lower_derivative_bound {f : Coord → ℂ} {m K l k k0 : ℕ}
    (hf : ContDiff ℝ ∞ f) (hm : 3 * K + 4 * k0 + 6 < m + 1) (hk : k ≤ k0) (hl : l ≤ k)
    (y z : Coord) {C R N : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hN : 1 ≤ N)
    (hzero : ∀ j, j ≤ m → iteratedFDeriv ℝ j f y = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (m + 1) f (y + t • z)‖ ≤ C)
    (hradius : ‖z‖ ≤ R * N ^ (-1 / 3 : ℝ)) :
    N ^ ((k : ℝ) + 2) * ‖iteratedFDeriv ℝ l f (y + z)‖ ≤
      C * R ^ (m + 1 - l) * N ^ (-(K : ℝ)) := by
  have hkm : l ≤ m := by omega
  have hpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let q : ℕ := m + 1 - l
  have ht := vanishing_jet_derivative_bound hf hkm y z C hzero hbound
  have hfact : (1 : ℝ) ≤ ((m - l).factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (m - l))
  have hsmall : ‖iteratedFDeriv ℝ l f (y + z)‖ ≤ C * (R * N ^ (-1 / 3 : ℝ)) ^ q := by
    calc
      _ ≤ C * ‖z‖ ^ q := ht.trans (div_le_self (mul_nonneg hC (pow_nonneg (norm_nonneg _) _)) hfact)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hradius q) hC
  have hp : (N ^ (-1 / 3 : ℝ)) ^ q = N ^ (-(q : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  have he : (k : ℝ) + 2 + (-(q : ℝ) / 3) ≤ -(K : ℝ) := by
    have hq : (q : ℝ) = (m : ℝ) + 1 - l := by
      dsimp [q]
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    rw [hq]
    have hm' : (3 : ℝ) * K + 4 * k0 + 6 < m + 1 := by exact_mod_cast hm
    have hk' : (k : ℝ) ≤ k0 := by exact_mod_cast hk
    have hl' : (l : ℝ) ≤ k := by exact_mod_cast hl
    linarith
  calc
    _ ≤ N ^ ((k : ℝ) + 2) * (C * (R * N ^ (-1 / 3 : ℝ)) ^ q) :=
      mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hpos.le _)
    _ = C * R ^ q * N ^ ((k : ℝ) + 2 + (-(q : ℝ) / 3)) := by
      rw [mul_pow, hp, Real.rpow_add hpos ((k : ℝ) + 2) (-(q : ℝ) / 3)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN he)
      (mul_nonneg hC (pow_nonneg hR _))

theorem uniform_flat_scaled_derivative_bound {T : Type*} [TopologicalSpace T]
    {s : Set T} {R : ℝ} {f : T → Coord → ℂ} (hf : UniformSmoothBounded s R f)
    {m K k0 : ℕ} (hm : 3*K + 4*k0 + 6 < m+1) (hR : 0 ≤ R)
    (hz : ∀ t ∈ s, FlatAt m (f t) 0) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord,
      ‖x‖ ≤ R * N ^ (-1/3 : ℝ) →
      ∀ l, l ≤ k0 → N ^ ((k0 : ℝ)+2) * ‖iteratedFDeriv ℝ l (f t) x‖ ≤
        C * N ^ (-(K : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := hf.2 (m+1)
  let C := 1 + ∑ l ∈ Finset.range (k0+1), B * R ^ (m+1-l)
  have hterm (l : ℕ) : 0 ≤ B * R ^ (m+1-l) := by positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t ht N hN x hx l hl
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : N ^ (-1/3 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
  have hxR : ‖x‖ ≤ R := hx.trans ((mul_le_mul_of_nonneg_left hpow hR).trans_eq (mul_one R))
  have hsegment : ∀ a ∈ Icc (0:ℝ) 1, ‖iteratedFDeriv ℝ (m+1) (f t) (0 + a • x)‖ ≤ B := by
    intro a ha
    apply hb t ht _ _ (m+1) le_rfl
    simp only [zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]
    exact (mul_le_mul_of_nonneg_right ha.2 (norm_nonneg x)).trans (by simpa using hxR)
  have h := scaled_taylor_lower_derivative_bound (hf.1 t) hm (le_refl k0) hl
    (0 : Coord) x hB.le hR hN (hz t ht) hsegment hx
  simp only [zero_add] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNp.le _)
  have htC := Finset.single_le_sum (fun i _ ↦ hterm i) (Finset.mem_range.mpr (by omega : l < k0+1))
  dsimp [C]
  linarith

theorem uniform_flat_derivative_decay {T : Type*} [TopologicalSpace T]
    {s : Set T} {R : ℝ} {f : T → Coord → ℂ} (hf : UniformSmoothBounded s R f)
    {m K k0 : ℕ} (hm : 3*K + 4*k0 + 6 < m+1) (hR : 0 ≤ R)
    (hz : ∀ t ∈ s, FlatAt m (f t) 0) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord,
      ‖x‖ ≤ R * N ^ (-1/3 : ℝ) →
      DerivativeBound k0 (f t) x (C * N ^ (-(K : ℝ) - k0 - 2)) := by
  obtain ⟨C, hC, hc⟩ := uniform_flat_scaled_derivative_bound hf hm hR hz
  refine ⟨C, hC, ?_⟩
  intro t ht N hN x hx l hl
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    _ ≤ (C * N ^ (-(K : ℝ))) / N ^ ((k0 : ℝ)+2) := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp _)).mpr
      simpa [mul_comm] using hc t ht N hN x hx l hl
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_sub hNp]
      congr 2
      ring

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_SmoothFiniteResidual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma revalLinear_apply (x : Coord) (p : CPoly) : revalLinear x p = reval p x := by
  simp [revalLinear, reval, aeval_def]

lemma secondOrderAt_apply (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    (x : Coord) (p : CPoly) : secondOrderAt g b x p = smoothSecondOrder g b (reval p) x := by
  simp [secondOrderAt, smoothSecondOrder, coordPartial_reval, revalLinear_apply, smul_eq_mul]

lemma transportAt_apply (W : Fin 4 → Coord → ℂ) (c : Coord → ℂ) (x : Coord) (p : CPoly) :
    transportAt W c x p = smoothTransport W c (fun _ ↦ 0) (reval p) x := by
  simp [transportAt, smoothTransport, coordPartial_reval, revalLinear_apply, smul_eq_mul]

theorem evaluated_transport_telescope (B L : CPoly →ₗ[ℂ] ℂ) (a : ℕ → CPoly)
    (N : ℂ) (hN : N ≠ 0) (J : ℕ) :
    N * B (∑ j ∈ Finset.range (J + 1), (N⁻¹ ^ j) • a j) +
      L (∑ j ∈ Finset.range (J + 1), (N⁻¹ ^ j) • a j) =
    N * B (a 0) +
      (∑ j ∈ Finset.range J, (N⁻¹ ^ j) * (B (a (j + 1)) + L (a j))) +
      (N⁻¹ ^ J) * L (a J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ (n := J + 1), map_add, map_add, map_smul, map_smul]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [smul_eq_mul]
    have hpow : N * N⁻¹ ^ (J + 1) = N⁻¹ ^ J := by
      rw [pow_succ]
      field_simp
    calc
      _ = (N * B (∑ j ∈ Finset.range (J + 1), N⁻¹ ^ j • a j) +
        L (∑ j ∈ Finset.range (J + 1), N⁻¹ ^ j • a j)) +
        (N * N⁻¹ ^ (J + 1)) * B (a (J + 1)) + N⁻¹ ^ (J + 1) * L (a (J + 1)) := by ring
      _ = _ := by rw [ih, hpow]; ring

lemma finiteAmplitude_range_reval (A : ℕ → CPoly) (J : ℕ) (N : ℝ) :
    reval (∑ j ∈ Finset.range (J + 1), ((N : ℂ)⁻¹ ^ j) • A j) = finiteAmplitude A J N := by
  funext x
  simp [finiteAmplitude, polynomialFamily, reval, Algebra.smul_def]
  exact (Fin.sum_univ_eq_sum_range (fun j ↦ ((N : ℂ)^j)⁻¹ *
    eval (fun i ↦ (x i : ℂ)) (A j)) (J + 1)).symm

theorem smooth_finite_transport_telescope
    (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    (phi : Coord → ℂ) (A : ℕ → CPoly) (J : ℕ) {N : ℝ} (hN : N ≠ 0) (x : Coord) :
    (N : ℂ) * smoothTransport (smoothBeamVector g phi) (smoothBeamScalar g b phi)
      (fun _ ↦ 0) (finiteAmplitude A J N) x + smoothSecondOrder g b (finiteAmplitude A J N) x =
    (N : ℂ) * smoothTransport (smoothBeamVector g phi) (smoothBeamScalar g b phi)
      (fun _ ↦ 0) (reval (A 0)) x +
      (∑ j ∈ Finset.range J, ((N : ℂ)⁻¹ ^ j) *
        (smoothTransport (smoothBeamVector g phi) (smoothBeamScalar g b phi)
          (fun _ ↦ 0) (reval (A (j + 1))) x + smoothSecondOrder g b (reval (A j)) x)) +
      ((N : ℂ)⁻¹ ^ J) * smoothSecondOrder g b (reval (A J)) x := by
  have h := evaluated_transport_telescope
    (transportAt (smoothBeamVector g phi) (smoothBeamScalar g b phi) x)
    (secondOrderAt g b x) A (N : ℂ) (by exact_mod_cast hN) J
  simpa only [transportAt_apply, secondOrderAt_apply, finiteAmplitude_range_reval] using h

theorem smooth_finite_wave_residual
    (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    (hg : ∀ i j x, g i j x = g j i x)
    (phi : Coord → ℂ) (hp : ContDiff ℝ ∞ phi) (A : ℕ → CPoly) (J : ℕ)
    {N : ℝ} (hN : N ≠ 0) (x : Coord) :
    smoothSecondOrder g b (fun z ↦ finiteAmplitude A J N z * waveExp phi N z) x +
      ((4 : ℂ) * (N : ℂ)^2 + 6 * (N : ℂ)) *
        (finiteAmplitude A J N x * waveExp phi N x) =
    waveExp phi N x *
      ((N : ℂ)^2 * smoothEikonal g phi x * finiteAmplitude A J N x +
        (N : ℂ) * smoothTransport (smoothBeamVector g phi) (smoothBeamScalar g b phi)
          (fun _ ↦ 0) (reval (A 0)) x +
        (∑ j ∈ Finset.range J, ((N : ℂ)⁻¹ ^ j) *
          (smoothTransport (smoothBeamVector g phi) (smoothBeamScalar g b phi)
            (fun _ ↦ 0) (reval (A (j + 1))) x + smoothSecondOrder g b (reval (A j)) x)) +
        ((N : ℂ)⁻¹ ^ J) * smoothSecondOrder g b (reval (A J)) x) := by
  rw [smooth_wave_residual_identity g b hg hp (finiteAmplitude_contDiff A J N)]
  have h := smooth_finite_transport_telescope g b phi A J hN x
  congr 1
  linear_combination h

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_ResidualProduct
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma DerivativeBound.enlarge {k : ℕ} {f : Coord → ℂ} {x : Coord} {A B : ℝ}
    (h : DerivativeBound k f x A) (hAB : A ≤ B) : DerivativeBound k f x B :=
  fun j hj ↦ (h j hj).trans hAB

lemma DerivativeBound.const_mul {k : ℕ} {f : Coord → ℂ} {x : Coord} {C : ℝ}
    (h : DerivativeBound k f x C) (hf : ContDiff ℝ ∞ f) (c : ℂ) :
    DerivativeBound k (fun z ↦ c * f z) x (‖c‖ * C) := by
  intro j hj
  change ‖iteratedFDeriv ℝ j (fun z ↦ c • f z) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le
    (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt, norm_smul]
  exact mul_le_mul_of_nonneg_left (h j hj) (norm_nonneg c)

lemma DerivativeBound.scale_power {k : ℕ} {f : Coord → ℂ} {x : Coord}
    {C N p q : ℝ} (h : DerivativeBound k f x (C * N ^ p))
    (hf : ContDiff ℝ ∞ f) (hC : 0 ≤ C) (hN : 0 < N)
    (c : ℂ) (hc : ‖c‖ ≤ N ^ q) :
    DerivativeBound k (fun z ↦ c * f z) x (C * N ^ (p+q)) := by
  apply (h.const_mul hf c).enlarge
  calc
    _ ≤ N ^ q * (C * N ^ p) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [Real.rpow_add hN]; ring

lemma DerivativeBound.exponent_mono {k : ℕ} {f : Coord → ℂ} {x : Coord}
    {C N p q : ℝ} (h : DerivativeBound k f x (C * N ^ p))
    (hC : 0 ≤ C) (hN : 1 ≤ N) (hpq : p ≤ q) :
    DerivativeBound k f x (C * N ^ q) :=
  h.enlarge (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hpq) hC)

lemma norm_complex_inv_pow {N : ℝ} (hN : 0 < N) (j : ℕ) :
    ‖((N : ℂ)⁻¹ ^ j)‖ = N ^ (-(j : ℝ)) := by
  rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN,
    inv_pow, Real.rpow_neg hN.le, Real.rpow_natCast]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CutoffResidualProductLemmas
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Yau.Jets

open scoped ContDiff

theorem cutoff_residual_times_exponential_bound (k0 : ℕ) : ∃ B > 0,
    ∀ (phi f : Coord → ℂ), ContDiff ℝ ∞ phi → ContDiff ℝ ∞ f →
    ∀ (x y : Coord) (C D N K S : ℝ), 0 ≤ C → 1 ≤ D → 1 ≤ N →
    DerivativeBound k0 f x (C * N ^ (-K-k0)) →
    DerivativeBound k0 phi x D → (phi x).re ≤ S →
    ‖iteratedFDeriv ℝ k0 (fun z ↦ Yau.Waves.scaledCutoff N y z •
      (f z * waveExp phi N z)) x‖ ≤
      B * C * (k0.factorial : ℝ) * D ^ k0 * N ^ (-K) * Real.exp (N*S) := by
  obtain ⟨B, hB, hcut⟩ := Yau.Waves.cutoff_preserves_derivative_exponent (E := Coord) (F := ℂ) k0
  refine ⟨2^k0*B*2^k0, by positivity, ?_⟩
  intro phi f hp hf x y C D N K S hC hD hN hcore hphase hgap
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let Q := (k0.factorial : ℝ) * D ^ k0
  have hQ : 0 ≤ Q := by dsimp [Q] <;> positivity
  have he (j : ℕ) (hj : j ≤ k0) :
      ‖iteratedFDeriv ℝ j (waveExp phi N) x‖ ≤ Q * N ^ j * Real.exp (N*S) := by
    apply (waveExp_derivative_bound hp j x hD hN
      (fun i _ hi ↦ hphase i (hi.trans hj))).trans
    have hfact : (j.factorial : ℝ) ≤ k0.factorial := by exact_mod_cast Nat.factorial_le hj
    have hpow : D ^ j ≤ D ^ k0 := pow_le_pow_right₀ hD hj
    have hexp : Real.exp (N*(phi x).re) ≤ Real.exp (N*S) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hgap hNp.le)
    dsimp [Q]
    gcongr
  have hau (j : ℕ) (hj : j ≤ k0) :
      ‖iteratedFDeriv ℝ j (fun z ↦ f z * waveExp phi N z) x‖ ≤
      (2^k0 * (C * N ^ (-K-k0)) * Q) * N ^ j * Real.exp (N*S) := by
    apply (mul_derivative_power_bound hf (waveExp_contDiff hp N) j x
      (by positivity : 0 ≤ C * N ^ (-K-k0)) hNp.le _
      (fun i hi ↦ he i (hi.trans hj))).trans
    · have hjpow : (2:ℝ)^j ≤ 2^k0 := pow_le_pow_right₀ (by norm_num) hj
      gcongr
    · intro i hi
      exact (hcore i (hi.trans hj)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hN))
  have h := hcut N hN y x (fun z ↦ f z * waveExp phi N z)
    (hf.mul (waveExp_contDiff hp N)) (2^k0*(C*N^(-K-k0))*Q) (Real.exp (N*S))
    (by positivity) (Real.exp_pos _).le hau
  have hpow : N ^ (-K) = N ^ (-K-k0) * N ^ k0 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNp]
    congr 1
    ring
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [hpow]
  dsimp [Q]
  ring

lemma finiteResidualCore_contDiff {E a t0 : Coord → ℂ} {tj : ℕ → Coord → ℂ}
    {L : Coord → ℂ} (hE : ContDiff ℝ ∞ E) (ha : ContDiff ℝ ∞ a)
    (ht0 : ContDiff ℝ ∞ t0) (htj : ∀ j, ContDiff ℝ ∞ (tj j))
    (hL : ContDiff ℝ ∞ L) (J : ℕ) (N : ℝ) :
    ContDiff ℝ ∞ (finiteResidualCore E a t0 tj L J N) :=
  (((contDiff_const.mul (hE.mul ha)).add (contDiff_const.mul ht0)).add
    (ContDiff.sum (fun j _ ↦ contDiff_const.mul (htj j)))).add (contDiff_const.mul hL)

theorem finiteResidualCore_bound {E a t0 : Coord → ℂ} {tj : ℕ → Coord → ℂ}
    {L : Coord → ℂ} (hE : ContDiff ℝ ∞ E) (ha : ContDiff ℝ ∞ a)
    (ht0 : ContDiff ℝ ∞ t0) (htj : ∀ j, ContDiff ℝ ∞ (tj j))
    (hL : ContDiff ℝ ∞ L) (k J : ℕ) (x : Coord) {K C A N : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hN : 1 ≤ N) (hJ : K+k ≤ J)
    (hEb : DerivativeBound k E x (C * N ^ (-K-k-2)))
    (hab : DerivativeBound k a x A)
    (ht0b : DerivativeBound k t0 x (C * N ^ (-K-k-2)))
    (htjb : ∀ j, j < J → DerivativeBound k (tj j) x (C * N ^ (-K-k-2)))
    (hLb : DerivativeBound k L x C) :
    DerivativeBound k (finiteResidualCore E a t0 tj L J N) x
      ((2^k*C*A + (J+2)*C) * N ^ (-K-k)) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hea : DerivativeBound k (fun z ↦ E z * a z) x
      ((2^k*C*A) * N ^ (-K-k-2)) := by
    convert hEb.mul hE ha (by positivity) hA hab using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hlead : DerivativeBound k (fun z ↦ (N:ℂ)^2 * (E z * a z)) x
      ((2^k*C*A) * N ^ (-K-k)) := by
    have h := hea.scale_power (hE.mul ha) (by positivity) hNp ((N:ℂ)^2)
      (q := 2) (by simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNp])
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  have htfirst : DerivativeBound k (fun z ↦ (N:ℂ) * t0 z) x (C * N ^ (-K-k)) := by
    apply (ht0b.scale_power ht0 hC hNp (N:ℂ) (q := 1)
      (by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNp])).exponent_mono hC hN
    linarith
  have htlater (j : ℕ) (hj : j < J) :
      DerivativeBound k (fun z ↦ ((N:ℂ)⁻¹^j) * tj j z) x (C * N ^ (-K-k)) := by
    apply ((htjb j hj).scale_power (htj j) hC hNp ((N:ℂ)⁻¹^j)
      (le_of_eq (norm_complex_inv_pow hNp j))).exponent_mono hC hN
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hlast : DerivativeBound k (fun z ↦ ((N:ℂ)⁻¹^J) * L z) x (C * N ^ (-K-k)) := by
    have hLb' : DerivativeBound k L x (C * N^ (0:ℝ)) := by simpa using hLb
    apply (hLb'.scale_power hL hC hNp ((N:ℂ)⁻¹^J)
      (le_of_eq (norm_complex_inv_pow hNp J))).exponent_mono hC hN
    linarith
  have hsum := DerivativeBound.sum (Finset.range J)
    (fun j _ ↦ contDiff_const.mul (htj j)) (fun j hj ↦ htlater j (Finset.mem_range.mp hj))
  have h := ((hlead.add (contDiff_const.mul (hE.mul ha)) (contDiff_const.mul ht0) htfirst).add
    ((contDiff_const.mul (hE.mul ha)).add (contDiff_const.mul ht0))
    (ContDiff.sum (fun j _ ↦ contDiff_const.mul (htj j))) hsum).add
    (((contDiff_const.mul (hE.mul ha)).add (contDiff_const.mul ht0)).add
      (ContDiff.sum (fun j _ ↦ contDiff_const.mul (htj j)))) (contDiff_const.mul hL) hlast
  apply h.enlarge
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_of_eq (by ring)

end Yau.Jets

end

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CommutatorBounds
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma DerivativeBound.sub {k : ℕ} {f g : Coord → ℂ} {x : Coord} {A B : ℝ}
    (h : DerivativeBound k f x A) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h' : DerivativeBound k g x B) : DerivativeBound k (fun z ↦ f z - g z) x (A+B) := by
  have hn : DerivativeBound k (fun z ↦ -g z) x B := by
    intro j hj
    change ‖iteratedFDeriv ℝ j (-g) x‖ ≤ B
    rw [iteratedFDeriv_neg_apply, norm_neg]
    exact h' j hj
  simpa only [sub_eq_add_neg] using h.add hf hg.neg hn

lemma secondOrder_derivative_bound (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (f : Coord → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : Coord) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgb : ∀ i j, DerivativeBound k (g i j) x C)
    (hbb : ∀ i, DerivativeBound k (b i) x C)
    (hfb : DerivativeBound (k+2) f x D) :
    DerivativeBound k (smoothSecondOrder g b f) x (20*2^k*C*D) := by
  have hh := (DerivativeBound.sum Finset.univ
    (fun i _ ↦ ContDiff.sum (fun j _ ↦ (hg i j).mul (coordPartial_contDiff (coordPartial_contDiff hf j) i)))
    (fun i _ ↦ DerivativeBound.sum Finset.univ
      (fun j _ ↦ (hg i j).mul (coordPartial_contDiff (coordPartial_contDiff hf j) i))
      (fun j _ ↦ (hgb i j).mul (hg i j) (coordPartial_contDiff (coordPartial_contDiff hf j) i)
        hC hD ((hfb.coordPartial hf j).coordPartial (coordPartial_contDiff hf j) i)))).add
    (ContDiff.sum (fun i _ ↦ ContDiff.sum (fun j _ ↦
      (hg i j).mul (coordPartial_contDiff (coordPartial_contDiff hf j) i))))
    (ContDiff.sum (fun i _ ↦ (hb i).mul (coordPartial_contDiff hf i)))
    (DerivativeBound.sum Finset.univ (fun i _ ↦ (hb i).mul (coordPartial_contDiff hf i))
      (fun i _ ↦ (hbb i).mul (hb i) (coordPartial_contDiff hf i) hC hD
        ((hfb.mono (by omega : k+1 ≤ k+2)).coordPartial hf i)))
  apply hh.enlarge
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_of_eq (by ring)

lemma real_smul_derivative_bound {beta : Coord → ℝ} {u : Coord → ℂ}
    (hb : ContDiff ℝ ∞ beta) (hu : ContDiff ℝ ∞ u) (k : ℕ) (x : Coord)
    {B A : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hbeta : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j beta x‖ ≤ B)
    (huB : DerivativeBound k u x A) :
    DerivativeBound k (fun z ↦ beta z • u z) x (2^k*B*A) := by
  intro j hj
  have h := Yau.Waves.smul_derivative_power_bound hb hu j x hB hA
    (N := 1) (w := 1) (by norm_num) (by norm_num)
    (fun i hi ↦ by simpa using hbeta i (hi.trans hj))
    (fun i hi ↦ by simpa using huB i (hi.trans hj))
  simp only [one_pow, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hB) hA)

lemma cutoffCommutator_contDiff (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hu : ContDiff ℝ ∞ u) (N : ℝ) (y : Coord) :
    ContDiff ℝ ∞ (cutoffCommutator g b u N y) :=
  (smoothSecondOrder_contDiff hg hb ((Yau.Waves.scaledCutoff_contDiff N y).smul hu)).sub
    ((Yau.Waves.scaledCutoff_contDiff N y).smul (smoothSecondOrder_contDiff hg hb hu))

theorem cutoffCommutator_polynomial_bound (k : ℕ) : ∃ B > 0,
    ∀ (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ),
    (∀ i j, ContDiff ℝ ∞ (g i j)) → (∀ i, ContDiff ℝ ∞ (b i)) → ContDiff ℝ ∞ u →
    ∀ (N : ℝ) (y x : Coord) (C A p w : ℝ), 1 ≤ N → 0 ≤ C → 0 ≤ A → 0 ≤ w →
    (∀ i j, DerivativeBound k (g i j) x C) →
    (∀ i, DerivativeBound k (b i) x C) →
    DerivativeBound (k+2) u x (A * N^p * w) →
    DerivativeBound k (cutoffCommutator g b u N y) x
      (B*C*A*N^(p+k+2)*w) := by
  obtain ⟨B, hB, hcut⟩ := Yau.Waves.scaledCutoff_all_derivatives (E := Coord) (k+2)
  refine ⟨20*2^k*2^(k+2)*B + 2^k*B*20*2^k, by positivity, ?_⟩
  intro g b u hg hb hu N y x C A p w hN hC hA hw hgb hbb hub
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hbeta (j : ℕ) (hj : j ≤ k+2) :
      ‖iteratedFDeriv ℝ j (Yau.Waves.scaledCutoff N y) x‖ ≤ B*N^(k+2) := by
    exact (hcut j hj N hN y x).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN hj) hB.le)
  have hcu := real_smul_derivative_bound (Yau.Waves.scaledCutoff_contDiff N y) hu
    (k+2) x (by positivity : 0 ≤ B*N^(k+2)) (by positivity : 0 ≤ A*N^p*w) hbeta hub
  have hLcu := secondOrder_derivative_bound g b _ hg hb
    ((Yau.Waves.scaledCutoff_contDiff N y).smul hu) k x hC (by positivity) hgb hbb hcu
  have hLu := secondOrder_derivative_bound g b u hg hb hu k x hC (by positivity) hgb hbb hub
  have hcuL := real_smul_derivative_bound (Yau.Waves.scaledCutoff_contDiff N y)
    (smoothSecondOrder_contDiff hg hb hu) k x (by positivity : 0 ≤ B*N^(k+2))
    (by positivity) (fun j hj ↦ hbeta j (by omega)) hLu
  have h := hLcu.sub (smoothSecondOrder_contDiff hg hb ((Yau.Waves.scaledCutoff_contDiff N y).smul hu))
    ((Yau.Waves.scaledCutoff_contDiff N y).smul (smoothSecondOrder_contDiff hg hb hu)) hcuL
  apply h.enlarge
  have hpow : N^(p+k+2) = N^(k+2:ℕ)*N^p := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNp]
    congr 1
    push_cast
    ring
  rw [hpow]
  exact le_of_eq (by ring)

open Filter
open scoped Topology

lemma coordPartial_eventuallyEq {f u : Coord → ℂ} {x : Coord}
    (h : f =ᶠ[𝓝 x] u) (i : Fin 4) : coordPartial i f =ᶠ[𝓝 x] coordPartial i u :=
  (h.fderiv (𝕜 := ℝ)).mono (fun _ hz ↦ congrArg (fun L : Coord →L[ℝ] ℂ ↦ L (Pi.single i 1)) hz)

lemma smoothSecondOrder_eventuallyEq (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) {f u : Coord → ℂ} {x : Coord} (h : f =ᶠ[𝓝 x] u) :
    smoothSecondOrder g b f =ᶠ[𝓝 x] smoothSecondOrder g b u := by
  have h1 : ∀ᶠ z in 𝓝 x, ∀ i, coordPartial i f z = coordPartial i u z :=
    Filter.eventually_all.mpr (fun i ↦ coordPartial_eventuallyEq h i)
  have h2 : ∀ᶠ z in 𝓝 x, ∀ i j, coordPartial i (coordPartial j f) z = coordPartial i (coordPartial j u) z :=
    Filter.eventually_all.mpr (fun i ↦ Filter.eventually_all.mpr
      (fun j ↦ coordPartial_eventuallyEq (coordPartial_eventuallyEq h j) i))
  filter_upwards [h1,h2] with z hz1 hz2
  simp only [smoothSecondOrder, hz1, hz2]

theorem cutoffCommutator_derivative_zero_near (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ) {N : ℝ} (hN : 0 < N)
    (y x : Coord) (k : ℕ) (hx : ‖x-y‖ < N^(-1/3:ℝ)) :
    iteratedFDeriv ℝ k (cutoffCommutator g b u N y) x = 0 := by
  have hnear : ∀ᶠ z in 𝓝 x, ‖z-y‖ < N^(-1/3:ℝ) :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hx
  have hbeta : Yau.Waves.scaledCutoff N y =ᶠ[𝓝 x] fun _ ↦ (1:ℝ) :=
    hnear.mono (fun z hz ↦ Yau.Waves.scaledCutoff_eq_one hN y z hz.le)
  have hprod : (fun z ↦ Yau.Waves.scaledCutoff N y z • u z) =ᶠ[𝓝 x] u := by
    filter_upwards [hbeta] with z hz
    rw [hz, one_smul]
  have hc : cutoffCommutator g b u N y =ᶠ[𝓝 x] fun _ ↦ (0:ℂ) := by
    filter_upwards [smoothSecondOrder_eventuallyEq g b hprod, hbeta] with z hz hz'
    simp only [cutoffCommutator, hz, hz', one_smul, sub_self]
  have h := (hc.iteratedFDeriv ℝ k).self_of_nhds
  simpa using h

theorem cutoffCommutator_gaussian_bound (k : ℕ) (c p K : ℝ) (hc : 0 < c) :
    ∃ B > 0, ∀ᶠ N : ℝ in atTop,
    ∀ (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ),
    (∀ i j, ContDiff ℝ ∞ (g i j)) → (∀ i, ContDiff ℝ ∞ (b i)) → ContDiff ℝ ∞ u →
    ∀ (y x : Coord) (C A S : ℝ), 0 ≤ C → 0 ≤ A →
    (∀ i j, DerivativeBound k (g i j) x C) →
    (∀ i, DerivativeBound k (b i) x C) →
    DerivativeBound (k+2) u x
      (A*N^p*Real.exp (N*S-c*N*‖x-y‖^2)) →
    ‖iteratedFDeriv ℝ k (cutoffCommutator g b u N y) x‖ ≤
      B*C*A*N^(-K)*Real.exp (N*S) := by
  obtain ⟨B, hB, hpoly⟩ := cutoffCommutator_polynomial_bound k
  refine ⟨B, hB, ?_⟩
  filter_upwards [Yau.Waves.gaussian_cutoff_bound c 1 hc (by norm_num) (p+k+2) K,
    eventually_ge_atTop (1:ℝ)] with N hgauss hN
  intro g b u hg hb hu y x C A S hC hA hgb hbb hub
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  by_cases hx : ‖x-y‖ < N^(-1/3:ℝ)
  · rw [cutoffCommutator_derivative_zero_near g b u hNp y x k hx, norm_zero]
    positivity
  have hrad : N^(-1/3:ℝ) ≤ ‖x-y‖ := le_of_not_gt hx
  have hann : N^(1/3:ℝ) ≤ N*‖x-y‖^2 := by
    have he : N * (N^(-1/3:ℝ))^2 = N^(1/3:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
      nth_rw 1 [← Real.rpow_one N]
      rw [← Real.rpow_add hNp]
      congr 1
      norm_num
    rw [← he]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hrad 2) hNp.le
  have h := hpoly g b u hg hb hu N y x C A p
    (Real.exp (N*S-c*N*‖x-y‖^2)) hN hC hA (Real.exp_pos _).le hgb hbb hub k le_rfl
  apply h.trans
  simpa only [one_mul, mul_assoc] using hgauss S ‖x-y‖ (B*C*A) (by positivity) (by simpa using hann)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CutoffWaveResidual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open Filter
open scoped ContDiff Topology
noncomputable section

lemma cutoff_residual_split (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ) (N : ℝ) (y x : Coord) (lam : ℂ) :
    smoothSecondOrder g b (fun z ↦ Yau.Waves.scaledCutoff N y z • u z) x +
      lam * (Yau.Waves.scaledCutoff N y x • u x) =
    Yau.Waves.scaledCutoff N y x • (smoothSecondOrder g b u x + lam*u x) +
      cutoffCommutator g b u N y x := by
  simp only [cutoffCommutator, smul_add, mul_smul_comm]
  abel

theorem cutoff_wave_residual_bound (k : ℕ) (c K p : ℝ) (hc : 0 < c) :
    ∃ B₁ > 0, ∃ B₂ > 0, ∀ᶠ N : ℝ in atTop,
    ∀ (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
      (u phi core : Coord → ℂ) (lam : ℂ),
    (∀ i j, ContDiff ℝ ∞ (g i j)) → (∀ i, ContDiff ℝ ∞ (b i)) →
    ContDiff ℝ ∞ u → ContDiff ℝ ∞ phi → ContDiff ℝ ∞ core →
    (∀ z, smoothSecondOrder g b u z + lam*u z = core z * waveExp phi N z) →
    ∀ (x y : Coord) (C D G A S : ℝ), 0 ≤ C → 1 ≤ D → 0 ≤ G → 0 ≤ A →
    DerivativeBound k core x (C*N^(-K-k)) → DerivativeBound k phi x D →
    (phi x).re ≤ S →
    (∀ i j, DerivativeBound k (g i j) x G) →
    (∀ i, DerivativeBound k (b i) x G) →
    DerivativeBound (k+2) u x (A*N^p*Real.exp (N*S-c*N*‖x-y‖^2)) →
    ‖iteratedFDeriv ℝ k (fun z ↦
      smoothSecondOrder g b (fun w ↦ Yau.Waves.scaledCutoff N y w • u w) z +
      lam * (Yau.Waves.scaledCutoff N y z • u z)) x‖ ≤
      (B₁*C*(k.factorial:ℝ)*D^k + B₂*G*A)*N^(-K)*Real.exp (N*S) := by
  obtain ⟨B₁, hB₁, hprod⟩ := cutoff_residual_times_exponential_bound k
  obtain ⟨B₂, hB₂, hcomm⟩ := cutoffCommutator_gaussian_bound k c p K hc
  refine ⟨B₁, hB₁, B₂, hB₂, ?_⟩
  filter_upwards [hcomm, eventually_ge_atTop (1:ℝ)] with N hcommN hN
  intro g b u phi core lam hg hb hu hp hcore heq x y C D G A S hC hD hG hA
    hcoreB hphiB hgap hgb hbb hub
  have h1 := hprod phi core hp hcore x y C D N K S hC hD hN hcoreB hphiB hgap
  have h2 := hcommN g b u hg hb hu y x G A S hG hA hgb hbb hub
  have he : (fun z ↦ smoothSecondOrder g b (fun w ↦ Yau.Waves.scaledCutoff N y w • u w) z +
      lam*(Yau.Waves.scaledCutoff N y z • u z)) =
      (fun z ↦ Yau.Waves.scaledCutoff N y z • (core z * waveExp phi N z)) +
      cutoffCommutator g b u N y := by
    funext z
    rw [cutoff_residual_split, heq z]
    rfl
  rw [he, iteratedFDeriv_add_apply
    (f := fun z ↦ Yau.Waves.scaledCutoff N y z • (core z * waveExp phi N z))
    (((Yau.Waves.scaledCutoff_contDiff N y).smul (hcore.mul (waveExp_contDiff hp N))).of_le
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    ((cutoffCommutator_contDiff g b u hg hb hu N y).of_le
      (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_UniformResidualCore
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

theorem uniform_finiteResidualCore_bound {s : Set T} {R : ℝ}
    (E t0 L : T → Coord → ℂ) (tj : ℕ → T → Coord → ℂ)
    (a : T → ℝ → Coord → ℂ)
    (hE : UniformSmoothBounded s R E) (ht0 : UniformSmoothBounded s R t0)
    (htj : ∀ j, UniformSmoothBounded s R (tj j)) (hL : UniformSmoothBounded s R L)
    (ha : ∀ t N, ContDiff ℝ ∞ (a t N))
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) (hR : 0 ≤ R)
    (hEz : ∀ t ∈ s, FlatAt m (E t) 0) (ht0z : ∀ t ∈ s, FlatAt m (t0 t) 0)
    (htjz : ∀ j, j < J → ∀ t ∈ s, FlatAt m (tj j t) 0)
    (hab : ∃ A > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord, ‖x‖ ≤ R →
      DerivativeBound k0 (a t N) x A) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord,
      ‖x‖ ≤ R * N ^ (-1/3 : ℝ) →
      DerivativeBound k0 (finiteResidualCore (E t) (a t N) (t0 t)
        (fun j ↦ tj j t) (L t) J N) x (C * N ^ (-(K : ℝ)-k0)) := by
  obtain ⟨CE, hCE, hEb⟩ := uniform_flat_derivative_decay hE hm hR hEz
  obtain ⟨C0, hC0, ht0b⟩ := uniform_flat_derivative_decay ht0 hm hR ht0z
  obtain ⟨CL, hCL, hLb⟩ := hL.2 k0
  obtain ⟨A, hA, haB⟩ := hab
  have hjs (j : Fin J) := uniform_flat_derivative_decay (htj j.val) hm hR (htjz j.val j.isLt)
  choose Cj hCj hjb using hjs
  let B := CE + C0 + CL + ∑ j, Cj j
  have hsum : 0 ≤ ∑ j, Cj j := Finset.sum_nonneg (fun j _ ↦ (hCj j).le)
  have hB : 0 < B := by dsimp [B] <;> positivity
  have heB : CE ≤ B := by dsimp [B] <;> linarith
  have h0B : C0 ≤ B := by dsimp [B] <;> linarith
  have hlB : CL ≤ B := by dsimp [B] <;> linarith
  have hjB (j : Fin J) : Cj j ≤ B := by
    have := Finset.single_le_sum (fun i _ ↦ (hCj i).le) (Finset.mem_univ j)
    dsimp [B]
    linarith
  refine ⟨2^k0*B*A + (J+2)*B, by positivity, ?_⟩
  intro t ht N hN x hx
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hp : 0 ≤ N ^ (-(K : ℝ)-k0-2) := Real.rpow_nonneg hNp.le _
  have hxR : ‖x‖ ≤ R := by
    apply hx.trans
    calc
      _ ≤ R * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)) hR
      _ = _ := mul_one R
  apply finiteResidualCore_bound (hE.1 t) (ha t N) (ht0.1 t) (fun j ↦ (htj j).1 t)
    (hL.1 t) k0 J x hB.le hA.le hN (by exact_mod_cast (show K+k0 ≤ J by omega))
  · exact (hEb t ht N hN x hx).enlarge (mul_le_mul_of_nonneg_right heB hp)
  · exact haB t ht N hN x hxR
  · exact (ht0b t ht N hN x hx).enlarge (mul_le_mul_of_nonneg_right h0B hp)
  · intro j hj
    exact (hjb ⟨j,hj⟩ t ht N hN x hx).enlarge
      (mul_le_mul_of_nonneg_right (hjB ⟨j,hj⟩) hp)
  · exact (hLb t ht x hxR).enlarge hlB

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_UniformUncutResidual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma finiteAmplitude_all_parameter_derivatives (A : ℕ → T → CPoly)
    (hA : ∀ j, ContinuousPolyFamily (A j)) (J k : ℕ)
    (s : Set T) (hs : IsCompact s) (R : ℝ) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord, ‖x‖ ≤ R →
      DerivativeBound k (finiteAmplitude (fun j ↦ A j t) J N) x C := by
  have h (j : Fin (k+1)) := finiteAmplitude_parameter_uniform_derivative_bound A hA J j.val s hs R
  choose C hC hb using h
  refine ⟨∑ j, C j, ?_, ?_⟩
  · exact (hC ⟨0, by omega⟩).trans_le
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))
  · intro t ht N hN x hx j hj
    exact (hb ⟨j, by omega⟩ t ht N hN x hx).trans
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_UniformWaveResidual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open Filter
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T]

omit [TopologicalSpace T] in
lemma finite_uniformSmoothBounded_bound {ι : Type*} [Fintype ι]
    {s : Set T} {R : ℝ} (f : ι → T → Coord → ℂ)
    (hf : ∀ i, UniformSmoothBounded s R (f i)) (k : ℕ) :
    ∃ C > 0, ∀ i t, t ∈ s → ∀ x : Coord, ‖x‖ ≤ R → DerivativeBound k (f i t) x C := by
  choose C hC hb using (fun i ↦ (hf i).2 k)
  have hnonneg : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ ↦ (hC i).le)
  refine ⟨1+∑ i, C i, by linarith, ?_⟩
  intro i t ht x hx
  apply (hb i t ht x hx).enlarge
  have := Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ i)
  linarith

lemma uncut_wave_all_gaussian_derivatives {phi a : Coord → ℂ}
    (hp : ContDiff ℝ ∞ phi) (ha : ContDiff ℝ ∞ a) (k : ℕ) (x : Coord)
    {A D N S c r : ℝ} (hA : 0 ≤ A) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hab : DerivativeBound k a x A) (hpb : DerivativeBound k phi x D)
    (hgap : (phi x).re-S ≤ -c*r^2) :
    DerivativeBound k (fun z ↦ a z * waveExp phi N z) x
      ((2^k*A*(k.factorial:ℝ)*D^k)*N^k*Real.exp (N*S-c*N*r^2)) := by
  let Q := (k.factorial:ℝ)*D^k
  have hNp : 0 ≤ N := le_trans zero_le_one hN
  have he (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (waveExp phi N) x‖ ≤ Q*N^j*Real.exp (N*S-c*N*r^2) := by
    apply (waveExp_gaussian_derivative_bound hp j x hD hN
      (fun i _ hi ↦ hpb i (hi.trans hj)) hgap).trans
    have hfact : (j.factorial:ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hj
    have hpow : D^j ≤ D^k := pow_le_pow_right₀ hD hj
    dsimp [Q]
    gcongr
  intro j hj
  have hh := mul_derivative_power_bound ha (waveExp_contDiff hp N) j x hA hNp
    (fun i hi ↦ (hab i (hi.trans hj)).trans
      (le_mul_of_one_le_right hA (one_le_pow₀ hN))) (fun i hi ↦ he i (hi.trans hj))
  apply hh.trans
  have h2 : (2:ℝ)^j ≤ 2^k := pow_le_pow_right₀ (by norm_num) hj
  have hn : N^j ≤ N^k := pow_le_pow_right₀ hN hj
  dsimp [Q]
  simp only [mul_assoc]
  gcongr

theorem uniform_cutoff_wave_residual {s : Set T} (hs : IsCompact s) {R : ℝ} (hR : 0 ≤ R)
    (c : ℝ) (hcpos : 0 < c)
    (g : T → Fin 4 → Fin 4 → Coord → ℂ) (b : T → Fin 4 → Coord → ℂ)
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hb : ∀ i, UniformSmoothBounded s R (fun t ↦ b t i))
    (hsym : ∀ t i j x, g t i j x = g t j i x)
    (phi : T → CPoly) (A : ℕ → T → CPoly)
    (hp : ContinuousPolyFamily phi) (hA : ∀ j, ContinuousPolyFamily (A j))
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J)
    (hE : ∀ t ∈ s, FlatAt m (smoothEikonal (g t) (reval (phi t))) 0)
    (hT0 : ∀ t ∈ s, FlatAt m (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
      (smoothBeamScalar (g t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A 0 t))) 0)
    (hTj : ∀ j, j < J → ∀ t ∈ s, FlatAt m
      (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
        (smoothBeamScalar (g t) (b t) (reval (phi t)))
        (fun x ↦ -smoothSecondOrder (g t) (b t) (reval (A j t)) x)
        (reval (A (j+1) t))) 0) :
    ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      ‖x‖ ≤ R * N ^ (-1/3 : ℝ) → ∀ S : ℝ,
      (reval (phi t) x).re-S ≤ -c*‖x‖^2 →
      ‖iteratedFDeriv ℝ k0 (fun z ↦
        smoothSecondOrder (g t) (b t) (fun w ↦ Yau.Waves.scaledCutoff N (0:Coord) w •
          (finiteAmplitude (fun j ↦ A j t) J N w * waveExp (reval (phi t)) N w)) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ)) * (Yau.Waves.scaledCutoff N (0:Coord) z •
          (finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z))) x‖ ≤
        C * N ^ (-(K:ℝ)) * Real.exp (N*S) := by

  let E := fun t ↦ smoothEikonal (g t) (reval (phi t))
  let t0 := fun t ↦ smoothTransport (smoothBeamVector (g t) (reval (phi t)))
    (smoothBeamScalar (g t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A 0 t))
  let tj := fun j t x ↦ smoothTransport (smoothBeamVector (g t) (reval (phi t)))
    (smoothBeamScalar (g t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A (j+1) t)) x +
      smoothSecondOrder (g t) (b t) (reval (A j t)) x
  let L := fun t ↦ smoothSecondOrder (g t) (b t) (reval (A J t))
  have hpB := hp.uniformSmoothBounded s hs R
  have hAB := fun j ↦ (hA j).uniformSmoothBounded s hs R
  have hEB : UniformSmoothBounded s R E := uniformSmoothBounded_eikonal hg hpB
  have ht0B : UniformSmoothBounded s R t0 := by
    have h := (UniformSmoothBounded.sum Finset.univ (fun i _ ↦
      (uniformSmoothBounded_beamVector hg hpB i).mul ((hAB 0).coordPartial i))).add
        ((uniformSmoothBounded_beamScalar hg hb hpB).mul (hAB 0))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext t x
    simp [t0, smoothTransport]
  have htjB : ∀ j, UniformSmoothBounded s R (tj j) := fun j ↦
    uniformSmoothBounded_transport_defect hg hb hpB (hAB (j+1)) (hAB j)
  have hLB : UniformSmoothBounded s R L := uniformSmoothBounded_secondOrder hg hb (hAB J)
  have htjz : ∀ j, j < J → ∀ t ∈ s, FlatAt m (tj j t) 0 := by
    intro j hj t ht
    convert hTj j hj t ht using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp [tj, smoothTransport]
  obtain ⟨C, hC, hc⟩ := uniform_finiteResidualCore_bound E t0 L tj
    (fun t N ↦ finiteAmplitude (fun j ↦ A j t) J N) hEB ht0B htjB hLB
    (fun t N ↦ finiteAmplitude_contDiff _ J N) m J K k0 hm hJ hR hE hT0 htjz
    (finiteAmplitude_all_parameter_derivatives A hA J k0 s hs R)
  obtain ⟨D, hD, hd⟩ := hpB.2 (k0+2)
  obtain ⟨AA, hAA, haa⟩ := finiteAmplitude_all_parameter_derivatives A hA J (k0+2) s hs R
  obtain ⟨G, hG, hGbound⟩ := finite_uniformSmoothBounded_bound
    (fun ij : Fin 4 × Fin 4 ↦ fun t ↦ g t ij.1 ij.2) (fun ij ↦ hg ij.1 ij.2) k0
  obtain ⟨B, hB, hBbound⟩ := finite_uniformSmoothBounded_bound (fun i t ↦ b t i) hb k0
  obtain ⟨Q1, hQ1, Q2, hQ2, hfull⟩ := cutoff_wave_residual_bound k0 c (K:ℝ) (k0+2) hcpos
  let AW := 2^(k0+2)*AA*((k0+2).factorial:ℝ)*(D+1)^(k0+2)
  refine ⟨Q1*C*(k0.factorial:ℝ)*(D+1)^k0 + Q2*(G+B)*AW, by dsimp [AW] <;> positivity, ?_⟩
  filter_upwards [hfull, eventually_ge_atTop (1:ℝ)] with N hfullN hN
  intro t ht x hx S hgap
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hxR : ‖x‖ ≤ R := by
    apply hx.trans
    calc
      _ ≤ R * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)) hR
      _ = _ := mul_one R
  let u := fun z ↦ finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z
  let core := finiteResidualCore (E t) (finiteAmplitude (fun j ↦ A j t) J N)
    (t0 t) (fun j ↦ tj j t) (L t) J N
  have hcore : ContDiff ℝ ∞ core := finiteResidualCore_contDiff (hEB.1 t)
    (finiteAmplitude_contDiff _ J N) (ht0B.1 t) (fun j ↦ (htjB j).1 t) (hLB.1 t) J N
  have heq (z : Coord) : smoothSecondOrder (g t) (b t) u z +
      ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ))*u z = core z * waveExp (reval (phi t)) N z := by
    dsimp [u]
    rw [smooth_finite_wave_residual (g t) (b t) (hsym t) _ (reval_contDiff _) _ J hNp.ne' z]
    dsimp [core, finiteResidualCore, E, t0, tj, L]
    ring
  have hphiB : DerivativeBound (k0+2) (reval (phi t)) x (D+1) :=
    (hd t ht x hxR).enlarge (by linarith)
  have huB := uncut_wave_all_gaussian_derivatives (reval_contDiff (phi t))
    (finiteAmplitude_contDiff (fun j ↦ A j t) J N) (k0+2) x hAA.le
    (by linarith : 1 ≤ D+1) hN (haa t ht N hN x hxR) hphiB hgap
  have hu : ContDiff ℝ ∞ u := (finiteAmplitude_contDiff _ J N).mul (waveExp_contDiff (reval_contDiff _) N)
  have h := hfullN (g t) (b t) u (reval (phi t)) core ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ))
    (fun i j ↦ (hg i j).1 t) (fun i ↦ (hb i).1 t) hu (reval_contDiff _) hcore heq
    x 0 C (D+1) (G+B) AW S hC.le (by linarith) (by positivity) (by dsimp [AW] <;> positivity)
    (hc t ht N hN x hx) (hphiB.mono (by omega))
    (by nlinarith [sq_nonneg ‖x‖])
    (fun i j ↦ (hGbound (i,j) t ht x hxR).enlarge (by linarith))
    (fun i ↦ (hBbound i t ht x hxR).enlarge (by linarith))
    (by
      have hpow : N ^ ((k0:ℝ)+2) = N ^ (k0+2:ℕ) := by
        rw [← Real.rpow_natCast]
        congr 1
        push_cast
        rfl
      simpa [u, AW, sub_zero, hpow] using huB)
  simpa [u] using h

theorem uniform_cutoff_wave_residual_all {s : Set T} (hs : IsCompact s) {R : ℝ} (hR : 0 ≤ R)
    (c : ℝ) (hcpos : 0 < c)
    (g : T → Fin 4 → Fin 4 → Coord → ℂ) (b : T → Fin 4 → Coord → ℂ)
    (hg : ∀ i j, UniformSmoothBounded s R (fun t ↦ g t i j))
    (hb : ∀ i, UniformSmoothBounded s R (fun t ↦ b t i))
    (hsym : ∀ t i j x, g t i j x = g t j i x)
    (phi : T → CPoly) (A : ℕ → T → CPoly)
    (hp : ContinuousPolyFamily phi) (hA : ∀ j, ContinuousPolyFamily (A j))
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J)
    (hE : ∀ t ∈ s, FlatAt m (smoothEikonal (g t) (reval (phi t))) 0)
    (hT0 : ∀ t ∈ s, FlatAt m (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
      (smoothBeamScalar (g t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A 0 t))) 0)
    (hTj : ∀ j, j < J → ∀ t ∈ s, FlatAt m
      (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
        (smoothBeamScalar (g t) (b t) (reval (phi t)))
        (fun x ↦ -smoothSecondOrder (g t) (b t) (reval (A j t)) x)
        (reval (A (j+1) t))) 0) :
    ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      ‖x‖ ≤ R * N ^ (-1/3 : ℝ) → ∀ S : ℝ,
      (reval (phi t) x).re-S ≤ -c*‖x‖^2 →
      DerivativeBound k0 (fun z ↦
        smoothSecondOrder (g t) (b t) (fun w ↦ Yau.Waves.scaledCutoff N (0:Coord) w •
          (finiteAmplitude (fun j ↦ A j t) J N w * waveExp (reval (phi t)) N w)) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ)) * (Yau.Waves.scaledCutoff N (0:Coord) z •
          (finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z))) x
        (C * N ^ (-(K:ℝ)) * Real.exp (N*S)) := by
  have h (j : Fin (k0+1)) := uniform_cutoff_wave_residual hs hR c hcpos g b hg hb hsym phi A hp hA
    m J K j.val (by omega) (by omega) hE hT0 hTj
  choose C hC hbound using h
  have hnonneg : 0 ≤ ∑ j, C j := Finset.sum_nonneg (fun j _ ↦ (hC j).le)
  refine ⟨1+∑ j, C j, by linarith, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound, eventually_ge_atTop (1:ℝ)] with N hNall hN
  intro t ht x hx S hgap j hj
  have h := hNall ⟨j, by omega⟩ t ht x hx S hgap
  apply h.trans
  have hsum : C ⟨j, by omega⟩ ≤ 1+∑ j, C j := by
    have := Finset.single_le_sum (fun i _ ↦ (hC i).le) (Finset.mem_univ (⟨j, by omega⟩ : Fin (k0+1)))
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg (by linarith : 0 ≤ N) _))
    (Real.exp_pos _).le

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_GlobalWaveResidual
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open Filter
open scoped ContDiff Topology
noncomputable section

lemma cutoff_residual_derivative_zero_outside (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ) (lam : ℂ) {N : ℝ} (hN : 0 < N)
    (x : Coord) (k : ℕ) (hx : 2*N^(-1/3:ℝ) < ‖x‖) :
    iteratedFDeriv ℝ k (fun z ↦
      smoothSecondOrder g b (fun w ↦ Yau.Waves.scaledCutoff N (0:Coord) w • u w) z +
        lam * (Yau.Waves.scaledCutoff N (0:Coord) z • u z)) x = 0 := by
  have hnear : ∀ᶠ z in 𝓝 x, 2*N^(-1/3:ℝ) < ‖z‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  have hbeta : Yau.Waves.scaledCutoff N (0:Coord) =ᶠ[𝓝 x] fun _ ↦ (0:ℝ) := by
    filter_upwards [hnear] with z hz
    by_contra hn
    have hm : z ∈ Function.support (Yau.Waves.scaledCutoff N (0:Coord)) := hn
    rw [Yau.Waves.scaledCutoff_support hN] at hm
    have hlt : ‖z‖ < 2*N^(-1/3:ℝ) := by simpa [Metric.mem_ball, dist_eq_norm] using hm
    linarith
  have hprod : (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z • u z) =ᶠ[𝓝 x] fun _ ↦ (0:ℂ) := by
    filter_upwards [hbeta] with z hz
    simp [hz]
  have hpartial (i : Fin 4) : coordPartial i (fun _ : Coord ↦ (0:ℂ)) = fun _ ↦ (0:ℂ) := by
    funext z
    simp [coordPartial]
  have hres : (fun z ↦ smoothSecondOrder g b (fun w ↦ Yau.Waves.scaledCutoff N (0:Coord) w • u w) z +
        lam * (Yau.Waves.scaledCutoff N (0:Coord) z • u z)) =ᶠ[𝓝 x] fun _ ↦ (0:ℂ) := by
    filter_upwards [smoothSecondOrder_eventuallyEq g b hprod, hprod] with z hz hz'
    rw [hz, hz']
    simp only [smoothSecondOrder, hpartial, mul_zero, Finset.sum_const_zero, zero_add]
  have h := (hres.iteratedFDeriv ℝ k).self_of_nhds
  simpa using h

variable {T : Type*} [TopologicalSpace T]
theorem global_uniform_cutoff_wave_residual {s : Set T} (hs : IsCompact s)
    (c : ℝ) (hcpos : 0 < c)
    (g : T → Fin 4 → Fin 4 → Coord → ℂ) (b : T → Fin 4 → Coord → ℂ)
    (hg : ∀ i j, UniformSmoothBounded s 2 (fun t ↦ g t i j))
    (hb : ∀ i, UniformSmoothBounded s 2 (fun t ↦ b t i))
    (hsym : ∀ t i j x, g t i j x = g t j i x)
    (phi : T → CPoly) (A : ℕ → T → CPoly)
    (hp : ContinuousPolyFamily phi) (hA : ∀ j, ContinuousPolyFamily (A j))
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J)
    (hE : ∀ t ∈ s, FlatAt m (smoothEikonal (g t) (reval (phi t))) 0)
    (hT0 : ∀ t ∈ s, FlatAt m (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
      (smoothBeamScalar (g t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A 0 t))) 0)
    (hTj : ∀ j, j < J → ∀ t ∈ s, FlatAt m
      (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
        (smoothBeamScalar (g t) (b t) (reval (phi t)))
        (fun x ↦ -smoothSecondOrder (g t) (b t) (reval (A j t)) x)
        (reval (A (j+1) t))) 0)
    (S : T → Coord → ℝ)
    (hgap : ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ 2*N^(-1/3:ℝ) →
      (reval (phi t) x).re-S t x ≤ -c*‖x‖^2) :
    ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      DerivativeBound k0 (fun z ↦
        smoothSecondOrder (g t) (b t) (fun w ↦ Yau.Waves.scaledCutoff N (0:Coord) w •
          (finiteAmplitude (fun j ↦ A j t) J N w * waveExp (reval (phi t)) N w)) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ)) * (Yau.Waves.scaledCutoff N (0:Coord) z •
          (finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z))) x
        (C * N ^ (-(K:ℝ)) * Real.exp (N*S t x)) := by
  obtain ⟨C, hC, hbound⟩ := uniform_cutoff_wave_residual_all hs (R := 2) (by norm_num)
    c hcpos g b hg hb hsym phi A hp hA m J K k0 hm hJ hE hT0 hTj
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, hgap, eventually_ge_atTop (1:ℝ)] with N hbN hgN hN
  intro t ht x
  by_cases hx : ‖x‖ ≤ 2*N^(-1/3:ℝ)
  · exact hbN t ht x hx (S t x) (hgN t ht x hx)
  · intro j hj
    rw [cutoff_residual_derivative_zero_outside (g t) (b t)
      (fun z ↦ finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z)
      ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ)) (by linarith : 0 < N) x j (lt_of_not_ge hx), norm_zero]
    positivity

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_MetricWaveJets
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Set MvPolynomial
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem MetricWaveJetFamily.global_residual
    {G : T → Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ} {b : T → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ}
    (hG : NormalOperatorFamily G b) {s a bb : T → ℝ} {H : T → Fin 4 → Fin 4 → ℝ}
    {m J : ℕ} {phi : T → CPoly} {A : ℕ → T → CPoly}
    (hj : MetricWaveJetFamily G b s a bb H m J phi A)
    (S : T → _root_.OAI.Yau.Jets.Coord → ℝ) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᶠ N : ℝ in atTop, ∀ t, ∀ x : _root_.OAI.Yau.Jets.Coord, ‖x‖ ≤ 2*N^(-1/3:ℝ) →
      (reval (phi t) x).re-S t x ≤ -c*‖x‖^2)
    (K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ t, ∀ x : _root_.OAI.Yau.Jets.Coord,
      DerivativeBound k0 (fun z ↦ smoothSecondOrder (G t) (b t)
        (fun w ↦ Yau.Waves.scaledCutoff N (0:_root_.OAI.Yau.Jets.Coord) w •
          (finiteAmplitude (fun j ↦ A j t) J N w * waveExp (reval (phi t)) N w)) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ)) * (Yau.Waves.scaledCutoff N (0:_root_.OAI.Yau.Jets.Coord) z •
          (finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z))) x
        (C*N^(-(K:ℝ))*Real.exp (N*S t x)) := by
  have hGb (i j : Fin 4) := uniformSmoothBounded_of_continuous_derivatives univ isCompact_univ 2
    (fun t ↦ G t i j) (fun t ↦ hG.principal_smooth t i j) (fun k ↦ hG.principal_jets k i j)
  have hbb (j : Fin 4) := uniformSmoothBounded_of_continuous_derivatives univ isCompact_univ 2
    (fun t ↦ b t j) (fun t ↦ hG.drift_smooth t j) (fun k ↦ hG.drift_jets k j)
  obtain ⟨C,hC,hbound⟩ := global_uniform_cutoff_wave_residual isCompact_univ c hc G b hGb hbb
    hG.principal_symm phi A hj.phase_continuous hj.amplitude_continuous m J K k0 hm hJ
    (fun t _ ↦ hj.eikonal_flat t) (fun t _ ↦ hj.transport_zero t)
    (fun j hj' t _ ↦ hj.transport_next j hj' t) S
    (hgap.mono (fun _ h t _ ↦ h t))
  exact ⟨C,hC,hbound.mono (fun _ h t ↦ h t (mem_univ t))⟩

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_UniformActualWaveSize
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open Filter Set
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma cutoff_wave_derivative_zero_outside (u : Coord → ℂ) {N : ℝ} (hN : 0 < N)
    (x : Coord) (k : ℕ) (hx : 2*N^(-1/3:ℝ) < ‖x‖) :
    iteratedFDeriv ℝ k (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z • u z) x = 0 := by
  have hnear : ∀ᶠ z in 𝓝 x, 2*N^(-1/3:ℝ) < ‖z‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  have he : (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z • u z) =ᶠ[𝓝 x] fun _ ↦ (0:ℂ) := by
    filter_upwards [hnear] with z hz
    have hb : Yau.Waves.scaledCutoff N (0:Coord) z = 0 := by
      by_contra hn
      have hm : z ∈ Function.support (Yau.Waves.scaledCutoff N (0:Coord)) := hn
      rw [Yau.Waves.scaledCutoff_support hN] at hm
      have hlt : ‖z‖ < 2*N^(-1/3:ℝ) := by simpa [Metric.mem_ball,dist_eq_norm] using hm
      linarith
    simp [hb]
  simpa using (he.iteratedFDeriv ℝ k).self_of_nhds

theorem uniform_cutoff_wave_size {s : Set T} (hs : IsCompact s)
    (phi : T → CPoly) (A : ℕ → T → CPoly)
    (hp : ContinuousPolyFamily phi) (hA : ∀ j, ContinuousPolyFamily (A j))
    (J k : ℕ) (S : T → Coord → ℝ) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord, ‖x‖ ≤ 2*N^(-1/3:ℝ) →
      (reval (phi t) x).re-S t x ≤ -c*‖x‖^2) :
    ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ t ∈ s, ∀ x : Coord,
      ‖iteratedFDeriv ℝ k (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z •
        (finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z)) x‖ ≤
        C*N^k*Real.exp (N*S t x-c*N*‖x‖^2) := by
  obtain ⟨Ca,hCa,hamp⟩ := finiteAmplitude_all_parameter_derivatives A hA J k s hs 2
  obtain ⟨Cp,hCp,hphase⟩ := (hp.uniformSmoothBounded s hs 2).2 k
  obtain ⟨B,hB,hsize⟩ := cutoff_wave_size k
  let D := max Cp (1+c)
  have hD : 1 ≤ D := (le_add_of_nonneg_right hc.le).trans (le_max_right _ _)
  refine ⟨B*Ca*(k.factorial:ℝ)*D^k,by positivity,?_⟩
  filter_upwards [hgap,eventually_ge_atTop (1:ℝ)] with N hgN hN
  intro t ht x
  by_cases hx : ‖x‖ ≤ 2*N^(-1/3:ℝ)
  · have hx2 : ‖x‖ ≤ 2 := hx.trans (by
      have hh := Real.rpow_le_one_of_one_le_of_nonpos hN (show (-1/3:ℝ) ≤ 0 by norm_num)
      linarith)
    simpa only [sub_zero,mul_assoc] using hsize (reval (phi t))
      (finiteAmplitude (fun j ↦ A j t) J N) (reval_contDiff _) (finiteAmplitude_contDiff _ _ _)
      0 x N Ca D (S t x) c hN hCa.le hD (hamp t ht N hN x hx2)
      (fun j _ hj ↦ (hphase t ht x hx2 j hj).trans (le_max_left _ _))
      (by simpa only [sub_zero] using hgN t ht x hx)
  · rw [cutoff_wave_derivative_zero_outside _ (by linarith) x k (lt_of_not_ge hx),norm_zero]
    positivity

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_CoefficientCutoffRemoval
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open Filter
open scoped ContDiff Topology
noncomputable section

lemma cutoff_operator_zero_outside (G : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ) {N : ℝ} (hN : 0 < N)
    (x : Coord) (hx : 2*N^(-1/3:ℝ) < ‖x‖) :
    smoothSecondOrder G b (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z • u z) x = 0 := by
  have h := cutoff_residual_derivative_zero_outside G b u 0 hN x 0 hx
  have hv := congrArg (fun L : Coord [×0]→L[ℝ] ℂ ↦ L 0) h
  simpa using hv

theorem coefficient_cutoff_operator_eq (beta : ContDiffBump (0:Coord)) :
    ∀ᶠ N : ℝ in atTop, ∀ (G : Fin 4 → Fin 4 → Coord → ℂ)
      (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ),
      smoothSecondOrder (fun i j x ↦ beta x • G i j x) (fun j x ↦ beta x • b j x)
        (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z • u z) =
      smoothSecondOrder G b (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z • u z) := by
  have ht : Tendsto (fun N : ℝ ↦ 2*N^(-1/3:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul 2
  have he : ∀ᶠ N : ℝ in atTop, 2*N^(-1/3:ℝ) < beta.rIn :=
    ht.eventually (gt_mem_nhds beta.rIn_pos)
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with N hsmall hN
  intro G b u
  funext x
  by_cases hx : ‖x‖ ≤ 2*N^(-1/3:ℝ)
  · have hbeta : beta x = 1 := beta.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hx.trans hsmall.le)
    simp only [smoothSecondOrder,hbeta,one_smul]
  · rw [cutoff_operator_zero_outside _ _ _ hN x (lt_of_not_ge hx),
      cutoff_operator_zero_outside _ _ _ hN x (lt_of_not_ge hx)]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_ConstructedCoordinateWaves
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Set MvPolynomial
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem constructed_coordinate_wave_estimates_oai
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
    (q : T → _root_.OAI.Yau.Jets.Coord) (a bb : T → ℝ) (ha : Continuous a) (hbb : Continuous bb)
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0) (hlen : ∀ t, bb t^2 = a t^2+4)
    (hap : ∀ t, a t • e t (Pi.single 0 1) = metricGradient g S (y t))
    (hbq : ∀ t, bb t • e t (Pi.single 1 1) = q t)
    (hstrict : ∀ t, 0 < sourceHessian g S (y t) (metricGradient g S (y t)) (metricGradient g S (y t)) +
      sourceHessian g S (y t) (q t) (q t)) (m J : ℕ) (K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    ∃ (beta : ContDiffBump (0:_root_.OAI.Yau.Jets.Coord)) (phi : T → CPoly) (A : ℕ → T → CPoly)
      (c Cr : ℝ) (Cs : Fin (k0+1) → ℝ),
      0 < c ∧ 0 < Cr ∧ (∀ k, 0 < Cs k) ∧
      MetricWaveJetFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta)
        (fun t ↦ S (y t)) a bb
        (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) m J phi A ∧
      ∀ᶠ n : ℕ in atTop, ∀ t, ∀ x : _root_.OAI.Yau.Jets.Coord,
        (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (coordinateWave phi A J (n:ℝ) t) x‖ ≤
          Cs k*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S (actualMetricChart g (y t) (e t) x)-c*(n:ℝ)*‖x‖^2)) ∧
        DerivativeBound k0 (fun z ↦ smoothSecondOrder (fun i j ↦ complexPrincipal g i j (metricChartParameter g (y t) (e t)))
          (fun j ↦ complexDrift g w j (metricChartParameter g (y t) (e t))) (coordinateWave phi A J (n:ℝ) t) z +
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*coordinateWave phi A J (n:ℝ) t z) x
          (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S (actualMetricChart g (y t) (e t) x))) := by
  obtain ⟨beta,phi,A,hG,hjets,c,hc,hgap⟩ := compact_actual_metric_wave_jets
    g hg hs hpos w hw S hS y hy e he ho hU hyU hwpos q a bb ha hbb ha0 hb0 hlen hap hbq hstrict
    m J (by omega)
  obtain ⟨Cr,hCr,hres⟩ := hjets.global_residual hG
    (fun t x ↦ S (actualMetricChart g (y t) (e t) x)) c hc hgap K k0 hm hJ
  have hsize (k : Fin (k0+1)) := uniform_cutoff_wave_size isCompact_univ phi A
    hjets.phase_continuous hjets.amplitude_continuous J k.val
    (fun t x ↦ S (actualMetricChart g (y t) (e t) x)) c hc
    (hgap.mono (fun _ h t _ ↦ h t))
  choose Cs hCs hsize using hsize
  refine ⟨beta,phi,A,c,Cr,Cs,hc,hCr,hCs,hjets,?_⟩
  have hreal : ∀ᶠ N : ℝ in atTop, ∀ t, ∀ x : _root_.OAI.Yau.Jets.Coord,
      (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (coordinateWave phi A J N t) x‖ ≤
        Cs k*N^k.val*Real.exp (N*S (actualMetricChart g (y t) (e t) x)-c*N*‖x‖^2)) ∧
      DerivativeBound k0 (fun z ↦ smoothSecondOrder (fun i j ↦ complexPrincipal g i j (metricChartParameter g (y t) (e t)))
        (fun j ↦ complexDrift g w j (metricChartParameter g (y t) (e t))) (coordinateWave phi A J N t) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ))*coordinateWave phi A J N t z) x
        (Cr*N^(-(K:ℝ))*Real.exp (N*S (actualMetricChart g (y t) (e t) x))) := by
    filter_upwards [hres,Filter.eventually_all.mpr hsize,coefficient_cutoff_operator_eq beta]
      with N hrN hsN heq
    intro t x
    refine ⟨fun k ↦ hsN k t (mem_univ t) x,?_⟩
    have he := heq
      (fun i j ↦ complexPrincipal g i j (metricChartParameter g (y t) (e t)))
      (fun j ↦ complexDrift g w j (metricChartParameter g (y t) (e t)))
      (fun z ↦ finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z)
    have hbound := hrN t x
    change DerivativeBound k0 (fun z ↦
      smoothSecondOrder (fun i j x ↦ beta x • complexPrincipal g i j (metricChartParameter g (y t) (e t)) x)
        (fun j x ↦ beta x • complexDrift g w j (metricChartParameter g (y t) (e t)) x)
        (coordinateWave phi A J N t) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ))*coordinateWave phi A J N t z) x _ at hbound
    change smoothSecondOrder _ _ (coordinateWave phi A J N t) = _ at he
    rw [he] at hbound
    exact hbound
  simpa only [Complex.ofReal_natCast] using eventually_nat_frequency hreal

end
end Yau.Geometry

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Yau.Geometry.constructed_coordinate_wave_estimates_oai.{u_1} := @OAI.Yau.Geometry.constructed_coordinate_wave_estimates_oai.{u_1}
