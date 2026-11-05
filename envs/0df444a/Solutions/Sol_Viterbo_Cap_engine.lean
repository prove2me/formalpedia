-- Prove2me | solution 1 for Viterbo.Cap.engine
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T17:54:44.068929+00:00
-- url     : https://prove2.me/submissions/a19f0dab-ddbd-4f94-a99c-59b0bc7b0d50

import Mathlib
import Definitions.Def_OAIQWSP000
import Theorems.Thm_MeasureTheory_sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Definitions.Def_ViterboCap
import Theorems.Thm_Viterbo_Cap_exists_critical_cerami
import Theorems.Thm_Viterbo_Cap_galerkin_cerami
universe u3 u4 u5 u6 u78 u79 u80 u81 u82 u83 u84 u85 u86 u87 u88 u89 u90 u91 u92 u93 u94 u95 u96 u97 u98 u99 u100 u101 u102 u103 u104 u105 u106 u107 u108 u109 u110 u111 u112 u113 u114 u115 u116 u117 u118 u119 u120 u121 u122 u123 u124 u125 u126 u127

section
section
-- module Solutions.OAIQW_SymmetricPolar.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_SymmetricPolar.LocalODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u5} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

noncomputable section

theorem curve_of_eq_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (hx : V x = 0) :
    EqOn (curve hV h hh x) (fun _ => x) (Icc 0 1) := by
  apply EqOn.symm
  apply curve_unique hV h hh x continuousOn_const
  · intro t _
    simpa only [hx, smul_zero] using (hasDerivWithinAt_const t (Ici t) x)
  · rfl

@[simp] theorem step_of_eq_zero {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x : E) (hx : V x = 0) :
    step hV h hh x = x := by
  have he := curve_of_eq_zero hV h hh x hx (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa using he

end
end SmoothODE

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.SmoothDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline
section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace SmoothDegree
noncomputable section

end
end SmoothDegree

end
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FiniteDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline
section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace SmoothLinking
noncomputable section
open Set Filter Function
open scoped Topology ContDiff
variable {E : Type u80} {F : Type u81} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

end
end SmoothLinking

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace FlowDescent
noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
variable {E : Type u82} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end
end FlowDescent

namespace FlowDescent
noncomputable section
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
variable {E : Type u83} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end
end FlowDescent

end
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.GradientLinking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline
section
open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace GradientDescent
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff
variable {E : Type u84} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

end
end GradientDescent

namespace GradientDescent
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {E : Type u85} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end
end GradientDescent

namespace FiniteLinking
noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
variable {H : Type u86} {E : Type u87} {F : Type u88} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

end
end FiniteLinking

end

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FourierIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate

 attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions
theorem continuous_eval {ι : Type u90} [Fintype ι] (k : ι → ℤ) (a : ι → ℂ) :
    Continuous (eval k a) := by
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (fourier (k i)).continuous)

 theorem integral_fourier (k : ℤ) :
    (∫ t : Time, fourier k t ∂μ) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Pi.single_apply,
    eq_comm (a := (0 : ℤ))] using h

 theorem integral_conj_fourier_mul (k l : ℤ) :
    (∫ t : Time, conj (fourier k t) * fourier l t ∂μ) = if k = l then 1 else 0 := by
  simp_rw [← fourier_neg, ← fourier_add]
  rw [integral_fourier]
  simp only [neg_add_eq_zero]

 theorem integral_conj_eval_mul {ι : Type u92} {κ : Type u93} [Fintype ι] [Fintype κ]
    (k : ι → ℤ) (l : κ → ℤ) (a : ι → ℂ) (b : κ → ℂ) :
    (∫ t : Time, conj (eval k a t) * eval l b t ∂μ) =
      ∑ i, ∑ j, if k i = l j then conj (a i) * b j else 0 := by
  classical
  have he (t : Time) : conj (eval k a t) * eval l b t =
      ∑ i, ∑ j, conj (a i)*conj (fourier (k i) t)*(b j*fourier (l j) t) := by
    change conj (∑ i, a i*fourier (k i) t) * eval l b t = _
    rw [map_sum, Finset.sum_mul]
    simp only [map_mul, eval, Finset.mul_sum]
  simp_rw [he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      simp_rw [show ∀ t : Time, conj (a i) * conj (fourier (k i) t) *
          (b j * fourier (l j) t) =
          (conj (a i)*b j) * (conj (fourier (k i) t)*fourier (l j) t) by intro t; ring]
      rw [integral_const_mul, integral_conj_fourier_mul]
      split_ifs <;> simp
    · intro j _
      exact integrable_continuous ((continuous_const.mul ((fourier (k i)).continuous.star)).mul
        (continuous_const.mul (fourier (l j)).continuous))
  · intro i _
    apply integrable_finsetSum
    intro j _
    exact integrable_continuous ((continuous_const.mul ((fourier (k i)).continuous.star)).mul
      (continuous_const.mul (fourier (l j)).continuous))

 theorem norm_sq_re (z : ℂ) : ‖z‖^2 = (conj z*z).re := by
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]

 theorem integral_norm_sq {ι : Type u94} [Fintype ι] (k : ι → ℤ) (hk : Function.Injective k)
    (a : ι → ℂ) : (∫ t : Time, ‖eval k a t‖^2 ∂μ) = ∑ i, ‖a i‖^2 := by
  classical
  simp_rw [norm_sq_re]
  have hI : Integrable (fun t : Time => conj (eval k a t) * eval k a t) μ :=
    integrable_continuous ((continuous_eval k a).star.mul (continuous_eval k a))
  change (∫ t : Time, RCLike.re (conj (eval k a t)*eval k a t) ∂μ) = _
  rw [integral_re hI, integral_conj_eval_mul]
  simp only [hk.eq_iff]
  simp

 theorem coe_integral_norm_fourth {ι : Type u95} [Fintype ι] (k : ι → ℤ) (a : ι → ℂ) :
    (((∫ t : Time, ‖eval k a t‖^4 ∂μ) : ℝ) : ℂ) =
      ∑ p : ι × ι, ∑ q : ι × ι,
        if k p.1+k p.2 = k q.1+k q.2 then conj (a p.1*a p.2)*(a q.1*a q.2) else 0 := by
  let k' : ι × ι → ℤ := fun p => k p.1+k p.2
  let a' : ι × ι → ℂ := fun p => a p.1*a p.2
  have heval (t : Time) : eval k' a' t = eval k a t * eval k a t := by
    simp only [eval, k', a', Fintype.sum_prod_type, fourier_add, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hintegrand (t : Time) : (↑(‖eval k a t‖^4) : ℂ) =
      conj (eval k' a' t)*eval k' a' t := by
    rw [heval, map_mul, mul_mul_mul_comm, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.sq_norm]
    push_cast
    ring
  rw [← integral_complex_ofReal]
  simp_rw [hintegrand]
  exact integral_conj_eval_mul k' k' a' a'

end
end FourierPolynomial

namespace WeightedSchur
noncomputable section
open Finset

 theorem two_mul_le_weighted {w v : ℝ} (hw : 0 < w) (hv : 0 < v) (x y : ℝ) :
    2*x*y ≤ w*x^2/v + v*y^2/w := by
  rw [div_add_div _ _ hv.ne' hw.ne', le_div_iff₀ (mul_pos hv hw)]
  nlinarith [sq_nonneg (w*x-v*y)]

 theorem sum_le {ι : Type u96} [Fintype ι] (r : ι → ι → Prop) [DecidableRel r]
    (hr : ∀ {i j}, r i j → r j i) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (x : ι → ℝ)
    {C : ℝ} (hrow : ∀ i, (∑ j, if r i j then 1/w j else 0) ≤ C) :
    (∑ i, ∑ j, if r i j then x i*x j else 0) ≤ C * ∑ i, w i*x i^2 := by
  have hp (i j : ι) : 2*(if r i j then x i*x j else 0) ≤
      (if r i j then w i*x i^2/w j else 0) +
      (if r j i then w j*x j^2/w i else 0) := by
    by_cases hij : r i j
    · simp only [ite_eq_left hij, ite_eq_left (hr hij)]
      simpa only [mul_assoc] using two_mul_le_weighted (hw i) (hw j) (x i) (x j)
    · have hji : ¬r j i := fun h => hij (hr h)
      simp only [ite_eq_right hij, ite_eq_right hji, mul_zero, add_zero, le_refl]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) => hp i j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hcomm : (∑ i : ι, ∑ j : ι, if r j i then w j*x j^2/w i else 0) =
      ∑ i : ι, ∑ j : ι, if r i j then w i*x i^2/w j else 0 := Finset.sum_comm
  rw [hcomm] at hs
  have hh : (∑ i : ι, ∑ j : ι, if r i j then w i*x i^2/w j else 0) ≤
      C * ∑ i, w i*x i^2 := by
    calc
      _ = ∑ i, w i*x i^2 * (∑ j, if r i j then 1/w j else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ ≤ ∑ i, w i*x i^2*C := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hrow i) (mul_nonneg (hw i).le (sq_nonneg _)))
      _ = _ := by rw [← Finset.sum_mul]; ring
  linarith

 theorem reciprocal_pair_rows {ι : Type u97} [Fintype ι] (k : ι → ℕ)
    (hk : Function.Injective k) (hk0 : ∀ i, 0 < k i) (p : ι × ι) :
    (∑ q : ι × ι, if k p.1+k p.2 = k q.1+k q.2 then
      1 / ((k q.1 : ℝ)*(k q.2 : ℝ)) else 0) ≤ 1 := by
  classical
  let m := k p.1+k p.2
  have hm : 2 ≤ m := by dsimp [m]; have := hk0 p.1; have := hk0 p.2; omega
  let Q := univ.filter (fun q : ι × ι => k q.1+k q.2 = m)
  have hQ (q : ι × ι) : q ∈ Q ↔ k q.1+k q.2 = m := by simp [Q]
  have hmaps : Set.MapsTo (fun q : ι × ι => k q.1) (↑Q : Set (ι × ι))
      (↑(Icc 1 (m-1)) : Set ℕ) := by
    intro q hq
    have he := (hQ q).mp hq
    have h0 := hk0 q.1
    have h1 := hk0 q.2
    simp only [mem_coe, mem_Icc]
    omega
  have hinj : Set.InjOn (fun q : ι × ι => k q.1) (↑Q : Set (ι × ι)) := by
    intro q hq z hz he
    change k q.1 = k z.1 at he
    have hq' := (hQ q).mp hq
    have hz' := (hQ z).mp hz
    apply Prod.ext (hk he)
    apply hk
    omega
  have hc : Q.card ≤ m-1 := by
    have hc' := Finset.card_le_card_of_injOn (fun q : ι × ι => k q.1) hmaps hinj
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc'
  have hd : 0 < (m : ℝ)-1 := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hterm (q : ι × ι) (hq : q ∈ Q) :
      1/((k q.1 : ℝ)*(k q.2 : ℝ)) ≤ 1/((m : ℝ)-1) := by
    apply one_div_le_one_div_of_le hd
    have h0 : 1 ≤ (k q.1 : ℝ) := by exact_mod_cast (show 1 ≤ k q.1 from hk0 q.1)
    have h1 : 1 ≤ (k q.2 : ℝ) := by exact_mod_cast (show 1 ≤ k q.2 from hk0 q.2)
    have he : (k q.1 : ℝ)+(k q.2 : ℝ) = m := by exact_mod_cast (hQ q).mp hq
    nlinarith [mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]
  calc
    _ = ∑ q ∈ Q, 1/((k q.1 : ℝ)*(k q.2 : ℝ)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q _
      simp only [m, eq_comm (a := k q.1+k q.2)]
    _ ≤ ∑ _q ∈ Q, 1/((m : ℝ)-1) := Finset.sum_le_sum hterm
    _ = (Q.card : ℝ)/((m : ℝ)-1) := by simp [div_eq_mul_inv]
    _ ≤ 1 := by
      rw [div_le_one hd]
      have hcR : (Q.card : ℝ) ≤ (m-1 : ℕ) := by exact_mod_cast hc
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at hcR
      exact hcR

end
end WeightedSchur

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate

 local instance instFactLtRealOfNat_solutions_1_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
theorem integral_norm_fourth_le_pairs {ι : Type u98} [Fintype ι] (k : ι → ℤ) (a : ι → ℂ) :
    (∫ t : Time, ‖eval k a t‖^4 ∂μ) ≤
      ∑ p : ι × ι, ∑ q : ι × ι,
        if k p.1+k p.2 = k q.1+k q.2 then
          (‖a p.1‖*‖a p.2‖)*(‖a q.1‖*‖a q.2‖) else 0 := by
  classical
  have hI : 0 ≤ ∫ t : Time, ‖eval k a t‖^4 ∂μ := integral_nonneg (fun _ => by positivity)
  calc
    _ = ‖(((∫ t : Time, ‖eval k a t‖^4 ∂μ) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hI]
    _ = ‖∑ p : ι × ι, ∑ q : ι × ι,
        if k p.1+k p.2 = k q.1+k q.2 then conj (a p.1*a p.2)*(a q.1*a q.2) else 0‖ :=
      congrArg norm (coe_integral_norm_fourth k a)
    _ ≤ ∑ p : ι × ι, ∑ q : ι × ι,
        ‖if k p.1+k p.2 = k q.1+k q.2 then conj (a p.1*a p.2)*(a q.1*a q.2) else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      split_ifs <;> simp only [norm_mul, Complex.norm_conj, norm_zero]

 theorem positive_L4 {ι : Type u99} [Fintype ι] (k : ι → ℕ)
    (hk : Function.Injective k) (hk0 : ∀ i, 0 < k i) (a : ι → ℂ) :
    (∫ t : Time, ‖eval (fun i => (k i : ℤ)) a t‖^4 ∂μ) ≤
      (∑ i, (k i : ℝ)*‖a i‖^2)^2 := by
  classical
  have hrows := WeightedSchur.reciprocal_pair_rows k hk hk0
  let w : ι × ι → ℝ := fun p => (k p.1 : ℝ)*(k p.2 : ℝ)
  have hw (p : ι × ι) : 0 < w p := by
    exact mul_pos (by exact_mod_cast hk0 p.1) (by exact_mod_cast hk0 p.2)
  have hS := WeightedSchur.sum_le
    (fun p q : ι × ι => k p.1+k p.2 = k q.1+k q.2)
    (fun h => h.symm) w hw (fun p => ‖a p.1‖*‖a p.2‖) hrows
  have hpair := integral_norm_fourth_le_pairs (fun i => (k i : ℤ)) a
  simp only [← Nat.cast_add, Int.natCast_inj] at hpair
  apply hpair.trans
  apply (hS.trans_eq _)
  simp only [one_mul, Fintype.sum_prod_type, w]
  calc
    _ = ∑ i, ∑ j, ((k i : ℝ)*‖a i‖^2)*((k j : ℝ)*‖a j‖^2) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [← Finset.sum_mul_sum]; ring

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.FourierPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
 local instance instFactLtRealOfNat_solutions_2_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
theorem real_inner_eq_complex_re {α : Type u100} [Fintype α] (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) a b = RCLike.re (inner (𝕜 := ℂ) a b) := by
  simp only [PiLp.inner_apply, real_inner_eq_re_inner, map_sum]

variable {ι : Type u101} {κ : Type u102} [Fintype ι] [Fintype κ]

 theorem integral_loop_norm_sq (k : ι → ℤ) (hk : Function.Injective k) (a : Coeff ι κ) :
    (∫ t : Time, ‖loop k a t‖^2 ∂μ) = ‖a‖^2 := by
  classical
  simp_rw [EuclideanSpace.norm_sq_eq, loop_coord]
  rw [integral_finsetSum]
  · simp_rw [integral_norm_sq k hk]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
  · intro j _
    exact integrable_continuous ((continuous_eval k _).norm.pow 2)

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_3_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u106} {κ : Type u107} [Fintype ι] [Fintype κ]

 theorem vector_norm_fourth_le (z : Vector κ) :
    ‖z‖^4 ≤ (Fintype.card κ : ℝ) * ∑ j, ‖z j‖^4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset κ)
    (fun j => ‖z j‖^2) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, ← pow_mul] at h
  calc
    _ = (∑ j, ‖z j‖^2)^2 := by rw [← EuclideanSpace.norm_sq_eq]; ring
    _ ≤ _ := by simpa only [mul_comm] using h

 theorem integral_loop_norm_fourth_le (k : ι → ℕ)
    (hk : Function.Injective k) (hk0 : ∀ i, 0 < k i) (a : Coeff ι κ) :
    (∫ t : Time, ‖loop (fun i => (k i : ℤ)) a t‖^4 ∂μ) ≤
      (Fintype.card κ : ℝ) * (∑ p : ι × κ, (k p.1 : ℝ)*‖a p‖^2)^2 := by
  classical
  let L := loop (fun i => (k i : ℤ)) a
  have hcont : Continuous (fun t : Time => (Fintype.card κ : ℝ)*∑ j, ‖L t j‖^4) :=
    continuous_const.mul (continuous_finsetSum _ (fun j _ =>
      (((PiLp.continuous_apply 2 _ j).comp L.continuous).norm.pow 4)))
  calc
    _ ≤ ∫ t : Time, (Fintype.card κ : ℝ)*∑ j, ‖L t j‖^4 ∂μ :=
      integral_mono (integrable_continuous (L.continuous.norm.pow 4))
        (integrable_continuous hcont) (fun t => vector_norm_fourth_le (L t))
    _ = (Fintype.card κ : ℝ)*∑ j, ∫ t : Time, ‖L t j‖^4 ∂μ := by
      rw [integral_const_mul, integral_finsetSum]
      intro j _
      exact integrable_continuous (((PiLp.continuous_apply 2 _ j).comp L.continuous).norm.pow 4)
    _ ≤ (Fintype.card κ : ℝ)*∑ j, (∑ i, (k i : ℝ)*‖a (i,j)‖^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      simp only [L, loop_coord]
      exact positive_L4 k hk hk0 _
    _ ≤ (Fintype.card κ : ℝ)*(∑ j, ∑ i, (k i : ℝ)*‖a (i,j)‖^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ =>
        Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
    _ = _ := by rw [Finset.sum_comm, Fintype.sum_prod_type]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_4
variable {ι : Type u108} {κ : Type u109} [Fintype ι] [Fintype κ]

 theorem fourierCoeff_eval (k : ι → ℤ) (a : ι → ℂ) (j : ℤ) :
    fourierCoeff (eval k a) j = ∑ i, if j = k i then a i else 0 := by
  classical
  simp only [fourierCoeff, eval, smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    have he (t : Time) : fourier (-j) t * (a i * fourier (k i) t) =
        a i*(conj (fourier j t)*fourier (k i) t) := by rw [fourier_neg]; ring
    simp_rw [he]
    rw [integral_const_mul, integral_conj_fourier_mul]
    split_ifs <;> simp only [mul_one, mul_zero]
  · intro i _
    exact integrable_continuous ((fourier (-j)).continuous.mul
      (continuous_const.mul (fourier (k i)).continuous))

 theorem project_loop (k : ι → ℤ) (hk : Function.Injective k) (a : Coeff ι κ) :
    project k (loop k a) = a := by
  classical
  ext p
  simp only [project_apply, loop_coord, fourierCoeff_eval, hk.eq_iff]
  simp

 theorem integral_fourier_mul_conj (k : ℤ) (f : C(Time, ℂ)) :
    (∫ t : Time, conj (f t) * fourier k t ∂μ) = conj (fourierCoeff f k) := by
  rw [fourierCoeff, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul, map_mul, fourier_neg, starRingEnd_self_apply]
  ring

 theorem integral_inner_loop (k : ι → ℤ) (f : C(Time, Vector κ)) (a : Coeff ι κ) :
    (∫ t : Time, inner (𝕜 := ℝ) (f t) (loop k a t) ∂μ) =
      inner (𝕜 := ℝ) (project k f) a := by
  classical
  have hstage (j : κ) :
      (∫ t : Time, conj (f t j)*eval k (fun i => a (i,j)) t ∂μ) =
        ∑ i, conj (project k f (i,j))*a (i,j) := by
    simp only [eval, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      have he (t : Time) : conj (f t j) * (a (i,j) * fourier (k i) t) =
          (conj (f t j) * fourier (k i) t) * a (i,j) := by ring
      simp_rw [he]
      rw [integral_mul_const]
      exact congrArg (fun z => z*a (i,j))
        (integral_fourier_mul_conj (k i)
          ⟨fun t => f t j, (PiLp.continuous_apply 2 _ j).comp f.continuous⟩)
    · intro i _
      exact integrable_continuous
        ((((PiLp.continuous_apply 2 _ j).comp f.continuous).star).mul
          (continuous_const.mul (fourier (k i)).continuous))
  have hcomplex : (∫ t : Time, inner (𝕜 := ℂ) (f t) (loop k a t) ∂μ) =
      inner (𝕜 := ℂ) (project k f) a := by
    change (∫ t : Time, ∑ j, loop k a t j * conj (f t j) ∂μ) =
      ∑ p : ι × κ, a p * conj (project k f p)
    simp_rw [loop_coord, mul_comm (eval k _ _)]
    rw [integral_finsetSum]
    · simp_rw [hstage]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      congr 1
      ext j
      apply Finset.sum_congr rfl
      intro i _
      ring
    · intro j _
      exact integrable_continuous
        ((((PiLp.continuous_apply 2 _ j).comp f.continuous).star).mul
          (continuous_eval k _))
  simp only [real_inner_eq_complex_re]
  rw [integral_re (integrable_continuous
    (show Continuous (fun t => inner (𝕜 := ℂ) (f t) (loop k a t)) from
      f.continuous.inner (loop k a).continuous)), hcomplex]

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_5_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι : Type u110} {κ : Type u111} [Fintype ι] [Fintype κ]

 theorem project_bessel (k : ι → ℤ) (hk : Function.Injective k) (f : C(Time, Vector κ)) :
    ‖project k f‖^2 ≤ ∫ t : Time, ‖f t‖^2 ∂μ := by
  -- coordinatewise from the published scalar Bessel inequality
  -- MeasureTheory.sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal, for the
  -- orthonormal characters fourier (k i), reindexed by Fin (card ι)
  classical
  let σ := Fintype.equivFin ι
  let e : Fin (Fintype.card ι) → Time → ℂ := fun i t => fourier (k (σ.symm i)) t
  have hcf (j : κ) : Continuous (fun t => f t j) :=
    (PiLp.continuous_apply 2 _ j).comp f.continuous
  have hj (j : κ) : ∑ i, ‖project k f (i, j)‖^2 ≤ ∫ t : Time, ‖f t j‖^2 ∂μ := by
    have h := MeasureTheory.sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal μ e
      (fun i i' => integrable_continuous
        ((fourier _).continuous.mul (Complex.continuous_conj.comp (fourier _).continuous)))
      (fun i i' => by
        have h0 := integral_conj_fourier_mul (k (σ.symm i')) (k (σ.symm i))
        simp_rw [e, mul_comm (fourier (k (σ.symm i)) _)]
        rw [h0]
        simp only [hk.eq_iff, σ.symm.injective.eq_iff, eq_comm])
      (fun t => f t j) (integrable_continuous ((hcf j).norm.pow 2))
      (fun i => integrable_continuous
        ((hcf j).mul (Complex.continuous_conj.comp (fourier _).continuous)))
    have hc (i : Fin (Fintype.card ι)) :
        (∫ t : Time, f t j * conj (e i t) ∂μ) = project k f (σ.symm i, j) := by
      rw [project_apply, fourierCoeff]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [e, smul_eq_mul, fourier_neg, mul_comm]
    simp_rw [hc] at h
    rw [← σ.symm.sum_comp]
    exact h
  calc ‖project k f‖^2 = ∑ j, ∑ i, ‖project k f (i, j)‖^2 := by
        rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
    _ ≤ ∑ j, ∫ t : Time, ‖f t j‖^2 ∂μ := Finset.sum_le_sum fun j _ => hj j
    _ = ∫ t : Time, ‖f t‖^2 ∂μ := by
        rw [← integral_finsetSum]
        · simp_rw [EuclideanSpace.norm_sq_eq]
        · intro j _
          exact integrable_continuous ((hcf j).norm.pow 2)

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_6
variable {ι κ : Type} [Fintype ι] [Fintype κ]

 theorem contDiff_potential (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (potential k H) := by
  exact average.contDiff.comp ((SmoothPaths.contDiff_superpose hH).comp (loopCLM k).contDiff)

 theorem hasGradientAt_potential (k : ι → ℤ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) :
    HasGradientAt (potential k H) (project k (gradLoop k hH a)) a := by
  have hl : HasFDerivAt (loop k) (loopCLM k) a := by
    change HasFDerivAt (loopCLM k) (loopCLM k) a
    exact (loopCLM (κ := κ) k).hasFDerivAt (x := a)
  have hS := (SmoothPaths.hasFDerivAt_superpose
    (hH.differentiable (by simp)) (hH.fderiv_right (m := ∞) (by simp)).continuous (loop k a)).comp
      a hl
  have hi := average.hasFDerivAt.comp a hS
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt (potential k H) _ a at hi
  apply hi.congr_fderiv
  ext b
  change (∫ t : Time, fderiv ℝ H (loop k a t) (loop k b t) ∂μ) =
    inner (𝕜 := ℝ) (project k (gradLoop k hH a)) b
  simp_rw [← inner_gradient_left]
  exact integral_inner_loop k (gradLoop k hH a) b

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.QuadraticAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace DiagonalQuadratic
noncomputable section
open Finset
open scoped ComplexConjugate ContDiff
variable {α : Type u112} [Fintype α]

 theorem real_inner_eq_sum (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) a b = ∑ p, inner (𝕜 := ℝ) (a p) (b p) := by
  exact PiLp.inner_apply a b

 theorem inner_diag (w : α → ℝ) (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) (diag w a) b = ∑ p, w p * inner (𝕜 := ℝ) (a p) (b p) := by
  rw [real_inner_eq_sum]
  simp only [diag_apply, real_inner_smul_left]

 theorem self_adjoint (w : α → ℝ) (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) (diag w a) b = inner (𝕜 := ℝ) a (diag w b) := by
  rw [inner_diag, real_inner_eq_sum]
  simp only [diag_apply, real_inner_smul_right]

 theorem energy_eq_inner (w : α → ℝ) (a : EuclideanSpace ℂ α) :
    energy w a = inner (𝕜 := ℝ) (diag w a) a := by
  rw [inner_diag]
  simp only [energy, real_inner_self_eq_norm_sq]

 theorem contDiff_energy (w : α → ℝ) : ContDiff ℝ ∞ (energy w) := by
  simp_rw [funext (energy_eq_inner w)]
  exact (diagCLM w).contDiff.inner ℝ contDiff_id

 theorem hasGradientAt_energy (w : α → ℝ) (a : EuclideanSpace ℂ α) :
    HasGradientAt (energy w) ((2 : ℝ) • diag w a) a := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (diagCLM w).hasFDerivAt.inner ℝ (hasFDerivAt_id a)
  simp only [diagCLM_apply] at h
  change HasFDerivAt (fun x => inner (𝕜 := ℝ) (diag w x) x) _ a at h
  simp_rw [← energy_eq_inner] at h
  apply h.congr_fderiv
  ext b
  change inner (𝕜 := ℝ) (diag w a) b + inner (𝕜 := ℝ) (diag w b) a =
    inner (𝕜 := ℝ) ((2 : ℝ) • diag w a) b
  rw [real_inner_smul_left, self_adjoint w b a]
  rw [real_inner_comm b (diag w a)]
  ring

 theorem energy_smul (w : α → ℝ) (r : ℝ) (a : EuclideanSpace ℂ α) :
    energy w (r • a) = r^2*energy w a := by
  simp only [energy, PiLp.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    mul_sum]
  apply sum_congr rfl
  intro p _
  ring

 theorem energy_mul (w : α → ℝ) (r : ℝ) (a : EuclideanSpace ℂ α) :
    energy (fun p => r*w p) a = r*energy w a := by
  simp only [energy, mul_sum, mul_assoc]

 theorem energy_nonpos (w : α → ℝ) (hw : ∀ p, w p ≤ 0)
    (a : EuclideanSpace ℂ α) : energy w a ≤ 0 :=
  sum_nonpos (fun p _ => mul_nonpos_of_nonpos_of_nonneg (hw p) (sq_nonneg _))

end
end DiagonalQuadratic

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_7_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 theorem contDiff_action (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (action k H) :=
  (contDiff_energy _).sub (contDiff_potential k hH)

 theorem hasGradientAt_action (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : Coeff ι κ) :
    HasGradientAt (action k H)
      ((2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)) a - project k (gradLoop k hH a)) a := by
  have h := (hasGradientAt_energy (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) a).hasFDerivAt.sub
    (hasGradientAt_potential k hH a).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt (action k H) _ a at h
  apply h.congr_fderiv
  ext b
  simp only [map_sub]

 theorem gradient_action (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : Coeff ι κ) : gradient (action k H) a =
      (2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)) a - project k (gradLoop k hH a) :=
  (hasGradientAt_action k hH a).gradient

 theorem potential_nonneg (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ∀ z, 0 ≤ H z)
    (a : Coeff ι κ) : 0 ≤ potential k H a := integral_nonneg (fun _ => hH _)

 theorem potential_upper_fourth (k : ι → ℕ) (hk : Function.Injective k)
    (hk0 : ∀ i, 0 < k i) {H : Vector κ → ℝ} (hH : Continuous H)
    {C : ℝ} (hC : 0 ≤ C) (hup : ∀ z, H z ≤ C*‖z‖^4) (a : Coeff ι κ) :
    potential (fun i => (k i : ℤ)) H a ≤
      C*(Fintype.card κ : ℝ)*(∑ p : ι × κ, (k p.1 : ℝ)*‖a p‖^2)^2 := by
  calc
    _ ≤ ∫ t : Time, C*‖loop (fun i => (k i : ℤ)) a t‖^4 ∂μ :=
      integral_mono (integrable_continuous (hH.comp (loop _ a).continuous))
        (integrable_continuous (continuous_const.mul ((loop _ a).continuous.norm.pow 4)))
        (fun t => hup _)
    _ = C*(∫ t : Time, ‖loop (fun i => (k i : ℤ)) a t‖^4 ∂μ) := integral_const_mul _ _
    _ ≤ _ := by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (integral_loop_norm_fourth_le k hk hk0 a) hC

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_8_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 theorem loop_zero (k : ι → ℤ) : loop k (0 : Coeff ι κ) = 0 := (loopCLM k).map_zero

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_9_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.GalerkinBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_10_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

 theorem energy_joinCoeff (w : (ι ⊕ ν) × κ → ℝ) (a : Coeff ι κ) (b : Coeff ν κ) :
    energy w (joinCoeff a b) = energy (fun p => w (Sum.inl p.1,p.2)) a +
      energy (fun p => w (Sum.inr p.1,p.2)) b := by
  simp only [energy, Fintype.sum_prod_type, Fintype.sum_sum_type,
    joinCoeff_inl, joinCoeff_inr]

 theorem loop_joinCoeff (k : ι → ℤ) (l : ν → ℤ) (a : Coeff ι κ) (b : Coeff ν κ) :
    loop (Sum.elim k l) (joinCoeff a b) = loop k a + loop l b := by
  ext t j
  simp only [ContinuousMap.add_apply, PiLp.add_apply, loop_coord, eval,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, joinCoeff_inl, joinCoeff_inr]

 theorem energy_scaled (k : ν → ℕ) (hk : ∀ i, 0 < k i) (b : Coeff ν κ) :
    energy (fun p => (k p.1 : ℝ))
      (diag (fun p => (Real.sqrt (k p.1 : ℝ))⁻¹) b) = ‖b‖^2 := by
  classical
  simp only [energy, EuclideanSpace.norm_sq_eq]
  apply sum_congr rfl
  intro p _
  have hp : 0 < (k p.1 : ℝ) := by exact_mod_cast hk p.1
  rw [diag_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, inv_pow, Real.sq_sqrt hp.le]
  field_simp

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_11_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

 theorem action_positive_lower (k : ι → ℤ) (l : ν → ℕ)
    (hl : Function.Injective l) (hl0 : ∀ i, 0 < l i)
    {H : Vector κ → ℝ} (hH : Continuous H) {C : ℝ} (hC : 0 ≤ C)
    (hup : ∀ z, H z ≤ C*‖z‖^4) (b : Coeff ν κ) :
    Real.pi*‖b‖^2-C*(Fintype.card κ : ℝ)*‖b‖^4 ≤
      action (Sum.elim k (fun i => (l i : ℤ))) H ((positiveScale l hl0).symm (0,b)) := by
  let v := diag (fun p : ν × κ => (Real.sqrt (l p.1 : ℝ))⁻¹) b
  have hkin : energy (fun p : (ι ⊕ ν) × κ =>
      Real.pi*((Sum.elim k (fun i => (l i : ℤ)) p.1 : ℤ) : ℝ)) (joinCoeff 0 v) = Real.pi*‖b‖^2 := by
    rw [energy_joinCoeff]
    simp only [Sum.elim_inl, Sum.elim_inr, Int.cast_natCast]
    have hz : energy (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) 0 = 0 := by simp [energy]
    rw [hz, zero_add, energy_mul, energy_scaled l hl0]
  have hp := potential_upper_fourth l hl hl0 hH hC hup v
  change _ ≤ C*(Fintype.card κ : ℝ)*(energy (fun p : ν × κ => (l p.1 : ℝ)) v)^2 at hp
  rw [energy_scaled l hl0] at hp
  have hlo : potential (Sum.elim k (fun i => (l i : ℤ))) H (joinCoeff 0 v) =
      potential (fun i => (l i : ℤ)) H v := by
    unfold potential
    rw [loop_joinCoeff, loop_zero, zero_add]
  change _ ≤ energy _ (joinCoeff 0 v)-potential _ H (joinCoeff 0 v)
  rw [hkin, hlo]
  nlinarith

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_12
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

omit [Fintype ι] [Fintype κ] in
 theorem mode_velocityCoeff (k : ι → ℤ) (a : Coeff ι κ) (i : ι) :
    mode (velocityCoeff k a) i = (2*(Real.pi : ℂ)*Complex.I*(k i : ℂ)) • mode a i := by
  ext j
  simp only [mode_apply, velocityCoeff, PiLp.smul_apply, diag_apply,
    RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  simp only [map_mul, map_intCast, map_ofNat]
  change Complex.I * ((2 : ℂ) * (((Real.pi : ℂ)*(k i : ℂ))*a (i,j))) =
    (2*(Real.pi : ℂ)*Complex.I*(k i : ℂ))*a (i,j)
  ring

 theorem hasDerivAt_loop (k : ι → ℤ) (a : Coeff ι κ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => loop k a (s : Time)) (loop k (velocityCoeff k a) (t : Time)) t := by
  have hs := HasDerivAt.fun_sum (u := univ) (fun i _ =>
    (hasDerivAt_fourier (1 : ℝ) (k i) t).smul_const (mode a i))
  change HasDerivAt (fun s : ℝ => loop k a (s : Time)) _ t at hs
  apply hs.congr_deriv
  simp only [loop_apply, mode_velocityCoeff, smul_smul, div_one, Complex.ofReal_one]
  apply sum_congr rfl
  intro i _
  congr 1
  ring

 theorem intervalIntegral_eq_average {E : Type u113} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Time → E) : (∫ t in (0:ℝ)..1, f (t : Time)) = ∫ t : Time, f t ∂μ := by
  rw [AddCircle.integral_haarAddCircle]
  simpa only [zero_add, inv_one, one_smul] using AddCircle.intervalIntegral_preimage (1 : ℝ) 0 f

 theorem contDiff_meanAction {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (meanAction hH) := by
  have hg : ContDiff ℝ ∞ (fun z : Vector κ => inner (𝕜 := ℝ) (gradient H z) z/2-H z) :=
    (((contDiff_gradient_function hH).inner ℝ contDiff_id).div_const 2).sub hH
  exact average.contDiff.comp (SmoothPaths.contDiff_superpose hg)

 theorem critical_action_eq (k : ι → ℤ) {H : Vector κ → ℝ}
    (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ) (ha : gradient (action k H) a = 0) :
    action k H a = meanAction hH (loop k a) := by
  have he : (2 : ℝ) • diag (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) a = project k (gradLoop k hH a) := by
    simpa only [gradient_action k hH, sub_eq_zero] using ha
  have hi := integral_inner_loop k (gradLoop k hH a) a
  rw [← he, real_inner_smul_left, ← energy_eq_inner] at hi
  have hgi : Integrable (fun t : Time => inner (𝕜 := ℝ) (gradient H (loop k a t)) (loop k a t)) μ :=
    integrable_continuous ((gradLoop k hH a).continuous.inner (loop k a).continuous)
  have hpi : Integrable (fun t : Time => H (loop k a t)) μ :=
    integrable_continuous (hH.continuous.comp (loop k a).continuous)
  unfold meanAction
  rw [integral_sub (hgi.div_const 2) hpi, integral_div]
  change action k H a = (∫ t : Time, inner (𝕜 := ℝ) (gradLoop k hH a t) (loop k a t) ∂μ)/2-potential k H a
  rw [hi]
  unfold action
  ring

end
end FourierPolynomial

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset
open scoped ComplexConjugate ContDiff
local instance instFactLtRealOfNat_solutions_13_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
open DiagonalQuadratic

 theorem linkRadius_pos {M : ℝ} (hM : 0 ≤ M) : 0 < linkRadius κ M := by
  unfold linkRadius
  apply Real.sqrt_pos.2
  exact div_pos Real.pi_pos (by positivity)

 theorem linkRadius_sq {M : ℝ} (hM : 0 ≤ M) :
    (linkRadius κ M)^2 = Real.pi/(2*(M*(Fintype.card κ : ℝ)+1)) :=
  Real.sq_sqrt (by positivity)

 theorem linkLevel_pos {M : ℝ} (hM : 0 ≤ M) : 0 < linkLevel κ M := by
  unfold linkLevel
  exact mul_pos (div_pos Real.pi_pos (by norm_num)) (sq_pos_of_pos (linkRadius_pos hM))

 theorem linkLevel_bound {M : ℝ} (hM : 0 ≤ M) :
    2*linkLevel κ M ≤ Real.pi*(linkRadius κ M)^2-
      M*(Fintype.card κ : ℝ)*(linkRadius κ M)^4 := by
  have hden : 0 < 2*(M*(Fintype.card κ : ℝ)+1) := by positivity
  have he : 2*(M*(Fintype.card κ : ℝ)+1)*(linkRadius κ M)^2 = Real.pi := by
    rw [linkRadius_sq hM]
    field_simp
  have hr : 0 ≤ (linkRadius κ M)^2 := sq_nonneg _
  have hm : M*(Fintype.card κ : ℝ)*(linkRadius κ M)^2 ≤ Real.pi/2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_right hm hr
  unfold linkLevel
  nlinarith

 theorem exists_link_epsilon {a : ℝ} (ha : 0 < a) :
    ∃ ε > 0, ∀ s : ℝ, 0 < s → s < ε → Real.pi*s^2 ≤ a/2 := by
  let ε := Real.sqrt (a/(2*Real.pi))
  have hε : 0 < ε := Real.sqrt_pos.2 (div_pos ha (by positivity))
  have hεsq : ε^2 = a/(2*Real.pi) := Real.sq_sqrt (by positivity)
  refine ⟨ε,hε,fun s hs hse => ?_⟩
  have hs2 : s^2 ≤ ε^2 := pow_le_pow_left₀ hs.le hse.le 2
  have hm := mul_le_mul_of_nonneg_left hs2 Real.pi_pos.le
  rw [hεsq] at hm
  have hid : Real.pi*(a/(2*Real.pi)) = a/2 := by field_simp
  rwa [hid] at hm

 theorem exists_link_far {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (C : ℝ) :
    ∃ R : ℝ, ρ < R ∧ ∀ u s : ℝ, 0 ≤ u → R ≤ max u |s| → C-η*(u^2+s^2) ≤ 0 := by
  let R := max (ρ+1) (max 1 ((|C|+1)/η))
  have hR : ρ < R := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hR1 : 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRc : (|C|+1)/η ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hReq : |C|+1 ≤ η*R := by
    have := (div_le_iff₀ hη).mp hRc
    linarith
  refine ⟨R,hR,fun u s _ hfar => ?_⟩
  have hsq : R^2 ≤ u^2+s^2 := by
    rcases le_max_iff.mp hfar with hy | hss
    · have := pow_le_pow_left₀ (by linarith : 0 ≤ R) hy 2
      nlinarith [sq_nonneg s]
    · have := pow_le_pow_left₀ (by linarith : 0 ≤ R) hss 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg u]
  have hh : R ≤ R^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left (hh.trans hsq) hη.le
  linarith [le_abs_self C]

end
end FourierPolynomial

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PeriodicFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace L2Paths
noncomputable section
open Set intervalIntegral
open MeasureTheory (volume)
open scoped Topology BoundedContinuousFunction
variable {E : Type u114} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem integral_sq_le (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, f t)^2 ≤ (b-a)*(∫ t in a..b, (f t)^2) := by
  rcases hab.eq_or_lt with he | hab
  · subst b
    simp
  let avg := ∫ t in a..b, f t
  let L := b-a
  have hL : 0 < L := sub_pos.mpr hab
  have hnon : 0 ≤ ∫ t in a..b, (L*f t-avg)^2 :=
    integral_nonneg_of_forall hab.le (fun _ => sq_nonneg _)
  have he (t : ℝ) : (L*f t-avg)^2 = L^2*(f t)^2-(2*L*avg)*f t+avg^2 := by ring
  simp_rw [he] at hnon
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_const] at hnon
  · simp only [smul_eq_mul] at hnon
    change 0 ≤ L^2*(∫ t in a..b, (f t)^2)-(2*L*avg)*avg+L*avg^2 at hnon
    change avg^2 ≤ L*(∫ t in a..b, (f t)^2)
    nlinarith
  · exact (hf.pow 2).intervalIntegrable _ _ |>.const_mul _
  · exact hf.intervalIntegrable _ _ |>.const_mul _
  · exact (((hf.pow 2).const_mul _).sub (hf.const_mul _)).intervalIntegrable _ _
  · exact intervalIntegrable_const

 theorem norm_sub_sq_le (x v : ℝ → E) (hv : Continuous v)
    (hd : ∀ t, HasDerivAt x (v t) t) {a b : ℝ} (hab : a ≤ b) :
    ‖x b-x a‖^2 ≤ (b-a)*(∫ t in a..b, ‖v t‖^2) := by
  have he := integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hv.intervalIntegrable a b)
  have hn : ‖x b-x a‖ ≤ ∫ t in a..b, ‖v t‖ := by
    rw [← he]
    exact norm_integral_le_integral_norm hab
  have hi := integral_sq_le (fun t => ‖v t‖) hv.norm hab
  have hs : ‖x b-x a‖^2 ≤ (∫ t in a..b, ‖v t‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact hs.trans hi

 theorem norm_sub_sq_le_global (x v : ℝ → E) (hv : Continuous v)
    (hd : ∀ t, HasDerivAt x (v t) t) {D : ℝ}
    (hD : (∫ t in (0:ℝ)..1, ‖v t‖^2) ≤ D^2)
    {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    ‖x b-x a‖^2 ≤ D^2*|b-a| := by
  wlog hab : a ≤ b generalizing a b
  · have h := this hb ha (le_of_not_ge hab)
    rwa [norm_sub_rev, abs_sub_comm] at h
  have hi := integral_mono_interval (μ := volume) ha.1 hab hb.2
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖v t‖)) ((hv.norm.pow 2).intervalIntegrable 0 1)
  have hc := norm_sub_sq_le x v hv hd hab
  have hm := mul_le_mul_of_nonneg_left (hi.trans hD) (sub_nonneg.mpr hab)
  rw [abs_of_nonneg (sub_nonneg.mpr hab)]
  exact hc.trans (by nlinarith)

 theorem norm_bound (x v : ℝ → E) (hv : Continuous v)
    (hd : ∀ t, HasDerivAt x (v t) t) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hxm : (∫ t in (0:ℝ)..1, ‖x t‖^2) ≤ A^2)
    (hvm : (∫ t in (0:ℝ)..1, ‖v t‖^2) ≤ D^2)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖x t‖ ≤ A+D := by
  have hx : Continuous x := continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)
  have hpoint (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖x t‖ ≤ ‖x s‖+D := by
    have hdiff := norm_sub_sq_le_global x v hv hd hvm hs ht
    have hab : |t-s| ≤ 1 := (abs_le).mpr ⟨by linarith [ht.1,hs.2], by linarith [ht.2,hs.1]⟩
    have hmul := mul_le_mul_of_nonneg_left hab (sq_nonneg D)
    have hn : ‖x t-x s‖ ≤ D := by nlinarith [norm_nonneg (x t-x s)]
    have htri := norm_sub_le (x t-x s) (-x s)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
    linarith
  have hi : ∫ s in (0:ℝ)..1, ‖x t‖ ≤ ∫ s in (0:ℝ)..1, ‖x s‖+D :=
    integral_mono_on (by norm_num) intervalIntegrable_const
      ((hx.norm.add continuous_const).intervalIntegrable _ _) hpoint
  rw [integral_const, integral_add (hx.norm.intervalIntegrable _ _) intervalIntegrable_const,
    integral_const] at hi
  simp only [sub_zero, one_smul] at hi
  have hcs := integral_sq_le (fun s => ‖x s‖) hx.norm (show (0:ℝ) ≤ 1 by norm_num)
  simp only [sub_zero, one_mul] at hcs
  have hmean : ∫ t_1 in (0:ℝ)..1, ‖x t_1‖ ≤ A := by
    nlinarith [integral_nonneg_of_forall (μ := volume) (show (0:ℝ) ≤ 1 by norm_num) (fun s => norm_nonneg (x s))]
  linarith

omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem exists_subsequence [ProperSpace E] (u : ℕ → C(Segment,E)) {D R : ℝ}
    (hmod : ∀ n (t s : Segment), dist (u n t) (u n s)^2 ≤ D^2*dist t s)
    (hbound : ∀ n (t : Segment), ‖u n t‖ ≤ R) :
    ∃ x : C(Segment,E), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 x) := by
  let eqv := ContinuousMap.isometryEquivBoundedOfCompact Segment E
  let v : ℕ → (Segment →ᵇ E) := fun n => eqv (u n)
  have heq : Equicontinuous ((↑) : Set.range v → Segment → E) := by
    apply UniformEquicontinuous.equicontinuous
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    refine ⟨ε^2/(D^2+1), by positivity, fun t s hts f => ?_⟩
    rcases f.property with ⟨n,hn⟩
    have hm := hmod n t s
    have hd : (D^2+1)*dist t s < ε^2 := by
      have := (lt_div_iff₀ (by positivity : 0 < D^2+1)).mp hts
      linarith
    rw [← hn]
    change dist (u n t) (u n s) < ε
    nlinarith [(dist_nonneg : 0 ≤ dist (u n t) (u n s)), (dist_nonneg : 0 ≤ dist t s)]
  have hc : IsCompact (closure (Set.range v)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:E) R)
      (isCompact_closedBall _ _) (Set.range v)
      (fun f t hf => by
        rcases hf with ⟨n,rfl⟩
        change dist (u n t) (0:E) ≤ R
        simpa only [dist_zero_right] using hbound n t) heq
  obtain ⟨x,hx,φ,hφ,ht⟩ := hc.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨eqv.symm x,φ,hφ,?_⟩
  exact eqv.symm.continuous.continuousAt.tendsto.comp ht

attribute [local instance] OAI.L2Paths.instFactLtRealOfNat_solutions
omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem restriction_isometry : Isometry (restriction (E := E)) := by
  rw [isometry_iff_dist_eq]
  intro x y
  apply le_antisymm
  · apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist x y)).2
    intro t
    exact ContinuousMap.dist_apply_le_dist (t.val : Time)
  · apply (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist (restriction x) (restriction y))).2
    intro t
    let r := AddCircle.equivIoc (1 : ℝ) 0 t
    have hr : r.val ∈ Set.Icc (0:ℝ) 1 := ⟨r.property.1.le, by simpa using r.property.2⟩
    have h := ContinuousMap.dist_apply_le_dist (f := restriction x) (g := restriction y) ⟨r.val,hr⟩
    simpa only [restriction, ContinuousMap.coe_mk, r, AddCircle.coe_equivIoc] using h

omit [NormedSpace ℝ E] in
 theorem exists_periodic_subsequence [ProperSpace E] (u : ℕ → C(Time,E)) {D R : ℝ}
    (hmod : ∀ n (t s : Segment), dist (u n (t.val : Time)) (u n (s.val : Time))^2 ≤ D^2*dist t s)
    (hbound : ∀ n (t : Segment), ‖u n (t.val : Time)‖ ≤ R) :
    ∃ x : C(Time,E), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (u ∘ φ) Filter.atTop (𝓝 x) := by
  obtain ⟨x,φ,hφ,ht⟩ := exists_subsequence (fun n => restriction (u n)) hmod hbound
  have hc' : Cauchy (Filter.map restriction (Filter.map (u ∘ φ) Filter.atTop)) := by
    rw [Filter.map_map]
    exact ht.cauchySeq
  have hc : CauchySeq (u ∘ φ) :=
    restriction_isometry.isUniformInducing.cauchy_map_iff.mp hc'
  obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨y,φ,hφ,hy⟩

end
end L2Paths

namespace PeriodicFourier
noncomputable section
open MeasureTheory AddCircle Finset Set
open scoped ComplexConjugate Topology
open FourierPolynomial (integrable_continuous)

 attribute [local instance] OAI.PeriodicFourier.instFactLtRealOfNat_solutions
theorem coefficient_ext {f g : C(Time,ℂ)} (h : ∀ n, coefficient n f = coefficient n g) : f = g := by
  have hz (n : ℤ) : fourierCoeff (f-g) n = 0 := by
    change coefficient n (f-g) = 0
    rw [map_sub, h, sub_self]
  have hs : Summable (fourierCoeff (f-g)) := by
    simpa only [funext hz] using (summable_zero : Summable (fun _ : ℤ => (0:ℂ)))
  have hh := hasSum_fourier_series_of_summable hs
  simp only [hz, zero_smul] at hh
  have he : f-g = 0 := hh.unique hasSum_zero
  exact sub_eq_zero.mp he

 theorem coefficient_const (n : ℤ) (c : ℂ) :
    coefficient n (ContinuousMap.const Time c) = if n = 0 then c else 0 := by
  rw [coefficient_apply, fourierCoeff]
  simp only [ContinuousMap.coe_const, Function.const_apply, smul_eq_mul]
  rw [integral_mul_const, FourierPolynomial.integral_fourier]
  simp only [neg_eq_zero]
  split_ifs <;> simp

 theorem constant_of_nonzero_coeff {f : C(Time,ℂ)}
    (h : ∀ n : ℤ, n ≠ 0 → coefficient n f = 0) :
    f = ContinuousMap.const Time (coefficient 0 f) := by
  apply coefficient_ext
  intro n
  rw [coefficient_const]
  by_cases hn : n = 0
  · subst n; simp
  · simp [hn,h n hn]

 theorem coefficient_eq_on (f : C(Time,ℂ)) (n : ℤ) :
    fourierCoeffOn (show (0:ℝ) < 1 by norm_num) (fun t : ℝ => f (t : Time)) n = coefficient n f := by
  rw [fourierCoeffOn_eq_integral, coefficient_apply, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp

 theorem derivative_coefficient (v : C(Time,ℂ)) (hzero : coefficient 0 v = 0)
    {n : ℤ} (hn : n ≠ 0) :
    (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)) * coefficient n (periodicPrimitive v hzero) = coefficient n v := by
  have hp := periodic_primitive v hzero
  have hi := fourierCoeffOn_of_hasDerivAt (show (0:ℝ) < 1 by norm_num) hn
    (fun t _ => hasDerivAt_primitive v t)
    ((v.continuous.comp continuous_quot_mk).intervalIntegrable 0 1)
  have ht : primitive v 1 = primitive v 0 := by simpa using hp 0
  simp only [ht, sub_self, mul_zero, Complex.ofReal_one, Complex.ofReal_zero, sub_zero, one_mul, zero_sub] at hi
  change fourierCoeffOn _ (fun t : ℝ => periodicPrimitive v hzero (t : Time)) n =
    1 / (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * -fourierCoeffOn _ (fun t : ℝ => v (t : Time)) n at hi
  rw [coefficient_eq_on, coefficient_eq_on] at hi
  rw [hi]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp

 theorem hasDerivAt_of_coefficients (x v : C(Time,ℂ))
    (h : ∀ n : ℤ, coefficient n v = (2*(Real.pi : ℂ)*Complex.I*(n : ℂ))*coefficient n x)
    (t : ℝ) : HasDerivAt (fun s : ℝ => x (s : Time)) (v (t : Time)) t := by
  have hz : coefficient 0 v = 0 := by simpa using h 0
  let y := periodicPrimitive v hz
  have hc : x-y = ContinuousMap.const Time (coefficient 0 (x-y)) := by
    apply constant_of_nonzero_coeff
    intro n hn
    rw [map_sub]
    have he := derivative_coefficient v hz hn
    rw [h n] at he
    have hn' : (2*(Real.pi : ℂ)*Complex.I*(n : ℂ)) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
      exact_mod_cast hn
    have heq := (mul_left_cancel₀ hn') he
    change coefficient n x-coefficient n (periodicPrimitive v hz) = 0
    exact sub_eq_zero.mpr heq.symm
  have hx (s : ℝ) : x (s : Time) = primitive v s+coefficient 0 (x-y) := by
    have he := congrArg (fun f : C(Time,ℂ) => f (s : Time)) hc
    change x (s : Time)-primitive v s = coefficient 0 (x-y) at he
    exact sub_eq_iff_eq_add'.mp he
  simpa only [← hx] using (hasDerivAt_primitive v t).add_const (coefficient 0 (x-y))

end
end PeriodicFourier

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PeriodicSolutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section NonsqueezingInline

namespace FourierPolynomial
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
attribute [local instance] OAI.FourierPolynomial.instFactLtRealOfNat_solutions_14
variable {ι κ : Type} [Fintype ι] [Fintype κ]
open DiagonalQuadratic

 theorem contDiff_gradPath {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (gradPath hH) :=
   SmoothPaths.contDiff_superpose (contDiff_gradient_function hH)

 theorem critical_coefficient (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (a : Coeff ι κ)
    (ha : gradient (action k H) a = 0) (i : ι) (j : κ) :
    PeriodicFourier.coefficient (k i) (coordPath j (gradPath hH (loop k a))) =
      (2*(Real.pi : ℂ)*(k i : ℂ))*PeriodicFourier.coefficient (k i) (coordPath j (loop k a)) := by
  have he : (2 : ℝ) • diag (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) a = project k (gradLoop k hH a) := by
    simpa only [gradient_action k hH, sub_eq_zero] using ha
  change project k (gradLoop k hH a) (i,j) = (2*(Real.pi : ℂ)*(k i : ℂ))*project k (loop k a) (i,j)
  rw [project_loop k hk, ← he]
  simp only [PiLp.smul_apply, diag_apply, RCLike.real_smul_eq_coe_mul, map_mul, map_intCast, map_ofNat]
  change (2:ℂ)*((Real.pi : ℂ)*(k i : ℂ)*a (i,j)) = (2*(Real.pi : ℂ)*(k i : ℂ))*a (i,j)
  ring

 theorem limit_coefficient {α : ℕ → Type} [∀ n, Fintype (α n)]
    (k : (n : ℕ) → α n → ℤ) (hk : ∀ n, Function.Injective (k n))
    (hex : ∀ m : ℤ, ∀ᶠ n in atTop, m ∈ Set.range (k n))
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : (n : ℕ) → Coeff (α n) κ) (ha : ∀ n, gradient (action (k n) H) (a n) = 0)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (x : C(Time,Vector κ))
    (ht : Tendsto (fun n => loop (k (φ n)) (a (φ n))) atTop (𝓝 x)) (m : ℤ) (j : κ) :
    PeriodicFourier.coefficient m (coordPath j (gradPath hH x)) =
      (2*(Real.pi : ℂ)*(m : ℂ))*PeriodicFourier.coefficient m (coordPath j x) := by
  have hg := (contDiff_gradPath hH).continuous.continuousAt.tendsto.comp ht
  have hc := (PeriodicFourier.coefficient m).continuous.comp (coordPath j).continuous
  have hleft := hc.continuousAt.tendsto.comp hg
  have hright := (tendsto_const_nhds (x := (2*(Real.pi : ℂ)*(m : ℂ)))).mul
    (hc.continuousAt.tendsto.comp ht)
  apply tendsto_nhds_unique_of_eventuallyEq hleft hright
  filter_upwards [hφ.tendsto_atTop.eventually (hex m)] with n hn
  rcases hn with ⟨i,rfl⟩
  exact critical_coefficient (k (φ n)) (hk (φ n)) hH (a (φ n)) (ha (φ n)) i j

 theorem hasDerivAt_of_critical_coefficients {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (x : C(Time,Vector κ))
    (h : ∀ m j, PeriodicFourier.coefficient m (coordPath j (gradPath hH x)) =
      (2*(Real.pi : ℂ)*(m : ℂ))*PeriodicFourier.coefficient m (coordPath j x)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x (s : Time)) (Complex.I • gradient H (x (t : Time))) t := by
  have hj (j : κ) : HasDerivAt (fun s : ℝ => x (s : Time) j)
      (Complex.I • gradient H (x (t : Time)) j) t := by
    have hc (m : ℤ) : PeriodicFourier.coefficient m (Complex.I • coordPath j (gradPath hH x)) =
        (2*(Real.pi : ℂ)*Complex.I*(m : ℂ))*PeriodicFourier.coefficient m (coordPath j x) := by
      rw [map_smul, h]
      simp only [smul_eq_mul]
      ring
    exact PeriodicFourier.hasDerivAt_of_coefficients (coordPath j x)
      (Complex.I • coordPath j (gradPath hH x)) hc t
  have hp := hasDerivAt_pi.mpr hj
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.hasFDerivAt.comp_hasDerivAt t hp

 theorem positive_action_limit {α : ℕ → Type} [∀ n, Fintype (α n)]
    (k : (n : ℕ) → α n → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : (n : ℕ) → Coeff (α n) κ) (ha : ∀ n, gradient (action (k n) H) (a n) = 0)
    {L : ℝ} (hL : ∀ n, L ≤ action (k n) H (a n))
    (φ : ℕ → ℕ) (x : C(Time,Vector κ))
    (ht : Tendsto (fun n => loop (k (φ n)) (a (φ n))) atTop (𝓝 x)) :
    L ≤ meanAction hH x := by
  apply ge_of_tendsto' ((contDiff_meanAction hH).continuous.continuousAt.tendsto.comp ht)
  intro n
  change L ≤ meanAction hH (loop (k (φ n)) (a (φ n)))
  rw [← critical_action_eq _ hH _ (ha (φ n))]
  exact hL (φ n)

end
end FourierPolynomial

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
open DiagonalQuadratic FourierPolynomial

 local instance instFactLtRealOfNat_solutions_rc74a79_1 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
theorem negativeMode_nonpos (N : ℕ) (i : Fin (N+1)) : negativeMode N i ≤ 0 := by
  simp [negativeMode]

 theorem positiveMode_pos (N : ℕ) (i : Fin (N+1)) : 0 < positiveMode N i := Nat.succ_pos _

 theorem positiveMode_injective (N : ℕ) : Function.Injective (positiveMode N) := by
  intro i j hij
  apply Fin.ext
  simpa [positiveMode] using hij

 theorem frequency_injective (N : ℕ) : Function.Injective (frequency N) := by
  intro i j hij
  cases i <;> cases j
  · simp only [frequency, Sum.elim_inl, negativeMode, neg_inj, Nat.cast_inj] at hij
    exact congrArg Sum.inl (Fin.ext hij)
  · simp only [frequency, Sum.elim_inl, Sum.elim_inr, negativeMode, positiveMode, Nat.cast_add, Nat.cast_one] at hij
    omega
  · simp only [frequency, Sum.elim_inl, Sum.elim_inr, negativeMode, positiveMode, Nat.cast_add, Nat.cast_one] at hij
    omega
  · simp only [frequency, Sum.elim_inr, Nat.cast_inj] at hij
    exact congrArg Sum.inr (positiveMode_injective N hij)

 theorem frequency_exhausts (m : ℤ) : ∀ᶠ N in atTop, m ∈ Set.range (frequency N) := by
  cases m with
  | ofNat m =>
    cases m with
    | zero =>
      filter_upwards [] with N
      exact ⟨Sum.inl ⟨0,Nat.succ_pos N⟩, by simp [frequency,negativeMode]⟩
    | succ m =>
      filter_upwards [eventually_ge_atTop m] with N hN
      exact ⟨Sum.inr ⟨m,by omega⟩, by simp [frequency,positiveMode]⟩
  | negSucc m =>
    filter_upwards [eventually_ge_atTop (m+1)] with N hN
    exact ⟨Sum.inl ⟨m+1,by omega⟩, by simp [frequency,negativeMode,Int.negSucc_eq]⟩

 variable {κ : Type} [Fintype κ] [DecidableEq κ]

end
end HamiltonianPeriodic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HamiltonianODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace HamiltonianODE
noncomputable section
open MeasureTheory AddCircle Finset Set Filter
open scoped ComplexConjugate ContDiff Topology
open FourierPolynomial DiagonalQuadratic
local instance instFactLtRealOfNat_solutions_rc74a79_2 : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {κ : Type u116} [Fintype κ]

end
end HamiltonianODE

namespace HamiltonianODE
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic
variable {κ : Type u118} [Fintype κ]

end
end HamiltonianODE

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HamiltonianGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace HamiltonianGrowth
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE
variable {κ : Type u119} [Fintype κ]

 theorem quartic_bound {H : Vector κ → ℝ} {A B r : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 < r)
    (hz : ∀ z, ‖z‖ < r → H z = 0) (hu : ∀ z, H z ≤ A*‖z‖^2+B*‖z‖) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, H z ≤ M*‖z‖^4 := by
   refine ⟨A/r^2+B/r^3, by positivity, ?_⟩
   intro z
   by_cases hzr : ‖z‖ < r
   · rw [hz z hzr]; positivity
   have hnr : r ≤ ‖z‖ := le_of_not_gt hzr
   have h2 : r^2*‖z‖^2 ≤ ‖z‖^4 := by
     have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hnr 2) (sq_nonneg ‖z‖)
     nlinarith only [this]
   have h3 : r^3*‖z‖ ≤ ‖z‖^4 := by
     have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hnr 3) (norm_nonneg z)
     nlinarith only [this]
   have ha : A*‖z‖^2 ≤ (A/r^2)*‖z‖^4 := by
     rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr 2)]
     nlinarith only [mul_le_mul_of_nonneg_left h2 hA]
   have hb : B*‖z‖ ≤ (B/r^3)*‖z‖^4 := by
     rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr 3)]
     nlinarith only [mul_le_mul_of_nonneg_left h3 hB]
   calc
     H z ≤ A*‖z‖^2+B*‖z‖ := hu z
     _ ≤ (A/r^2+B/r^3)*‖z‖^4 := by nlinarith only [ha,hb]

end
end HamiltonianGrowth

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth
variable {κ : Type u120} [Fintype κ]

end
end HamiltonianPeriodic

namespace HamiltonianPeriodic
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth
variable {κ : Type} [Fintype κ] [DecidableEq κ]

end
end HamiltonianPeriodic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.EmbeddingInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace EmbeddingInverse
noncomputable section
open Set Filter
open scoped ContDiff Topology
variable {E : Type u121} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end
end EmbeddingInverse

namespace ComplexSymplectic
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial HamiltonianODE
variable {κ : Type u122} [Fintype κ]

end
end ComplexSymplectic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.SmoothProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section NonsqueezingInline

namespace SmoothProfiles
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

end
end SmoothProfiles

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.ExteriorHamiltonian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace PushedBall
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial HamiltonianODE SmoothProfiles EmbeddingInverse
variable {κ : Type u123} [Fintype κ]

end
end PushedBall

namespace ExteriorHamiltonian
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE HamiltonianGrowth SmoothProfiles
variable {κ : Type u124} [Fintype κ]

end
end ExteriorHamiltonian

namespace ExteriorHamiltonian
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles HamiltonianPeriodic
variable {κ : Type u125} [Fintype κ]

end
end ExteriorHamiltonian

namespace PushedBall
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles ExteriorHamiltonian
variable {κ : Type u126} [Fintype κ]

end
end PushedBall

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.Nonsqueezing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section NonsqueezingInline

namespace CylinderParameters
noncomputable section
open Set Filter Finset
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE
variable {κ : Type u127} [Fintype κ] [DecidableEq κ]

end
end CylinderParameters

namespace CylinderNonsqueezing
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial DiagonalQuadratic HamiltonianODE SmoothProfiles HamiltonianPeriodic
open ExteriorHamiltonian PushedBall CylinderParameters
variable {κ : Type} [Fintype κ] [DecidableEq κ]

end
end CylinderNonsqueezing
end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.UpperBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace CylinderNonsqueezing
noncomputable section
open Set
open scoped ContDiff
open FourierPolynomial
variable {κ : Type} [Fintype κ] [DecidableEq κ]

end
end CylinderNonsqueezing
end

end OAI
end
end

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

/-! ## Helpers -/

/-! ### Absolutely continuous loops -/

/-! ### Support functions -/

/-! ### Translation -/

/-! ### Scaling -/

/-! ### Positivity of the action -/

end Viterbo.CM
end

section
set_option autoImplicit false

open scoped ENNReal ContDiff Pointwise

namespace Viterbo.Capacities

open OAI.SymmetricPolar Set Topology

/-! ## Generic facts about symplectic embeddings -/

/-! ## The bridge `ℝ²ⁿ ≅ ℂⁿ`, `(q, p) ↦ q + i p` -/


/-! ## Non-squeezing in phase-space form -/

/-! ## The two capacities -/

end Viterbo.Capacities
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {H : Type} {E : Type} {F : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-!
# Blueprint: `c_EHZ` extends to a symplectic capacity (HKO p. 2)

Target: `Viterbo.exists_isSymplecticCapacity_eq_cEHZ_and_exists_action_eq_cEHZ`.

Route (see `proofs/capacity/BRIEF.md` in the mission repo):
* the capacity is the envelope `c(U) = ⨆ {cEHZ K : K convex domain, K ↪ U}`;
* everything reduces to (A) `cEHZ_le_of_hse`: `K ↪ L` between convex domains gives
  `cEHZ K ≤ cEHZ L`, proved by a Hofer–Zehnder argument on OpenAI's Galerkin engine
  (`OAI.FourierPolynomial`, `OAI.HamiltonianPeriodic`), with
  - linking along a trigonometric approximation of a minimal characteristic of `L` (Parts W, C),
  - compactness from the identity `Φ = ∫ (⟨∇H x, x⟩/2 - H x)` and a homogeneous limit (Parts E1, E2a),
  - mollified gauges for smoothness (Part M) and slow profiles on `K` (Part K).
-/
/-! ## Shared definitions -/
/-! ## Part E1: the linking lemma under a Cerami condition (finite dimension) -/

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ] [DecidableEq κ]
/-! ## Parts E2a, E2b: the Galerkin engine -/

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartE2b
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic OAI.DiagonalQuadratic
local instance instFactOneE2b : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩

end Viterbo.Cap.PartE2b
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartE2b
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic OAI.DiagonalQuadratic
variable {ι κ : Type} [Fintype ι] [Fintype κ]
/-- Copied from Part E2a. -/
theorem norm_project_gradLoop_le (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) {C : ℝ}
    (hgrow : ∀ z, ‖gradient H z‖ ≤ C * (1 + ‖z‖)) (a : Coeff ι κ) :
    ‖project k (gradLoop k hH a)‖ ≤ 2 * C * (1 + ‖a‖) := by
  have hC : 0 ≤ C := by
    have h := hgrow 0
    simp only [norm_zero, add_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  have hb := project_bessel k hk (gradLoop k hH a)
  have hpt : ∀ t : Time, ‖gradLoop k hH a t‖ ^ 2 ≤ 2 * C ^ 2 * (1 + ‖loop k a t‖ ^ 2) := by
    intro t
    have h1 := hgrow (loop k a t)
    have h2 : ‖gradLoop k hH a t‖ ≤ C * (1 + ‖loop k a t‖) := h1
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [sq_nonneg (1 - ‖loop k a t‖), sq_nonneg C]
  have hint : (∫ t : Time, ‖gradLoop k hH a t‖ ^ 2 ∂μ) ≤ 2 * C ^ 2 * (1 + ‖a‖ ^ 2) := by
    calc
      _ ≤ ∫ t : Time, 2 * C ^ 2 * (1 + ‖loop k a t‖ ^ 2) ∂μ :=
        integral_mono (integrable_continuous ((gradLoop k hH a).continuous.norm.pow 2))
          (integrable_continuous (continuous_const.mul
            (continuous_const.add ((loop k a).continuous.norm.pow 2)))) hpt
      _ = 2 * C ^ 2 * (1 + ‖a‖ ^ 2) := by
        rw [integral_const_mul, integral_add (integrable_const _)
          (integrable_continuous (f := fun t : Time => ‖loop k a t‖ ^ 2)
            ((loop k a).continuous.norm.pow 2))]
        rw [integral_loop_norm_sq k hk]
        simp
  have hsq : ‖project k (gradLoop k hH a)‖ ^ 2 ≤ (2 * C * (1 + ‖a‖)) ^ 2 := by
    nlinarith [sq_nonneg (1 - ‖a‖), sq_nonneg C, norm_nonneg a]
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

/-- Copied from Part E2a. -/
theorem norm_velocityCoeff_le (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : Coeff ι κ) :
    ‖velocityCoeff k a‖ ≤ ‖gradient (FourierPolynomial.action k H) a‖ + ‖project k (gradLoop k hH a)‖ := by
  have he : (2 : ℝ) • diag (fun p => Real.pi * (k p.1 : ℝ)) a =
      gradient (FourierPolynomial.action k H) a + project k (gradLoop k hH a) := by
    rw [gradient_action k hH]; abel
  simp only [velocityCoeff, he, norm_smul, Complex.norm_I, one_mul]
  exact norm_add_le _ _

/-- Copied from Part E2a. -/
theorem loop_modulus (k : ι → ℤ) (hk : Function.Injective k) (b : Coeff ι κ) {D : ℝ}
    (hv : ‖velocityCoeff k b‖ ≤ D) (t s : L2Paths.Segment) :
    dist (loop k b (t.val : Time)) (loop k b (s.val : Time)) ^ 2 ≤ D ^ 2 * dist t s := by
  have hb : (∫ t in (0:ℝ)..1, ‖loop k (velocityCoeff k b) (t : Time)‖ ^ 2) ≤ D ^ 2 := by
    rw [intervalIntegral_eq_average (fun t : Time => ‖loop k (velocityCoeff k b) t‖ ^ 2),
      integral_loop_norm_sq k hk]
    exact pow_le_pow_left₀ (norm_nonneg _) hv 2
  have h := L2Paths.norm_sub_sq_le_global
    (fun t : ℝ => loop k b (t : Time)) (fun t : ℝ => loop k (velocityCoeff k b) (t : Time))
    ((loop k (velocityCoeff k b)).continuous.comp continuous_quot_mk)
    (hasDerivAt_loop k b) hb s.property t.property
  simpa only [dist_eq_norm, Subtype.dist_eq, Real.dist_eq, Real.norm_eq_abs] using h

/-- Part E2a's `loop_bound`, with `‖b‖ ≤ A`. -/
theorem loop_bound' (k : ι → ℤ) (hk : Function.Injective k) (b : Coeff ι κ) {A D : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hb1 : ‖b‖ ≤ A) (hv : ‖velocityCoeff k b‖ ≤ D)
    (t : L2Paths.Segment) :
    ‖loop k b (t.val : Time)‖ ≤ A + D := by
  have hx : (∫ t in (0:ℝ)..1, ‖loop k b (t : Time)‖ ^ 2) ≤ A ^ 2 := by
    rw [intervalIntegral_eq_average (fun t : Time => ‖loop k b t‖ ^ 2),
      integral_loop_norm_sq k hk]
    exact pow_le_pow_left₀ (norm_nonneg _) hb1 2
  have hvv : (∫ t in (0:ℝ)..1, ‖loop k (velocityCoeff k b) (t : Time)‖ ^ 2) ≤ D ^ 2 := by
    rw [intervalIntegral_eq_average (fun t : Time => ‖loop k (velocityCoeff k b) t‖ ^ 2),
      integral_loop_norm_sq k hk]
    exact pow_le_pow_left₀ (norm_nonneg _) hv 2
  exact L2Paths.norm_bound
    (fun t : ℝ => loop k b (t : Time)) (fun t : ℝ => loop k (velocityCoeff k b) (t : Time))
    ((loop k (velocityCoeff k b)).continuous.comp continuous_quot_mk)
    (hasDerivAt_loop k b) hA hD hx hvv t.property

/-- A Hamiltonian vanishing near `0` with linearly growing gradient is `O(‖z‖⁴)`. -/
theorem quartic_of_flat {H : Vector κ → ℝ} {C : ℝ} (hH : ContDiff ℝ ∞ H)
    (hgrow : ∀ z, ‖gradient H z‖ ≤ C * (1 + ‖z‖))
    (hflat : ∀ᶠ z in 𝓝 (0 : Vector κ), H z = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, H z ≤ M * ‖z‖ ^ 4 := by
  have hC : 0 ≤ C := by
    have h := hgrow 0
    simp only [norm_zero, add_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  have h0 := hflat.self_of_nhds
  obtain ⟨r, hr, hzr⟩ := Metric.eventually_nhds_iff.mp hflat
  have hu (z : Vector κ) : H z ≤ C * ‖z‖ ^ 2 + C * ‖z‖ := by
    have hd : ∀ w ∈ Metric.closedBall (0 : Vector κ) ‖z‖, DifferentiableAt ℝ H w :=
      fun w _ => hH.differentiable (by simp) w
    have hb : ∀ w ∈ Metric.closedBall (0 : Vector κ) ‖z‖, ‖fderiv ℝ H w‖ ≤ C * (1 + ‖z‖) := by
      intro w hw
      have he : ‖fderiv ℝ H w‖ = ‖gradient H w‖ := by simp [gradient]
      rw [he]
      refine (hgrow w).trans ?_
      have : ‖w‖ ≤ ‖z‖ := by simpa using hw
      gcongr
    have hm := (convex_closedBall (0 : Vector κ) ‖z‖).norm_image_sub_le_of_norm_fderiv_le hd hb
      (Metric.mem_closedBall_self (norm_nonneg z)) (by simp : z ∈ Metric.closedBall (0 : Vector κ) ‖z‖)
    rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at hm
    nlinarith [le_abs_self (H z)]
  exact HamiltonianGrowth.quartic_bound hC hC hr
    (fun z hz => hzr (by simpa only [dist_zero_right] using hz)) hu

end Viterbo.Cap.PartE2b
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartE2b
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic OAI.DiagonalQuadratic
variable {κ : Type} [Fintype κ]
/-- The `F`-component of the cone direction. -/
def coneVec (N : ℕ) (p : Coeff (Fin (N + 1)) κ) : Coeff (Fin (N + 1)) κ :=
  diag (fun q : Fin (N + 1) × κ => Real.sqrt (positiveMode N q.1 : ℝ)) p

theorem positiveScale_joinCoeff (N : ℕ) (y p : Coeff (Fin (N + 1)) κ) (t : ℝ) :
    (positiveScale (ι := Fin (N + 1)) (positiveMode N) (positiveMode_pos N))
      (joinCoeff y (t • p)) = (y, t • coneVec N p) := by
  ext q
  · rfl
  · simp [positiveScale, splitEquiv, coneVec, diag_apply]
    ring

theorem positiveScale_symm_cone (N : ℕ) (y p : Coeff (Fin (N + 1)) κ) (t : ℝ) :
    (positiveScale (ι := Fin (N + 1)) (positiveMode N) (positiveMode_pos N)).symm
      (y, t • coneVec N p) = joinCoeff y (t • p) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  exact (positiveScale_joinCoeff N y p t).symm

theorem energy_pos_eq (N : ℕ) (p : Coeff (Fin (N + 1)) κ) :
    energy (fun q : Fin (N + 1) × κ => Real.pi * (positiveMode N q.1 : ℝ)) p =
      Real.pi * ‖coneVec N p‖ ^ 2 := by
  rw [energy_mul (fun q : Fin (N + 1) × κ => (positiveMode N q.1 : ℝ))]
  congr 1
  simp only [energy, EuclideanSpace.norm_sq_eq, coneVec, diag_apply, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem action_cone_le {H : Vector κ → ℝ} (hH0 : ∀ z, 0 ≤ H z) (N : ℕ)
    (y p : Coeff (Fin (N + 1)) κ) (t : ℝ) :
    FourierPolynomial.action (frequency N) H (joinCoeff y (t • p)) ≤
      t ^ 2 * (Real.pi * ‖coneVec N p‖ ^ 2) := by
  have hn := energy_nonpos (fun q : Fin (N + 1) × κ => Real.pi * (negativeMode N q.1 : ℝ))
    (fun q => mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le
      (by exact_mod_cast negativeMode_nonpos N q.1)) y
  have hp := potential_nonneg (Sum.elim (negativeMode N) fun i => (positiveMode N i : ℤ)) hH0
    (joinCoeff y (t • p))
  unfold FourierPolynomial.action
  rw [energy_joinCoeff]
  simp only [frequency, Sum.elim_inl, Sum.elim_inr, Int.cast_natCast, energy_smul]
  rw [energy_pos_eq]
  linarith

end Viterbo.Cap.PartE2b
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap.PartE2b
open Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic OAI.DiagonalQuadratic
variable {κ : Type} [Fintype κ] [DecidableEq κ]
theorem engine {H : Vector κ → ℝ} {V : Vector κ → Vector κ} {C R γ₀ : ℝ}
    (hE : EngineHyp H V C R γ₀) (hH0 : ∀ z, 0 ≤ H z)
    (hflat : ∀ᶠ z in 𝓝 (0 : Vector κ), H z = 0) (hcone : ConeHyp H) :
    ∃ x : ℝ → Vector κ, x 1 = x 0 ∧ 0 < actionIntegral H x ∧
      ∀ t, HasDerivAt x (Complex.I • gradient H (x t)) t := by
  obtain ⟨b, D, C₀, c, hc, ⟨m₀, hm₀⟩, hbD, hb0, hcone⟩ := hcone
  have hH := hE.smooth
  have hC : 0 ≤ C := by
    have h := hE.grow 0
    simp only [norm_zero, add_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  obtain ⟨M, hM, hup⟩ := quartic_of_flat hH hE.grow hflat
  have ha : 0 < linkLevel κ M := linkLevel_pos hM
  have hρ : 0 < linkRadius κ M := linkRadius_pos hM
  obtain ⟨ε, hε, hnear⟩ := exists_link_epsilon ha
  obtain ⟨N₀, R₁, c₁, hc₁, hcer⟩ := galerkin_cerami hE ha
  have hm0 : m₀ ≠ 0 := fun h => hm₀ (h ▸ hb0)
  have hmD : m₀ ≤ D := by
    by_contra h
    exact hm₀ (hbD m₀ (by omega))
  obtain ⟨j, hj⟩ : ∃ j, b m₀ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hm₀ (by ext j; simp [h])
  set N₁ := max N₀ D with hN₁
  -- critical points of the Galerkin functionals
  have hcrit : ∀ N, N₁ ≤ N → ∃ x : Coeff (Fin (N + 1) ⊕ Fin (N + 1)) κ,
      linkLevel κ M ≤ FourierPolynomial.action (frequency N) H x ∧
      gradient (FourierPolynomial.action (frequency N) H) x = 0 := by
    intro N hN
    have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
    have hND : D ≤ N := le_trans (le_max_right _ _) hN
    set p := posCoeff b N with hp
    set w := coneVec N p with hw_def
    have hw : w ≠ 0 := by
      intro h
      have hq := congrArg (fun v : Coeff (Fin (N + 1)) κ => v (⟨m₀ - 1, by omega⟩, j)) h
      have hval : w (⟨m₀ - 1, by omega⟩, j) =
          (Real.sqrt (positiveMode N ⟨m₀ - 1, by omega⟩ : ℝ)) • b (m₀ - 1 + 1) j := rfl
      simp only at hq
      rw [hval, Nat.sub_add_cancel (by omega), PiLp.zero_apply, smul_eq_zero] at hq
      rcases hq with hq | hq
      · exact (Real.sqrt_pos.2 (by exact_mod_cast positiveMode_pos N _)).ne' hq
      · exact hj hq
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    set c' := min c (c * (‖w‖⁻¹) ^ 2) with hc'_def
    have hc' : 0 < c' := lt_min hc (by positivity)
    obtain ⟨Rf, hRf, hfar⟩ := exists_link_far hρ hc' C₀
    let l := positiveScale (ι := Fin (N + 1)) (κ := κ) (positiveMode N) (positiveMode_pos N)
    have hcone' : ∀ (y : Coeff (Fin (N + 1)) κ) (s : ℝ), 0 ≤ s →
        FourierPolynomial.action (frequency N) H (l.symm (y, s • (‖w‖⁻¹ • w))) ≤
          C₀ - c' * (‖y‖ ^ 2 + s ^ 2) := by
      intro y s hs
      rw [smul_smul, positiveScale_symm_cone]
      refine (hcone N hND y (s * ‖w‖⁻¹) (by positivity)).trans ?_
      have h1 : c' * ‖y‖ ^ 2 ≤ c * ‖y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
      have h2 : c' * s ^ 2 ≤ c * (‖w‖⁻¹) ^ 2 * s ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
      have h3 : c * (‖y‖ ^ 2 + (s * ‖w‖⁻¹) ^ 2) = c * ‖y‖ ^ 2 + c * (‖w‖⁻¹) ^ 2 * s ^ 2 := by
        ring
      rw [h3]
      linarith
    have he : ‖‖w‖⁻¹ • w‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwpos.ne']
    have hpos : ∀ z : Coeff (Fin (N + 1)) κ, ‖z‖ = linkRadius κ M →
        2 * linkLevel κ M ≤ FourierPolynomial.action (frequency N) H (l.symm (0, z)) := by
      intro z hz
      have hb := action_positive_lower (negativeMode N) (positiveMode N)
        (positiveMode_injective N) (positiveMode_pos N) hH.continuous hM hup z
      rw [hz] at hb
      exact (linkLevel_bound hM).trans hb
    have hnear' : ∀ (y : Coeff (Fin (N + 1)) κ) (s : ℝ), 0 < s → s < ε →
        FourierPolynomial.action (frequency N) H (l.symm (y, s • (‖w‖⁻¹ • w))) ≤
          linkLevel κ M / 2 := by
      intro y s hs hse
      rw [smul_smul, positiveScale_symm_cone]
      refine (action_cone_le hH0 N y p _).trans ?_
      have h : (s * ‖w‖⁻¹) ^ 2 * (Real.pi * ‖w‖ ^ 2) = Real.pi * s ^ 2 := by
        field_simp
      rw [h]
      exact hnear s hs hse
    have hfar' : ∀ (y : Coeff (Fin (N + 1)) κ) (s : ℝ), 0 < s → Rf ≤ ‖(y, s)‖ →
        FourierPolynomial.action (frequency N) H (l.symm (y, s • (‖w‖⁻¹ • w))) ≤
          linkLevel κ M / 2 := by
      intro y s hs hys
      refine (hcone' y s hs.le).trans ((hfar ‖y‖ s (norm_nonneg y) ?_).trans (by positivity))
      simpa only [Prod.norm_def, Real.norm_eq_abs] using hys
    have hupper' : ∀ (y : Coeff (Fin (N + 1)) κ) (s : ℝ), 0 < s → ‖(y, s)‖ < Rf →
        FourierPolynomial.action (frequency N) H (l.symm (y, s • (‖w‖⁻¹ • w))) ≤
          max C₀ (linkLevel κ M) := by
      intro y s hs _
      have hnn : 0 ≤ c' * (‖y‖ ^ 2 + s ^ 2) := by positivity
      exact (hcone' y s hs.le).trans ((sub_le_self _ hnn).trans (le_max_left _ _))
    obtain ⟨x, hx1, -, hx3⟩ := exists_critical_cerami l (contDiff_action (frequency N) hH) he ha
      (le_max_right C₀ _) hρ hε hRf hpos hnear' hfar' hupper'
      ⟨R₁, c₁, hc₁, fun x hx1 _ hx3 => hcer N hN0 x hx1 hx3⟩
    exact ⟨x, hx1, hx3⟩
  have hseq : ∀ n : ℕ, ∃ x : Coeff (Fin (n + N₁ + 1) ⊕ Fin (n + N₁ + 1)) κ,
      linkLevel κ M ≤ FourierPolynomial.action (frequency (n + N₁)) H x ∧
      gradient (FourierPolynomial.action (frequency (n + N₁)) H) x = 0 :=
    fun n => hcrit (n + N₁) (by omega)
  choose xs hxa hxg using hseq
  have hxR : ∀ n, ‖xs n‖ < R₁ := by
    intro n
    by_contra h
    push Not at h
    have h' := hcer (n + N₁) (by omega) (xs n) (hxa n) h
    rw [hxg n, norm_zero, mul_zero] at h'
    linarith
  have hR₁ : 0 ≤ R₁ := (norm_nonneg _).trans (hxR 0).le
  have hDv : 0 ≤ 2 * C * (1 + R₁) := by positivity
  have hvel : ∀ n, ‖velocityCoeff (frequency (n + N₁)) (xs n)‖ ≤ 2 * C * (1 + R₁) := by
    intro n
    have h1 := norm_velocityCoeff_le (frequency (n + N₁)) hH (xs n)
    have h2 := norm_project_gradLoop_le (frequency (n + N₁)) (frequency_injective _) hH
      hE.grow (xs n)
    rw [hxg n, norm_zero, zero_add] at h1
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left (by linarith [hxR n]) (by linarith)))
  obtain ⟨X, φ, hφ, hX⟩ := L2Paths.exists_periodic_subsequence
    (fun n => loop (frequency (n + N₁)) (xs n))
    (fun n t s => loop_modulus _ (frequency_injective _) (xs n) (hvel n) t s)
    (fun n t => loop_bound' _ (frequency_injective _) (xs n) hR₁ hDv (hxR n).le (hvel n) t)
  have hex : ∀ m : ℤ, ∀ᶠ n in atTop, m ∈ Set.range (frequency (n + N₁)) := fun m =>
    (tendsto_add_atTop_nat N₁).eventually (frequency_exhausts m)
  have hcoef := limit_coefficient (α := fun n => Fin (n + N₁ + 1) ⊕ Fin (n + N₁ + 1))
    (fun n => frequency (n + N₁)) (fun n => frequency_injective _) hex hH xs hxg φ hφ X hX
  have hposA := positive_action_limit (α := fun n => Fin (n + N₁ + 1) ⊕ Fin (n + N₁ + 1))
    (fun n => frequency (n + N₁)) hH xs hxg hxa φ X hX
  refine ⟨fun t => X (t : Time), ?_, ?_, ?_⟩
  · simp only [AddCircle.coe_period, AddCircle.coe_zero]
  · change 0 < ∫ t in (0:ℝ)..1, (fun s : Time =>
      inner (𝕜 := ℝ) (gradient H (X s)) (X s) / 2 - H (X s)) (t : Time)
    rw [intervalIntegral_eq_average (fun s : Time =>
      inner (𝕜 := ℝ) (gradient H (X s)) (X s) / 2 - H (X s))]
    exact lt_of_lt_of_le ha hposA
  · exact hasDerivAt_of_critical_coefficients hH X hcoef

end Viterbo.Cap.PartE2b
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-! ## Part C: the cone estimate from a lower bound `H ≥ α gauge_L² - C₀` -/

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Part W: a trigonometric loop beating `α > c_EHZ(L)` -/

end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
variable {κ : Type} [Fintype κ]
variable {L : Set (Vector κ)} (φ : ContDiffBump (0 : Vector κ))
/-! ## Part M: mollified gauges -/














end Viterbo.Cap
end
end

section
open MeasureTheory Set Filter Topology OAI.SymmetricPolar
open scoped ENNReal ContDiff Pointwise NNReal
noncomputable section
namespace Viterbo.Cap
open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic
/-! ## Part K: profiles of a mollified gauge on `K` have only constant `1`-periodic orbits -/

/-! ## Part A1: the bridge from a symplectic embedding of convex domains -/

/-! ## Part A2: one-variable profiles -/


/-! ## Part A3: monotonicity of `c_EHZ` under symplectic embeddings of convex domains -/

/-! ## Part P: the envelope capacity and the target -/

end Viterbo.Cap
end
end

theorem solution : type_of% @Viterbo.Cap.PartE2b.engine := @Viterbo.Cap.PartE2b.engine
