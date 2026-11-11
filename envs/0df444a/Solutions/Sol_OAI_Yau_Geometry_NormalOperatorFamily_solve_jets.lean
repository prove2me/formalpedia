-- Prove2me | solution 1 for OAI.Yau.Geometry.NormalOperatorFamily.solve_jets
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:24:58.028203+00:00
-- url     : https://prove2.me/submissions/c19fec7f-6732-4d6f-9c83-6a5d32b87ffa

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

section
-- module Solutions.OAIQ237_NY.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PhaseJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
noncomputable section

theorem contactEta_compatibility {a b h00 h11 : ℝ} (ha : a ≠ 0) :
    a ^ 2 * (h00 - contactEta a b h00 h11) +
      b ^ 2 * (h11 - contactEta a b h00 h11) = 0 := by
  have hd : a ^ 2 + b ^ 2 ≠ 0 := by
    have := sq_pos_of_ne_zero ha
    positivity
  unfold contactEta
  field_simp
  ring

theorem imaginaryHessian_symmetric {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {H : Matrix (Fin 4) (Fin 4) ℝ}
    (hc : a ^ 2 * H 0 0 + b ^ 2 * H 1 1 = 0) :
    ∀ i j, imaginaryHessian a b H i j = imaginaryHessian a b H j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [imaginaryHessian]
  all_goals field_simp
  all_goals nlinarith [hc]

theorem imaginaryHessian_contractions {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (H : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    b * imaginaryHessian a b H 1 j = a * H 0 j ∧
    a * imaginaryHessian a b H 0 j = -b * H 1 j := by
  simp [imaginaryHessian]
  constructor <;> field_simp

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_PolynomialJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
open MvPolynomial Finsupp
noncomputable section

theorem pderiv_primitive {σ K : Type*} [Field K] [CharZero K]
    (i : σ) (p : MvPolynomial σ K) : pderiv i (primitive i p) = p := by
  classical
  unfold primitive
  rw [map_sum]
  conv_rhs => rw [p.as_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [pderiv_monomial]
  have hn : (s i : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (s i)
  simp [Finsupp.add_apply, hn]

theorem primitive_homogeneous {σ K : Type*} [Field K]
    (i : σ) {p : MvPolynomial σ K} {m : ℕ} (hp : p.IsHomogeneous m) :
    (primitive i p).IsHomogeneous (m + 1) := by
  classical
  unfold primitive
  apply IsHomogeneous.sum
  intro s hs
  apply isHomogeneous_monomial
  have hd : s.degree = m := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hs) (hp.coeff_eq_zero h)
  simp [map_add, Finsupp.degree_single, hd]

end
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_DirectionalJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau
namespace Jets
open MvPolynomial
noncomputable section
variable {σ K : Type*} [Field K] [DecidableEq σ]

omit [DecidableEq σ] in
lemma direction_X (v : σ → K) (j : σ) : direction v (X j) = C (v j) := by
  simp [direction]

omit [DecidableEq σ] in
lemma direction_C_mul (v : σ → K) (a : K) (p : Poly σ K) :
    direction v (C a * p) = C a * direction v p := by
  rw [(direction v).leibniz]
  simp [smul_eq_mul]

lemma transverse_derivative (v : σ → K) (i : σ) (hi : v i ≠ 0) (j : σ) :
    direction v (transverse v i j) = if j = i then 1 else 0 := by
  by_cases hj : j = i
  · subst j
    simp [transverse, direction_X, ← map_mul, hi]
  · simp only [transverse, ite_eq_right hj, map_add, direction_C_mul, direction_X]
    have he : v j + -(v j / v i) * v i = 0 := by field_simp <;> ring
    simpa only [map_add, map_mul, map_neg, map_zero] using congrArg (C : K → Poly σ K) he

lemma transverse_inverse (v : σ → K) (i : σ) (hi : v i ≠ 0) (j : σ) :
    aeval (transverse v i) (original v i j) = X j := by
  by_cases hj : j = i
  · subst j
    simp only [original, map_mul, aeval_C, algebraMap_eq, aeval_X,
      transverse, ite_true, if_true]
    rw [← mul_assoc, ← map_mul]
    simp [hi]
  · simp only [original, map_add, map_mul, aeval_X, aeval_C,
      algebraMap_eq, transverse, ite_eq_right hj, ite_true, if_true]
    have he : C (-(v j / v i)) + C (v j) * C ((v i)⁻¹) = (0 : Poly σ K) := by
      rw [← map_mul, ← map_add]
      simp [div_eq_mul_inv]
    linear_combination (X i) * he

lemma substitution_inverse (v : σ → K) (i : σ) (hi : v i ≠ 0) (p : Poly σ K) :
    aeval (transverse v i) (aeval (original v i) p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, hp, transverse_inverse v i hi]

lemma directional_substitution (v : σ → K) (i : σ) (hi : v i ≠ 0) (p : Poly σ K) :
    direction v (aeval (transverse v i) p) =
      aeval (transverse v i) (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, (direction v).leibniz, hp, transverse_derivative v i hi,
      pderiv_mul, pderiv_X, map_add, smul_eq_mul]
    by_cases hj : j = i <;> simp [hj] <;> ring

lemma transverse_homogeneous (v : σ → K) (i j : σ) :
    (transverse v i j).IsHomogeneous 1 := by
  unfold transverse
  split_ifs
  · exact isHomogeneous_C_mul_X _ _
  · exact (isHomogeneous_X K j).add (isHomogeneous_C_mul_X _ _)

lemma original_homogeneous (v : σ → K) (i j : σ) :
    (original v i j).IsHomogeneous 1 := by
  unfold original
  split_ifs
  · exact isHomogeneous_C_mul_X _ _
  · exact (isHomogeneous_X K j).add (isHomogeneous_C_mul_X _ _)

lemma direction_eq_sum [Fintype σ] (v : σ → K) :
    direction v = ∑ i, v i • pderiv (R := K) i := by
  apply MvPolynomial.derivation_ext
  intro j
  have hs (s : Finset σ) :
      (∑ i ∈ s, v i • pderiv (R := K) i) (X j) =
        ∑ i ∈ s, v i • pderiv (R := K) i (X j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, Derivation.smul_apply, ih]
  rw [hs]
  simp [direction_X, pderiv_X, Algebra.smul_def, Pi.single_apply]

end
end Jets
end Yau

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_RecursiveJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

lemma gradientJet_congr (v : Fin 4 → ℂ) {a b : Jet} {k n : ℕ}
    (hk : k ≤ n) (h : ∀ j, j ≤ n + 1 → a j = b j) (i : Fin 4) :
    gradientJet v a k i = gradientJet v b k i := by
  unfold gradientJet
  split_ifs
  · rfl
  · rw [h (k + 1) (by omega)]

lemma eikonalKnown_congr (v : Fin 4 → ℂ) (g : ℕ → Fin 4 → Fin 4 → CPoly)
    (n : ℕ) (a b : Jet) (h : ∀ k, k ≤ n + 1 → a k = b k) :
    eikonalKnown v g n a = eikonalKnown v g n b := by
  unfold eikonalKnown
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro i _
    rw [gradientJet_congr v (by have := Finset.mem_range.mp ht; omega) h,
      gradientJet_congr v (Nat.sub_le _ _) h]
  · apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [gradientJet_congr v (by have := Finset.mem_range.mp ht; omega) h,
      gradientJet_congr v (by omega) h]

lemma direction_apply (v : Fin 4 → ℂ) (p : CPoly) :
    direction v p = ∑ i, C (v i) * pderiv i p := by
  rw [direction_eq_sum]
  have hs (s : Finset (Fin 4)) :
      (∑ i ∈ s, v i • pderiv (R := ℂ) i) p =
        ∑ i ∈ s, C (v i) * pderiv i p := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, Derivation.smul_apply,
        Algebra.smul_def, ih]
  exact hs _

lemma direction_two (v : Fin 4 → ℂ) (p : CPoly) :
    direction (fun i ↦ 2 * v i) p = 2 * ∑ i, C (v i) * pderiv i p := by
  rw [direction_apply]
  simp only [map_mul, map_ofNat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eikonalCoefficient_split (v : Fin 4 → ℂ)
    (g : ℕ → Fin 4 → Fin 4 → CPoly) (n : ℕ) (a : Jet) :
    eikonalCoefficient v g n a = homogeneousComponent (n + 1)
      (direction (fun i ↦ 2 * v i) (a (n + 2)) + eikonalKnown v g n a) := by
  unfold eikonalCoefficient eikonalKnown
  apply congrArg (homogeneousComponent (n + 1))
  rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ',
    Finset.sum_range_succ]
  simp only [Nat.sub_zero, gradientJet, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ite_false, if_false]
  rw [direction_two]
  simp only [Nat.add_sub_add_right, Nat.sub_self, ite_true, if_true]
  have hc : (∑ i : Fin 4, pderiv i (a (n + 1 + 1)) * C (v i)) =
      ∑ i : Fin 4, C (v i) * pderiv i (a (n + 1 + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hc]
  ring

lemma pderiv_homogeneous {p : CPoly} {n : ℕ} (hp : p.IsHomogeneous (n + 1))
    (i : Fin 4) : (pderiv i p).IsHomogeneous n := by
  intro d hd
  rw [coeff_pderiv] at hd
  have hc : p.coeff (d + Finsupp.single i 1) ≠ 0 := by
    intro h; simp [h] at hd
  have h := hp hc
  simpa [map_add, Finsupp.weight_single] using h

lemma direction_homogeneous (v : Fin 4 → ℂ) {p : CPoly} {n : ℕ}
    (hp : p.IsHomogeneous (n + 1)) : (direction v p).IsHomogeneous n := by
  rw [direction_apply]
  apply IsHomogeneous.sum
  intro i _
  simpa using (isHomogeneous_C _ (v i)).mul (pderiv_homogeneous hp i)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TransportJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

lemma transportKnown_congr (W : ℕ → Fin 4 → CPoly) (c f : Jet) (n : ℕ)
    (a b : Jet) (h : ∀ k, k ≤ n → a k = b k) :
    transportKnown W c f n a = transportKnown W c f n b := by
  unfold transportKnown
  apply congrArg (· - f n)
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro i _
    rw [h (n - r) (Nat.sub_le _ _)]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [h (n - r) (Nat.sub_le _ _)]

theorem transportCoefficient_split (w : Fin 4 → ℂ) (W : ℕ → Fin 4 → CPoly)
    (c f : Jet) (n : ℕ) (a : Jet) :
    transportCoefficient w W c f n a = homogeneousComponent n
      (direction w (a (n + 1)) + transportKnown W c f n a) := by
  unfold transportCoefficient transportKnown
  apply congrArg (homogeneousComponent n)
  rw [Finset.sum_range_succ', direction_apply]
  simp only [Nat.sub_zero, ite_true, if_true, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ite_false, if_false]
  have hs : (∑ r ∈ Finset.range n, ∑ i, W (r + 1) i * pderiv i (a (n - (r + 1) + 1))) =
      ∑ r ∈ Finset.range n, ∑ i, W (r + 1) i * pderiv i (a (n - r)) := by
    apply Finset.sum_congr rfl
    intro r hr
    have he : n - (r + 1) + 1 = n - r := by have := Finset.mem_range.mp hr; omega
    rw [he]
  rw [hs]
  ring

theorem secondOrderCoefficient_congr (g : ℕ → Fin 4 → Fin 4 → CPoly)
    (b : ℕ → Fin 4 → CPoly) (a a' : Jet) (n : ℕ)
    (h : ∀ k, k ≤ n + 2 → a k = a' k) :
    secondOrderCoefficient g b a n = secondOrderCoefficient g b a' n := by
  unfold secondOrderCoefficient
  apply congrArg (homogeneousComponent n)
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [h (n - r + 2) (by omega)]
  · apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    rw [h (n - r + 1) (by omega)]

theorem wave_degree_budgets (m J j : ℕ) (hj : j < J) :
    (m + 1 + 2 * (J - j)) = (m + 1 + 2 * (J - (j + 1))) + 2 ∧
    (m + 1 + 2 * (J - j)) + 1 < m + 2 * J + 3 ∧
    m < m + 1 + 2 * (J - j) := by omega

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_FiniteWaveJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

theorem polynomialJet_truncate (a : Jet) (ha : ∀ k, (a k).IsHomogeneous k) (d k : ℕ) :
    polynomialJet (truncateJet a d) k = if k ≤ d then a k else 0 := by
  unfold polynomialJet truncateJet
  rw [map_sum]
  simp_rw [homogeneousComponent_of_mem (ha _)]
  simp [Finset.mem_range]

lemma polynomialJet_truncate_eq (a : Jet) (ha : ∀ k, (a k).IsHomogeneous k)
    (d k : ℕ) (hk : k ≤ d) : polynomialJet (truncateJet a d) k = a k := by
  simp [polynomialJet_truncate a ha, hk]

lemma eikonalCoefficient_congr (v : Fin 4 → ℂ) (g : ℕ → Fin 4 → Fin 4 → CPoly)
    (n : ℕ) (a b : Jet) (h : ∀ k, k ≤ n + 2 → a k = b k) :
    eikonalCoefficient v g n a = eikonalCoefficient v g n b := by
  rw [eikonalCoefficient_split, eikonalCoefficient_split, h (n + 2) le_rfl,
    eikonalKnown_congr v g n a b (fun k hk ↦ h k (by omega))]

lemma transportCoefficient_congr (w : Fin 4 → ℂ) (W : ℕ → Fin 4 → CPoly)
    (c : Jet) (f f' : Jet) (n : ℕ) (a b : Jet)
    (h : ∀ k, k ≤ n + 1 → a k = b k) (hf : f n = f' n) :
    transportCoefficient w W c f n a = transportCoefficient w W c f' n b := by
  rw [transportCoefficient_split, transportCoefficient_split, h (n + 1) le_rfl]
  rw [transportKnown_congr W c f n a b (fun k hk ↦ h k (by omega))]
  simp only [transportKnown, hf]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_JetCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

lemma homogeneousComponent_pderiv (p : CPoly) (n : ℕ) (i : Fin 4) :
    homogeneousComponent n (pderiv i p) = pderiv i (homogeneousComponent (n + 1) p) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_pderiv, map_add, Finsupp.degree_single]
  by_cases hd : d.degree = n
  · simp [hd]
  · simp [hd]

theorem homogeneousComponent_mul (p q : CPoly) (n : ℕ) :
    homogeneousComponent n (p * q) = ∑ r ∈ Finset.range (n + 1),
      homogeneousComponent r p * homogeneousComponent (n - r) q := by
  let A := homogeneousSubmodule (Fin 4) ℂ
  have hd (p : CPoly) (k : ℕ) :
      ((DirectSum.decompose A p) k : CPoly) = homogeneousComponent k p :=
    MvPolynomial.decomposition.decompose'_apply p k
  rw [← hd, DirectSum.decompose_mul, DirectSum.coe_mul_apply_eq_sum_antidiagonal]
  simp only [hd]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ homogeneousComponent i p * homogeneousComponent j q) n

theorem secondOrderCoefficient_eq (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly)
    (p : CPoly) (n : ℕ) :
    secondOrderCoefficient (fun r i j ↦ homogeneousComponent r (g i j))
      (fun r i ↦ homogeneousComponent r (b i)) (polynomialJet p) n =
      homogeneousComponent n (polynomialSecondOrder g b p) := by
  unfold secondOrderCoefficient polynomialSecondOrder polynomialJet
  have he : ((∑ r ∈ Finset.range (n + 1), ∑ i, ∑ j,
      homogeneousComponent r (g i j) * pderiv i (pderiv j (homogeneousComponent (n - r + 2) p))) +
      ∑ r ∈ Finset.range (n + 1), ∑ i,
        homogeneousComponent r (b i) * pderiv i (homogeneousComponent (n - r + 1) p)) =
      homogeneousComponent n ((∑ i, ∑ j, g i j * pderiv i (pderiv j p)) +
        ∑ i, b i * pderiv i p) := by
    simp only [map_add, map_sum, homogeneousComponent_mul, homogeneousComponent_pderiv]
    apply congrArg₂ (· + ·)
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    · rw [Finset.sum_comm]
  rw [he, homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _)]

theorem transportCoefficient_eq (w : Fin 4 → ℂ) (W : Fin 4 → CPoly)
    (hW : ∀ i, homogeneousComponent 0 (W i) = C (w i)) (c f a : CPoly) (n : ℕ) :
    transportCoefficient w (fun r i ↦ homogeneousComponent r (W i))
      (polynomialJet c) (polynomialJet f) n (polynomialJet a) =
      homogeneousComponent n (polynomialTransport W c f a) := by
  unfold transportCoefficient polynomialTransport polynomialJet
  have hw (r : ℕ) (i : Fin 4) :
      (if r = 0 then C (w i) else homogeneousComponent r (W i)) =
        homogeneousComponent r (W i) := by
    split_ifs with h
    · subst r; exact (hW i).symm
    · rfl
  simp only [hw]
  have he : ((∑ r ∈ Finset.range (n + 1), ∑ i,
      homogeneousComponent r (W i) * pderiv i (homogeneousComponent (n - r + 1) a)) +
      (∑ r ∈ Finset.range (n + 1), homogeneousComponent r c * homogeneousComponent (n - r) a) -
      homogeneousComponent n f) =
      homogeneousComponent n ((∑ i, W i * pderiv i a) + c * a - f) := by
    simp only [map_sub, map_add, map_sum, homogeneousComponent_mul, homogeneousComponent_pderiv]
    rw [Finset.sum_comm]
  rw [he, homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _)]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_EikonalPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

lemma gradientJet_polynomial (v : Fin 4 → ℂ) (p : CPoly)
    (hfirst : ∀ i, pderiv i (homogeneousComponent 1 p) = C (v i)) (k : ℕ) (i : Fin 4) :
    gradientJet v (polynomialJet p) k i = homogeneousComponent k (pderiv i p) := by
  rw [homogeneousComponent_pderiv]
  unfold gradientJet polynomialJet
  split_ifs with hk
  · subst k; exact (hfirst i).symm
  · rfl

lemma eikonal_convolution (g : Fin 4 → Fin 4 → CPoly) (p : CPoly) (d : ℕ) :
    (∑ r ∈ Finset.range (d + 1), ∑ t ∈ Finset.range (d - r + 1), ∑ i, ∑ j,
      homogeneousComponent r (g i j) * homogeneousComponent t (pderiv i p) *
        homogeneousComponent (d - r - t) (pderiv j p)) =
    homogeneousComponent d (∑ i, ∑ j, g i j * (pderiv i p * pderiv j p)) := by
  simp only [map_sum, homogeneousComponent_mul, Finset.mul_sum]
  simp only [mul_assoc]
  calc
    _ = ∑ r ∈ Finset.range (d + 1), ∑ i : Fin 4, ∑ j : Fin 4,
        ∑ t ∈ Finset.range (d - r + 1),
          homogeneousComponent r (g i j) * homogeneousComponent t (pderiv i p) *
            homogeneousComponent (d - r - t) (pderiv j p) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [mul_assoc]

theorem eikonalCoefficient_eq (v : Fin 4 → ℂ) (g : Fin 4 → Fin 4 → CPoly)
    (hmetric : ∀ i j, homogeneousComponent 0 (g i j) = if i = j then 1 else 0)
    (p : CPoly) (hfirst : ∀ i, pderiv i (homogeneousComponent 1 p) = C (v i)) (n : ℕ) :
    eikonalCoefficient v (fun r i j ↦ homogeneousComponent r (g i j)) n (polynomialJet p) =
      homogeneousComponent (n + 1) (polynomialEikonal g p) := by
  have he := eikonal_convolution g p (n + 1)
  rw [Finset.sum_range_succ'] at he
  simp only [Nat.sub_zero, hmetric] at he
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true] at he
  have hs : (∑ r ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1 - (r + 1) + 1), ∑ i, ∑ j,
      homogeneousComponent (r + 1) (g i j) * homogeneousComponent t (pderiv i p) *
        homogeneousComponent (n + 1 - (r + 1) - t) (pderiv j p)) =
      ∑ r ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1 - r), ∑ i, ∑ j,
        homogeneousComponent (r + 1) (g i j) * homogeneousComponent t (pderiv i p) *
          homogeneousComponent (n - r - t) (pderiv j p) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hnr : n + 1 - (r + 1) + 1 = n + 1 - r := by
      have := Finset.mem_range.mp hr
      omega
    rw [hnr, Nat.add_sub_add_right]
  rw [hs] at he
  unfold eikonalCoefficient
  simp_rw [gradientJet_polynomial v p hfirst]
  rw [show n + 1 + 1 = n + 2 by omega] at he
  rw [add_comm (G := CPoly)] at he
  rw [he, homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _)]
  unfold polynomialEikonal
  rw [map_add, homogeneousComponent_of_mem (isHomogeneous_C (Fin 4) (4 : ℂ))]
  simp

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_WaveJetAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

lemma beamVector_center (v : Fin 4 → ℂ) (g : Fin 4 → Fin 4 → CPoly)
    (hmetric : ∀ i j, homogeneousComponent 0 (g i j) = if i = j then 1 else 0)
    (phi : CPoly) (hfirst : ∀ i, pderiv i (homogeneousComponent 1 phi) = C (v i)) :
    ∀ i, homogeneousComponent 0 (beamVector g phi i) = C (2 * v i) := by
  intro i
  have hc0 (a b : CPoly) : homogeneousComponent 0 (a * b) =
      homogeneousComponent 0 a * homogeneousComponent 0 b := by
    simpa using homogeneousComponent_mul a b 0
  unfold beamVector
  rw [homogeneousComponent_C_mul, map_sum]
  simp only [hc0, homogeneousComponent_pderiv, Nat.zero_add, hfirst, hmetric,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, map_mul]

end
end Yau.Jets

end OAI
end

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

theorem reval_secondOrder (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly) (p : CPoly) :
    reval (polynomialSecondOrder g b p) =
      smoothSecondOrder (fun i j ↦ reval (g i j)) (fun i ↦ reval (b i)) (reval p) := by
  funext x
  simp [polynomialSecondOrder, smoothSecondOrder, coordPartial_reval, reval]

theorem reval_eikonal (g : Fin 4 → Fin 4 → CPoly) (p : CPoly) :
    reval (polynomialEikonal g p) = smoothEikonal (fun i j ↦ reval (g i j)) (reval p) := by
  funext x
  simp [polynomialEikonal, smoothEikonal, coordPartial_reval, reval, mul_assoc]

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

lemma FlatAt.add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f g : Coord → F} {x : Coord}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h : FlatAt n f x) (h' : FlatAt n g x) : FlatAt n (fun y ↦ f y + g y) x := by
  intro k hk
  change iteratedFDeriv ℝ k (f + g) x = 0
  rw [iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    (hg.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt, h k hk, h' k hk, add_zero]

lemma FlatAt.sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} (s : Finset ι) {n : ℕ} {f : ι → Coord → F} {x : Coord}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (h : ∀ i ∈ s, FlatAt n (f i) x) :
    FlatAt n (fun y ↦ ∑ i ∈ s, f i y) x := by
  intro k hk
  rw [iteratedFDeriv_fun_sum_apply (fun i hi ↦ ((hf i hi).of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
  exact Finset.sum_eq_zero (fun i hi ↦ h i hi k hk)

theorem FlatAt.mul {n : ℕ} {f g : Coord → ℂ} {x : Coord}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (h : FlatAt n f x) :
    FlatAt n (fun y ↦ f y * g y) x := by
  intro k hk
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hb := norm_iteratedFDeriv_mul_le hf hg x (n := k) (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  calc
    _ ≤ _ := hb
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [h i (by have := Finset.mem_range.mp hi; omega), norm_zero]
      ring

lemma coordPartial_contDiff {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    ContDiff ℝ ∞ (coordPartial i f) :=
  (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

lemma fderiv_reval_eq (p : CPoly) :
    fderiv ℝ (reval p) = fun x ↦ ∑ i, reval (pderiv i p) x • coordCLM i := by
  funext x
  ext v
  simp [fderiv_reval, coordCLM, smul_eq_mul]

theorem flatAt_reval {p : CPoly} {n : ℕ}
    (h : ∀ k, k ≤ n → homogeneousComponent k p = 0) : FlatAt n (reval p) 0 := by
  induction n generalizing p with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_zero]
    have hc := congrArg (fun polynomial : CPoly ↦ polynomial.coeff 0) (h 0 le_rfl)
    simpa [reval, eval_zero, constantCoeff_eq, coeff_homogeneousComponent] using congrArg norm hc
  | succ n ih =>
    have hp (i : Fin 4) : FlatAt n (reval (pderiv i p)) 0 := by
      apply ih
      intro k hk
      rw [homogeneousComponent_pderiv, h (k + 1) (by omega), map_zero]
    have hd : FlatAt n (fderiv ℝ (reval p)) 0 := by
      rw [fderiv_reval_eq]
      apply FlatAt.sum Finset.univ
      · intro i _
        exact (reval_contDiff _).smul contDiff_const
      · intro i _ k hk
        rw [iteratedFDeriv_smul_const_apply ((reval_contDiff _).of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt,
          hp i k hk]
        ext v
        simp
    intro k hk
    cases k with
    | zero =>
      exact (ih (fun j hj ↦ h j (by omega))) 0 (by omega)
    | succ k =>
      apply norm_eq_zero.mp
      rw [← norm_iteratedFDeriv_fderiv, hd k (by omega), norm_zero]

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

lemma continuousPolyFamily_of_representation {ι : Type*} (s : Finset ι)
    (p : ι → CPoly) (c : T → ι → ℂ) (hc : ∀ i ∈ s, Continuous (fun t ↦ c t i)) :
    ContinuousPolyFamily (fun t ↦ ∑ i ∈ s, c t i • p i) := by
  classical
  constructor
  · intro d
    simp only [coeff_sum, coeff_smul, smul_eq_mul]
    exact continuous_finsetSum _ (fun i hi ↦ (hc i hi).mul continuous_const)
  · refine ⟨s.biUnion (fun i ↦ (p i).support), ?_⟩
    intro t d hd
    by_contra hn
    have hz (i : ι) (hi : i ∈ s) : (p i).coeff d = 0 := by
      apply notMem_support_iff.mp
      intro h
      exact hn (Finset.mem_biUnion.mpr ⟨i, hi, h⟩)
    have : (∑ i ∈ s, c t i • p i).coeff d = 0 := by
      simp only [coeff_sum, coeff_smul]
      exact Finset.sum_eq_zero (fun i hi ↦ by rw [hz i hi, smul_zero])
    exact (mem_support_iff.mp hd) this

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

lemma ContinuousPolyFamily.linearMap {P : T → CPoly} (hp : ContinuousPolyFamily P)
    (L : CPoly →ₗ[ℂ] CPoly) : ContinuousPolyFamily (fun t ↦ L (P t)) := by
  obtain ⟨s, hs⟩ := hp.2
  have he : (fun t ↦ L (P t)) = fun t ↦
      ∑ d ∈ s, (P t).coeff d • L (monomial d (1 : ℂ)) := by
    funext t
    conv_lhs => rw [polynomial_sum_of_support_subset (P t) s (hs t)]
    simp
  rw [he]
  exact continuousPolyFamily_of_representation s _ _ (fun d _ ↦ hp.1 d)

lemma ContinuousPolyFamily.mul {P Q : T → CPoly}
    (hp : ContinuousPolyFamily P) (hq : ContinuousPolyFamily Q) :
    ContinuousPolyFamily (fun t ↦ P t * Q t) := by
  obtain ⟨s, hs⟩ := hp.2
  have he : (fun t ↦ P t * Q t) = fun t ↦
      ∑ d ∈ s, (P t).coeff d • (monomial d (1 : ℂ) * Q t) := by
    funext t
    conv_lhs => rw [polynomial_sum_of_support_subset (P t) s (hs t)]
    simp [Finset.sum_mul]
  rw [he]
  apply ContinuousPolyFamily.sum
  intro d _
  exact (hq.linearMap (LinearMap.mulLeft ℂ (monomial d (1 : ℂ)))).smul (hp.1 d)

lemma ContinuousPolyFamily.C {c : T → ℂ} (hc : Continuous c) :
    ContinuousPolyFamily (fun t ↦ C (c t)) := by
  simpa [Algebra.smul_def] using (ContinuousPolyFamily.const (T := T) 1).smul hc

lemma continuousPolyFamily_aeval_fixed (p : CPoly) (q : Fin 4 → T → CPoly)
    (hq : ∀ i, ContinuousPolyFamily (q i)) :
    ContinuousPolyFamily (fun t ↦ MvPolynomial.aeval (fun i ↦ q i t) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (ContinuousPolyFamily.const (T := T) (C a))
  | add p r hp hr => simpa using hp.add hr
  | mul_X p i hp => simpa using hp.mul (hq i)

lemma ContinuousPolyFamily.aeval {P : T → CPoly} (hp : ContinuousPolyFamily P)
    (q : Fin 4 → T → CPoly) (hq : ∀ i, ContinuousPolyFamily (q i)) :
    ContinuousPolyFamily (fun t ↦ MvPolynomial.aeval (fun i ↦ q i t) (P t)) := by
  obtain ⟨s, hs⟩ := hp.2
  have he : (fun t ↦ MvPolynomial.aeval (fun i ↦ q i t) (P t)) = fun t ↦
      ∑ d ∈ s, (P t).coeff d • MvPolynomial.aeval (fun i ↦ q i t) (monomial d (1 : ℂ)) := by
    funext t
    conv_lhs => rw [polynomial_sum_of_support_subset (P t) s (hs t)]
    simp only [Algebra.smul_def, map_sum, map_mul, aeval_C, algebraMap_eq]
  rw [he]
  exact ContinuousPolyFamily.sum s (fun d _ ↦
    (continuousPolyFamily_aeval_fixed _ q hq).smul (hp.1 d))

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
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformDirectional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

theorem directionalPrimitive_right_inverse (v : Fin 4 → ℂ) (i : Fin 4)
    (hi : v i ≠ 0) (p : CPoly) : direction v (directionalPrimitive v i p) = p := by
  rw [directionalPrimitive, directional_substitution v i hi, Yau.pderiv_primitive]
  exact substitution_inverse v i hi p

lemma directionalPrimitive_homogeneous (v : Fin 4 → ℂ) (i : Fin 4)
    {p : CPoly} {n : ℕ} (hp : p.IsHomogeneous n) :
    (directionalPrimitive v i p).IsHomogeneous (n + 1) := by
  have hq : (aeval (original v i) p).IsHomogeneous n := by
    simpa using hp.aeval (original v i) (original_homogeneous v i)
  simpa [directionalPrimitive] using (Yau.primitive_homogeneous i hq).aeval (transverse v i)
    (transverse_homogeneous v i)

variable {T : Type*} [TopologicalSpace T]

lemma ContinuousPolyFamily.primitive {P : T → CPoly} (hp : ContinuousPolyFamily P)
    (i : Fin 4) : ContinuousPolyFamily (fun t ↦ Yau.primitive i (P t)) := by
  obtain ⟨s, hs⟩ := hp.2
  have he : (fun t ↦ Yau.primitive i (P t)) = fun t ↦
      ∑ d ∈ s, (P t).coeff d • monomial (d + Finsupp.single i 1)
        (((d i : ℂ) + 1)⁻¹) := by
    funext t
    simp only [Yau.primitive, smul_monomial, smul_eq_mul, div_eq_mul_inv]
    exact Finset.sum_subset (hs t) (fun d _ hd ↦ by
      simp [notMem_support_iff.mp hd])
  rw [he]
  exact continuousPolyFamily_of_representation s _ _ (fun d _ ↦ hp.1 d)

lemma continuousPolyFamily_original (v : T → Fin 4 → ℂ)
    (hv : ∀ j, Continuous (fun t ↦ v t j)) (i j : Fin 4) :
    ContinuousPolyFamily (fun t ↦ original (v t) i j) := by
  unfold original
  split_ifs
  · exact (ContinuousPolyFamily.C (hv i)).mul (ContinuousPolyFamily.const _)
  · exact (ContinuousPolyFamily.const _).add ((ContinuousPolyFamily.C (hv j)).mul (ContinuousPolyFamily.const _))

lemma continuousPolyFamily_transverse (v : T → Fin 4 → ℂ)
    (hv : ∀ j, Continuous (fun t ↦ v t j)) (i : Fin 4) (hi : ∀ t, v t i ≠ 0)
    (j : Fin 4) : ContinuousPolyFamily (fun t ↦ transverse (v t) i j) := by
  unfold transverse
  split_ifs
  · exact (ContinuousPolyFamily.C ((hv i).inv₀ hi)).mul (ContinuousPolyFamily.const _)
  · exact (ContinuousPolyFamily.const _).add ((ContinuousPolyFamily.C (((hv j).div (hv i) hi).neg)).mul (ContinuousPolyFamily.const _))

theorem ContinuousPolyFamily.directionalPrimitive {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (v : T → Fin 4 → ℂ)
    (hv : ∀ j, Continuous (fun t ↦ v t j)) (i : Fin 4) (hi : ∀ t, v t i ≠ 0) :
    ContinuousPolyFamily (fun t ↦ directionalPrimitive (v t) i (P t)) := by
  exact ((hp.aeval (fun j t ↦ original (v t) i j)
    (continuousPolyFamily_original v hv i)).primitive i).aeval
      (fun j t ↦ transverse (v t) i j) (continuousPolyFamily_transverse v hv i hi)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformRecursiveJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma ContinuousPolyFamily.neg {P : T → CPoly} (hp : ContinuousPolyFamily P) :
    ContinuousPolyFamily (fun t ↦ -P t) := by
  simpa using hp.smul (continuous_const : Continuous (fun _ : T ↦ (-1 : ℂ)))

lemma ContinuousPolyFamily.sub {P Q : T → CPoly}
    (hp : ContinuousPolyFamily P) (hq : ContinuousPolyFamily Q) :
    ContinuousPolyFamily (fun t ↦ P t - Q t) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg

lemma ContinuousPolyFamily.pderiv {P : T → CPoly} (hp : ContinuousPolyFamily P)
    (i : Fin 4) : ContinuousPolyFamily (fun t ↦ pderiv i (P t)) :=
  hp.linearMap (MvPolynomial.pderiv i).toLinearMap

lemma ContinuousPolyFamily.homogeneousComponent {P : T → CPoly}
    (hp : ContinuousPolyFamily P) (n : ℕ) :
    ContinuousPolyFamily (fun t ↦ homogeneousComponent n (P t)) :=
  hp.linearMap (MvPolynomial.homogeneousComponent n)

theorem finite_triangular_jets_continuous
    (v : T → Fin 4 → ℂ) (hv : ∀ j, Continuous (fun t ↦ v t j))
    (i : Fin 4) (hi : ∀ t, v t i ≠ 0)
    (lower : T → ℕ → Jet → CPoly)
    (hlower : ∀ t n a, (lower t n a).IsHomogeneous n)
    (hcausal : ∀ t n a b, (∀ k, k ≤ n → a k = b k) → lower t n a = lower t n b)
    (hc : ∀ n (a : T → Jet), (∀ k, ContinuousPolyFamily (fun t ↦ a t k)) →
      ContinuousPolyFamily (fun t ↦ lower t n (a t)))
    (initial : T → Jet) (hinitial : ∀ t k, (initial t k).IsHomogeneous k)
    (hic : ∀ k, ContinuousPolyFamily (fun t ↦ initial t k)) (base steps : ℕ) :
    ∃ a : T → Jet,
      (∀ t k, (a t k).IsHomogeneous k) ∧
      (∀ k, ContinuousPolyFamily (fun t ↦ a t k)) ∧
      (∀ t k, k ≤ base → a t k = initial t k) ∧
      ∀ t n, base ≤ n → n < base + steps →
        direction (v t) (a t (n + 1)) + lower t n (a t) = 0 := by
  induction steps with
  | zero => exact ⟨initial, hinitial, hic, fun _ _ _ ↦ rfl, by omega⟩
  | succ steps ih =>
    obtain ⟨a, ha, hac, hkeep, hsolve⟩ := ih
    let n := base + steps
    let q : T → CPoly := fun t ↦ directionalPrimitive (v t) i (-lower t n (a t))
    have hq (t : T) : (q t).IsHomogeneous (n + 1) :=
      directionalPrimitive_homogeneous _ _ (hlower t n (a t)).neg
    have hqc : ContinuousPolyFamily q := (hc n a hac).neg.directionalPrimitive v hv i hi
    let b : T → Jet := fun t ↦ Function.update (a t) (n + 1) (q t)
    have heq (t : T) (k : ℕ) (hk : k ≤ n) : b t k = a t k :=
      Function.update_of_ne (by omega) _ _
    refine ⟨b, ?_, ?_, ?_, ?_⟩
    · intro t k
      by_cases hk : k = n + 1
      · subst k; simpa [b] using hq t
      · simpa [b, Function.update_of_ne hk] using ha t k
    · intro k
      by_cases hk : k = n + 1
      · subst k; simpa [b] using hqc
      · simpa [b, Function.update_of_ne hk] using hac k
    · intro t k hk
      exact (heq t k (by dsimp [n]; omega)).trans (hkeep t k hk)
    · intro t r hr hrbound
      by_cases hrn : r = n
      · subst r
        rw [hcausal t n (b t) (a t) (heq t)]
        rw [show b t (n + 1) = q t by simp [b]]
        rw [show direction (v t) (q t) = -lower t n (a t) from
          directionalPrimitive_right_inverse (v t) i (hi t) _]
        exact neg_add_cancel _
      · have hrlt : r < n := by dsimp [n] at *; omega
        rw [heq t (r + 1) (by omega), hcausal t r (b t) (a t)
          (fun k hk ↦ heq t k (by omega))]
        exact hsolve t r hr hrlt

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformEikonal
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

lemma gradientJet_family (v : T → Fin 4 → ℂ) (hv : ∀ i, Continuous (fun t ↦ v t i))
    (a : T → Jet) (ha : ∀ k, ContinuousPolyFamily (fun t ↦ a t k)) (k : ℕ) (i : Fin 4) :
    ContinuousPolyFamily (fun t ↦ gradientJet (v t) (a t) k i) := by
  unfold gradientJet
  split_ifs
  · exact ContinuousPolyFamily.C (hv i)
  · exact (ha _).pderiv i

lemma eikonalKnown_family (v : T → Fin 4 → ℂ) (hv : ∀ i, Continuous (fun t ↦ v t i))
    (g : T → ℕ → Fin 4 → Fin 4 → CPoly)
    (hg : ∀ r i j, ContinuousPolyFamily (fun t ↦ g t r i j))
    (a : T → Jet) (ha : ∀ k, ContinuousPolyFamily (fun t ↦ a t k)) (n : ℕ) :
    ContinuousPolyFamily (fun t ↦ eikonalKnown (v t) (g t) n (a t)) := by
  unfold eikonalKnown
  apply ContinuousPolyFamily.add
  · apply ContinuousPolyFamily.sum
    intro r _
    apply ContinuousPolyFamily.sum
    intro i _
    exact (gradientJet_family v hv a ha _ i).mul (gradientJet_family v hv a ha _ i)
  · apply ContinuousPolyFamily.sum
    intro r _
    apply ContinuousPolyFamily.sum
    intro u _
    apply ContinuousPolyFamily.sum
    intro i _
    apply ContinuousPolyFamily.sum
    intro j _
    exact ((hg _ i j).mul (gradientJet_family v hv a ha _ i)).mul
      (gradientJet_family v hv a ha _ j)

theorem finite_eikonal_jets_continuous
    (v : T → Fin 4 → ℂ) (hv : ∀ j, Continuous (fun t ↦ v t j))
    (i : Fin 4) (hi : ∀ t, v t i ≠ 0)
    (g : T → ℕ → Fin 4 → Fin 4 → CPoly)
    (hg : ∀ r i j, ContinuousPolyFamily (fun t ↦ g t r i j))
    (initial : T → Jet) (hinitial : ∀ t k, (initial t k).IsHomogeneous k)
    (hic : ∀ k, ContinuousPolyFamily (fun t ↦ initial t k)) (steps : ℕ) :
    ∃ a : T → Jet,
      (∀ t k, (a t k).IsHomogeneous k) ∧
      (∀ k, ContinuousPolyFamily (fun t ↦ a t k)) ∧
      (∀ t k, k ≤ 2 → a t k = initial t k) ∧
      ∀ t n, 1 ≤ n → n < 1 + steps → eikonalCoefficient (v t) (g t) n (a t) = 0 := by
  let low : T → ℕ → Jet → CPoly := fun t n a ↦
    if n = 0 then 0 else homogeneousComponent n (eikonalKnown (v t) (g t) (n - 1) a)
  have hlow : ∀ t n a, (low t n a).IsHomogeneous n := by
    intro t n a
    dsimp [low]
    split_ifs
    · exact isHomogeneous_zero _ _ _
    · exact homogeneousComponent_isHomogeneous _ _
  have hcausal : ∀ t n a b, (∀ k, k ≤ n → a k = b k) → low t n a = low t n b := by
    intro t n a b h
    dsimp [low]
    split_ifs with hn
    · rfl
    · rw [eikonalKnown_congr (v t) (g t) (n - 1) a b
        (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h)]
  have hlc : ∀ n (a : T → Jet), (∀ k, ContinuousPolyFamily (fun t ↦ a t k)) →
      ContinuousPolyFamily (fun t ↦ low t n (a t)) := by
    intro n a ha
    dsimp [low]
    split_ifs
    · exact .const _
    · exact (eikonalKnown_family v hv g hg a ha _).homogeneousComponent n
  obtain ⟨a, ha, hac, hkeep, hsolve⟩ := finite_triangular_jets_continuous
    (fun t j ↦ 2 * v t j) (fun j ↦ continuous_const.mul (hv j))
    i (fun t ↦ mul_ne_zero (by norm_num) (hi t)) low hlow hcausal hlc
    initial hinitial hic 2 steps
  refine ⟨a, ha, hac, hkeep, ?_⟩
  intro t n hn hnb
  rw [eikonalCoefficient_split, map_add,
    homogeneousComponent_eq_self (direction_homogeneous _ (ha t (n + 2)))]
  simpa [low] using hsolve t (n + 1) (by omega) (by omega)

theorem finite_eikonal_polynomial_continuous
    (v : T → Fin 4 → ℂ) (hv : ∀ j, Continuous (fun t ↦ v t j))
    (i : Fin 4) (hi : ∀ t, v t i ≠ 0)
    (g : T → ℕ → Fin 4 → Fin 4 → CPoly)
    (hg : ∀ r i j, ContinuousPolyFamily (fun t ↦ g t r i j))
    (initial : T → Jet) (hinitial : ∀ t k, (initial t k).IsHomogeneous k)
    (hic : ∀ k, ContinuousPolyFamily (fun t ↦ initial t k))
    (hsecond : ∀ t, eikonalCoefficient (v t) (g t) 0 (initial t) = 0) (steps : ℕ) :
    ∃ p : T → CPoly, ContinuousPolyFamily p ∧
      (∀ t k, k ≤ 2 → polynomialJet (p t) k = initial t k) ∧
      (∀ t k, steps + 2 < k → polynomialJet (p t) k = 0) ∧
      (∀ t n, n ≤ steps → eikonalCoefficient (v t) (g t) n (polynomialJet (p t)) = 0) ∧
      ∀ (s : Set T), IsCompact s → ∀ R k, ∃ C > 0, ∀ t ∈ s, ∀ x : Coord,
        ‖x‖ ≤ R → ‖iteratedFDeriv ℝ k (reval (p t)) x‖ ≤ C := by
  obtain ⟨a, ha, hac, hkeep, hsolve⟩ :=
    finite_eikonal_jets_continuous v hv i hi g hg initial hinitial hic steps
  have hpc : ContinuousPolyFamily (fun t ↦ truncateJet (a t) (steps + 2)) :=
    ContinuousPolyFamily.sum _ (fun k _ ↦ hac k)
  refine ⟨fun t ↦ truncateJet (a t) (steps + 2), hpc, ?_, ?_, ?_,
    fun s hs R k ↦ hpc.uniform_derivative_bound s hs R k⟩
  · intro t k hk
    rw [polynomialJet_truncate_eq (a t) (ha t) _ _ (by omega), hkeep t k hk]
  · intro t k hk
    simp [polynomialJet_truncate (a t) (ha t), show ¬ k ≤ steps + 2 by omega]
  · intro t n hn
    rw [eikonalCoefficient_congr (v t) (g t) n _ (a t)
      (fun k hk ↦ polynomialJet_truncate_eq (a t) (ha t) _ _ (by omega))]
    by_cases hz : n = 0
    · subst n
      rw [eikonalCoefficient_congr (v t) (g t) 0 (a t) (initial t) (by simpa using hkeep t)]
      exact hsecond t
    · exact hsolve t n (by omega) (by omega)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_InitialPhasePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

lemma linearPhase_homogeneous (v : Fin 4 → ℂ) : (linearPhase v).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

lemma quadraticPhase_homogeneous (H : Fin 4 → Fin 4 → ℂ) :
    (quadraticPhase H).IsHomogeneous 2 := by
  unfold quadraticPhase
  apply IsHomogeneous.C_mul
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_C_mul_X _ _).mul (isHomogeneous_X ℂ j)

lemma pderiv_linearPhase (v : Fin 4 → ℂ) (i : Fin 4) :
    pderiv i (linearPhase v) = C (v i) := by
  simp [linearPhase, pderiv_X, Pi.single_apply]

lemma pderiv_quadraticPhase (H : Fin 4 → Fin 4 → ℂ)
    (hH : ∀ i j, H i j = H j i) (i : Fin 4) :
    pderiv i (quadraticPhase H) = ∑ j, C (H i j) * X j := by
  simp only [quadraticPhase, pderiv_mul, map_sum, pderiv_C, pderiv_X, Pi.single_apply,
    zero_mul, zero_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  have he : (∑ j, C (H j i) * X j) = ∑ j, C (H i j) * X j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hH j i]
  rw [he]
  have hs : (∑ x, ∑ j, if x = i then C (H x j) * X j else 0) =
      ∑ j, C (H i j) * X j := by
    rw [Finset.sum_comm]
    simp
  rw [hs, ← two_mul, ← mul_assoc]
  have hc : C (1/2 : ℂ) * (2:CPoly) = 1 := by
    calc
      _ = C ((1/2 : ℂ)*2) := by rw [map_mul]; congr 1
      _ = _ := by norm_num
  rw [hc, one_mul]

lemma initialPhaseJet_homogeneous (S : ℝ) (v : Fin 4 → ℂ) (H : Fin 4 → Fin 4 → ℂ)
    (k : ℕ) : (initialPhaseJet S v H k).IsHomogeneous k := by
  unfold initialPhaseJet
  split_ifs with h0 h1 h2
  · subst k; exact isHomogeneous_C _ _
  · subst k; exact linearPhase_homogeneous v
  · subst k; exact quadraticPhase_homogeneous H
  · exact isHomogeneous_zero (Fin 4) ℂ k

lemma initialPhaseJet_first (S : ℝ) (v : Fin 4 → ℂ) (H : Fin 4 → Fin 4 → ℂ) (i : Fin 4) :
    pderiv i (initialPhaseJet S v H 1) = C (v i) := by
  simpa [initialPhaseJet] using pderiv_linearPhase v i

theorem initialPhaseJet_second (S : ℝ) (v : Fin 4 → ℂ)
    (H : Fin 4 → Fin 4 → ℂ) (hH : ∀ i j, H i j = H j i)
    (hcontract : ∀ j, ∑ i, v i * H i j = 0)
    (g : ℕ → Fin 4 → Fin 4 → CPoly) (hg : ∀ i j, g 1 i j = 0) :
    eikonalCoefficient v g 0 (initialPhaseJet S v H) = 0 := by
  have hd : (∑ i, C (v i) * pderiv i (quadraticPhase H)) = 0 := by
    simp_rw [pderiv_quadraticPhase H hH, Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum, hcontract, map_zero, zero_mul]
    simp
  rw [eikonalCoefficient_split, direction_two]
  simp [initialPhaseJet, eikonalKnown, hg, hd]

variable {T : Type*} [TopologicalSpace T]

lemma initialPhaseJet_continuous (S : T → ℝ) (v : T → Fin 4 → ℂ)
    (H : T → Fin 4 → Fin 4 → ℂ) (hS : Continuous S)
    (hv : ∀ i, Continuous (fun t ↦ v t i))
    (hH : ∀ i j, Continuous (fun t ↦ H t i j)) (k : ℕ) :
    ContinuousPolyFamily (fun t ↦ initialPhaseJet (S t) (v t) (H t) k) := by
  by_cases h0 : k = 0
  · subst k
    simpa [initialPhaseJet] using ContinuousPolyFamily.C (Complex.continuous_ofReal.comp hS)
  by_cases h1 : k = 1
  · subst k
    simp only [initialPhaseJet, Nat.one_ne_zero, ite_false, if_false, ite_true, if_true]
    exact ContinuousPolyFamily.sum Finset.univ (fun i _ ↦
      (ContinuousPolyFamily.C (hv i)).mul (.const (X i)))
  by_cases h2 : k = 2
  · subst k
    simp only [initialPhaseJet, show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, ite_false, if_false, ite_true, if_true]
    exact (ContinuousPolyFamily.const (C (1/2 : ℂ))).mul
      (ContinuousPolyFamily.sum Finset.univ (fun i _ ↦
        ContinuousPolyFamily.sum Finset.univ (fun j _ ↦
          ((ContinuousPolyFamily.C (hH i j)).mul (.const (X i))).mul (.const (X j)))))
  · simpa [initialPhaseJet, h0, h1, h2] using (ContinuousPolyFamily.const (0:CPoly) :
      ContinuousPolyFamily (fun _ : T ↦ (0:CPoly)))

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_NormalFramePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section

lemma normalFrameVector_null {a b : ℝ} (hlen : b^2 = a^2+4) :
    (∑ i, normalFrameVector a b i * normalFrameVector a b i) + 4 = 0 := by
  simp only [Fin.sum_univ_succ, normalFrameVector, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero, zero_mul]
  apply Complex.ext <;> simp
  nlinarith

lemma normalRealHessian_compatibility {a b : ℝ} (ha : a ≠ 0) (H : Fin 4 → Fin 4 → ℝ) :
    a^2 * normalRealHessian a b H 0 0 + b^2 * normalRealHessian a b H 1 1 = 0 := by
  simpa [normalRealHessian] using Yau.contactEta_compatibility (b := b) (h00 := H 0 0) (h11 := H 1 1) ha

lemma normalComplexHessian_symmetric {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (H : Fin 4 → Fin 4 → ℝ) (hH : ∀ i j, H i j = H j i) :
    ∀ i j, normalComplexHessian a b H i j = normalComplexHessian a b H j i := by
  intro i j
  have hK := Yau.imaginaryHessian_symmetric ha hb (normalRealHessian_compatibility ha H) i j
  have hR : normalRealHessian a b H i j = normalRealHessian a b H j i := by
    simp only [normalRealHessian, hH i j, eq_comm]
  simp only [normalComplexHessian, hK, hR]

lemma normalComplexHessian_contract {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (H : Fin 4 → Fin 4 → ℝ) (j : Fin 4) :
    (∑ i, normalFrameVector a b i * normalComplexHessian a b H i j) = 0 := by
  obtain ⟨h1,h2⟩ := Yau.imaginaryHessian_contractions ha hb (normalRealHessian a b H) j
  simp only [Fin.sum_univ_succ, normalFrameVector, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero, add_zero, zero_mul]
  apply Complex.ext <;> simp [normalComplexHessian] <;> nlinarith

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_NormalFrameContinuous
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma contactEta_continuous (a b : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hH : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) :
    Continuous (fun t ↦ Yau.contactEta (a t) (b t) (H t 0 0) (H t 1 1)) := by
  apply Continuous.div (((ha.pow 2).mul (hH 0 0)).add ((hb.pow 2).mul (hH 1 1)))
    ((ha.pow 2).add (hb.pow 2))
  intro t
  change a t ^ 2 + b t ^ 2 ≠ 0
  have h := sq_pos_of_ne_zero (ha0 t)
  nlinarith [sq_nonneg (b t)]

lemma normalRealHessian_continuous (a b : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hH : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) (i j : Fin 4) :
    Continuous (fun t ↦ normalRealHessian (a t) (b t) (H t) i j) := by
  unfold normalRealHessian
  split_ifs
  · exact (hH i j).sub (contactEta_continuous a b H ha hb hH ha0)
  · exact (hH i j).sub continuous_const

lemma normalComplexHessian_continuous (a b : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hH : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, b t ≠ 0) (i j : Fin 4) :
    Continuous (fun t ↦ normalComplexHessian (a t) (b t) (H t) i j) := by
  have hR := normalRealHessian_continuous a b H ha hb hH ha0
  have hK : Continuous (fun t ↦ Yau.imaginaryHessian (a t) (b t)
      (normalRealHessian (a t) (b t) (H t)) i j) := by
    unfold Yau.imaginaryHessian
    split_ifs
    · exact ((hb.div ha ha0).neg).mul (hR 1 j)
    · exact (ha.div hb hb0).mul (hR 0 j)
    · exact ((hb.div ha ha0).neg).mul (hR 1 i)
    · exact (ha.div hb hb0).mul (hR 0 i)
    · exact continuous_const
  exact (Complex.continuous_ofReal.comp (hR i j)).add
    ((Complex.continuous_ofReal.comp hK).mul continuous_const)

lemma normalFrameVector_continuous (a b : T → ℝ) (ha : Continuous a) (hb : Continuous b)
    (i : Fin 4) : Continuous (fun t ↦ normalFrameVector (a t) (b t) i) := by
  fin_cases i
  · exact Complex.continuous_ofReal.comp ha
  · exact (Complex.continuous_ofReal.comp hb).mul continuous_const
  · exact continuous_const
  · exact continuous_const

theorem normal_frame_initial_jets_continuous (a b S : T → ℝ)
    (H : T → Fin 4 → Fin 4 → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hS : Continuous S) (hH : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, b t ≠ 0) (k : ℕ) :
    ContinuousPolyFamily (fun t ↦ initialPhaseJet (S t) (normalFrameVector (a t) (b t))
      (normalComplexHessian (a t) (b t) (H t)) k) :=
  initialPhaseJet_continuous S _ _ hS (normalFrameVector_continuous a b ha hb)
    (normalComplexHessian_continuous a b H ha hb hH ha0 hb0) k

end
end Yau.Jets

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

lemma smoothEikonal_contDiff {g : Fin 4 → Fin 4 → Coord → ℂ} {f : Coord → ℂ}
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (smoothEikonal g f) := by
  apply ContDiff.add _ contDiff_const
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact ((hg i j).mul (coordPartial_contDiff hf i)).mul (coordPartial_contDiff hf j)

theorem flat_secondOrder_coefficients {n : ℕ}
    {g G : Fin 4 → Fin 4 → Coord → ℂ} {b B : Fin 4 → Coord → ℂ} {f : Coord → ℂ}
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hG : ∀ i j, ContDiff ℝ ∞ (G i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hB : ∀ i, ContDiff ℝ ∞ (B i))
    (hf : ContDiff ℝ ∞ f)
    (hgj : ∀ i j, FlatAt n (fun x ↦ g i j x - G i j x) 0)
    (hbj : ∀ i, FlatAt n (fun x ↦ b i x - B i x) 0) :
    FlatAt n (fun x ↦ smoothSecondOrder g b f x - smoothSecondOrder G B f x) 0 := by
  have he : (fun x ↦ smoothSecondOrder g b f x - smoothSecondOrder G B f x) =
      (fun x ↦ (∑ i, ∑ j, (g i j x - G i j x) * coordPartial i (coordPartial j f) x) +
        ∑ i, (b i x - B i x) * coordPartial i f x) := by
    funext x
    simp only [smoothSecondOrder, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  apply FlatAt.add
  · exact ContDiff.sum (fun i _ ↦ ContDiff.sum (fun j _ ↦
      ((hg i j).sub (hG i j)).mul (coordPartial_contDiff (coordPartial_contDiff hf j) i)))
  · exact ContDiff.sum (fun i _ ↦ ((hb i).sub (hB i)).mul (coordPartial_contDiff hf i))
  · apply FlatAt.sum Finset.univ
    · intro i _
      exact ContDiff.sum (fun j _ ↦ ((hg i j).sub (hG i j)).mul
        (coordPartial_contDiff (coordPartial_contDiff hf j) i))
    · intro i _
      apply FlatAt.sum Finset.univ
      · intro j _
        exact ((hg i j).sub (hG i j)).mul (coordPartial_contDiff (coordPartial_contDiff hf j) i)
      · intro j _
        exact (hgj i j).mul ((hg i j).sub (hG i j))
          (coordPartial_contDiff (coordPartial_contDiff hf j) i)
  · apply FlatAt.sum Finset.univ
    · intro i _
      exact ((hb i).sub (hB i)).mul (coordPartial_contDiff hf i)
    · intro i _
      exact (hbj i).mul ((hb i).sub (hB i)) (coordPartial_contDiff hf i)

theorem flat_eikonal_coefficients {n : ℕ}
    {g G : Fin 4 → Fin 4 → Coord → ℂ} {f : Coord → ℂ}
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hG : ∀ i j, ContDiff ℝ ∞ (G i j))
    (hf : ContDiff ℝ ∞ f) (hgj : ∀ i j, FlatAt n (fun x ↦ g i j x - G i j x) 0) :
    FlatAt n (fun x ↦ smoothEikonal g f x - smoothEikonal G f x) 0 := by
  have he : (fun x ↦ smoothEikonal g f x - smoothEikonal G f x) =
      fun x ↦ ∑ i, ∑ j, (g i j x - G i j x) * coordPartial i f x * coordPartial j f x := by
    funext x
    simp only [smoothEikonal, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  apply FlatAt.sum Finset.univ
  · intro i _
    exact ContDiff.sum (fun j _ ↦ (((hg i j).sub (hG i j)).mul
      (coordPartial_contDiff hf i)).mul (coordPartial_contDiff hf j))
  · intro i _
    apply FlatAt.sum Finset.univ
    · intro j _
      exact (((hg i j).sub (hG i j)).mul (coordPartial_contDiff hf i)).mul
        (coordPartial_contDiff hf j)
    · intro j _
      exact ((hgj i j).mul ((hg i j).sub (hG i j)) (coordPartial_contDiff hf i)).mul
        (((hg i j).sub (hG i j)).mul (coordPartial_contDiff hf i)) (coordPartial_contDiff hf j)

lemma flat_of_sub {n : ℕ} {f q : Coord → ℂ} (hf : ContDiff ℝ ∞ f)
    (hq : ContDiff ℝ ∞ q) (h : FlatAt n (fun x ↦ f x - q x) 0) (h' : FlatAt n q 0) :
    FlatAt n f 0 := by
  have he : f = fun x ↦ (f x - q x) + q x := by ext; ring
  rw [he]
  exact h.add (hf.sub hq) hq h'

theorem smooth_eikonal_flat {n : ℕ} {g : Fin 4 → Fin 4 → Coord → ℂ}
    (G : Fin 4 → Fin 4 → CPoly) (phi : CPoly)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hjet : ∀ i j, FlatAt n (fun x ↦ g i j x - reval (G i j) x) 0)
    (hpoly : ∀ k, k ≤ n → homogeneousComponent k (polynomialEikonal G phi) = 0) :
    FlatAt n (smoothEikonal g (reval phi)) 0 := by
  apply flat_of_sub (smoothEikonal_contDiff hg (reval_contDiff phi))
    (smoothEikonal_contDiff (fun i j ↦ reval_contDiff _) (reval_contDiff phi))
  · exact flat_eikonal_coefficients hg (fun i j ↦ reval_contDiff _) (reval_contDiff phi) hjet
  · rw [← reval_eikonal]
    exact flatAt_reval hpoly

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothSymmetry
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma directionalList_contDiff (l : List Coord) {f : Coord → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (directionalList l f) := by
  induction l with
  | nil => exact hf
  | cons v l ih => exact (ih.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

lemma directionalList_perm {l r : List Coord} (h : l.Perm r) {f : Coord → ℂ}
    (hf : ContDiff ℝ ∞ f) : directionalList l f = directionalList r f := by
  induction h with
  | nil => rfl
  | cons v h ih => simp only [directionalList, ih]
  | swap v w l =>
    funext x
    have hs : IsSymmSndFDerivAt ℝ (directionalList l f) x :=
      (directionalList_contDiff l hf).contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    dsimp [directionalList]
    rw [fderiv_clm_apply, fderiv_clm_apply]
    · simpa using hs w v
    all_goals first | exact differentiableAt_const _ | exact
      ((directionalList_contDiff l hf).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  | trans h h' ih ih' => exact ih.trans ih'

theorem iteratedFDeriv_eq_directionalList {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (v : Fin n → Coord) (x : Coord) :
    iteratedFDeriv ℝ n f x v = directionalList (List.ofFn v) f x := by
  induction n generalizing x with
  | zero => simp [directionalList]
  | succ n ih =>
    rw [iteratedFDeriv_succ_apply_left]
    have he : (fun y ↦ iteratedFDeriv ℝ n f y (Fin.tail v)) =
        directionalList (List.ofFn (Fin.tail v)) f := funext (fun y ↦ ih _ y)
    rw [← fderiv_continuousMultilinear_apply_const_apply
      ((hf.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast (show (n : ℕ∞) < ⊤ by simp))) x)]
    rw [he]
    simp only [List.ofFn_succ, directionalList]
    rfl

theorem smooth_iteratedFDeriv_perm {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (v : Fin n → Coord) (x : Coord) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  rw [iteratedFDeriv_eq_directionalList hf, iteratedFDeriv_eq_directionalList hf,
    directionalList_perm (σ.ofFn_comp_perm v) hf]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TaylorPolynomial
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

lemma coord_basis_sum (x : Coord) : ∑ i : Fin 4, x i • Pi.single i 1 = x := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, mul_ite]

theorem reval_tensorPolynomial {n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Coord) ℂ) (x : Coord) :
    reval (tensorPolynomial T) x = T (fun _ ↦ x) := by
  induction n with
  | zero => simp [tensorPolynomial, reval]; congr; ext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [tensorPolynomial, reval, map_sum, map_mul, eval_X]
    change (∑ i, (x i : ℂ) * reval (tensorPolynomial (T.curryLeft (Pi.single i 1))) x) = _
    simp_rw [ih]
    have h := congrArg (fun z : Coord ↦ (T.curryLeft z) (fun _ ↦ x)) (coord_basis_sum x)
    have he : Fin.cons x (fun _ : Fin n ↦ x) = fun _ ↦ x := by ext i; exact Fin.cases rfl (fun _ ↦ rfl) i
    simpa [map_sum, map_smul, ContinuousMultilinearMap.curryLeft_apply, he,
      RCLike.real_smul_eq_coe_mul] using h

lemma tensorPolynomial_homogeneous {n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Coord) ℂ) :
    (tensorPolynomial T).IsHomogeneous n := by
  induction n with
  | zero => exact isHomogeneous_C _ _
  | succ n ih =>
    apply IsHomogeneous.sum
    intro i _
    simpa [Nat.add_comm] using (isHomogeneous_X ℂ i).mul (ih _)

theorem reval_taylorPolynomial (f : Coord → ℂ) (y x : Coord) (m : ℕ) :
    reval (taylorPolynomial f y m) x =
      ∑ k ∈ Finset.range (m + 1), (k.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ k f y (fun _ ↦ x) := by
  simp only [taylorPolynomial, reval, map_sum, map_mul, eval_C]
  change (∑ k ∈ Finset.range (m + 1), _ * reval (tensorPolynomial _) x) = _
  simp_rw [reval_tensorPolynomial, RCLike.real_smul_eq_coe_mul]
  rfl

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_TaylorMatching
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma taylorPolynomial_hasFiniteSeries (f : Coord → ℂ) (y : Coord) (m : ℕ) :
    HasFiniteFPowerSeriesOnBall (reval (taylorPolynomial f y m))
      (finiteTaylorSeries f y m) 0 (m + 1) ⊤ := by
  apply HasFiniteFPowerSeriesOnBall.mk'
  · intro k hk
    simp [finiteTaylorSeries, show ¬ k ≤ m by omega]
  · simp
  · intro x _
    rw [zero_add, reval_taylorPolynomial]
    apply Finset.sum_congr rfl
    intro k hk
    simp [finiteTaylorSeries, show k ≤ m by have := Finset.mem_range.mp hk; omega]

theorem iteratedFDeriv_taylorPolynomial {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f)
    (y : Coord) (m k : ℕ) (hk : k ≤ m) :
    iteratedFDeriv ℝ k (reval (taylorPolynomial f y m)) 0 = iteratedFDeriv ℝ k f y := by
  ext v
  rw [(taylorPolynomial_hasFiniteSeries f y m).toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace]
  simp only [finiteTaylorSeries, ite_eq_left hk, smul_apply]
  have hs (σ : Equiv.Perm (Fin k)) :
      iteratedFDeriv ℝ k f y (fun i ↦ v (σ i)) = iteratedFDeriv ℝ k f y v :=
    smooth_iteratedFDeriv_perm hf k v y σ
  simp_rw [hs]
  simp [Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
    Nat.factorial_ne_zero]

theorem flatAt_taylorPolynomial {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    FlatAt m (fun x ↦ f x - reval (taylorPolynomial f 0 m) x) 0 := by
  intro k hk
  change iteratedFDeriv ℝ k (f - reval (taylorPolynomial f 0 m)) 0 = 0
  rw [iteratedFDeriv_sub_apply
    (hf.contDiffAt.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)))
    ((reval_contDiff _).contDiffAt.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))),
    iteratedFDeriv_taylorPolynomial hf 0 m k hk, sub_self]

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformTaylor
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

lemma tensorPolynomial_coeff_continuous (n : ℕ) (d : Fin 4 →₀ ℕ) :
    Continuous (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Coord) ℂ ↦
      (tensorPolynomial T).coeff d) := by
  induction n generalizing d with
  | zero =>
    simp only [tensorPolynomial, coeff_C]
    split_ifs
    · exact (ContinuousMultilinearMap.apply ℝ _ ℂ 0).continuous
    · exact continuous_const
  | succ n ih =>
    simp only [tensorPolynomial, coeff_sum, coeff_X_mul']
    apply continuous_finsetSum
    intro i _
    split_ifs
    · apply (ih _).comp
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ Coord) ℂ).continuous.clm_apply
        continuous_const
    · exact continuous_const

lemma tensorPolynomial_family {T : Type*} [TopologicalSpace T] {n : ℕ}
    (A : T → ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Coord) ℂ) (hA : Continuous A) :
    ContinuousPolyFamily (fun t ↦ tensorPolynomial (A t)) := by
  classical
  refine ⟨fun d ↦ (tensorPolynomial_coeff_continuous n d).comp hA,
    (Finsupp.finite_of_degree_eq (σ := Fin 4) n).toFinset, ?_⟩
  intro t d hd
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  rw [Finsupp.degree_eq_weight_one]
  have hw : (fun _ : Fin 4 ↦ (1 : ℕ)) = (1 : Fin 4 → ℕ) := by funext i; rfl
  rw [hw]
  exact tensorPolynomial_homogeneous (A t) (mem_support_iff.mp hd)

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Charts_NormalTaylorMetric
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

lemma tensorPolynomial_zero (k : ℕ) : tensorPolynomial (0 : Coord [×k]→L[ℝ] ℂ) = 0 := by
  induction k with
  | zero => simp [tensorPolynomial]
  | succ k ih =>
    simp only [tensorPolynomial]
    have hz (i : Fin 4) : (0 : Coord [×(k+1)]→L[ℝ] ℂ).curryLeft (Pi.single i 1) = 0 := by ext v; simp
    simp_rw [hz, ih]
    simp

lemma taylorPolynomial_component (f : Coord → ℂ) (y : Coord) (m k : ℕ) (hk : k ≤ m) :
    homogeneousComponent k (taylorPolynomial f y m) =
      C (((k.factorial:ℝ)⁻¹:ℝ):ℂ) * tensorPolynomial (iteratedFDeriv ℝ k f y) := by
  unfold taylorPolynomial
  rw [map_sum]
  have ht (l : ℕ) :
      (C (((l.factorial:ℝ)⁻¹:ℝ):ℂ) * tensorPolynomial (iteratedFDeriv ℝ l f y)).IsHomogeneous l :=
    (tensorPolynomial_homogeneous _).C_mul _
  simp_rw [homogeneousComponent_of_mem (ht _)]
  simp [Finset.mem_range, show k < m+1 by omega]

lemma taylorPolynomial_value_component (f : Coord → ℂ) (y : Coord) (m : ℕ) :
    homogeneousComponent 0 (taylorPolynomial f y m) = C (f y) := by
  rw [taylorPolynomial_component f y m 0 (by omega)]
  simp [tensorPolynomial]

lemma taylorPolynomial_first_zero (f : Coord → ℂ) (y : Coord) (m : ℕ)
    (hm : 1 ≤ m) (hf : fderiv ℝ f y = 0) :
    homogeneousComponent 1 (taylorPolynomial f y m) = 0 := by
  rw [taylorPolynomial_component f y m 1 hm]
  have hd : iteratedFDeriv ℝ 1 f y = 0 := by
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_one, hf, norm_zero]
  rw [hd, tensorPolynomial_zero, mul_zero]

theorem normal_metric_matching_taylor
    (g : Fin 4 → Fin 4 → Coord → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (h0 : ∀ i j, g i j 0 = if i=j then 1 else 0)
    (h1 : ∀ i j, fderiv ℝ (g i j) 0 = 0) (m : ℕ) (hm : 1 ≤ m) :
    let G := fun i j ↦ taylorPolynomial (g i j) 0 m
    (∀ i j, homogeneousComponent 0 (G i j) = if i=j then 1 else 0) ∧
    (∀ i j, homogeneousComponent 1 (G i j) = 0) ∧
    ∀ i j, FlatAt m (fun x ↦ g i j x-reval (G i j) x) 0 := by
  refine ⟨?_,fun i j ↦ taylorPolynomial_first_zero _ _ _ hm (h1 i j),
    fun i j ↦ flatAt_taylorPolynomial (hg i j) m⟩
  intro i j
  rw [taylorPolynomial_value_component, h0]
  split_ifs <;> simp

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothTransportJet
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

lemma reval_transport (W : Fin 4 → CPoly) (c f a : CPoly) :
    reval (polynomialTransport W c f a) =
      smoothTransport (fun i ↦ reval (W i)) (reval c) (reval f) (reval a) := by
  funext x
  simp [reval, polynomialTransport, smoothTransport, coordPartial_reval]

lemma smoothTransport_contDiff {W : Fin 4 → Coord → ℂ} {c f a : Coord → ℂ}
    (hW : ∀ i, ContDiff ℝ ∞ (W i)) (hc : ContDiff ℝ ∞ c)
    (hf : ContDiff ℝ ∞ f) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (smoothTransport W c f a) :=
  ((ContDiff.sum (fun i _ ↦ (hW i).mul (coordPartial_contDiff ha i))).add (hc.mul ha)).sub hf

lemma FlatAt.neg {n : ℕ} {f : Coord → ℂ} (h : FlatAt n f 0) :
    FlatAt n (fun x ↦ -f x) 0 := by
  intro k hk
  change iteratedFDeriv ℝ k (-f) 0 = 0
  rw [iteratedFDeriv_neg_apply, h k hk, neg_zero]

lemma FlatAt.sub {n : ℕ} {f g : Coord → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h : FlatAt n f 0) (h' : FlatAt n g 0) : FlatAt n (fun x ↦ f x - g x) 0 := by
  simpa only [sub_eq_add_neg] using h.add hf hg.neg h'.neg

theorem flat_transport_coefficients {n : ℕ}
    {W W' : Fin 4 → Coord → ℂ} {c c' f f' a : Coord → ℂ}
    (hW : ∀ i, ContDiff ℝ ∞ (W i)) (hW' : ∀ i, ContDiff ℝ ∞ (W' i))
    (hc : ContDiff ℝ ∞ c) (hc' : ContDiff ℝ ∞ c')
    (hf : ContDiff ℝ ∞ f) (hf' : ContDiff ℝ ∞ f') (ha : ContDiff ℝ ∞ a)
    (hjW : ∀ i, FlatAt n (fun x ↦ W i x - W' i x) 0)
    (hjc : FlatAt n (fun x ↦ c x - c' x) 0) (hjf : FlatAt n (fun x ↦ f x - f' x) 0) :
    FlatAt n (fun x ↦ smoothTransport W c f a x - smoothTransport W' c' f' a x) 0 := by
  have he : (fun x ↦ smoothTransport W c f a x - smoothTransport W' c' f' a x) =
      fun x ↦ (∑ i, (W i x - W' i x) * coordPartial i a x) +
        (c x - c' x) * a x - (f x - f' x) := by
    funext x
    simp only [smoothTransport, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  apply FlatAt.sub _ (hf.sub hf') _ hjf
  · exact (ContDiff.sum (fun i _ ↦ ((hW i).sub (hW' i)).mul
      (coordPartial_contDiff ha i))).add ((hc.sub hc').mul ha)
  · apply FlatAt.add _ ((hc.sub hc').mul ha) _ (hjc.mul (hc.sub hc') ha)
    · exact ContDiff.sum (fun i _ ↦ ((hW i).sub (hW' i)).mul (coordPartial_contDiff ha i))
    · exact FlatAt.sum Finset.univ
        (fun i _ ↦ ((hW i).sub (hW' i)).mul (coordPartial_contDiff ha i))
        (fun i _ ↦ (hjW i).mul ((hW i).sub (hW' i)) (coordPartial_contDiff ha i))

theorem smooth_transport_flat {n : ℕ} {W : Fin 4 → Coord → ℂ} {c f : Coord → ℂ}
    (WP : Fin 4 → CPoly) (cP fP a : CPoly)
    (hW : ∀ i, ContDiff ℝ ∞ (W i)) (hc : ContDiff ℝ ∞ c) (hf : ContDiff ℝ ∞ f)
    (hjW : ∀ i, FlatAt n (fun x ↦ W i x - reval (WP i) x) 0)
    (hjc : FlatAt n (fun x ↦ c x - reval cP x) 0)
    (hjf : FlatAt n (fun x ↦ f x - reval fP x) 0)
    (hp : ∀ k, k ≤ n → homogeneousComponent k (polynomialTransport WP cP fP a) = 0) :
    FlatAt n (smoothTransport W c f (reval a)) 0 := by
  apply flat_of_sub (smoothTransport_contDiff hW hc hf (reval_contDiff a))
    (smoothTransport_contDiff (fun i ↦ reval_contDiff _) (reval_contDiff _)
      (reval_contDiff _) (reval_contDiff a))
  · exact flat_transport_coefficients hW (fun i ↦ reval_contDiff _) hc (reval_contDiff _)
      hf (reval_contDiff _) (reval_contDiff a) hjW hjc hjf
  · rw [← reval_transport]
    exact flatAt_reval hp

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_SmoothBeamJet
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

lemma reval_beamVector (g : Fin 4 → Fin 4 → CPoly) (phi : CPoly) (i : Fin 4) :
    reval (beamVector g phi i) = smoothBeamVector (fun i j ↦ reval (g i j)) (reval phi) i := by
  ext x
  simp [beamVector, smoothBeamVector, reval, coordPartial_reval]

lemma reval_beamScalar (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly) (phi : CPoly) :
    reval (beamScalar g b phi) =
      smoothBeamScalar (fun i j ↦ reval (g i j)) (fun i ↦ reval (b i)) (reval phi) := by
  have he := reval_secondOrder g b phi
  ext x
  simpa [beamScalar, smoothBeamScalar, reval] using congrFun he x

lemma smoothBeamVector_contDiff {g : Fin 4 → Fin 4 → Coord → ℂ} {phi : Coord → ℂ}
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hp : ContDiff ℝ ∞ phi) (i : Fin 4) :
    ContDiff ℝ ∞ (smoothBeamVector g phi i) :=
  contDiff_const.mul (ContDiff.sum (fun j _ ↦ (hg i j).mul (coordPartial_contDiff hp j)))

lemma smoothBeamScalar_contDiff {g : Fin 4 → Fin 4 → Coord → ℂ}
    {b : Fin 4 → Coord → ℂ} {phi : Coord → ℂ}
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hp : ContDiff ℝ ∞ phi) : ContDiff ℝ ∞ (smoothBeamScalar g b phi) :=
  (smoothSecondOrder_contDiff hg hb hp).add contDiff_const

lemma flat_beamVector {n : ℕ} {g : Fin 4 → Fin 4 → Coord → ℂ}
    (G : Fin 4 → Fin 4 → CPoly) (phi : CPoly)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hjet : ∀ i j, FlatAt n (fun x ↦ g i j x - reval (G i j) x) 0) (i : Fin 4) :
    FlatAt n (fun x ↦ smoothBeamVector g (reval phi) i x - reval (beamVector G phi i) x) 0 := by
  rw [reval_beamVector]
  have he : (fun x ↦ smoothBeamVector g (reval phi) i x -
      smoothBeamVector (fun i j ↦ reval (G i j)) (reval phi) i x) =
      fun x ↦ (∑ j, (g i j x - reval (G i j) x) * coordPartial j (reval phi) x) * 2 := by
    ext x
    simp only [smoothBeamVector, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  have hs : ContDiff ℝ ∞ (fun x ↦ ∑ j,
      (g i j x - reval (G i j) x) * coordPartial j (reval phi) x) :=
    ContDiff.sum (fun j _ ↦ ((hg i j).sub (reval_contDiff _)).mul
      (coordPartial_contDiff (reval_contDiff phi) j))
  apply FlatAt.mul hs contDiff_const
  exact FlatAt.sum Finset.univ
    (fun j _ ↦ ((hg i j).sub (reval_contDiff _)).mul (coordPartial_contDiff (reval_contDiff phi) j))
    (fun j _ ↦ (hjet i j).mul ((hg i j).sub (reval_contDiff _))
      (coordPartial_contDiff (reval_contDiff phi) j))

lemma flat_beamScalar {n : ℕ} {g : Fin 4 → Fin 4 → Coord → ℂ} {b : Fin 4 → Coord → ℂ}
    (G : Fin 4 → Fin 4 → CPoly) (B : Fin 4 → CPoly) (phi : CPoly)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hgj : ∀ i j, FlatAt n (fun x ↦ g i j x - reval (G i j) x) 0)
    (hbj : ∀ i, FlatAt n (fun x ↦ b i x - reval (B i) x) 0) :
    FlatAt n (fun x ↦ smoothBeamScalar g b (reval phi) x - reval (beamScalar G B phi) x) 0 := by
  rw [reval_beamScalar]
  simp only [smoothBeamScalar, add_sub_add_right_eq_sub]
  exact flat_secondOrder_coefficients hg (fun i j ↦ reval_contDiff _) hb
    (fun i ↦ reval_contDiff _) (reval_contDiff phi) hgj hbj

theorem smooth_beam_transport_flat {n : ℕ} {g : Fin 4 → Fin 4 → Coord → ℂ}
    {b : Fin 4 → Coord → ℂ} (G : Fin 4 → Fin 4 → CPoly) (B : Fin 4 → CPoly)
    (phi prev a : CPoly)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hgj : ∀ i j, FlatAt n (fun x ↦ g i j x - reval (G i j) x) 0)
    (hbj : ∀ i, FlatAt n (fun x ↦ b i x - reval (B i) x) 0)
    (hp : ∀ k, k ≤ n → homogeneousComponent k (polynomialTransport (beamVector G phi)
      (beamScalar G B phi) (-polynomialSecondOrder G B prev) a) = 0) :
    FlatAt n (smoothTransport (smoothBeamVector g (reval phi))
      (smoothBeamScalar g b (reval phi)) (fun x ↦ -smoothSecondOrder g b (reval prev) x)
      (reval a)) 0 := by
  apply smooth_transport_flat (beamVector G phi) (beamScalar G B phi)
    (-polynomialSecondOrder G B prev) a
    (smoothBeamVector_contDiff hg (reval_contDiff phi))
    (smoothBeamScalar_contDiff hg hb (reval_contDiff phi))
    (smoothSecondOrder_contDiff hg hb (reval_contDiff prev)).neg
    (flat_beamVector G phi hg hgj) (flat_beamScalar G B phi hg hb hgj hbj) _ hp
  have h := (flat_secondOrder_coefficients hg (fun i j ↦ reval_contDiff _) hb
    (fun i ↦ reval_contDiff _) (reval_contDiff prev) hgj hbj).neg
  have he : (fun x ↦ -smoothSecondOrder g b (reval prev) x -
      reval (-polynomialSecondOrder G B prev) x) =
      fun x ↦ -(smoothSecondOrder g b (reval prev) x -
        smoothSecondOrder (fun i j ↦ reval (G i j)) (fun i ↦ reval (B i)) (reval prev) x) := by
    rw [← reval_secondOrder]
    ext x
    simp [reval]
    ring
  rw [he]
  exact h

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma transportKnown_family (W : T → ℕ → Fin 4 → CPoly) (c f a : T → Jet)
    (hW : ∀ r i, ContinuousPolyFamily (fun t ↦ W t r i))
    (hc : ∀ r, ContinuousPolyFamily (fun t ↦ c t r))
    (hf : ∀ r, ContinuousPolyFamily (fun t ↦ f t r))
    (ha : ∀ r, ContinuousPolyFamily (fun t ↦ a t r)) (n : ℕ) :
    ContinuousPolyFamily (fun t ↦ transportKnown (W t) (c t) (f t) n (a t)) := by
  unfold transportKnown
  apply ContinuousPolyFamily.sub _ (hf n)
  apply ContinuousPolyFamily.add
  · apply ContinuousPolyFamily.sum
    intro r _
    apply ContinuousPolyFamily.sum
    intro i _
    exact (hW _ i).mul ((ha _).pderiv i)
  · exact ContinuousPolyFamily.sum _ (fun r _ ↦ (hc r).mul (ha _))

lemma secondOrderCoefficient_family (g : T → ℕ → Fin 4 → Fin 4 → CPoly)
    (b : T → ℕ → Fin 4 → CPoly) (a : T → Jet)
    (hg : ∀ r i j, ContinuousPolyFamily (fun t ↦ g t r i j))
    (hb : ∀ r i, ContinuousPolyFamily (fun t ↦ b t r i))
    (ha : ∀ r, ContinuousPolyFamily (fun t ↦ a t r)) (n : ℕ) :
    ContinuousPolyFamily (fun t ↦ secondOrderCoefficient (g t) (b t) (a t) n) := by
  unfold secondOrderCoefficient
  apply ContinuousPolyFamily.homogeneousComponent
  apply ContinuousPolyFamily.add
  · apply ContinuousPolyFamily.sum
    intro r _
    apply ContinuousPolyFamily.sum
    intro i _
    apply ContinuousPolyFamily.sum
    intro j _
    exact (hg _ i j).mul (((ha _).pderiv j).pderiv i)
  · apply ContinuousPolyFamily.sum
    intro r _
    apply ContinuousPolyFamily.sum
    intro i _
    exact (hb _ i).mul ((ha _).pderiv i)

theorem finite_transport_jets_continuous
    (w : T → Fin 4 → ℂ) (hw : ∀ j, Continuous (fun t ↦ w t j))
    (i : Fin 4) (hi : ∀ t, w t i ≠ 0)
    (W : T → ℕ → Fin 4 → CPoly) (c f : T → Jet)
    (hW : ∀ r i, ContinuousPolyFamily (fun t ↦ W t r i))
    (hc : ∀ r, ContinuousPolyFamily (fun t ↦ c t r))
    (hf : ∀ r, ContinuousPolyFamily (fun t ↦ f t r))
    (value : T → ℂ) (hvalue : Continuous value) (degree : ℕ) :
    ∃ a : T → Jet,
      (∀ t k, (a t k).IsHomogeneous k) ∧
      (∀ k, ContinuousPolyFamily (fun t ↦ a t k)) ∧
      (∀ t, a t 0 = C (value t)) ∧
      ∀ t n, n < degree → transportCoefficient (w t) (W t) (c t) (f t) n (a t) = 0 := by
  let initial : T → Jet := fun t k ↦ if k = 0 then C (value t) else 0
  have hinitial : ∀ t k, (initial t k).IsHomogeneous k := by
    intro t k
    dsimp [initial]
    split_ifs with hk
    · subst k; exact isHomogeneous_C _ _
    · exact isHomogeneous_zero _ _ _
  have hic : ∀ k, ContinuousPolyFamily (fun t ↦ initial t k) := by
    intro k
    dsimp [initial]
    split_ifs
    · exact ContinuousPolyFamily.C hvalue
    · exact ContinuousPolyFamily.const _
  let low : T → ℕ → Jet → CPoly := fun t n a ↦
    homogeneousComponent n (transportKnown (W t) (c t) (f t) n a)
  obtain ⟨a, ha, hac, hkeep, hsolve⟩ := finite_triangular_jets_continuous w hw i hi low
    (fun t n a ↦ homogeneousComponent_isHomogeneous _ _)
    (fun t n a b h ↦ congrArg (homogeneousComponent n)
      (transportKnown_congr (W t) (c t) (f t) n a b h))
    (fun n a hac ↦ (transportKnown_family W c f a hW hc hf hac n).homogeneousComponent n)
    initial hinitial hic 0 degree
  refine ⟨a, ha, hac, fun t ↦ by simpa [initial] using hkeep t 0 (by omega), ?_⟩
  intro t n hn
  rw [transportCoefficient_split, map_add,
    homogeneousComponent_eq_self (direction_homogeneous _ (ha t (n + 1)))]
  exact hsolve t n (Nat.zero_le _) (by simpa using hn)

theorem transport_tower_continuous
    (w : T → Fin 4 → ℂ) (hw : ∀ j, Continuous (fun t ↦ w t j))
    (i : Fin 4) (hi : ∀ t, w t i ≠ 0)
    (W : T → ℕ → Fin 4 → CPoly) (c : T → Jet)
    (g : T → ℕ → Fin 4 → Fin 4 → CPoly) (b : T → ℕ → Fin 4 → CPoly)
    (hW : ∀ r i, ContinuousPolyFamily (fun t ↦ W t r i))
    (hc : ∀ r, ContinuousPolyFamily (fun t ↦ c t r))
    (hg : ∀ r i j, ContinuousPolyFamily (fun t ↦ g t r i j))
    (hb : ∀ r i, ContinuousPolyFamily (fun t ↦ b t r i)) (m J : ℕ) :
    ∃ A : ℕ → T → Jet,
      (∀ j t k, (A j t k).IsHomogeneous k) ∧
      (∀ j k, ContinuousPolyFamily (fun t ↦ A j t k)) ∧
      (∀ j t, A j t 0 = if j = 0 then 1 else 0) ∧
      (∀ t n, n < m + 1 + 2 * J →
        transportCoefficient (w t) (W t) (c t) 0 n (A 0 t) = 0) ∧
      ∀ j t n, n < m + 1 + 2 * (J - (j + 1)) →
        transportCoefficient (w t) (W t) (c t)
          (fun k ↦ -secondOrderCoefficient (g t) (b t) (A j t) k) n (A (j + 1) t) = 0 := by
  let Family := {a : T → Jet // (∀ t k, (a t k).IsHomogeneous k) ∧
    ∀ k, ContinuousPolyFamily (fun t ↦ a t k)}
  have hex (f : T → Jet) (hf : ∀ k, ContinuousPolyFamily (fun t ↦ f t k))
      (value : ℂ) (d : ℕ) :=
    finite_transport_jets_continuous w hw i hi W c f hW hc hf
      (fun _ ↦ value) continuous_const d
  let solve (f : T → Jet) (hf : ∀ k, ContinuousPolyFamily (fun t ↦ f t k))
      (value : ℂ) (d : ℕ) : Family :=
    ⟨Classical.choose (hex f hf value d), (Classical.choose_spec (hex f hf value d)).1,
      (Classical.choose_spec (hex f hf value d)).2.1⟩
  have hs (f : T → Jet) (hf : ∀ k, ContinuousPolyFamily (fun t ↦ f t k))
      (value : ℂ) (d : ℕ) := (Classical.choose_spec (hex f hf value d)).2.2
  let A : ℕ → Family := fun j ↦ Nat.rec
    (solve (fun _ ↦ 0) (fun _ ↦ ContinuousPolyFamily.const _) 1 (m + 1 + 2 * J))
    (fun j prev ↦ solve (fun t k ↦ -secondOrderCoefficient (g t) (b t) (prev.val t) k)
      (fun k ↦ (secondOrderCoefficient_family g b prev.val hg hb prev.property.2 k).neg)
      0 (m + 1 + 2 * (J - (j + 1)))) j
  refine ⟨fun j ↦ (A j).val, fun j ↦ (A j).property.1, fun j ↦ (A j).property.2, ?_, ?_, ?_⟩
  · intro j t
    cases j with
    | zero => simpa [A, solve] using (hs (fun _ ↦ 0) (fun _ ↦ ContinuousPolyFamily.const _) 1 _).1 t
    | succ j =>
      exact ((hs (fun t k ↦ -secondOrderCoefficient (g t) (b t) ((A j).val t) k)
        (fun k ↦ (secondOrderCoefficient_family g b (A j).val hg hb (A j).property.2 k).neg)
        0 _).1 t).trans (map_zero C)
  · exact (hs (fun _ ↦ 0) (fun _ ↦ ContinuousPolyFamily.const _) 1 _).2
  · intro j
    exact (hs (fun t k ↦ -secondOrderCoefficient (g t) (b t) ((A j).val t) k)
      (fun k ↦ (secondOrderCoefficient_family g b (A j).val hg hb (A j).property.2 k).neg)
      0 _).2

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_UniformTransportPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

theorem finite_transport_polynomials_continuous
    (w : T → Fin 4 → ℂ) (hw : ∀ j, Continuous (fun t ↦ w t j))
    (i : Fin 4) (hi : ∀ t, w t i ≠ 0)
    (W : T → ℕ → Fin 4 → CPoly) (c : T → Jet)
    (g : T → ℕ → Fin 4 → Fin 4 → CPoly) (b : T → ℕ → Fin 4 → CPoly)
    (hW : ∀ r i, ContinuousPolyFamily (fun t ↦ W t r i))
    (hc : ∀ r, ContinuousPolyFamily (fun t ↦ c t r))
    (hg : ∀ r i j, ContinuousPolyFamily (fun t ↦ g t r i j))
    (hb : ∀ r i, ContinuousPolyFamily (fun t ↦ b t r i)) (m J : ℕ) :
    ∃ P : ℕ → T → CPoly,
      (∀ j, ContinuousPolyFamily (P j)) ∧
      (∀ j t, polynomialJet (P j t) 0 = if j = 0 then 1 else 0) ∧
      (∀ j t k, m + 1 + 2 * (J - j) < k → polynomialJet (P j t) k = 0) ∧
      (∀ t n, n < m + 1 + 2 * J →
        transportCoefficient (w t) (W t) (c t) 0 n (polynomialJet (P 0 t)) = 0) ∧
      ∀ j, j < J → ∀ t n, n < m + 1 + 2 * (J - (j + 1)) →
        transportCoefficient (w t) (W t) (c t)
          (fun k ↦ -secondOrderCoefficient (g t) (b t) (polynomialJet (P j t)) k)
          n (polynomialJet (P (j + 1) t)) = 0 := by
  obtain ⟨A, hA, hAc, hzero, hfirst, hnext⟩ :=
    transport_tower_continuous w hw i hi W c g b hW hc hg hb m J
  let d : ℕ → ℕ := fun j ↦ m + 1 + 2 * (J - j)
  let P : ℕ → T → CPoly := fun j t ↦ truncateJet (A j t) (d j)
  have heq (j : ℕ) (t : T) (k : ℕ) (hk : k ≤ d j) :
      polynomialJet (P j t) k = A j t k := polynomialJet_truncate_eq _ (hA j t) _ _ hk
  refine ⟨P, fun j ↦ ContinuousPolyFamily.sum _ (fun k _ ↦ hAc j k), ?_, ?_, ?_, ?_⟩
  · intro j t
    rw [heq j t 0 (Nat.zero_le _), hzero]
  · intro j t k hk
    exact (polynomialJet_truncate (A j t) (hA j t) _ _).trans (ite_eq_right (by dsimp [d]; omega))
  · intro t n hn
    rw [transportCoefficient_congr (w t) (W t) (c t) 0 0 n _ (A 0 t)
      (fun k hk ↦ heq 0 t k (by dsimp [d]; omega)) rfl]
    exact hfirst t n hn
  · intro j hj t n hn
    have hd : d j = d (j + 1) + 2 := (wave_degree_budgets m J j hj).1
    have hforce : -secondOrderCoefficient (g t) (b t) (polynomialJet (P j t)) n =
        -secondOrderCoefficient (g t) (b t) (A j t) n := by
      rw [secondOrderCoefficient_congr (g t) (b t) _ (A j t) n
        (fun k hk ↦ heq j t k (by dsimp [d] at *; omega))]
    rw [transportCoefficient_congr (w t) (W t) (c t) _
      (fun k ↦ -secondOrderCoefficient (g t) (b t) (A j t) k) n _ (A (j + 1) t)
      (fun k hk ↦ heq (j + 1) t k (by dsimp [d]; omega)) hforce]
    exact hnext j t n hn

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_UniformWaveJet
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

lemma beamVector_family (g : T → Fin 4 → Fin 4 → CPoly) (phi : T → CPoly)
    (hg : ∀ i j, ContinuousPolyFamily (fun t ↦ g t i j))
    (hp : ContinuousPolyFamily phi) (i : Fin 4) :
    ContinuousPolyFamily (fun t ↦ beamVector (g t) (phi t) i) := by
  apply ContinuousPolyFamily.mul (.const _)
  exact ContinuousPolyFamily.sum _ (fun j _ ↦ (hg i j).mul (hp.pderiv j))

lemma secondOrder_family (g : T → Fin 4 → Fin 4 → CPoly)
    (b : T → Fin 4 → CPoly) (phi : T → CPoly)
    (hg : ∀ i j, ContinuousPolyFamily (fun t ↦ g t i j))
    (hb : ∀ i, ContinuousPolyFamily (fun t ↦ b t i))
    (hp : ContinuousPolyFamily phi) :
    ContinuousPolyFamily (fun t ↦ polynomialSecondOrder (g t) (b t) (phi t)) := by
  apply ContinuousPolyFamily.add
  · apply ContinuousPolyFamily.sum
    intro i _
    exact ContinuousPolyFamily.sum _ (fun j _ ↦ (hg i j).mul ((hp.pderiv j).pderiv i))
  · exact ContinuousPolyFamily.sum _ (fun i _ ↦ (hb i).mul (hp.pderiv i))

lemma beamScalar_family (g : T → Fin 4 → Fin 4 → CPoly)
    (b : T → Fin 4 → CPoly) (phi : T → CPoly)
    (hg : ∀ i j, ContinuousPolyFamily (fun t ↦ g t i j))
    (hb : ∀ i, ContinuousPolyFamily (fun t ↦ b t i))
    (hp : ContinuousPolyFamily phi) :
    ContinuousPolyFamily (fun t ↦ beamScalar (g t) (b t) (phi t)) :=
  (secondOrder_family g b phi hg hb hp).add (.const _)

theorem polynomial_wave_jets_continuous
    (v : T → Fin 4 → ℂ) (hv : ∀ j, Continuous (fun t ↦ v t j))
    (i : Fin 4) (hvi : ∀ t, v t i ≠ 0)
    (g : T → Fin 4 → Fin 4 → CPoly) (b : T → Fin 4 → CPoly)
    (hg : ∀ i j, ContinuousPolyFamily (fun t ↦ g t i j))
    (hb : ∀ i, ContinuousPolyFamily (fun t ↦ b t i))
    (hmetric : ∀ t i j, homogeneousComponent 0 (g t i j) = if i = j then 1 else 0)
    (initial : T → Jet) (hi : ∀ t k, (initial t k).IsHomogeneous k)
    (hic : ∀ k, ContinuousPolyFamily (fun t ↦ initial t k))
    (hfirst : ∀ t i, pderiv i (initial t 1) = C (v t i))
    (hcenter : ∀ t, (∑ i, v t i * v t i) + 4 = 0)
    (hsecond : ∀ t, eikonalCoefficient (v t)
      (fun r i j ↦ homogeneousComponent r (g t i j)) 0 (initial t) = 0) (m J : ℕ) :
    ∃ (phi : T → CPoly) (A : ℕ → T → CPoly),
      ContinuousPolyFamily phi ∧ (∀ j, ContinuousPolyFamily (A j)) ∧
      (∀ t k, k ≤ 2 → homogeneousComponent k (phi t) = initial t k) ∧
      (∀ t d, m + 2 * J + 3 < d → homogeneousComponent d (phi t) = 0) ∧
      (∀ t d, d ≤ m + 2 * J + 2 →
        homogeneousComponent d (polynomialEikonal (g t) (phi t)) = 0) ∧
      (∀ j t, homogeneousComponent 0 (A j t) = if j = 0 then 1 else 0) ∧
      (∀ j t k, m + 1 + 2 * (J - j) < k → homogeneousComponent k (A j t) = 0) ∧
      (∀ t n, n < m + 1 + 2 * J → homogeneousComponent n
        (polynomialTransport (beamVector (g t) (phi t)) (beamScalar (g t) (b t) (phi t))
          0 (A 0 t)) = 0) ∧
      ∀ j, j < J → ∀ t n, n < m + 1 + 2 * (J - (j + 1)) → homogeneousComponent n
        (polynomialTransport (beamVector (g t) (phi t)) (beamScalar (g t) (b t) (phi t))
          (-polynomialSecondOrder (g t) (b t) (A j t)) (A (j + 1) t)) = 0 := by
  obtain ⟨phi, hpc, hkeep, hdegree, hsolve, _⟩ := finite_eikonal_polynomial_continuous
    v hv i hvi (fun t r i j ↦ homogeneousComponent r (g t i j))
    (fun r i j ↦ (hg i j).homogeneousComponent r) initial hi hic hsecond (m + 2 * J + 1)
  have hf : ∀ t i, pderiv i (homogeneousComponent 1 (phi t)) = C (v t i) := by
    intro t i
    rw [show homogeneousComponent 1 (phi t) = initial t 1 from hkeep t 1 (by omega), hfirst]
  have he : ∀ t d, d ≤ m + 2 * J + 2 →
      homogeneousComponent d (polynomialEikonal (g t) (phi t)) = 0 := by
    intro t d hd
    cases d with
    | zero =>
      unfold polynomialEikonal
      have hc0 (a b : CPoly) : homogeneousComponent 0 (a * b) =
          homogeneousComponent 0 a * homogeneousComponent 0 b := by
        simpa using homogeneousComponent_mul a b 0
      simp only [map_add, map_sum, hc0, homogeneousComponent_pderiv, Nat.zero_add, hf, hmetric]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
      rw [homogeneousComponent_eq_self (isHomogeneous_C (Fin 4) (4 : ℂ))]
      have h := congrArg (MvPolynomial.C : ℂ →+* CPoly) (hcenter t)
      rw [map_add, map_sum, map_zero] at h
      simpa only [map_mul] using h
    | succ n =>
      rw [← eikonalCoefficient_eq (v t) (g t) (hmetric t) (phi t) (hf t) n]
      exact hsolve t n (by omega)
  have hW := beamVector_family g phi hg hpc
  have hc := beamScalar_family g b phi hg hb hpc
  obtain ⟨A, hAc, hA0, hAd, hAfirst, hAnext⟩ := finite_transport_polynomials_continuous
    (fun t j ↦ 2 * v t j) (fun j ↦ continuous_const.mul (hv j))
    i (fun t ↦ mul_ne_zero (by norm_num) (hvi t))
    (fun t r j ↦ homogeneousComponent r (beamVector (g t) (phi t) j))
    (fun t ↦ polynomialJet (beamScalar (g t) (b t) (phi t)))
    (fun t r i j ↦ homogeneousComponent r (g t i j))
    (fun t r i ↦ homogeneousComponent r (b t i))
    (fun r j ↦ (hW j).homogeneousComponent r) (fun r ↦ hc.homogeneousComponent r)
    (fun r i j ↦ (hg i j).homogeneousComponent r)
    (fun r i ↦ (hb i).homogeneousComponent r) m J
  refine ⟨phi, A, hpc, hAc, hkeep, ?_, he, hA0, hAd, ?_, ?_⟩
  · simpa [Nat.add_assoc, polynomialJet] using hdegree
  · intro t n hn
    rw [← transportCoefficient_eq (fun j ↦ 2 * v t j) _
      (beamVector_center (v t) (g t) (hmetric t) (phi t) (hf t)) _ 0 (A 0 t) n]
    have hz : polynomialJet (0 : CPoly) = (0 : Jet) := funext (fun k ↦ map_zero _)
    rw [hz]
    exact hAfirst t n hn
  · intro j hj t n hn
    rw [← transportCoefficient_eq (fun j ↦ 2 * v t j) _
      (beamVector_center (v t) (g t) (hmetric t) (phi t) (hf t)) _
      (-polynomialSecondOrder (g t) (b t) (A j t)) (A (j + 1) t) n]
    have hforce : polynomialJet (-polynomialSecondOrder (g t) (b t) (A j t)) =
        fun k ↦ -secondOrderCoefficient (fun r i j ↦ homogeneousComponent r (g t i j))
          (fun r i ↦ homogeneousComponent r (b t i)) (polynomialJet (A j t)) k := by
      funext k
      rw [secondOrderCoefficient_eq]
      exact map_neg (homogeneousComponent k) _
    rw [hforce]
    exact hAnext j hj t n hn

theorem smooth_wave_jets_continuous
    (v : T → Fin 4 → ℂ) (hv : ∀ j, Continuous (fun t ↦ v t j))
    (i : Fin 4) (hvi : ∀ t, v t i ≠ 0)
    (g : T → Fin 4 → Fin 4 → Coord → ℂ) (b : T → Fin 4 → Coord → ℂ)
    (G : T → Fin 4 → Fin 4 → CPoly) (B : T → Fin 4 → CPoly)
    (hG : ∀ i j, ContinuousPolyFamily (fun t ↦ G t i j))
    (hB : ∀ i, ContinuousPolyFamily (fun t ↦ B t i))
    (hg : ∀ t i j, ContDiff ℝ ∞ (g t i j)) (hb : ∀ t i, ContDiff ℝ ∞ (b t i))
    (hmetric : ∀ t i j, homogeneousComponent 0 (G t i j) = if i = j then 1 else 0)
    (initial : T → Jet) (hi : ∀ t k, (initial t k).IsHomogeneous k)
    (hic : ∀ k, ContinuousPolyFamily (fun t ↦ initial t k))
    (hfirst : ∀ t i, pderiv i (initial t 1) = C (v t i))
    (hcenter : ∀ t, (∑ i, v t i * v t i) + 4 = 0)
    (hsecond : ∀ t, eikonalCoefficient (v t)
      (fun r i j ↦ homogeneousComponent r (G t i j)) 0 (initial t) = 0) (m J : ℕ)
    (hgj : ∀ t i j, FlatAt m (fun x ↦ g t i j x - reval (G t i j) x) 0)
    (hbj : ∀ t i, FlatAt m (fun x ↦ b t i x - reval (B t i) x) 0) :
    ∃ (phi : T → CPoly) (A : ℕ → T → CPoly),
      ContinuousPolyFamily phi ∧ (∀ j, ContinuousPolyFamily (A j)) ∧
      (∀ t k, k ≤ 2 → homogeneousComponent k (phi t) = initial t k) ∧
      (∀ t d, m + 2 * J + 3 < d → homogeneousComponent d (phi t) = 0) ∧
      (∀ j t, homogeneousComponent 0 (A j t) = if j = 0 then 1 else 0) ∧
      (∀ j t k, m + 1 + 2 * (J - j) < k → homogeneousComponent k (A j t) = 0) ∧
      (∀ t, FlatAt m (smoothEikonal (g t) (reval (phi t))) 0) ∧
      (∀ t, FlatAt m (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
        (smoothBeamScalar (g t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A 0 t))) 0) ∧
      ∀ j, j < J → ∀ t, FlatAt m
        (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
          (smoothBeamScalar (g t) (b t) (reval (phi t)))
          (fun x ↦ -smoothSecondOrder (g t) (b t) (reval (A j t)) x)
          (reval (A (j + 1) t))) 0 := by
  obtain ⟨phi, A, hpc, hAc, hkeep, hdeg, he, hA0, hAd, ht0, htj⟩ :=
    polynomial_wave_jets_continuous v hv i hvi G B hG hB hmetric initial hi hic
      hfirst hcenter hsecond m J
  refine ⟨phi, A, hpc, hAc, hkeep, hdeg, hA0, hAd, ?_, ?_, ?_⟩
  · intro t
    exact smooth_eikonal_flat (G t) (phi t) (hg t) (hgj t) (fun k hk ↦ he t k (by omega))
  · intro t
    have hp : ∀ k, k ≤ m → homogeneousComponent k
        (polynomialTransport (beamVector (G t) (phi t)) (beamScalar (G t) (B t) (phi t))
          (-polynomialSecondOrder (G t) (B t) 0) (A 0 t)) = 0 := by
      intro k hk
      simpa [polynomialSecondOrder] using ht0 t k (by omega)
    have h := smooth_beam_transport_flat (G t) (B t) (phi t) 0 (A 0 t)
      (hg t) (hb t) (hgj t) (hbj t) hp
    have hz : (fun x ↦ -smoothSecondOrder (g t) (b t) (reval 0) x) = fun _ ↦ 0 := by
      ext x
      simp [smoothSecondOrder, coordPartial_reval, reval]
    rw [hz] at h
    exact h
  · intro j hj t
    exact smooth_beam_transport_flat (G t) (B t) (phi t) (A j t) (A (j + 1) t)
      (hg t) (hb t) (hgj t) (hbj t) (fun k hk ↦ htj j hj t k (by omega))

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Waves_NormalFrameWaveJet
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

theorem normal_frame_smooth_wave_jets_continuous
    (a bb S : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hbb : Continuous bb) (hS : Continuous S)
    (hHc : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) (hbb0 : ∀ t, bb t ≠ 0)
    (hlen : ∀ t, bb t ^ 2 = a t ^ 2 + 4) (hH : ∀ t i j, H t i j = H t j i)
    (g : T → Fin 4 → Fin 4 → Coord → ℂ) (b : T → Fin 4 → Coord → ℂ)
    (G : T → Fin 4 → Fin 4 → CPoly) (B : T → Fin 4 → CPoly)
    (hG : ∀ i j, ContinuousPolyFamily (fun t ↦ G t i j))
    (hB : ∀ i, ContinuousPolyFamily (fun t ↦ B t i))
    (hg : ∀ t i j, ContDiff ℝ ∞ (g t i j)) (hb : ∀ t i, ContDiff ℝ ∞ (b t i))
    (hmetric : ∀ t i j, homogeneousComponent 0 (G t i j) = if i = j then 1 else 0)
    (hmetricFirst : ∀ t i j, homogeneousComponent 1 (G t i j) = 0) (m J : ℕ)
    (hgj : ∀ t i j, FlatAt m (fun x ↦ g t i j x - reval (G t i j) x) 0)
    (hbj : ∀ t i, FlatAt m (fun x ↦ b t i x - reval (B t i) x) 0) :
    ∃ (phi : T → CPoly) (A : ℕ → T → CPoly),
      ContinuousPolyFamily phi ∧ (∀ j, ContinuousPolyFamily (A j)) ∧
      (∀ t k, k ≤ 2 → homogeneousComponent k (phi t) = initialPhaseJet (S t) (normalFrameVector (a t) (bb t))
        (normalComplexHessian (a t) (bb t) (H t)) k) ∧
      (∀ t d, m + 2 * J + 3 < d → homogeneousComponent d (phi t) = 0) ∧
      (∀ j t, homogeneousComponent 0 (A j t) = if j = 0 then 1 else 0) ∧
      (∀ j t k, m + 1 + 2 * (J - j) < k → homogeneousComponent k (A j t) = 0) ∧
      (∀ t, FlatAt m (smoothEikonal (g t) (reval (phi t))) 0) ∧
      (∀ t, FlatAt m (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
        (smoothBeamScalar (g t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A 0 t))) 0) ∧
      ∀ j, j < J → ∀ t, FlatAt m
        (smoothTransport (smoothBeamVector (g t) (reval (phi t)))
          (smoothBeamScalar (g t) (b t) (reval (phi t)))
          (fun x ↦ -smoothSecondOrder (g t) (b t) (reval (A j t)) x)
          (reval (A (j + 1) t))) 0 := by
  apply smooth_wave_jets_continuous (fun t ↦ normalFrameVector (a t) (bb t))
    (normalFrameVector_continuous a bb ha hbb) 0
    (fun t ↦ by simpa [normalFrameVector] using (Complex.ofReal_ne_zero.mpr (ha0 t)))
    g b G B hG hB hg hb hmetric
    (fun t ↦ initialPhaseJet (S t) (normalFrameVector (a t) (bb t))
      (normalComplexHessian (a t) (bb t) (H t)))
    (fun t k ↦ initialPhaseJet_homogeneous _ _ _ k)
    (normal_frame_initial_jets_continuous a bb S H ha hbb hS hHc ha0 hbb0)
    (fun t i ↦ initialPhaseJet_first _ _ _ i)
    (fun t ↦ normalFrameVector_null (hlen t))
    (fun t ↦ initialPhaseJet_second _ _ _
      (normalComplexHessian_symmetric (ha0 t) (hbb0 t) (H t) (hH t))
      (normalComplexHessian_contract (ha0 t) (hbb0 t) (H t))
      (fun r i j ↦ homogeneousComponent r (G t i j)) (hmetricFirst t)) m J hgj hbj

end
end Yau.Jets

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Coefficients_ComplexChartCoefficient
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

variable {T : Type*} [TopologicalSpace T]

theorem parametric_taylor_family (f : T → _root_.OAI.Yau.Jets.Coord → ℂ)
    (hc : ∀ k, Continuous (fun z : T × _root_.OAI.Yau.Jets.Coord ↦ iteratedFDeriv ℝ k (f z.1) z.2)) (m : ℕ) :
    ContinuousPolyFamily (fun t ↦ taylorPolynomial (f t) 0 m) := by
  unfold taylorPolynomial
  apply ContinuousPolyFamily.sum
  intro k _
  exact (ContinuousPolyFamily.const _).mul (tensorPolynomial_family _
    ((hc k).comp (continuous_id.prodMk continuous_const)))

end
end Yau.Geometry

end OAI
end

section
-- module Solutions.OAIQ237_NY.NodalSets_Elliptic_CompactNormalOperator
attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Set
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

omit [CompactSpace T] in
theorem NormalOperatorFamily.matching_taylor
    {a : T → Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ} {b : T → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ}
    (h : NormalOperatorFamily a b) (m : ℕ) (hm : 1 ≤ m) :
    let A := fun t i j ↦ taylorPolynomial (a t i j) 0 m
    let B := fun t j ↦ taylorPolynomial (b t j) 0 m
    (∀ i j, ContinuousPolyFamily (fun t ↦ A t i j)) ∧
    (∀ j, ContinuousPolyFamily (fun t ↦ B t j)) ∧
    (∀ t i j, MvPolynomial.homogeneousComponent 0 (A t i j) = if i=j then 1 else 0) ∧
    (∀ t i j, MvPolynomial.homogeneousComponent 1 (A t i j) = 0) ∧
    (∀ t i j, FlatAt m (fun x ↦ a t i j x-reval (A t i j) x) 0) ∧
    ∀ t j, FlatAt m (fun x ↦ b t j x-reval (B t j) x) 0 := by
  dsimp only
  have hmets (t : T) := normal_metric_matching_taylor (a t) (h.principal_smooth t)
    (h.normal_value t) (h.normal_first t) m hm
  exact ⟨fun i j ↦ parametric_taylor_family _ (fun k ↦ h.principal_jets k i j) m,
    fun j ↦ parametric_taylor_family _ (fun k ↦ h.drift_jets k j) m,
    fun t ↦ (hmets t).1,fun t ↦ (hmets t).2.1,fun t ↦ (hmets t).2.2,
    fun t j ↦ flatAt_taylorPolynomial (h.drift_smooth t j) m⟩

end
end Yau.Geometry

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

omit [CompactSpace T] in
theorem NormalOperatorFamily.solve_jets_oai
    {G : T → Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ} {b : T → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ}
    (hG : NormalOperatorFamily G b) (a bb s : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hbb : Continuous bb) (hs : Continuous s)
    (hHc : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0)
    (hlen : ∀ t, bb t^2 = a t^2+4) (hH : ∀ t i j, H t i j = H t j i)
    (m J : ℕ) (hm : 1 ≤ m) :
    ∃ phi A, MetricWaveJetFamily G b s a bb H m J phi A := by
  obtain ⟨hAc,hBc,hA0,hA1,hAj,hBj⟩ := hG.matching_taylor m hm
  obtain ⟨phi,A,hp,hA,hkeep,hdeg,hv,had,hE,hT,hTj⟩ := normal_frame_smooth_wave_jets_continuous
    a bb s H ha hbb hs hHc ha0 hb0 hlen hH G b
    (fun t i j ↦ taylorPolynomial (G t i j) 0 m)
    (fun t j ↦ taylorPolynomial (b t j) 0 m) hAc hBc hG.principal_smooth hG.drift_smooth
    hA0 hA1 m J hAj hBj
  exact ⟨phi,A,⟨hp,hA,hkeep,hdeg,hv,had,hE,hT,hTj⟩⟩

end
end Yau.Geometry

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Yau.Geometry.NormalOperatorFamily.solve_jets_oai.{u_1} := @OAI.Yau.Geometry.NormalOperatorFamily.solve_jets_oai.{u_1}
