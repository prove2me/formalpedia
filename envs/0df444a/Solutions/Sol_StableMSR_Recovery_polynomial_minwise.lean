-- Prove2me | solution 1 for StableMSR.Recovery.polynomial_minwise
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T15:23:55.336787+00:00
-- url     : https://prove2.me/submissions/9b24e110-36eb-488a-904a-0e3ae272d20d

/-
Explicit fixed-degree polynomial minwise bound
Source: Exact Sum-of-Radii Clustering under Any Constant Stability,
Appendix B (https://arxiv.org/html/2611.03547v1).

Lean leanprover/lean4:v4.33.1
Mathlib 0df444a360eaa60ab8c11dca51a86af692955474

This proof derives the finite minwise estimate from interpolation, finite
joint-value counts, conditional binomial/fourth-moment estimates, and a
finite numerical sum bound. No Indyk/minwise theorem is assumed. The theorem
uses a given prime q satisfying q>=8193 and q>=4m^2. It counts all q^8193
coefficient seeds, including seeds inducing identical orders, and makes no
claim that their enumeration is implemented in the clustering RAM model.
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic




set_option autoImplicit false
open scoped Classical BigOperators

namespace StableMSR.Recovery.Derandomization

/-- Evaluation on s distinct field elements is a bijection from the first |s| coefficients
onto arbitrary |s|-tuples of field values. -/
noncomputable def coefficientEvaluation {F : Type*} [Field F] (s : Finset F) :
    (Fin s.card → F) ≃ (s → F) :=
  (Polynomial.degreeLTEquiv F s.card).symm.toEquiv.trans
    (Lagrange.funEquivDegreeLT (s := s) (v := fun x : F => x) (by intro x _ y _ h; exact h)).toEquiv

lemma coefficientEvaluation_apply {F : Type*} [Field F] (s : Finset F)
    (a : Fin s.card → F) (x : s) :
    coefficientEvaluation s a x = ∑ i : Fin s.card, a i * (x : F) ^ (i : ℕ) := by
  let p := (Polynomial.degreeLTEquiv F s.card).symm a
  change p.val.eval (x : F) = _
  rw [Polynomial.eval_eq_sum_degreeLTEquiv p.property]
  change (∑ i : Fin s.card,
    ((Polynomial.degreeLTEquiv F s.card) ((Polynomial.degreeLTEquiv F s.card).symm a)) i *
      (x : F) ^ (i : ℕ)) = _
  simp

/-- Every joint value assignment has exactly one coefficient preimage.
This is the finite counting content of |s|-wise uniform polynomial hashing. -/
theorem polynomialHash_joint_unique {F : Type*} [Field F] (s : Finset F) (v : s → F) :
    ∃! a : Fin s.card → F,
      ∀ x : s, (∑ i : Fin s.card, a i * (x : F) ^ (i : ℕ)) = v x := by
  refine ⟨(coefficientEvaluation s).symm v, ?_, ?_⟩
  · intro x
    rw [← coefficientEvaluation_apply]
    exact congrFun ((coefficientEvaluation s).apply_symm_apply v) x
  · intro a ha
    apply (coefficientEvaluation s).injective
    funext x
    rw [coefficientEvaluation_apply]
    rw [ha x]
    exact (congrFun ((coefficientEvaluation s).apply_symm_apply v) x).symm

/-- Enumerating the coefficients uniformly realizes each complete joint value tuple once. -/
theorem polynomialHash_joint_count {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (s : Finset F) (v : s → F) :
    ((Finset.univ : Finset (Fin s.card → F)).filter
      (fun a => ∀ x : s, (∑ i : Fin s.card, a i * (x : F) ^ (i : ℕ)) = v x)).card = 1 := by
  exact (Fintype.existsUnique_iff_card_one _).mp (polynomialHash_joint_unique s v)

/-- Thus the joint probability equals q^(-|s|), the product of |s| uniform marginals. -/
theorem polynomialHash_joint_probability {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (s : Finset F) (v : s → F) :
    (((Finset.univ : Finset (Fin s.card → F)).filter
      (fun a => ∀ x : s, (∑ i : Fin s.card, a i * (x : F) ^ (i : ℕ)) = v x)).card : ℝ) /
      (Fintype.card (Fin s.card → F) : ℝ) = 1 / (Fintype.card F : ℝ) ^ s.card := by
  rw [polynomialHash_joint_count]
  simp [Fintype.card_fun]

end StableMSR.Recovery.Derandomization



set_option autoImplicit false
open scoped Classical BigOperators

namespace StableMSR.Recovery.Derandomization

/-- Fixing the values on T leaves precisely the values on U minus T free. -/
noncomputable def extensionFiberEquiv {F : Type*} [DecidableEq F] (T U : Finset F)
    (hTU : T ⊆ U) (v : T → F) :
    {f : U → F // ∀ x : T, f ⟨x, hTU x.property⟩ = v x} ≃ ((U \ T : Finset F) → F) where
  toFun f x := f.val ⟨x, (Finset.mem_sdiff.mp x.property).1⟩
  invFun g := ⟨fun x => if h : x.val ∈ T then v ⟨x, h⟩
    else g ⟨x, Finset.mem_sdiff.mpr ⟨x.property, h⟩⟩, by
      intro x
      simp only [dif_pos x.property]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    by_cases hx : x.val ∈ T
    · simp only [dif_pos hx]
      exact (f.property ⟨x, hx⟩).symm
    · simp only [dif_neg hx]
  right_inv g := by
    funext x
    simp only [dif_neg (Finset.mem_sdiff.mp x.property).2]

/-- Padding T to a set of size ℓ makes interpolation a bijection; its unconstrained
values count the coefficient vectors realizing any prescribed marginal. -/
theorem polynomialHash_marginal_count {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ℓ : ℕ) (T : Finset F) (hT : T.card ≤ ℓ) (hℓ : ℓ ≤ Fintype.card F)
    (v : T → F) :
    ((Finset.univ : Finset (Fin ℓ → F)).filter
      (fun a => ∀ x : T, (∑ i : Fin ℓ, a i * (x : F) ^ (i : ℕ)) = v x)).card =
      Fintype.card F ^ (ℓ - T.card) := by
  obtain ⟨U, hTU, _, hU⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ T) hT (by simpa only [Finset.card_univ] using hℓ)
  subst ℓ
  let e : {a : Fin U.card → F //
        ∀ x : T, (∑ i : Fin U.card, a i * (x : F) ^ (i : ℕ)) = v x} ≃
      {f : U → F // ∀ x : T, f ⟨x, hTU x.property⟩ = v x} :=
    (coefficientEvaluation U).subtypeEquiv (by
      intro a
      simp only [coefficientEvaluation_apply])
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (e.trans (extensionFiberEquiv T U hTU v))]
  rw [Fintype.card_fun, Fintype.card_coe, Finset.card_sdiff_of_subset hTU]

/-- Uniformly enumerating all ℓ coefficients has uniform joint marginals on every
set of at most ℓ distinct field points, using the same fixed coefficient family. -/
theorem polynomialHash_marginal_probability {F : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    (ℓ : ℕ) (T : Finset F) (hT : T.card ≤ ℓ) (hℓ : ℓ ≤ Fintype.card F)
    (v : T → F) :
    (((Finset.univ : Finset (Fin ℓ → F)).filter
      (fun a => ∀ x : T, (∑ i : Fin ℓ, a i * (x : F) ^ (i : ℕ)) = v x)).card : ℝ) /
      (Fintype.card (Fin ℓ → F) : ℝ) = 1 / (Fintype.card F : ℝ) ^ T.card := by
  rw [polynomialHash_marginal_count ℓ T hT hℓ v]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card F ≠ 0)
  have hp : (Fintype.card F : ℝ) ^ ℓ =
      (Fintype.card F : ℝ) ^ (ℓ - T.card) * (Fintype.card F : ℝ) ^ T.card := by
    rw [← pow_add, Nat.sub_add_cancel hT]
  rw [hp, div_mul_cancel_left₀ (pow_ne_zero _ hq), one_div]

end StableMSR.Recovery.Derandomization



set_option autoImplicit false
open scoped Classical BigOperators

namespace StableMSR.Recovery.Derandomization
namespace FourthMoment

/-- Uniform finite expectation over the actual enumerated seeds. -/
noncomputable def average {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

lemma average_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    average (fun ω => f ω + g ω) = average f + average g := by
  simp only [average, Finset.sum_add_distrib, add_div]

lemma average_mul {Ω : Type*} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    average (fun ω => a * f ω) = a * average f := by
  simp only [average, ← Finset.mul_sum, mul_div_assoc]

lemma average_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    average (fun _ : Ω => a) = a := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω ≠ 0)
  simp [average, nsmul_eq_mul, hn]

lemma average_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : average f ≤ average g := by
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω))
  positivity

lemma average_sum {Ω I : Type*} [Fintype Ω] [Fintype I] (f : I → Ω → ℝ) :
    average (fun ω => ∑ i, f i ω) = ∑ i, average (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

/-- Injective tuples of hits are exactly embeddings into the finite hit set. -/
noncomputable def hitTupleEquiv {I : Type*} (H : Finset I) (r : ℕ) :
    {e : Fin r ↪ I // ∀ j, e j ∈ H} ≃ (Fin r ↪ H) where
  toFun e := ⟨fun j => ⟨e.val j, e.property j⟩, by
    intro i j hij
    exact e.val.injective (congrArg Subtype.val hij)⟩
  invFun e := ⟨⟨fun j => (e j).val, by
    intro i j hij
    exact e.injective (Subtype.ext hij)⟩, fun j => (e j).property⟩
  left_inv e := by
    apply Subtype.ext
    apply DFunLike.ext
    intro j
    rfl
  right_inv e := by
    apply DFunLike.ext
    intro j
    rfl

lemma falling_count_eq_sum {I : Type*} [Fintype I] (H : Finset I) (r : ℕ) :
    (H.card.descFactorial r : ℝ) =
      ∑ e : Fin r ↪ I, if ∀ j, e j ∈ H then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole, ← Fintype.card_subtype]
  rw [Fintype.card_congr (hitTupleEquiv H r), Fintype.card_embedding_eq,
    Fintype.card_coe, Fintype.card_fin]

/-- Joint hit probabilities on distinct r-tuples determine the r-th factorial moment. -/
lemma factorial_moment_of_joint_hits {Ω I : Type*} [Fintype Ω] [Fintype I]
    (H : Ω → Finset I) (r : ℕ) (p : ℝ)
    (hjoint : ∀ e : Fin r ↪ I,
      average (fun ω => if ∀ j, e j ∈ H ω then (1 : ℝ) else 0) = p ^ r) :
    average (fun ω => ((H ω).card.descFactorial r : ℝ)) =
      (Fintype.card I).descFactorial r * p ^ r := by
  simp_rw [falling_count_eq_sum]
  rw [average_sum]
  simp only [hjoint, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_embedding_eq, Fintype.card_fin]

/-- The corresponding binomial moment, at arbitrary order, follows by dividing
the injective-tuple count by the number of orderings of each subset. -/
lemma binomial_moment_of_joint_hits {Ω I : Type*} [Fintype Ω] [Fintype I]
    (H : Ω → Finset I) (r : ℕ) (p : ℝ)
    (hjoint : ∀ e : Fin r ↪ I,
      average (fun ω => if ∀ j, e j ∈ H ω then (1 : ℝ) else 0) = p ^ r) :
    average (fun ω => ((H ω).card.choose r : ℝ)) =
      (Fintype.card I).choose r * p ^ r := by
  have h := factorial_moment_of_joint_hits H r p hjoint
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul] at h
  rw [average_mul] at h
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  apply (mul_left_cancel₀ hfac)
  simpa only [mul_assoc] using h

/-- Uniform joint hits through order k give all binomial moments through order k,
including the zeroth moment, for the genuine cardinality of the hit set. -/
theorem binomial_moments_of_joint_hits_up_to {Ω I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype I]
    (H : Ω → Finset I) (k : ℕ) (p : ℝ)
    (hjoint : ∀ r : ℕ, 1 ≤ r → r ≤ k → ∀ e : Fin r ↪ I,
      average (fun ω => if ∀ j, e j ∈ H ω then (1 : ℝ) else 0) = p ^ r) :
    ∀ r ≤ k, average (fun ω => ((H ω).card.choose r : ℝ)) =
      (Fintype.card I).choose r * p ^ r := by
  intro r hr
  by_cases hz : r = 0
  · subst r
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, average_const]
  · exact binomial_moment_of_joint_hits H r p
      (hjoint r (Nat.one_le_iff_ne_zero.mpr hz) hr)

lemma cast_descFactorial_three (N : ℕ) :
    (N.descFactorial 3 : ℝ) = (N : ℝ) * (N - 1) * (N - 2) := by
  cases N with
  | zero => norm_num
  | succ N =>
      rw [Nat.succ_descFactorial_succ N 2, Nat.cast_mul, Nat.cast_descFactorial_two]
      push_cast
      ring

lemma cast_descFactorial_four (N : ℕ) :
    (N.descFactorial 4 : ℝ) = (N : ℝ) * (N - 1) * (N - 2) * (N - 3) := by
  cases N with
  | zero => norm_num
  | succ N =>
      rw [Nat.succ_descFactorial_succ N 3, Nat.cast_mul, cast_descFactorial_three]
      push_cast
      ring

/-- This algebraic interface states the first four factorial moments explicitly.
It is the moment information furnished by four-wise uniform Bernoulli hits; the
theorems below do not assume a central-moment or tail bound. -/
structure FactorialMoments4 {Ω : Type*} [Fintype Ω] (Z : Ω → ℝ) (N : ℕ) (p : ℝ) : Prop where
  first : average Z = (N : ℝ) * p
  second : average (fun ω => Z ω * (Z ω - 1)) = (N : ℝ) * (N - 1) * p ^ 2
  third : average (fun ω => Z ω * (Z ω - 1) * (Z ω - 2)) =
    (N : ℝ) * (N - 1) * (N - 2) * p ^ 3
  fourth : average (fun ω => Z ω * (Z ω - 1) * (Z ω - 2) * (Z ω - 3)) =
    (N : ℝ) * (N - 1) * (N - 2) * (N - 3) * p ^ 4

/-- Four-wise uniform hit events supply the factorial-moment interface for their
actual finite hit count; the hypothesis only concerns distinct joint hit events. -/
theorem factorialMoments4_of_joint_hits {Ω I : Type*} [Fintype Ω] [Fintype I]
    (H : Ω → Finset I) (p : ℝ)
    (hjoint : ∀ r : ℕ, 1 ≤ r → r ≤ 4 → ∀ e : Fin r ↪ I,
      average (fun ω => if ∀ j, e j ∈ H ω then (1 : ℝ) else 0) = p ^ r) :
    FactorialMoments4 (fun ω => ((H ω).card : ℝ)) (Fintype.card I) p := by
  constructor
  · simpa only [Nat.descFactorial_one, pow_one] using
      factorial_moment_of_joint_hits H 1 p (hjoint 1 (by decide) (by decide))
  · simpa only [Nat.cast_descFactorial_two] using
      factorial_moment_of_joint_hits H 2 p (hjoint 2 (by decide) (by decide))
  · simpa only [cast_descFactorial_three] using
      factorial_moment_of_joint_hits H 3 p (hjoint 3 (by decide) (by decide))
  · simpa only [cast_descFactorial_four] using
      factorial_moment_of_joint_hits H 4 p (hjoint 4 (by decide) (by decide))

/-- The fourth central moment is determined by factorial moments through order four. -/
theorem central_fourth_eq {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Z : Ω → ℝ) (N : ℕ) (p : ℝ) (h : FactorialMoments4 Z N p) :
    average (fun ω => (Z ω - (N : ℝ) * p) ^ 4) =
      3 * ((N : ℝ) * p) ^ 2 * (1 - p) ^ 2 +
        ((N : ℝ) * p) * (1 - p) * (1 - 6 * p * (1 - p)) := by
  let μ : ℝ := (N : ℝ) * p
  have hpoly : (fun ω => (Z ω - μ) ^ 4) = (fun ω =>
      Z ω * (Z ω - 1) * (Z ω - 2) * (Z ω - 3) +
      (6 - 4 * μ) * (Z ω * (Z ω - 1) * (Z ω - 2)) +
      (7 - 12 * μ + 6 * μ ^ 2) * (Z ω * (Z ω - 1)) +
      (1 - 4 * μ + 6 * μ ^ 2 - 4 * μ ^ 3) * Z ω + μ ^ 4) := by
    funext ω
    ring
  change average (fun ω => (Z ω - μ) ^ 4) = _
  rw [hpoly]
  simp only [average_add, average_mul, average_const, h.first, h.second, h.third, h.fourth]
  dsimp [μ]
  ring

/-- A Bernoulli count with the stated four factorial moments obeys the standard
fourth-moment estimate 3μ²+μ. -/
theorem central_fourth_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Z : Ω → ℝ) (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (h : FactorialMoments4 Z N p) :
    average (fun ω => (Z ω - (N : ℝ) * p) ^ 4) ≤
      3 * ((N : ℝ) * p) ^ 2 + (N : ℝ) * p := by
  rw [central_fourth_eq Z N p h]
  have hμ : 0 ≤ (N : ℝ) * p := mul_nonneg (Nat.cast_nonneg N) hp
  have h₁ : 0 ≤ 3 * ((N : ℝ) * p) ^ 2 * p * (2 - p) := by
    apply mul_nonneg
    · positivity
    · linarith
  have h₂ : 0 ≤ ((N : ℝ) * p) * p * (1 + 6 * (1 - p) ^ 2) := by positivity
  nlinarith

/-- Pointwise fourth-power domination turns the central moment into a zero-hit bound. -/
theorem zero_probability_le_central_fourth {Ω : Type*} [Fintype Ω]
    (Z : Ω → ℝ) (μ : ℝ) (hμ : 0 < μ) :
    (((Finset.univ : Finset Ω).filter (fun ω => Z ω = 0)).card : ℝ) /
        (Fintype.card Ω : ℝ) ≤ average (fun ω => (Z ω - μ) ^ 4) / μ ^ 4 := by
  have hpoint : ∀ ω, μ ^ 4 * (if Z ω = 0 then (1 : ℝ) else 0) ≤ (Z ω - μ) ^ 4 := by
    intro ω
    by_cases hz : Z ω = 0
    · simp [hz]
      ring_nf
      exact le_rfl
    · simp only [if_neg hz, mul_zero]
      positivity
  have hav := average_mono hpoint
  rw [average_mul] at hav
  have hevent : average (fun ω => if Z ω = 0 then (1 : ℝ) else 0) =
      (((Finset.univ : Finset Ω).filter (fun ω => Z ω = 0)).card : ℝ) /
        (Fintype.card Ω : ℝ) := by simp only [average, Finset.sum_boole]
  rw [hevent] at hav
  apply (le_div_iff₀ (pow_pos hμ 4)).2
  simpa only [mul_comm] using hav

/-- The fourth factorial-moment identities yield Pr[Z=0] ≤ 3/μ²+1/μ³.
All probabilities here are literal finite seed counts divided by the seed count. -/
theorem zero_probability_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Z : Ω → ℝ) (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (h : FactorialMoments4 Z N p) (hμ : 0 < (N : ℝ) * p) :
    (((Finset.univ : Finset Ω).filter (fun ω => Z ω = 0)).card : ℝ) /
        (Fintype.card Ω : ℝ) ≤
      3 / ((N : ℝ) * p) ^ 2 + 1 / ((N : ℝ) * p) ^ 3 := by
  calc
    _ ≤ average (fun ω => (Z ω - (N : ℝ) * p) ^ 4) / ((N : ℝ) * p) ^ 4 :=
      zero_probability_le_central_fourth Z _ hμ
    _ ≤ (3 * ((N : ℝ) * p) ^ 2 + (N : ℝ) * p) / ((N : ℝ) * p) ^ 4 :=
      div_le_div_of_nonneg_right (central_fourth_le Z N p hp hpone h) (by positivity)
    _ = _ := by
      have hn : (N : ℝ) * p ≠ 0 := ne_of_gt hμ
      field_simp

/-- A finite four-wise uniform Bernoulli hit family has the claimed zero-hit tail. -/
theorem no_hit_probability_le_of_fourwise {Ω I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype I]
    (H : Ω → Finset I) (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (hjoint : ∀ r : ℕ, 1 ≤ r → r ≤ 4 → ∀ e : Fin r ↪ I,
      average (fun ω => if ∀ j, e j ∈ H ω then (1 : ℝ) else 0) = p ^ r)
    (hμ : 0 < (Fintype.card I : ℝ) * p) :
    (((Finset.univ : Finset Ω).filter (fun ω => H ω = ∅)).card : ℝ) /
        (Fintype.card Ω : ℝ) ≤
      3 / ((Fintype.card I : ℝ) * p) ^ 2 + 1 / ((Fintype.card I : ℝ) * p) ^ 3 := by
  simpa only [Nat.cast_eq_zero, Finset.card_eq_zero] using
    zero_probability_le (fun ω => ((H ω).card : ℝ)) (Fintype.card I) p hp hpone
      (factorialMoments4_of_joint_hits H p hjoint) hμ

end FourthMoment
end StableMSR.Recovery.Derandomization



set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped Classical BigOperators

namespace StableMSR.Recovery.Derandomization
namespace Conditional

noncomputable def probability {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω

lemma probability_eq_average {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] :
    probability P = FourthMoment.average (fun ω => if P ω then 1 else 0) := by
  simp only [probability, FourthMoment.average, Finset.sum_boole]

lemma probability_congr {Ω : Type*} [Fintype Ω] {P Q : Ω → Prop}
    [DecidablePred P] [DecidablePred Q] (hpq : ∀ ω, P ω ↔ Q ω) :
    probability P = probability Q := by
  have hf : (Finset.univ.filter P) = (Finset.univ.filter Q) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpq ω]
  unfold probability
  rw [hf]

lemma probability_map_mem {Ω V : Type*} [Fintype Ω] [DecidableEq V]
    (f : Ω → V) (S : Finset V) :
    probability (fun ω => f ω ∈ S) = ∑ v ∈ S, probability (fun ω => f ω = v) := by
  classical
  unfold probability
  have hc := Finset.sum_card_fiberwise_eq_card_filter Finset.univ S f
  have hr := congrArg (fun n : ℕ => (n : ℝ) / Fintype.card Ω) hc
  simpa only [Nat.cast_sum, Finset.sum_div] using hr.symm

/-- Joint uniformity is stated as literal counts in the enumerated finite seed family. -/
def Uniform {Ω J : Type*} [Fintype Ω] [Fintype J] {q : ℕ}
    (h : Ω → J → Fin q) : Prop :=
  ∀ v : J → Fin q, probability (fun ω => h ω = v) = 1 / (q : ℝ) ^ Fintype.card J

lemma rectangle_probability {Ω J : Type*} [Fintype Ω] [Fintype J] {q : ℕ}
    (h : Ω → J → Fin q) (hu : Uniform h) (A : J → Finset (Fin q)) :
    probability (fun ω => ∀ j, h ω j ∈ A j) =
      (∏ j, ((A j).card : ℝ)) / (q : ℝ) ^ Fintype.card J := by
  have hmem : (fun ω => ∀ j, h ω j ∈ A j) =
      (fun ω => h ω ∈ Fintype.piFinset A) := by
    funext ω
    exact propext Fintype.mem_piFinset.symm
  simp only [hmem]
  rw [probability_map_mem]
  have huv : ∀ v, probability (fun ω => h ω = v) =
      1 / (q : ℝ) ^ Fintype.card J := hu
  simp only [huv, Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset,
    Nat.cast_prod, mul_one_div]

lemma conditional_probability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P Q : Ω → Prop) [DecidablePred P] [DecidablePred Q] :
    probability (fun ω : {ω // P ω} => Q ω.val) =
      probability (fun ω => P ω ∧ Q ω) / probability P := by
  let he : {ω : {ω // P ω} // Q ω.val} ≃ {ω // P ω ∧ Q ω} := {
    toFun ω := ⟨ω.val.val, ω.val.property, ω.property⟩
    invFun ω := ⟨⟨ω.val, ω.property.1⟩, ω.property.2⟩
    left_inv ω := rfl
    right_inv ω := rfl }
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω ≠ 0)
  simp only [probability, ← Fintype.card_subtype]
  rw [Fintype.card_congr he]
  rw [div_div_div_cancel_right₀ hn]

lemma singleton_probability {Ω J : Type*} [Fintype Ω] [Fintype J] {q : ℕ}
    (hq : 0 < q) (h : Ω → Option J → Fin q) (hu : Uniform h) (i : Fin q) :
    probability (fun ω => h ω none = i) = 1 / (q : ℝ) := by
  let A : Option J → Finset (Fin q) := fun j => match j with
    | none => {i}
    | some _ => Finset.univ
  have hr := rectangle_probability h hu A
  have he : (fun ω => ∀ j, h ω j ∈ A j) = (fun ω => h ω none = i) := by
    funext ω
    apply propext
    constructor
    · intro hall
      simpa [A] using hall none
    · intro hi j
      cases j with
      | none => simpa [A] using hi
      | some j => simp [A]
  simp only [he] at hr
  simp only [Fintype.prod_option, A, Finset.card_singleton, Nat.cast_one,
    Finset.card_univ, Fintype.card_fin, Finset.prod_const, Finset.card_univ,
    one_mul, Fintype.card_option, pow_succ] at hr
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [div_mul_cancel_left₀ (pow_ne_zero _ hq0), ← one_div] at hr
  exact hr

lemma fiber_nonempty {Ω J : Type*} [Fintype Ω] [Nonempty Ω] [Fintype J] {q : ℕ}
    (hq : 0 < q) (h : Ω → Option J → Fin q) (hu : Uniform h) (i : Fin q) :
    Nonempty {ω // h ω none = i} := by
  classical
  have hp := singleton_probability hq h hu i
  have hpos : 0 < probability (fun ω => h ω none = i) := by
    rw [hp]
    exact one_div_pos.mpr (Nat.cast_pos.mpr hq)
  unfold probability at hpos
  have hc : 0 < ((Finset.univ.filter (fun ω => h ω none = i)).card : ℝ) :=
    (div_pos_iff_of_pos_right (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card Ω))).mp hpos
  have hn : 0 < (Finset.univ.filter (fun ω => h ω none = i)).card := by exact_mod_cast hc
  obtain ⟨ω, hω⟩ := Finset.card_pos.mp hn
  exact ⟨ω, (Finset.mem_filter.mp hω).2⟩

lemma conditional_rectangle_probability {Ω J : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype J] {q : ℕ}
    (hq : 0 < q) (h : Ω → Option J → Fin q) (hu : Uniform h)
    (i : Fin q) (A : J → Finset (Fin q)) :
    probability (fun ω : {ω // h ω none = i} => ∀ j, h ω.val (some j) ∈ A j) =
      (∏ j, ((A j).card : ℝ)) / (q : ℝ) ^ Fintype.card J := by
  let B : Option J → Finset (Fin q) := fun j => match j with
    | none => {i}
    | some j => A j
  have hr := rectangle_probability h hu B
  have he : (fun ω => ∀ j, h ω j ∈ B j) =
      (fun ω => h ω none = i ∧ ∀ j, h ω (some j) ∈ A j) := by
    funext ω
    apply propext
    constructor
    · intro hall
      exact ⟨by simpa [B] using hall none, fun j => hall (some j)⟩
    · rintro ⟨hi, hall⟩ j
      cases j with
      | none => simpa [B] using hi
      | some j => exact hall j
  simp only [he, Fintype.prod_option, B, Finset.card_singleton, Nat.cast_one,
    one_mul, Fintype.card_option] at hr
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  calc
    _ = probability (fun ω => h ω none = i ∧ ∀ j, h ω (some j) ∈ A j) /
        probability (fun ω => h ω none = i) :=
      conditional_probability (fun ω => h ω none = i) (fun ω => ∀ j, h ω (some j) ∈ A j)
    _ = ((∏ j, ((A j).card : ℝ)) / (q : ℝ) ^ (Fintype.card J + 1)) /
        (1 / (q : ℝ)) := by rw [hr, singleton_probability hq h hu i]
    _ = _ := by rw [pow_succ, ← div_div, div_div_div_cancel_right₀ hq0, div_one]

/-- Conditioning on a designated value leaves every other threshold coordinate uniform. -/
theorem conditional_threshold_probability {Ω J : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype J] {q : ℕ}
    (hq : 0 < q) (h : Ω → Option J → Fin q) (hu : Uniform h) (i : Fin q) :
    probability (fun ω : {ω // h ω none = i} => ∀ j, h ω.val (some j) ≤ i) =
      (((i.val + 1 : ℕ) : ℝ) / (q : ℝ)) ^ Fintype.card J := by
  have hr := conditional_rectangle_probability hq h hu i (fun _ => Finset.Iic i)
  simpa only [Finset.mem_Iic, Fin.card_Iic, Finset.prod_const, Finset.card_univ,
    div_pow] using hr

lemma full_function_uniform {J : Type*} [Fintype J] {q : ℕ} :
    Uniform (fun ω : J → Fin q => ω) := by
  intro v
  unfold probability
  rw [← Fintype.card_subtype, Fintype.card_subtype_eq]
  simp [Fintype.card_fun]

noncomputable def restrictionFiberEquiv {I J V : Type*} (e : I ↪ J) (v : I → V) :
    {f : J → V // ∀ i, f (e i) = v i} ≃ ({j // j ∉ Set.range e} → V) where
  toFun f j := f.val j.val
  invFun g := ⟨fun j => if hj : j ∈ Set.range e then
      v ((Equiv.ofInjective e e.injective).symm ⟨j, hj⟩) else g ⟨j, hj⟩, by
    intro i
    simp only [dif_pos (show e i ∈ Set.range e from ⟨i, rfl⟩),
      Equiv.ofInjective_symm_apply]⟩
  left_inv f := by
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ Set.range e
    · simp only [dif_pos hj]
      have he := f.property ((Equiv.ofInjective e e.injective).symm ⟨j, hj⟩)
      rw [Equiv.apply_ofInjective_symm e.injective ⟨j, hj⟩] at he
      exact he.symm
    · simp only [dif_neg hj]
  right_inv g := by
    funext j
    simp only [dif_neg j.property]

lemma uniform_event_probability {Ω J : Type*} [Fintype Ω] [Fintype J] {q : ℕ}
    (h : Ω → J → Fin q) (hu : Uniform h) (P : (J → Fin q) → Prop) [DecidablePred P] :
    probability (fun ω => P (h ω)) =
      ((Finset.univ.filter P).card : ℝ) / (q : ℝ) ^ Fintype.card J := by
  have he : probability (fun ω => P (h ω)) =
      probability (fun ω => h ω ∈ Finset.univ.filter P) := by
    apply probability_congr
    intro ω
    simp
  rw [he, probability_map_mem]
  have huv : ∀ v, probability (fun ω => h ω = v) =
      1 / (q : ℝ) ^ Fintype.card J := hu
  simp only [huv, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- A uniform full joint assignment stays uniform on every injectively selected tuple. -/
theorem uniform_restrict {Ω I J : Type*} [Fintype Ω] [Fintype I] [Fintype J] {q : ℕ}
    (hq : 0 < q) (h : Ω → J → Fin q) (hu : Uniform h) (e : I ↪ J) :
    Uniform (fun ω i => h ω (e i)) := by
  intro v
  have hp : probability (fun ω => (fun i => h ω (e i)) = v) =
      probability (fun ω => ∀ i, h ω (e i) = v i) := by
    apply probability_congr
    intro ω
    exact funext_iff
  rw [hp, uniform_event_probability h hu (fun f => ∀ i, f (e i) = v i)]
  rw [← Fintype.card_subtype, Fintype.card_congr (restrictionFiberEquiv e v),
    Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin,
    Nat.cast_pow]
  have hcard : Fintype.card I ≤ Fintype.card J := Fintype.card_le_of_injective e e.injective
  have hpow : (q : ℝ) ^ Fintype.card J =
      (q : ℝ) ^ (Fintype.card J - Fintype.card I) * (q : ℝ) ^ Fintype.card I := by
    rw [← pow_add, Nat.sub_add_cancel hcard]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [hpow, div_mul_cancel_left₀ (pow_ne_zero _ hq0), one_div]

/-- The exact independent comparator has no-hit probability ((q-i-1)/q)^N. -/
theorem full_function_no_hit {J : Type*} [Fintype J] {q : ℕ} (i : Fin q) :
    probability (fun ω : J → Fin q => ∀ j, i < ω j) =
      (((q - 1 - i.val : ℕ) : ℝ) / (q : ℝ)) ^ Fintype.card J := by
  have hr := rectangle_probability (fun ω : J → Fin q => ω) full_function_uniform
    (fun _ => Finset.Ioi i)
  simpa only [Finset.mem_Ioi, Fin.card_Ioi, Finset.prod_const, Finset.card_univ,
    div_pow] using hr

theorem full_function_no_hit_real {J : Type*} [Fintype J] {q : ℕ} (i : Fin q) :
    probability (fun ω : J → Fin q => ∀ j, i < ω j) =
      (1 - (((i.val + 1 : ℕ) : ℝ) / (q : ℝ))) ^ Fintype.card J := by
  rw [full_function_no_hit]
  congr 1
  have hle : i.val + 1 ≤ q := i.isLt
  have hn : q - 1 - i.val = q - (i.val + 1) := by omega
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  rw [hn, Nat.cast_sub hle, sub_div]
  simp only [div_self hq0]

lemma total_probability_of_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] {q : ℕ}
    (hq : 0 < q) (f : Ω → Fin q)
    (hsingle : ∀ i, probability (fun ω => f ω = i) = 1 / (q : ℝ))
    (P : Ω → Prop) [DecidablePred P] :
    probability P = (1 / (q : ℝ)) *
      ∑ i : Fin q, probability (fun ω : {ω // f ω = i} => P ω.val) := by
  have hc := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ.filter P)
    (Finset.univ : Finset (Fin q)) f
  simp only [Finset.mem_univ, Finset.filter_true_of_mem (fun _ _ => True.intro),
    Finset.filter_filter] at hc
  have hr := congrArg (fun n : ℕ => (n : ℝ) / Fintype.card Ω) hc
  have hsplit : probability P =
      ∑ i : Fin q, probability (fun ω => P ω ∧ f ω = i) := by
    simpa only [probability, Nat.cast_sum, Finset.sum_div] using hr.symm
  rw [hsplit, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [conditional_probability (fun ω => f ω = i) P, hsingle i]
  rw [probability_congr (fun ω => and_comm (a := P ω) (b := f ω = i))]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp

/-- Strict minimum probability is the average of conditional no-hit probabilities. -/
theorem strict_min_decomposition {Ω J : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype J] {q : ℕ}
    (hq : 0 < q) (h : Ω → Option J → Fin q)
    (hsingle : ∀ i, probability (fun ω => h ω none = i) = 1 / (q : ℝ)) :
    probability (fun ω => ∀ j, h ω none < h ω (some j)) =
      (1 / (q : ℝ)) * ∑ i : Fin q,
        probability (fun ω : {ω // h ω none = i} => ∀ j, i < h ω.val (some j)) := by
  rw [total_probability_of_uniform hq (fun ω => h ω none) hsingle]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply probability_congr
  intro ω
  rw [ω.property]

end Conditional
end StableMSR.Recovery.Derandomization



set_option autoImplicit false
open scoped Classical BigOperators

namespace StableMSR.Recovery.Derandomization

/-- Polynomial marginals remain exactly uniform after injecting an arbitrary
finite key tuple and bijectively coding field outputs as bounded integers. -/
theorem polynomialHash_reindexed_uniform {F J : Type*} [Field F] [Fintype F]
    [DecidableEq F] [Fintype J] {q : ℕ} (outputEquiv : F ≃ Fin q)
    (ℓ : ℕ) (key : J ↪ F) (hJ : Fintype.card J ≤ ℓ) (hℓ : ℓ ≤ Fintype.card F) :
    Conditional.Uniform (fun (a : Fin ℓ → F) (j : J) =>
      outputEquiv (∑ i : Fin ℓ, a i * (key j) ^ (i : ℕ))) := by
  classical
  intro v
  let T : Finset F := Finset.univ.image key
  have hcard : T.card = Fintype.card J := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ key.injective]
    exact Finset.card_univ
  let e : J ≃ T := Equiv.ofBijective
    (fun j => ⟨key j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => key.injective (congrArg Subtype.val h), by
      intro x
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp x.property
      exact ⟨j, Subtype.ext hj⟩⟩
  let w : T → F := fun x => outputEquiv.symm (v (e.symm x))
  have hevent :
      (fun a : Fin ℓ → F =>
        (fun j => outputEquiv (∑ i : Fin ℓ, a i * (key j) ^ (i : ℕ))) = v) =
      (fun a : Fin ℓ → F => ∀ x : T,
        (∑ i : Fin ℓ, a i * (x : F) ^ (i : ℕ)) = w x) := by
    funext a
    apply propext
    constructor
    · intro hv x
      have hx : key (e.symm x) = x.val := congrArg Subtype.val (e.apply_symm_apply x)
      apply outputEquiv.injective
      have hvx := congrFun hv (e.symm x)
      simpa only [hx, w, Equiv.apply_symm_apply] using hvx
    · intro hw
      funext j
      have hj := congrArg outputEquiv (hw (e j))
      change outputEquiv (∑ i : Fin ℓ, a i * (key j) ^ (i : ℕ)) = outputEquiv (w (e j)) at hj
      simpa only [w, Equiv.symm_apply_apply, Equiv.apply_symm_apply] using hj
  unfold Conditional.probability
  simp only [hevent]
  have hq : Fintype.card F = q := by simpa using Fintype.card_congr outputEquiv
  have hp := polynomialHash_marginal_probability ℓ T (hcard ▸ hJ) hℓ w
  simpa only [hcard, hq] using hp

/-- The bounded-integer encoding is literally ZMod.val, not an arbitrary ordering. -/
def zmodValueEquiv (q : ℕ) [NeZero q] : ZMod q ≃ Fin q where
  toFun x := ⟨x.val, ZMod.val_lt x⟩
  invFun x := (x.val : ZMod q)
  left_inv x := ZMod.natCast_zmod_val x
  right_inv x := Fin.ext (ZMod.val_natCast_of_lt x.isLt)

noncomputable def polynomialFinValue {q : ℕ} [NeZero q] (ℓ : ℕ)
    (a : Fin ℓ → ZMod q) (x : ZMod q) : Fin q :=
  zmodValueEquiv q (∑ i : Fin ℓ, a i * x ^ (i : ℕ))

@[simp] lemma polynomialFinValue_val {q : ℕ} [NeZero q] (ℓ : ℕ)
    (a : Fin ℓ → ZMod q) (x : ZMod q) :
    (polynomialFinValue ℓ a x).val = (∑ i : Fin ℓ, a i * x ^ (i : ℕ)).val := rfl

/-- Actual prime-field polynomial hashes have uniform values on every injected
key tuple of size at most the fixed coefficient count. -/
theorem polynomialFinValue_uniform {q : ℕ} [Fact q.Prime] {J : Type*} [Fintype J]
    (ℓ : ℕ) (key : J ↪ ZMod q) (hJ : Fintype.card J ≤ ℓ) (hℓ : ℓ ≤ q) :
    Conditional.Uniform (fun (a : Fin ℓ → ZMod q) (j : J) =>
      polynomialFinValue ℓ a (key j)) := by
  exact polynomialHash_reindexed_uniform (zmodValueEquiv q) ℓ key hJ
    (by simpa only [ZMod.card] using hℓ)

/-- A designated key and an injected competitor tuple share the same fixed
coefficient family; the result directly matches the conditional-moment interface. -/
theorem polynomialFinValue_option_uniform {q : ℕ} [Fact q.Prime] {I : Type*}
    (ℓ : ℕ) (key : Option I ↪ ZMod q) (r : ℕ) (e : Fin r ↪ I)
    (hr : r+1 ≤ ℓ) (hℓ : ℓ ≤ q) :
    Conditional.Uniform (fun (a : Fin ℓ → ZMod q) (o : Option (Fin r)) =>
      match o with
      | none => polynomialFinValue ℓ a (key none)
      | some j => polynomialFinValue ℓ a (key (some (e j)))) := by
  convert polynomialFinValue_uniform ℓ (e.optionMap.trans key)
    (by simpa only [Fintype.card_option, Fintype.card_fin] using hr) hℓ using 1
  funext a o
  cases o <;> rfl

/-- The fixed 8193-coefficient family supplies all conditional tuples through order 8192. -/
theorem polynomialFinValue_option_8193_uniform {q : ℕ} [Fact q.Prime] {I : Type*}
    (key : Option I ↪ ZMod q) (hq : 8193 ≤ q) (r : ℕ) (hr : r ≤ 8192) (e : Fin r ↪ I) :
    Conditional.Uniform (fun (a : Fin 8193 → ZMod q) (o : Option (Fin r)) =>
      match o with
      | none => polynomialFinValue 8193 a (key none)
      | some j => polynomialFinValue 8193 a (key (some (e j)))) := by
  exact polynomialFinValue_option_uniform 8193 key r e (by omega) hq

/-- The actual coefficient family has q^ℓ seeds, including repeated induced orders. -/
lemma polynomialFinValue_seed_card {q : ℕ} [NeZero q] (ℓ : ℕ) :
    Fintype.card (Fin ℓ → ZMod q) = q^ℓ := by simp

end StableMSR.Recovery.Derandomization



set_option autoImplicit false
set_option maxRecDepth 65536
open scoped Classical BigOperators

namespace StableMSR.Recovery.MinwiseEstimate

noncomputable def mean {A : Type*} (S : Finset A) (f : A → ℝ) : ℝ :=
  (∑ a ∈ S, f a) / (S.card : ℝ)

def zeroIndicator (z : ℕ) : ℝ := if z = 0 then 1 else 0

noncomputable def binomialTruncation (z k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * (z.choose j : ℝ)

lemma mean_mono {A : Type*} {S : Finset A} {f g : A → ℝ}
    (h : ∀ a ∈ S, f a ≤ g a) : mean S f ≤ mean S g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

lemma mean_add {A : Type*} (S : Finset A) (f g : A → ℝ) :
    mean S (fun a => f a + g a) = mean S f + mean S g := by
  simp [mean, Finset.sum_add_distrib, add_div]

/-- The even Bonferroni polynomial majorizes the zero-hit indicator with error at most
its last binomial moment. This is a pointwise combinatorial identity, not a probability axiom. -/
lemma binomialTruncation_bounds (z k : ℕ) (hk : Even k) :
    zeroIndicator z ≤ binomialTruncation z k ∧
      binomialTruncation z k ≤ zeroIndicator z + (z.choose k : ℝ) := by
  cases z with
  | zero =>
    have hz : binomialTruncation 0 k = 1 := by
      unfold binomialTruncation
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hj0
        simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj0)]
      · simp
    rw [hz]
    simp only [zeroIndicator, ↓reduceIte, le_refl, true_and]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  | succ z =>
    have hid : binomialTruncation (z + 1) k = (-1 : ℝ) ^ k * (z.choose k : ℝ) := by
      have hi := @Int.alternating_sum_range_choose_eq_choose z k
      unfold binomialTruncation
      exact_mod_cast hi
    rw [hid, hk.neg_one_pow, one_mul]
    simp only [zeroIndicator, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, zero_add]
    constructor
    · positivity
    · exact_mod_cast Nat.choose_le_succ z k

lemma mean_binomialTruncation {C : Type*} (R : Finset C) (X : C → ℕ) (k : ℕ) :
    mean R (fun c => binomialTruncation (X c) k) =
    ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * mean R (fun c => ((X c).choose j : ℝ)) := by
  unfold mean binomialTruncation
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum, mul_div_assoc]

/-- Equal low-order binomial moments transfer zero-hit probabilities, with an explicit
last-moment error. Applied to a limited-independent law and the full product law, this is
Indyk's small-occupancy inclusion-exclusion step. -/
theorem no_hit_comparison {A B : Type*} (S : Finset A) (U : Finset B)
    (Z : A → ℕ) (W : B → ℕ) (k : ℕ) (hk : Even k)
    (hmom : ∀ j ≤ k,
      mean S (fun a => ((Z a).choose j : ℝ)) =
      mean U (fun b => ((W b).choose j : ℝ))) :
    mean S (fun a => zeroIndicator (Z a)) ≤
      mean U (fun b => zeroIndicator (W b)) + mean U (fun b => ((W b).choose k : ℝ)) := by
  have hsame : mean S (fun a => binomialTruncation (Z a) k) =
      mean U (fun b => binomialTruncation (W b) k) := by
    rw [mean_binomialTruncation, mean_binomialTruncation]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hmom j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  calc
    _ ≤ mean S (fun a => binomialTruncation (Z a) k) :=
      mean_mono (fun a _ => (binomialTruncation_bounds (Z a) k hk).1)
    _ = mean U (fun b => binomialTruncation (W b) k) := hsame
    _ ≤ mean U (fun b => zeroIndicator (W b) + ((W b).choose k : ℝ)) :=
      mean_mono (fun b _ => (binomialTruncation_bounds (W b) k hk).2)
    _ = _ := mean_add U _ _

/-- The binomial factorial-moment bound expressed using the mean occupancy μ=Np. -/
lemma binomialMoment_le (N k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    (N.choose k : ℝ) * p ^ k ≤ ((N : ℝ) * p) ^ k / (k.factorial : ℝ) := by
  have h := mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div (α := ℝ) k N)
    (pow_nonneg hp k)
  simpa only [mul_pow, div_mul_eq_mul_div] using h

/-- A deliberately coarse fixed truncation suffices: no asymptotic Stirling estimate is used. -/
lemma fixed_factorial_bound :
    (2 : ℝ) ^ 20 * 256 ^ 8192 ≤ (Nat.factorial 8192 : ℝ) := by
  have hfac : (2048 : ℕ) ^ 6144 ≤ Nat.factorial 8192 := by
    have h := Nat.factorial_mul_pow_sub_le_factorial (n := 2048) (m := 8192) (by omega)
    have hpos := Nat.factorial_pos 2048
    have hle : (2048 : ℕ) ^ 6144 ≤ Nat.factorial 2048 * 2048 ^ 6144 := by
      exact Nat.le_mul_of_pos_left _ hpos
    rw [show (8192 : ℕ) - 2048 = 6144 by omega] at h
    exact hle.trans h
  have hpow : (2 : ℝ) ^ 20 * 256 ^ 8192 ≤ 2048 ^ 6144 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, show (2048 : ℝ) = 2 ^ 11 by norm_num,
      ← pow_mul, ← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  apply hpow.trans
  have hcast := (Nat.cast_le (α := ℝ)).2 hfac
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcast

/-- For all mean occupancies at most 256, the explicit even truncation 8192 gives
an additive no-hit comparison error at most 2^(-20). -/
theorem small_occupancy_remainder (N : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hμ : (N : ℝ) * p ≤ 256) :
    (N.choose 8192 : ℝ) * p ^ 8192 ≤ 1 / (2 : ℝ) ^ 20 := by
  apply le_trans (binomialMoment_le N 8192 p hp)
  have hfacpos : (0 : ℝ) < (Nat.factorial 8192 : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.factorial_pos 8192)
  apply (div_le_div_iff₀ hfacpos (by positivity)).2
  have hpw := pow_le_pow_left₀ (show (0 : ℝ) ≤ (N : ℝ) * p by positivity) hμ 8192
  calc
    ((N : ℝ) * p) ^ 8192 * 2 ^ 20 ≤ 256 ^ 8192 * 2 ^ 20 :=
      mul_le_mul_of_nonneg_right hpw (pow_nonneg (by norm_num) 20)
    _ = 2 ^ 20 * 256 ^ 8192 := mul_comm _ _
    _ ≤ 1 * (Nat.factorial 8192 : ℝ) := by
      simpa only [one_mul] using fixed_factorial_bound

end StableMSR.Recovery.MinwiseEstimate



set_option autoImplicit false
open scoped Classical BigOperators

namespace StableMSR.Recovery.MinwiseEstimate
open Derandomization.FourthMoment

lemma mean_univ_eq_average {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    mean Finset.univ f = average f := by simp only [mean, average, Finset.card_univ]

lemma zero_hit_mean {Ω I : Type*} [Fintype Ω] (H : Ω → Finset I) :
    mean Finset.univ (fun ω => zeroIndicator (H ω).card) =
      (((Finset.univ : Finset Ω).filter (fun ω => H ω = ∅)).card : ℝ) /
        (Fintype.card Ω : ℝ) := by
  simp only [mean, zeroIndicator, Finset.card_eq_zero, Finset.sum_boole, Finset.card_univ]

/-- The complete small-occupancy comparison from actual joint hit probabilities.
The comparator can be the full independent function family; no moment identity is assumed. -/
theorem low_occupancy_comparison {Ω Ψ I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype Ψ] [Nonempty Ψ] [Fintype I]
    (H : Ω → Finset I) (G : Ψ → Finset I) (p : ℝ) (hp : 0 ≤ p)
    (hμ : (Fintype.card I : ℝ) * p ≤ 256)
    (hH : ∀ r : ℕ, 1 ≤ r → r ≤ 8192 → ∀ e : Fin r ↪ I,
      average (fun ω => if ∀ j, e j ∈ H ω then (1 : ℝ) else 0) = p ^ r)
    (hG : ∀ r : ℕ, 1 ≤ r → r ≤ 8192 → ∀ e : Fin r ↪ I,
      average (fun ω => if ∀ j, e j ∈ G ω then (1 : ℝ) else 0) = p ^ r) :
    (((Finset.univ : Finset Ω).filter (fun ω => H ω = ∅)).card : ℝ) /
        (Fintype.card Ω : ℝ) ≤
      (((Finset.univ : Finset Ψ).filter (fun ω => G ω = ∅)).card : ℝ) /
        (Fintype.card Ψ : ℝ) + 1 / (2 : ℝ) ^ 20 := by
  have hmH := binomial_moments_of_joint_hits_up_to H 8192 p hH
  have hmG := binomial_moments_of_joint_hits_up_to G 8192 p hG
  have hcompare := no_hit_comparison Finset.univ Finset.univ
    (fun ω => (H ω).card) (fun ω => (G ω).card) 8192 (by decide) (by
      intro r hr
      rw [mean_univ_eq_average, mean_univ_eq_average, hmH r hr, hmG r hr])
  rw [zero_hit_mean, zero_hit_mean, mean_univ_eq_average, hmG 8192 le_rfl] at hcompare
  exact hcompare.trans (add_le_add le_rfl (small_occupancy_remainder (Fintype.card I) p hp hμ))

end StableMSR.Recovery.MinwiseEstimate



set_option autoImplicit false
open scoped Classical BigOperators

namespace StableMSR.Recovery.MinwiseEstimate

lemma power_increment (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    ((n : ℝ) + 1) * x ^ n ≤ (x + 1) ^ (n + 1) - x ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm := mul_le_mul_of_nonneg_right ih (show 0 ≤ x + 1 by linarith)
    have hp : 0 ≤ ((n : ℝ) + 1) * x ^ n := by positivity
    push_cast
    simp only [pow_succ] at ih hm ⊢
    nlinarith

lemma sum_powers_bound (q N : ℕ) :
    ((N : ℝ) + 1) * (∑ j ∈ Finset.range q, (j : ℝ) ^ N) ≤ (q : ℝ) ^ (N + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ]
    have hi := power_increment (q : ℝ) (by positivity) N
    push_cast
    nlinarith

/-- A purely discrete bound for the full-independent strict-minimum probability. -/
theorem uniform_baseline (q N : ℕ) (hq : 0 < q) :
    (∑ j ∈ Finset.range q, ((j : ℝ) / (q : ℝ)) ^ N) / (q : ℝ) ≤ 1 / ((N : ℝ) + 1) := by
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  have hnp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  apply (div_le_iff₀ hqr).2
  apply (div_le_iff₀ (pow_pos hqr N)).2
  have h := sum_powers_bound q N
  have heq : 1 / ((N : ℝ) + 1) * (q : ℝ) * (q : ℝ) ^ N =
      (q : ℝ) ^ (N + 1) / ((N : ℝ) + 1) := by rw [pow_succ]; ring
  rw [heq]
  apply (le_div_iff₀ hnp).2
  simpa only [mul_comm] using h

/-- Equivalent form indexed by the sampled distinguished hash value plus one. -/
theorem uniform_baseline_Ioc (q N : ℕ) (hq : 0 < q) :
    (∑ j ∈ Finset.Ioc 0 q, (1 - (j : ℝ) / (q : ℝ)) ^ N) / (q : ℝ) ≤
      1 / ((N : ℝ) + 1) := by
  have hsum : (∑ j ∈ Finset.Ioc 0 q, (1 - (j : ℝ) / (q : ℝ)) ^ N) =
      ∑ j ∈ Finset.range q, ((j : ℝ) / (q : ℝ)) ^ N := by
    apply Finset.sum_bij (fun j _ => q - j)
    · intro j hj
      simp only [Finset.mem_Ioc] at hj
      exact Finset.mem_range.mpr (by omega)
    · intro j hj j' hj' heq
      simp only [Finset.mem_Ioc] at hj hj'
      omega
    · intro j hj
      have hjq := Finset.mem_range.mp hj
      refine ⟨q - j, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj
      have hjq := (Finset.mem_Ioc.mp hj).2
      congr 1
      rw [Nat.cast_sub hjq]
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp
  rw [hsum]
  exact uniform_baseline q N hq

lemma inverse_cube_le_square (x : ℝ) (hx : 1 ≤ x) : 1 / x ^ 3 ≤ 1 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  apply (div_le_div_iff₀ (pow_pos hx0 3) (pow_pos hx0 2)).2
  nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ x - 1 by linarith)]

/-- Sum the fourth-moment zero-hit estimate by the elementary telescoping inverse-square bound. -/
theorem fourth_tail_sum (δ : ℝ) (hδ : 0 < δ) (J q : ℕ) (hJ : 0 < J) (hJq : J ≤ q)
    (hscale : 1 ≤ δ * (J : ℝ)) :
    (∑ j ∈ Finset.Ioc J q, (3 / (δ * (j : ℝ)) ^ 2 + 1 / (δ * (j : ℝ)) ^ 3)) ≤
      4 / (δ ^ 2 * (J : ℝ)) := by
  have hJr : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hpoint : ∀ j ∈ Finset.Ioc J q,
      3 / (δ * (j : ℝ)) ^ 2 + 1 / (δ * (j : ℝ)) ^ 3 ≤
        (4 / δ ^ 2) * ((j : ℝ) ^ 2)⁻¹ := by
    intro j hj
    have hjJ : (J : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hj).1.le
    have hμ : 1 ≤ δ * (j : ℝ) := hscale.trans (mul_le_mul_of_nonneg_left hjJ hδ.le)
    have hc := inverse_cube_le_square (δ * (j : ℝ)) hμ
    calc
      _ ≤ 3 / (δ * (j : ℝ)) ^ 2 + 1 / (δ * (j : ℝ)) ^ 2 := add_le_add le_rfl hc
      _ = 4 / (δ * (j : ℝ)) ^ 2 := by ring
      _ = _ := by rw [mul_pow]; ring
  calc
    _ ≤ ∑ j ∈ Finset.Ioc J q, (4 / δ ^ 2) * ((j : ℝ) ^ 2)⁻¹ := Finset.sum_le_sum hpoint
    _ = (4 / δ ^ 2) * ∑ j ∈ Finset.Ioc J q, ((j : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ (4 / δ ^ 2) * ((J : ℝ)⁻¹ - (q : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (α := ℝ) hJ.ne' hJq) (by positivity)
    _ ≤ (4 / δ ^ 2) * (J : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)
    _ = _ := by ring

/-- The finite threshold split in Indyk's proof with absolute, non-optimized constants.
The low branch is supplied by Bonferroni and the high branch by the fourth-moment estimate. -/
theorem minwise_numeric_bound (N q J : ℕ) (hN : 0 < N) (hq : 0 < q)
    (hJ : 0 < J) (hJq : J ≤ q)
    (hlower : 127 * (q : ℝ) ≤ (N : ℝ) * (J : ℝ))
    (hupper : (N : ℝ) * (J : ℝ) ≤ 128 * (q : ℝ))
    (a : ℕ → ℝ)
    (hlow : ∀ j ∈ Finset.Ioc 0 J,
      a j ≤ (1 - (j : ℝ) / (q : ℝ)) ^ N + 1 / (2 : ℝ) ^ 20)
    (hhigh : ∀ j ∈ Finset.Ioc J q,
      a j ≤ 3 / ((N : ℝ) * (j : ℝ) / (q : ℝ)) ^ 2 +
        1 / ((N : ℝ) * (j : ℝ) / (q : ℝ)) ^ 3) :
    (∑ j ∈ Finset.Ioc 0 q, a j) / (q : ℝ) ≤ 5 / (4 * ((N : ℝ) + 1)) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hJr : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hscale : 1 ≤ ((N : ℝ) / (q : ℝ)) * (J : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hqr).2
    nlinarith
  have ht := fourth_tail_sum ((N : ℝ) / (q : ℝ)) (div_pos hNr hqr) J q hJ hJq hscale
  have htail : (∑ j ∈ Finset.Ioc J q, a j) / (q : ℝ) ≤ 4 / (127 * (N : ℝ)) := by
    have hpoint : ∀ j ∈ Finset.Ioc J q,
        a j ≤ 3 / (((N : ℝ) / (q : ℝ)) * (j : ℝ)) ^ 2 +
          1 / (((N : ℝ) / (q : ℝ)) * (j : ℝ)) ^ 3 := by
      intro j hj
      simpa only [div_mul_eq_mul_div] using hhigh j hj
    calc
      _ ≤ (4 / (((N : ℝ) / (q : ℝ)) ^ 2 * (J : ℝ))) / (q : ℝ) :=
        div_le_div_of_nonneg_right ((Finset.sum_le_sum hpoint).trans ht) hqr.le
      _ = 4 * (q : ℝ) / ((N : ℝ) ^ 2 * (J : ℝ)) := by field_simp
      _ ≤ _ := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith [mul_le_mul_of_nonneg_left hlower hNr.le]
  have hlow_sum : (∑ j ∈ Finset.Ioc 0 J, a j) ≤
      (∑ j ∈ Finset.Ioc 0 q, (1 - (j : ℝ) / (q : ℝ)) ^ N) +
        (J : ℝ) / (2 : ℝ) ^ 20 := by
    have hpart : (∑ j ∈ Finset.Ioc 0 J, (1 - (j : ℝ) / (q : ℝ)) ^ N) ≤
        ∑ j ∈ Finset.Ioc 0 q, (1 - (j : ℝ) / (q : ℝ)) ^ N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hj).1, (Finset.mem_Ioc.mp hj).2.trans hJq⟩
      · intro j hj _
        apply pow_nonneg
        apply sub_nonneg.mpr
        apply (div_le_one hqr).2
        exact_mod_cast (Finset.mem_Ioc.mp hj).2
    have hs := Finset.sum_le_sum hlow
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc,
      Nat.sub_zero, mul_one_div] at hs
    exact hs.trans (add_le_add hpart le_rfl)
  have herr : ((J : ℝ) / (2 : ℝ) ^ 20) / (q : ℝ) ≤
      (128 / (2 : ℝ) ^ 20) / (N : ℝ) := by
    apply (div_le_div_iff₀ hqr hNr).2
    norm_num
    nlinarith
  have hbase := uniform_baseline_Ioc q N hq
  have hsum := div_le_div_of_nonneg_right hlow_sum hqr.le
  rw [add_div] at hsum
  have hall : (∑ j ∈ Finset.Ioc 0 q, a j) / (q : ℝ) ≤
      1 / ((N : ℝ) + 1) + (128 / (2 : ℝ) ^ 20) / (N : ℝ) + 4 / (127 * (N : ℝ)) := by
    rw [← Finset.sum_Ioc_consecutive a (Nat.zero_le J) hJq, add_div]
    linarith
  apply hall.trans
  have hsmall : (128 / (2 : ℝ) ^ 20) / (N : ℝ) + 4 / (127 * (N : ℝ)) ≤
      1 / (8 * (N : ℝ)) := by
    field_simp
    nlinarith
  have hlast : 1 / (8 * (N : ℝ)) ≤ 1 / (4 * ((N : ℝ) + 1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    linarith
  have hfinal : 1 / ((N : ℝ) + 1) + 1 / (4 * ((N : ℝ) + 1)) =
      5 / (4 * ((N : ℝ) + 1)) := by field_simp; ring
  linarith

/-- A concrete integral threshold exists throughout the large-set regime. -/
theorem minwise_cutoff_exists (N q : ℕ) (hN : 128 ≤ N) (hNq : N ≤ q) :
    ∃ J : ℕ, 0 < J ∧ J ≤ q ∧
      127 * (q : ℝ) ≤ (N : ℝ) * (J : ℝ) ∧
      (N : ℝ) * (J : ℝ) ≤ 128 * (q : ℝ) := by
  have hNr : (128 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNqr : (N : ℝ) ≤ (q : ℝ) := by exact_mod_cast hNq
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  let J : ℕ := ⌊128 * (q : ℝ) / (N : ℝ)⌋₊
  have hfloor : (J : ℝ) ≤ 128 * (q : ℝ) / (N : ℝ) := Nat.floor_le (by positivity)
  have hceil : 128 * (q : ℝ) / (N : ℝ) < (J : ℝ) + 1 := Nat.lt_floor_add_one _
  have hu : (N : ℝ) * (J : ℝ) ≤ 128 * (q : ℝ) := by
    have h := (le_div_iff₀ hNpos).mp hfloor
    simpa only [mul_comm] using h
  have hl : 127 * (q : ℝ) ≤ (N : ℝ) * (J : ℝ) := by
    have h := (div_lt_iff₀ hNpos).mp hceil
    nlinarith
  refine ⟨J, ?_, ?_, hl, hu⟩
  · have hj : (0 : ℝ) < (J : ℝ) := by nlinarith
    exact_mod_cast hj
  · have hj : (J : ℝ) ≤ (q : ℝ) := by nlinarith
    exact_mod_cast hj

end StableMSR.Recovery.MinwiseEstimate



set_option autoImplicit false
set_option maxRecDepth 65536
open scoped Classical BigOperators

namespace StableMSR.Recovery.Derandomization
open Conditional FourthMoment MinwiseEstimate

/-- Select the distinguished key and an injective tuple of competitors. -/
def selectedHash {Ω I : Type*} {q r : ℕ} (h : Ω → Option I → Fin q)
    (e : Fin r ↪ I) (ω : Ω) : Option (Fin r) → Fin q
  | none => h ω none
  | some j => h ω (some (e j))

/-- The precise limited-independence hypothesis needed for one designated minimum. -/
def DesignatedUniform {Ω I : Type*} [Fintype Ω] {q : ℕ}
    (h : Ω → Option I → Fin q) (k : ℕ) : Prop :=
  ∀ r ≤ k, ∀ e : Fin r ↪ I, Uniform (selectedHash h e)

lemma designated_singleton {Ω I : Type*} [Fintype Ω] {q k : ℕ}
    (hq : 0 < q) (h : Ω → Option I → Fin q) (hu : DesignatedUniform h k) (i : Fin q) :
    probability (fun ω => h ω none = i) = 1 / (q : ℝ) := by
  let e : Fin 0 ↪ I := ⟨Fin.elim0, fun x => Fin.elim0 x⟩
  exact singleton_probability hq (selectedHash h e) (hu 0 (Nat.zero_le k) e) i

lemma designated_fiber_nonempty {Ω I : Type*} [Fintype Ω] [Nonempty Ω] {q k : ℕ}
    (hq : 0 < q) (h : Ω → Option I → Fin q) (hu : DesignatedUniform h k) (i : Fin q) :
    Nonempty {ω // h ω none = i} := by
  let e : Fin 0 ↪ I := ⟨Fin.elim0, fun x => Fin.elim0 x⟩
  exact fiber_nonempty hq (selectedHash h e) (hu 0 (Nat.zero_le k) e) i

lemma designated_full_uniform {Ω I : Type*} [Fintype Ω] [Fintype I] {q k : ℕ}
    (hq : 0 < q) (h : Ω → Option I → Fin q) (hu : DesignatedUniform h k)
    (hcard : Fintype.card I ≤ k) : Uniform h := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hh := uniform_restrict hq (selectedHash h e.toEmbedding) (hu _ hcard e.toEmbedding)
    (Equiv.optionCongr e.symm).toEmbedding
  have heq : (fun ω x => selectedHash h e.toEmbedding ω ((Equiv.optionCongr e.symm).toEmbedding x)) = h := by
    funext ω x
    cases x with
    | none => rfl
    | some x =>
        change h ω (some (e (e.symm x))) = h ω (some x)
        rw [e.apply_symm_apply]
  rw [heq] at hh
  exact hh

noncomputable def conditionalHits {Ω I : Type*} [Fintype I] {q : ℕ}
    (h : Ω → Option I → Fin q) (i : Fin q) (ω : {ω // h ω none = i}) : Finset I :=
  Finset.univ.filter (fun j => h ω.val (some j) ≤ i)

noncomputable def independentHits {I : Type*} [Fintype I] {q : ℕ}
    (i : Fin q) (ω : I → Fin q) : Finset I := Finset.univ.filter (fun j => ω j ≤ i)

lemma conditional_joint_hits {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I] {q k : ℕ}
    (hq : 0 < q) (h : Ω → Option I → Fin q) (hu : DesignatedUniform h k)
    (i : Fin q) (r : ℕ) (hr : r ≤ k) (e : Fin r ↪ I) :
    average (fun ω : {ω // h ω none = i} =>
      if ∀ j, e j ∈ conditionalHits h i ω then (1 : ℝ) else 0) =
      (((i.val + 1 : ℕ) : ℝ) / (q : ℝ)) ^ r := by
  have hh := conditional_threshold_probability hq (selectedHash h e) (hu r hr e) i
  rw [probability_eq_average] at hh
  simp only [selectedHash, Fintype.card_fin] at hh
  convert hh using 2
  apply congrArg average
  funext ω
  by_cases hx : ∀ j : Fin r, h ω.val (some (e j)) ≤ i
  · simp [conditionalHits, selectedHash, hx]
  · simp [conditionalHits, selectedHash, hx]

lemma independent_joint_hits {I : Type*} [Fintype I] {q : ℕ}
    (hq : 0 < q) (i : Fin q) (r : ℕ) (e : Fin r ↪ I) :
    average (fun ω : I → Fin q => if ∀ j, e j ∈ independentHits i ω then (1 : ℝ) else 0) =
      (((i.val + 1 : ℕ) : ℝ) / (q : ℝ)) ^ r := by
  have hu := uniform_restrict hq (fun ω : I → Fin q => ω) full_function_uniform e
  have hr := rectangle_probability (fun (ω : I → Fin q) j => ω (e j)) hu
    (fun _ => Finset.Iic i)
  rw [probability_eq_average] at hr
  simpa only [independentHits, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_Iic, Fin.card_Iic, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, div_pow] using hr

lemma conditional_low_bound {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I] {q : ℕ}
    (hq : 0 < q) (h : Ω → Option I → Fin q) (hu : DesignatedUniform h 8192)
    (i : Fin q) (hμ : (Fintype.card I : ℝ) * (((i.val + 1 : ℕ) : ℝ) / (q : ℝ)) ≤ 256) :
    probability (fun ω : {ω // h ω none = i} => ∀ j, i < h ω.val (some j)) ≤
      (1 - (((i.val + 1 : ℕ) : ℝ) / (q : ℝ))) ^ Fintype.card I + 1 / (2 : ℝ) ^ 20 := by
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  letI := designated_fiber_nonempty hq h hu i
  have hc := low_occupancy_comparison (conditionalHits h i) (independentHits (I := I) i)
    (((i.val + 1 : ℕ) : ℝ) / (q : ℝ)) (by positivity) hμ
    (fun r _ hr e => conditional_joint_hits hq h hu i r hr e)
    (fun r _ _ e => independent_joint_hits hq i r e)
  change probability (fun ω : {ω // h ω none = i} => conditionalHits h i ω = ∅) ≤
    probability (fun ω : I → Fin q => independentHits i ω = ∅) + _ at hc
  have hz : probability (fun ω : {ω // h ω none = i} => conditionalHits h i ω = ∅) =
      probability (fun ω : {ω // h ω none = i} => ∀ j, i < h ω.val (some j)) := by
    apply probability_congr
    intro ω
    simp [conditionalHits, Finset.filter_eq_empty_iff]
  have hi : probability (fun ω : I → Fin q => independentHits i ω = ∅) =
      probability (fun ω : I → Fin q => ∀ j, i < ω j) := by
    apply probability_congr
    intro ω
    simp [independentHits, Finset.filter_eq_empty_iff]
  rw [hz, hi, full_function_no_hit_real] at hc
  exact hc

lemma conditional_high_bound {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I] {q : ℕ}
    (hq : 0 < q) (h : Ω → Option I → Fin q) (hu : DesignatedUniform h 8192)
    (i : Fin q) (hN : 0 < Fintype.card I) :
    probability (fun ω : {ω // h ω none = i} => ∀ j, i < h ω.val (some j)) ≤
      3 / ((Fintype.card I : ℝ) * (((i.val + 1 : ℕ) : ℝ) / (q : ℝ))) ^ 2 +
      1 / ((Fintype.card I : ℝ) * (((i.val + 1 : ℕ) : ℝ) / (q : ℝ))) ^ 3 := by
  letI := designated_fiber_nonempty hq h hu i
  have hp1 : (((i.val + 1 : ℕ) : ℝ) / (q : ℝ)) ≤ 1 := by
    apply (div_le_one (Nat.cast_pos.mpr hq)).2
    exact_mod_cast i.isLt
  have hμ : (0 : ℝ) < (Fintype.card I : ℝ) * (((i.val + 1 : ℕ) : ℝ) / (q : ℝ)) := by
    exact mul_pos (Nat.cast_pos.mpr hN) (div_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) (Nat.cast_pos.mpr hq))
  have hc := no_hit_probability_le_of_fourwise (conditionalHits h i)
    (((i.val + 1 : ℕ) : ℝ) / (q : ℝ)) (by positivity) hp1
    (fun r _ hr e => conditional_joint_hits hq h hu i r (by omega) e) hμ
  change probability (fun ω : {ω // h ω none = i} => conditionalHits h i ω = ∅) ≤ _ at hc
  have hz : probability (fun ω : {ω // h ω none = i} => conditionalHits h i ω = ∅) =
      probability (fun ω : {ω // h ω none = i} => ∀ j, i < h ω.val (some j)) := by
    apply probability_congr
    intro ω
    simp [conditionalHits, Finset.filter_eq_empty_iff]
  rw [hz] at hc
  exact hc


lemma sum_fin_as_Ioc (q : ℕ) (f : Fin q → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i : Fin q, a (i.val + 1) = f i) :
    (∑ i : Fin q, f i) = ∑ j ∈ Finset.Ioc 0 q, a j := by
  apply Finset.sum_bij (fun i _ => i.val + 1)
  · intro i _
    exact Finset.mem_Ioc.mpr ⟨Nat.succ_pos _, i.isLt⟩
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro j hj
    obtain ⟨hj0, hjq⟩ := Finset.mem_Ioc.mp hj
    refine ⟨⟨j - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    change j - 1 + 1 = j
    omega
  · intro i _
    exact (ha i).symm

lemma fin_uniform_baseline (q N : ℕ) (hq : 0 < q) :
    (1 / (q : ℝ)) * (∑ i : Fin q,
      (1 - (((i.val + 1 : ℕ) : ℝ) / (q : ℝ))) ^ N) ≤ 1 / ((N : ℝ) + 1) := by
  rw [sum_fin_as_Ioc q _ (fun j => (1 - (j : ℝ) / (q : ℝ)) ^ N) (fun _ => rfl)]
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using uniform_baseline_Ioc q N hq

lemma strict_min_uniform_bound {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I] {q : ℕ}
    (hq : 0 < q) (h : Ω → Option I → Fin q) (hu : Uniform h) :
    probability (fun ω => ∀ j, h ω none < h ω (some j)) ≤ 1 / ((Fintype.card I : ℝ) + 1) := by
  rw [strict_min_decomposition hq h (singleton_probability hq h hu)]
  have heach : ∀ i : Fin q,
      probability (fun ω : {ω // h ω none = i} => ∀ j, i < h ω.val (some j)) =
        (1 - (((i.val + 1 : ℕ) : ℝ) / (q : ℝ))) ^ Fintype.card I := by
    intro i
    have hc := conditional_rectangle_probability hq h hu i (fun _ => Finset.Ioi i)
    simp only [Finset.mem_Ioi, Fin.card_Ioi, Finset.prod_const, Finset.card_univ, div_pow] at hc
    have hh := full_function_no_hit_real (J := I) i
    rw [full_function_no_hit] at hh
    exact hc.trans (by simpa only [div_pow] using hh)
  simp_rw [heach]
  exact fin_uniform_baseline q (Fintype.card I) hq

/-- A complete finite fixed-constant version of the upper half of Indyk's minwise estimate.
8193-wise uniformity (the distinguished key plus8192 competitors) is sufficient.
All hypotheses are finite joint-value counts, and the proof derives the strict-minimum bound. -/
theorem finite_minwise_upper {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I] {q : ℕ}
    (hq : 0 < q) (hIq : Fintype.card I ≤ q)
    (h : Ω → Option I → Fin q) (hu : DesignatedUniform h 8192) :
    probability (fun ω => ∀ j, h ω none < h ω (some j)) ≤
      5 / (4 * ((Fintype.card I : ℝ) + 1)) := by
  by_cases hsmall : Fintype.card I < 128
  · have hf := designated_full_uniform hq h hu (by omega)
    have hb := strict_min_uniform_bound hq h hf
    apply hb.trans
    have hpos : (0 : ℝ) < (Fintype.card I : ℝ) + 1 := by positivity
    apply (div_le_div_iff₀ hpos (by positivity)).2
    linarith
  · have hN : 128 ≤ Fintype.card I := by omega
    obtain ⟨J, hJ, hJq, hlower, hupper⟩ := minwise_cutoff_exists (Fintype.card I) q hN hIq
    let f : Fin q → ℝ := fun i =>
      probability (fun ω : {ω // h ω none = i} => ∀ j, i < h ω.val (some j))
    let a : ℕ → ℝ := fun j => if hj : j - 1 < q then f ⟨j - 1, hj⟩ else 0
    have ha : ∀ i : Fin q, a (i.val + 1) = f i := by
      intro i
      simp only [a, Nat.add_sub_cancel, dif_pos i.isLt]
    have halow : ∀ j ∈ Finset.Ioc 0 J,
        a j ≤ (1 - (j : ℝ) / (q : ℝ)) ^ Fintype.card I + 1 / (2 : ℝ) ^ 20 := by
      intro j hj
      obtain ⟨hj0, hjJ⟩ := Finset.mem_Ioc.mp hj
      have hjq : j - 1 < q := by omega
      let i : Fin q := ⟨j - 1, hjq⟩
      have hij : i.val + 1 = j := by dsimp [i]; omega
      have hμ : (Fintype.card I : ℝ) * (((i.val + 1 : ℕ) : ℝ) / (q : ℝ)) ≤ 256 := by
        rw [hij, ← mul_div_assoc]
        apply (div_le_iff₀ (Nat.cast_pos.mpr hq)).2
        have hjJr : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hjJ
        have hm := mul_le_mul_of_nonneg_left hjJr (Nat.cast_nonneg (Fintype.card I))
        nlinarith
      have hc := conditional_low_bound hq h hu i hμ
      simpa only [a, dif_pos hjq, f, hij] using hc
    have hahigh : ∀ j ∈ Finset.Ioc J q,
        a j ≤ 3 / ((Fintype.card I : ℝ) * (j : ℝ) / (q : ℝ)) ^ 2 +
          1 / ((Fintype.card I : ℝ) * (j : ℝ) / (q : ℝ)) ^ 3 := by
      intro j hj
      obtain ⟨hjJ, hjq'⟩ := Finset.mem_Ioc.mp hj
      have hjq : j - 1 < q := by omega
      let i : Fin q := ⟨j - 1, hjq⟩
      have hij : i.val + 1 = j := by dsimp [i]; omega
      have hc := conditional_high_bound hq h hu i (by omega)
      simpa only [a, dif_pos hjq, f, hij, ← mul_div_assoc] using hc
    have hn := minwise_numeric_bound (Fintype.card I) q J (by omega) hq hJ hJq
      hlower hupper a halow hahigh
    rw [strict_min_decomposition hq h (designated_singleton hq h hu),
      sum_fin_as_Ioc q f a ha]
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hn

end StableMSR.Recovery.Derandomization



set_option autoImplicit false
open scoped Classical BigOperators

namespace StableMSR.Recovery.Derandomization

/-- The order obtained by sorting hash values and breaking ties in the input order. -/
def HashBefore {V : Type*} [LinearOrder V] (h : V → ℕ) (x y : V) : Prop :=
  h x < h y ∨ (h x = h y ∧ x < y)

lemma hashBefore_irrefl {V : Type*} [LinearOrder V] (h : V → ℕ) (x : V) :
    ¬ HashBefore h x x := by
  simp [HashBefore]

lemma hashBefore_trans {V : Type*} [LinearOrder V] (h : V → ℕ) {x y z : V}
    (hxy : HashBefore h x y) (hyz : HashBefore h y z) : HashBefore h x z := by
  rcases hxy with hxy | ⟨heqxy, hxy⟩
  · rcases hyz with hyz | ⟨heqyz, _⟩
    · exact Or.inl (lt_trans hxy hyz)
    · exact Or.inl (by simpa [heqyz] using hxy)
  · rcases hyz with hyz | ⟨heqyz, hyz⟩
    · exact Or.inl (by simpa [heqxy] using hyz)
    · exact Or.inr ⟨heqxy.trans heqyz, lt_trans hxy hyz⟩

lemma hashBefore_total {V : Type*} [LinearOrder V] (h : V → ℕ) {x y : V}
    (hxy : x ≠ y) : HashBefore h x y ∨ HashBefore h y x := by
  rcases lt_trichotomy (h x) (h y) with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact Or.inl (Or.inr ⟨heq, hlt⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hgt⟩)
  · exact Or.inr (Or.inl hgt)

/-- Seeds on which the designated point is first after deterministic tie-breaking. -/
noncomputable def firstSeeds {A V : Type*} [DecidableEq A] [LinearOrder V]
    (S : Finset A) (h : A → V → ℕ) (T : Finset V) (z : V) : Finset A :=
  S.filter (fun a => ∀ y ∈ T, y ≠ z → HashBefore (h a) z y)

/-- Seeds on which the designated point has the strictly smallest hash. -/
noncomputable def strictSeeds {A V : Type*} [DecidableEq A] [LinearOrder V]
    (S : Finset A) (h : A → V → ℕ) (T : Finset V) (z : V) : Finset A :=
  S.filter (fun a => ∀ y ∈ T, y ≠ z → h a z < h a y)

/-- Seeds on which the two specified points collide. -/
noncomputable def collisionSeeds {A V : Type*} [DecidableEq A] [LinearOrder V]
    (S : Finset A) (h : A → V → ℕ) (z y : V) : Finset A :=
  S.filter (fun a => h a z = h a y)

/-- The only difference between strict hash minima and first-in-order events is a collision. -/
lemma firstSeeds_subset {A V : Type*} [DecidableEq A] [LinearOrder V]
    (S : Finset A) (h : A → V → ℕ) (T : Finset V) (z : V) :
    firstSeeds S h T z ⊆ strictSeeds S h T z ∪
      (T.erase z).biUnion (fun y => collisionSeeds S h z y) := by
  intro a ha
  obtain ⟨haS, hfirst⟩ := Finset.mem_filter.mp ha
  by_cases hs : ∀ y ∈ T, y ≠ z → h a z < h a y
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haS, hs⟩)
  · push_neg at hs
    obtain ⟨y, hyT, hyz, hnot⟩ := hs
    have hcol : h a z = h a y := by
      rcases hfirst y hyT hyz with hlt | ⟨heq, _⟩
      · exact False.elim (not_lt_of_ge hnot hlt)
      · exact heq
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_erase.mpr ⟨hyz, hyT⟩,
      Finset.mem_filter.mpr ⟨haS, hcol⟩⟩

/-- A counting form of the union bound, preserving multiplicities through distinct seeds. -/
lemma firstSeeds_card_le {A V : Type*} [DecidableEq A] [LinearOrder V]
    (S : Finset A) (h : A → V → ℕ) (T : Finset V) (z : V) :
    (firstSeeds S h T z).card ≤ (strictSeeds S h T z).card +
      ∑ y ∈ T.erase z, (collisionSeeds S h z y).card := by
  calc
    (firstSeeds S h T z).card ≤
      (strictSeeds S h T z ∪ (T.erase z).biUnion (fun y => collisionSeeds S h z y)).card :=
        Finset.card_le_card (firstSeeds_subset S h T z)
    _ ≤ (strictSeeds S h T z).card +
      ((T.erase z).biUnion (fun y => collisionSeeds S h z y)).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left (Finset.card_biUnion_le) _

/-- Appendix B's tie estimate. The finite seed set represents a multiset of output orders,
so different seeds that induce the same order are counted separately. -/
theorem first_probability_bound {A V : Type*} [DecidableEq A] [LinearOrder V]
    (S : Finset A) (hS : S.Nonempty) (h : A → V → ℕ)
    (T : Finset V) (hT : T.Nonempty) (z : V) (q : ℝ)
    (hq : 4 * (T.card : ℝ) ^ 2 ≤ q)
    (hstrict : ((strictSeeds S h T z).card : ℝ) ≤
      5 * (S.card : ℝ) / (4 * (T.card : ℝ)))
    (hcollision : ∀ y ∈ T.erase z,
      ((collisionSeeds S h z y).card : ℝ) ≤ (S.card : ℝ) / q) :
    ((firstSeeds S h T z).card : ℝ) / (S.card : ℝ) ≤ 3 / (2 * (T.card : ℝ)) := by
  have hs : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have ht : (0 : ℝ) < (T.card : ℝ) := by exact_mod_cast hT.card_pos
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hc := firstSeeds_card_le S h T z
  have hcr : ((firstSeeds S h T z).card : ℝ) ≤
      ((strictSeeds S h T z).card : ℝ) +
      ∑ y ∈ T.erase z, ((collisionSeeds S h z y).card : ℝ) := by
    have hc' := (Nat.cast_le (α := ℝ)).2 hc
    push_cast at hc'
    exact hc'
  have hsum : (∑ y ∈ T.erase z, ((collisionSeeds S h z y).card : ℝ)) ≤
      (T.card : ℝ) * ((S.card : ℝ) / q) := by
    calc
      _ ≤ ∑ _y ∈ T.erase z, (S.card : ℝ) / q := Finset.sum_le_sum hcollision
      _ = ((T.erase z).card : ℝ) * ((S.card : ℝ) / q) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le)
        (by positivity)
  have hties : (T.card : ℝ) * ((S.card : ℝ) / q) ≤
      (S.card : ℝ) / (4 * (T.card : ℝ)) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hqpos (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hq (le_of_lt hs)]
  have htotal : ((firstSeeds S h T z).card : ℝ) ≤
      3 * (S.card : ℝ) / (2 * (T.card : ℝ)) := by
    have hadd : 5 * (S.card : ℝ) / (4 * (T.card : ℝ)) +
        (S.card : ℝ) / (4 * (T.card : ℝ)) =
        3 * (S.card : ℝ) / (2 * (T.card : ℝ)) := by ring
    linarith
  apply (div_le_iff₀ hs).2
  have heq : 3 / (2 * (T.card : ℝ)) * (S.card : ℝ) =
      3 * (S.card : ℝ) / (2 * (T.card : ℝ)) := by ring
  simpa only [heq] using htotal

/-- The precise finite interface used in Appendix B: a strict-minwise hash estimate
and pairwise collision estimate imply an approximate-minwise family of deterministic orders. -/
theorem hash_family_to_order_family {A V : Type*} [DecidableEq A] [LinearOrder V]
    (S : Finset A) (hS : S.Nonempty) (h : A → V → ℕ) (V₀ : Finset V) (q : ℝ)
    (hq : 4 * (V₀.card : ℝ) ^ 2 ≤ q)
    (hstrict : ∀ T ⊆ V₀, T.Nonempty → ∀ z ∈ T,
      ((strictSeeds S h T z).card : ℝ) ≤ 5 * (S.card : ℝ) / (4 * (T.card : ℝ)))
    (hcollision : ∀ x ∈ V₀, ∀ y ∈ V₀, x ≠ y →
      ((collisionSeeds S h x y).card : ℝ) ≤ (S.card : ℝ) / q) :
    ∀ T ⊆ V₀, T.Nonempty → ∀ z ∈ T,
      ((firstSeeds S h T z).card : ℝ) / (S.card : ℝ) ≤ 3 / (2 * (T.card : ℝ)) := by
  intro T hTV hT z hz
  apply first_probability_bound S hS h T hT z q
  · have hc : (T.card : ℝ) ≤ (V₀.card : ℝ) := by exact_mod_cast Finset.card_le_card hTV
    have hsq := mul_self_le_mul_self (show (0 : ℝ) ≤ (T.card : ℝ) by positivity) hc
    nlinarith
  · exact hstrict T hTV hT z hz
  · intro y hy
    obtain ⟨hyz, hyT⟩ := Finset.mem_erase.mp hy
    exact hcollision z (hTV hz) y (hTV hyT) hyz.symm

end StableMSR.Recovery.Derandomization



set_option autoImplicit false
set_option maxRecDepth 65536
open scoped Classical BigOperators

namespace StableMSR.Recovery.Derandomization
open Conditional

/-- The explicit fixed-degree prime-field polynomial family satisfies the strict-minwise
bound; no approximate-minwise theorem is used as an assumption. -/
theorem polynomial_strict_minwise {q : ℕ} [Fact q.Prime] {I : Type*} [Fintype I]
    (key : Option I ↪ ZMod q) (hq : 8193 ≤ q) :
    probability (fun a : Fin 8193 → ZMod q => ∀ j,
      polynomialFinValue 8193 a (key none) < polynomialFinValue 8193 a (key (some j))) ≤
      5 / (4 * ((Fintype.card I : ℝ) + 1)) := by
  have hcard := Fintype.card_le_of_injective key key.injective
  simp only [Fintype.card_option, ZMod.card] at hcard
  let h : (Fin 8193 → ZMod q) → Option I → Fin q :=
    fun a o => polynomialFinValue 8193 a (key o)
  have hu : DesignatedUniform h 8192 := by
    intro r hr e
    exact polynomialFinValue_option_8193_uniform key hq r hr e
  exact finite_minwise_upper (Ω := Fin 8193 → ZMod q) (I := I) (q := q)
    (by omega) (by omega) h hu

noncomputable def equalPairEquiv {q : ℕ} :
    {v : Bool → Fin q // v false = v true} ≃ Fin q where
  toFun v := v.val false
  invFun i := ⟨fun _ => i, rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext b
    cases b
    · rfl
    · exact v.property
  right_inv _ := rfl

/-- Exact joint uniformity on two coordinates gives collision probability1/q. -/
lemma uniform_pair_collision {Ω : Type*} [Fintype Ω] {q : ℕ} (hq : 0 < q)
    (h : Ω → Bool → Fin q) (hu : Uniform h) :
    probability (fun ω => h ω false = h ω true) = 1 / (q : ℝ) := by
  letI : DecidableEq Bool := Classical.decEq Bool
  rw [uniform_event_probability h hu (fun v => v false = v true)]
  rw [← Fintype.card_subtype, Fintype.card_congr equalPairEquiv]
  simp only [Fintype.card_fin, Fintype.card_bool]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [pow_two, div_mul_cancel_left₀ hq0, one_div]

lemma polynomial_collision {q : ℕ} [Fact q.Prime] (hq : 8193 ≤ q)
    (x y : ZMod q) (hxy : x ≠ y) :
    probability (fun a : Fin 8193 → ZMod q =>
      polynomialFinValue 8193 a x = polynomialFinValue 8193 a y) = 1 / (q : ℝ) := by
  let key : Bool ↪ ZMod q := ⟨(fun b => if b then y else x), by
    intro b c heq
    cases b <;> cases c <;> simp_all⟩
  have hu := polynomialFinValue_uniform 8193 key (by norm_num) hq
  exact uniform_pair_collision (by omega) (fun a b => polynomialFinValue 8193 a (key b)) hu

/-- Distinguish one member of T, retaining every other member exactly once. -/
def optionEraseEmbedding {V : Type*} [DecidableEq V] (T : Finset V) (z : V) :
    Option (T.erase z) ↪ V where
  toFun x := match x with | none => z | some y => y.val
  inj' := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim ((Finset.mem_erase.mp b.property).1 hab.symm)
    | some a =>
      cases b with
      | none => exact False.elim ((Finset.mem_erase.mp a.property).1 hab)
      | some b => exact congrArg some (Subtype.ext hab)

noncomputable def polynomialNatHash {q : ℕ} [NeZero q] {V : Type*}
    (key : V ↪ ZMod q) (a : Fin 8193 → ZMod q) (x : V) : ℕ :=
  (polynomialFinValue 8193 a (key x)).val

/-- The strict-minwise estimate on an arbitrary finite subset of injected ordered keys. -/
theorem polynomial_strictSeeds_bound {q : ℕ} [Fact q.Prime] {V : Type*} [LinearOrder V]
    (key : V ↪ ZMod q) (hq : 8193 ≤ q) (T : Finset V) (z : V) (hz : z ∈ T) :
    ((strictSeeds Finset.univ (polynomialNatHash key) T z).card : ℝ) /
      (Fintype.card (Fin 8193 → ZMod q) : ℝ) ≤ 5 / (4 * (T.card : ℝ)) := by
  have hp := polynomial_strict_minwise ((optionEraseEmbedding T z).trans key) hq
  have hevent (a : Fin 8193 → ZMod q) :
      (∀ j : T.erase z,
        polynomialFinValue 8193 a (key z) < polynomialFinValue 8193 a (key j.val)) ↔
      ∀ y ∈ T, y ≠ z → polynomialNatHash key a z < polynomialNatHash key a y := by
    constructor
    · intro hall y hy hyz
      exact hall ⟨y, Finset.mem_erase.mpr ⟨hyz, hy⟩⟩
    · intro hall j
      exact hall j.val (Finset.mem_erase.mp j.property).2 (Finset.mem_erase.mp j.property).1
  change probability (fun a : Fin 8193 → ZMod q => ∀ j : T.erase z,
    polynomialFinValue 8193 a (key z) < polynomialFinValue 8193 a (key j.val)) ≤ _ at hp
  rw [probability_congr hevent] at hp
  have hcard : Fintype.card (T.erase z) + 1 = T.card := by
    rw [Fintype.card_coe]
    exact Finset.card_erase_add_one hz
  have hcardr : (Fintype.card (T.erase z) : ℝ) + 1 = (T.card : ℝ) := by exact_mod_cast hcard
  simpa only [probability, strictSeeds, hcardr] using hp

/-- The explicit polynomial coefficient family, sorted by hash and input order, is
3/2-approximately minwise. Different coefficient seeds are counted with multiplicity. -/
theorem polynomial_order_minwise {q : ℕ} [Fact q.Prime] {V : Type*} [LinearOrder V]
    (key : V ↪ ZMod q) (hq : 8193 ≤ q) (T : Finset V) (z : V) (hz : z ∈ T)
    (hsize : 4 * (T.card : ℝ) ^ 2 ≤ (q : ℝ)) :
    ((firstSeeds Finset.univ (polynomialNatHash key) T z).card : ℝ) /
      (q : ℝ) ^ 8193 ≤ 3 / (2 * (T.card : ℝ)) := by
  have hspos : (0 : ℝ) < (Fintype.card (Fin 8193 → ZMod q) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Fin 8193 → ZMod q))
  have hstrict := polynomial_strictSeeds_bound key hq T z hz
  have hstrict' : ((strictSeeds Finset.univ (polynomialNatHash key) T z).card : ℝ) ≤
      5 * ((Finset.univ : Finset (Fin 8193 → ZMod q)).card : ℝ) / (4 * (T.card : ℝ)) := by
    have h := (div_le_iff₀ hspos).mp hstrict
    simpa only [Finset.card_univ, div_mul_eq_mul_div, mul_assoc] using h
  have hcol : ∀ y ∈ T.erase z,
      ((collisionSeeds Finset.univ (polynomialNatHash key) z y).card : ℝ) ≤
        ((Finset.univ : Finset (Fin 8193 → ZMod q)).card : ℝ) / (q : ℝ) := by
    intro y hy
    have hzy : key z ≠ key y := fun heq =>
      (Finset.mem_erase.mp hy).1 (key.injective heq).symm
    have hp := polynomial_collision hq (key z) (key y) hzy
    have hevent (a : Fin 8193 → ZMod q) :
        polynomialFinValue 8193 a (key z) = polynomialFinValue 8193 a (key y) ↔
        polynomialNatHash key a z = polynomialNatHash key a y := Fin.ext_iff
    rw [probability_congr hevent] at hp
    have heq : ((collisionSeeds Finset.univ (polynomialNatHash key) z y).card : ℝ) /
        (Fintype.card (Fin 8193 → ZMod q) : ℝ) = 1 / (q : ℝ) := hp
    have hc := (div_le_iff₀ hspos).mp heq.le
    simpa only [Finset.card_univ, one_div_mul_eq_div] using hc
  have hf := first_probability_bound Finset.univ Finset.univ_nonempty (polynomialNatHash key)
    T ⟨z, hz⟩ z (q : ℝ) hsize hstrict' hcol
  simpa only [Finset.card_univ, polynomialFinValue_seed_card, Nat.cast_pow] using hf

end StableMSR.Recovery.Derandomization



set_option autoImplicit false
open scoped Classical BigOperators

namespace StableMSR.Recovery.Derandomization

/-- A fully explicit finite polynomial family on the input indices. For a prime
q at least max(8193,4m²), ordering by the polynomial value and then input index
makes every member of a nonempty T first with probability at most 3/(2|T|).
Seeds are counted with multiplicity; no RAM enumeration claim is made here. -/
theorem explicit_polynomial_minwise (q m : ℕ) [Fact q.Prime]
    (hq : 8193 ≤ q) (hm : 4*m^2 ≤ q) :
    let hash : (Fin 8193 → ZMod q) → Fin m → ℕ := fun a x =>
      (∑ i : Fin 8193, a i * (x.val : ZMod q) ^ (i : ℕ)).val
    ∀ (T : Finset (Fin m)) (z : Fin m), z ∈ T →
      (((Finset.univ : Finset (Fin 8193 → ZMod q)).filter (fun a =>
        ∀ y ∈ T, y ≠ z →
          hash a z < hash a y ∨ (hash a z = hash a y ∧ z < y))).card : ℝ) /
        (q : ℝ)^8193 ≤ 3 / (2*(T.card : ℝ)) := by
  have hmq : m ≤ q := by
    by_cases hzero : m = 0
    · omega
    have hmpos : 1 ≤ m := by omega
    nlinarith [Nat.mul_le_mul_left m hmpos]
  let key : Fin m ↪ ZMod q := ⟨fun x => (x.val : ZMod q), by
    intro x y hxy
    apply Fin.ext
    have he := congrArg ZMod.val hxy
    simpa only [ZMod.val_natCast_of_lt (x.isLt.trans_le hmq),
      ZMod.val_natCast_of_lt (y.isLt.trans_le hmq)] using he⟩
  dsimp only
  intro T z hz
  have hcard : T.card ≤ m := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
  have hsize : 4*(T.card : ℝ)^2 ≤ (q : ℝ) := by
    exact_mod_cast (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hcard 2)).trans hm
  have hkey (x : Fin m) : key x = (x.val : ZMod q) := rfl
  have hp := polynomial_order_minwise key hq T z hz hsize
  simpa only [firstSeeds, polynomialNatHash, polynomialFinValue_val, HashBefore, hkey] using hp

end StableMSR.Recovery.Derandomization

open StableMSR.Recovery.Derandomization

theorem solution (q m : ℕ) [Fact q.Prime]
    (hq : 8193 ≤ q) (hm : 4*m^2 ≤ q) :
    let hash : (Fin 8193 → ZMod q) → Fin m → ℕ := fun a x =>
      (∑ i : Fin 8193, a i * (x.val : ZMod q) ^ (i : ℕ)).val
    ∀ (T : Finset (Fin m)) (z : Fin m), z ∈ T →
      (((Finset.univ : Finset (Fin 8193 → ZMod q)).filter (fun a =>
        ∀ y ∈ T, y ≠ z →
          hash a z < hash a y ∨ (hash a z = hash a y ∧ z < y))).card : ℝ) /
        (q : ℝ)^8193 ≤ 3 / (2*(T.card : ℝ)) := by
  exact explicit_polynomial_minwise q m hq hm
