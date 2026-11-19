-- Prove2me | solution 1 for TightCoreset2027.Euclidean.projection_family_of_binary_code
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:10:26.315208+00:00
-- url     : https://prove2.me/submissions/adbaaabd-3bb5-4027-8b21-239d586d0432

import Definitions.Def_TightCoreset2027_Euclidean_projectionModel
import Theorems.Thm_TightCoreset2027_Euclidean_moment_interpolation
import Mathlib.Probability.Distributions.Uniform
set_option maxHeartbeats 1000000

open scoped BigOperators
set_option autoImplicit false
namespace TightCoreset2027.Euclidean

noncomputable def coordEquiv (L : ℕ) : Fin (2 * L) ≃ Fin L × ZMod 2 :=
  Fintype.equivOfCardEq (by simp [Nat.mul_comm])

noncomputable def codePoint {L : ℕ} (b : Fin L → ZMod 2) : ProjectionSpace L :=
  WithLp.toLp 2 (fun h => if (coordEquiv L h).2 = b (coordEquiv L h).1 then
    (Real.sqrt (L : ℝ))⁻¹ else 0)

noncomputable def signDirection {L : ℕ} (r : (Fin L × ZMod 2) → Bool) : ProjectionSpace L :=
  WithLp.toLp 2 (fun h => (if r (coordEquiv L h) then (-1 : ℝ) else 1) /
    Real.sqrt (L : ℝ))

noncomputable def directionLevel {L : ℕ} (b : Fin L → ZMod 2) (v : ProjectionSpace L) :
    Fin (L + 1) := by
  classical
  exact ⟨(Finset.univ.filter (fun a => v ((coordEquiv L).symm (a, b a)) < 0)).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin L))⟩

private lemma sqrt_nat_ne {L : ℕ} (hL : 1 ≤ L) : Real.sqrt (L : ℝ) ≠ 0 := by
  positivity

lemma codePoint_norm_sq {L : ℕ} (hL : 1 ≤ L) (b : Fin L → ZMod 2) :
    ‖codePoint b‖ ^ 2 = 1 := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ h : Fin (2 * L), (if (coordEquiv L h).2 = b (coordEquiv L h).1 then
    (Real.sqrt (L : ℝ))⁻¹ else 0) ^ 2) = 1
  rw [← (coordEquiv L).symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  simp only [ite_pow, zero_pow (by decide : 2 ≠ 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ L)]
  exact mul_inv_cancel₀ (by positivity)

lemma codePoint_norm {L : ℕ} (hL : 1 ≤ L) (b : Fin L → ZMod 2) : ‖codePoint b‖ = 1 := by
  have := codePoint_norm_sq hL b
  nlinarith [norm_nonneg (codePoint b)]

lemma codePoint_injective {L : ℕ} (hL : 1 ≤ L) :
    Function.Injective (codePoint (L := L)) := by
  classical
  intro b c heq
  funext a
  have h := congrArg (fun x : ProjectionSpace L => x ((coordEquiv L).symm (a, b a))) heq
  change (if (coordEquiv L ((coordEquiv L).symm (a, b a))).2 = b (coordEquiv L ((coordEquiv L).symm (a, b a))).1 then
    (Real.sqrt (L : ℝ))⁻¹ else 0) =
      (if (coordEquiv L ((coordEquiv L).symm (a, b a))).2 = c (coordEquiv L ((coordEquiv L).symm (a, b a))).1 then
        (Real.sqrt (L : ℝ))⁻¹ else 0) at h
  simp only [Equiv.apply_symm_apply, ite_true] at h
  split_ifs at h with hbc
  · exact hbc
  · exact False.elim ((inv_ne_zero (sqrt_nat_ne hL)) h)

lemma signDirection_norm_sq {L : ℕ} (hL : 1 ≤ L)
    (r : (Fin L × ZMod 2) → Bool) : ‖signDirection r‖ ^ 2 = 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ h : Fin (2 * L), ((if r (coordEquiv L h) then (-1 : ℝ) else 1) /
    Real.sqrt (L : ℝ)) ^ 2) = 2
  have hv (h : Fin (2 * L)) :
      ((if r (coordEquiv L h) then (-1 : ℝ) else 1) / Real.sqrt (L : ℝ)) ^ 2 =
        (L : ℝ)⁻¹ := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    split_ifs <;> norm_num
  simp only [hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_ofNat]
  field_simp

lemma directionLevel_eq_count {L : ℕ} (hL : 1 ≤ L)
    (b : Fin L → ZMod 2) (r : (Fin L × ZMod 2) → Bool) :
    (directionLevel b (signDirection r)).val =
      (Finset.univ.filter (fun a => r (a, b a) = true)).card := by
  classical
  change (Finset.univ.filter (fun a => (signDirection r) ((coordEquiv L).symm (a, b a)) < 0)).card = _
  congr 1
  apply Finset.filter_congr
  intro a ha
  change ((if r (coordEquiv L ((coordEquiv L).symm (a, b a))) then (-1 : ℝ) else 1) /
    Real.sqrt (L : ℝ) < 0) ↔ _
  simp only [Equiv.apply_symm_apply]
  have hs : 0 < Real.sqrt (L : ℝ) := by positivity
  cases hr : r (a, b a) <;> simp [hr, hs, div_neg_iff, not_lt_of_ge hs.le]

lemma codePoint_inner {L : ℕ} (hL : 1 ≤ L) (b : Fin L → ZMod 2)
    (r : (Fin L × ZMod 2) → Bool) :
    inner ℝ (codePoint b) (signDirection r) =
      gridValue L (directionLevel b (signDirection r)) := by
  classical
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  change (∑ h : Fin (2 * L),
    ((if r (coordEquiv L h) then (-1 : ℝ) else 1) / Real.sqrt (L : ℝ)) *
      (if (coordEquiv L h).2 = b (coordEquiv L h).1 then (Real.sqrt (L : ℝ))⁻¹ else 0)) = _
  rw [← (coordEquiv L).symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  have hinv : (Real.sqrt (L : ℝ))⁻¹ ^ 2 = (L : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  have hterm (a : Fin L) (β : ZMod 2) :
      ((if r (a, β) then (-1 : ℝ) else 1) / Real.sqrt (L : ℝ)) *
        (if β = b a then (Real.sqrt (L : ℝ))⁻¹ else 0) =
      if β = b a then (if r (a, β) then (-1 : ℝ) else 1) / (L : ℝ) else 0 := by
    split_ifs <;> simp [*, div_eq_mul_inv] <;> nlinarith only [hinv]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [gridValue, directionLevel_eq_count hL]
  have hs (a : Fin L) : (if r (a, b a) then (-1 : ℝ) else 1) / (L : ℝ) =
      (1 - 2 * (if r (a, b a) = true then 1 else 0 : ℝ)) / (L : ℝ) := by
    cases r (a, b a) <;> norm_num
  simp_rw [hs]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

end TightCoreset2027.Euclidean

open scoped BigOperators
set_option autoImplicit false

namespace TightCoreset2027.Euclidean

private lemma bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide


noncomputable def binarySign : AddChar (ZMod 2) ℝ where
  toFun x := (-1 : ℝ) ^ x.val
  map_zero_eq_one' := by norm_num
  map_add_eq_mul' := by
    intro x y
    rcases bit_cases x with rfl|rfl <;> rcases bit_cases y with rfl|rfl <;>
      norm_num [show (1 : ZMod 2).val = 1 by decide, show (2 : ZMod 2).val = 0 by decide]

@[simp] lemma binarySign_zero : binarySign 0 = 1 := by rfl
@[simp] lemma binarySign_one : binarySign 1 = -1 := by
  change (-1 : ℝ) ^ (1 : ZMod 2).val = -1
  rw [show (1 : ZMod 2).val = 1 by decide]; norm_num

lemma binarySign_eq (x : ZMod 2) : binarySign x = if x = 1 then -1 else 1 := by
  rcases bit_cases x with rfl|rfl <;> simp [binarySign_zero, binarySign_one]

noncomputable def featureChar {I : Type*} [Fintype I] (f : I → ZMod 2) :
    AddChar (I → ZMod 2) ℝ where
  toFun r := binarySign (∑ i, r i * f i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro r s
    simp [add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul]

@[simp] lemma featureChar_zero {I : Type*} [Fintype I] :
    featureChar (0 : I → ZMod 2) = 0 := by
  ext r
  simp [featureChar]

lemma featureChar_add {I : Type*} [Fintype I] (f g : I → ZMod 2) (r : I → ZMod 2) :
    featureChar (f + g) r = featureChar f r * featureChar g r := by
  simp [featureChar, mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul]

lemma featureChar_ne_zero {I : Type*} [Fintype I] {f : I → ZMod 2} (hf : f ≠ 0) :
    featureChar f ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    contrapose! hf
    ext i
    exact hf i
  have hfi : f i = 1 := by
    exact (bit_cases (f i)).resolve_left hi
  intro h
  have hh := congrArg (fun χ : AddChar (I → ZMod 2) ℝ => χ (Pi.single i (1 : ZMod 2))) h
  have hs : (∑ j, (Pi.single i (1 : ZMod 2) : I → ZMod 2) j * f j) = 1 := by
    rw [Finset.sum_eq_single i]
    · simp [hfi]
    · intro j hj hji
      simp [Pi.single_apply, hji]
    · simp
  simp only [featureChar, AddChar.coe_mk, hs, binarySign_one, AddChar.zero_apply] at hh
  norm_num at hh

lemma featureChar_sum {I : Type*} [Fintype I] [DecidableEq I] (f : I → ZMod 2) :
    ∑ r, featureChar f r = if f = 0 then (Fintype.card (I → ZMod 2) : ℝ) else 0 := by
  classical
  by_cases h : f = 0
  · simp [h]
  · rw [if_neg h]
    exact AddChar.sum_eq_zero_iff_ne_zero.mpr (featureChar_ne_zero h)

noncomputable def wordFeature {L : ℕ} (b : Fin L → ZMod 2) : (Fin L × ZMod 2) → ZMod 2 :=
  fun i => if i.2 = b i.1 then 1 else 0

lemma wordFeature_one {L : ℕ} (b : Fin L → ZMod 2) (a : Fin L) :
    wordFeature b (a, 1) = b a := by
  change (if (1 : ZMod 2) = b a then 1 else 0) = b a
  rcases bit_cases (b a) with h|h <;> rw [h] <;> norm_num

lemma wordFeature_sum_ne {L : ℕ} (S : Finset (Fin L → ZMod 2))
    (hS : ∑ b ∈ S, b ≠ 0) : ∑ b ∈ S, wordFeature b ≠ 0 := by
  intro h
  apply hS
  ext a
  have hh := congrFun h (a, 1)
  simpa [Finset.sum_apply, wordFeature_one] using hh

lemma wordFeature_dot {L : ℕ} (b : Fin L → ZMod 2) (r : (Fin L × ZMod 2) → ZMod 2) :
    ∑ i, r i * wordFeature b i = ∑ a, r (a, b a) := by
  classical
  simp [wordFeature, Fintype.sum_prod_type, mul_ite]

lemma wordFeatureChar_prod {L : ℕ} (b : Fin L → ZMod 2)
    (r : (Fin L × ZMod 2) → ZMod 2) :
    featureChar (wordFeature b) r = ∏ a, binarySign (r (a, b a)) := by
  change binarySign (∑ i, r i * wordFeature b i) = _
  rw [wordFeature_dot]
  generalize (Finset.univ : Finset (Fin L)) = S
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp [ha, AddChar.map_add_eq_mul, ih]

end TightCoreset2027.Euclidean

open scoped BigOperators
set_option autoImplicit false
set_option linter.all false
namespace TightCoreset2027.Euclidean

@[simp] private lemma binary_add_self {I : Type*} (f : I → ZMod 2) : f + f = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (f i)

@[simp] private lemma binary_add_cancel_left {I : Type*} (f g : I → ZMod 2) : f + (f + g) = g := by
  rw [← add_assoc, binary_add_self, zero_add]

private lemma binary_add_zero_iff {I : Type*} (f g : I → ZMod 2) : f + g = 0 ↔ f = g := by
  constructor
  · intro h
    have := congrArg (fun a => a + g) h
    simpa [add_assoc] using this
  · rintro rfl; exact binary_add_self _

lemma wordFeature_injective {L : ℕ} : Function.Injective (wordFeature (L := L)) := by
  intro b c h
  ext a
  have := congrFun h (a, 1)
  simpa [wordFeature_one] using this

lemma four_features_eq_zero_iff {L q : ℕ} (S : Finset (Fin L → ZMod 2))
    (B : Fin q → Fin L → ZMod 2) (hB : Function.Injective B)
    (hBS : ∀ i, B i ∈ S)
    (hfour : ∀ T ⊆ S, T.card = 4 → ∑ x ∈ T, x ≠ 0)
    (a b c d : Fin q) :
    wordFeature (B a) + wordFeature (B b) + wordFeature (B c) + wordFeature (B d) = 0 ↔
      (a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  let f := fun i => wordFeature (B i)
  have hf : Function.Injective f := wordFeature_injective.comp hB
  have htwo (i j : Fin q) : f i + f j = 0 ↔ i = j := by
    rw [binary_add_zero_iff]; exact hf.eq_iff
  change f a + f b + f c + f d = 0 ↔ _
  constructor
  · intro h
    by_cases hab : a = b
    · subst b
      simp only [binary_add_self, zero_add] at h
      exact Or.inl ⟨rfl, (htwo c d).mp h⟩
    by_cases hac : a = c
    · subst c
      have hh : f b + f d = 0 := by convert h using 1 <;> simp [add_comm, add_left_comm]
      exact Or.inr (Or.inl ⟨rfl, (htwo b d).mp hh⟩)
    by_cases had : a = d
    · subst d
      have hh : f b + f c = 0 := by convert h using 1 <;> simp [add_comm, add_left_comm]
      exact Or.inr (Or.inr ⟨rfl, (htwo b c).mp hh⟩)
    have hbc : b ≠ c := by
      intro heq; subst c
      have hh : f a + f d = 0 := by convert h using 1 <;> simp [add_assoc]
      exact had ((htwo a d).mp hh)
    have hbd : b ≠ d := by
      intro heq; subst d
      have hh : f a + f c = 0 := by convert h using 1 <;> simp [add_comm, add_left_comm]
      exact hac ((htwo a c).mp hh)
    have hcd : c ≠ d := by
      intro heq; subst d
      have hh : f a + f b = 0 := by convert h using 1 <;> simp [add_assoc]
      exact hab ((htwo a b).mp hh)
    have hne : ∑ x ∈ ({B a, B b, B c, B d} : Finset (Fin L → ZMod 2)), x ≠ 0 := by
      apply hfour _
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl|rfl|rfl|rfl <;> exact hBS _
      · simp [hB.eq_iff, hab, hac, had, hbc, hbd, hcd]
    have hfeat := wordFeature_sum_ne _ hne
    apply False.elim
    apply hfeat
    simpa [f, hB.eq_iff, hab, hac, had, hbc, hbd, hcd, add_assoc] using h
  · rintro (⟨rfl, rfl⟩|⟨rfl, rfl⟩|⟨rfl, rfl⟩) <;> simp [add_comm, add_left_comm]

lemma finite_second_moment {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (χ : ι → Ω → ℝ) (N : ℝ)
    (h2 : ∀ a b, ∑ ω, χ a ω * χ b ω = if a = b then N else 0)
    (A : ι → ℝ) :
    ∑ ω, (∑ a, A a * χ a ω) ^ 2 = N * ∑ a, A a ^ 2 := by
  classical
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  simp_rw [show ∀ b ω, A a * χ a ω * (A b * χ b ω) =
    (A a * A b) * (χ a ω * χ b ω) by intros; ring]
  simp_rw [← Finset.mul_sum, h2, mul_ite, mul_zero]
  simp [Finset.sum_ite_eq, mul_assoc, mul_comm]

lemma finite_fourth_moment {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (χ : ι → Ω → ℝ) (N : ℝ)
    (h4 : ∀ a b c d, ∑ ω, χ a ω * χ b ω * χ c ω * χ d ω =
      if (a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c) then N else 0)
    (A : ι → ℝ) :
    ∑ ω, (∑ a, A a * χ a ω) ^ 4 =
      N * (3 * (∑ a, A a ^ 2) ^ 2 - 2 * ∑ a, A a ^ 4) := by
  classical
  have hexpand (ω : Ω) : (∑ a, A a * χ a ω) ^ 4 =
      ∑ a, ∑ b, ∑ c, ∑ d,
        (A a * A b * A c * A d) * (χ a ω * χ b ω * χ c ω * χ d ω) := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    congr 1; funext a
    congr 1; funext b
    congr 1; funext c
    congr 1; funext d
    ring
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]; arg 2; ext b; rw [Finset.sum_comm]; arg 2; ext c; rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, h4]
  have hind (a b c d : ι) :
      (A a * A b * A c * A d) *
        (if (a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c) then N else 0) =
      N * ((if a = b then (if c = d then A a ^ 2 * A c ^ 2 else 0) else 0) +
        (if a = c then (if b = d then A a ^ 2 * A b ^ 2 else 0) else 0) +
        (if a = d then (if b = c then A a ^ 2 * A b ^ 2 else 0) else 0) -
        2 * (if a = b then (if b = c then (if c = d then A a ^ 4 else 0) else 0) else 0)) := by
    by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases had : a = d <;>
      by_cases hbc : b = c <;> by_cases hbd : b = d <;> by_cases hcd : c = d <;>
      simp_all <;> ring
  simp_rw [hind]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

lemma featureChar_moments {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}
    (f : Fin q → I → ZMod 2) (hf : Function.Injective f)
    (hfour : ∀ a b c d, f a + f b + f c + f d = 0 ↔
      (a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    (A : Fin q → ℝ) :
    (∑ r, (∑ a, A a * featureChar (f a) r) ^ 2 =
      (Fintype.card (I → ZMod 2) : ℝ) * ∑ a, A a ^ 2) ∧
    (∑ r, (∑ a, A a * featureChar (f a) r) ^ 4 =
      (Fintype.card (I → ZMod 2) : ℝ) *
        (3 * (∑ a, A a ^ 2) ^ 2 - 2 * ∑ a, A a ^ 4)) := by
  classical
  constructor
  · apply finite_second_moment
    intro a b
    simp_rw [← featureChar_add]
    rw [featureChar_sum]
    have heq : f a + f b = 0 ↔ a = b := (binary_add_zero_iff _ _).trans hf.eq_iff
    simp only [heq]
  · apply finite_fourth_moment
    intro a b c d
    simp_rw [← featureChar_add]
    rw [featureChar_sum]
    simp only [hfour]

end TightCoreset2027.Euclidean

open scoped BigOperators
open MeasureTheory
set_option autoImplicit false
set_option linter.all false
namespace TightCoreset2027.Euclidean

lemma uniform_integral {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (g : Ω → ℝ) :
    ∫ ω, g ω ∂(PMF.uniformOfFintype Ω).toMeasure =
      (∑ ω, g ω) / (Fintype.card Ω : ℝ) := by
  rw [integral_fintype (by fun_prop)]
  have hμ (ω : Ω) : (PMF.uniformOfFintype Ω).toMeasure.real {ω} =
      (Fintype.card Ω : ℝ)⁻¹ := by
    rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp_rw [hμ, smul_eq_mul]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

lemma finite_abs_average_lower {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Y : Ω → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (h2 : ∑ ω, (Y ω) ^ 2 = (Fintype.card Ω : ℝ) * a ^ 2)
    (h4 : ∑ ω, (Y ω) ^ 4 ≤ 3 * (Fintype.card Ω : ℝ) * a ^ 4) :
    (1 / Real.sqrt 3) * a ≤ (∑ ω, |Y ω|) / (Fintype.card Ω : ℝ) := by
  classical
  letI : MeasurableSpace Ω := ⊤
  let μ := (PMF.uniformOfFintype Ω).toMeasure
  have hN : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  by_cases ha0 : a = 0
  · simp only [ha0, mul_zero]
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hN.le
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  obtain ⟨ω, hω⟩ : ∃ ω, Y ω ≠ 0 := by
    by_contra! hz
    have hh : (∑ ω, (Y ω) ^ 2) = 0 := by simp [hz]
    have hp : 0 < (Fintype.card Ω : ℝ) * a ^ 2 := mul_pos hN (sq_pos_of_pos hap)
    linarith
  have h4p : 0 < ∑ ω, |Y ω| ^ 4 := by
    apply Finset.sum_pos'
    · intro i hi; positivity
    · exact ⟨ω, Finset.mem_univ _, pow_pos (abs_pos.mpr hω) _⟩
  have hpos : 0 < ∫ ω, |Y ω| ^ 4 ∂μ := by
    rw [uniform_integral]
    exact div_pos h4p hN
  have hi := moment_interpolation μ Y (by fun_prop) Integrable.of_finite hpos
  have hE2 : (∫ ω, |Y ω| ^ 2 ∂μ) = a ^ 2 := by
    rw [uniform_integral]
    simp_rw [sq_abs]
    rw [h2, mul_div_cancel_left₀ _ hN.ne']
  have hE4 : (∫ ω, |Y ω| ^ 4 ∂μ) ≤ 3 * a ^ 4 := by
    rw [uniform_integral]
    simp_rw [show ∀ x : ℝ, |x| ^ 4 = x ^ 4 by intro x; exact_mod_cast (abs_pow x 4).symm.trans (abs_of_nonneg (by positivity))]
    apply (div_le_iff₀ hN).mpr
    nlinarith [h4]
  have hsqrt : Real.sqrt (∫ ω, |Y ω| ^ 4 ∂μ) ≤ Real.sqrt 3 * a ^ 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith only [hE4]
  have hrpow : Real.rpow (a ^ 2) ((3 : ℝ) / 2) = a ^ 3 := by
    rw [Real.rpow_eq_pow, Real.rpow_div_two_eq_sqrt _ (sq_nonneg a), Real.sqrt_sq ha]
    exact Real.rpow_natCast a 3
  rw [hE2, hrpow] at hi
  have hsp : 0 < Real.sqrt (∫ ω, |Y ω| ^ 4 ∂μ) := Real.sqrt_pos.mpr hpos
  have h3p : 0 < Real.sqrt 3 := by positivity
  have hE1 : 0 ≤ ∫ ω, |Y ω| ∂μ := integral_nonneg (fun ω => abs_nonneg _)
  have hmul := (div_le_iff₀ hsp).mp hi
  have hfinal : a ≤ Real.sqrt 3 * ∫ ω, |Y ω| ∂μ := by
    have hh := mul_le_mul_of_nonneg_left hsqrt hE1
    have hhbound : a ^ 2 * a ≤ a ^ 2 * (Real.sqrt 3 * ∫ ω, |Y ω| ∂μ) := by
      nlinarith only [hmul, hh]
    exact le_of_mul_le_mul_left hhbound (sq_pos_of_pos hap)
  rw [show (1 / Real.sqrt 3) * a = a / Real.sqrt 3 by ring]
  apply (div_le_iff₀ h3p).mpr
  simpa [uniform_integral, μ, mul_comm] using hfinal

end TightCoreset2027.Euclidean

open scoped BigOperators
set_option autoImplicit false
set_option linter.all false
namespace TightCoreset2027.Euclidean

lemma featureChar_directionLevel {L : ℕ} (hL : 1 ≤ L) (b : Fin L → ZMod 2)
    (r : (Fin L × ZMod 2) → ZMod 2) :
    (-1 : ℝ) ^ (directionLevel b (signDirection (fun i => decide (r i = 1)))).val =
      featureChar (wordFeature b) r := by
  classical
  rw [directionLevel_eq_count hL, wordFeatureChar_prod]
  simp_rw [binarySign_eq]
  simp only [decide_eq_true_eq]
  rw [Finset.prod_ite]
  simp

 theorem projection_realization (L q : ℕ) (hL : 1 ≤ L) (_hq : 1 ≤ q)
    (S : Finset (Fin L → ZMod 2)) (hS : S.card = q)
    (hfour : ∀ T ⊆ S, T.card = 4 → ∑ x ∈ T, x ≠ 0) :
    ∃ G : ProjectionFamily L q, ProjectionSpecification G := by
  classical
  let e : Fin q ≃ S := (Fintype.equivFinOfCardEq (by simpa using hS)).symm
  let B : Fin q → Fin L → ZMod 2 := fun i => e i
  have hB : Function.Injective B := Subtype.coe_injective.comp e.injective
  have hBS (i : Fin q) : B i ∈ S := (e i).property
  let D : ((Fin L × ZMod 2) → ZMod 2) → ProjectionSpace L :=
    fun r => signDirection (fun i => decide (r i = 1))
  let G : ProjectionFamily L q :=
    { x := fun i => codePoint (B i)
      directions := Finset.univ.image D
      level := fun i => directionLevel (B i) }
  refine ⟨G, ?_, ?_⟩
  · refine ⟨(codePoint_injective hL).comp hB, ?_, ?_, ?_, ?_⟩
    · exact fun i => codePoint_norm hL (B i)
    · exact Finset.image_nonempty.mpr Finset.univ_nonempty
    · intro v hv
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hv
      exact signDirection_norm_sq hL _
    · intro i v hv
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hv
      exact codePoint_inner hL _ _
  · intro t ht A
    let f := fun i => wordFeature (B i)
    have hf : Function.Injective f := wordFeature_injective.comp hB
    have h4 := four_features_eq_zero_iff S B hB hBS hfour
    let N : ℝ := Fintype.card ((Fin L × ZMod 2) → ZMod 2)
    have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
    have hav (j : Fin t) :
        (1 / Real.sqrt 3) * ‖A j‖ ≤
          (∑ r, |∑ i, A j i * featureChar (f i) r|) / N := by
      obtain ⟨h2, h4exact⟩ := featureChar_moments f hf h4 (fun i => A j i)
      apply finite_abs_average_lower _ ‖A j‖ (norm_nonneg _)
      · simpa [N, EuclideanSpace.real_norm_sq_eq] using h2
      · have hpow : (∑ i, A j i ^ 2) ^ 2 = ‖A j‖ ^ 4 := by
          rw [← EuclideanSpace.real_norm_sq_eq]
          ring
        rw [h4exact, hpow]
        have hn : 0 ≤ ∑ i, A j i ^ 4 := Finset.sum_nonneg (fun _ _ => by positivity)
        dsimp [N]
        nlinarith
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hav j)
    have hbound : (1 / Real.sqrt 3) * (∑ j, ‖A j‖) ≤
        (∑ r, ∑ j, |∑ i, A j i * featureChar (f i) r|) / N := by
      rw [Finset.sum_comm]
      simpa only [Finset.mul_sum, Finset.sum_div] using hsum
    obtain ⟨r, hr⟩ : ∃ r, (1 / Real.sqrt 3) * (∑ j, ‖A j‖) ≤
        ∑ j, |∑ i, A j i * featureChar (f i) r| := by
      by_contra! h
      have hs := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun r _ => h r)
      have hlt : (∑ r, ∑ j, |∑ i, A j i * featureChar (f i) r|) / N <
          (1 / Real.sqrt 3) * (∑ j, ‖A j‖) := by
        apply (div_lt_iff₀ hN).mpr
        simpa [N, mul_comm] using hs
      linarith
    refine ⟨D r, Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩, ?_⟩
    simpa only [G, D, featureChar_directionLevel hL] using hr

end TightCoreset2027.Euclidean
 theorem solution (L q : ℕ) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (S : Finset (Fin L → ZMod 2)) (hS : S.card = q)
    (hfour : ∀ T ⊆ S, T.card = 4 → ∑ x ∈ T, x ≠ 0) :
    ∃ G : TightCoreset2027.Euclidean.ProjectionFamily L q,
      TightCoreset2027.Euclidean.ProjectionSpecification G := by
  exact TightCoreset2027.Euclidean.projection_realization L q hL hq S hS hfour
