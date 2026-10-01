-- Prove2me | solution 1 for PhilipponMultiplicity.section_three_initial_hilbert_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T13:59:45.574987+00:00
-- url     : https://prove2.me/submissions/2034e8b4-eb14-44ea-ab61-0e312560c182

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Tactic
import Theorems.Thm_PhilipponMultiplicity_Hilbert_component_length_formula
import Theorems.Thm_PhilipponMultiplicity_Hilbert_primaryComponent_degreeValue_eq_localLength
import Theorems.Thm_PhilipponMultiplicity_Hilbert_exists_relevant_minimalPrime_dimension_eq


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

end MultiProjectiveSpace
end PhilipponMultiplicity
end


set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem isHomogeneous_X (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun i => if i = v.1 then 1 else 0) := by
  classical
  intro a ha i
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  rcases v with ⟨b, j⟩
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b, j⟩ : M.Variable) ≠ ⟨i, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, hi, hn]

theorem isHomogeneous_C (c : K) : M.IsHomogeneous (MvPolynomial.C c) 0 := by
  classical
  intro a ha i
  have ha0 : a = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  simp [ha0]

theorem IsHomogeneous.add {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  classical
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

theorem IsHomogeneous.neg {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : M.IsHomogeneous (-P) D := by
  intro a ha i
  exact hP a (by simpa only [MvPolynomial.support_neg] using ha) i

theorem IsHomogeneous.sub {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  simpa only [sub_eq_add_neg] using hP.add M (hQ.neg M)

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

theorem IsHomogeneous.nat_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : ℕ) : M.IsHomogeneous (c * P) D := by
  simpa only [map_natCast] using hP.C_mul M (c : K)

theorem IsHomogeneous.pow {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (n : ℕ) :
    M.IsHomogeneous (P ^ n) (fun i => n * D i) := by
  induction n with
  | zero =>
    convert M.isHomogeneous_one using 1
    · simp
    · funext i; simp
  | succ n ih =>
    convert ih.mul M hP using 1
    · exact pow_succ P n
    · funext i; simp [Nat.succ_mul]

end PhilipponMultiplicity.MultiProjectiveSpace
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem blockWeight_apply (d : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d) i =
      ∑ j : Fin (M.ambientDimension i + 1), d ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex,
    ∑ j : Fin (M.ambientDimension b + 1),
      d ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem degreePiece_iff (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    P ∈ Hilbert.degreePiece K M.factorCount M.ambientDimension D ↔ M.IsHomogeneous P D := by
  change (∀ d, coeff d P ≠ 0 →
    Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d = D) ↔ _
  simp only [← mem_support_iff]
  constructor
  · intro h d hd i
    exact (M.blockWeight_apply d i).symm.trans (congrFun (h d hd) i)
  · intro h d hd
    funext i
    rw [M.blockWeight_apply]
    exact h d hd i

end PhilipponMultiplicity.MultiProjectiveSpace
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [Field K]

theorem homogeneous_span (M : MultiProjectiveSpace K) (S : Set M.CoordinateRing)
    (hS : ∀ P ∈ S, ∃ D, M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (Ideal.span S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hh : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D,hD⟩ := hS P hP
    exact ⟨D,(M.degreePiece_iff P D).mpr hD⟩
  intro P hP D
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP D

end PhilipponMultiplicity.OperatorSupport
end


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary
open SectionThree

abbrev vindex (j : Fin 5) : ambient.Variable := ⟨(0 : Fin 1), j⟩

theorem X_homogeneous (j : Fin 5) : ambient.IsHomogeneous (X j) (fun _ => 1) := by
  change ambient.IsHomogeneous (MvPolynomial.X (vindex j)) _
  convert ambient.isHomogeneous_X (vindex j) using 1
  funext i
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem firstGenerator_homogeneous : ambient.IsHomogeneous firstGenerator (fun _ => 3) := by
  exact ((X_homogeneous 1).pow ambient 2 |>.mul ambient (X_homogeneous 3)).sub ambient
    ((X_homogeneous 2).pow ambient 2 |>.mul ambient (X_homogeneous 0))

theorem secondGenerator_homogeneous : ambient.IsHomogeneous secondGenerator (fun _ => 2) := by
  exact ((X_homogeneous 1).mul ambient (X_homogeneous 4)).sub ambient
    ((X_homogeneous 2).mul ambient (X_homogeneous 3))

theorem thirdGenerator_homogeneous : ambient.IsHomogeneous thirdGenerator (fun _ => 3) := by
  exact ((X_homogeneous 3).pow ambient 3).sub ambient
    ((X_homogeneous 4).pow ambient 2 |>.mul ambient (X_homogeneous 0))

theorem initial_homogeneous : IsMultihomogeneousIdeal ambient initialIdeal := by
  apply OperatorSupport.homogeneous_span
  rintro P (rfl | rfl | rfl)
  · exact ⟨_, firstGenerator_homogeneous⟩
  · exact ⟨_, secondGenerator_homogeneous⟩
  · exact ⟨_, thirdGenerator_homogeneous⟩

theorem firstEquation_homogeneous : ambient.IsHomogeneous firstEquation (fun _ => 1) :=
  X_homogeneous 3

theorem secondEquation_homogeneous : ambient.IsHomogeneous secondEquation (fun _ => 1) :=
  (X_homogeneous 1).sub ambient (X_homogeneous 4)

/-- The projective point (1:0:0:0:0) witnesses relevance of the printed ideal. -/
theorem initial_nontrivial : IsNontrivialIdeal ambient initialIdeal := by
  classical
  let v : ambient.Variable → ℂ := fun j => if j = vindex 0 then 1 else 0
  have hi : initialIdeal ≤ RingHom.ker (MvPolynomial.eval v) := by
    rw [initialIdeal, Ideal.span_le]
    rintro f (rfl | rfl | rfl) <;>
      simp [RingHom.mem_ker, firstGenerator, secondGenerator, thirdGenerator, X, v, vindex]
  have hq : X 0 ∈ Hilbert.irrelevantIdeal ℂ ambient.factorCount ambient.ambientDimension := by
    rw [Hilbert.irrelevantIdeal, Ideal.mem_iInf]
    intro i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact Ideal.subset_span ⟨0, rfl⟩
  intro h
  obtain ⟨n, hn⟩ := h hq
  have hz := hi hn
  change MvPolynomial.eval v (X 0 ^ n) = 0 at hz
  simpa [X, v, vindex] using hz

end PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary
end

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial
namespace PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary
theorem weight_eq_iff (m : ambient.Variable →₀ ℕ) (d : Fin 1 → ℕ) :
    Finsupp.weight (Hilbert.blockWeight ambient.factorCount ambient.ambientDimension) m = d ↔
      m (vindex 0) + m (vindex 1) + m (vindex 2) + m (vindex 3) + m (vindex 4) = d 0 := by
  have h : (Finsupp.weight (Hilbert.blockWeight ambient.factorCount ambient.ambientDimension) m) (0 : Fin 1) =
      m (vindex 0) + m (vindex 1) + m (vindex 2) + m (vindex 3) + m (vindex 4) := by
    rw [ambient.blockWeight_apply]
    change (∑ j : Fin 5, m (vindex j)) = _
    simp [Fin.sum_univ_succ, add_assoc]
  constructor
  · intro he
    rw [← h, he]
  · intro he
    funext i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact h.trans he

theorem ordinary_weight (m : ambient.Variable →₀ ℕ) :
    Finsupp.weight (1 : ambient.Variable → ℕ) m =
      m (vindex 0) + m (vindex 1) + m (vindex 2) + m (vindex 3) + m (vindex 4) := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ i : Fin 1, ∑ j : Fin 5, m ⟨i,j⟩ • (1 : ℕ)) = _
  simp [Fin.sum_univ_succ, vindex, add_assoc]

theorem degreePiece_ordinary (f : ambient.CoordinateRing) (d : Fin 1 → ℕ) :
    f ∈ Hilbert.degreePiece ℂ ambient.factorCount ambient.ambientDimension d ↔
      f.IsHomogeneous (d 0) := by
  change (∀ m, coeff m f ≠ 0 → _) ↔ (∀ m, coeff m f ≠ 0 → _)
  simp_rw [weight_eq_iff, ordinary_weight]

end PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary
open SectionThree

theorem expected_dimension : expectedInitialHilbertPolynomial.totalDegree = 2 := by
  have ha : (C (2 : ℚ) * (MvPolynomial.X (0 : Fin 1)) ^ 2).totalDegree = 2 :=
    (isHomogeneous_C_mul_X_pow _ _ _).totalDegree (by
      apply mul_ne_zero
      · simpa using (show (2 : ℚ) ≠ 0 by norm_num)
      · exact pow_ne_zero _ (X_ne_zero _))
  have hb : (C (3 : ℚ) * (MvPolynomial.X (0 : Fin 1))).totalDegree = 1 :=
    (isHomogeneous_C_mul_X _ _).totalDegree (by
      apply mul_ne_zero
      · simpa using (show (3 : ℚ) ≠ 0 by norm_num)
      · exact X_ne_zero _)
  have hab : (C (2 : ℚ) * MvPolynomial.X (0 : Fin 1) ^ 2 +
      C (3 : ℚ) * MvPolynomial.X 0).totalDegree = 2 :=
    (totalDegree_add_eq_left_of_totalDegree_lt (by rw [hb, ha]; omega)).trans ha
  have habc : (C (2 : ℚ) * MvPolynomial.X (0 : Fin 1) ^ 2 +
      C (3 : ℚ) * MvPolynomial.X 0 + 1).totalDegree = 2 :=
    (totalDegree_add_eq_left_of_totalDegree_lt (by rw [totalDegree_one, hab]; omega)).trans hab
  simpa only [map_ofNat, expectedInitialHilbertPolynomial] using habc

theorem expected_top : homogeneousComponent 2 expectedInitialHilbertPolynomial =
    C (2 : ℚ) * MvPolynomial.X (0 : Fin 1) ^ 2 := by
  change homogeneousComponent 2
    (C (2 : ℚ) * MvPolynomial.X (0 : Fin 1) ^ 2 + C (3 : ℚ) * MvPolynomial.X 0 + 1) = _
  simp only [map_add,
    homogeneousComponent_of_mem (isHomogeneous_C_mul_X_pow (2 : ℚ) (0 : Fin 1) 2),
    homogeneousComponent_of_mem (isHomogeneous_C_mul_X (3 : ℚ) (0 : Fin 1)),
    homogeneousComponent_of_mem (isHomogeneous_one (σ := Fin 1) ℚ)]
  norm_num

theorem initial_dimension_and_degree
    (hp : Hilbert.hilbertPolynomial ℂ ambient.factorCount ambient.ambientDimension initialIdeal =
      expectedInitialHilbertPolynomial) :
    idealDimension ambient initialIdeal = 2 ∧
      idealDegreeValue ambient initialIdeal (fun _ => 1) = 4 := by
  constructor
  · rw [idealDimension, hp, expected_dimension]
  · unfold idealDegreeValue Hilbert.degreeValue Hilbert.degreeForm
    rw [hp]
    change eval (fun _ : Fin 1 => (1 : ℚ))
      ((expectedInitialHilbertPolynomial.totalDegree.factorial : ℚ) •
        homogeneousComponent expectedInitialHilbertPolynomial.totalDegree expectedInitialHilbertPolynomial) = _
    rw [expected_dimension, expected_top]
    norm_num

end PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary
end


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
open scoped BigOperators MonomialOrder
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponMultiplicity.InitialNormalForms

def ex (e a b c d : ℕ) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![e,a,b,c,d]

@[simp] theorem ex_apply (e a b c d : ℕ) (i : Fin 5) :
    ex e a b c d i = ![e,a,b,c,d] i := rfl

def lead (i : Fin 4) : Fin 5 →₀ ℕ :=
  ![ex 1 0 2 0 0, ex 0 1 0 0 1, ex 1 0 0 0 2, ex 1 0 1 1 1] i

def tail (i : Fin 4) : Fin 5 →₀ ℕ :=
  ![ex 0 2 0 1 0, ex 0 0 1 1 0, ex 0 0 0 3 0, ex 0 1 0 3 0] i

def gen (K : Type*) [Field K] (i : Fin 4) : MvPolynomial (Fin 5) K :=
  monomial (lead i) 1 - monomial (tail i) 1

def ideal (K : Type*) [Field K] : Ideal (MvPolynomial (Fin 5) K) :=
  Ideal.span {gen K 0, gen K 1, gen K 2}

def radicalGenerator (K : Type*) [Field K] : MvPolynomial (Fin 5) K :=
  monomial (ex 1 0 1 0 1) 1 - monomial (ex 0 1 0 2 0) 1

def radicalIdeal (K : Type*) [Field K] : Ideal (MvPolynomial (Fin 5) K) :=
  ideal K ⊔ Ideal.span {radicalGenerator K}

def Normal (m : Fin 5 →₀ ℕ) : Prop :=
  (m 0 = 0 ∨ m 2 < 2) ∧ (m 1 = 0 ∨ m 4 = 0) ∧
  (m 0 = 0 ∨ m 4 < 2) ∧ (m 0 = 0 ∨ m 2 = 0 ∨ m 3 = 0 ∨ m 4 = 0)

def RadicalNormal (m : Fin 5 →₀ ℕ) : Prop :=
  (m 0 = 0 ∨ m 2 < 2) ∧ (m 1 = 0 ∨ m 4 = 0) ∧
  (m 0 = 0 ∨ m 4 < 2) ∧ (m 0 = 0 ∨ m 2 = 0 ∨ m 4 = 0)

theorem ex_le_iff (e a b c d : ℕ) (m : Fin 5 →₀ ℕ) :
    ex e a b c d ≤ m ↔ e ≤ m 0 ∧ a ≤ m 1 ∧ b ≤ m 2 ∧ c ≤ m 3 ∧ d ≤ m 4 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4⟩
  · rintro ⟨h0,h1,h2,h3,h4⟩ i
    fin_cases i <;> assumption

theorem normal_iff (m : Fin 5 →₀ ℕ) :
    Normal m ↔ ∀ i, ¬ lead i ≤ m := by
  simp only [Fin.forall_fin_succ, lead, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.forall_fin_zero, and_true, ex_le_iff]
  unfold Normal
  omega

theorem tail_lt_lead (i : Fin 4) : tail i ≺[MonomialOrder.lex] lead i := by
  change toLex (tail i) < toLex (lead i)
  fin_cases i
  · exact ⟨0, by intro j hj; omega, by simp [tail, lead]⟩
  · refine ⟨1, ?_, by simp [tail, lead]⟩
    intro j hj
    have : j = 0 := by omega
    subst j
    simp [tail, lead]
  · exact ⟨0, by intro j hj; omega, by simp [tail, lead]⟩
  · exact ⟨0, by intro j hj; omega, by simp [tail, lead]⟩

variable (K : Type*) [Field K]

theorem gen_degree (i : Fin 4) : MonomialOrder.lex.degree (gen K i) = lead i := by
  classical
  unfold gen
  rw [MonomialOrder.degree_sub_of_lt, MonomialOrder.degree_monomial]
  · simp
  · simpa [MonomialOrder.degree_monomial] using tail_lt_lead i

theorem gen_leadingCoeff (i : Fin 4) : MonomialOrder.lex.leadingCoeff (gen K i) = 1 := by
  classical
  unfold gen
  rw [MonomialOrder.leadingCoeff_sub_of_lt, MonomialOrder.leadingCoeff_monomial]
  · simpa [MonomialOrder.degree_monomial] using tail_lt_lead i

theorem monomial_ex (e a b c d : ℕ) :
    monomial (ex e a b c d) (1 : K) =
      X 0 ^ e * X 1 ^ a * X 2 ^ b * X 3 ^ c * X 4 ^ d := by
  rw [MvPolynomial.monomial_eq]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_succ, mul_assoc]
  · simp

theorem gen_mem (i : Fin 4) : gen K i ∈ ideal K := by
  have h (j : Fin 4) (hj : j = 0 ∨ j = 1 ∨ j = 2) : gen K j ∈ ideal K := by
    apply Ideal.subset_span
    rcases hj with rfl | rfl | rfl <;> simp
  fin_cases i
  · exact h 0 (Or.inl rfl)
  · exact h 1 (Or.inr (Or.inl rfl))
  · exact h 2 (Or.inr (Or.inr rfl))
  · have heq : gen K 3 = X 1 * gen K 2 - X 0 * X 4 * gen K 1 := by
      simp [gen, lead, tail, monomial_ex]
      ring
    change gen K 3 ∈ ideal K
    rw [heq]
    exact (ideal K).sub_mem ((ideal K).mul_mem_left _ (h 2 (Or.inr (Or.inr rfl))))
      ((ideal K).mul_mem_left _ (h 1 (Or.inr (Or.inl rfl))))

theorem normal_remainder (f : MvPolynomial (Fin 5) K) :
    ∃ r : MvPolynomial (Fin 5) K,
      f - r ∈ ideal K ∧ ∀ m ∈ r.support, Normal m := by
  obtain ⟨g,r,hf,_,hr⟩ := MonomialOrder.lex.div
    (b := gen K) (fun i => by rw [gen_leadingCoeff]; exact isUnit_one) f
  refine ⟨r, ?_, fun m hm => (normal_iff m).mpr ?_⟩
  · rw [hf, add_sub_cancel_right, Finsupp.linearCombination_apply]
    exact (ideal K).sum_mem (fun i _ => (ideal K).mul_mem_left _ (gen_mem K i))
  · simpa only [gen_degree] using hr m hm

def toricExponent : (Fin 5 →₀ ℕ) →+ (Fin 3 →₀ ℕ) where
  toFun m := Finsupp.equivFunOnFinite.symm
    ![3 * m 0 + m 1 + m 3, m 2 + 2 * m 3 + 3 * m 4, m 1 + m 2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' m n := by ext i; fin_cases i <;> simp [mul_add] <;> omega

def toricMap : MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 3) K :=
  AddMonoidAlgebra.mapDomainRingHom K toricExponent

@[simp] theorem toricMap_monomial (m : Fin 5 →₀ ℕ) (c : K) :
    toricMap K (monomial m c) = monomial (toricExponent m) c := by
  exact AddMonoidAlgebra.mapDomain_single

theorem radicalNormal_injective : Set.InjOn toricExponent {m | RadicalNormal m} := by
  intro m hm n hn h
  have h0 := congrArg (fun p : Fin 3 →₀ ℕ => p 0) h
  have h1 := congrArg (fun p : Fin 3 →₀ ℕ => p 1) h
  have h2 := congrArg (fun p : Fin 3 →₀ ℕ => p 2) h
  change 3 * m 0 + m 1 + m 3 = 3 * n 0 + n 1 + n 3 at h0
  change m 2 + 2 * m 3 + 3 * m 4 = n 2 + 2 * n 3 + 3 * n 4 at h1
  change m 1 + m 2 = n 1 + n 2 at h2
  change RadicalNormal m at hm
  change RadicalNormal n at hn
  have small (p : Fin 5 →₀ ℕ) (hp : RadicalNormal p) (he : p 0 ≠ 0) : p 2 + p 4 ≤ 1 := by
    obtain ⟨h1,_,h3,h4⟩ := hp
    omega
  have hrel : 2 * m 0 + n 2 + n 4 = 2 * n 0 + m 2 + m 4 := by omega
  have he : m 0 = n 0 := by
    have hsm := small m hm
    have hsn := small n hn
    clear hm hn small h h0 h1 h2
    by_cases hmE : m 0 = 0 <;> by_cases hnE : n 0 = 0 <;> omega
  have hmAD := hm.2.1
  have hnAD := hn.2.1
  clear hm hn small h
  have ha : m 1 = n 1 := by
    rcases hmAD with hmA | hmD <;> rcases hnAD with hnA | hnD <;> omega
  ext i
  fin_cases i <;> simp only [Fin.reduceFinMk] <;> omega

theorem toricMap_eq_zero_of_normal (f : MvPolynomial (Fin 5) K)
    (hn : ∀ m ∈ f.support, RadicalNormal m) (hf : toricMap K f = 0) : f = 0 := by
  classical
  ext m
  rw [coeff_zero]
  by_contra h
  have hm := mem_support_iff.mpr h
  have hc : coeff (toricExponent m) (toricMap K f) = coeff m f := by
    change Finsupp.mapDomain toricExponent (AddMonoidAlgebra.coeff f) (toricExponent m) = _
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_eq_single m]
    · exact Finsupp.single_eq_same
    · intro b hb hbm
      apply Finsupp.single_eq_of_ne'
      exact fun he => hbm (radicalNormal_injective (hn b (mem_support_iff.mpr hb)) (hn m hm) he)
    · intro hnot
      exact (h hnot).elim
  rw [hf, coeff_zero] at hc
  exact h hc.symm

theorem toricMap_gen (i : Fin 4) : toricMap K (gen K i) = 0 := by
  rw [gen, map_sub, toricMap_monomial, toricMap_monomial, sub_eq_zero]
  apply congrArg (fun e => monomial e (1 : K))
  ext j
  fin_cases i <;> fin_cases j <;> rfl

theorem ideal_le_toric_ker : ideal K ≤ RingHom.ker (toricMap K) := by
  apply Ideal.span_le.mpr
  rintro f (rfl | rfl | rfl) <;> exact toricMap_gen K _

def envelope : Ideal (MvPolynomial (Fin 5) K) :=
  Ideal.span ((fun m => monomial m (1 : K)) ''
    {ex 0 1 0 0 0, ex 0 0 0 1 0, ex 0 0 2 0 0, ex 0 0 0 0 2})

theorem mem_envelope (f : MvPolynomial (Fin 5) K) :
    f ∈ envelope K ↔ ∀ m ∈ f.support,
      1 ≤ m 1 ∨ 1 ≤ m 3 ∨ 2 ≤ m 2 ∨ 2 ≤ m 4 := by
  rw [envelope, mem_ideal_span_monomial_image]
  apply forall₂_congr
  intro m _
  simp [ex_le_iff]

theorem ideal_le_envelope : ideal K ≤ envelope K := by
  apply Ideal.span_le.mpr
  have h (i : Fin 4) : gen K i ∈ envelope K := by
    apply (envelope K).sub_mem
    · rw [mem_envelope]
      intro m hm
      have he : m = lead i := by simpa using support_monomial_subset hm
      subst m
      fin_cases i <;> norm_num [lead, Matrix.cons_val] <;> decide
    · rw [mem_envelope]
      intro m hm
      have he : m = tail i := by simpa using support_monomial_subset hm
      subst m
      fin_cases i <;> norm_num [tail, Matrix.cons_val] <;> decide
  rintro f (rfl | rfl | rfl) <;> exact h _

theorem normal_ideal_eq_zero (f : MvPolynomial (Fin 5) K)
    (hn : ∀ m ∈ f.support, Normal m) (hf : f ∈ ideal K) : f = 0 := by
  apply toricMap_eq_zero_of_normal K f
  · intro m hm
    have hnormal := hn m hm
    have he := (mem_envelope K f).mp (ideal_le_envelope K hf) m hm
    unfold Normal at hnormal
    unfold RadicalNormal
    omega
  · exact ideal_le_toric_ker K hf

theorem gen_homogeneous (i : Fin 4) :
    ∃ n, (gen K i).IsHomogeneous n := by
  refine ⟨(lead i).degree, (isHomogeneous_monomial (1 : K) rfl).sub ?_⟩
  have he : (tail i).degree = (lead i).degree := by
    simp only [Finsupp.degree_eq_sum, Finsupp.sum_fintype]
    fin_cases i <;> simp [lead, tail, Fin.sum_univ_succ]
  rw [← he]
  exact isHomogeneous_monomial (1 : K) rfl

theorem ideal_homogeneous : (ideal K).IsHomogeneous (homogeneousSubmodule (Fin 5) K) := by
  apply Ideal.homogeneous_span
  rintro f (rfl | rfl | rfl) <;> exact gen_homogeneous K _

theorem homogeneous_normal_remainder (n : ℕ) (f : MvPolynomial (Fin 5) K)
    (hf : f.IsHomogeneous n) :
    ∃ r : MvPolynomial (Fin 5) K, f - r ∈ ideal K ∧
      r.IsHomogeneous n ∧ ∀ m ∈ r.support, Normal m := by
  obtain ⟨r,hr,hn⟩ := normal_remainder K f
  refine ⟨homogeneousComponent n r, ?_, homogeneousComponent_isHomogeneous _ _, ?_⟩
  · have h := homogeneousComponent_mem_of_mem (ideal_homogeneous K) hr n
    simpa only [map_sub, homogeneousComponent_eq_self hf] using h
  · intro m hm
    rw [support_homogeneousComponent] at hm
    exact hn m (Finset.mem_filter.mp hm).1

theorem normal_finrank (n : ℕ) :
    Module.finrank K ((homogeneousSubmodule (Fin 5) K n).map
      (Ideal.Quotient.mkₐ K (ideal K)).toLinearMap) =
      Nat.card {m : Fin 5 →₀ ℕ // m.degree = n ∧ Normal m} := by
  classical
  let S : Set (Fin 5 →₀ ℕ) := {m | m.degree = n ∧ Normal m}
  let V := restrictSupport K S
  let W := (homogeneousSubmodule (Fin 5) K n).map (Ideal.Quotient.mkₐ K (ideal K)).toLinearMap
  have memV (f : MvPolynomial (Fin 5) K) : f ∈ V ↔ ∀ m ∈ f.support, m ∈ S := Iff.rfl
  have homog {f : MvPolynomial (Fin 5) K} (hf : f ∈ V) : f.IsHomogeneous n := by
    intro m hm
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using ((memV f).mp hf m (mem_support_iff.mpr hm)).1
  let q : V →ₗ[K] W :=
    { toFun := fun f => ⟨Ideal.Quotient.mk (ideal K) f.val, ⟨f.val, homog f.property, rfl⟩⟩
      map_add' := by intro f g; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro c f; apply Subtype.ext; exact (Ideal.Quotient.mkₐ K (ideal K)).toLinearMap.map_smul c f.val }
  have hqinj : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro f hf
    exact Subtype.ext (normal_ideal_eq_zero K f.val (fun m hm => ((memV f.val).mp f.property m hm).2)
      (Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hf)))
  have hqsurj : Function.Surjective q := by
    rintro ⟨z,f,hf,rfl⟩
    obtain ⟨r,hr,hh,hn⟩ := homogeneous_normal_remainder K n f hf
    refine ⟨⟨r, (memV r).mpr (fun m hm => ⟨?_, hn m hm⟩)⟩, ?_⟩
    · simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hh (mem_support_iff.mp hm)
    apply Subtype.ext
    apply Ideal.Quotient.eq.mpr
    simpa only [neg_sub] using (ideal K).neg_mem hr
  let e := LinearEquiv.ofBijective q ⟨hqinj,hqsurj⟩
  rw [← e.finrank_eq]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K S)

end PhilipponMultiplicity.InitialNormalForms
end


set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
open scoped BigOperators MonomialOrder
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.InitialNormalForms
variable (K : Type*) [Field K]

def radicalLead (i : Fin 4) : Fin 5 →₀ ℕ :=
  ![ex 1 0 2 0 0, ex 0 1 0 0 1, ex 1 0 0 0 2, ex 1 0 1 0 1] i

def radicalTail (i : Fin 4) : Fin 5 →₀ ℕ :=
  ![ex 0 2 0 1 0, ex 0 0 1 1 0, ex 0 0 0 3 0, ex 0 1 0 2 0] i

def radicalGen (i : Fin 4) : MvPolynomial (Fin 5) K :=
  if i = 3 then radicalGenerator K else gen K i

theorem radicalGen_eq (i : Fin 4) : radicalGen K i =
    monomial (radicalLead i) 1 - monomial (radicalTail i) 1 := by
  fin_cases i <;> simp [radicalGen, radicalGenerator, gen, lead, tail, radicalLead, radicalTail]

theorem radicalNormal_iff (m : Fin 5 →₀ ℕ) :
    RadicalNormal m ↔ ∀ i, ¬ radicalLead i ≤ m := by
  simp only [Fin.forall_fin_succ, radicalLead, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.forall_fin_zero, and_true, ex_le_iff]
  unfold RadicalNormal
  omega

theorem radicalTail_lt_lead (i : Fin 4) : radicalTail i ≺[MonomialOrder.lex] radicalLead i := by
  change toLex (radicalTail i) < toLex (radicalLead i)
  fin_cases i
  · exact ⟨0, by intro j hj; omega, by simp [radicalTail, radicalLead]⟩
  · refine ⟨1, ?_, by simp [radicalTail, radicalLead]⟩
    intro j hj
    have : j = 0 := by omega
    subst j
    simp [radicalTail, radicalLead]
  · exact ⟨0, by intro j hj; omega, by simp [radicalTail, radicalLead]⟩
  · exact ⟨0, by intro j hj; omega, by simp [radicalTail, radicalLead]⟩

theorem radicalGen_degree (i : Fin 4) :
    MonomialOrder.lex.degree (radicalGen K i) = radicalLead i := by
  classical
  rw [radicalGen_eq]
  rw [MonomialOrder.degree_sub_of_lt, MonomialOrder.degree_monomial]
  · simp
  · simpa [MonomialOrder.degree_monomial] using radicalTail_lt_lead i

theorem radicalGen_leadingCoeff (i : Fin 4) :
    MonomialOrder.lex.leadingCoeff (radicalGen K i) = 1 := by
  classical
  rw [radicalGen_eq]
  rw [MonomialOrder.leadingCoeff_sub_of_lt, MonomialOrder.leadingCoeff_monomial]
  · simpa [MonomialOrder.degree_monomial] using radicalTail_lt_lead i

theorem radicalGen_mem (i : Fin 4) : radicalGen K i ∈ radicalIdeal K := by
  have hle : ideal K ≤ radicalIdeal K := le_sup_left
  have hg : radicalGenerator K ∈ radicalIdeal K := by
    apply (le_sup_right : Ideal.span {radicalGenerator K} ≤ radicalIdeal K)
    exact Ideal.subset_span (Set.mem_singleton _)
  unfold radicalGen
  split_ifs
  · exact hg
  · exact hle (gen_mem K i)

theorem toricMap_radicalGen (i : Fin 4) : toricMap K (radicalGen K i) = 0 := by
  rw [radicalGen_eq, map_sub, toricMap_monomial, toricMap_monomial, sub_eq_zero]
  apply congrArg (fun e => monomial e (1 : K))
  ext j
  fin_cases i <;> fin_cases j <;> rfl

theorem radicalIdeal_le_toric_ker : radicalIdeal K ≤ RingHom.ker (toricMap K) := by
  apply sup_le (ideal_le_toric_ker K)
  rw [Ideal.span_singleton_le_iff_mem]
  change toricMap K (radicalGenerator K) = 0
  simpa [radicalGen] using toricMap_radicalGen K 3

theorem radical_normal_remainder (f : MvPolynomial (Fin 5) K) :
    ∃ r : MvPolynomial (Fin 5) K,
      f - r ∈ radicalIdeal K ∧ ∀ m ∈ r.support, RadicalNormal m := by
  obtain ⟨g,r,hf,_,hr⟩ := MonomialOrder.lex.div
    (b := radicalGen K) (fun i => by rw [radicalGen_leadingCoeff]; exact isUnit_one) f
  refine ⟨r, ?_, fun m hm => (radicalNormal_iff m).mpr ?_⟩
  · rw [hf, add_sub_cancel_right, Finsupp.linearCombination_apply]
    exact (radicalIdeal K).sum_mem
      (fun i _ => (radicalIdeal K).mul_mem_left _ (radicalGen_mem K i))
  · simpa only [radicalGen_degree] using hr m hm

theorem radicalIdeal_eq_toric_ker : radicalIdeal K = RingHom.ker (toricMap K) := by
  apply le_antisymm (radicalIdeal_le_toric_ker K)
  intro f hf
  obtain ⟨r,hr,hn⟩ := radical_normal_remainder K f
  have hker := radicalIdeal_le_toric_ker K hr
  change toricMap K (f-r) = 0 at hker
  change toricMap K f = 0 at hf
  rw [map_sub, hf, zero_sub, neg_eq_zero] at hker
  have hz := toricMap_eq_zero_of_normal K r hn hker
  simpa [hz] using hr

theorem radicalIdeal_prime : (radicalIdeal K).IsPrime := by
  rw [radicalIdeal_eq_toric_ker]
  exact RingHom.ker_isPrime _

theorem radicalGenerator_sq_mem : radicalGenerator K ^ 2 ∈ ideal K := by
  have heq : radicalGenerator K ^ 2 = gen K 0 * gen K 2 + X 0 * X 3 * gen K 1 ^ 2 := by
    simp [radicalGenerator, gen, lead, tail, monomial_ex]
    ring
  rw [heq]
  exact (ideal K).add_mem ((ideal K).mul_mem_left _ (gen_mem K 2))
    ((ideal K).mul_mem_left _ ((ideal K).pow_mem_of_mem (gen_mem K 1) 2 (by decide)))

theorem ideal_radical : (ideal K).radical = radicalIdeal K := by
  apply le_antisymm
  · exact (Ideal.radical_mono le_sup_left).trans_eq (radicalIdeal_prime K).radical
  · apply sup_le Ideal.le_radical
    rw [Ideal.span_singleton_le_iff_mem]
    exact ⟨2, radicalGenerator_sq_mem K⟩

theorem ideal_radical_prime : (ideal K).radical.IsPrime := by
  rw [ideal_radical]
  exact radicalIdeal_prime K

end PhilipponMultiplicity.InitialNormalForms
end


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.InitialNormalForms

def Triple (n : ℕ) := {t : ℕ × ℕ × ℕ // t.1 + t.2.1 + t.2.2 = n}

def tripleEquiv (n : ℕ) : Triple n ≃ (Finset.univ : Finset (Fin 3)).finsuppAntidiag n where
  toFun t := ⟨Finsupp.equivFunOnFinite.symm ![t.val.1,t.val.2.1,t.val.2.2], by
    rw [Finset.mem_finsuppAntidiag]
    constructor
    · simpa [Finsupp.sum_fintype, Fin.sum_univ_succ, add_assoc] using t.property
    · exact Finset.subset_univ _⟩
  invFun t := ⟨(t.val 0,t.val 1,t.val 2), by
    have h := (Finset.mem_finsuppAntidiag.mp t.property).1
    simpa [Finsupp.sum_fintype, Fin.sum_univ_succ, add_assoc] using h⟩
  left_inv t := by apply Subtype.ext; rfl
  right_inv t := by apply Subtype.ext; ext i; fin_cases i <;> rfl

instance triple_finite (n : ℕ) : Finite (Triple n) :=
  Finite.of_equiv _ (tripleEquiv n).symm

theorem triple_card (n : ℕ) : Nat.card (Triple n) = (n+2).choose 2 := by
  rw [Nat.card_congr (tripleEquiv n), Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  have h : 3 + n - 1 = n+2 := by omega
  rw [h, ← Nat.choose_symm (by omega : 2 ≤ n+2)]
  congr 1

def NormalExponents (n : ℕ) := {m : Fin 5 →₀ ℕ //
  m 0 + m 1 + m 2 + m 3 + m 4 = n ∧ Normal m}

def NormalFamilies (n : ℕ) :=
  Triple n ⊕ (Triple (n-1) ⊕ (Triple (n-1) ⊕ (Triple (n-2) ⊕ (Fin (n-1) ⊕ Unit))))

def encodeNormal (n : ℕ) (m : NormalExponents n) : NormalFamilies n := by
  have hm := m.property
  unfold Normal at hm
  by_cases he : m.val 0 = 0
  · by_cases ha : m.val 1 = 0
    · exact Sum.inl ⟨(m.val 2,m.val 3,m.val 4), by dsimp; omega⟩
    · exact Sum.inr (Sum.inl ⟨(m.val 1-1,m.val 2,m.val 3), by dsimp; omega⟩)
  · by_cases hd : m.val 4 = 0
    · by_cases hb : m.val 2 = 0
      · exact Sum.inr (Sum.inr (Sum.inl ⟨(m.val 0-1,m.val 1,m.val 3), by dsimp; omega⟩))
      · exact Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨(m.val 0-1,m.val 1,m.val 3), by dsimp; omega⟩)))
    · by_cases hb : m.val 2 = 0
      · exact Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨m.val 0-1, by omega⟩))))
      · exact Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))

def decodeNormal (n : ℕ) (hn : 3 ≤ n) : NormalFamilies n → NormalExponents n := by
  rintro (t | t | t | t | t | u)
  · exact ⟨ex 0 0 t.val.1 t.val.2.1 t.val.2.2, by
      have h := t.property
      dsimp [ex, Normal]
      omega⟩
  · exact ⟨ex 0 (t.val.1+1) t.val.2.1 t.val.2.2 0, by
      have h := t.property
      dsimp [ex, Normal]
      omega⟩
  · exact ⟨ex (t.val.1+1) t.val.2.1 0 t.val.2.2 0, by
      have h := t.property
      dsimp [ex, Normal]
      omega⟩
  · exact ⟨ex (t.val.1+1) t.val.2.1 1 t.val.2.2 0, by
      have h := t.property
      dsimp [ex, Normal]
      omega⟩
  · exact ⟨ex (t.val+1) 0 0 (n-2-t.val) 1, by
      have h := t.isLt
      dsimp [ex, Normal]
      omega⟩
  · exact ⟨ex (n-2) 0 1 0 1, by
      dsimp [ex, Normal]
      omega⟩

theorem decode_encode (n : ℕ) (hn : 3 ≤ n) (m : NormalExponents n) :
    decodeNormal n hn (encodeNormal n m) = m := by
  have hm := m.property
  unfold Normal at hm
  unfold encodeNormal
  split_ifs <;> apply Subtype.ext <;> ext i <;> fin_cases i <;>
    simp only [decodeNormal, ex_apply, Matrix.cons_val, Fin.reduceFinMk] <;> omega

theorem encode_decode (n : ℕ) (hn : 3 ≤ n) (s : NormalFamilies n) :
    encodeNormal n (decodeNormal n hn s) = s := by
  rcases s with t | t | t | t | t | u
  all_goals simp [encodeNormal, decodeNormal, ex_apply, Matrix.cons_val, Fin.reduceFinMk]
  have h : n-2 ≠ 0 := by omega
  simp [h]

def normalEquivFamilies (n : ℕ) (hn : 3 ≤ n) : NormalExponents n ≃ NormalFamilies n where
  toFun := encodeNormal n
  invFun := decodeNormal n hn
  left_inv := decode_encode n hn
  right_inv := encode_decode n hn

theorem normal_card (n : ℕ) (hn : 3 ≤ n) :
    Nat.card {m : Fin 5 →₀ ℕ // m.degree = n ∧ Normal m} = 2*n^2+3*n+1 := by
  have hdegree (m : Fin 5 →₀ ℕ) :
      m.degree = m 0 + m 1 + m 2 + m 3 + m 4 := by
    simp [Finsupp.degree_eq_sum, Finsupp.sum_fintype, Fin.sum_univ_succ, add_assoc]
  have htype : {m : Fin 5 →₀ ℕ // m.degree = n ∧ Normal m} ≃ NormalExponents n :=
    Equiv.subtypeEquivRight (fun m => by rw [hdegree])
  rw [Nat.card_congr htype, Nat.card_congr (normalEquivFamilies n hn)]
  change Nat.card (Triple n ⊕ (Triple (n-1) ⊕ (Triple (n-1) ⊕ (Triple (n-2) ⊕ (Fin (n-1) ⊕ Unit))))) = _
  simp only [Nat.card_sum, triple_card, Nat.card_fin, Nat.card_unique]
  have h1 : n-1+2 = n+1 := by omega
  have h2 : n-2+2 = n := by omega
  rw [h1,h2]
  have a := Nat.add_one_mul_choose_eq (n+1) 1
  have b := Nat.add_one_mul_choose_eq n 1
  have c := Nat.add_one_mul_choose_eq (n-1) 1
  simp only [Nat.choose_one_right] at a b c
  have he : n-1+1 = n := by omega
  rw [he] at c
  nlinarith

end PhilipponMultiplicity.InitialNormalForms
end


set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem componentSum_top_eq_of_equidimensional (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I)
    (hdim : ∀ q ∈ I.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      idealDimension M q = idealDimension M I)
    (d : M.FactorIndex → ℕ) :
    componentHilbertSum M I (⊤ : MaximalOpenLocus M) d = idealDegreeValue M I d := by
  classical
  rw [Hilbert.component_length_formula M I hI d]
  unfold componentHilbertSum Hilbert.componentSum topComponentLengthSum
  apply Finset.sum_congr rfl
  intro q _
  have ht : Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal ⊤ := by
    obtain ⟨m,hm,hle⟩ := Ideal.exists_le_maximal q.1.asIdeal q.1.isPrime.ne_top
    exact ⟨⟨m,hm⟩, by trivial, hle⟩
  by_cases hr : Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal
  · rw [if_pos ⟨hr,ht⟩, if_pos ⟨hr, hdim q.1.asIdeal q.2 hr⟩]
    exact Hilbert.primaryComponent_degreeValue_eq_localLength M I hI q.1 q.2 hr d
  · rw [if_neg (fun h => hr h.1), if_neg (fun h => hr h.1)]

theorem componentSum_top_eq_of_prime_radical (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hNontrivial : IsNontrivialIdeal M I)
    (hp : I.radical.IsPrime) (d : M.FactorIndex → ℕ) :
    componentHilbertSum M I (⊤ : MaximalOpenLocus M) d = idealDegreeValue M I d := by
  letI : I.radical.IsPrime := hp
  have hmin : I.minimalPrimes = {I.radical} := by
    rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self]
  obtain ⟨q,hq,_,hdim⟩ := Hilbert.exists_relevant_minimalPrime_dimension_eq M I hI hNontrivial
  apply componentSum_top_eq_of_equidimensional M I hI
  intro r hr _
  have hq' : q = I.radical := by simpa only [hmin, Set.mem_singleton_iff] using hq
  have hr' : r = I.radical := by simpa only [hmin, Set.mem_singleton_iff] using hr
  exact hr'.trans hq'.symm ▸ hdim

end PhilipponMultiplicity.SectionThreeSupport
end


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary
open SectionThree

def flattenVariables : ambient.Variable ≃ Fin 5 where
  toFun j := j.2
  invFun j := vindex j
  left_inv j := by
    obtain ⟨i,j⟩ := j
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  right_inv j := rfl

def flatten : ambient.CoordinateRing ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ :=
  renameEquiv ℂ flattenVariables

@[simp] theorem flatten_X (i : Fin 5) : flatten (X i) = MvPolynomial.X i := by
  exact rename_X _ _

theorem flatten_first : flatten firstGenerator = -InitialNormalForms.gen ℂ 0 := by
  simp [firstGenerator, InitialNormalForms.gen, InitialNormalForms.lead,
    InitialNormalForms.tail, InitialNormalForms.monomial_ex]
  ring

theorem flatten_second : flatten secondGenerator = InitialNormalForms.gen ℂ 1 := by
  simp [secondGenerator, InitialNormalForms.gen, InitialNormalForms.lead,
    InitialNormalForms.tail, InitialNormalForms.monomial_ex]

theorem flatten_third : flatten thirdGenerator = -InitialNormalForms.gen ℂ 2 := by
  simp [thirdGenerator, InitialNormalForms.gen, InitialNormalForms.lead,
    InitialNormalForms.tail, InitialNormalForms.monomial_ex]
  ring

theorem flatten_initialIdeal : initialIdeal.map flatten.toRingHom = InitialNormalForms.ideal ℂ := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, initialIdeal, Ideal.span_le]
    rintro f (rfl | rfl | rfl)
    · change flatten firstGenerator ∈ InitialNormalForms.ideal ℂ
      rw [flatten_first]
      exact (InitialNormalForms.ideal ℂ).neg_mem (InitialNormalForms.gen_mem ℂ 0)
    · change flatten secondGenerator ∈ InitialNormalForms.ideal ℂ
      rw [flatten_second]
      exact InitialNormalForms.gen_mem ℂ 1
    · change flatten thirdGenerator ∈ InitialNormalForms.ideal ℂ
      rw [flatten_third]
      exact (InitialNormalForms.ideal ℂ).neg_mem (InitialNormalForms.gen_mem ℂ 2)
  · rw [InitialNormalForms.ideal, Ideal.span_le]
    have hfirst : firstGenerator ∈ initialIdeal := Ideal.subset_span (by simp [initialIdeal])
    have hsecond : secondGenerator ∈ initialIdeal := Ideal.subset_span (by simp [initialIdeal])
    have hthird : thirdGenerator ∈ initialIdeal := Ideal.subset_span (by simp [initialIdeal])
    rintro f (rfl | rfl | rfl)
    · have h := Ideal.mem_map_of_mem flatten.toRingHom hfirst
      change flatten firstGenerator ∈ _ at h
      rw [flatten_first] at h
      exact (initialIdeal.map flatten.toRingHom).neg_mem_iff.mp h
    · have h := Ideal.mem_map_of_mem flatten.toRingHom hsecond
      change flatten secondGenerator ∈ _ at h
      rwa [flatten_second] at h
    · have h := Ideal.mem_map_of_mem flatten.toRingHom hthird
      change flatten thirdGenerator ∈ _ at h
      rw [flatten_third] at h
      exact (initialIdeal.map flatten.toRingHom).neg_mem_iff.mp h

theorem flatten_hilbertFunction (d : Fin 1 → ℕ) :
    Hilbert.hilbertFunction ℂ ambient.factorCount ambient.ambientDimension initialIdeal d =
      Module.finrank ℂ ((homogeneousSubmodule (Fin 5) ℂ (d 0)).map
        (Ideal.Quotient.mkₐ ℂ (InitialNormalForms.ideal ℂ)).toLinearMap) := by
  let e := Ideal.quotientEquivAlg initialIdeal (InitialNormalForms.ideal ℂ) flatten
    flatten_initialIdeal.symm
  let V := Hilbert.quotientPiece ℂ ambient.factorCount ambient.ambientDimension initialIdeal d
  let W := (homogeneousSubmodule (Fin 5) ℂ (d 0)).map
    (Ideal.Quotient.mkₐ ℂ (InitialNormalForms.ideal ℂ)).toLinearMap
  have hV (x : V) : e x.val ∈ W := by
    obtain ⟨f,hf,hfx⟩ := x.property
    rw [← hfx]
    refine ⟨flatten f, ?_, rfl⟩
    exact ((degreePiece_ordinary f d).mp hf).rename_isHomogeneous
  have hW (x : W) : e.symm x.val ∈ V := by
    obtain ⟨f,hf,hfx⟩ := x.property
    rw [← hfx]
    refine ⟨flatten.symm f, ?_, rfl⟩
    apply (degreePiece_ordinary _ d).mpr
    exact hf.rename_isHomogeneous
  let E : V ≃ₗ[ℂ] W :=
    { toFun := fun x => ⟨e x.val,hV x⟩
      invFun := fun x => ⟨e.symm x.val,hW x⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val)
      map_add' := fun x y => Subtype.ext (map_add e x.val y.val)
      map_smul' := fun c x => Subtype.ext (e.toLinearEquiv.map_smul c x.val) }
  exact E.finrank_eq

theorem initial_hilbertFunction (d : Fin 1 → ℕ) (hd : 3 ≤ d 0) :
    Hilbert.hilbertFunction ℂ ambient.factorCount ambient.ambientDimension initialIdeal d =
      2 * (d 0)^2 + 3 * d 0 + 1 := by
  rw [flatten_hilbertFunction, InitialNormalForms.normal_finrank, InitialNormalForms.normal_card _ hd]

theorem initial_hilbertPolynomial :
    Hilbert.hilbertPolynomial ℂ ambient.factorCount ambient.ambientDimension initialIdeal =
      expectedInitialHilbertPolynomial := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun _ => 3, fun d hd => ?_⟩
  rw [initial_hilbertFunction d (hd (0 : Fin 1))]
  simp [expectedInitialHilbertPolynomial]

theorem initial_radical_prime : initialIdeal.radical.IsPrime := by
  have h : initialIdeal = (InitialNormalForms.ideal ℂ).comap flatten.toRingHom := by
    rw [← flatten_initialIdeal]
    exact (Ideal.comap_map_of_bijective (I := initialIdeal) flatten.toRingHom flatten.bijective).symm
  rw [h, ← Ideal.comap_radical]
  exact (InitialNormalForms.ideal_radical_prime ℂ).comap flatten.toRingHom

theorem initial_component_sum :
    componentHilbertSum ambient initialIdeal (⊤ : MaximalOpenLocus ambient) (fun _ => 1) = 4 := by
  rw [componentSum_top_eq_of_prime_radical ambient initialIdeal initial_homogeneous
    initial_nontrivial initial_radical_prime]
  exact (initial_dimension_and_degree initial_hilbertPolynomial).2

end PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary
end

open PhilipponMultiplicity SectionThree SectionThreeSupport

theorem solution :
    let M := BezoutBoundary.ambient
    let I₀ := BezoutBoundary.initialIdeal
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension I₀ =
      BezoutBoundary.expectedInitialHilbertPolynomial ∧
    componentHilbertSum M I₀ (⊤ : MaximalOpenLocus M) (fun _ => 1) = 4 := by
  exact ⟨BezoutBoundary.initial_hilbertPolynomial, BezoutBoundary.initial_component_sum⟩
