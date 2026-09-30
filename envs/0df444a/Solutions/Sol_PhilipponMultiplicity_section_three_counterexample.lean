-- Prove2me | solution 1 for PhilipponMultiplicity.section_three_counterexample
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T10:35:45.335429+00:00
-- url     : https://prove2.me/submissions/d5f8b262-2d79-4482-973e-60dde5dca94b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Mathlib.RingTheory.MvPolynomial.Ideal
import Theorems.Thm_PhilipponMultiplicity_proposition_3_3
import Theorems.Thm_PhilipponMultiplicity_section_three_initial_hilbert_certificate
import Theorems.Thm_PhilipponMultiplicity_section_three_section_primary_certificate


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

/-- A monomial envelope separates AC² from every element of the printed ideal. -/
theorem witness_not_mem : nonradicalWitness ∉ initialIdeal := by
  classical
  let s : Set (ambient.Variable →₀ ℕ) :=
    {Finsupp.single (vindex 0) 1, Finsupp.single (vindex 2) 1,
     Finsupp.single (vindex 4) 1, Finsupp.single (vindex 1) 2,
     Finsupp.single (vindex 3) 3}
  let J : Ideal ambient.CoordinateRing := Ideal.span ((fun e => monomial e (1 : ℂ)) '' s)
  have hmono (j : Fin 5) (n : ℕ) (h : Finsupp.single (vindex j) n ∈ s) : X j ^ n ∈ J := by
    apply Ideal.subset_span
    refine ⟨_, h, ?_⟩
    exact X_pow_eq_monomial.symm
  have hE : X 0 ∈ J := by simpa using hmono 0 1 (by simp [s])
  have hB : X 2 ∈ J := by simpa using hmono 2 1 (by simp [s])
  have hD : X 4 ∈ J := by simpa using hmono 4 1 (by simp [s])
  have hA : X 1 ^ 2 ∈ J := hmono 1 2 (by simp [s])
  have hC : X 3 ^ 3 ∈ J := hmono 3 3 (by simp [s])
  have hIJ : initialIdeal ≤ J := by
    apply Ideal.span_le.mpr
    rintro f (rfl | rfl | rfl)
    · exact J.sub_mem (J.mul_mem_right _ hA) (J.mul_mem_left _ hE)
    · exact J.sub_mem (J.mul_mem_left _ hD) (J.mul_mem_right _ hB)
    · exact J.sub_mem hC (J.mul_mem_left _ hE)
  intro hg
  have hterm : X 1 * X 3 ^ 2 ∈ J := by
    have h := J.add_mem (hIJ hg) (J.mul_mem_left (X 2 * X 4) hE)
    simpa only [nonradicalWitness, sub_add_cancel] using h
  let a : ambient.Variable →₀ ℕ := Finsupp.single (vindex 1) 1 + Finsupp.single (vindex 3) 2
  have heq : X 1 * X 3 ^ 2 = monomial a (1 : ℂ) := by
    rw [show X 1 = monomial (Finsupp.single (vindex 1) 1) (1 : ℂ) from rfl,
      show X 3 ^ 2 = monomial (Finsupp.single (vindex 3) 2) (1 : ℂ) from X_pow_eq_monomial,
      monomial_mul, one_mul]
  rw [heq] at hterm
  obtain ⟨e, he, hle⟩ := mem_ideal_span_monomial_image.mp hterm a (by simp)
  rcases he with rfl | rfl | rfl | rfl | rfl
  · have := hle (vindex 0); norm_num [a, Finsupp.single_apply, vindex, Fin.ext_iff] at this
  · have := hle (vindex 2); norm_num [a, Finsupp.single_apply, vindex, Fin.ext_iff] at this
  · have := hle (vindex 4); norm_num [a, Finsupp.single_apply, vindex, Fin.ext_iff] at this
  · have := hle (vindex 1); norm_num [a, Finsupp.single_apply, vindex, Fin.ext_iff] at this
  · have := hle (vindex 3); norm_num [a, Finsupp.single_apply, vindex, Fin.ext_iff] at this

theorem witness_mem_radical : nonradicalWitness ∈ initialIdeal.radical :=
  ⟨2, witness_sq_mem_initialIdeal⟩

theorem initial_not_radical : initialIdeal.radical ≠ initialIdeal := by
  intro h
  exact witness_not_mem (h ▸ witness_mem_radical)

theorem initial_not_prime : ¬ initialIdeal.IsPrime := by
  intro h
  exact initial_not_radical h.isRadical.radical

/-- Eliminate C and A-D, without replacing the initial ideal by its radical. -/
theorem section_generators : sectionIdeal = reducedSectionGenerators := by
  have hA : X 1 ^ 2 ∈ sectionIdeal := by
    have hf : secondGenerator ∈ sectionIdeal :=
      Ideal.mem_sup_left (Ideal.subset_span (by simp [initialIdeal]))
    have hC : X 3 ∈ sectionIdeal := Ideal.mem_sup_right (Ideal.subset_span (by simp [firstEquation]))
    have hAD : X 1-X 4 ∈ sectionIdeal := Ideal.mem_sup_right (Ideal.subset_span (by simp [secondEquation]))
    convert sectionIdeal.add_mem (sectionIdeal.add_mem hf (sectionIdeal.mul_mem_left (X 2) hC))
      (sectionIdeal.mul_mem_left (X 1) hAD) using 1 <;> dsimp [secondGenerator] <;> ring
  have hB : X 2 ^ 2 * X 0 ∈ sectionIdeal := by
    have hf : firstGenerator ∈ sectionIdeal :=
      Ideal.mem_sup_left (Ideal.subset_span (by simp [initialIdeal]))
    convert sectionIdeal.sub_mem (sectionIdeal.mul_mem_right (X 3) hA) hf using 1 <;>
      dsimp [firstGenerator] <;> ring
  apply le_antisymm
  · have hA' : X 1 ^ 2 ∈ reducedSectionGenerators := Ideal.subset_span (by simp [reducedSectionGenerators])
    have hB' : X 2 ^ 2 * X 0 ∈ reducedSectionGenerators := Ideal.subset_span (by simp [reducedSectionGenerators])
    have hC : X 3 ∈ reducedSectionGenerators := Ideal.subset_span (by simp [reducedSectionGenerators])
    have hAD : X 1-X 4 ∈ reducedSectionGenerators := Ideal.subset_span (by simp [reducedSectionGenerators])
    have hD : X 4 ^ 2 ∈ reducedSectionGenerators := by
      convert reducedSectionGenerators.sub_mem hA'
        (reducedSectionGenerators.mul_mem_right (X 1+X 4) hAD) using 1 <;> ring
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro f (rfl | rfl | rfl)
      · exact reducedSectionGenerators.sub_mem (reducedSectionGenerators.mul_mem_right _ hA') hB'
      · change secondGenerator ∈ reducedSectionGenerators
        convert reducedSectionGenerators.sub_mem
          (reducedSectionGenerators.sub_mem hA' (reducedSectionGenerators.mul_mem_left (X 1) hAD))
          (reducedSectionGenerators.mul_mem_left (X 2) hC) using 1 <;> dsimp [secondGenerator] <;> ring
      · exact reducedSectionGenerators.sub_mem (Ideal.pow_mem_of_mem _ hC 3 (by decide))
          (reducedSectionGenerators.mul_mem_right _ hD)
    · apply Ideal.span_le.mpr
      rintro f (rfl | rfl)
      · exact hC
      · exact hAD
  · apply Ideal.span_le.mpr
    rintro f (rfl | rfl | rfl | rfl)
    · exact hA
    · exact hB
    · exact Ideal.mem_sup_right (Ideal.subset_span (by simp [firstEquation]))
    · exact Ideal.mem_sup_right (Ideal.subset_span (by simp [secondEquation]))

end PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary

end


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

theorem constant_dimension_and_degree (Q : Ideal ambient.CoordinateRing) (c : ℕ)
    (hp : Hilbert.hilbertPolynomial ℂ ambient.factorCount ambient.ambientDimension Q = c) :
    idealDimension ambient Q = 0 ∧ idealDegreeValue ambient Q (fun _ => 1) = c := by
  constructor
  · rw [idealDimension, hp]
    change (C (c : ℚ) : MvPolynomial (Fin 1) ℚ).totalDegree = 0
    exact totalDegree_C _
  · unfold idealDegreeValue Hilbert.degreeValue Hilbert.degreeForm
    rw [hp]
    change eval (fun _ : Fin 1 => (1 : ℚ))
      (((C (c : ℚ) : MvPolynomial (Fin 1) ℚ).totalDegree.factorial : ℚ) •
        homogeneousComponent (C (c : ℚ) : MvPolynomial (Fin 1) ℚ).totalDegree (C (c : ℚ))) = _
    rw [totalDegree_C, homogeneousComponent_of_mem (isHomogeneous_C (Fin 1) (c : ℚ))]
    simp only [ite_true, Nat.factorial_zero, Nat.cast_one, one_smul, eval_C]

/-- Proposition 3.3 would make the component sum decrease, contradicting 6 > 4. -/
theorem not_locally_cohenMacaulay
    (hbefore : componentHilbertSum ambient initialIdeal (⊤ : MaximalOpenLocus ambient) (fun _ => 1) = 4)
    (hafter : componentHilbertSum ambient sectionIdeal (⊤ : MaximalOpenLocus ambient) (fun _ => 1) = 6) :
    ¬ IsLocallyCohenMacaulayOn ambient initialIdeal (⊤ : MaximalOpenLocus ambient) := by
  let P : Fin 2 → ambient.CoordinateRing := ![firstEquation, secondEquation]
  have hP : ∀ j, IsMultihomogeneousOfDegreeAtMost ambient (P j) (fun _ => 1) := by
    intro j
    fin_cases j
    · exact ⟨_, fun _ => le_rfl, (ambient.degreePiece_iff _ _).mpr firstEquation_homogeneous⟩
    · exact ⟨_, fun _ => le_rfl, (ambient.degreePiece_iff _ _).mpr secondEquation_homogeneous⟩
  have hrange : Set.range P = {firstEquation, secondEquation} := by
    ext f
    simp [P, Set.mem_range, Fin.exists_fin_two, or_comm]
  intro hCM
  have h := (proposition_3_3 ℂ (Or.inl ⟨RingEquiv.refl ℂ, isometry_id⟩)
    ambient initialIdeal initial_homogeneous 2 P (fun _ => 1) hP).2 ⊤ hCM
  rw [hrange] at h
  change componentHilbertSum ambient sectionIdeal _ _ ≤ _ at h
  rw [hbefore, hafter] at h
  norm_num at h

end PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary

end


set_option autoImplicit false
namespace PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary
open SectionThree

/-- Assemble the counterexample from its two explicit computational certificates. -/
theorem assemble (hInitial :
    let M := BezoutBoundary.ambient
    let I₀ := BezoutBoundary.initialIdeal
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension I₀ =
      BezoutBoundary.expectedInitialHilbertPolynomial ∧
    componentHilbertSum M I₀ (⊤ : MaximalOpenLocus M) (fun _ => 1) = 4) (hSection :
    let M := BezoutBoundary.ambient
    let I := BezoutBoundary.sectionIdeal
    let Q₁ := BezoutBoundary.firstComponent
    let Q₂ := BezoutBoundary.secondComponent
    I = Q₁ ⊓ Q₂ ∧ Q₁.IsPrimary ∧ Q₂.IsPrimary ∧ Q₁.radical ≠ Q₂.radical ∧
    I.minimalPrimes = {Q₁.radical, Q₂.radical} ∧
    Hilbert.IsRelevant ℂ M.factorCount M.ambientDimension Q₁.radical ∧
    Hilbert.IsRelevant ℂ M.factorCount M.ambientDimension Q₂.radical ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension Q₁ = 4 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension Q₂ = 2 ∧
    componentHilbertSum M I (⊤ : MaximalOpenLocus M) (fun _ => 1) = 6) :
    let M := BezoutBoundary.ambient
    let I₀ := BezoutBoundary.initialIdeal
    let I := BezoutBoundary.sectionIdeal
    let Q₁ := BezoutBoundary.firstComponent
    let Q₂ := BezoutBoundary.secondComponent
    let g := BezoutBoundary.nonradicalWitness
    IsMultihomogeneousIdeal M I₀ ∧ IsNontrivialIdeal M I₀ ∧
    M.IsHomogeneous BezoutBoundary.firstEquation (fun _ => 1) ∧
    M.IsHomogeneous BezoutBoundary.secondEquation (fun _ => 1) ∧
    g ∉ I₀ ∧ g ^ 2 ∈ I₀ ∧ g ∈ I₀.radical ∧ I₀.radical ≠ I₀ ∧ ¬ I₀.IsPrime ∧
    idealDimension M I₀ = 2 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension I₀ =
      BezoutBoundary.expectedInitialHilbertPolynomial ∧
    idealDegreeValue M I₀ (fun _ => 1) = 4 ∧
    I = BezoutBoundary.reducedSectionGenerators ∧ I = Q₁ ⊓ Q₂ ∧
    Q₁.IsPrimary ∧ Q₂.IsPrimary ∧ Q₁.radical ≠ Q₂.radical ∧
    I.minimalPrimes = {Q₁.radical, Q₂.radical} ∧
    Hilbert.IsRelevant ℂ M.factorCount M.ambientDimension Q₁.radical ∧
    Hilbert.IsRelevant ℂ M.factorCount M.ambientDimension Q₂.radical ∧
    idealDimension M Q₁ = 0 ∧ idealDimension M Q₂ = 0 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension Q₁ = 4 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension Q₂ = 2 ∧
    idealDegreeValue M Q₁ (fun _ => 1) = 4 ∧
    idealDegreeValue M Q₂ (fun _ => 1) = 2 ∧
    componentHilbertSum M I (⊤ : MaximalOpenLocus M) (fun _ => 1) = 6 ∧
    componentHilbertSum M I₀ (⊤ : MaximalOpenLocus M) (fun _ => 1) = 4 ∧
    componentHilbertSum M I₀ (⊤ : MaximalOpenLocus M) (fun _ => 1) <
      componentHilbertSum M I (⊤ : MaximalOpenLocus M) (fun _ => 1) ∧
    ¬ IsLocallyCohenMacaulayOn M I₀ (⊤ : MaximalOpenLocus M) := by
  obtain ⟨hp0, hbefore⟩ := hInitial
  obtain ⟨hintersection, hq1, hq2, hdistinct, hmin, hr1, hr2, hp1, hp2, hafter⟩ := hSection
  obtain ⟨hd0, hv0⟩ := initial_dimension_and_degree hp0
  obtain ⟨hd1, hv1⟩ := constant_dimension_and_degree firstComponent 4 hp1
  obtain ⟨hd2, hv2⟩ := constant_dimension_and_degree secondComponent 2 hp2
  refine ⟨initial_homogeneous, initial_nontrivial,
    firstEquation_homogeneous, secondEquation_homogeneous,
    witness_not_mem, witness_sq_mem_initialIdeal, witness_mem_radical,
    initial_not_radical, initial_not_prime, hd0, hp0, hv0,
    section_generators, hintersection, hq1, hq2, hdistinct, hmin,
    hr1, hr2, hd1, hd2, hp1, hp2, hv1, hv2, hafter, hbefore, ?_,
    not_locally_cohenMacaulay hbefore hafter⟩
  rw [hbefore, hafter]
  norm_num

end PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary


open PhilipponMultiplicity SectionThree SectionThreeSupport

theorem solution :
    let M := BezoutBoundary.ambient
    let I₀ := BezoutBoundary.initialIdeal
    let I := BezoutBoundary.sectionIdeal
    let Q₁ := BezoutBoundary.firstComponent
    let Q₂ := BezoutBoundary.secondComponent
    let g := BezoutBoundary.nonradicalWitness
    IsMultihomogeneousIdeal M I₀ ∧ IsNontrivialIdeal M I₀ ∧
    M.IsHomogeneous BezoutBoundary.firstEquation (fun _ => 1) ∧
    M.IsHomogeneous BezoutBoundary.secondEquation (fun _ => 1) ∧
    g ∉ I₀ ∧ g ^ 2 ∈ I₀ ∧ g ∈ I₀.radical ∧ I₀.radical ≠ I₀ ∧ ¬ I₀.IsPrime ∧
    idealDimension M I₀ = 2 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension I₀ =
      BezoutBoundary.expectedInitialHilbertPolynomial ∧
    idealDegreeValue M I₀ (fun _ => 1) = 4 ∧
    I = BezoutBoundary.reducedSectionGenerators ∧ I = Q₁ ⊓ Q₂ ∧
    Q₁.IsPrimary ∧ Q₂.IsPrimary ∧ Q₁.radical ≠ Q₂.radical ∧
    I.minimalPrimes = {Q₁.radical, Q₂.radical} ∧
    Hilbert.IsRelevant ℂ M.factorCount M.ambientDimension Q₁.radical ∧
    Hilbert.IsRelevant ℂ M.factorCount M.ambientDimension Q₂.radical ∧
    idealDimension M Q₁ = 0 ∧ idealDimension M Q₂ = 0 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension Q₁ = 4 ∧
    Hilbert.hilbertPolynomial ℂ M.factorCount M.ambientDimension Q₂ = 2 ∧
    idealDegreeValue M Q₁ (fun _ => 1) = 4 ∧
    idealDegreeValue M Q₂ (fun _ => 1) = 2 ∧
    componentHilbertSum M I (⊤ : MaximalOpenLocus M) (fun _ => 1) = 6 ∧
    componentHilbertSum M I₀ (⊤ : MaximalOpenLocus M) (fun _ => 1) = 4 ∧
    componentHilbertSum M I₀ (⊤ : MaximalOpenLocus M) (fun _ => 1) <
      componentHilbertSum M I (⊤ : MaximalOpenLocus M) (fun _ => 1) ∧
    ¬ IsLocallyCohenMacaulayOn M I₀ (⊤ : MaximalOpenLocus M) := by
  exact BezoutBoundary.assemble
    section_three_initial_hilbert_certificate section_three_section_primary_certificate
