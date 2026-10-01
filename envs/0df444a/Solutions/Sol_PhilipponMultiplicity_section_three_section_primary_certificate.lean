-- Prove2me | solution 1 for PhilipponMultiplicity.section_three_section_primary_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T12:31:32.180986+00:00
-- url     : https://prove2.me/submissions/2aa75d95-dd8c-48b2-a140-72d91dd77d71

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Mathlib.RingTheory.MvPolynomial.Ideal
import Theorems.Thm_PhilipponMultiplicity_Support_coordinate_power_ideal_isPrimary


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary
open SectionThree

abbrev vindex (j : Fin 5) : ambient.Variable := ⟨(0 : Fin 1), j⟩

/-- Eliminate the two section equations. -/
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
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MonomialQuotientCount
variable {K σ Γ : Type*} [Field K] [AddCommMonoid Γ]

/-- Count a homogeneous quotient using its actual monomial ideal membership
criterion. The proof projects onto the complementary monomial support. -/
theorem finrank_piece (w : σ → Γ) (I : Ideal (MvPolynomial σ K))
    (U : Set (σ →₀ ℕ))
    (hI : ∀ f, f ∈ I ↔ ∀ m ∈ f.support, m ∈ U) (d : Γ) :
    Module.finrank K ((weightedHomogeneousSubmodule K w d).map
      (Ideal.Quotient.mkₐ K I).toLinearMap) =
      Nat.card {m : σ →₀ ℕ // Finsupp.weight w m = d ∧ m ∉ U} := by
  classical
  let S : Set (σ →₀ ℕ) := {m | Finsupp.weight w m = d ∧ m ∉ U}
  let V := restrictSupport K S
  let W := (weightedHomogeneousSubmodule K w d).map (Ideal.Quotient.mkₐ K I).toLinearMap
  have memV (f : MvPolynomial σ K) : f ∈ V ↔ ∀ m ∈ f.support, m ∈ S := Iff.rfl
  have homog {f : MvPolynomial σ K} (hf : f ∈ V) : f.IsWeightedHomogeneous w d := by
    intro m hm
    exact ((memV f).mp hf m (mem_support_iff.mpr hm)).1
  let q : V →ₗ[K] W :=
    { toFun := fun f => ⟨Ideal.Quotient.mk I f.val, ⟨f.val, homog f.property, rfl⟩⟩
      map_add' := by intro f g; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro c f; apply Subtype.ext; exact (Ideal.Quotient.mkₐ K I).toLinearMap.map_smul c f.val }
  have hqinj : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro f hf
    have hfI : f.val ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hf)
    have hf0 : f.val = 0 := by
      apply MvPolynomial.ext
      intro m
      rw [coeff_zero]
      by_contra hn
      have hm := mem_support_iff.mpr hn
      exact ((memV f.val).mp f.property m hm).2 ((hI f.val).mp hfI m hm)
    exact Subtype.ext hf0
  have hqsurj : Function.Surjective q := by
    rintro ⟨z, f, hf, rfl⟩
    let r : MvPolynomial σ K := AddMonoidAlgebra.ofCoeff
      (Finsupp.filter (fun m => m ∉ U) (AddMonoidAlgebra.coeff f))
    have hr : r ∈ V := by
      intro m hm
      have hm' : m ∈ f.support ∧ m ∉ U := Finset.mem_filter.mp hm
      exact ⟨hf (mem_support_iff.mp hm'.1), hm'.2⟩
    refine ⟨⟨r, hr⟩, Subtype.ext (Ideal.Quotient.eq.mpr ?_)⟩
    rw [hI]
    intro m hm
    by_contra hmU
    have hc := mem_support_iff.mp hm
    apply hc
    change coeff m r - coeff m f = 0
    simp [r, MvPolynomial.coeff, Finsupp.filter_apply, hmU]
  let e := LinearEquiv.ofBijective q ⟨hqinj, hqsurj⟩
  rw [← e.finrank_eq]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K S)

end PhilipponMultiplicity.MonomialQuotientCount
end


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary

/-- The involution replacing the equation `A-D` by a coordinate. -/
def shear : ambient.CoordinateRing →ₐ[ℂ] ambient.CoordinateRing :=
  aeval fun j => if j = vindex 4 then X 1 - X 4 else MvPolynomial.X j

@[simp] theorem shear_X (j : Fin 5) :
    shear (X j) = if j = 4 then X 1 - X 4 else X j := by
  simp [shear, X, vindex, Fin.ext_iff]

theorem shear_involutive : Function.Involutive shear := by
  have h : shear.comp shear = AlgHom.id ℂ ambient.CoordinateRing := by
    apply MvPolynomial.algHom_ext
    intro j
    obtain ⟨i,j⟩ := j
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change Fin 5 at j
    change shear (shear (X j)) = X j
    fin_cases j <;> norm_num [Fin.ext_iff] <;> rfl
  intro f
  exact DFunLike.congr_fun h f

def shearEquiv : ambient.CoordinateRing ≃ₐ[ℂ] ambient.CoordinateRing :=
  AlgEquiv.ofAlgHom shear shear
    (AlgHom.ext fun f => shear_involutive f)
    (AlgHom.ext fun f => shear_involutive f)

def monoSection : Ideal ambient.CoordinateRing :=
  Ideal.span {X 1 ^ 2, X 2 ^ 2 * X 0, X 3, X 4}

def monoFirst : Ideal ambient.CoordinateRing :=
  Ideal.span {X 1 ^ 2, X 2 ^ 2, X 3, X 4}

def monoSecond : Ideal ambient.CoordinateRing :=
  Ideal.span {X 0, X 1 ^ 2, X 3, X 4}

theorem shear_section : sectionIdeal.map shear.toRingHom = monoSection := by
  rw [section_generators]
  simp [reducedSectionGenerators, monoSection, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton]

theorem shear_first : firstComponent.map shear.toRingHom = monoFirst := by
  simp [firstComponent, monoFirst, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]

theorem shear_second : secondComponent.map shear.toRingHom = monoSecond := by
  simp [secondComponent, monoSecond, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]

def sectionExponents : Set (ambient.Variable →₀ ℕ) :=
  {Finsupp.single (vindex 1) 2,
   Finsupp.single (vindex 2) 2 + Finsupp.single (vindex 0) 1,
   Finsupp.single (vindex 3) 1, Finsupp.single (vindex 4) 1}

def firstExponents : Set (ambient.Variable →₀ ℕ) :=
  {Finsupp.single (vindex 1) 2, Finsupp.single (vindex 2) 2,
   Finsupp.single (vindex 3) 1, Finsupp.single (vindex 4) 1}

def secondExponents : Set (ambient.Variable →₀ ℕ) :=
  {Finsupp.single (vindex 0) 1, Finsupp.single (vindex 1) 2,
   Finsupp.single (vindex 3) 1, Finsupp.single (vindex 4) 1}

theorem monoSection_span : monoSection =
    Ideal.span ((fun e => monomial e (1 : ℂ)) '' sectionExponents) := by
  have hm : monomial (Finsupp.single (vindex 2) 2 + Finsupp.single (vindex 0) 1) (1 : ℂ) =
      X 2 ^ 2 * X 0 := by
    rw [show (1 : ℂ) = 1 * 1 from (one_mul 1).symm, ← monomial_mul]
    rw [← X_pow_eq_monomial]
    rfl
  simp [monoSection, sectionExponents, Set.image_insert_eq, Set.image_singleton,
    hm, X, vindex, ← X_pow_eq_monomial]

theorem monoFirst_span : monoFirst =
    Ideal.span ((fun e => monomial e (1 : ℂ)) '' firstExponents) := by
  simp [monoFirst, firstExponents, Set.image_insert_eq, Set.image_singleton,
    X, ← X_pow_eq_monomial]

theorem monoSecond_span : monoSecond =
    Ideal.span ((fun e => monomial e (1 : ℂ)) '' secondExponents) := by
  simp [monoSecond, secondExponents, Set.image_insert_eq, Set.image_singleton,
    X, ← X_pow_eq_monomial]

theorem mixed_exponent_le (e : ambient.Variable →₀ ℕ) :
    Finsupp.single (vindex 2) 2 + Finsupp.single (vindex 0) 1 ≤ e ↔
      2 ≤ e (vindex 2) ∧ 1 ≤ e (vindex 0) := by
  constructor
  · intro h
    exact ⟨by simpa [vindex, Fin.ext_iff] using h (vindex 2),
      by simpa [vindex, Fin.ext_iff] using h (vindex 0)⟩
  · rintro ⟨hB,hE⟩ j
    by_cases h2 : j = vindex 2
    · subst j; simpa [vindex, Fin.ext_iff] using hB
    by_cases h0 : j = vindex 0
    · subst j; simpa [vindex, Fin.ext_iff] using hE
    simp [Finsupp.single_apply, h2, h0]

theorem mem_monoSection (f : ambient.CoordinateRing) : f ∈ monoSection ↔
    ∀ e ∈ f.support, 2 ≤ e (vindex 1) ∨
      (2 ≤ e (vindex 2) ∧ 1 ≤ e (vindex 0)) ∨
      1 ≤ e (vindex 3) ∨ 1 ≤ e (vindex 4) := by
  rw [monoSection_span, mem_ideal_span_monomial_image]
  simp [sectionExponents, mixed_exponent_le]

theorem mem_monoFirst (f : ambient.CoordinateRing) : f ∈ monoFirst ↔
    ∀ e ∈ f.support, 2 ≤ e (vindex 1) ∨ 2 ≤ e (vindex 2) ∨
      1 ≤ e (vindex 3) ∨ 1 ≤ e (vindex 4) := by
  rw [monoFirst_span, mem_ideal_span_monomial_image]
  simp [firstExponents]

theorem mem_monoSecond (f : ambient.CoordinateRing) : f ∈ monoSecond ↔
    ∀ e ∈ f.support, 1 ≤ e (vindex 0) ∨ 2 ≤ e (vindex 1) ∨
      1 ≤ e (vindex 3) ∨ 1 ≤ e (vindex 4) := by
  rw [monoSecond_span, mem_ideal_span_monomial_image]
  simp [secondExponents]

theorem monomial_intersection : monoSection = monoFirst ⊓ monoSecond := by
  ext f
  simp only [Submodule.mem_inf, mem_monoSection, mem_monoFirst, mem_monoSecond]
  constructor
  · intro h
    exact ⟨fun e he => by have := h e he; tauto,
      fun e he => by have := h e he; tauto⟩
  · rintro ⟨h1,h2⟩ e he
    have := h1 e he
    have := h2 e he
    tauto

theorem section_intersection : sectionIdeal = firstComponent ⊓ secondComponent := by
  have hI := Ideal.comap_map_of_bijective (I := sectionIdeal) shear.toRingHom shear_involutive.bijective
  have h1 := Ideal.comap_map_of_bijective (I := firstComponent) shear.toRingHom shear_involutive.bijective
  have h2 := Ideal.comap_map_of_bijective (I := secondComponent) shear.toRingHom shear_involutive.bijective
  rw [shear_section] at hI
  rw [shear_first] at h1
  rw [shear_second] at h2
  rw [← hI, ← h1, ← h2, monomial_intersection, Ideal.comap_inf]

def coordinateProjection (k : Fin 5) : ambient.CoordinateRing →ₐ[ℂ] ambient.CoordinateRing :=
  aeval fun j => if j = vindex k then X k else 0

@[simp] theorem coordinateProjection_X (k j : Fin 5) :
    coordinateProjection k (X j) = if j = k then X k else 0 := by
  simp [coordinateProjection, X, vindex, Fin.ext_iff]

def coordinatePrime (k : Fin 5) : Ideal ambient.CoordinateRing :=
  RingHom.ker (coordinateProjection k).toRingHom

theorem coordinatePrime_prime (k : Fin 5) : (coordinatePrime k).IsPrime :=
  RingHom.ker_isPrime _

theorem coordinatePrime_span (k : Fin 5) : coordinatePrime k =
    Ideal.span (MvPolynomial.X '' {j : ambient.Variable | j ≠ vindex k}) := by
  classical
  let J : Ideal ambient.CoordinateRing :=
    Ideal.span (MvPolynomial.X '' {j : ambient.Variable | j ≠ vindex k})
  have hsub (f : ambient.CoordinateRing) : f - coordinateProjection k f ∈ J := by
    induction f using MvPolynomial.induction_on with
    | C a => simp [coordinateProjection, J]
    | add p q hp hq =>
      convert J.add_mem hp hq using 1 <;> simp only [map_add] <;> ring
    | mul_X p j hp =>
      by_cases hj : j = vindex k
      · subst j
        convert J.mul_mem_right (X k) hp using 1 <;>
          simp only [map_mul, show MvPolynomial.X (vindex k) = X k from rfl,
            coordinateProjection_X, ite_true] <;> ring
      · have hX : MvPolynomial.X j ∈ J := Ideal.subset_span ⟨j, hj, rfl⟩
        simpa [coordinateProjection, hj] using J.mul_mem_left p hX
  apply le_antisymm
  · intro f hf
    have hf0 : coordinateProjection k f = 0 := hf
    simpa [hf0] using hsub f
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    change j ≠ vindex k at hj
    simp [coordinatePrime, RingHom.mem_ker, coordinateProjection, hj]

theorem monoFirst_radical : monoFirst.radical = coordinatePrime 0 := by
  have hle : monoFirst ≤ coordinatePrime 0 := by
    apply Ideal.span_le.mpr
    rintro f (rfl | rfl | rfl | rfl) <;>
      simp [coordinatePrime, RingHom.mem_ker, Fin.ext_iff]
  apply le_antisymm ((coordinatePrime_prime 0).radical_le_iff.mpr hle)
  rw [coordinatePrime_span, Ideal.span_le]
  rintro _ ⟨⟨i,j⟩,hj,rfl⟩
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change Fin 5 at j
  change X j ∈ monoFirst.radical
  fin_cases j
  · exact (hj rfl).elim
  · exact ⟨2, Ideal.subset_span (by simp [monoFirst, X, vindex])⟩
  · exact ⟨2, Ideal.subset_span (by simp [monoFirst, X, vindex])⟩
  · exact Ideal.le_radical (Ideal.subset_span (by simp [monoFirst, X, vindex]))
  · exact Ideal.le_radical (Ideal.subset_span (by simp [monoFirst, X, vindex]))

theorem monoSecond_radical : monoSecond.radical = coordinatePrime 2 := by
  have hle : monoSecond ≤ coordinatePrime 2 := by
    apply Ideal.span_le.mpr
    rintro f (rfl | rfl | rfl | rfl) <;>
      simp [coordinatePrime, RingHom.mem_ker, Fin.ext_iff]
  apply le_antisymm ((coordinatePrime_prime 2).radical_le_iff.mpr hle)
  rw [coordinatePrime_span, Ideal.span_le]
  rintro _ ⟨⟨i,j⟩,hj,rfl⟩
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change Fin 5 at j
  change X j ∈ monoSecond.radical
  fin_cases j
  · exact Ideal.le_radical (Ideal.subset_span (by simp [monoSecond, X, vindex]))
  · exact ⟨2, Ideal.subset_span (by simp [monoSecond, X, vindex])⟩
  · exact (hj rfl).elim
  · exact Ideal.le_radical (Ideal.subset_span (by simp [monoSecond, X, vindex]))
  · exact Ideal.le_radical (Ideal.subset_span (by simp [monoSecond, X, vindex]))

theorem first_radical : firstComponent.radical = (coordinatePrime 0).comap shear.toRingHom := by
  rw [← monoFirst_radical, Ideal.comap_radical, ← shear_first,
    Ideal.comap_map_of_bijective shear.toRingHom shear_involutive.bijective]

theorem second_radical : secondComponent.radical = (coordinatePrime 2).comap shear.toRingHom := by
  rw [← monoSecond_radical, Ideal.comap_radical, ← shear_second,
    Ideal.comap_map_of_bijective shear.toRingHom shear_involutive.bijective]

theorem first_radical_prime : firstComponent.radical.IsPrime := by
  rw [first_radical]
  exact (coordinatePrime_prime 0).comap _

theorem second_radical_prime : secondComponent.radical.IsPrime := by
  rw [second_radical]
  exact (coordinatePrime_prime 2).comap _

theorem B_mem_first_radical : X 2 ∈ firstComponent.radical := by
  simp [first_radical, Ideal.mem_comap, coordinatePrime, RingHom.mem_ker, Fin.ext_iff]

theorem B_not_mem_second_radical : X 2 ∉ secondComponent.radical := by
  simp only [second_radical, Ideal.mem_comap, coordinatePrime, RingHom.mem_ker,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, shear_X]
  norm_num [Fin.ext_iff]
  exact MvPolynomial.X_ne_zero (vindex 2)

theorem E_mem_second_radical : X 0 ∈ secondComponent.radical := by
  simp [second_radical, Ideal.mem_comap, coordinatePrime, RingHom.mem_ker, Fin.ext_iff]

theorem E_not_mem_first_radical : X 0 ∉ firstComponent.radical := by
  simp only [first_radical, Ideal.mem_comap, coordinatePrime, RingHom.mem_ker,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, shear_X]
  norm_num [Fin.ext_iff]
  exact MvPolynomial.X_ne_zero (vindex 0)

theorem radicals_incomparable :
    ¬ firstComponent.radical ≤ secondComponent.radical ∧
    ¬ secondComponent.radical ≤ firstComponent.radical :=
  ⟨fun h => B_not_mem_second_radical (h B_mem_first_radical),
   fun h => E_not_mem_first_radical (h E_mem_second_radical)⟩

theorem radicals_distinct : firstComponent.radical ≠ secondComponent.radical :=
  fun h => radicals_incomparable.1 h.le

theorem coordinate_mem_irrelevant (k : Fin 5) : X k ∈
    Hilbert.irrelevantIdeal ℂ ambient.factorCount ambient.ambientDimension := by
  rw [Hilbert.irrelevantIdeal, Ideal.mem_iInf]
  intro i
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact Ideal.subset_span ⟨k, rfl⟩

theorem first_relevant : Hilbert.IsRelevant ℂ ambient.factorCount ambient.ambientDimension
    firstComponent.radical := fun h => E_not_mem_first_radical (h (coordinate_mem_irrelevant 0))

theorem second_relevant : Hilbert.IsRelevant ℂ ambient.factorCount ambient.ambientDimension
    secondComponent.radical := fun h => B_not_mem_second_radical (h (coordinate_mem_irrelevant 2))

theorem section_minimalPrimes :
    sectionIdeal.minimalPrimes = {firstComponent.radical, secondComponent.radical} := by
  have hrad : sectionIdeal.radical = firstComponent.radical ⊓ secondComponent.radical := by
    rw [section_intersection, Ideal.radical_inf]
  rw [← Ideal.radical_minimalPrimes (I := sectionIdeal), hrad]
  ext P
  constructor
  · intro hP
    rcases hP.isPrime.inf_le.mp hP.le with h1 | h2
    · exact Or.inl ((hP.2 ⟨first_radical_prime, inf_le_left⟩ h1).antisymm h1)
    · exact Or.inr ((hP.2 ⟨second_radical_prime, inf_le_right⟩ h2).antisymm h2)
  · rintro (rfl | rfl)
    · refine ⟨⟨first_radical_prime, inf_le_left⟩, ?_⟩
      intro P hP hle
      rcases hP.1.inf_le.mp hP.2 with h1 | h2
      · exact h1
      · exact (radicals_incomparable.2 (h2.trans hle)).elim
    · refine ⟨⟨second_radical_prime, inf_le_right⟩, ?_⟩
      intro P hP hle
      rcases hP.1.inf_le.mp hP.2 with h1 | h2
      · exact (radicals_incomparable.1 (h1.trans hle)).elim
      · exact h2

end PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary

end


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary

def exponent (e a b c d : ℕ) : ambient.Variable →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => ![e,a,b,c,d] j.2)

@[simp] theorem exponent_apply (e a b c d : ℕ) (j : Fin 5) :
    exponent e a b c d (vindex j) = ![e,a,b,c,d] j := rfl

theorem exponent_ext {m n : ambient.Variable →₀ ℕ}
    (h : ∀ j : Fin 5, m (vindex j) = n (vindex j)) : m = n := by
  ext ⟨i,j⟩
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact h j

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

theorem shear_homogeneous (f : ambient.CoordinateRing) (d : Fin 1 → ℕ)
    (hf : f ∈ Hilbert.degreePiece ℂ ambient.factorCount ambient.ambientDimension d) :
    shear f ∈ Hilbert.degreePiece ℂ ambient.factorCount ambient.ambientDimension d := by
  rw [degreePiece_ordinary] at hf ⊢
  have hvars (j : ambient.Variable) :
      (if j = vindex 4 then X 1 - X 4 else MvPolynomial.X j).IsHomogeneous 1 := by
    split_ifs
    · exact (MvPolynomial.isHomogeneous_X ℂ (vindex 1)).sub (MvPolynomial.isHomogeneous_X ℂ (vindex 4))
    · exact MvPolynomial.isHomogeneous_X ℂ j
  simpa [shear, one_mul] using hf.aeval _ hvars

theorem shear_hilbertFunction (I J : Ideal ambient.CoordinateRing)
    (h : I.map shear.toRingHom = J) (d : Fin 1 → ℕ) :
    Hilbert.hilbertFunction ℂ ambient.factorCount ambient.ambientDimension I d =
      Hilbert.hilbertFunction ℂ ambient.factorCount ambient.ambientDimension J d := by
  let e := Ideal.quotientEquivAlg I J shearEquiv h.symm
  let V := Hilbert.quotientPiece ℂ ambient.factorCount ambient.ambientDimension I d
  let W := Hilbert.quotientPiece ℂ ambient.factorCount ambient.ambientDimension J d
  have he (f : ambient.CoordinateRing) : e (Ideal.Quotient.mk I f) = Ideal.Quotient.mk J (shear f) := rfl
  have he' (f : ambient.CoordinateRing) : e.symm (Ideal.Quotient.mk J f) = Ideal.Quotient.mk I (shear f) := rfl
  have hV (x : V) : e x.val ∈ W := by
    obtain ⟨f,hf,hfx⟩ := x.property
    rw [← hfx]
    change e (Ideal.Quotient.mk I f) ∈ W
    rw [he]
    exact ⟨shear f, shear_homogeneous f d hf, rfl⟩
  have hW (x : W) : e.symm x.val ∈ V := by
    obtain ⟨f,hf,hfx⟩ := x.property
    rw [← hfx]
    change e.symm (Ideal.Quotient.mk J f) ∈ V
    rw [he']
    exact ⟨shear f, shear_homogeneous f d hf, rfl⟩
  let E : V ≃ₗ[ℂ] W :=
    { toFun := fun x => ⟨e x.val, hV x⟩
      invFun := fun x => ⟨e.symm x.val, hW x⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val)
      map_add' := fun x y => Subtype.ext (map_add e x.val y.val)
      map_smul' := fun c x => Subtype.ext (e.toLinearEquiv.map_smul c x.val) }
  exact E.finrank_eq

def StandardFirst (n : ℕ) := {m : ambient.Variable →₀ ℕ //
    m (vindex 0) + m (vindex 1) + m (vindex 2) + m (vindex 3) + m (vindex 4) = n ∧
    m (vindex 1) < 2 ∧ m (vindex 2) < 2 ∧ m (vindex 3) = 0 ∧ m (vindex 4) = 0}

def firstStandardEquiv (n : ℕ) (hn : 2 ≤ n) : StandardFirst n ≃ Fin 2 × Fin 2 where
  toFun m := (⟨m.val (vindex 1),m.property.2.1⟩, ⟨m.val (vindex 2),m.property.2.2.1⟩)
  invFun ab := ⟨exponent (n-ab.1.val-ab.2.val) ab.1.val ab.2.val 0 0, by
    have ha := ab.1.isLt
    have hb := ab.2.isLt
    simp only [exponent_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val, Fin.reduceFinMk, add_zero]
    exact ⟨by omega, ha, hb, trivial, trivial⟩⟩
  left_inv m := by
    apply Subtype.ext
    apply exponent_ext
    intro j
    have hm := m.property
    fin_cases j <;> simp [Fin.ext_iff] <;> omega
  right_inv ab := by
    apply Prod.ext <;> apply Fin.ext <;> rfl

def StandardSecond (n : ℕ) := {m : ambient.Variable →₀ ℕ //
    m (vindex 0) + m (vindex 1) + m (vindex 2) + m (vindex 3) + m (vindex 4) = n ∧
    m (vindex 0) = 0 ∧ m (vindex 1) < 2 ∧ m (vindex 3) = 0 ∧ m (vindex 4) = 0}

def secondStandardEquiv (n : ℕ) (hn : 1 ≤ n) : StandardSecond n ≃ Fin 2 where
  toFun m := ⟨m.val (vindex 1), m.property.2.2.1⟩
  invFun a := ⟨exponent 0 a.val (n-a.val) 0 0, by
    have ha := a.isLt
    simp only [exponent_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val, Fin.reduceFinMk, add_zero, zero_add]
    exact ⟨by omega, trivial, ha, trivial, trivial⟩⟩
  left_inv m := by
    apply Subtype.ext
    apply exponent_ext
    intro j
    have hm := m.property
    fin_cases j <;> simp [Fin.ext_iff] <;> omega
  right_inv a := by apply Fin.ext; rfl

theorem monoFirst_hilbertFunction (d : Fin 1 → ℕ) (hd : 2 ≤ d 0) :
    Hilbert.hilbertFunction ℂ ambient.factorCount ambient.ambientDimension monoFirst d = 4 := by
  classical
  rw [Hilbert.hilbertFunction, Hilbert.quotientPiece, Hilbert.degreePiece,
    MonomialQuotientCount.finrank_piece _ _
      {m | 2 ≤ m (vindex 1) ∨ 2 ≤ m (vindex 2) ∨ 1 ≤ m (vindex 3) ∨ 1 ≤ m (vindex 4)}
      mem_monoFirst]
  calc
    _ = Nat.card (StandardFirst (d 0)) := Nat.card_congr (Equiv.subtypeEquivRight (by
      intro m
      simp only [weight_eq_iff, Set.mem_setOf_eq, not_or, not_le]
      constructor <;> intro h <;> exact ⟨h.1, by omega, by omega, by omega, by omega⟩))
    _ = Nat.card (Fin 2 × Fin 2) := Nat.card_congr (firstStandardEquiv (d 0) hd)
    _ = 4 := by simp [Nat.card_prod]

theorem monoSecond_hilbertFunction (d : Fin 1 → ℕ) (hd : 1 ≤ d 0) :
    Hilbert.hilbertFunction ℂ ambient.factorCount ambient.ambientDimension monoSecond d = 2 := by
  classical
  rw [Hilbert.hilbertFunction, Hilbert.quotientPiece, Hilbert.degreePiece,
    MonomialQuotientCount.finrank_piece _ _
      {m | 1 ≤ m (vindex 0) ∨ 2 ≤ m (vindex 1) ∨ 1 ≤ m (vindex 3) ∨ 1 ≤ m (vindex 4)}
      mem_monoSecond]
  calc
    _ = Nat.card (StandardSecond (d 0)) := Nat.card_congr (Equiv.subtypeEquivRight (by
      intro m
      simp only [weight_eq_iff, Set.mem_setOf_eq, not_or, not_le]
      constructor <;> intro h <;> exact ⟨h.1, by omega, by omega, by omega, by omega⟩))
    _ = Nat.card (Fin 2) := Nat.card_congr (secondStandardEquiv (d 0) hd)
    _ = 2 := by simp

theorem first_hilbertPolynomial :
    Hilbert.hilbertPolynomial ℂ ambient.factorCount ambient.ambientDimension firstComponent = 4 := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun _ => 2, fun d hd => ?_⟩
  rw [shear_hilbertFunction _ _ shear_first, monoFirst_hilbertFunction d (hd (0 : Fin 1))]
  simp

theorem second_hilbertPolynomial :
    Hilbert.hilbertPolynomial ℂ ambient.factorCount ambient.ambientDimension secondComponent = 2 := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun _ => 1, fun d hd => ?_⟩
  rw [shear_hilbertFunction _ _ shear_second, monoSecond_hilbertFunction d (hd (0 : Fin 1))]
  simp

end PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary

end


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary

theorem primary_from_coordinate_powers
    (hcoordinate : ∀ (S : Set ambient.Variable) (n : ambient.Variable → ℕ),
      (∀ i ∈ S, 0 < n i) →
      (Ideal.span ((fun i => (MvPolynomial.X i : ambient.CoordinateRing) ^ n i) '' S)).IsPrimary) :
    firstComponent.IsPrimary ∧ secondComponent.IsPrimary := by
  have h1 : monoFirst.IsPrimary := by
    have h := hcoordinate {vindex 1, vindex 2, vindex 3, vindex 4}
      (fun j => if j = vindex 1 ∨ j = vindex 2 then 2 else 1)
      (by intro i hi; split_ifs <;> decide)
    simpa [monoFirst, X, vindex, Set.image_insert_eq, Set.image_singleton, Fin.ext_iff] using h
  have h2 : monoSecond.IsPrimary := by
    have h := hcoordinate {vindex 0, vindex 1, vindex 3, vindex 4}
      (fun j => if j = vindex 1 then 2 else 1)
      (by intro i hi; split_ifs <;> decide)
    simpa [monoSecond, X, vindex, Set.image_insert_eq, Set.image_singleton, Fin.ext_iff] using h
  constructor
  · have h := h1.comap shear.toRingHom
    rwa [← shear_first, Ideal.comap_map_of_bijective shear.toRingHom shear_involutive.bijective] at h
  · have h := h2.comap shear.toRingHom
    rwa [← shear_second, Ideal.comap_map_of_bijective shear.toRingHom shear_involutive.bijective] at h

end PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary

end


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary
open SectionThree

/-- Contracting a primary ideal from its radical's localization recovers it;
the other component becomes the unit ideal. -/
theorem canonical_pair_component {R : Type*} [CommRing R]
    (Q T : Ideal R) (hQ : Q.IsPrimary)
    (q : PrimeSpectrum R) (hq : q.asIdeal = Q.radical)
    (hT : ¬ T ≤ q.asIdeal) :
    (((Q ⊓ T).map (algebraMap R (Localization.AtPrime q.asIdeal))).comap
      (algebraMap R (Localization.AtPrime q.asIdeal))) = Q := by
  let A := Localization.AtPrime q.asIdeal
  have hmap : (Q ⊓ T).map (algebraMap R A) =
      Q.map (algebraMap R A) ⊓ T.map (algebraMap R A) := by
    exact map_inf (IsLocalization.mapFrameHom q.asIdeal.primeCompl A) Q T
  rw [hmap, IsLocalization.AtPrime.map_eq_top_of_not_le (S := A) hT, inf_top_eq]
  apply IsLocalization.under_map_of_isPrimary_disjoint q.asIdeal.primeCompl A hQ
  apply Set.disjoint_left.mpr
  intro x hx hxQ
  exact hx (hq.symm ▸ Ideal.le_radical hxQ)

def firstPoint : PrimeSpectrum ambient.CoordinateRing := ⟨firstComponent.radical,first_radical_prime⟩
def secondPoint : PrimeSpectrum ambient.CoordinateRing := ⟨secondComponent.radical,second_radical_prime⟩

theorem first_canonical (h1 : firstComponent.IsPrimary) :
    Hilbert.primaryComponent ℂ ambient.factorCount ambient.ambientDimension sectionIdeal firstPoint =
      firstComponent := by
  rw [Hilbert.primaryComponent, section_intersection]
  apply canonical_pair_component _ _ h1 _ rfl
  intro h
  exact radicals_incomparable.2 (first_radical_prime.radical_le_iff.mpr h)

theorem second_canonical (h2 : secondComponent.IsPrimary) :
    Hilbert.primaryComponent ℂ ambient.factorCount ambient.ambientDimension sectionIdeal secondPoint =
      secondComponent := by
  rw [Hilbert.primaryComponent, section_intersection, inf_comm]
  apply canonical_pair_component _ _ h2 _ rfl
  intro h
  exact radicals_incomparable.1 (second_radical_prime.radical_le_iff.mpr h)

theorem prime_meets_top (q : PrimeSpectrum ambient.CoordinateRing) :
    Hilbert.MeetsOpen ℂ ambient.factorCount ambient.ambientDimension q.asIdeal ⊤ := by
  obtain ⟨m,hm,hle⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  exact ⟨⟨m,hm⟩, by trivial, hle⟩

theorem constant_degree (Q : Ideal ambient.CoordinateRing) (c : ℕ)
    (hp : Hilbert.hilbertPolynomial ℂ ambient.factorCount ambient.ambientDimension Q = c) :
    Hilbert.degreeValue ℂ ambient.factorCount ambient.ambientDimension Q (fun _ => 1) = c := by
  unfold Hilbert.degreeValue Hilbert.degreeForm
  rw [hp]
  change eval (fun _ : Fin 1 => (1 : ℚ))
    (((C (c : ℚ) : MvPolynomial (Fin 1) ℚ).totalDegree.factorial : ℚ) •
      homogeneousComponent (C (c : ℚ) : MvPolynomial (Fin 1) ℚ).totalDegree (C (c : ℚ))) = _
  rw [totalDegree_C, homogeneousComponent_of_mem (isHomogeneous_C (Fin 1) (c : ℚ))]
  simp only [ite_true, Nat.factorial_zero, Nat.cast_one, one_smul, eval_C]

theorem sum_of_two_elements {α : Type*} [Fintype α] (a b : α) (hne : a ≠ b)
    (h : ∀ x : α, x = a ∨ x = b) (f : α → ℚ) : ∑ x, f x = f a + f b := by
  classical
  have hu : (Finset.univ : Finset α) = {a,b} := by
    apply Finset.ext
    intro x
    simpa only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff] using h x
  rw [hu, Finset.sum_pair hne]

theorem section_component_sum (h1 : firstComponent.IsPrimary) (h2 : secondComponent.IsPrimary) :
    componentHilbertSum ambient sectionIdeal (⊤ : MaximalOpenLocus ambient) (fun _ => 1) = 6 := by
  classical
  let T := Hilbert.MinimalComponent ℂ ambient.factorCount ambient.ambientDimension sectionIdeal
  letI := Fintype.ofFinite T
  let q1 : T := ⟨firstPoint, by rw [section_minimalPrimes]; exact Or.inl rfl⟩
  let q2 : T := ⟨secondPoint, by rw [section_minimalPrimes]; exact Or.inr rfl⟩
  have hne : q1 ≠ q2 := by
    intro h
    exact radicals_distinct (congrArg (fun q : T => q.val.asIdeal) h)
  have hcover : ∀ q : T, q = q1 ∨ q = q2 := by
    intro q
    have h : q.val.asIdeal ∈ sectionIdeal.minimalPrimes := q.property
    simp only [section_minimalPrimes, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · apply Or.inl
      apply Subtype.ext
      apply PrimeSpectrum.ext
      exact h
    · apply Or.inr
      apply Subtype.ext
      apply PrimeSpectrum.ext
      exact h
  unfold componentHilbertSum Hilbert.componentSum
  change (∑ q : T, if Hilbert.IsRelevant ℂ ambient.factorCount ambient.ambientDimension q.val.asIdeal ∧
    Hilbert.MeetsOpen ℂ ambient.factorCount ambient.ambientDimension q.val.asIdeal ⊤ then
      Hilbert.degreeValue ℂ ambient.factorCount ambient.ambientDimension
        (Hilbert.primaryComponent ℂ ambient.factorCount ambient.ambientDimension sectionIdeal q.val)
        (fun _ => 1) else 0) = 6
  rw [sum_of_two_elements q1 q2 hne hcover]
  change (if Hilbert.IsRelevant ℂ ambient.factorCount ambient.ambientDimension firstPoint.asIdeal ∧
      Hilbert.MeetsOpen ℂ ambient.factorCount ambient.ambientDimension firstPoint.asIdeal ⊤ then _ else 0) +
    (if Hilbert.IsRelevant ℂ ambient.factorCount ambient.ambientDimension secondPoint.asIdeal ∧
      Hilbert.MeetsOpen ℂ ambient.factorCount ambient.ambientDimension secondPoint.asIdeal ⊤ then _ else 0) = 6
  rw [if_pos ⟨first_relevant,prime_meets_top firstPoint⟩,
    if_pos ⟨second_relevant,prime_meets_top secondPoint⟩,
    first_canonical h1, second_canonical h2,
    constant_degree _ 4 first_hilbertPolynomial, constant_degree _ 2 second_hilbertPolynomial]
  norm_num

end PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary

end


set_option autoImplicit false
namespace PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary
open SectionThree

theorem assemble_section_certificate (h1 : firstComponent.IsPrimary) (h2 : secondComponent.IsPrimary) :
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
    componentHilbertSum M I (⊤ : MaximalOpenLocus M) (fun _ => 1) = 6 := by
  exact ⟨section_intersection, h1, h2, radicals_distinct, section_minimalPrimes,
    first_relevant, second_relevant, first_hilbertPolynomial, second_hilbertPolynomial,
    section_component_sum h1 h2⟩

end PhilipponMultiplicity.SectionThreeSupport.BezoutBoundary


open PhilipponMultiplicity SectionThree SectionThreeSupport

theorem solution :
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
    componentHilbertSum M I (⊤ : MaximalOpenLocus M) (fun _ => 1) = 6 := by
  obtain ⟨h1,h2⟩ := BezoutBoundary.primary_from_coordinate_powers
    (fun S n hn => Support.coordinate_power_ideal_isPrimary ℂ BezoutBoundary.ambient.Variable S n hn)
  exact BezoutBoundary.assemble_section_certificate h1 h2
