-- Prove2me | solution 1 for PhilipponMultiplicity.connected_ambient_hilbert_lower
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-10T19:19:33.152021+00:00
-- url     : https://prove2.me/submissions/1a6a3fd3-2c54-43e5-b9a4-5c674659907b

import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_ErratumCorrections
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic
import Theorems.Thm_PhilipponMultiplicity_Hilbert_hilbertPolynomial_zero_iff_trivial
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_primaryDecomposition
import Theorems.Thm_PhilipponMultiplicity_idealMixedDegree_integral
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_exists
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
import Theorems.Thm_PhilipponMultiplicity_product_projective_hilbert_function

section
-- Reused implementation: Solutions.PhilipponProjectiveGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

end MultiProjectiveSpace

end PhilipponMultiplicity

namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

end WeierstrassEllipticZeta
end
end

section
-- Reused implementation: Solutions.PhilipponPointHilbert

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

theorem exists_form_nonzero_at (p : M.Point) (D : M.FactorIndex → ℕ) :
    ∃ Q : M.CoordinateRing, M.IsHomogeneous Q D ∧ M.eval Q p ≠ 0 := by
  classical
  have hj (i : M.FactorIndex) : ∃ j, (p i).rep j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using
      (Projectivization.rep_nonzero (p i))
  choose j hj using hj
  let d : M.Variable →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun v => if v.2 = j v.1 then D v.1 else 0)
  refine ⟨monomial d 1, ?_, ?_⟩
  · intro m hm i
    have hm' : m = d := Finset.mem_singleton.mp (support_monomial_subset hm)
    subst m
    simp [d]
  · change MvPolynomial.eval (M.coordinate p) (monomial d 1) ≠ 0
    rw [eval_monomial]
    simp only [one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    dsimp [d]
    split_ifs with h
    · apply pow_ne_zero
      change (p v.1).rep v.2 ≠ 0
      rw [h]
      exact hj v.1
    · simp

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
end PhilipponMultiplicity
end
end

section
-- Reused implementation: Solutions.PhilipponParametrizedHilbert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertFunction_eq_finrank_image
    {T A : Type*} [CommRing A] [Algebra K A]
    (p : T → M.Point) (φ : M.CoordinateRing →ₐ[K] A) (D : M.FactorIndex → ℕ)
    (hker : ∀ P : M.CoordinateRing, M.IsHomogeneous P D →
      (φ P = 0 ↔ ∀ t, M.eval P (p t) = 0)) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D =
      Module.finrank K ((Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
        φ.toLinearMap) := by
  let V := Hilbert.degreePiece K M.factorCount M.ambientDimension D
  let I := M.vanishingIdeal (Set.range p)
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let g := φ.toLinearMap.domRestrict V
  have hfg : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ φ P.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hker P.val ((M.degreePiece_iff _ _).mp P.property)]
    constructor
    · intro h t
      exact M.eval_eq_zero_of_mem_vanishingIdeal h (Set.mem_range_self t)
    · intro h
      exact Ideal.subset_span ⟨⟨D, (M.degreePiece_iff _ _).mp P.property⟩,
        by rintro x ⟨t, rfl⟩; exact h t⟩
  have hf : LinearMap.range f = V.map (Ideal.Quotient.mkₐ K I).toLinearMap := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  have hg : LinearMap.range g = V.map φ.toLinearMap := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  have he := (f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hfg).trans g.quotKerEquivRange)).finrank_eq
  rw [hf, hg] at he
  exact he

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] {p : ℕ} {N : Fin p → ℕ}

end PhilipponMultiplicity.Hilbert
end
end

section
-- Reused implementation: Solutions.PhilipponProductHilbert

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_total {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : P.IsHomogeneous (∑ i, D i) := by
  intro a ha
  change (Finsupp.weight (fun _ : M.Variable => (1 : ℕ))) a = _
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _ => hP a (mem_support_iff.mpr ha) i)

instance degreePiece_finite (D : M.FactorIndex → ℕ) :
    Module.Finite K (Hilbert.degreePiece K M.factorCount M.ambientDimension D) := by
  let W := MvPolynomial.homogeneousSubmodule M.Variable K (∑ i, D i)
  letI : Module.Finite K W := Module.Finite.of_fg
    (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  have hle : Hilbert.degreePiece K M.factorCount M.ambientDimension D ≤ W := by
    intro P hP
    exact M.homogeneous_total ((M.degreePiece_iff P D).mp hP)
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

def evaluationMap {X : Type*} (p : X → M.Point) : M.CoordinateRing →ₐ[K] (X → K) :=
  AlgHom.pi (fun x => MvPolynomial.aeval (M.coordinate (p x)))

def sectionSpace {X : Type*} (p : X → M.Point) (D : M.FactorIndex → ℕ) :
    Submodule K (X → K) :=
  (Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
    (M.evaluationMap p).toLinearMap

instance sectionSpace_finite {X : Type*} (p : X → M.Point) (D : M.FactorIndex → ℕ) :
    Module.Finite K (M.sectionSpace p D) := by
  unfold sectionSpace
  infer_instance

theorem hilbertFunction_eq_sectionSpace {X : Type*} (p : X → M.Point)
    (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D = Module.finrank K (M.sectionSpace p D) := by
  apply M.hilbertFunction_eq_finrank_image p (M.evaluationMap p) D
  intro P _
  exact funext_iff

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
open SectionThree

theorem product_projective_hilbert_polynomial_of_exists (K : Type*) [Field K]
    (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (hexists : ∀ i, ∃ P, Hilbert.IsHilbertPolynomial K 1 (fun _ => M.ambientDimension i)
      ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
        (V i).carrierInSingleFactor) P) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal (productCarrier M V)) =
      ∏ i, MvPolynomial.rename (fun _ : Fin 1 => i)
        (Hilbert.hilbertPolynomial K 1 (fun _ => M.ambientDimension i)
          ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
            (V i).carrierInSingleFactor)) := by
  classical
  have hspec (i : M.FactorIndex) := Hilbert.hilbertPolynomial_spec
    K 1 (fun _ => M.ambientDimension i)
    ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
      (V i).carrierInSingleFactor) (hexists i)
  choose d₀ hd₀ using hspec
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun i => d₀ i 0, ?_⟩
  intro d hd
  rw [map_prod, product_projective_hilbert_function, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [eval_rename]
  apply hd₀ i (fun _ => d i)
  intro j
  fin_cases j
  exact hd i

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponColonHilbert

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

instance quotientPiece_finite_colon (I : Ideal M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    Module.Finite K (quotientPiece K M.factorCount M.ambientDimension I d) := by
  unfold quotientPiece
  infer_instance

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponPrimeFiltration

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_sup_span (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I ⊔ Ideal.span {P}) := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    simpa only [GradedRing.proj_apply, MvPolynomial.decompose'_apply] using hI f hf d
  have hPg : (Ideal.span {P}).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro f hf
    have heq : f = P := Set.mem_singleton_iff.mp hf
    subst f
    exact ⟨D, (M.degreePiece_iff P D).mpr hP⟩
  intro f hf d
  exact weightedHomogeneousComponent_mem_of_mem K w (hIg.sup hPg) hf d

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponMonomialPartition

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MonomialCells

variable (p : ℕ) (N : Fin p → ℕ)

abbrev Var := Sigma fun i : Fin p => Fin (N i + 1)

theorem weight_apply (e : Var p N →₀ ℕ) (i : Fin p) :
    Finsupp.weight (Hilbert.blockWeight p N) e i = ∑ j, e ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : Fin p, ∑ j : Fin (N b + 1),
    e ⟨b,j⟩ • Hilbert.blockWeight p N ⟨b,j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

end PhilipponMultiplicity.MonomialCells

end
end

section
-- Reused implementation: Solutions.PhilipponProductDegree

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ProductDegree

theorem top_mul {σ : Type*} (P Q : MvPolynomial σ ℚ) (a b : ℕ)
    (hP : P.totalDegree ≤ a) (hQ : Q.totalDegree ≤ b) :
    homogeneousComponent (a + b) (P * Q) =
      homogeneousComponent a P * homogeneousComponent b Q := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  by_cases hd : d.degree = a + b
  · rw [if_pos hd]
    apply Finset.sum_congr rfl
    rintro ⟨e, f⟩ hef
    have hef' : e + f = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hef
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases he : coeff e P = 0
    · simp [he]
    by_cases hf : coeff f Q = 0
    · simp [hf]
    have he' : e.degree ≤ a := (le_totalDegree (mem_support_iff.mpr he)).trans hP
    have hf' : f.degree ≤ b := (le_totalDegree (mem_support_iff.mpr hf)).trans hQ
    have hsum : e.degree + f.degree = a + b := by
      rw [← map_add, hef', hd]
    have hea : e.degree = a := by omega
    have hfb : f.degree = b := by omega
    simp [hea, hfb]
  · rw [if_neg hd]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨e, f⟩ hef
    have hef' : e + f = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hef
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases he : e.degree = a
    · by_cases hf : f.degree = b
      · exfalso
        apply hd
        rw [← hef', map_add, he, hf]
      · simp [hf]
    · simp [he]

theorem top_prod {σ ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℚ)
    (hP : ∀ i ∈ s, P i ≠ 0) :
    (∏ i ∈ s, P i).totalDegree = ∑ i ∈ s, (P i).totalDegree ∧
    homogeneousComponent (∏ i ∈ s, P i).totalDegree (∏ i ∈ s, P i) =
      ∏ i ∈ s, homogeneousComponent (P i).totalDegree (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hpi := hP i (Finset.mem_insert_self i s)
    have hps : ∀ j ∈ s, P j ≠ 0 := fun j hj => hP j (Finset.mem_insert_of_mem hj)
    obtain ⟨hdeg, htop⟩ := ih hps
    have hprod : ∏ j ∈ s, P j ≠ 0 := Finset.prod_ne_zero_iff.mpr hps
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [totalDegree_mul_of_isDomain hpi hprod]
    constructor
    · rw [hdeg]
    · rw [top_mul _ _ _ _ le_rfl le_rfl, htop]

theorem degree_fin_one (d : Fin 1 →₀ ℕ) : d.degree = d 0 := by
  simp [Finsupp.degree_eq_sum]

theorem top_fin_one (P : MvPolynomial (Fin 1) ℚ) :
    homogeneousComponent P.totalDegree P =
      monomial (Finsupp.single 0 P.totalDegree) (coeff (Finsupp.single 0 P.totalDegree) P) := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_monomial]
  have hd : d.degree = P.totalDegree ↔ Finsupp.single 0 P.totalDegree = d := by
    rw [degree_fin_one]
    constructor
    · intro h
      apply Finsupp.ext
      intro i
      fin_cases i
      simpa using h.symm
    · intro h
      rw [← h, Finsupp.single_eq_same]
  by_cases h : d.degree = P.totalDegree
  · rw [if_pos h, if_pos (hd.mp h), ← hd.mp h]
  · rw [if_neg h, if_neg (mt hd.mpr h)]

theorem degree_rename_single {ι : Type*} (i : ι) (P : MvPolynomial (Fin 1) ℚ) :
    (rename (fun _ => i) P).totalDegree = P.totalDegree := by
  have h := (weightedTotalDegree_rename_of_injective
      (w := (1 : ι → ℕ)) (P := P)
      (show Function.Injective (fun _ : Fin 1 => i) from fun _ _ _ => Subsingleton.elim _ _))
  change weightedTotalDegree 1 _ = weightedTotalDegree 1 _ at h
  simpa only [weightedTotalDegree_one] using h

theorem eval_top_fin_one (P : MvPolynomial (Fin 1) ℚ) (d : Fin 1 → ℚ) :
    eval d (homogeneousComponent P.totalDegree P) =
      coeff (Finsupp.single 0 P.totalDegree) P * d 0 ^ P.totalDegree := by
  conv_lhs => rw [top_fin_one P]
  rw [eval_monomial, Finsupp.prod_single_index]
  simp

theorem normalized_product {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial (Fin 1) ℚ) (d : ι → ℚ) :
    let Q := ∏ i, rename (fun _ : Fin 1 => i) (P i)
    eval d ((Q.totalDegree.factorial : ℚ) • homogeneousComponent Q.totalDegree Q) =
      (Q.totalDegree.factorial : ℚ) / (∏ i, ((P i).totalDegree.factorial : ℚ)) *
        (∏ i, eval (fun _ => 1)
          (((P i).totalDegree.factorial : ℚ) •
            homogeneousComponent (P i).totalDegree (P i))) *
        ∏ i, d i ^ (P i).totalDegree := by
  classical
  dsimp only
  by_cases hP : ∀ i, P i ≠ 0
  · have hrename (i : ι) : rename (fun _ : Fin 1 => i) (P i) ≠ 0 := by
      exact fun h => hP i ((rename_injective _ (fun _ _ _ => Subsingleton.elim _ _)) h)
    have htop := (top_prod Finset.univ
      (fun i => rename (fun _ : Fin 1 => i) (P i)) (fun i _ => hrename i)).2
    rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, htop, map_prod]
    simp_rw [degree_rename_single, ← rename_homogeneousComponent, eval_rename,
      eval_top_fin_one, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, eval_top_fin_one]
    simp only [Function.comp_apply, one_pow, mul_one, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hfact : (∏ i, ((P i).totalDegree.factorial : ℚ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact_mod_cast Nat.factorial_ne_zero (P i).totalDegree
    field_simp
  · push Not at hP
    obtain ⟨i, hi⟩ := hP
    have hprod : (∏ j, rename (fun _ : Fin 1 => j) (P j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hi, map_zero]
    have hprod' : (∏ j, eval (fun _ => (1 : ℚ))
        (((P j).totalDegree.factorial : ℚ) •
          homogeneousComponent (P j).totalDegree (P j))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [hprod, hprod']
    simp

end PhilipponMultiplicity.ProductDegree

namespace PhilipponMultiplicity
open SectionThree

theorem lemma_3_4_of_product_hilbertPolynomial
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (hprod : Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal (productCarrier M V)) =
      ∏ i, MvPolynomial.rename (fun _ : Fin 1 => i)
        (Hilbert.hilbertPolynomial K 1 (fun _ => M.ambientDimension i)
          ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
            (V i).carrierInSingleFactor)))
    (d : M.FactorIndex → ℕ) :
    locusDegreeValue M (productCarrier M V) d =
      ((locusDimension M (productCarrier M V)).factorial : ℚ) /
        (∏ i, ((V i).dimension.factorial : ℚ)) *
        (∏ i, (V i).degree) * ∏ i, (d i : ℚ) ^ (V i).dimension := by
  unfold locusDegreeValue locusDimension idealDegreeValue idealDimension
    ProjectiveSubvariety.dimension ProjectiveSubvariety.degree
    idealDegreeValue idealDimension Hilbert.degreeValue Hilbert.degreeForm
  rw [hprod]
  exact ProductDegree.normalized_product _ _

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponFiltrationPolynomial

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertPolynomial_top :
    hilbertPolynomial K M.factorCount M.ambientDimension (⊤ : Ideal M.CoordinateRing) = 0 := by
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, fun d hd => ?_⟩
  simp only [map_zero, hilbertFunction]
  letI : Subsingleton (quotientPiece K M.factorCount M.ambientDimension
      (⊤ : Ideal M.CoordinateRing) d) := inferInstance
  rw [Module.finrank_zero_of_subsingleton]
  rfl

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponFiniteDifference

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.FiniteDifference
variable {ι : Type*} [Fintype ι]

def shift (D : ι → ℚ) : MvPolynomial ι ℚ →ₐ[ℚ] MvPolynomial ι ℚ :=
  aeval (fun i => X i - C (D i))

def deriv (D : ι → ℚ) : MvPolynomial ι ℚ →ₗ[ℚ] MvPolynomial ι ℚ :=
  ∑ i, D i • (pderiv i).toLinearMap

theorem deriv_apply (D : ι → ℚ) (F : MvPolynomial ι ℚ) :
    deriv D F = ∑ i, D i • pderiv i F := by
  simp only [deriv, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

theorem deriv_mul_X (D : ι → ℚ) (F : MvPolynomial ι ℚ) (i : ι) :
    deriv D (F * X i) = deriv D F * X i + D i • F := by
  classical
  simp only [deriv_apply, pderiv_mul, pderiv_X, MvPolynomial.smul_eq_C_mul,
    mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  simp [Pi.single_apply, mul_ite, mul_assoc]

private theorem component_mul_X (F : MvPolynomial ι ℚ) (i : ι) (n : ℕ) :
    homogeneousComponent (n + 1) (F * X i) = homogeneousComponent n F * X i := by
  classical
  letI := weightedGradedAlgebra ℚ (1 : ι → ℕ)
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule ℚ (1 : ι → ℕ))
    (a := F) (i := n) (isHomogeneous_X ℚ i)
  change ((MvPolynomial.decompose' ℚ (1 : ι → ℕ) (F * X i)) (n + 1) : MvPolynomial ι ℚ) =
    ((MvPolynomial.decompose' ℚ (1 : ι → ℕ) F) n : MvPolynomial ι ℚ) * X i at h
  simpa only [MvPolynomial.decompose'_apply, homogeneousComponent] using h

private theorem degree_le_pred_of_top_zero (F : MvPolynomial ι ℚ) (n : ℕ)
    (hdegree : F.totalDegree ≤ n) (hzero : homogeneousComponent n F = 0) :
    F.totalDegree ≤ n - 1 := by
  classical
  apply Finset.sup_le
  intro d hd
  have hdn : d.degree ≤ n := (le_totalDegree hd).trans hdegree
  have hne : d.degree ≠ n := by
    intro heq
    have hh := congrArg (coeff d) hzero
    simp only [coeff_homogeneousComponent, heq, if_pos rfl, coeff_zero] at hh
    exact (mem_support_iff.mp hd) hh
  change d.degree ≤ n - 1
  omega

private def Expansion (D : ι → ℚ) (F : MvPolynomial ι ℚ) (n : ℕ) : Prop :=
  (shift D F).totalDegree ≤ n ∧ homogeneousComponent n (shift D F) = F ∧
    (∀ k, n = k + 1 → homogeneousComponent k (shift D F) = -deriv D F)

private theorem expansion_C (D : ι → ℚ) (c : ℚ) : Expansion D (C c) 0 := by
  simp [Expansion, shift]

private theorem expansion_mul_X (D : ι → ℚ) (F : MvPolynomial ι ℚ) (n : ℕ)
    (hF : F.IsHomogeneous n) (h : Expansion D F n) (i : ι) :
    Expansion D (F * X i) (n + 1) := by
  classical
  rcases h with ⟨hdeg, htop, hnext⟩
  have hs : shift D (F * X i) = shift D F * X i - D i • shift D F := by
    simp only [shift, map_mul, aeval_X, mul_sub, MvPolynomial.smul_eq_C_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (by simpa using Nat.add_le_add_right hdeg 1)
    · exact (totalDegree_smul_le _ _).trans (hdeg.trans (Nat.le_succ n))
  · rw [hs, map_sub, map_smul, component_mul_X, htop,
      homogeneousComponent_eq_zero _ _ (by omega : (shift D F).totalDegree < n + 1)]
    simp
  · intro k hk
    have hkn : k = n := by omega
    subst k
    rw [hs, map_sub, map_smul, htop, deriv_mul_X]
    cases n with
    | zero =>
      have hconst : F = C (coeff 0 F) := by
        exact (homogeneousComponent_eq_self hF).symm.trans
          (MvPolynomial.homogeneousComponent_zero F)
      have hd : deriv D F = 0 := by
        nth_rw 1 [hconst]
        simp [deriv]
      have hz : coeff (0 : ι →₀ ℕ) (shift D F * X i) = 0 := by
        simpa using (MvPolynomial.coeff_mul_X' (0 : ι →₀ ℕ) i (shift D F))
      simp [hd, homogeneousComponent_zero, hz]
    | succ n =>
      rw [component_mul_X, hnext n rfl]
      simp only [neg_mul, neg_add_rev, sub_eq_add_neg]
      ac_rfl

private theorem expansion_monomial (D : ι → ℚ) (a : ι →₀ ℕ) (c : ℚ) :
    Expansion D (monomial a c) a.degree := by
  classical
  induction a using Finsupp.induction with
  | zero => simpa using expansion_C D c
  | @single_add i k a hia hk ih =>
    have haux : ∀ k, Expansion D (monomial (Finsupp.single i k + a) c)
        ((Finsupp.single i k + a).degree) := by
      intro k
      induction k with
      | zero => simpa using ih
      | succ k ihk =>
        have heq : monomial (Finsupp.single i (k + 1) + a) c =
            monomial (Finsupp.single i k + a) c * X i := by
          simp only [monomial_single_add, pow_succ]
          ring
        rw [heq]
        have hh := expansion_mul_X D (monomial (Finsupp.single i k + a) c)
          (Finsupp.single i k + a).degree (isHomogeneous_monomial c rfl) ihk i
        simpa only [map_add, Finsupp.degree_single, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hh
    exact haux k

private theorem monomial_difference (D : ι → ℚ) (a : ι →₀ ℕ) (c : ℚ) :
    (monomial a c - shift D (monomial a c)).totalDegree ≤ a.degree - 1 ∧
    (a.degree = 0 → monomial a c - shift D (monomial a c) = 0) ∧
    (0 < a.degree → homogeneousComponent (a.degree - 1)
      (monomial a c - shift D (monomial a c)) = deriv D (monomial a c)) := by
  obtain ⟨hdeg, htop, hnext⟩ := expansion_monomial D a c
  have hhom := isHomogeneous_monomial (σ := ι) c (show a.degree = a.degree from rfl)
  have hbd : (monomial a c - shift D (monomial a c)).totalDegree ≤ a.degree :=
    (totalDegree_sub _ _).trans (max_le hhom.totalDegree_le hdeg)
  refine ⟨degree_le_pred_of_top_zero _ _ hbd ?_, ?_, ?_⟩
  · rw [map_sub, homogeneousComponent_eq_self hhom, htop, sub_self]
  · intro ha
    have hconst : monomial a c = C (coeff 0 (monomial a c)) :=
      (homogeneousComponent_eq_self (ha ▸ hhom)).symm.trans
        (MvPolynomial.homogeneousComponent_zero _)
    conv_lhs => rw [hconst]
    simp [shift]
  · intro ha
    rw [map_sub, homogeneousComponent_of_mem hhom,
      if_neg (by omega), hnext (a.degree - 1) (by omega)]
    simp

theorem top_difference (D : ι → ℚ) (F : MvPolynomial ι ℚ) (a : ℕ)
    (ha : 0 < a) (hF : F.totalDegree ≤ a) :
    (F - shift D F).totalDegree ≤ a - 1 ∧
    homogeneousComponent (a - 1) (F - shift D F) =
      deriv D (homogeneousComponent a F) := by
  classical
  let δ : MvPolynomial ι ℚ →ₗ[ℚ] MvPolynomial ι ℚ :=
    LinearMap.id - (shift D).toLinearMap
  have hδ : δ F = F - shift D F := rfl
  have hsum : F - shift D F = ∑ d ∈ F.support, δ (monomial d (coeff d F)) := by
    rw [← hδ, ← map_sum]
    congr 1
    exact F.as_sum
  have hterm (d : ι →₀ ℕ) (hd : d ∈ F.support) :
      (δ (monomial d (coeff d F))).totalDegree ≤ a - 1 ∧
      homogeneousComponent (a - 1) (δ (monomial d (coeff d F))) =
        deriv D (homogeneousComponent a (monomial d (coeff d F))) := by
    obtain ⟨hdeg, hz, ht⟩ := monomial_difference D d (coeff d F)
    have hda : d.degree ≤ a := (le_totalDegree hd).trans hF
    refine ⟨hdeg.trans (Nat.sub_le_sub_right hda 1), ?_⟩
    change homogeneousComponent (a - 1) (monomial d (coeff d F) - shift D (monomial d (coeff d F))) = _
    by_cases heq : d.degree = a
    · rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff d F) rfl),
        if_pos heq.symm, ← heq]
      exact ht (heq ▸ ha)
    · rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff d F) rfl),
        if_neg (Ne.symm heq), map_zero]
      by_cases hd0 : d.degree = 0
      · rw [hz hd0, map_zero]
      · exact homogeneousComponent_eq_zero _ _ (by omega)
  constructor
  · rw [hsum]
    exact (totalDegree_finsetSum _ _).trans (Finset.sup_le (fun d hd => (hterm d hd).1))
  · rw [hsum, map_sum]
    conv_rhs => rw [F.as_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun d hd => (hterm d hd).2)

theorem coeff_deriv (D : ι → ℚ) (F : MvPolynomial ι ℚ) (b : ι →₀ ℕ) :
    coeff b (deriv D F) =
      ∑ i, D i * (coeff (b + Finsupp.single i 1) F * (b i + 1 : ℚ)) := by
  classical
  rw [deriv_apply]
  change coeff b (∑ i, D i • pderiv i F) = _
  simp only [coeff_sum, coeff_smul, smul_eq_mul, coeff_pderiv]

theorem eval_deriv_self (D : ι → ℚ) (F : MvPolynomial ι ℚ) (a : ℕ)
    (hF : F.IsHomogeneous a) : eval D (deriv D F) = (a : ℚ) * eval D F := by
  classical
  have hh := congrArg (eval D) hF.sum_X_mul_pderiv
  rw [deriv_apply]
  change eval D (∑ i, D i • pderiv i F) = _
  simpa only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, eval_X, map_nsmul,
    nsmul_eq_mul, map_natCast] using hh

end PhilipponMultiplicity.FiniteDifference

end
end

section
-- Reused implementation: Solutions.PhilipponRelevantHilbert

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertFunction_antitone (I J : Ideal M.CoordinateRing) (hIJ : I ≤ J)
    (d : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension J d ≤
      hilbertFunction K M.factorCount M.ambientDimension I d := by
  let q := Ideal.quotientMapₐ J (AlgHom.id K M.CoordinateRing) hIJ
  let f : quotientPiece K M.factorCount M.ambientDimension I d →ₗ[K]
      quotientPiece K M.factorCount M.ambientDimension J d :=
    (q.toLinearMap.domRestrict _).codRestrict _ (by
      rintro ⟨x, P, hP, rfl⟩
      exact ⟨P, hP, rfl⟩)
  apply LinearMap.finrank_le_finrank_of_surjective (f := f)
  rintro ⟨x, P, hP, rfl⟩
  exact ⟨⟨Ideal.Quotient.mk I P, ⟨P, hP, rfl⟩⟩, rfl⟩

theorem relevant_variables (Q : Ideal M.CoordinateRing)
    (hQ : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ v : ∀ i, Fin (M.ambientDimension i + 1), ∀ i, X ⟨i, v i⟩ ∉ Q := by
  classical
  have hx (i : M.FactorIndex) : ∃ j : Fin (M.ambientDimension i + 1), X ⟨i, j⟩ ∉ Q := by
    by_contra! h
    apply hQ
    apply (iInf_le (blockIdeal K M.factorCount M.ambientDimension) i).trans
    rw [blockIdeal, Ideal.span_le]
    rintro x ⟨j, rfl⟩
    exact h j
  exact Classical.axiomOfChoice hx

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponProjectiveLocalMembership

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_mem_of_hilbertFunction_zero
    (I : Ideal M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hzero : hilbertFunction K M.factorCount M.ambientDimension I D = 0)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D) : P ∈ I := by
  have hbot : quotientPiece K M.factorCount M.ambientDimension I D = ⊥ :=
    Submodule.finrank_eq_zero.mp hzero
  have hmem : Ideal.Quotient.mk I P ∈
      quotientPiece K M.factorCount M.ambientDimension I D :=
    ⟨P, (M.degreePiece_iff P D).mpr hP, rfl⟩
  rw [hbot] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hmem)

theorem irrelevant_eventually_contains_homogeneous
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hirr : ¬ IsRelevant K M.factorCount M.ambientDimension I.radical) :
    ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
      ∀ P, M.IsHomogeneous P D → P ∈ I := by
  have hz : hilbertPolynomial K M.factorCount M.ambientDimension I = 0 :=
    (hilbertPolynomial_zero_iff_trivial M I hI).mpr hirr
  have hspec := hilbertPolynomial_spec K M.factorCount M.ambientDimension I
    (multigraded_hilbert_polynomial_exists K M I hI)
  rw [hz] at hspec
  obtain ⟨E, hE⟩ := hspec
  refine ⟨E, fun D hD P hP => ?_⟩
  have hzero : hilbertFunction K M.factorCount M.ambientDimension I D = 0 := by
    have h := hE D hD
    simp only [map_zero] at h
    exact_mod_cast h.symm
  exact homogeneous_mem_of_hilbertFunction_zero M I D hzero P hP

theorem PrimaryDecomposition.eventual_relevant_membership
    {I : Ideal M.CoordinateRing} (A : PrimaryDecomposition M I) :
    ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
      ∀ P, M.IsHomogeneous P D →
        (P ∈ I ↔ ∀ j : Fin A.count,
          IsRelevant K M.factorCount M.ambientDimension (A.component j).radical →
          P ∈ A.component j) := by
  classical
  have hchoose (j : Fin A.count) : ∃ E : M.FactorIndex → ℕ,
      ¬ IsRelevant K M.factorCount M.ambientDimension (A.component j).radical →
      ∀ D, (∀ i, E i ≤ D i) → ∀ P, M.IsHomogeneous P D → P ∈ A.component j := by
    by_cases hj : IsRelevant K M.factorCount M.ambientDimension (A.component j).radical
    · exact ⟨0, fun h => (h hj).elim⟩
    · obtain ⟨E, hE⟩ := irrelevant_eventually_contains_homogeneous M
        (A.component j) (A.homogeneous j) hj
      exact ⟨E, fun _ => hE⟩
  choose E hE using hchoose
  refine ⟨fun i => ∑ j, E j i, ?_⟩
  intro D hD P hP
  have hmem : P ∈ I ↔ ∀ j : Fin A.count, P ∈ A.component j := by
    constructor
    · exact fun h j => (A.intersection_eq.le.trans (iInf_le _ j)) h
    · exact fun h => A.intersection_eq.ge (Ideal.mem_iInf.mpr h)
  rw [hmem]
  constructor
  · exact fun h j _ => h j
  · intro h j
    by_cases hj : IsRelevant K M.factorCount M.ambientDimension (A.component j).radical
    · exact h j hj
    · exact hE j hj D (fun i =>
        (Finset.single_le_sum (fun k _ => Nat.zero_le (E k i))
          (Finset.mem_univ j)).trans (hD i)) P hP

end PhilipponMultiplicity.Hilbert
end
end

section
-- Reused implementation: Solutions.PhilipponProjectiveHilbertExistence

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

theorem vanishingIdeal_multihomogeneous (K : Type*) [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hh : (M.vanishingIdeal S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D, hD⟩ := hP.1
    refine ⟨D, ?_⟩
    intro e he
    funext i
    rw [MonomialCells.weight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponFilterRegularSections

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertFunction_eq_of_homogeneous_mem_iff
    (I J : Ideal M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hmem : ∀ P, M.IsHomogeneous P D → (P ∈ I ↔ P ∈ J)) :
    hilbertFunction K M.factorCount M.ambientDimension I D =
      hilbertFunction K M.factorCount M.ambientDimension J D := by
  let V := degreePiece K M.factorCount M.ambientDimension D
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let g := (Ideal.Quotient.mkₐ K J).toLinearMap.domRestrict V
  have hker : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ Ideal.Quotient.mk J P.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem P.val ((M.degreePiece_iff _ _).mp P.property)
  have hrange (A : Ideal M.CoordinateRing) :
      LinearMap.range ((Ideal.Quotient.mkₐ K A).toLinearMap.domRestrict V) =
        V.map (Ideal.Quotient.mkₐ K A).toLinearMap := by
    ext x
    constructor
    · rintro ⟨P,rfl⟩
      exact ⟨P.val,P.property,rfl⟩
    · rintro ⟨P,hP,rfl⟩
      exact ⟨⟨P,hP⟩,rfl⟩
  have he := (f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans g.quotKerEquivRange)).finrank_eq
  rw [hrange I,hrange J] at he
  exact he

theorem hilbertPolynomial_eq_of_eventual_homogeneous_mem_iff
    (I J : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hmem : ∃ B : M.FactorIndex → ℕ, ∀ D, (∀ i, B i ≤ D i) →
      ∀ P, M.IsHomogeneous P D → (P ∈ I ↔ P ∈ J)) :
    hilbertPolynomial K M.factorCount M.ambientDimension I =
      hilbertPolynomial K M.factorCount M.ambientDimension J := by
  obtain ⟨F,hF⟩ := multigraded_hilbert_polynomial_exists K M I hI
  obtain ⟨a,ha⟩ := hF
  obtain ⟨b,hb⟩ := hmem
  have hJ : IsHilbertPolynomial K M.factorCount M.ambientDimension J F := by
    refine ⟨fun i => max (a i) (b i),?_⟩
    intro D hD
    rw [ha D (fun i => (le_max_left _ _).trans (hD i)),
      hilbertFunction_eq_of_homogeneous_mem_iff M I J D
        (hb D (fun i => (le_max_right _ _).trans (hD i)))]
  rw [hilbertPolynomial_eq_of_isHilbertPolynomial K M.factorCount M.ambientDimension I ⟨a,ha⟩,
      hilbertPolynomial_eq_of_isHilbertPolynomial K M.factorCount M.ambientDimension J hJ]

theorem degreeValue_of_constant_hilbertPolynomial
    (I : Ideal M.CoordinateRing) (c : ℚ)
    (hP : hilbertPolynomial K M.factorCount M.ambientDimension I = C c)
    (D : M.FactorIndex → ℕ) :
    degreeValue K M.factorCount M.ambientDimension I D = c := by
  unfold degreeValue degreeForm
  rw [hP]
  dsimp only
  rw [totalDegree_C]
  simp only [Nat.factorial_zero,Nat.cast_one,one_smul,homogeneousComponent_zero,
    coeff_C,ite_true,eval_C]

end PhilipponMultiplicity.Hilbert
end
end

section
-- Reused implementation: Solutions.PhilipponGenericChoice

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.GenericChoice
variable {K σ : Type*} [Field K] [Infinite K]

theorem exists_eval_ne_zero (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x F ≠ 0 := by
  by_contra! h
  apply hF
  apply MvPolynomial.funext
  intro x
  simpa using h x

theorem exists_eval_ne_zero_avoiding_subspaces [Fintype σ]
    (S : Finset (Submodule K (σ → K))) (hS : ∀ U ∈ S, U ≠ ⊤)
    (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x F ≠ 0 ∧ ∀ U ∈ S, x ∉ U := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty =>
    obtain ⟨x,hx⟩ := exists_eval_ne_zero F hF
    exact ⟨x,hx,by simp⟩
  | @insert U S hUS ih =>
    have hU : U ≠ ⊤ := hS U (Finset.mem_insert_self _ _)
    obtain ⟨v,hv⟩ : ∃ v : σ → K, v ∉ U := by
      by_contra! h
      exact hU (top_unique (fun x _ => h x))
    obtain ⟨f,hfv,hUf⟩ := Submodule.exists_le_ker_of_notMem hv
    let g : MvPolynomial σ K := ∑ i, MvPolynomial.C (f (Pi.single i 1)) * MvPolynomial.X i
    have heval (x : σ → K) : MvPolynomial.eval x g = f x := by
      calc
        MvPolynomial.eval x g = ∑ i, f (Pi.single i 1) * x i := by simp [g]
        _ = f (∑ i, x i • Pi.single i (1 : K)) := by
          simp [map_sum, map_smul, smul_eq_mul, mul_comm]
        _ = f x := by
          congr 1
          ext j
          simp [Pi.single_apply]
    have hg : g ≠ 0 := by
      intro hz
      have := heval v
      rw [hz, map_zero] at this
      exact hfv this.symm
    obtain ⟨x,hx,havoid⟩ := ih (fun V hV => hS V (Finset.mem_insert_of_mem hV))
      (F * g) (mul_ne_zero hF hg)
    rw [map_mul, mul_ne_zero_iff] at hx
    refine ⟨x,hx.1,?_⟩
    intro V hV
    rcases Finset.mem_insert.mp hV with rfl | hV
    · intro hxU
      apply hx.2
      rw [heval]
      exact hUf hxU
    · exact havoid V hV

end PhilipponMultiplicity.GenericChoice

end
end

section
-- Reused implementation: Solutions.PhilipponMixedFlagChoice

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MixedFlag
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem rowForm_single (i : M.FactorIndex) (j : Fin (M.ambientDimension i + 1)) :
    rowForm M i (Pi.single ⟨i,j⟩ 1) = MvPolynomial.X ⟨i,j⟩ := by
  classical
  simp [rowForm, Pi.single_apply]

theorem rowForm_homogeneous (b : M.FactorIndex) (a : M.Variable → K) :
    M.IsHomogeneous (rowForm M b a) (Pi.single b 1) := by
  classical
  intro m hm i
  change m ∈ (∑ t : Fin (M.ambientDimension b + 1),
    a ⟨b,t⟩ • (MvPolynomial.X ⟨b,t⟩ : M.CoordinateRing)).support at hm
  have hs := MvPolynomial.support_sum (s := Finset.univ)
    (f := fun t : Fin (M.ambientDimension b + 1) =>
      a ⟨b,t⟩ • (MvPolynomial.X ⟨b,t⟩ : M.CoordinateRing)) hm
  obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hs
  have hmX : m ∈ (MvPolynomial.X (⟨b,t⟩ : M.Variable) : M.CoordinateRing).support :=
    MvPolynomial.support_smul ht
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at hmX
  subst m
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff, Pi.single_apply]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b,t⟩ : M.Variable) ≠ ⟨i,k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, Pi.single_apply, hi, hn]

end PhilipponMultiplicity.MixedFlag

end
end

section
-- Reused implementation: Solutions.PhilipponEmbeddedAvoidance

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.ComponentSelection

theorem regular_quotient_iInf {R ι : Type*} [CommRing R]
    (Q : ι → Ideal R) (s : ι → Prop) (hQ : ∀ i, (Q i).IsPrimary)
    (x : R) (hx : ∀ i, s i → x ∉ (Q i).radical) :
    IsRegular (Ideal.Quotient.mk (⨅ i, if s i then Q i else ⊤) x) := by
  classical
  let A : Ideal R := ⨅ i, if s i then Q i else ⊤
  apply (Commute.isRegular_iff (fun y => mul_comm _ y)).mpr
  apply isLeftRegular_of_non_zero_divisor
  intro z hz
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change r ∈ A
  have hxr : x * r ∈ A := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hz
  simp only [A, Submodule.mem_iInf] at hxr ⊢
  intro i
  split_ifs with hi
  · have hmem : x * r ∈ Q i := by simpa only [if_pos hi] using hxr i
    exact ((Ideal.isPrimary_iff.mp (hQ i)).2 (mul_comm x r ▸ hmem)).resolve_right (hx i hi)
  · trivial

end PhilipponMultiplicity.ComponentSelection

namespace PhilipponMultiplicity.SectionThreeSupport
open ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

end PhilipponMultiplicity.SectionThreeSupport

end
end

section
-- Reused implementation: Solutions.PhilipponProjectiveRegularReduction

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem exists_regular_linear_reduction [Infinite K]
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (i : M.FactorIndex) :
    ∃ (J : Ideal M.CoordinateRing) (L : M.CoordinateRing),
      I ≤ J ∧ IsMultihomogeneousIdeal M J ∧
      hilbertPolynomial K M.factorCount M.ambientDimension J =
        hilbertPolynomial K M.factorCount M.ambientDimension I ∧
      M.IsHomogeneous L (Pi.single i 1) ∧ IsRegular (Ideal.Quotient.mk J L) := by
  classical
  obtain ⟨D⟩ := exists_primaryDecomposition M I hI
  let good (j : Fin D.count) :=
    IsRelevant K M.factorCount M.ambientDimension (D.component j).radical
  let J : Ideal M.CoordinateRing := ⨅ j, if good j then D.component j else ⊤
  have hIJ : I ≤ J := by
    apply le_iInf
    intro j
    split_ifs
    · exact D.intersection_eq.le.trans (iInf_le _ j)
    · exact le_top
  have hJ : IsMultihomogeneousIdeal M J := by
    intro P hP d
    apply Ideal.mem_iInf.mpr
    intro j
    by_cases hj : good j
    · have hPj := Ideal.mem_iInf.mp hP j
      simp only [if_pos hj] at hPj ⊢
      exact D.homogeneous j P hPj d
    · simp only [if_neg hj, Submodule.mem_top]
  have hpoly : hilbertPolynomial K M.factorCount M.ambientDimension J =
      hilbertPolynomial K M.factorCount M.ambientDimension I := by
    symm
    apply hilbertPolynomial_eq_of_eventual_homogeneous_mem_iff M I J hI
    obtain ⟨B, hB⟩ := PrimaryDecomposition.eventual_relevant_membership M D
    refine ⟨B, fun d hd P hP => ?_⟩
    rw [hB d hd P hP]
    simp only [J, Ideal.mem_iInf]
    constructor
    · intro h j
      split_ifs with hj
      · exact h j hj
      · trivial
    · intro h j hj
      change good j at hj
      simpa only [if_pos hj] using h j
  let bad (j : Fin D.count) : Submodule K (M.Variable → K) :=
    ((D.component j).radical.restrictScalars K).comap (MixedFlag.rowForm M i)
  let S := (Finset.univ.filter good).image bad
  have hS : ∀ U ∈ S, U ≠ ⊤ := by
    intro U hU
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨v, hv⟩ := relevant_variables M _ (Finset.mem_filter.mp hj).2
    intro heq
    have hx : Pi.single (⟨i, v i⟩ : M.Variable) (1 : K) ∈ bad j := by
      rw [heq]
      trivial
    change MixedFlag.rowForm M i (Pi.single ⟨i, v i⟩ 1) ∈ (D.component j).radical at hx
    rw [MixedFlag.rowForm_single] at hx
    exact hv i hx
  obtain ⟨a, _, ha⟩ := GenericChoice.exists_eval_ne_zero_avoiding_subspaces S hS
    (1 : MvPolynomial M.Variable K) one_ne_zero
  refine ⟨J, MixedFlag.rowForm M i a, hIJ, hJ, hpoly,
    MixedFlag.rowForm_homogeneous M i a, ?_⟩
  apply ComponentSelection.regular_quotient_iInf D.component good D.primary
  intro j hj
  exact ha (bad j) (Finset.mem_image.mpr
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩)

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponProjectiveAmbientDegree

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ProjectiveAmbientDegree
open Hilbert SectionThree

def monomialEquiv (N d : ℕ) :
    {e : MonomialCells.Var 1 (fun _ => N) →₀ ℕ //
      Finsupp.weight (blockWeight 1 (fun _ => N)) e = fun _ => d} ≃
    {f : Fin (N+1) → ℕ // ∑ j, f j = d} where
  toFun e := ⟨fun j => e.1 ⟨0,j⟩, by
    have h := congrFun e.2 (0 : Fin 1)
    rwa [MonomialCells.weight_apply] at h⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun v => f.1 v.2), by
    funext i
    rw [MonomialCells.weight_apply]
    simpa using f.2⟩
  left_inv e := by
    apply Subtype.ext
    apply Finsupp.ext
    rintro ⟨i,j⟩
    fin_cases i
    rfl
  right_inv f := by
    apply Subtype.ext
    rfl

theorem degreePiece_finrank (K : Type*) [Field K] (N d : ℕ) :
    Module.finrank K (degreePiece K 1 (fun _ => N) (fun _ => d)) = (d+N).choose N := by
  classical
  unfold degreePiece
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K) _).finrank_eq]
  change Module.finrank K ({e : MonomialCells.Var 1 (fun _ => N) →₀ ℕ //
    Finsupp.weight (blockWeight 1 (fun _ => N)) e = fun _ => d} →₀ K) = _
  let e := (monomialEquiv N d).trans (Sym.equivNatSumOfFintype (Fin (N+1)) d).symm
  rw [(Finsupp.domLCongr e : (_ →₀ K) ≃ₗ[K] (Sym (Fin (N+1)) d →₀ K)).finrank_eq,
    Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card,
    Sym.natCard_sym_eq_multichoose, Nat.card_fin, Nat.multichoose_eq]
  have heq : N+1+d-1 = d+N := by omega
  rw [heq, ← Nat.choose_symm (show d ≤ d+N by omega)]
  simp

theorem hilbertFunction_bot (K : Type*) [Field K] (N d : ℕ) :
    hilbertFunction K 1 (fun _ => N) ⊥ (fun _ => d) = (d+N).choose N := by
  let e := (AlgEquiv.quotientBot K (CoordinateRing K 1 (fun _ => N))).symm.toLinearEquiv
  have h := e.finrank_map_eq (degreePiece K 1 (fun _ => N) (fun _ => d))
  change Module.finrank K (quotientPiece K 1 (fun _ => N) ⊥ (fun _ => d)) = _
  exact h.trans (degreePiece_finrank K N d)

end PhilipponMultiplicity.ProjectiveAmbientDegree

end
end

section
-- Reused implementation: Solutions.PhilipponHypersurfaceHilbert

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
namespace Hilbert

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

private theorem component_mul_homogeneous
    {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (Q : M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (D + d)
      (P * Q) =
    P * weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d Q := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hP' : P ∈ weightedHomogeneousSubmodule K w D :=
    (M.degreePiece_iff P D).mpr hP
  have hh := DirectSum.coe_decompose_mul_add_of_left_mem
    (weightedHomogeneousSubmodule K w) (b := Q) (j := d) hP'
  change ((MvPolynomial.decompose' K w (P * Q)) (D + d) : M.CoordinateRing) =
    P * ((MvPolynomial.decompose' K w Q) d : M.CoordinateRing) at hh
  simpa only [MvPolynomial.decompose'_apply] using hh

instance quotientPiece_finite (I : Ideal M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    Module.Finite K (quotientPiece K M.factorCount M.ambientDimension I d) := by
  unfold quotientPiece
  infer_instance

theorem hilbertFunction_hypersurface_add
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P)) (d : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension
        (I ⊔ Ideal.span {P}) (D + d) +
      hilbertFunction K M.factorCount M.ambientDimension I d =
    hilbertFunction K M.factorCount M.ambientDimension I (D + d) := by
  classical
  let J := I ⊔ Ideal.span {P}
  let W := fun n => quotientPiece K M.factorCount M.ambientDimension I n
  let V := quotientPiece K M.factorCount M.ambientDimension J (D + d)
  let f : W d →ₗ[K] W (D + d) :=
    ((LinearMap.mulLeft K (Ideal.Quotient.mk I P)).domRestrict (W d)).codRestrict
      (W (D + d)) (by
        rintro ⟨x, Q, hQ, rfl⟩
        refine ⟨P * Q, ?_, ?_⟩
        · exact ((M.degreePiece_iff P D).mpr hP :
            P.IsWeightedHomogeneous (blockWeight M.factorCount M.ambientDimension) D).mul hQ
        · exact map_mul (Ideal.Quotient.mk I) P Q)
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact hregular.left (congrArg Subtype.val hxy)
  let q : (M.CoordinateRing ⧸ I) →ₐ[K] (M.CoordinateRing ⧸ J) :=
    Ideal.quotientMapₐ J (AlgHom.id K M.CoordinateRing) (by
      intro x hx
      exact (le_sup_left : I ≤ J) hx)
  let g : W (D + d) →ₗ[K] V :=
    (q.toLinearMap.domRestrict (W (D + d))).codRestrict V (by
      rintro ⟨x, Q, hQ, rfl⟩
      exact ⟨Q, hQ, rfl⟩)
  have hsurj : Function.Surjective g := by
    rintro ⟨x, Q, hQ, rfl⟩
    exact ⟨⟨Ideal.Quotient.mk I Q, ⟨Q, hQ, rfl⟩⟩, rfl⟩
  have hker : LinearMap.ker g = LinearMap.range f := by
    ext x
    constructor
    · intro hx
      obtain ⟨Q, hQ, hQx⟩ := x.property
      have hQJ : Q ∈ J := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hx' := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
        change q x.val = 0 at hx'
        rw [← hQx] at hx'
        exact hx'
      obtain ⟨a, b, hb, heq⟩ :=
        Ideal.mem_span_singleton_sup.mp (show Q ∈ Ideal.span {P} ⊔ I by
          simpa only [sup_comm] using hQJ)
      let a' := weightedHomogeneousComponent
        (blockWeight M.factorCount M.ambientDimension) d a
      let b' := weightedHomogeneousComponent
        (blockWeight M.factorCount M.ambientDimension) (D + d) b
      have hb' : b' ∈ I := hI b hb (D + d)
      have hproj : P * a' + b' = Q := by
        have hh := congrArg
          (weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (D + d)) heq
        rw [map_add, mul_comm a P, component_mul_homogeneous M hP a d,
          IsWeightedHomogeneous.weightedHomogeneousComponent_same hQ] at hh
        exact hh
      refine ⟨⟨Ideal.Quotient.mk I a', ⟨a', ?_, rfl⟩⟩, ?_⟩
      · exact weightedHomogeneousComponent_mem _ _ _
      · apply Subtype.ext
        change Ideal.Quotient.mk I P * Ideal.Quotient.mk I a' = x.val
        change Ideal.Quotient.mk I Q = x.val at hQx
        rw [← hQx, ← hproj, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb', add_zero,
          map_mul]
    · rintro ⟨y, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change q (Ideal.Quotient.mk I P * y.val) = 0
      rw [map_mul]
      have hP0 : q (Ideal.Quotient.mk I P) = 0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact (le_sup_right : Ideal.span {P} ≤ J) (Ideal.subset_span (Set.mem_singleton P))
      rw [hP0, zero_mul]
  have hdim := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
    LinearMap.finrank_range_of_inj hinj] at hdim
  exact hdim

theorem IsHilbertPolynomial.hypersurface
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P))
    (F : MvPolynomial M.FactorIndex ℚ)
    (hF : IsHilbertPolynomial K M.factorCount M.ambientDimension I F) :
    IsHilbertPolynomial K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P})
      (F - aeval (fun i => X i - C (D i : ℚ)) F) := by
  obtain ⟨b, hb⟩ := hF
  refine ⟨D + b, fun n hn => ?_⟩
  have hDn : ∀ i, D i ≤ n i := fun i => (Nat.le_add_right _ _).trans (hn i)
  have hbn : ∀ i, b i ≤ n i := fun i => (Nat.le_add_left _ _).trans (hn i)
  have hbsub : ∀ i, b i ≤ n i - D i := by
    intro i
    have := hn i
    change D i + b i ≤ n i at this
    omega
  have hnsub : D + (n - D) = n := by
    funext i
    exact Nat.add_sub_of_le (hDn i)
  have heval : eval (fun i => (n i : ℚ)) (aeval (fun i => X i - C (D i : ℚ)) F) =
      eval (fun i => (((n - D) i : ℕ) : ℚ)) F := by
    have hc : (fun i => ((n i : ℚ) - D i)) = (fun i => (((n - D) i : ℕ) : ℚ)) := by
      funext i
      simp [Nat.cast_sub (hDn i)]
    clear hb
    induction F using MvPolynomial.induction_on with
    | C a => simp
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F i hF =>
        simp only [map_mul, hF, aeval_X, map_sub, eval_X, eval_C]
        rw [congrFun hc i]
  rw [map_sub, heval, hb n hbn, hb (n - D) hbsub]
  have hdim := hilbertFunction_hypersurface_add M I hI P D hP hregular (n - D)
  rw [hnsub] at hdim
  exact_mod_cast (show
    (hilbertFunction K M.factorCount M.ambientDimension I n : ℚ) -
      hilbertFunction K M.factorCount M.ambientDimension I (n - D) =
      hilbertFunction K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) n by
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) hdim
    push_cast at hcast
    linarith)

end Hilbert
end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponOrdinaryHilbertGrowth

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (N : ℕ)

theorem ordinary_hilbertFunction_zero_succ
    (I : Ideal (projectiveSpace K N).CoordinateRing) (m : ℕ)
    (hz : hilbertFunction K 1 (fun _ => N) I (fun _ => m) = 0) :
    hilbertFunction K 1 (fun _ => N) I (fun _ => m + 1) = 0 := by
  classical
  let M := projectiveSpace K N
  have hmem : ∀ P, M.IsHomogeneous P (fun _ => m + 1) → P ∈ I := by
    intro P hP
    rw [P.as_sum]
    apply I.sum_mem
    intro e he
    have hsum := hP e he (0 : Fin 1)
    change (∑ j : Fin (N + 1), e ⟨(0 : Fin 1), j⟩) = m + 1 at hsum
    obtain ⟨j, hj⟩ : ∃ j : Fin (N + 1), 0 < e ⟨(0 : Fin 1), j⟩ := by
      by_contra! h
      have hs : ∑ j : Fin (N + 1), e ⟨(0 : Fin 1), j⟩ = 0 :=
        Finset.sum_eq_zero fun j _ => Nat.eq_zero_of_le_zero (h j)
      omega
    let v : M.Variable := ⟨(0 : Fin 1), j⟩
    let a : M.Variable →₀ ℕ := e - Finsupp.single v 1
    have heq : a + Finsupp.single v 1 = e :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hj)
    have ha : Finsupp.weight (blockWeight 1 (fun _ => N)) a = fun _ => m := by
      have hw : Finsupp.weight (blockWeight 1 (fun _ => N)) e = fun _ => m + 1 :=
        ((M.degreePiece_iff P _).mpr hP) (mem_support_iff.mp he)
      rw [← heq, map_add] at hw
      funext i
      have hi := congrFun hw i
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [Pi.add_apply, Finsupp.weight_single, one_nsmul] at hi
      change Finsupp.weight (blockWeight 1 (fun _ => N)) a (0 : Fin 1) + 1 = m + 1 at hi
      omega
    have hm : monomial a (coeff e P) ∈ I :=
      homogeneous_mem_of_hilbertFunction_zero M I (fun _ => m) hz _
        ((M.degreePiece_iff _ _).mp (isWeightedHomogeneous_monomial _ _ _ ha))
    have hmul := I.mul_mem_left (X v) hm
    rw [X, monomial_mul, one_mul, add_comm (Finsupp.single v 1) a, heq] at hmul
    exact hmul
  have hbot : quotientPiece K M.factorCount M.ambientDimension I (fun _ => m + 1) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨P, hP, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem P ((M.degreePiece_iff _ _).mp hP))
  change Module.finrank K (quotientPiece K M.factorCount M.ambientDimension I
    (fun _ => m + 1)) = 0
  rw [hbot, finrank_bot]

theorem ordinary_hilbertFunction_zero_of_le
    (I : Ideal (projectiveSpace K N).CoordinateRing) {m t : ℕ} (hmt : m ≤ t)
    (hz : hilbertFunction K 1 (fun _ => N) I (fun _ => m) = 0) :
    hilbertFunction K 1 (fun _ => N) I (fun _ => t) = 0 := by
  induction t, hmt using Nat.le_induction with
  | base => exact hz
  | succ t hmt ih => exact ordinary_hilbertFunction_zero_succ N I t ih

theorem ordinary_hilbertFunction_zero_degree
    (I : Ideal (projectiveSpace K N).CoordinateRing) (hne : I ≠ ⊤) :
    hilbertFunction K 1 (fun _ => N) I (fun _ => 0) = 1 := by
  have hup : hilbertFunction K 1 (fun _ => N) I (fun _ => 0) ≤ 1 := by
    have h := hilbertFunction_antitone (projectiveSpace K N) ⊥ I bot_le (fun _ => 0)
    change hilbertFunction K 1 (fun _ => N) I (fun _ => 0) ≤
      hilbertFunction K 1 (fun _ => N) ⊥ (fun _ => 0) at h
    simpa only [ProjectiveAmbientDegree.hilbertFunction_bot, zero_add, Nat.choose_self] using h
  have hpos : hilbertFunction K 1 (fun _ => N) I (fun _ => 0) ≠ 0 := by
    intro hz
    apply hne
    apply (Ideal.eq_top_iff_one I).mpr
    apply homogeneous_mem_of_hilbertFunction_zero (projectiveSpace K N) I _ hz 1
    intro e he i
    simp only [support_one, Finset.mem_singleton] at he
    subst e
    simp
  omega

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponRegularCutDegree

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem regular_cut_degreeValue_of_dimension (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P))
    (hdim : idealDimension M (I ⊔ Ideal.span {P}) + 1 = idealDimension M I) :
    idealDegreeValue M (I ⊔ Ideal.span {P}) D = idealDegreeValue M I D := by
  classical
  let F := hilbertPolynomial K M.factorCount M.ambientDimension I
  let a := F.totalDegree
  let Q := F - FiniteDifference.shift (fun i => (D i : ℚ)) F
  have ha : 0 < a := by change 0 < idealDimension M I; omega
  have hpoly : hilbertPolynomial K M.factorCount M.ambientDimension
      (I ⊔ Ideal.span {P}) = Q :=
    hilbertPolynomial_eq_of_isHilbertPolynomial _ _ _ _
      (IsHilbertPolynomial.hypersurface M I hI P D hP hregular F
        (hilbertPolynomial_spec _ _ _ _ (multigraded_hilbert_polynomial_exists K M I hI)))
  have hdegree : Q.totalDegree = a - 1 := by
    change (hilbertPolynomial K M.factorCount M.ambientDimension
      (I ⊔ Ideal.span {P})).totalDegree + 1 = a at hdim
    rw [hpoly] at hdim
    omega
  have htop := (FiniteDifference.top_difference (fun i => (D i : ℚ)) F a ha le_rfl).2
  unfold idealDegreeValue degreeValue degreeForm
  rw [hpoly]
  change eval _ ((Q.totalDegree.factorial : ℚ) • homogeneousComponent Q.totalDegree Q) =
    eval _ ((a.factorial : ℚ) • homogeneousComponent a F)
  rw [hdegree, htop, MvPolynomial.smul_eq_C_mul, map_mul, eval_C,
    FiniteDifference.eval_deriv_self _ _ _ (homogeneousComponent_isHomogeneous _ _),
    MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
  have haeq : a = (a - 1) + 1 := by omega
  have hfac : ((a - 1).factorial : ℚ) * (a : ℚ) = (a.factorial : ℚ) := by
    have hh := Nat.factorial_succ (a - 1)
    rw [← haeq] at hh
    exact_mod_cast (Nat.mul_comm _ _).trans hh.symm
  rw [← mul_assoc, hfac]

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

end PhilipponMultiplicity.SectionThreeSupport

end
end

section
-- Reused implementation: Solutions.PhilipponOrdinaryHilbertCut

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (N : ℕ)

theorem ordinary_regular_linear_recurrence
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)
    (L : (projectiveSpace K N).CoordinateRing)
    (hL : (projectiveSpace K N).IsHomogeneous L (fun _ => 1))
    (hreg : IsRegular (Ideal.Quotient.mk I L)) (m : ℕ) :
    hilbertFunction K 1 (fun _ => N) (I ⊔ Ideal.span {L}) (fun _ => m + 1) +
      hilbertFunction K 1 (fun _ => N) I (fun _ => m) =
      hilbertFunction K 1 (fun _ => N) I (fun _ => m + 1) := by
  have h := hilbertFunction_hypersurface_add (projectiveSpace K N) I hI L
    (fun _ => 1) hL hreg (fun _ => m)
  simpa only [Pi.add_def, Nat.add_comm, projectiveSpace] using h

theorem ordinary_regular_linear_sum
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)
    (L : (projectiveSpace K N).CoordinateRing)
    (hL : (projectiveSpace K N).IsHomogeneous L (fun _ => 1))
    (hreg : IsRegular (Ideal.Quotient.mk I L))
    (hproper : I ⊔ Ideal.span {L} ≠ ⊤) (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
      hilbertFunction K 1 (fun _ => N) (I ⊔ Ideal.span {L}) (fun _ => j)) =
        hilbertFunction K 1 (fun _ => N) I (fun _ => m) := by
  have hIproper : I ≠ ⊤ := fun h => hproper (by simp [h])
  induction m with
  | zero =>
    simp only [Nat.zero_add, Finset.sum_range_one]
    exact (ordinary_hilbertFunction_zero_degree N (I ⊔ Ideal.span {L}) hproper).trans
      (ordinary_hilbertFunction_zero_degree N I hIproper).symm
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, add_comm]
    exact ordinary_regular_linear_recurrence N I hI L hL hreg m

theorem ordinary_difference_degree (F : MvPolynomial (Fin 1) ℚ) (r : ℕ)
    (hdeg : F.totalDegree = r + 1) :
    (F - FiniteDifference.shift (fun _ => 1) F).totalDegree = r ∧
      F - FiniteDifference.shift (fun _ => 1) F ≠ 0 := by
  classical
  have hF : F ≠ 0 := by intro hz; simp [hz] at hdeg
  obtain ⟨e, he, hedeg⟩ := Finset.exists_mem_eq_sup F.support
    (support_nonempty.mpr hF) Finsupp.degree
  have heq : e = Finsupp.single (0 : Fin 1) (r + 1) := by
    apply Finsupp.ext
    intro i
    fin_cases i
    have h : F.totalDegree = e.degree := hedeg
    simpa [ProductDegree.degree_fin_one, Finsupp.single_apply, hdeg] using h.symm
  have hlead : coeff (Finsupp.single (0 : Fin 1) (r + 1)) F ≠ 0 := by
    rw [← heq]
    exact mem_support_iff.mp he
  have ht := FiniteDifference.top_difference (fun _ : Fin 1 => 1) F (r + 1)
    (by omega) hdeg.le
  have hc := congrArg (coeff (Finsupp.single (0 : Fin 1) r)) ht.2
  simp only [Nat.add_sub_cancel, coeff_homogeneousComponent, Finsupp.degree_single,
    ite_true, FiniteDifference.coeff_deriv, Fin.sum_univ_one, one_mul,
    Finsupp.single_eq_same, ← Finsupp.single_add] at hc
  have hcne : coeff (Finsupp.single (0 : Fin 1) r)
      (F - FiniteDifference.shift (fun _ => 1) F) ≠ 0 := by
    rw [hc]
    exact mul_ne_zero hlead (by positivity)
  refine ⟨le_antisymm (by simpa using ht.1) ?_, ?_⟩
  · have hle : (Finsupp.single (0 : Fin 1) r).degree ≤
        (F - FiniteDifference.shift (fun _ => 1) F).totalDegree :=
      le_totalDegree (mem_support_iff.mpr hcne)
    rw [Finsupp.degree_single] at hle
    exact hle
  · intro hz
    exact hcne (by rw [hz, coeff_zero])

theorem ordinary_regular_linear_cut_data
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)
    (L : (projectiveSpace K N).CoordinateRing)
    (hL : (projectiveSpace K N).IsHomogeneous L (fun _ => 1))
    (hreg : IsRegular (Ideal.Quotient.mk I L))
    (r : ℕ) (hdim : idealDimension (projectiveSpace K N) I = r + 1) :
    idealDimension (projectiveSpace K N) (I ⊔ Ideal.span {L}) = r ∧
      idealDegreeValue (projectiveSpace K N) (I ⊔ Ideal.span {L}) (fun _ => 1) =
        idealDegreeValue (projectiveSpace K N) I (fun _ => 1) ∧
      hilbertPolynomial K 1 (fun _ => N) (I ⊔ Ideal.span {L}) ≠ 0 := by
  let M := projectiveSpace K N
  let F := hilbertPolynomial K 1 (fun _ => N) I
  have hpoly : hilbertPolynomial K 1 (fun _ => N) (I ⊔ Ideal.span {L}) =
      F - FiniteDifference.shift (fun _ => 1) F := by
    apply hilbertPolynomial_eq_of_isHilbertPolynomial
    exact IsHilbertPolynomial.hypersurface M I hI L (fun _ => 1) hL hreg F
      (hilbertPolynomial_spec K 1 (fun _ => N) I
        (multigraded_hilbert_polynomial_exists K M I hI))
  obtain ⟨hdegree, hne⟩ := ordinary_difference_degree F r hdim
  have hcutdim : idealDimension M (I ⊔ Ideal.span {L}) = r := by
    change (hilbertPolynomial K 1 (fun _ => N) (I ⊔ Ideal.span {L})).totalDegree = r
    rw [hpoly, hdegree]
  refine ⟨hcutdim, ?_, by rwa [hpoly]⟩
  exact regular_cut_degreeValue_of_dimension M I hI L (fun _ => 1) hL hreg
    (by rw [hcutdim]; exact hdim.symm)

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponNesterenkoNumerics

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity.HilbertNumerics

private theorem sum_range_cast_real (d : ℕ) :
    (∑ j ∈ Finset.range d, (j : ℝ)) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_shifted_choose (a d n : ℕ) :
    (∑ j ∈ Finset.range d, (Nat.choose (a + j + n) n : ℝ)) =
      (Nat.choose (a + d + n) (n + 1) : ℝ) -
        (Nat.choose (a + n) (n + 1) : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show a + (d + 1) + n = (a + d + n) + 1 by omega,
      Nat.choose_succ_succ']
    push_cast
    ring

theorem nesterenko_binomial_lower {d m : ℕ} (hd : 0 < d) (hdm : d ≤ m) (n : ℕ) :
    (d : ℝ) * (m : ℝ) ^ n / ((2 : ℝ) ^ n * (n.factorial : ℝ)) ≤
      (Nat.choose (m + n + 1) (n + 1) : ℝ) -
        (Nat.choose (m - d + n + 1) (n + 1) : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdm' : (d : ℝ) ≤ m := by exact_mod_cast hdm
  let z (j : ℕ) : ℝ := (m : ℝ) - d + j + 2
  have hz (j : ℕ) : 0 ≤ z j := by dsimp [z]; positivity [sub_nonneg.mpr hdm']
  have hsum : (∑ j ∈ Finset.range d, z j) =
      (d : ℝ) * ((m : ℝ) - d + 2) + (d : ℝ) * ((d : ℝ) - 1) / 2 := by
    simp only [z]
    simp_rw [show ∀ j : ℕ, (m : ℝ) - d + j + 2 = ((m : ℝ) - d + 2) + j by
      intro j; ring]
    rw [Finset.sum_add_distrib, sum_range_cast_real]
    simp
    ring
  have hmean : (m : ℝ) / 2 ≤
      ∑ j ∈ Finset.range d, (d : ℝ)⁻¹ * z j := by
    rw [← Finset.mul_sum, hsum]
    apply (mul_le_mul_iff_right₀ hd').mp
    field_simp
    nlinarith
  have hjensen := Real.pow_arith_mean_le_arith_mean_pow (Finset.range d)
    (fun _ => (d : ℝ)⁻¹) z (fun _ _ => (inv_pos.mpr hd').le)
    (by simp [hd'.ne']) (fun j _ => hz j) n
  have hpowers : (m : ℝ) ^ n / (2 : ℝ) ^ n ≤
      (d : ℝ)⁻¹ * ∑ j ∈ Finset.range d, z j ^ n := by
    rw [← div_pow, Finset.mul_sum]
    exact (pow_le_pow_left₀ (by positivity) hmean n).trans hjensen
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hterm (j : ℕ) :
      z j ^ n ≤ (n.factorial : ℝ) * (Nat.choose (m - d + 1 + j + n) n : ℝ) := by
    have h := (Nat.pow_le_choose (α := ℝ) n (m - d + 1 + j + n))
    rw [show m - d + 1 + j + n + 1 - n = m - d + j + 2 by omega] at h
    have heq : (m - d + j + 2 : ℕ) = (m : ℝ) - d + j + 2 := by
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hdm]
      norm_num
    rw [heq] at h
    exact (div_le_iff₀' hfac).mp h
  have hterms := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range d) => hterm j)
  rw [← Finset.mul_sum] at hterms
  have hbound : (d : ℝ) * (m : ℝ) ^ n / ((2 : ℝ) ^ n * (n.factorial : ℝ)) ≤
      ∑ j ∈ Finset.range d, (Nat.choose (m - d + 1 + j + n) n : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_left hpowers hd'.le
    rw [← mul_assoc, mul_inv_cancel₀ hd'.ne', one_mul] at h₁
    have h₂ := h₁.trans hterms
    calc
      _ = ((d : ℝ) * ((m : ℝ) ^ n / (2 : ℝ) ^ n)) / (n.factorial : ℝ) := by
        ring
      _ ≤ _ := (div_le_iff₀' hfac).mpr h₂
  rw [sum_shifted_choose] at hbound
  convert hbound using 1 <;> congr 3 <;> omega

theorem product_lower_of_binomial_bounds {ι : Type*} [Fintype ι]
    (d m n : ι → ℕ) (hd : ∀ i, 0 < d i) (hdm : ∀ i, d i ≤ m i)
    (h : ι → ℝ)
    (hbound : ∀ i,
      (Nat.choose (m i + n i + 1) (n i + 1) : ℝ) -
        (Nat.choose (m i - d i + n i + 1) (n i + 1) : ℝ) ≤ h i) :
    ((∏ i, (d i : ℝ)) * ∏ i, (m i : ℝ) ^ n i) /
        ((2 : ℝ) ^ (∑ i, n i) * ∏ i, ((n i).factorial : ℝ)) ≤
      ∏ i, h i := by
  classical
  have hprod := Finset.prod_le_prod
    (s := (Finset.univ : Finset ι))
    (f := fun i => (d i : ℝ) * (m i : ℝ) ^ n i /
      ((2 : ℝ) ^ n i * ((n i).factorial : ℝ)))
    (g := h) (fun _ _ => by positivity)
    (fun i _ => (nesterenko_binomial_lower (hd i) (hdm i) (n i)).trans (hbound i))
  simpa only [Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum] using hprod

end PhilipponMultiplicity.HilbertNumerics

end

section
-- Reused implementation: Solutions.PhilipponHilbertLowerSequence

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity.HilbertNumerics

def lowerSequence (δ r m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range δ, if j ≤ m then (m - j + r).choose r else 0

theorem lowerSequence_dim_zero (δ m : ℕ) : lowerSequence δ 0 m = min δ (m + 1) := by
  simp only [lowerSequence, Nat.choose_zero_right]
  have hf : (Finset.range δ).filter (fun j => j ≤ m) = Finset.range (min δ (m + 1)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    omega
  rw [← Finset.sum_filter, hf]
  simp

private theorem sum_truncated_choose (r m j : ℕ) :
    (∑ k ∈ Finset.range (m + 1), if j ≤ k then (k - j + r).choose r else 0) =
      if j ≤ m then (m - j + r + 1).choose (r + 1) else 0 := by
  induction m with
  | zero =>
    by_cases hj : j = 0
    · simp [hj]
    · simp [hj]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : j ≤ m
    · rw [if_pos h, if_pos (by omega : j ≤ m + 1), if_pos (by omega : j ≤ m + 1)]
      rw [show m + 1 - j + r = m - j + r + 1 by omega]
      simpa only [add_comm] using (Nat.choose_succ_succ' (m - j + r + 1) r).symm
    · by_cases hj : j = m + 1
      · subst j
        simp
      · have hj' : ¬ j ≤ m + 1 := by omega
        simp [h, hj']

theorem lowerSequence_succ (δ r m : ℕ) :
    lowerSequence δ (r + 1) m = ∑ k ∈ Finset.range (m + 1), lowerSequence δ r k := by
  unfold lowerSequence
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Nat.add_assoc] using (sum_truncated_choose r m j).symm

theorem lowerSequence_eq_binomial_real (δ r m : ℕ) (hδm : δ ≤ m) :
    (lowerSequence δ r m : ℝ) =
      (Nat.choose (m + r + 1) (r + 1) : ℝ) -
        (Nat.choose (m - δ + r + 1) (r + 1) : ℝ) := by
  have hs : lowerSequence δ r m =
      ∑ j ∈ Finset.range δ, (m - j + r).choose r := by
    unfold lowerSequence
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos (by have := Finset.mem_range.mp hj; omega)]
  rw [hs, Nat.cast_sum]
  rw [← Finset.sum_range_reflect (fun j => ((m - j + r).choose r : ℝ)) δ]
  have heq : (∑ j ∈ Finset.range δ, ((m - (δ - 1 - j) + r).choose r : ℝ)) =
      ∑ j ∈ Finset.range δ, ((m - δ + 1 + j + r).choose r : ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    have := Finset.mem_range.mp hj
    congr 2
    omega
  rw [heq, sum_shifted_choose]
  rw [show m - δ + 1 + δ + r = m + r + 1 by omega,
    show m - δ + 1 + r = m - δ + r + 1 by omega]

theorem min_le_of_no_early_plateau (h : ℕ → ℕ) (δ : ℕ)
    (hzero : 1 ≤ h 0) (hmono : Monotone h)
    (hevent : ∃ B, ∀ m, B ≤ m → h m = δ)
    (hplateau : ∀ m, h (m + 1) = h m → ∀ t, m ≤ t → h t = h m) :
    ∀ m, min δ (m + 1) ≤ h m := by
  have hup (m : ℕ) : h m ≤ δ := by
    obtain ⟨B, hB⟩ := hevent
    exact (hmono (le_max_left m B)).trans_eq (hB _ (le_max_right m B))
  intro m
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hsat : h m = δ
    · have hm : h m ≤ h (m + 1) := hmono (Nat.le_succ m)
      omega
    · have hstrict : h m < h (m + 1) := by
        by_contra! hle
        have heq : h (m + 1) = h m := le_antisymm hle (hmono (Nat.le_succ m))
        obtain ⟨B, hB⟩ := hevent
        have hh := hplateau m heq (max m B) (le_max_left m B)
        rw [hB _ (le_max_right m B)] at hh
        exact hsat hh.symm
      have := hup m
      omega

end PhilipponMultiplicity.HilbertNumerics

end

section
-- Reused implementation: Solutions.PhilipponOrdinaryHilbertLower

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree HilbertNumerics
variable {K : Type*} [Field K] (N : ℕ)

theorem ordinary_dim_zero_lower
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)
    (hpoly : hilbertPolynomial K 1 (fun _ => N) I ≠ 0)
    (L : (projectiveSpace K N).CoordinateRing)
    (hL : (projectiveSpace K N).IsHomogeneous L (fun _ => 1))
    (hreg : IsRegular (Ideal.Quotient.mk I L))
    (δ : ℕ) (hdegree : idealDegreeValue (projectiveSpace K N) I (fun _ => 1) = δ)
    (hdim : idealDimension (projectiveSpace K N) I = 0) (m : ℕ) :
    min δ (m + 1) ≤ hilbertFunction K 1 (fun _ => N) I (fun _ => m) := by
  let M := projectiveSpace K N
  let h (t : ℕ) := hilbertFunction K 1 (fun _ => N) I (fun _ => t)
  let g (t : ℕ) := hilbertFunction K 1 (fun _ => N) (I ⊔ Ideal.span {L}) (fun _ => t)
  have hrec (t : ℕ) : g (t + 1) + h t = h (t + 1) :=
    ordinary_regular_linear_recurrence N I hI L hL hreg t
  have hproper : I ≠ ⊤ := by
    intro heq
    apply hpoly
    rw [heq]
    exact hilbertPolynomial_top M
  have hzero : h 0 = 1 := ordinary_hilbertFunction_zero_degree N I hproper
  have hmono : Monotone h := monotone_nat_of_le_succ fun t => by have := hrec t; omega
  have hevent : ∃ B, ∀ t, B ≤ t → h t = δ := by
    let F := hilbertPolynomial K 1 (fun _ => N) I
    have hF : F = C (coeff 0 F) := totalDegree_eq_zero_iff_eq_C.mp hdim
    have hc : coeff 0 F = (δ : ℚ) := by
      have hh := degreeValue_of_constant_hilbertPolynomial M I (coeff 0 F) hF (fun _ => 1)
      exact hh.symm.trans hdegree
    have hspec := hilbertPolynomial_spec K 1 (fun _ => N) I
      (multigraded_hilbert_polynomial_exists K M I hI)
    change IsHilbertPolynomial K 1 (fun _ => N) I F at hspec
    rw [hF, hc] at hspec
    obtain ⟨B, hB⟩ := hspec
    refine ⟨B 0, fun t ht => ?_⟩
    have hh := hB (fun _ => t) (fun i => by fin_cases i; exact ht)
    rw [eval_C] at hh
    exact_mod_cast hh.symm
  apply min_le_of_no_early_plateau h δ hzero.ge hmono hevent ?_ m
  intro t ht u htu
  have hg : g (t + 1) = 0 := by have := hrec t; omega
  induction u, htu using Nat.le_induction with
  | base => rfl
  | succ u htu ih =>
    have hgu : g (u + 1) = 0 := ordinary_hilbertFunction_zero_of_le N
      (I ⊔ Ideal.span {L}) (Nat.succ_le_succ htu) hg
    have hh := hrec u
    omega

theorem ordinary_hilbert_lower [Infinite K]
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)
    (hpoly : hilbertPolynomial K 1 (fun _ => N) I ≠ 0)
    (δ : ℕ) (hdegree : idealDegreeValue (projectiveSpace K N) I (fun _ => 1) = δ)
    (r : ℕ) (hdim : idealDimension (projectiveSpace K N) I = r) (m : ℕ) :
    lowerSequence δ r m ≤ hilbertFunction K 1 (fun _ => N) I (fun _ => m) := by
  induction r generalizing I m with
  | zero =>
    obtain ⟨J, L, hIJ, hJ, hJP, hL, hreg⟩ :=
      exists_regular_linear_reduction (projectiveSpace K N) I hI (0 : Fin 1)
    have hL' : (projectiveSpace K N).IsHomogeneous L (fun _ => 1) := by
      convert hL using 1
      funext i
      fin_cases i
      simp
    have hJdeg : idealDegreeValue (projectiveSpace K N) J (fun _ => 1) = δ := by
      unfold idealDegreeValue degreeValue degreeForm
      rw [hJP]
      exact hdegree
    have hJdim : idealDimension (projectiveSpace K N) J = 0 := by
      unfold idealDimension
      rw [hJP]
      exact hdim
    rw [lowerSequence_dim_zero]
    exact (ordinary_dim_zero_lower N J hJ (fun hz => hpoly (hJP.symm.trans hz)) L hL' hreg δ hJdeg hJdim m).trans
      (hilbertFunction_antitone (projectiveSpace K N) I J hIJ (fun _ => m))
  | succ r ih =>
    obtain ⟨J, L, hIJ, hJ, hJP, hL, hreg⟩ :=
      exists_regular_linear_reduction (projectiveSpace K N) I hI (0 : Fin 1)
    have hL' : (projectiveSpace K N).IsHomogeneous L (fun _ => 1) := by
      convert hL using 1
      funext i
      fin_cases i
      simp
    have hJdeg : idealDegreeValue (projectiveSpace K N) J (fun _ => 1) = δ := by
      unfold idealDegreeValue degreeValue degreeForm
      rw [hJP]
      exact hdegree
    have hJdim : idealDimension (projectiveSpace K N) J = r + 1 := by
      unfold idealDimension
      rw [hJP]
      exact hdim
    obtain ⟨hcutdim, hcutdeg, hcutpoly⟩ :=
      ordinary_regular_linear_cut_data N J hJ L hL' hreg r hJdim
    have hcut : IsMultihomogeneousIdeal (projectiveSpace K N) (J ⊔ Ideal.span {L}) :=
      homogeneous_sup_span (projectiveSpace K N) J hJ L (fun _ => 1) hL'
    have hcutproper : J ⊔ Ideal.span {L} ≠ ⊤ := by
      intro heq
      apply hcutpoly
      exact (congrArg (fun A : Ideal (projectiveSpace K N).CoordinateRing =>
        hilbertPolynomial K 1 (fun _ => N) A) heq).trans
          (hilbertPolynomial_top (projectiveSpace K N))
    calc
      lowerSequence δ (r + 1) m = ∑ k ∈ Finset.range (m + 1), lowerSequence δ r k :=
        lowerSequence_succ δ r m
      _ ≤ ∑ k ∈ Finset.range (m + 1),
          hilbertFunction K 1 (fun _ => N) (J ⊔ Ideal.span {L}) (fun _ => k) :=
        Finset.sum_le_sum fun k _ => ih _ hcut hcutpoly (hcutdeg.trans hJdeg) hcutdim k
      _ = hilbertFunction K 1 (fun _ => N) J (fun _ => m) :=
        ordinary_regular_linear_sum N J hJ L hL' hreg hcutproper m
      _ ≤ hilbertFunction K 1 (fun _ => N) I (fun _ => m) :=
        hilbertFunction_antitone (projectiveSpace K N) I J hIJ (fun _ => m)

theorem ordinary_hilbert_binomial_lower [Infinite K]
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)
    (hpoly : hilbertPolynomial K 1 (fun _ => N) I ≠ 0)
    (δ : ℕ) (hdegree : idealDegreeValue (projectiveSpace K N) I (fun _ => 1) = δ)
    (r : ℕ) (hdim : idealDimension (projectiveSpace K N) I = r)
    (m : ℕ) (hδm : δ ≤ m) :
    (Nat.choose (m + r + 1) (r + 1) : ℝ) -
        (Nat.choose (m - δ + r + 1) (r + 1) : ℝ) ≤
      (hilbertFunction K 1 (fun _ => N) I (fun _ => m) : ℝ) := by
  rw [← lowerSequence_eq_binomial_real δ r m hδm]
  exact_mod_cast ordinary_hilbert_lower N I hI hpoly δ hdegree r hdim m

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponProductHilbertExistence

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertFunction_empty (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal ∅) D = 0 := by
  have h := M.hilbertFunction_eq_sectionSpace (fun x : Empty => isEmptyElim x) D
  have hr : Set.range (fun x : Empty => (isEmptyElim x : M.Point)) = ∅ := by
    ext x
    simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
    rintro ⟨e, _⟩
    exact isEmptyElim e
  have hf : Module.finrank K (M.sectionSpace (fun x : Empty => isEmptyElim x) D) = 0 :=
    Module.finrank_eq_zero_of_subsingleton K _
  rw [hr, hf] at h
  exact h

theorem hilbertPolynomial_empty :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
      (M.vanishingIdeal ∅) = 0 := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, fun D _ => ?_⟩
  rw [M.hilbertFunction_empty]
  simp

theorem hilbertFunction_pos {S : Set M.Point} (hS : S.Nonempty)
    (D : M.FactorIndex → ℕ) :
    0 < Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal S) D := by
  classical
  obtain ⟨x, hx⟩ := hS
  obtain ⟨Q, hQ, hQx⟩ := M.exists_form_nonzero_at x D
  let I := M.vanishingIdeal S
  let W := Hilbert.quotientPiece K M.factorCount M.ambientDimension I D
  let q : W := ⟨Ideal.Quotient.mk I Q,
    ⟨Q, (M.degreePiece_iff Q D).mpr hQ, rfl⟩⟩
  have hq : q ≠ 0 := by
    intro h
    have hz : Ideal.Quotient.mk I Q = 0 := congrArg Subtype.val h
    have hm : Q ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
    exact hQx (M.eval_eq_zero_of_mem_vanishingIdeal hm hx)
  letI : Nontrivial W := nontrivial_of_ne q 0 hq
  letI : Module.Finite K W := by
    dsimp [W, Hilbert.quotientPiece]
    infer_instance
  exact Module.finrank_pos

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
open SectionThree

theorem factor_hilbert_polynomial_exists_of_product
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (hne : ∀ i, (V i).carrier.Nonempty)
    (hprod : ∃ P, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension
      (M.vanishingIdeal (productCarrier M V)) P) (i : M.FactorIndex) :
    ∃ P, Hilbert.IsHilbertPolynomial K 1 (fun _ => M.ambientDimension i)
      ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
        (V i).carrierInSingleFactor) P := by
  classical
  obtain ⟨P, N, hP⟩ := hprod
  let f (j : M.FactorIndex) (n : ℕ) := Hilbert.hilbertFunction K 1
    (fun _ => M.ambientDimension j)
    ((projectiveSpace K (M.ambientDimension j)).vanishingIdeal
      (V j).carrierInSingleFactor) (fun _ => n)
  have hf (j : M.FactorIndex) (n : ℕ) : 0 < f j n := by
    exact (projectiveSpace K (M.ambientDimension j)).hilbertFunction_pos
      ((hne j).image (fun x => fun _ => x)) (fun _ => n)
  let c : ℚ := ∏ j ∈ Finset.univ.erase i, (f j (N j) : ℚ)
  have hc : c ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast (hf j (N j)).ne'
  let zvar (j : M.FactorIndex) : MvPolynomial (Fin 1) ℚ :=
    if j = i then X 0 else C (N j : ℚ)
  refine ⟨C c⁻¹ * eval₂ C zvar P, fun _ => N i, ?_⟩
  intro d hd
  let e := Function.update N i (d 0)
  have he (j : M.FactorIndex) : N j ≤ e j := by
    by_cases hj : j = i
    · subst j
      simpa [e] using hd 0
    · simp [e, hj]
  have hPe := hP e he
  rw [product_projective_hilbert_function] at hPe
  have heval : eval (fun j => (d j : ℚ)) (eval₂ C zvar P) =
      eval (fun j => (e j : ℚ)) P := by
    rw [eval_eval₂]
    congr 1
    · ext r
      simp
    · funext j
      by_cases hj : j = i <;> simp [zvar, e, hj]
  rw [map_mul, eval_C, heval, hPe, Nat.cast_prod]
  change c⁻¹ * (∏ j, (f j (e j) : ℚ)) = _
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (f j (e j) : ℚ)) (Finset.mem_univ i)]
  have herase : (∏ j ∈ Finset.univ.erase i, (f j (e j) : ℚ)) = c := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [e, Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [herase]
  have hd' : d = fun _ => d 0 := funext (fun j => congrArg d (Fin.eq_zero j))
  rw [hd']
  change c⁻¹ * ((f i (e i) : ℚ) * c) = (f i (d 0) : ℚ)
  simp only [e, Function.update_self]
  field_simp

theorem product_projective_hilbert_polynomial (K : Type*) [Field K]
    (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i)) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal (productCarrier M V)) =
      ∏ i, MvPolynomial.rename (fun _ : Fin 1 => i)
        (Hilbert.hilbertPolynomial K 1 (fun _ => M.ambientDimension i)
          ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
            (V i).carrierInSingleFactor)) := by
  classical
  by_cases hne : ∀ i, (V i).carrier.Nonempty
  · by_cases hprod : ∃ P, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal (productCarrier M V)) P
    · exact product_projective_hilbert_polynomial_of_exists K M V
        (factor_hilbert_polynomial_exists_of_product K M V hne hprod)
    · rw [Hilbert.hilbertPolynomial_eq_zero_of_not_exists _ _ _ _ hprod]
      have hn : ¬ ∀ i, ∃ P, Hilbert.IsHilbertPolynomial K 1 (fun _ => M.ambientDimension i)
          ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
            (V i).carrierInSingleFactor) P := by
        intro h
        have hspec (i : M.FactorIndex) := Hilbert.hilbertPolynomial_spec
          K 1 (fun _ => M.ambientDimension i)
          ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
            (V i).carrierInSingleFactor) (h i)
        choose N hN using hspec
        apply hprod
        refine ⟨∏ i, rename (fun _ : Fin 1 => i)
          (Hilbert.hilbertPolynomial K 1 (fun _ => M.ambientDimension i)
            ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
              (V i).carrierInSingleFactor)), fun i => N i 0, ?_⟩
        intro d hd
        rw [map_prod, product_projective_hilbert_function, Nat.cast_prod]
        apply Finset.prod_congr rfl
        intro i _
        rw [eval_rename]
        apply hN i
        intro j
        fin_cases j
        exact hd i
      push Not at hn
      obtain ⟨i, hi⟩ := hn
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [Hilbert.hilbertPolynomial_eq_zero_of_not_exists _ _ _ _ (by simpa using hi), map_zero]
  · push Not at hne
    obtain ⟨i, hi⟩ := hne
    have hiempty : (V i).carrier = ∅ := hi
    have hprodempty : productCarrier M V = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxi := hx i
      rwa [hiempty] at hxi
    have hsingleempty : (V i).carrierInSingleFactor = ∅ := by
      simp [ProjectiveSubvariety.carrierInSingleFactor, hiempty]
    rw [hprodempty, M.hilbertPolynomial_empty]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hsingleempty]
    have hz : Hilbert.hilbertPolynomial K 1 (fun _ => M.ambientDimension i)
        ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal ∅) = 0 :=
      (projectiveSpace K (M.ambientDimension i)).hilbertPolynomial_empty
    rw [hz, map_zero]

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponHilbertRays

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial Filter
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {ι : Type*} [Fintype ι]

def rayPolynomial (F : MvPolynomial ι ℚ) (a E : ι → ℚ) : Polynomial ℚ :=
  eval₂ Polynomial.C (fun i => Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) F

def rayTerm (a E : ι → ℚ) (e : ι →₀ ℕ) (r : ℚ) : Polynomial ℚ :=
  Polynomial.C r * ∏ i, (Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) ^ e i

theorem rayPolynomial_eq_sum (F : MvPolynomial ι ℚ) (a E : ι → ℚ) :
    rayPolynomial F a E = ∑ e ∈ F.support, rayTerm a E e (coeff e F) := by
  classical
  simp only [rayPolynomial,MvPolynomial.eval₂_eq,rayTerm]
  apply Finset.sum_congr rfl
  intro e _
  change Polynomial.C _ * e.prod (fun i n =>
      (Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) ^ n) = _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem rayTerm_degree_and_leadingCoeff (a E : ι → ℚ) (ha : ∀ i, a i ≠ 0)
    (e : ι →₀ ℕ) (r : ℚ) (hr : r ≠ 0) :
    (rayTerm a E e r).natDegree = e.degree ∧
      (rayTerm a E e r).leadingCoeff = r * ∏ i, (a i) ^ e i := by
  classical
  have hn (i : ι) : Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i) ≠ 0 := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_linear (ha i),Polynomial.natDegree_zero] at this
    omega
  constructor
  · rw [rayTerm,Polynomial.natDegree_C_mul hr,
      Polynomial.natDegree_prod Finset.univ _ (fun i _ => pow_ne_zero _ (hn i))]
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_linear (ha _),mul_one]
    change (∑ i, e i) = e.sum (fun _ n => n)
    exact (Finsupp.sum_fintype e (fun _ n => n) (fun _ => rfl)).symm
  · simp only [rayTerm,Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_prod,Polynomial.leadingCoeff_pow]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [Polynomial.leadingCoeff_linear (ha i)]

theorem rayPolynomial_top_coeff (F : MvPolynomial ι ℚ) (a E : ι → ℚ)
    (ha : ∀ i, a i ≠ 0) :
    (rayPolynomial F a E).coeff F.totalDegree =
      eval a (homogeneousComponent F.totalDegree F) := by
  classical
  rw [rayPolynomial_eq_sum,Polynomial.finsetSum_coeff]
  conv_rhs => arg 2; arg 2; rw [F.as_sum]
  rw [map_sum,eval_sum]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨hdeg,hlc⟩ := rayTerm_degree_and_leadingCoeff a E ha e _ (mem_support_iff.mp he)
  rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff e F) rfl)]
  by_cases hd : e.degree = F.totalDegree
  · rw [if_pos hd.symm,← hd,← hdeg,Polynomial.coeff_natDegree,hlc,eval_monomial]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [hdeg]; exact lt_of_le_of_ne (le_totalDegree he) hd)]
    simp [Ne.symm hd]

theorem eval_top_pos (F : MvPolynomial ι ℚ) (hF : F ≠ 0)
    (hpos : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F)
    (a : ι → ℚ) (ha : ∀ i, 0 < a i) :
    0 < eval a (homogeneousComponent F.totalDegree F) := by
  classical
  rw [← rayPolynomial_top_coeff F a 0 (fun i => (ha i).ne'),
    rayPolynomial_eq_sum,Polynomial.finsetSum_coeff]
  have hterm (e : ι →₀ ℕ) (he : e ∈ F.support) :
      (rayTerm a 0 e (coeff e F)).coeff F.totalDegree =
        if e.degree = F.totalDegree then coeff e F * ∏ i, a i ^ e i else 0 := by
    obtain ⟨hdeg,hlc⟩ := rayTerm_degree_and_leadingCoeff a 0 (fun i => (ha i).ne')
      e _ (mem_support_iff.mp he)
    split_ifs with hd
    · rw [← hd,← hdeg,Polynomial.coeff_natDegree,hlc]
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
        rw [hdeg]; exact lt_of_le_of_ne (le_totalDegree he) hd)
  obtain ⟨e,he,hd⟩ := Finset.exists_mem_eq_sup F.support
    (support_nonempty.mpr hF) Finsupp.degree
  change F.totalDegree = e.degree at hd
  apply Finset.sum_pos'
  · intro b hb
    rw [hterm b hb]
    split_ifs with h
    · exact mul_nonneg (hpos b h) (Finset.prod_nonneg fun i _ => pow_nonneg (ha i).le _)
    · exact le_rfl
  · refine ⟨e,he,?_⟩
    rw [hterm e he,if_pos hd.symm]
    exact mul_pos (lt_of_le_of_ne (hpos e hd.symm) (Ne.symm (mem_support_iff.mp he)))
      (Finset.prod_pos fun i _ => pow_pos (ha i) _)

end PhilipponMultiplicity.Hilbert
end
end

section
-- Reused implementation: Solutions.PhilipponShiftedHilbertComparison

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial Filter
noncomputable section

namespace PhilipponMultiplicity.Hilbert

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem vanishing_hilbertPolynomial_ne_zero {S : Set M.Point} (hS : S.Nonempty) :
    hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S) ≠ 0 := by
  obtain ⟨d₀,hd₀⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension
    (M.vanishingIdeal S) (multigraded_hilbert_polynomial_exists K M _
      (vanishingIdeal_multihomogeneous K M S))
  intro hz
  have h := hd₀ d₀ (fun _ => le_rfl)
  rw [hz,map_zero] at h
  have hp : (0 : ℚ) < hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal S) d₀ := by exact_mod_cast M.hilbertFunction_pos hS d₀
  exact hp.ne' h.symm

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponDegreeModelDimension

set_option autoImplicit false
open scoped BigOperators Topology
noncomputable section

namespace HomogeneousExtraction

end HomogeneousExtraction

namespace PhilipponMultiplicity.SectionThree

theorem locusDegreeValue_pos {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    {V : Set M.Point} (hV : V.Nonempty) (D : M.FactorIndex → ℕ)
    (hD : ∀ i, 1 ≤ D i) : 0 < locusDegreeValue M V D := by
  let F := Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal V)
  have htop : ∀ e, e.degree = F.totalDegree → 0 ≤ MvPolynomial.coeff e F := by
    intro e he
    have h := (multigraded_hilbert_polynomial_top_coefficients K M _
      (vanishingIdeal_multihomogeneous K M V)).1 e
    rwa [MvPolynomial.coeff_homogeneousComponent, if_pos he] at h
  have hpos := Hilbert.eval_top_pos F (Hilbert.vanishing_hilbertPolynomial_ne_zero M hV)
    htop (fun i => (D i : ℚ)) (fun i => by exact_mod_cast (hD i))
  unfold locusDegreeValue idealDegreeValue Hilbert.degreeValue Hilbert.degreeForm
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
  exact mul_pos (by exact_mod_cast Nat.factorial_pos F.totalDegree) hpos

end PhilipponMultiplicity.SectionThree

namespace PhilipponMultiplicity.DegreeModelDimension

variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)
  (τ : G.Point → (groupProjectiveClosure G ≃ groupProjectiveClosure G))
  (hzero : τ 0 = Equiv.refl _)
  (hadd : ∀ g h, τ (g+h) = (τ h).trans (τ g))

include hzero hadd

omit hzero hadd

end PhilipponMultiplicity.DegreeModelDimension
end
end

section
-- Reused implementation: Solutions.PhilipponProjectiveHilbertLower

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (N : ℕ)

theorem ordinary_degree_integral (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I) :
    ∃ δ : ℕ, idealDegreeValue (projectiveSpace K N) I (fun _ => 1) = δ := by
  classical
  let M := projectiveSpace K N
  let F := hilbertPolynomial K 1 (fun _ => N) I
  let e : Fin 1 →₀ ℕ := Finsupp.single 0 F.totalDegree
  obtain ⟨δ, hδ⟩ := idealMixedDegree_integral M I hI (fun _ => F.totalDegree)
  have he : Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => F.totalDegree) = e := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp [e]
  have hh : idealDegreeValue M I (fun _ => 1) =
      (F.totalDegree.factorial : ℚ) * coeff e F := by
    change eval (fun _ => (1 : ℚ)) ((F.totalDegree.factorial : ℚ) •
      homogeneousComponent F.totalDegree F) = _
    rw [smul_eq_C_mul, map_mul, eval_C, ProductDegree.eval_top_fin_one]
    simp [e]
  change (if (∑ _ : Fin 1, F.totalDegree) = F.totalDegree then
    coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => F.totalDegree)) F *
      (∏ _ : Fin 1, (F.totalDegree.factorial : ℚ)) else 0) = (δ : ℚ) at hδ
  refine ⟨δ, hh.trans ?_⟩
  simpa [he, mul_comm] using hδ

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.SectionThree.ProjectiveSubvariety
variable {K : Type*} [Field K] {N : ℕ}

theorem exists_positive_degree_nat (V : ProjectiveSubvariety K N)
    (hne : V.carrier.Nonempty) : ∃ δ : ℕ, 0 < δ ∧ V.degree = δ := by
  obtain ⟨δ, hδ⟩ := Hilbert.ordinary_degree_integral N
    ((projectiveSpace K N).vanishingIdeal V.carrierInSingleFactor)
    (vanishingIdeal_multihomogeneous K _ _)
  have hpos : 0 < V.degree := locusDegreeValue_pos (projectiveSpace K N)
    (hne.image (fun x => fun _ => x)) (fun _ => 1) (fun _ => le_rfl)
  refine ⟨δ, ?_, hδ⟩
  change V.degree = (δ : ℚ) at hδ
  rw [hδ] at hpos
  exact_mod_cast hpos

theorem hilbert_binomial_lower [Infinite K] (V : ProjectiveSubvariety K N)
    (hne : V.carrier.Nonempty) (δ m : ℕ) (hδ : V.degree = δ) (hδm : δ ≤ m) :
    (Nat.choose (m + V.dimension + 1) (V.dimension + 1) : ℝ) -
        (Nat.choose (m - δ + V.dimension + 1) (V.dimension + 1) : ℝ) ≤
      (Hilbert.hilbertFunction K 1 (fun _ => N)
        ((projectiveSpace K N).vanishingIdeal V.carrierInSingleFactor) (fun _ => m) : ℝ) :=
  Hilbert.ordinary_hilbert_binomial_lower N _ (vanishingIdeal_multihomogeneous K _ _)
    (Hilbert.vanishing_hilbertPolynomial_ne_zero (projectiveSpace K N)
      (show V.carrierInSingleFactor.Nonempty from hne.image (fun x => fun _ => x)))
    δ hδ V.dimension rfl m hδm

end PhilipponMultiplicity.SectionThree.ProjectiveSubvariety

end
end

section
-- Reused implementation: Solutions.PhilipponSectionFiveChain

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem MultiProjectiveSpace.hilbertPolynomial_ne_zero_of_nonempty
    (M : MultiProjectiveSpace K) (S : Set M.Point) (hne : S.Nonempty) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S) ≠ 0 := by
  intro hz
  obtain ⟨b,hb⟩ := Hilbert.hilbertPolynomial_spec K M.factorCount M.ambientDimension
    (M.vanishingIdeal S) (multigraded_hilbert_polynomial_exists K M _
      (vanishingIdeal_multihomogeneous K M S))
  have heq := hb b (fun _ => le_rfl)
  rw [hz,map_zero] at heq
  have hzero : Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal S) b = 0 := by exact_mod_cast heq.symm
  exact (Nat.ne_of_gt (M.hilbertFunction_pos hne b)) hzero

theorem EmbeddedGroupProduct.varietyDimension_univ (G : EmbeddedGroupProduct K) :
    varietyDimension G Set.univ = G.dimension := by
  classical
  let V (i : G.FactorIndex) : SectionThree.ProjectiveSubvariety K (G.ambient.ambientDimension i) :=
    ⟨(G.factor i).carrier,(G.factor i).locallyClosed⟩
  have heq : G.embedding '' Set.univ = SectionThree.productCarrier G.ambient V := by
    ext x
    constructor
    · rintro ⟨y,_,rfl⟩ i
      exact (y i).property
    · intro hx
      exact ⟨(fun i => ⟨x i,hx i⟩),Set.mem_univ _,rfl⟩
  let P (i : G.FactorIndex) := Hilbert.hilbertPolynomial K 1
    (fun _ => G.ambient.ambientDimension i)
    ((projectiveSpace K (G.ambient.ambientDimension i)).vanishingIdeal
      (V i).carrierInSingleFactor)
  have hP (i : G.FactorIndex) : P i ≠ 0 := by
    apply MultiProjectiveSpace.hilbertPolynomial_ne_zero_of_nonempty
      (projectiveSpace K (G.ambient.ambientDimension i)) (V i).carrierInSingleFactor
    exact ⟨(fun _ => (0 : (G.factor i).Point).val),
      (0 : (G.factor i).Point).val,(0 : (G.factor i).Point).property,rfl⟩
  have hr (i : G.FactorIndex) : rename (fun _ : Fin 1 => i) (P i) ≠ 0 := by
    intro hz
    apply hP i
    exact (rename_injective _ (fun _ _ _ => Subsingleton.elim _ _))
      (by simpa only [map_zero] using hz)
  unfold varietyDimension EmbeddedGroupProduct.vanishingIdeal
  rw [heq]
  change (Hilbert.hilbertPolynomial K G.ambient.factorCount G.ambient.ambientDimension
    (G.ambient.vanishingIdeal (SectionThree.productCarrier G.ambient V))).totalDegree = _
  rw [product_projective_hilbert_polynomial K G.ambient V]
  change (∏ i, rename (fun _ : Fin 1 => i) (P i)).totalDegree = _
  rw [(ProductDegree.top_prod Finset.univ _ (fun i _ => hr i)).1]
  simp only [ProductDegree.degree_rename_single]
  rfl

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponAmbientHilbertLowerLocal

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

theorem ambient_hilbert_lower_proof
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hG : G.IsConnected)
    (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ)) :
    hilbertDegreeForm G Set.univ D /
        ((2 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ)) ≤
      (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) D : ℝ) := by
  classical
  let V (i : G.FactorIndex) : ProjectiveSubvariety K (G.ambient.ambientDimension i) :=
    ⟨(G.factor i).carrier, (G.factor i).locallyClosed⟩
  have hne (i : G.FactorIndex) : (V i).carrier.Nonempty :=
    ⟨(0 : (G.factor i).Point).val, (0 : (G.factor i).Point).property⟩
  obtain ⟨δ, hδ⟩ := Classical.axiomOfChoice (fun i => (V i).exists_positive_degree_nat (hne i))
  have hδpos (i : G.FactorIndex) : 0 < δ i := (hδ i).1
  have hemb : G.embedding '' Set.univ = productCarrier G.ambient V := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩ i
      exact (y i).property
    · intro hx
      exact ⟨(fun i => ⟨x i, hx i⟩), Set.mem_univ _, rfl⟩
  have hdim : locusDimension G.ambient (productCarrier G.ambient V) = G.dimension := by
    rw [← hemb]
    exact G.varietyDimension_univ
  have hdeg (d : G.FactorIndex → ℕ) :
      hilbertDegreeForm G Set.univ d =
        (G.dimension.factorial : ℝ) / (∏ i, ((V i).dimension.factorial : ℝ)) *
          (∏ i, (δ i : ℝ)) * ∏ i, (d i : ℝ) ^ (V i).dimension := by
    have h := lemma_3_4_of_product_hilbertPolynomial K G.ambient V
      (product_projective_hilbert_polynomial K G.ambient V) d
    rw [hdim] at h
    simp_rw [(hδ _).2] at h
    have hh : hilbertDegreeForm G Set.univ d =
        (locusDegreeValue G.ambient (productCarrier G.ambient V) d : ℝ) := by
      unfold hilbertDegreeForm EmbeddedGroupProduct.vanishingIdeal
      rw [hemb]
      rfl
    rw [hh]
    have hr := congrArg (fun q : ℚ => (q : ℝ)) h
    push_cast at hr
    exact hr
  have hfacpos : (0 : ℝ) < ∏ i, ((V i).dimension.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
  have hfac : (∏ i, ((V i).dimension.factorial : ℝ)) ≤ (G.dimension.factorial : ℝ) := by
    have h := Nat.le_of_dvd (Nat.factorial_pos (∑ i, (V i).dimension))
      (Nat.prod_factorial_dvd_factorial_sum Finset.univ (fun i => (V i).dimension))
    have hn : (∑ i, (V i).dimension) = G.dimension := rfl
    rw [hn] at h
    exact_mod_cast h
  have hratio : (1 : ℝ) ≤ (G.dimension.factorial : ℝ) /
      (∏ i, ((V i).dimension.factorial : ℝ)) := (one_le_div hfacpos).mpr hfac
  have hδD (i : G.FactorIndex) : δ i ≤ D i := by
    have hδle : (δ i : ℝ) ≤ ∏ j, (δ j : ℝ) := by
      have hn := Finset.single_le_prod' (f := δ)
        (fun j _ => Nat.succ_le_of_lt (hδpos j)) (Finset.mem_univ i)
      exact_mod_cast hn
    have hprodpos : (0 : ℝ) ≤ ∏ j, (δ j : ℝ) :=
      Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    have hle : (δ i : ℝ) ≤ hilbertDegreeForm G Set.univ (fun _ => 1) := by
      rw [hdeg]
      simp only [Nat.cast_one, one_pow, Finset.prod_const_one, mul_one]
      exact hδle.trans (le_mul_of_one_le_left hprodpos hratio)
    exact_mod_cast hle.trans (hD i)
  let h (i : G.FactorIndex) : ℝ :=
    Hilbert.hilbertFunction K 1 (fun _ => G.ambient.ambientDimension i)
      ((projectiveSpace K (G.ambient.ambientDimension i)).vanishingIdeal
        (V i).carrierInSingleFactor) (fun _ => D i)
  have hlower := HilbertNumerics.product_lower_of_binomial_bounds δ D
    (fun i => (V i).dimension) hδpos hδD h
    (fun i => (V i).hilbert_binomial_lower (hne i) (δ i) (D i) (hδ i).2 (hδD i))
  have hh : (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
      (G.vanishingIdeal Set.univ) D : ℝ) = ∏ i, h i := by
    have hp := product_projective_hilbert_function K G.ambient V D
    unfold EmbeddedGroupProduct.vanishingIdeal
    rw [hemb]
    have hpR := congrArg (fun n : ℕ => (n : ℝ)) hp
    push_cast at hpR
    exact hpR
  rw [hh, hdeg]
  have hn : (∑ i, (V i).dimension) = G.dimension := rfl
  rw [hn] at hlower
  convert hlower using 1
  have hnfac : (G.dimension.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  <;> ring

end PhilipponMultiplicity

end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hG : G.IsConnected)
    (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ)) :
    hilbertDegreeForm G Set.univ D /
        ((2 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ)) ≤
      (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) D : ℝ) := by
  exact ambient_hilbert_lower_proof K hK G hG D hD
