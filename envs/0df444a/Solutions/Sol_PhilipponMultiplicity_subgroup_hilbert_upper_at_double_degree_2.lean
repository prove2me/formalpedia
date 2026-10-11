-- Prove2me | solution 2 for PhilipponMultiplicity.subgroup_hilbert_upper_at_double_degree
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-10T22:11:09.150572+00:00
-- url     : https://prove2.me/submissions/07198c4c-ea10-4c9a-89b8-b4a5319c40b5

import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_SectionFive
import Definitions.Def_PhilipponMultiplicity_SectionFour
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Mathlib
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.KrullDimension
import Theorems.Thm_PhilipponMultiplicity_Hilbert_component_length_formula
import Theorems.Thm_PhilipponMultiplicity_Hilbert_hilbertPolynomial_filtration_sum
import Theorems.Thm_PhilipponMultiplicity_Hilbert_homogeneous_prime_filtration
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_antitone
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_prime_krull_dimension_formula
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_exists
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients

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

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isClosed_zero (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsClosed _ M.zariskiTopology {x | M.eval P x = 0} := by
  letI := M.zariskiTopology
  simpa only [Set.compl_setOf, not_not] using (M.isOpen_basic P D hP).isClosed_compl

theorem isTopologicalBasis_basic :
    @TopologicalSpace.IsTopologicalBasis _ M.zariskiTopology
      {U | ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
        U = {x | M.eval P x ≠ 0}} := by
  classical
  letI := M.zariskiTopology
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (show M.zariskiTopology = TopologicalSpace.generateFrom _ from rfl) (by
      rintro U ⟨P, D, hP, rfl⟩ V ⟨Q, E, hQ, rfl⟩
      refine ⟨P * Q, D + E, hP.mul M hQ, ?_⟩
      ext x
      simp [eval, mul_ne_zero_iff])
  have huniv : Set.univ ∈ {U | ∃ P : M.CoordinateRing, ∃ D,
      M.IsHomogeneous P D ∧ U = {x | M.eval P x ≠ 0}} := by
    refine ⟨1, 0, M.isHomogeneous_one, ?_⟩
    ext x
    simp [eval]
  simpa only [Set.insert_eq_of_mem huniv] using h

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

theorem vanishingIdeal_antitone {S T : Set M.Point} (h : S ⊆ T) :
    M.vanishingIdeal T ≤ M.vanishingIdeal S := by
  apply Ideal.span_mono
  rintro P ⟨hP, hz⟩
  exact ⟨hP, fun x hx => hz x (h hx)⟩

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
-- Reused implementation: Solutions.PhilipponProjectiveContact

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_block_scale {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (v : M.Variable → K) (a : M.FactorIndex → K) :
    MvPolynomial.eval (fun j => a j.1 * v j) P = (∏ i, a i ^ D i) * MvPolynomial.eval v P := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hscale : (∏ j : M.Variable, a j.1 ^ d j) = ∏ i, a i ^ D i := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ d ⟨i, j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP d hd i]
  simp only [mul_pow, Finset.prod_mul_distrib, hscale]
  ring

private theorem completeSpace_of_isometric_ringEquiv
    {K F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField F]
    [CompleteSpace F] (e : K ≃+* F) (he : Isometry e) : CompleteSpace K :=
  (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

theorem IsPhilipponBaseField.completeSpace {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact completeSpace_of_isometric_ringEquiv e he
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact completeSpace_of_isometric_ringEquiv e he

end PhilipponMultiplicity
end
end

section
-- Reused implementation: Solutions.PhilipponAdditiveSubgroups

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_eq_zero_iff_of_lift
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (p : M.Point)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    MvPolynomial.eval v P = 0 ↔ M.eval P p = 0 := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K))]
  exact mul_eq_zero.trans (or_iff_right hne)

end PhilipponMultiplicity
end
end

section
-- Reused implementation: Solutions.PhilipponHomogeneousOperations

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

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

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
-- Reused implementation: Solutions.PhilipponRegularMapTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem isHomogeneous_zero (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) :
    M.IsHomogeneous 0 D := by simp [IsHomogeneous]

theorem isHomogeneous_sum (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) D) :
    M.IsHomogeneous (∑ i ∈ s, P i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_zero D
  | @insert i s hi ih =>
    simp only [Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).add M (ih (fun j hj => hP j (by simp [hj])))

theorem isHomogeneous_prod (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : ι → M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) (D i)) :
    M.IsHomogeneous (∏ i ∈ s, P i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_one
  | @insert i s hi ih =>
    simp only [Finset.prod_insert, Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).mul M (ih (fun j hj => hP j (by simp [hj])))

theorem IsHomogeneous.eval₂_blocks (M N : MultiProjectiveSpace K)
    {Q : N.CoordinateRing} {D : N.FactorIndex → ℕ} (hQ : N.IsHomogeneous Q D)
    (P : N.Variable → M.CoordinateRing) (E : N.FactorIndex → M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) (E j.1)) :
    M.IsHomogeneous (eval₂ C P Q) (fun i => ∑ b, D b * E b i) := by
  classical
  rw [eval₂_eq']
  apply M.isHomogeneous_sum
  intro d hd
  have hh := M.isHomogeneous_prod Finset.univ (fun j => P j ^ d j)
    (fun j i => d j * E j.1 i) (fun j _ => (hP j).pow M (d j))
  have he : (∑ j : N.Variable, fun i => d j * E j.1 i) =
      (fun i => ∑ b, D b * E b i) := by
    funext i
    simp only [Finset.sum_apply]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro b _
    change (∑ y, d ⟨b, y⟩ * E b i) = D b * E b i
    rw [← Finset.sum_mul, hQ d hd b]
  rw [he] at hh
  exact hh.C_mul M _

theorem projectivization_mk_eq_iff_cross {ι : Type*}
    (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K w hw ↔
      ∀ j k, v j * w k = v k * w j := by
  classical
  constructor
  · intro heq
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K v w hv hw).mp heq
    intro j k
    rw [← ha]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
    change w k ≠ 0 at hk
    apply (Projectivization.mk_eq_mk_iff' K v w hv hw).mpr
    refine ⟨v k / w k, ?_⟩
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
    apply (div_eq_iff hk).mpr
    exact h k j

theorem IsRegularAlong.continuous
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) :
    @Continuous X N.Point (TopologicalSpace.induced e M.zariskiTopology)
      N.zariskiTopology f := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨R, D, hR, rfl⟩
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  choose U hU hxU E P hP hlift using hf x
  let pull := eval₂ C (fun j : N.Variable => P j.1 j.2) R
  have hpull : M.IsHomogeneous pull (fun i => ∑ b, D b * E b i) :=
    hR.eval₂_blocks M N _ E (fun j => hP j.1 j.2)
  have heval (y : X) : M.eval pull (e y) =
      MvPolynomial.eval (fun j : N.Variable => M.eval (P j.1 j.2) (e y)) R := by
    dsimp only [eval, pull]
    rw [← eval_assoc]
    rfl
  have hiff (y : X) (hy : ∀ b, e y ∈ U b) :
      M.eval pull (e y) = 0 ↔ N.eval R (f y) = 0 := by
    rw [heval]
    exact N.eval_eq_zero_iff_of_lift (f y) _ (fun b => hlift b y (hy b)) R D hR
  let W : Set M.Point := (⋂ b, U b) ∩ {p | M.eval pull p ≠ 0}
  have hW : IsOpen (e ⁻¹' W) :=
    ((isOpen_iInter_of_finite hU).inter (M.isOpen_basic _ _ hpull)).preimage
      continuous_induced_dom
  have hxW : x ∈ e ⁻¹' W := ⟨Set.mem_iInter.mpr hxU, (hiff x hxU).not.mpr hx⟩
  refine Filter.mem_of_superset (hW.mem_nhds hxW) ?_
  intro y hy
  exact (hiff y (Set.mem_iInter.mp hy.1)).not.mp hy.2

theorem IsRegularAlong.comp_domain
    {X Y : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) (g : Y → X) :
    M.IsRegularAlong N (e ∘ g) (f ∘ g) := by
  intro y b
  obtain ⟨U, hU, hy, D, P, hP, hl⟩ := hf (g y) b
  exact ⟨U, hU, hy, D, P, hP, fun z hz => hl (g z) hz⟩

end PhilipponMultiplicity.MultiProjectiveSpace
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

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponSegreVeronesePieces

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

def blockLinearSpace (i : M.FactorIndex) : Submodule K M.CoordinateRing :=
  Submodule.span K (Set.range (fun j : Fin (M.ambientDimension i + 1) => X ⟨i,j⟩))

def blockProductSpace (D : M.FactorIndex → ℕ) : Submodule K M.CoordinateRing :=
  ∏ i, M.blockLinearSpace i ^ D i

theorem blockProductSpace_add (D E : M.FactorIndex → ℕ) :
    M.blockProductSpace (D + E) = M.blockProductSpace D * M.blockProductSpace E := by
  simp [blockProductSpace, pow_add, Finset.prod_mul_distrib]

theorem blockProductSpace_single (i : M.FactorIndex) (n : ℕ) :
    M.blockProductSpace (Pi.single i n) = M.blockLinearSpace i ^ n := by
  classical
  simp [blockProductSpace, Pi.single_apply]

theorem monomial_mem_blockProductSpace (e : M.Variable →₀ ℕ) (c : K) :
    monomial e c ∈ M.blockProductSpace
      (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) e) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp [blockProductSpace]
  | single_add v n e hv hn ih =>
    rw [map_add, Finsupp.weight_single, blockProductSpace_add, monomial_single_add]
    have he : n • Hilbert.blockWeight M.factorCount M.ambientDimension v = Pi.single v.1 n := by
      ext i
      simp [Hilbert.blockWeight, Pi.single_apply]
    rw [he, blockProductSpace_single]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _
      (Submodule.subset_span (Set.mem_range_self v.2)) n) ih

theorem degreePiece_pow_le (D : M.FactorIndex → ℕ) (n : ℕ) :
    (Hilbert.degreePiece K M.factorCount M.ambientDimension D) ^ n ≤
      Hilbert.degreePiece K M.factorCount M.ambientDimension (n • D) := by
  induction n with
  | zero =>
    simp only [pow_zero, zero_nsmul]
    exact Submodule.one_le.mpr (MvPolynomial.isWeightedHomogeneous_one K _)
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact (mul_le_mul' ih le_rfl).trans
      (MvPolynomial.weightedHomogeneousSubmodule_mul _ _ _)

theorem blockProductSpace_le_degreePiece (D : M.FactorIndex → ℕ) :
    M.blockProductSpace D ≤ Hilbert.degreePiece K M.factorCount M.ambientDimension D := by
  classical
  have hblock (i : M.FactorIndex) : M.blockLinearSpace i ≤
      Hilbert.degreePiece K M.factorCount M.ambientDimension (Pi.single i 1) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have he : (Pi.single i 1 : M.FactorIndex → ℕ) = fun k => if k = i then 1 else 0 := by
      ext k
      simp [Pi.single_apply]
    rw [he]
    exact (M.degreePiece_iff _ _).mpr (M.isHomogeneous_X ⟨i,j⟩)
  have hpow (i : M.FactorIndex) : M.blockLinearSpace i ^ D i ≤
      Hilbert.degreePiece K M.factorCount M.ambientDimension (Pi.single i (D i)) := by
    have h := (pow_le_pow_left' (hblock i) (D i)).trans (M.degreePiece_pow_le _ _)
    have he : D i • (Pi.single i 1 : M.FactorIndex → ℕ) = Pi.single i (D i) := by
      ext j
      simp [Pi.single_apply]
    rw [he] at h
    exact h
  have hprod (s : Finset M.FactorIndex) : (∏ i ∈ s, M.blockLinearSpace i ^ D i) ≤
      Hilbert.degreePiece K M.factorCount M.ambientDimension (∑ i ∈ s, Pi.single i (D i)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact Submodule.one_le.mpr (MvPolynomial.isWeightedHomogeneous_one K _)
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (mul_le_mul' (hpow i) ih).trans
        (MvPolynomial.weightedHomogeneousSubmodule_mul _ _ _)
  have hsum : (∑ i, Pi.single i (D i)) = D := by
    ext j
    simp [Pi.single_apply]
  simpa only [hsum, blockProductSpace] using hprod Finset.univ

theorem degreePiece_eq_blockProductSpace (D : M.FactorIndex → ℕ) :
    Hilbert.degreePiece K M.factorCount M.ambientDimension D = M.blockProductSpace D := by
  apply le_antisymm _ (M.blockProductSpace_le_degreePiece D)
  intro P hP
  rw [P.as_sum]
  apply Submodule.sum_mem
  intro e he
  have heD := hP (MvPolynomial.mem_support_iff.mp he)
  rw [← heD]
  exact M.monomial_mem_blockProductSpace e _

theorem degreePiece_diagonal_pow (D : M.FactorIndex → ℕ) (n : ℕ) :
    (Hilbert.degreePiece K M.factorCount M.ambientDimension D) ^ n =
      Hilbert.degreePiece K M.factorCount M.ambientDimension (fun i => n * D i) := by
  rw [M.degreePiece_eq_blockProductSpace, M.degreePiece_eq_blockProductSpace]
  change (∏ i, M.blockLinearSpace i ^ D i) ^ n = ∏ i, M.blockLinearSpace i ^ (n * D i)
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, mul_comm]

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
-- Reused implementation: Solutions.PhilipponFixedFactorHilbert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace

variable {K : Type*} [Field K] (N : ℕ)

theorem projective_homogeneous_iff (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) :
    (projectiveSpace K N).IsHomogeneous P (fun _ => n) ↔ P.IsHomogeneous n := by
  classical
  change (∀ d ∈ P.support, ∀ i : Fin 1, ∑ j : Fin (N + 1), d ⟨i, j⟩ = n) ↔ _
  constructor
  · intro h d hd
    rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
    change (∑ i : Fin 1, ∑ j : Fin (N + 1), d ⟨i, j⟩ • (1 : ℕ)) = n
    simpa [Fin.sum_univ_one] using h d (mem_support_iff.mpr hd) (0 : Fin 1)
  · intro h d hd i
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    have hh := h (mem_support_iff.mp hd)
    rw [Finsupp.weight_eq_sum, Fintype.sum_sigma] at hh
    change (∑ i : Fin 1, ∑ j : Fin (N + 1), d ⟨i, j⟩ • (1 : ℕ)) = n at hh
    simpa [Fin.sum_univ_one] using hh

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
-- Reused implementation: Solutions.PhilipponSegreVeroneseHilbert

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K]

theorem ordinary_degreePiece_eq (N n : ℕ) :
    degreePiece K 1 (fun _ => N) (fun _ => n) =
      homogeneousSubmodule (projectiveSpace K N).Variable K n := by
  ext P
  exact ((projectiveSpace K N).degreePiece_iff P _).trans
    (MultiProjectiveSpace.projective_homogeneous_iff N P n)

namespace SegreVeronese
variable (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
  (b : Module.Basis (projectiveSpace K N).Variable K
    (degreePiece K M.factorCount M.ambientDimension D))

def substitution : (projectiveSpace K N).CoordinateRing →ₐ[K] M.CoordinateRing :=
  aeval (fun j => (b j).val)

theorem substitution_degreePiece (n : ℕ) :
    (degreePiece K 1 (fun _ => N) (fun _ => n)).map
      (substitution M D b).toLinearMap =
        degreePiece K M.factorCount M.ambientDimension (fun i => n * D i) := by
  rw [ordinary_degreePiece_eq, ← homogeneousSubmodule_one_pow,
    Submodule.map_pow, homogeneousSubmodule_one_eq_span_X, Submodule.map_span]
  have he : (substitution M D b).toLinearMap '' Set.range X = Set.range (fun j => (b j).val) := by
    rw [← Set.range_comp]
    congr 1
    funext j
    simp [substitution]
  rw [he]
  have hspan : Submodule.span K (Set.range (fun j => (b j).val)) =
      degreePiece K M.factorCount M.ambientDimension D := by
    change Submodule.span K (Set.range
      ((degreePiece K M.factorCount M.ambientDimension D).subtype ∘ b)) = _
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  rw [hspan, M.degreePiece_diagonal_pow]

theorem substitution_homogeneous (n : ℕ)
    (P : (projectiveSpace K N).CoordinateRing) (hP : P.IsHomogeneous n) :
    (substitution M D b P).IsWeightedHomogeneous
      (blockWeight M.factorCount M.ambientDimension) (fun i => n * D i) := by
  have hmem : P ∈ degreePiece K 1 (fun _ => N) (fun _ => n) := by
    rw [ordinary_degreePiece_eq]
    exact hP
  change substitution M D b P ∈ degreePiece K M.factorCount M.ambientDimension _
  rw [← substitution_degreePiece M D b n]
  exact Submodule.mem_map_of_mem hmem

def diagonalIdeal (I : Ideal M.CoordinateRing) :
    Ideal (projectiveSpace K N).CoordinateRing :=
  I.comap (substitution M D b).toRingHom

theorem hilbertFunction_diagonal (I : Ideal M.CoordinateRing) (n : ℕ) :
    hilbertFunction K 1 (fun _ => N) (diagonalIdeal M D b I) (fun _ => n) =
      hilbertFunction K M.factorCount M.ambientDimension I (fun i => n * D i) := by
  let V := degreePiece K 1 (fun _ => N) (fun _ => n)
  let J := diagonalIdeal M D b I
  let f := (Ideal.Quotient.mkₐ K J).toLinearMap.domRestrict V
  let g := ((Ideal.Quotient.mkₐ K I).comp (substitution M D b)).toLinearMap.domRestrict V
  have hk : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk J P.val = 0 ↔
      Ideal.Quotient.mk I (substitution M D b P.val) = 0
    simp only [Ideal.Quotient.eq_zero_iff_mem, J, diagonalIdeal, Ideal.mem_comap]
    rfl
  have he := (f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans g.quotKerEquivRange)).finrank_eq
  have hf : LinearMap.range f = quotientPiece K 1 (fun _ => N) J (fun _ => n) :=
    LinearMap.range_domRestrict _ _
  have hg : LinearMap.range g = quotientPiece K M.factorCount M.ambientDimension I
      (fun i => n * D i) := by
    rw [LinearMap.range_domRestrict]
    change V.map ((Ideal.Quotient.mkₐ K I).toLinearMap.comp
      (substitution M D b).toLinearMap) = _
    rw [Submodule.map_comp, substitution_degreePiece]
    rfl
  rw [hf, hg] at he
  exact he

end SegreVeronese
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
-- Reused implementation: Solutions.PhilipponSegreVeroneseAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K]

theorem ordinary_weight_eq (N : ℕ) (e : ((i : Fin 1) × Fin (N + 1)) →₀ ℕ) :
    Finsupp.weight (blockWeight 1 (fun _ => N)) e = fun _ => e.degree := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hd : e.degree = ∑ j : Fin (N + 1), e ⟨(0 : Fin 1), j⟩ := by
    rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
    simp [Fin.sum_univ_one]
  exact (MonomialCells.weight_apply 1 (fun _ => N) e 0).trans hd.symm

theorem ordinary_component_eq (N : ℕ) (P : CoordinateRing K 1 (fun _ => N))
    (d : Fin 1 → ℕ) :
    weightedHomogeneousComponent (blockWeight 1 (fun _ => N)) d P =
      homogeneousComponent (d 0) P := by
  classical
  apply MvPolynomial.ext
  intro e
  have he : (fun _ : Fin 1 => e.degree) = d ↔ e.degree = d 0 := by
    constructor
    · exact fun h => congrFun h 0
    · intro h
      ext i
      simpa only [Subsingleton.elim i (0 : Fin 1)] using h
  calc
    _ = if Finsupp.weight (blockWeight 1 (fun _ => N)) e = d then coeff e P else 0 :=
      coeff_weightedHomogeneousComponent d P e
    _ = if e.degree = d 0 then coeff e P else 0 := by simp only [ordinary_weight_eq, he]
    _ = _ := (coeff_homogeneousComponent (d 0) P e).symm

namespace SegreVeronese
variable (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
  (b : Module.Basis (projectiveSpace K N).Variable K
    (degreePiece K M.factorCount M.ambientDimension D))

theorem substitution_component (hD : ∀ i, 1 ≤ D i)
    (P : (projectiveSpace K N).CoordinateRing) (n : ℕ) :
    weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension)
      (fun i => n * D i) (substitution M D b P) =
        substitution M D b (homogeneousComponent n P) := by
  classical
  have hinj : Function.Injective (fun m : ℕ => fun i => m * D i) := by
    intro m n h
    let i : M.FactorIndex := ⟨0, M.positive⟩
    have hi := congrFun h i
    have hpos := hD i
    nlinarith
  rw [P.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hh := isHomogeneous_monomial (coeff e P) (rfl : e.degree = e.degree)
  have hs := substitution_homogeneous M D b e.degree _ hh
  rw [weightedHomogeneousComponent_of_mem hs, homogeneousComponent_of_mem hh]
  by_cases hn : n = e.degree
  · subst n
    simp only [ite_true]
  · rw [if_neg (fun h => hn (hinj h)), if_neg hn, map_zero]

theorem diagonalIdeal_homogeneous (hD : ∀ i, 1 ≤ D i)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    IsMultihomogeneousIdeal (projectiveSpace K N) (diagonalIdeal M D b I) := by
  intro P hP d
  change Fin 1 → ℕ at d
  change substitution M D b
    (weightedHomogeneousComponent (blockWeight 1 (fun _ => N)) d P) ∈ I
  rw [ordinary_component_eq]
  exact (substitution_component M D b hD P (d 0)) ▸
    hI _ hP (fun i => d 0 * D i)

theorem diagonalIdeal_isPrime (I : Ideal M.CoordinateRing) (hI : I.IsPrime) :
    (diagonalIdeal M D b I).IsPrime := by
  letI := hI
  exact Ideal.IsPrime.comap (substitution M D b).toRingHom

theorem degreePiece_finrank_pos :
    0 < Module.finrank K (degreePiece K M.factorCount M.ambientDimension D) := by
  classical
  let e : M.Variable →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun v => if v.2 = 0 then D v.1 else 0)
  have hhom : M.IsHomogeneous (monomial e (1 : K)) D := by
    intro a ha i
    have he : a = e := Finset.mem_singleton.mp (support_monomial_subset ha)
    subst a
    change (∑ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩) = D i
    simp only [e, Finsupp.coe_equivFunOnFinite_symm]
    exact (Finset.sum_ite_eq' Finset.univ (0 : Fin (M.ambientDimension i + 1))
      (fun _ => D i)).trans (if_pos (Finset.mem_univ _))
  have hmem := (M.degreePiece_iff _ _).mpr hhom
  let x : degreePiece K M.factorCount M.ambientDimension D := ⟨monomial e 1, hmem⟩
  have hx : x ≠ 0 := by
    intro h
    have hz := congrArg Subtype.val h
    simpa only [x, ZeroMemClass.coe_zero, monomial_eq_zero, one_ne_zero] using hz
  letI : Nontrivial (degreePiece K M.factorCount M.ambientDimension D) :=
    ⟨⟨x, 0, hx⟩⟩
  exact Module.finrank_pos

theorem exists_coordinate_basis : ∃ N : ℕ,
    Nonempty (Module.Basis (projectiveSpace K N).Variable K
      (degreePiece K M.factorCount M.ambientDimension D)) := by
  classical
  let d := Module.finrank K (degreePiece K M.factorCount M.ambientDimension D)
  have hd : 0 < d := degreePiece_finrank_pos M D
  let N := d - 1
  have hc : Fintype.card (projectiveSpace K N).Variable = d := by
    simp [MultiProjectiveSpace.Variable, projectiveSpace, N, Nat.sub_add_cancel hd]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨N, ⟨(Module.finBasis K (degreePiece K M.factorCount M.ambientDimension D)).reindex e.symm⟩⟩

end SegreVeronese
end PhilipponMultiplicity.Hilbert

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

theorem component_mul_homogeneous
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

instance quotientPiece_finite_colon (I : Ideal M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    Module.Finite K (quotientPiece K M.factorCount M.ambientDimension I d) := by
  unfold quotientPiece
  infer_instance

theorem homogeneous_colon (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I.colon {P}) := by
  intro Q hQ d
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hQ ⊢
  have h := hI (P * Q) (by simpa [mul_comm] using hQ) (D + d)
  rw [component_mul_homogeneous M hP Q d, mul_comm] at h
  exact h

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

theorem prime_of_homogeneous_products (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hne : I ≠ ⊤)
    (hmul : ∀ P Q : M.CoordinateRing, (∃ D, M.IsHomogeneous P D) →
      (∃ E, M.IsHomogeneous Q E) → P * Q ∈ I → P ∈ I ∨ Q ∈ I) : I.IsPrime := by
  classical
  let w : M.Variable → Lex (M.FactorIndex → ℕ) :=
    fun x => toLex (blockWeight M.factorCount M.ambientDimension x)
  letI : DecidableEq (Lex (M.FactorIndex → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra K w
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    rw [MvPolynomial.decompose'_apply]
    have heq : weightedHomogeneousComponent w d f =
        weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (ofLex d) f := by
      ext e
      simp only [coeff_weightedHomogeneousComponent]
      rfl
    rw [heq]
    exact hI f hf (ofLex d)
  apply hIg.isPrime_of_homogeneous_mem_or_mem hne
  rintro P Q ⟨D, hP⟩ ⟨E, hQ⟩ hPQ
  apply hmul P Q _ _ hPQ
  · exact ⟨ofLex D, (M.degreePiece_iff P (ofLex D)).mp hP⟩
  · exact ⟨ofLex E, (M.degreePiece_iff Q (ofLex E)).mp hQ⟩

end PhilipponMultiplicity.Hilbert

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

end PhilipponMultiplicity.ProductDegree

namespace PhilipponMultiplicity
open SectionThree

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponBinomialPolynomial

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.BinomialPolynomial

def oneVariable (q a : ℕ) : MvPolynomial (Fin 1) ℚ :=
  (uniqueAlgEquiv ℚ (Fin 1)).symm (Polynomial.preHilbertPoly ℚ q a)

theorem oneVariable_coeff (q a : ℕ) (b : Fin 1 →₀ ℕ) :
    coeff b (oneVariable q a) = (Polynomial.preHilbertPoly ℚ q a).coeff (b 0) :=
  coeff_uniqueAlgEquiv_symm ℚ _ _

theorem oneVariable_degree (q a : ℕ) : (oneVariable q a).totalDegree = q := by
  classical
  apply le_antisymm
  · change (oneVariable q a).support.sup (fun b : Fin 1 →₀ ℕ => b.sum (fun _ e => e)) ≤ q
    apply Finset.sup_le
    intro b hb
    have h := mem_support_iff.mp hb
    rw [oneVariable_coeff] at h
    have ht := Polynomial.le_natDegree_of_ne_zero h
    rw [Polynomial.natDegree_preHilbertPoly] at ht
    simpa [Finsupp.sum_fintype] using ht
  · have hcoeff : coeff (Finsupp.single 0 q) (oneVariable q a) ≠ 0 := by
      rw [oneVariable_coeff, Finsupp.single_eq_same, Polynomial.coeff_preHilbertPoly_self]
      exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero q)
    simpa using le_totalDegree (mem_support_iff.mpr hcoeff)

theorem oneVariable_top (q a : ℕ) :
    homogeneousComponent q (oneVariable q a) =
      monomial (Finsupp.single 0 q) (q.factorial : ℚ)⁻¹ := by
  have h := ProductDegree.top_fin_one (oneVariable q a)
  simpa only [oneVariable_degree, oneVariable_coeff, Finsupp.single_eq_same,
    Polynomial.coeff_preHilbertPoly_self] using h

def block {ι : Type*} (i : ι) (q a : ℕ) : MvPolynomial ι ℚ :=
  rename (fun _ : Fin 1 => i) (oneVariable q a)

theorem block_degree {ι : Type*} (i : ι) (q a : ℕ) : (block i q a).totalDegree = q := by
  rw [block, ProductDegree.degree_rename_single, oneVariable_degree]

theorem block_top {ι : Type*} (i : ι) (q a : ℕ) :
    homogeneousComponent q (block i q a) =
      monomial (Finsupp.single i q) (q.factorial : ℚ)⁻¹ := by
  rw [block, ← rename_homogeneousComponent, oneVariable_top, rename_monomial]
  simp

theorem block_eval {ι : Type*} (i : ι) (q a : ℕ) (d : ι → ℕ) (ha : a ≤ d i) :
    eval (fun i => (d i : ℚ)) (block i q a) = ((d i - a + q).choose q : ℚ) := by
  rw [block, eval_rename]
  change MvPolynomial.eval₂ (RingHom.id ℚ) _
    ((uniqueAlgEquiv ℚ (Fin 1)).symm _) = _
  rw [eval₂_uniqueAlgEquiv_symm]
  exact Polynomial.preHilbertPoly_eq_choose_sub_add ℚ q ha

end PhilipponMultiplicity.BinomialPolynomial

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

theorem variable_product_homogeneous (v : ∀ i, Fin (M.ambientDimension i + 1))
    (d : M.FactorIndex → ℕ) :
    M.IsHomogeneous (∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i) d := by
  classical
  apply (M.degreePiece_iff _ d).mp
  let w := blockWeight M.factorCount M.ambientDimension
  have hx (i : M.FactorIndex) : (X ⟨i, v i⟩ : M.CoordinateRing).IsWeightedHomogeneous w
      (w ⟨i, v i⟩) := isWeightedHomogeneous_X K w ⟨i, v i⟩
  have h := IsWeightedHomogeneous.prod (w := w) Finset.univ
    (fun i => (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i)
    (fun i => d i • blockWeight M.factorCount M.ambientDimension ⟨i, v i⟩)
    (fun i _ => (hx i).pow (d i))
  have heq : (∑ i, d i • blockWeight M.factorCount M.ambientDimension ⟨i, v i⟩) = d := by
    funext i
    simp [blockWeight, Pi.single_apply, Finset.sum_apply, smul_eq_mul]
  rwa [heq] at h

theorem variable_product_notMem (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (v : ∀ i, Fin (M.ambientDimension i + 1)) (hv : ∀ i, X ⟨i, v i⟩ ∉ Q)
    (d : M.FactorIndex → ℕ) : (∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i) ∉ Q := by
  classical
  letI := hQ
  intro h
  obtain ⟨i, hi, hip⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hv i (hQ.mem_of_pow_mem _ hip)

theorem relevant_prime_hilbertPolynomial_ne_zero (Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    hilbertPolynomial K M.factorCount M.ambientDimension Q ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := relevant_variables M Q hrel
  intro hz
  have hex := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q hhom)
  rw [hz] at hex
  obtain ⟨d, hd⟩ := hex
  let P : M.CoordinateRing := ∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i
  have hP : P ∉ Q := variable_product_notMem M Q hQ v hv d
  let x : quotientPiece K M.factorCount M.ambientDimension Q d :=
    ⟨Ideal.Quotient.mk Q P, P, (M.degreePiece_iff P d).mpr (variable_product_homogeneous M v d), rfl⟩
  have hx : x ≠ 0 := by
    intro h
    exact hP (Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val h))
  letI : Nontrivial (quotientPiece K M.factorCount M.ambientDimension Q d) :=
    ⟨⟨x, 0, hx⟩⟩
  have hpos := Module.finrank_pos (R := K)
    (M := quotientPiece K M.factorCount M.ambientDimension Q d)
  have heq := hd d (fun _ => le_rfl)
  change (MvPolynomial.eval _ (0 : MvPolynomial M.FactorIndex ℚ)) = _ at heq
  rw [map_zero] at heq
  have hzero : hilbertFunction K M.factorCount M.ambientDimension Q d = 0 := by exact_mod_cast heq.symm
  exact (Nat.ne_of_gt hpos) hzero

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponHilbertGrowthExponent

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology
open Filter
noncomputable section

namespace PhilipponMultiplicity.Hilbert

theorem polynomial_eventually_two_sided (P : Polynomial ℚ) (hpos : 0 < P.leadingCoeff) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℚ) ^ P.natDegree ≤ P.eval (n : ℚ) ∧
        P.eval (n : ℚ) ≤ C * (n : ℚ) ^ P.natDegree := by
  have hP : P ≠ 0 := by
    intro hz
    simpa [hz] using hpos
  have hdegree : P.degree = (Polynomial.X ^ P.natDegree : Polynomial ℚ).degree := by
    rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hP]
  have hlim := P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (Polynomial.X ^ P.natDegree) hdegree
  have hlim' : Tendsto (fun n : ℕ => P.eval (n : ℚ) / (n : ℚ) ^ P.natDegree)
      atTop (𝓝 P.leadingCoeff) := by
    simpa [Function.comp_def] using hlim.comp (tendsto_natCast_atTop_atTop (R := ℚ))
  have hlo := (tendsto_order.mp hlim').1 (P.leadingCoeff / 2) (by linarith)
  have hhi := (tendsto_order.mp hlim').2 (2 * P.leadingCoeff) (by linarith)
  refine ⟨P.leadingCoeff / 2, 2 * P.leadingCoeff, by positivity, by positivity, ?_⟩
  filter_upwards [hlo, hhi, eventually_ge_atTop 1] with n hnlo hnhi hn
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp := pow_pos hnpos P.natDegree
  exact ⟨(le_div_iff₀ hp).mp hnlo.le, (div_le_iff₀ hp).mp hnhi.le⟩

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponGrowthExponentComparison

set_option autoImplicit false
set_option maxHeartbeats 500000
open Filter
noncomputable section

namespace PhilipponMultiplicity.Hilbert

theorem exponent_le_of_eventual_power_bound {a b : ℕ} {c C : ℚ}
    (hc : 0 < c)
    (h : ∀ᶠ n : ℕ in atTop, c * (n : ℚ) ^ a ≤ C * (n : ℚ) ^ b) : a ≤ b := by
  by_contra hab
  have hba : b + 1 ≤ a := by omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C / c) (max (N : ℚ) 1))
  have hnN : N ≤ n := by
    exact_mod_cast le_of_lt ((le_max_left (N : ℚ) 1).trans (le_max_right _ _) |>.trans_lt hn)
  have hn1 : (1 : ℚ) < n :=
    ((le_max_right (N : ℚ) 1).trans (le_max_right _ _)).trans_lt hn
  have hnpos : (0 : ℚ) < n := lt_trans zero_lt_one hn1
  have hpow : (n : ℚ) ^ (b + 1) ≤ (n : ℚ) ^ a :=
    pow_le_pow_right₀ hn1.le hba
  have hprod : (c * n) * (n : ℚ) ^ b ≤ C * (n : ℚ) ^ b := by
    calc
      (c * n) * (n : ℚ) ^ b = c * (n : ℚ) ^ (b + 1) := by rw [pow_succ]; ring
      _ ≤ c * (n : ℚ) ^ a := mul_le_mul_of_nonneg_left hpow hc.le
      _ ≤ _ := hN n hnN
  have hcn : c * n ≤ C := (mul_le_mul_iff_left₀ (pow_pos hnpos b)).mp hprod
  have hlarge : C < c * n := by
    have := (le_max_left (C / c) (max (N : ℚ) 1)).trans_lt hn
    have := (div_lt_iff₀ hc).mp this
    simpa [mul_comm] using this
  exact (not_lt_of_ge hcn) hlarge

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

theorem rayPolynomial_natDegree_le (F : MvPolynomial ι ℚ) (a E : ι → ℚ)
    (ha : ∀ i, a i ≠ 0) : (rayPolynomial F a E).natDegree ≤ F.totalDegree := by
  classical
  rw [rayPolynomial_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  rw [(rayTerm_degree_and_leadingCoeff a E ha e _ (mem_support_iff.mp he)).1]
  exact le_totalDegree he

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

theorem rayPolynomial_degree_and_leadingCoeff (F : MvPolynomial ι ℚ) (hF : F ≠ 0)
    (hpos : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F)
    (a E : ι → ℚ) (ha : ∀ i, 0 < a i) :
    (rayPolynomial F a E).natDegree = F.totalDegree ∧
      (rayPolynomial F a E).leadingCoeff = eval a (homogeneousComponent F.totalDegree F) ∧
      0 < (rayPolynomial F a E).leadingCoeff := by
  have hcoeff := rayPolynomial_top_coeff F a E (fun i => (ha i).ne')
  have hpos' := eval_top_pos F hF hpos a ha
  have hdeg := le_antisymm (rayPolynomial_natDegree_le F a E (fun i => (ha i).ne'))
    (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact hpos'.ne'))
  refine ⟨hdeg,?_,?_⟩
  · simpa only [Polynomial.leadingCoeff,hdeg] using hcoeff
  · simpa only [Polynomial.leadingCoeff,hdeg,hcoeff] using hpos'

theorem rayPolynomial_eval (F : MvPolynomial ι ℚ) (a E : ι → ℚ) (x : ℚ) :
    (rayPolynomial F a E).eval x = eval (fun i => a i * x + E i) F := by
  change (Polynomial.evalRingHom x) (eval₂ Polynomial.C
    (fun i => Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) F) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom x).comp Polynomial.C = RingHom.id ℚ := by
    ext r
    simp
  rw [hc,MvPolynomial.eval₂_id]
  have hf : (⇑(Polynomial.evalRingHom x) ∘ fun i =>
      Polynomial.C (a i) * Polynomial.X + Polynomial.C (E i)) =
        fun i => a i * x + E i := by
    funext i
    simp
  rw [hf]

end PhilipponMultiplicity.Hilbert
end
end

section
-- Reused implementation: Solutions.PhilipponSegreVeroneseDegree

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert

theorem totalDegree_uniqueAlgEquiv_symm (P : Polynomial ℚ) :
    ((uniqueAlgEquiv ℚ (Fin 1)).symm P).totalDegree = P.natDegree := by
  classical
  have h0 : (default : Fin 1) = 0 := Subsingleton.elim _ _
  apply le_antisymm
  · apply Finset.sup_le
    intro e he
    have hc := mem_support_iff.mp he
    rw [coeff_uniqueAlgEquiv_symm] at hc
    change e.degree ≤ P.natDegree
    simpa only [ProductDegree.degree_fin_one, h0] using Polynomial.le_natDegree_of_ne_zero hc
  · by_cases hP : P = 0
    · simp [hP]
    have hc : coeff (Finsupp.single 0 P.natDegree)
        ((uniqueAlgEquiv ℚ (Fin 1)).symm P) ≠ 0 := by
      rw [coeff_uniqueAlgEquiv_symm]
      simpa only [h0, Finsupp.single_eq_same, Polynomial.coeff_natDegree] using
        Polynomial.leadingCoeff_ne_zero.mpr hP
    have hle : (Finsupp.single (0 : Fin 1) P.natDegree).degree ≤
        ((uniqueAlgEquiv ℚ (Fin 1)).symm P).totalDegree := le_totalDegree (mem_support_iff.mpr hc)
    simpa only [Finsupp.degree_single] using hle

namespace SegreVeronese
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) {N : ℕ}
  (b : Module.Basis (projectiveSpace K N).Variable K
    (degreePiece K M.factorCount M.ambientDimension D))

def diagonalPolynomial (I : Ideal M.CoordinateRing) : Polynomial ℚ :=
  rayPolynomial (hilbertPolynomial K M.factorCount M.ambientDimension I)
    (fun i => (D i : ℚ)) 0

theorem hilbertPolynomial_diagonal (hD : ∀ i, 1 ≤ D i)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    hilbertPolynomial K 1 (fun _ => N) (diagonalIdeal M D b I) =
      (uniqueAlgEquiv ℚ (Fin 1)).symm (diagonalPolynomial M D I) := by
  classical
  obtain ⟨B, hB⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension I
    (multigraded_hilbert_polynomial_exists K M I hI)
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun _ => ∑ i, B i, ?_⟩
  intro d hd
  have hBd : ∀ i, B i ≤ d 0 * D i := by
    intro i
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (B j)) (Finset.mem_univ i)).trans
      ((hd 0).trans (Nat.le_mul_of_pos_right _ (hD i)))
  have hd' : d = fun _ => d 0 := by
    ext i
    exact congrArg d (Subsingleton.elim i 0)
  calc
    _ = (diagonalPolynomial M D I).eval (d 0 : ℚ) := by
      change eval₂ (RingHom.id ℚ) _ ((uniqueAlgEquiv ℚ (Fin 1)).symm _) = _
      rw [eval₂_uniqueAlgEquiv_symm]
      rfl
    _ = eval (fun i => ((d 0 * D i : ℕ) : ℚ))
        (hilbertPolynomial K M.factorCount M.ambientDimension I) := by
      rw [diagonalPolynomial, rayPolynomial_eval]
      have hx : (fun i => (D i : ℚ) * (d 0 : ℚ) + (0 : M.FactorIndex → ℚ) i) =
          fun i => ((d 0 * D i : ℕ) : ℚ) := by
        ext i
        simp [mul_comm]
      exact congrArg (fun v : M.FactorIndex → ℚ =>
        MvPolynomial.eval v (hilbertPolynomial K M.factorCount M.ambientDimension I)) hx
    _ = (hilbertFunction K M.factorCount M.ambientDimension I (fun i => d 0 * D i) : ℚ) :=
      hB _ hBd
    _ = _ := by rw [hd', hilbertFunction_diagonal]

theorem diagonalPolynomial_degree_and_leadingCoeff (hD : ∀ i, 1 ≤ D i)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hne : hilbertPolynomial K M.factorCount M.ambientDimension I ≠ 0) :
    (diagonalPolynomial M D I).natDegree = SectionThree.idealDimension M I ∧
      (diagonalPolynomial M D I).leadingCoeff =
        eval (fun i => (D i : ℚ))
          (homogeneousComponent (SectionThree.idealDimension M I)
            (hilbertPolynomial K M.factorCount M.ambientDimension I)) := by
  have htop : ∀ e, e.degree =
      (hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree →
      0 ≤ coeff e (hilbertPolynomial K M.factorCount M.ambientDimension I) := by
    intro e he
    have h := (multigraded_hilbert_polynomial_top_coefficients K M I hI).1 e
    rwa [coeff_homogeneousComponent, if_pos he] at h
  have h := rayPolynomial_degree_and_leadingCoeff
    (hilbertPolynomial K M.factorCount M.ambientDimension I) hne htop
    (fun i => (D i : ℚ)) 0 (fun i => by exact_mod_cast hD i)
  exact ⟨h.1, h.2.1⟩

theorem dimension_diagonal (hD : ∀ i, 1 ≤ D i)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hne : hilbertPolynomial K M.factorCount M.ambientDimension I ≠ 0) :
    SectionThree.idealDimension (projectiveSpace K N) (diagonalIdeal M D b I) =
      SectionThree.idealDimension M I := by
  change (hilbertPolynomial K 1 (fun _ => N) (diagonalIdeal M D b I)).totalDegree = _
  rw [hilbertPolynomial_diagonal M D b hD I hI, totalDegree_uniqueAlgEquiv_symm]
  exact (diagonalPolynomial_degree_and_leadingCoeff M D hD I hI hne).1

theorem degreeValue_diagonal (hD : ∀ i, 1 ≤ D i)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hne : hilbertPolynomial K M.factorCount M.ambientDimension I ≠ 0) :
    SectionThree.idealDegreeValue (projectiveSpace K N) (diagonalIdeal M D b I) (fun _ => 1) =
      SectionThree.idealDegreeValue M I D := by
  let F := hilbertPolynomial K M.factorCount M.ambientDimension I
  let R := diagonalPolynomial M D I
  have h := diagonalPolynomial_degree_and_leadingCoeff M D hD I hI hne
  change eval (fun _ => (1 : ℚ))
    (((hilbertPolynomial K 1 (fun _ => N) (diagonalIdeal M D b I)).totalDegree.factorial : ℚ) •
      homogeneousComponent (hilbertPolynomial K 1 (fun _ => N) (diagonalIdeal M D b I)).totalDegree
        (hilbertPolynomial K 1 (fun _ => N) (diagonalIdeal M D b I))) = _
  rw [hilbertPolynomial_diagonal M D b hD I hI, smul_eq_C_mul, map_mul, eval_C,
    ProductDegree.eval_top_fin_one, totalDegree_uniqueAlgEquiv_symm,
    coeff_uniqueAlgEquiv_symm]
  simp only [show (default : Fin 1) = 0 from Subsingleton.elim _ _,
    Finsupp.single_eq_same, Polynomial.coeff_natDegree, one_pow, mul_one]
  rw [h.1, h.2]
  change _ = eval (fun i => (D i : ℚ)) ((F.totalDegree.factorial : ℚ) •
    homogeneousComponent F.totalDegree F)
  rw [smul_eq_C_mul, map_mul, eval_C]
  rfl

end SegreVeronese
end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponAnalyticPolynomialSubstitution

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AtlasSupport

theorem substitution_coeff_analytic
    {K Z σ τ : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup Z] [NormedSpace K Z]
    (Q : σ → MvPolynomial τ (Z → K)) (z : Z)
    (hQ : ∀ v e, AnalyticAt K ((Q v).coeff e) z)
    (P : MvPolynomial σ K) (e : τ →₀ ℕ) :
    AnalyticAt K ((eval₂Hom (C.comp (Pi.constRingHom Z K)) Q P).coeff e) z := by
  classical
  induction P using MvPolynomial.induction_on generalizing e with
  | C a =>
    simp only [eval₂Hom_C,RingHom.comp_apply,coeff_C]
    split_ifs <;> exact analyticAt_const
  | add P R hP hR =>
    simp only [map_add,coeff_add]
    exact (hP e).add (hR e)
  | mul_X P v hP =>
    simp only [map_mul,eval₂Hom_X']
    rw [coeff_mul]
    exact Finset.analyticAt_sum _ fun p _ => (hP p.1).mul (hQ v p.2)

theorem homogeneous_substitution
    {K R τ L : Type*} [Field K] [CommSemiring R] [AddCommMonoid L]
    (M : MultiProjectiveSpace K) (φ : K →+* R) (w : τ → L)
    (Q : M.Variable → MvPolynomial τ R) (E : M.FactorIndex → L)
    (hQ : ∀ v, (Q v).IsWeightedHomogeneous w (E v.1))
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    (eval₂Hom (C.comp φ) Q P).IsWeightedHomogeneous w (∑ i, D i • E i) := by
  classical
  change (eval₂ (C.comp φ) Q P).IsWeightedHomogeneous w _
  rw [eval₂_eq']
  apply IsWeightedHomogeneous.sum
  intro d hd
  have hh := (IsWeightedHomogeneous.prod Finset.univ (fun v => Q v ^ d v)
    (fun v => d v • E v.1) (fun v _ => (hQ v).pow (d v))).C_mul (φ (coeff d P))
  have he : (∑ v : M.Variable, d v • E v.1) = ∑ i, D i • E i := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    change (∑ j, d ⟨i,j⟩ • E i) = D i • E i
    rw [Finset.sum_nsmul_assoc,hP d hd i]
  simpa only [he,RingHom.comp_apply] using hh

end PhilipponMultiplicity.AtlasSupport
end
end

section
-- Reused implementation: Solutions.PhilipponFiniteBasicCover

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity

theorem finite_polynomial_nonzero_cover {K σ X ι : Type*} [Field K] [Finite σ]
    (P : ι → MvPolynomial σ K) (v : X → σ → K)
    (hcover : ∀ x, ∃ i, MvPolynomial.eval (v x) (P i) ≠ 0) :
    ∃ t : Finset ι, ∀ x, ∃ i ∈ t, MvPolynomial.eval (v x) (P i) ≠ 0 := by
  classical
  obtain ⟨s,hs,hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := MvPolynomial σ K) (Set.range P)).mp
      (IsNoetherian.noetherian (Ideal.span (Set.range P)))
  choose ind hind using (fun q : s => hs q.property)
  let t : Finset ι := Finset.univ.image ind
  refine ⟨t,?_⟩
  intro x
  by_contra hx
  push Not at hx
  have hle : Ideal.span (Set.range P) ≤ RingHom.ker (MvPolynomial.eval (v x)) := by
    change Ideal.span (Set.range P) = Ideal.span (s : Set (MvPolynomial σ K)) at hspan
    rw [hspan]
    apply Ideal.span_le.mpr
    intro q hq
    change MvPolynomial.eval (v x) q = 0
    have hi : P (ind ⟨q,hq⟩) = q := hind ⟨q,hq⟩
    rw [← hi]
    exact hx (ind ⟨q,hq⟩) (Finset.mem_image.mpr ⟨⟨q,hq⟩,Finset.mem_univ _,rfl⟩)
  obtain ⟨i,hi⟩ := hcover x
  exact hi (hle (Ideal.subset_span (Set.mem_range_self i)))

namespace MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem finite_open_subcover {X ι : Type*} (e : X → M.Point)
    (U : ι → Set M.Point) (hU : ∀ i, @IsOpen _ M.zariskiTopology (U i))
    (hcover : ∀ x, ∃ i, e x ∈ U i) :
    ∃ t : Finset ι, ∀ x, ∃ i ∈ t, e x ∈ U i := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  choose ind hind using hcover
  have hbasic (x : X) : ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
      M.eval P (e x) ≠ 0 ∧ {p : M.Point | M.eval P p ≠ 0} ⊆ U (ind x) := by
    obtain ⟨V,⟨P,D,hP,rfl⟩,hx,hV⟩ :=
      M.isTopologicalBasis_basic.exists_subset_of_mem_open (hind x) (hU (ind x))
    exact ⟨P,D,hP,hx,hV⟩
  choose P D hP hx hPU using hbasic
  obtain ⟨s,hs⟩ := finite_polynomial_nonzero_cover P (fun x => M.coordinate (e x))
    (fun x => ⟨x,hx x⟩)
  refine ⟨s.image ind,?_⟩
  intro x
  obtain ⟨y,hy,hyx⟩ := hs x
  exact ⟨ind y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,hPU y hyx⟩

end MultiProjectiveSpace
end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponPolynomialMapCharts

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K] {X : Type u}
  {M N : MultiProjectiveSpace K} {e : X → M.Point} {f : X → N.Point}

structure PolynomialMapChart (M N : MultiProjectiveSpace K)
    {X : Type u} (e : X → M.Point) (f : X → N.Point) (b : N.FactorIndex) where
  cut : M.CoordinateRing
  cutDegree : M.FactorIndex → ℕ
  cut_homogeneous : M.IsHomogeneous cut cutDegree
  degree : M.FactorIndex → ℕ
  coordinates : Fin (N.ambientDimension b + 1) → M.CoordinateRing
  homogeneous : ∀ j, M.IsHomogeneous (coordinates j) degree
  zero_off : ∀ x, M.eval cut (e x) = 0 → ∀ j, M.eval (coordinates j) (e x) = 0
  represents : ∀ x, M.eval cut (e x) ≠ 0 →
    ∃ h : (fun j => M.eval (coordinates j) (e x)) ≠ 0,
      Projectivization.mk K (fun j => M.eval (coordinates j) (e x)) h = f x b

theorem IsRegularAlong.exists_polynomialMapChart (hf : M.IsRegularAlong N e f)
    (x : X) (b : N.FactorIndex) :
    ∃ chart : PolynomialMapChart M N e f b, M.eval chart.cut (e x) ≠ 0 := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  obtain ⟨U,hU,hx,D,P,hP,hrep⟩ := hf x b
  obtain ⟨V,⟨q,E,hq,rfl⟩,hxq,hqU⟩ :=
    M.isTopologicalBasis_basic.exists_subset_of_mem_open hx hU
  let chart : PolynomialMapChart M N e f b :=
    { cut := q
      cutDegree := E
      cut_homogeneous := hq
      degree := E+D
      coordinates := fun j => q * P j
      homogeneous := fun j => hq.mul M (hP j)
      zero_off := by
        intro y hy j
        simp only [eval,map_mul] at hy ⊢
        rw [hy,zero_mul]
      represents := by
        intro y hy
        obtain ⟨hn,heq⟩ := hrep y (hqU hy)
        have hval : (fun j => M.eval (q * P j) (e y)) =
            M.eval q (e y) • (fun j => M.eval (P j) (e y)) := by
          funext j
          simp only [eval,map_mul,Pi.smul_apply,smul_eq_mul]
        have hn' : (fun j => M.eval (q * P j) (e y)) ≠ 0 := by
          rw [hval]
          exact smul_ne_zero hy hn
        exact ⟨hn',((Projectivization.mk_eq_mk_iff' K _ _ hn' hn).mpr
          ⟨M.eval q (e y),hval.symm⟩).trans heq⟩ }
  exact ⟨chart,hxq⟩

theorem IsRegularAlong.exists_finite_polynomialMapCharts (hf : M.IsRegularAlong N e f)
    (b : N.FactorIndex) :
    ∃ charts : Finset (PolynomialMapChart M N e f b),
      ∀ x, ∃ chart ∈ charts, M.eval chart.cut (e x) ≠ 0 := by
  classical
  exact finite_polynomial_nonzero_cover (fun chart : PolynomialMapChart M N e f b => chart.cut)
    (fun x => M.coordinate (e x)) (fun x => hf.exists_polynomialMapChart x b)

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
-- Reused implementation: Solutions.PhilipponBoundedAdditionCharts

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

namespace EmbeddedCommutativeGroup

def additionSource (E : EmbeddedCommutativeGroup K) (xy : E.Point × E.Point) :
    (projectiveSquare K E.ambientDimension).Point :=
  fun i => if i.val = 0 then xy.1.val else xy.2.val

abbrev AdditionPolynomialChart (E : EmbeddedCommutativeGroup K) :=
  MultiProjectiveSpace.PolynomialMapChart (projectiveSquare K E.ambientDimension)
    (projectiveSpace K E.ambientDimension) E.additionSource
    (fun xy : E.Point × E.Point => fun _ => (xy.1 + xy.2).val) ⟨0,by change 0 < 1; decide⟩

theorem exists_finite_bounded_addition_charts (E : EmbeddedCommutativeGroup K) :
    ∃ c : ℕ, 1 ≤ c ∧ ∃ charts : Finset E.AdditionPolynomialChart,
      (∀ chart ∈ charts, ∀ i, chart.degree i ≤ c) ∧
      ∀ xy : E.Point × E.Point, ∃ chart ∈ charts,
        (projectiveSquare K E.ambientDimension).eval chart.cut (E.additionSource xy) ≠ 0 := by
  classical
  obtain ⟨charts,hcover⟩ := E.addition_regular.exists_finite_polynomialMapCharts
    ⟨0,by change 0 < 1; decide⟩
  let c : ℕ := 1 + ∑ chart ∈ charts, ∑ i, chart.degree i
  refine ⟨c,by dsimp [c]; omega,charts,?_,hcover⟩
  intro chart hchart i
  have hinner : chart.degree i ≤ ∑ j, chart.degree j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (chart.degree j)) (Finset.mem_univ i)
  have houter : (∑ j, chart.degree j) ≤ ∑ ch ∈ charts, ∑ j, ch.degree j :=
    Finset.single_le_sum (fun ch _ => Nat.zero_le (∑ j, ch.degree j)) hchart
  exact hinner.trans (houter.trans (Nat.le_add_left _ _))

end EmbeddedCommutativeGroup
end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponAdditionSubstitution

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AtlasSupport
universe u
variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (g : G.Point)

abbrev factorSquare (i : G.FactorIndex) := projectiveSquare K (G.factor i).ambientDimension

def firstBlock (i : G.FactorIndex) : (factorSquare i).FactorIndex :=
  ⟨0,by change 0 < 2; decide⟩

def pairSubstitutionCoordinate (i : G.FactorIndex) (v : (factorSquare i).Variable) :
    MvPolynomial G.ambient.Variable (AnalyticCoefficientRing A) :=
  if v.1.val = 0 then X ⟨i,v.2⟩ else C (fun z => A.lift g z ⟨i,v.2⟩)

def pairSubstitution (i : G.FactorIndex) : (factorSquare i).CoordinateRing →+*
    MvPolynomial G.ambient.Variable (AnalyticCoefficientRing A) :=
  eval₂Hom (C.comp (Pi.constRingHom A.ParameterSpace K)) (pairSubstitutionCoordinate A g i)

def pairLift (i : G.FactorIndex) (x : G.Point) (z : A.ParameterSpace)
    (v : (factorSquare i).Variable) : K :=
  if v.1.val = 0 then (G.embedding x i).rep v.2 else A.lift g z ⟨i,v.2⟩

theorem evaluate_pairSubstitution (i : G.FactorIndex) (P : (factorSquare i).CoordinateRing)
    (x : G.Point) (z : A.ParameterSpace) :
    evaluateCoefficientPolynomial A (pairSubstitution A g i P) x z =
      MvPolynomial.eval (pairLift A g i x z) P := by
  change eval₂Hom _ _ (eval₂Hom _ _ P) = eval₂Hom (RingHom.id K) _ P
  rw [map_eval₂Hom]
  congr 2
  · ext a
    simp
  · funext v
    by_cases hv : v.1.val = 0
    · simp [pairSubstitutionCoordinate,pairLift,hv,MultiProjectiveSpace.coordinate]
    · simp [pairSubstitutionCoordinate,pairLift,hv]

theorem pairSubstitution_coeff_analytic (i : G.FactorIndex)
    (P : (factorSquare i).CoordinateRing) (e : G.ambient.Variable →₀ ℕ) :
    AnalyticAt K ((pairSubstitution A g i P).coeff e) 0 := by
  apply substitution_coeff_analytic
  intro v d
  by_cases hv : v.1.val = 0
  · simp only [pairSubstitutionCoordinate,if_pos hv,coeff_X]
    split_ifs <;> exact analyticAt_const
  · simp only [pairSubstitutionCoordinate,if_neg hv,coeff_C]
    split_ifs
    · exact A.lift_analytic g _
    · exact analyticAt_const

theorem pairSubstitution_homogeneous (i : G.FactorIndex)
    (P : (factorSquare i).CoordinateRing) (D : (factorSquare i).FactorIndex → ℕ)
    (hP : (factorSquare i).IsHomogeneous P D) :
    (pairSubstitution A g i P).IsWeightedHomogeneous
      (Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension)
      (Pi.single i (D (firstBlock i))) := by
  classical
  let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
  let E : (factorSquare i).FactorIndex → G.FactorIndex → ℕ :=
    fun b => if b.val = 0 then Pi.single i 1 else 0
  have hQ (v : (factorSquare i).Variable) :
      (pairSubstitutionCoordinate A g i v).IsWeightedHomogeneous w (E v.1) := by
    by_cases hv : v.1.val = 0
    · simp only [pairSubstitutionCoordinate,E,if_pos hv]
      exact isWeightedHomogeneous_X (AnalyticCoefficientRing A) w ⟨i,v.2⟩
    · simp only [pairSubstitutionCoordinate,E,if_neg hv]
      exact isWeightedHomogeneous_C w _
  have hh := homogeneous_substitution (factorSquare i) (Pi.constRingHom A.ParameterSpace K)
    w (pairSubstitutionCoordinate A g i) E hQ P D hP
  have he : (∑ b, D b • E b) = Pi.single i (D (firstBlock i)) := by
    funext k
    change (∑ b : Fin 2, D b * E b k) = _
    rw [Fin.sum_univ_two]
    simp [E,firstBlock,factorSquare,projectiveSquare,Pi.single_apply]
  simpa only [he,w,pairSubstitution] using hh

def specializationAtZero (i : G.FactorIndex) (P : (factorSquare i).CoordinateRing) :
    G.CoordinateRing :=
  MvPolynomial.map (Pi.evalRingHom (fun _ : A.ParameterSpace => K) 0) (pairSubstitution A g i P)

theorem specializationAtZero_eval (i : G.FactorIndex) (P : (factorSquare i).CoordinateRing)
    (x : G.Point) :
    G.ambient.eval (specializationAtZero A g i P) (G.embedding x) =
      MvPolynomial.eval (pairLift A g i x 0) P := by
  rw [← evaluate_pairSubstitution A g i P x 0]
  exact (eval₂_eq_eval_map _ _ _).symm

theorem specializationAtZero_homogeneous (i : G.FactorIndex)
    (P : (factorSquare i).CoordinateRing) (D : (factorSquare i).FactorIndex → ℕ)
    (hP : (factorSquare i).IsHomogeneous P D) :
    G.ambient.IsHomogeneous (specializationAtZero A g i P) (Pi.single i (D (firstBlock i))) := by
  classical
  intro e he k
  have he' : (pairSubstitution A g i P).coeff e ≠ 0 := by
    intro hz
    have hn := mem_support_iff.mp he
    simp only [specializationAtZero,coeff_map,hz,map_zero,ne_eq,not_true_eq_false] at hn
  exact (G.ambient.blockWeight_apply e k).symm.trans
    (congrFun (pairSubstitution_homogeneous A g i P D hP he') k)

end PhilipponMultiplicity.AtlasSupport
end
end

section
-- Reused implementation: Solutions.PhilipponRegularMapComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set MvPolynomial
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem homogeneous_tuple_lift {ι : Type*} (M : MultiProjectiveSpace K)
    (p : M.Point) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) D)
    (hn : (fun j => M.eval (P j) p) ≠ 0) :
    ∃ h : (fun j => MvPolynomial.eval v (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval v (P j)) h =
        Projectivization.mk K (fun j => M.eval (P j) p) hn := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  let b : K := ∏ i, (a i : K) ^ D i
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ (a i).ne_zero)
  have heval : (fun j => MvPolynomial.eval v (P j)) = b • (fun j => M.eval (P j) p) := by
    funext j
    rw [hv', M.eval_block_scale (P j) D (hP j) (M.coordinate p) (fun i => (a i : K))]
    rfl
  have hn' : (fun j => MvPolynomial.eval v (P j)) ≠ 0 := by
    rw [heval]
    exact smul_ne_zero hb hn
  exact ⟨hn', (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨b, heval.symm⟩⟩

theorem IsRegularAlong.comp {X : Type u} {M N Q : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} {g : X → Q.Point}
    (hf : M.IsRegularAlong N e f) (hg : N.IsRegularAlong Q f g) :
    M.IsRegularAlong Q e g := by
  classical
  let := M.zariskiTopology
  let := N.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  intro x b
  obtain ⟨U, hU, hxU, D, P, hP, hPlift⟩ := hg x b
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp (hU.preimage hf.continuous)
  choose W hW hxW E R hR hRlift using hf x
  let pull (j : Fin (Q.ambientDimension b + 1)) :=
    eval₂ C (fun t : N.Variable => R t.1 t.2) (P j)
  refine ⟨V ∩ ⋂ a, W a, hV.inter (isOpen_iInter_of_finite hW),
    ⟨?_, mem_iInter.mpr hxW⟩, (fun i => ∑ a, D a * E a i), pull, ?_, ?_⟩
  · have hx : x ∈ f ⁻¹' U := hxU
    rwa [← hVeq] at hx
  · intro j
    exact (hP j).eval₂_blocks M N _ E (fun t => hR t.1 t.2)
  · intro y hy
    have hyU : f y ∈ U := by
      change y ∈ f ⁻¹' U
      rw [← hVeq]
      exact hy.1
    obtain ⟨hn, heq⟩ := hPlift y hyU
    have hlift (a : N.FactorIndex) := hRlift a y (mem_iInter.mp hy.2 a)
    obtain ⟨hn', heq'⟩ := N.homogeneous_tuple_lift (f y)
      (fun t : N.Variable => M.eval (R t.1 t.2) (e y)) hlift P D hP hn
    have heval (j) : M.eval (pull j) (e y) =
        MvPolynomial.eval (fun t : N.Variable => M.eval (R t.1 t.2) (e y)) (P j) := by
      dsimp only [eval, pull]
      rw [← eval_assoc]
      rfl
    simpa only [heval] using ⟨hn', heq'.trans heq⟩

end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section
-- Reused implementation: Solutions.PhilipponPolynomialChartLifts

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K] {X : Type u}
  {M N : MultiProjectiveSpace K} {e : X → M.Point} {f : X → N.Point}
  {b : N.FactorIndex}

theorem PolynomialMapChart.represents_lift (chart : PolynomialMapChart M N e f b)
    (x : X) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = e x i)
    (hcut : MvPolynomial.eval v chart.cut ≠ 0) :
    ∃ h : (fun j => MvPolynomial.eval v (chart.coordinates j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval v (chart.coordinates j)) h = f x b := by
  have hc : M.eval chart.cut (e x) ≠ 0 :=
    (M.eval_eq_zero_iff_of_lift (e x) v hv chart.cut chart.cutDegree chart.cut_homogeneous).not.mp hcut
  obtain ⟨hn,heq⟩ := chart.represents x hc
  obtain ⟨hn',heq'⟩ := M.homogeneous_tuple_lift (e x) v hv chart.coordinates chart.degree chart.homogeneous hn
  exact ⟨hn',heq'.trans heq⟩

theorem PolynomialMapChart.compatible_lifts (chart : PolynomialMapChart M N e f b)
    (x : X) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = e x i)
    (w : Fin (N.ambientDimension b + 1) → K) (hw : w ≠ 0)
    (hwrep : Projectivization.mk K w hw = f x b) :
    ∀ j k, MvPolynomial.eval v (chart.coordinates j) * w k =
      MvPolynomial.eval v (chart.coordinates k) * w j := by
  by_cases hcut : MvPolynomial.eval v chart.cut = 0
  · have hc := (M.eval_eq_zero_iff_of_lift (e x) v hv chart.cut chart.cutDegree
      chart.cut_homogeneous).mp hcut
    have hz (j) : MvPolynomial.eval v (chart.coordinates j) = 0 :=
      (M.eval_eq_zero_iff_of_lift (e x) v hv (chart.coordinates j) chart.degree
        (chart.homogeneous j)).mpr (chart.zero_off x hc j)
    intro j k
    rw [hz j,hz k,zero_mul,zero_mul]
  · obtain ⟨hn,heq⟩ := chart.represents_lift x v hv hcut
    exact (projectivization_mk_eq_iff_cross _ _ hn hw).mp (heq.trans hwrep.symm)

end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section
-- Reused implementation: Solutions.PhilipponAdditionChartGerms

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AtlasSupport
universe u
variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (g : G.Point)

theorem pairLift_evaluation_analytic (i : G.FactorIndex)
    (P : (factorSquare i).CoordinateRing) (x : G.Point) :
    AnalyticAt K (fun z => MvPolynomial.eval (pairLift A g i x z) P) 0 := by
  apply AnalyticAt.aeval_mvPolynomial
  intro v
  by_cases hv : v.1.val = 0
  · simp only [pairLift,if_pos hv]
    exact analyticAt_const
  · simpa only [pairLift,if_neg hv] using A.lift_analytic g ⟨i,v.2⟩

theorem liftAtZero_represents (i : G.FactorIndex) :
    ∃ h : (fun j => A.lift g 0 ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => A.lift g 0 ⟨i,j⟩) h = G.embedding g i := by
  obtain ⟨hz,hi⟩ := (A.lift_represents g).self_of_nhds
  have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
  rw [hz',A.map_zero,add_zero] at hi
  exact hi i

theorem pairLift_represents (i : G.FactorIndex) (x : G.Point) (z : A.ParameterSpace)
    (y : G.Point)
    (hy : ∃ h : (fun j => A.lift g z ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => A.lift g z ⟨i,j⟩) h = G.embedding y i) :
    ∀ b : (factorSquare i).FactorIndex,
      ∃ h : (fun j => pairLift A g i x z ⟨b,j⟩) ≠ 0,
        Projectivization.mk K (fun j => pairLift A g i x z ⟨b,j⟩) h =
          (G.factor i).additionSource (x i,y i) b := by
  intro b
  by_cases hb : b.val = 0
  · simp only [pairLift,EmbeddedCommutativeGroup.additionSource,if_pos hb]
    exact ⟨(G.embedding x i).rep_nonzero,(G.embedding x i).mk_rep⟩
  · simp only [pairLift,EmbeddedCommutativeGroup.additionSource,if_neg hb]
    exact hy

def factorChartDomain (i : G.FactorIndex) (chart : (G.factor i).AdditionPolynomialChart) :
    Set G.Point :=
  {x | G.ambient.eval (specializationAtZero A g i chart.cut) (G.embedding x) ≠ 0}

theorem factorChartDomain_isOpen (i : G.FactorIndex) (chart : (G.factor i).AdditionPolynomialChart) :
    @IsOpen _ G.zariskiTopology (factorChartDomain A g i chart) := by
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact (G.ambient.isOpen_basic _ _
    (specializationAtZero_homogeneous A g i chart.cut chart.cutDegree chart.cut_homogeneous)).preimage
      (continuous_induced_dom : @Continuous _ _ G.zariskiTopology G.ambient.zariskiTopology G.embedding)

theorem mem_factorChartDomain (i : G.FactorIndex) (chart : (G.factor i).AdditionPolynomialChart)
    (x : G.Point)
    (hx : (factorSquare i).eval chart.cut ((G.factor i).additionSource (x i,g i)) ≠ 0) :
    x ∈ factorChartDomain A g i chart := by
  change G.ambient.eval (specializationAtZero A g i chart.cut) (G.embedding x) ≠ 0
  rw [specializationAtZero_eval]
  exact ((factorSquare i).eval_eq_zero_iff_of_lift _ (pairLift A g i x 0)
    (pairLift_represents A g i x 0 g (liftAtZero_represents A g i))
    chart.cut chart.cutDegree chart.cut_homogeneous).not.mpr hx

theorem factorChart_represents (i : G.FactorIndex) (chart : (G.factor i).AdditionPolynomialChart)
    (x : G.Point) (hx : x ∈ factorChartDomain A g i chart) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      ∃ h : (fun j => MvPolynomial.eval (pairLift A g i x z) (chart.coordinates j)) ≠ 0,
        Projectivization.mk K (fun j => MvPolynomial.eval (pairLift A g i x z) (chart.coordinates j)) h =
          G.embedding (x+g+A.map ⟨z,hz⟩) i := by
  have hx' : MvPolynomial.eval (pairLift A g i x 0) chart.cut ≠ 0 := by
    rw [← specializationAtZero_eval]
    exact hx
  have hnear := (pairLift_evaluation_analytic A g i chart.cut x).continuousAt.eventually_ne hx'
  filter_upwards [hnear,A.lift_represents g] with z hz hrep
  obtain ⟨hzA,hL⟩ := hrep
  obtain ⟨hn,heq⟩ := chart.represents_lift (x i,(g+A.map ⟨z,hzA⟩) i)
    (pairLift A g i x z) (pairLift_represents A g i x z _ (hL i)) hz
  refine ⟨hzA,hn,?_⟩
  simpa only [EmbeddedGroupProduct.embedding,Pi.add_apply,add_assoc] using heq

theorem factorChart_compatible (i : G.FactorIndex) (chart : (G.factor i).AdditionPolynomialChart)
    (x : G.Point) (j k : Fin (G.ambient.ambientDimension i + 1)) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      MvPolynomial.eval (pairLift A g i x z) (chart.coordinates j) * A.lift (g+x) z ⟨i,k⟩ =
        MvPolynomial.eval (pairLift A g i x z) (chart.coordinates k) * A.lift (g+x) z ⟨i,j⟩ := by
  filter_upwards [A.lift_represents g,A.lift_represents (g+x)] with z hg hgx
  obtain ⟨hz,hL⟩ := hg
  obtain ⟨hz',hL'⟩ := hgx
  have hzeq : (⟨z,hz'⟩ : A.domain) = ⟨z,hz⟩ := Subtype.ext rfl
  rw [hzeq] at hL'
  obtain ⟨hn,heq⟩ := hL' i
  apply chart.compatible_lifts (x i,(g+A.map ⟨z,hz⟩) i) (pairLift A g i x z)
    (pairLift_represents A g i x z _ (hL i)) (fun l => A.lift (g+x) z ⟨i,l⟩) hn ?_ j k
  change Projectivization.mk K (fun l : Fin (G.ambient.ambientDimension i + 1) =>
    A.lift (g+x) z ⟨i,l⟩) hn = (x i + (g i + A.map ⟨z,hz⟩ i)).val
  simpa only [EmbeddedGroupProduct.embedding,Pi.add_apply,add_assoc,add_left_comm] using heq

end PhilipponMultiplicity.AtlasSupport
end
end

section
-- Reused implementation: Solutions.PhilipponBoundedTranslationAtlas

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AtlasSupport
universe u
variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (g : G.Point)

def assembledTranslationChart (charts : ∀ i, (G.factor i).AdditionPolynomialChart) :
    TranslationChart A g where
  domain := ⋂ i, factorChartDomain A g i (charts i)
  domain_isOpen := by
    letI : TopologicalSpace G.Point := G.zariskiTopology
    exact isOpen_iInter_of_finite (fun i => factorChartDomain_isOpen A g i (charts i))
  degree i := (charts i).degree (firstBlock i)
  coordinates v := pairSubstitution A g v.1 ((charts v.1).coordinates v.2)
  coefficient_analytic v e _ := pairSubstitution_coeff_analytic A g v.1 _ e
  coordinate_homogeneous := by
    intro v e he
    have hh := pairSubstitution_homogeneous A g v.1 ((charts v.1).coordinates v.2)
      (charts v.1).degree ((charts v.1).homogeneous v.2) (mem_support_iff.mp he)
    have hd (i : G.FactorIndex) := (G.ambient.blockWeight_apply e i).symm.trans (congrFun hh i)
    refine ⟨?_,?_⟩
    · simpa only [Pi.single_eq_same] using hd v.1
    · intro i hi
      simpa only [Pi.single_apply,if_neg hi] using hd i
  coordinate_compatible := by
    intro x i j k
    simpa only [evaluate_pairSubstitution] using factorChart_compatible A g i (charts i) x j k
  represents := by
    intro x hx
    have hh : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ i,
        ∃ hz : z ∈ A.domain,
        ∃ h : (fun j => MvPolynomial.eval (pairLift A g i x z) ((charts i).coordinates j)) ≠ 0,
          Projectivization.mk K
            (fun j => MvPolynomial.eval (pairLift A g i x z) ((charts i).coordinates j)) h =
              G.embedding (x+g+A.map ⟨z,hz⟩) i :=
      Filter.eventually_all.mpr (fun i => factorChart_represents A g i (charts i) x (Set.mem_iInter.mp hx i))
    filter_upwards [hh,A.domain_open.mem_nhds A.zero_mem] with z hrep hz
    refine ⟨hz,?_⟩
    intro i
    obtain ⟨hzi,hn,heq⟩ := hrep i
    have hzeq : (⟨z,hzi⟩ : A.domain) = ⟨z,hz⟩ := Subtype.ext rfl
    rw [hzeq] at heq
    simp only [evaluate_pairSubstitution]
    exact ⟨hn,heq⟩

theorem exists_uniformly_bounded_translation_atlas :
    ∃ c : EmbeddedCommutativeGroup K → ℕ, (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point),
        ∃ atlas : TranslationAtlas A g, atlas.IsBoundedBy (fun i => c (G.factor i)) := by
  classical
  choose c hc charts hbound hcover using
    (fun E : EmbeddedCommutativeGroup K => E.exists_finite_bounded_addition_charts)
  refine ⟨c,hc,?_⟩
  intro G A g
  let Index : Type u := ∀ i : G.FactorIndex, {chart : (G.factor i).AdditionPolynomialChart // chart ∈ charts (G.factor i)}
  let atlas : TranslationAtlas A g :=
    { Index := Index
      chart := fun a => assembledTranslationChart A g (fun i => (a i).val)
      covers := by
        intro x
        choose ch hch hx using (fun i => hcover (G.factor i) (x i,g i))
        refine ⟨(fun i => ⟨ch i,hch i⟩),Set.mem_iInter.mpr ?_⟩
        intro i
        exact mem_factorChartDomain A g i (ch i) x (hx i) }
  refine ⟨atlas,?_⟩
  intro a i
  exact hbound (G.factor i) (a i).val (a i).property (firstBlock i)

end PhilipponMultiplicity.AtlasSupport
end
end

section
-- Reused implementation: Solutions.PhilipponProjectiveNullstellensatz

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneousIdeal_eq_span (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) : M.IsHomogeneousIdeal I := by
  classical
  apply le_antisymm
  · intro P hP
    let w := Hilbert.blockWeight M.factorCount M.ambientDimension
    rw [← sum_weightedHomogeneousComponent w P,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) P)]
    apply Ideal.sum_mem
    intro D _
    exact Ideal.subset_span ⟨hI P hP D, D,
      (M.degreePiece_iff _ D).mp (weightedHomogeneousComponent_mem w P D)⟩
  · exact Ideal.span_le.mpr (fun _ h => h.1)

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section
-- Reused implementation: Solutions.PhilipponProjectiveTranslations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K] {n : ℕ}

def projectiveLeftSlice (a : Projectivization K (Fin (n + 1) → K))
    (p : (projectiveSpace K n).Point) : (projectiveSquare K n).Point :=
  fun b => if b.val = 0 then p (0 : Fin 1) else a

def projectiveLeftSlicePolynomial (a : Projectivization K (Fin (n + 1) → K))
    (v : (projectiveSquare K n).Variable) : (projectiveSpace K n).CoordinateRing :=
  if v.1.val = 0 then X ⟨(0 : Fin 1), v.2⟩ else C (a.rep v.2)

theorem projectiveLeftSlicePolynomial_homogeneous
    (a : Projectivization K (Fin (n + 1) → K)) (v : (projectiveSquare K n).Variable) :
    (projectiveSpace K n).IsHomogeneous (projectiveLeftSlicePolynomial a v)
      (fun _ => if v.1.val = 0 then 1 else 0) := by
  classical
  by_cases hv : v.1.val = 0
  · simp only [projectiveLeftSlicePolynomial, if_pos hv]
    convert (projectiveSpace K n).isHomogeneous_X ⟨(0 : Fin 1), v.2⟩ using 1
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    simp [hi]
  · simpa only [projectiveLeftSlicePolynomial, if_neg hv] using!
      (projectiveSpace K n).isHomogeneous_C (a.rep v.2)

theorem projectiveLeftSlice_eval (a : Projectivization K (Fin (n + 1) → K))
    (P : (projectiveSquare K n).CoordinateRing) (p : (projectiveSpace K n).Point) :
    (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p =
      (projectiveSquare K n).eval P (projectiveLeftSlice a p) := by
  dsimp only [MultiProjectiveSpace.eval]
  rw [← eval_assoc]
  apply congrArg (fun v => MvPolynomial.eval v P)
  funext v
  by_cases hv : v.1.val = 0 <;>
    simp [projectiveLeftSlicePolynomial, projectiveLeftSlice,
      MultiProjectiveSpace.coordinate, hv]

theorem projectiveLeftSlice_continuous (a : Projectivization K (Fin (n + 1) → K)) :
    @Continuous _ _ (projectiveSpace K n).zariskiTopology
      (projectiveSquare K n).zariskiTopology (projectiveLeftSlice a) := by
  classical
  let := (projectiveSpace K n).zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩
  have heq : projectiveLeftSlice a ⁻¹' {p | (projectiveSquare K n).eval P p ≠ 0} =
      {p | (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p ≠ 0} := by
    ext p
    change (projectiveSquare K n).eval P (projectiveLeftSlice a p) ≠ 0 ↔
      (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p ≠ 0
    rw [projectiveLeftSlice_eval]
  rw [heq]
  apply (projectiveSpace K n).isOpen_basic
  exact hP.eval₂_blocks _ _ _ (fun b _ => if b.val = 0 then 1 else 0)
    (projectiveLeftSlicePolynomial_homogeneous a)

theorem MultiProjectiveSpace.IsRegularAlong.of_left_slice
    {X : Type u} (N : MultiProjectiveSpace K)
    (a : Projectivization K (Fin (n + 1) → K))
    {e : X → (projectiveSpace K n).Point} {f : X → N.Point}
    (hf : (projectiveSquare K n).IsRegularAlong N (projectiveLeftSlice a ∘ e) f) :
    (projectiveSpace K n).IsRegularAlong N e f := by
  classical
  let := (projectiveSpace K n).zariskiTopology
  let := (projectiveSquare K n).zariskiTopology
  intro x b
  obtain ⟨U, hU, hxU, D, P, hP, hlift⟩ := hf x b
  refine ⟨projectiveLeftSlice a ⁻¹' U, hU.preimage (projectiveLeftSlice_continuous a),
    hxU, (fun i => ∑ c, D c * (if c.val = 0 then 1 else 0)),
    (fun j => eval₂ C (projectiveLeftSlicePolynomial a) (P j)), ?_, ?_⟩
  · intro j
    exact (hP j).eval₂_blocks _ _ _ (fun c _ => if c.val = 0 then 1 else 0)
      (projectiveLeftSlicePolynomial_homogeneous a)
  · intro y hy
    obtain ⟨hn, heq⟩ := hlift y hy
    simpa only [projectiveLeftSlice_eval, Function.comp_apply] using ⟨hn, heq⟩

theorem EmbeddedCommutativeGroup.translation_regular
    (G : EmbeddedCommutativeGroup K) (a : G.Point) :
    (projectiveSpace K G.ambientDimension).IsRegularAlong
      (projectiveSpace K G.ambientDimension)
      (fun x : G.Point => fun _ => x.val)
      (fun x => fun _ => (x + a).val) := by
  apply MultiProjectiveSpace.IsRegularAlong.of_left_slice _ a.val
  exact G.addition_regular.comp_domain (fun x : G.Point => (x, a))

end PhilipponMultiplicity
end
end

section
-- Reused implementation: Solutions.PhilipponProductRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set MvPolynomial
open scoped Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

theorem MultiProjectiveSpace.projection_regular (M : MultiProjectiveSpace K)
    (i : M.FactorIndex) :
    M.IsRegularAlong (projectiveSpace K (M.ambientDimension i)) id (fun p _ => p i) := by
  let := M.zariskiTopology
  intro x b
  refine ⟨univ, isOpen_univ, mem_univ _, (fun a => if a = i then 1 else 0),
    (fun j => X ⟨i, j⟩), (fun j => M.isHomogeneous_X ⟨i, j⟩), ?_⟩
  intro y _
  simp only [MultiProjectiveSpace.eval, eval_X, MultiProjectiveSpace.coordinate, id_eq]
  exact ⟨Projectivization.rep_nonzero (y i), Projectivization.mk_rep (y i)⟩

theorem EmbeddedGroupProduct.translation_regular (G : EmbeddedGroupProduct K) (a : G.Point) :
    G.ambient.IsRegularAlong G.ambient G.embedding (fun x => G.embedding (x + a)) := by
  intro x b
  have hp := (G.ambient.projection_regular b).comp_domain G.embedding
  have ht := ((G.factor b).translation_regular (a b)).comp_domain (fun y : G.Point => y b)
  obtain ⟨U, hU, hx, D, P, hP, hl⟩ := (hp.comp ht) x (0 : Fin 1)
  exact ⟨U, hU, hx, D, P, hP, hl⟩

theorem EmbeddedGroupProduct.negation_regular (G : EmbeddedGroupProduct K) :
    G.ambient.IsRegularAlong G.ambient G.embedding (fun x => G.embedding (-x)) := by
  intro x b
  have hp := (G.ambient.projection_regular b).comp_domain G.embedding
  have hn := (G.factor b).negation_regular.comp_domain (fun y : G.Point => y b)
  obtain ⟨U, hU, hx, D, P, hP, hl⟩ := (hp.comp hn) x (0 : Fin 1)
  exact ⟨U, hU, hx, D, P, hP, hl⟩

end PhilipponMultiplicity
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

end PhilipponMultiplicity.FiniteDifference

end
end

section
-- Reused implementation: Solutions.PhilipponHilbertDimension

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ComponentDegree
variable {ι : Type*} [Fintype ι]

theorem shift_top (D : ι → ℚ) (F : MvPolynomial ι ℚ) :
    homogeneousComponent F.totalDegree (FiniteDifference.shift D F) =
      homogeneousComponent F.totalDegree F ∧
    (FiniteDifference.shift D F).totalDegree = F.totalDegree := by
  classical
  by_cases hz : F.totalDegree = 0
  · have hc := totalDegree_eq_zero_iff_eq_C.mp hz
    rw [hc]
    simp [FiniteDifference.shift]
  · have hp : 0 < F.totalDegree := Nat.pos_of_ne_zero hz
    have hdiff := (FiniteDifference.top_difference D F F.totalDegree hp le_rfl).1
    have hzero : homogeneousComponent F.totalDegree (F - FiniteDifference.shift D F) = 0 :=
      homogeneousComponent_eq_zero _ _ (by omega)
    rw [map_sub, sub_eq_zero] at hzero
    refine ⟨hzero.symm, le_antisymm ?_ ?_⟩
    · have heq : FiniteDifference.shift D F = F - (F - FiniteDifference.shift D F) := by abel
      nth_rw 1 [heq]
      exact (totalDegree_sub _ _).trans (max_le le_rfl (by omega))
    · by_contra hlt
      have hc := homogeneousComponent_eq_zero F.totalDegree (FiniteDifference.shift D F)
        (lt_of_not_ge hlt)
      rw [← hzero] at hc
      have ht : homogeneousComponent F.totalDegree F ≠ 0 := by
        have hne : F ≠ 0 := by intro h; apply hz; rw [h, totalDegree_zero]
        obtain ⟨e, he, hed⟩ := Finset.exists_mem_eq_sup F.support
          (support_nonempty.mpr hne) Finsupp.degree
        change F.totalDegree = e.degree at hed
        intro h
        have hx := congrArg (coeff e) h
        rw [coeff_homogeneousComponent, if_pos hed.symm, coeff_zero] at hx
        exact (mem_support_iff.mp he) hx
      exact ht hc

end PhilipponMultiplicity.ComponentDegree

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponIrrelevantHilbert

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_mem_blockIdeal (i : M.FactorIndex) (d : M.FactorIndex → ℕ)
    (hd : 0 < d i) (P : M.CoordinateRing) (hP : M.IsHomogeneous P d) :
    P ∈ blockIdeal K M.factorCount M.ambientDimension i := by
  classical
  have hset : Set.range (fun j : Fin (M.ambientDimension i + 1) =>
        (X ⟨i, j⟩ : M.CoordinateRing)) =
      X '' {x : M.Variable | x.1 = i} := by
    ext f
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨⟨i, j⟩, rfl, rfl⟩
    · rintro ⟨⟨k, j⟩, hk, rfl⟩
      change k = i at hk
      subst k
      exact ⟨j, rfl⟩
  unfold blockIdeal
  rw [hset, mem_ideal_span_X_image]
  intro e he
  have hsum : ∑ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩ = d i := hP e he i
  have hsome : ∃ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩ ≠ 0 := by
    by_contra! h
    have hz : ∑ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩ = 0 := by simp [h]
    omega
  obtain ⟨j, hj⟩ := hsome
  exact ⟨⟨i, j⟩, rfl, hj⟩

theorem hilbertPolynomial_zero_of_blockIdeal_le (I : Ideal M.CoordinateRing)
    (i : M.FactorIndex) (hI : blockIdeal K M.factorCount M.ambientDimension i ≤ I) :
    hilbertPolynomial K M.factorCount M.ambientDimension I = 0 := by
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun _ => 1, fun d hd => ?_⟩
  have hz : quotientPiece K M.factorCount M.ambientDimension I d = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨P, hP, rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hI (homogeneous_mem_blockIdeal M i d (hd i) P ((M.degreePiece_iff P d).mp hP))
  rw [map_zero, hilbertFunction, hz, finrank_bot, Nat.cast_zero]

theorem irrelevant_prime_hilbertPolynomial_zero (Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hirr : ¬ IsRelevant K M.factorCount M.ambientDimension Q) :
    hilbertPolynomial K M.factorCount M.ambientDimension Q = 0 := by
  classical
  have hle : irrelevantIdeal K M.factorCount M.ambientDimension ≤ Q := not_not.mp hirr
  have hfin : Finset.univ.inf (blockIdeal K M.factorCount M.ambientDimension) ≤ Q := by
    simpa only [irrelevantIdeal, Finset.inf_eq_iInf, Finset.mem_univ, iInf_true] using hle
  obtain ⟨i, hi, hblock⟩ := hQ.inf_le'.mp hfin
  exact hilbertPolynomial_zero_of_blockIdeal_le M Q i hblock

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponDegreeMonotonicity

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ComponentDegree
variable {ι : Type*} [Fintype ι]

theorem eval_nonneg_of_coeff_nonneg (F : MvPolynomial ι ℚ)
    (hF : ∀ e, 0 ≤ coeff e F) (d : ι → ℕ) : 0 ≤ eval (fun i => (d i : ℚ)) F := by
  classical
  rw [eval_eq]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (hF e)
    (Finset.prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) _)

end PhilipponMultiplicity.ComponentDegree

namespace PhilipponMultiplicity.Hilbert
open SectionThree ComponentDegree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponSchemeEndpoint

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.PrimaryComponentSupport

open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem degreeValue_nonneg (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (D : M.FactorIndex → ℕ) :
    0 ≤ Hilbert.degreeValue K M.factorCount M.ambientDimension I D := by
  unfold Hilbert.degreeValue Hilbert.degreeForm
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
  apply mul_nonneg (Nat.cast_nonneg _)
  exact ComponentDegree.eval_nonneg_of_coeff_nonneg _
    (multigraded_hilbert_polynomial_top_coefficients K M I hI).1 D

end PhilipponMultiplicity.PrimaryComponentSupport

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree PrimaryComponentSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

end PhilipponMultiplicity.SectionThreeSupport

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

theorem idealDimension_le_of_minimalPrimes (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (b : ℕ)
    (hb : ∀ q ∈ I.minimalPrimes, IsRelevant K M.factorCount M.ambientDimension q →
      idealDimension M q ≤ b) : idealDimension M I ≤ b := by
  classical
  obtain ⟨n, A, P, D, hfirst, hlast, hhom, hstep⟩ := homogeneous_prime_filtration M I hI
  have hmono : Monotone A := Fin.monotone_iff_le_succ.mpr fun j => by
    rw [(hstep j).2.2.1]; exact le_sup_left
  unfold idealDimension
  rw [← hfirst, hilbertPolynomial_filtration_sum M n A P D hhom
    (fun j => ⟨(hstep j).1, (hstep j).2.2.1⟩) hlast]
  apply totalDegree_finsetSum_le
  intro j _
  let Q := (A j.castSucc).colon {P j}
  have hQ := (hstep j).2.2.2
  have hQhom := homogeneous_colon M _ (hhom j.castSucc) _ _ (hstep j).1
  change (FiniteDifference.shift (fun i => (D j i : ℚ))
      (hilbertPolynomial K M.factorCount M.ambientDimension Q)).totalDegree ≤ b
  by_cases hr : IsRelevant K M.factorCount M.ambientDimension Q
  · have hIQ : I ≤ Q := by
      rw [← hfirst]
      exact (hmono (Fin.zero_le _)).trans Ideal.le_colon
    letI : Q.IsPrime := hQ
    obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le hIQ
    have hprel : IsRelevant K M.factorCount M.ambientDimension p := fun h => hr (h.trans hpQ)
    rw [(ComponentDegree.shift_top _ _).2]
    exact (idealDimension_antitone M p Q (minimalPrime_homogeneous M I p hI hp)
      hQhom hpQ).trans (hb p hp hprel)
  · rw [irrelevant_prime_hilbertPolynomial_zero M Q hQ hr, map_zero, totalDegree_zero]
    exact Nat.zero_le b

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

end PhilipponMultiplicity.SectionThreeSupport

end
end

section
-- Reused implementation: Solutions.PhilipponGroupPrimeComponents

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem IsPhilipponBaseField.isAlgClosed {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : IsAlgClosed K := by
  have transfer (L : Type) [Field L] [IsAlgClosed L] (e : K ≃+* L) : IsAlgClosed K := by
    apply IsAlgClosed.of_exists_root K
    intro P _ hP
    obtain ⟨x,hx⟩ := IsAlgClosed.exists_eval₂_eq_zero e.toRingHom P
      (ne_of_gt (Polynomial.degree_pos_of_irreducible hP))
    refine ⟨e.symm x,?_⟩
    apply e.injective
    rw [map_zero]
    change e.toRingHom (P.eval (e.symm x)) = 0
    rw [← Polynomial.eval₂_at_apply]
    change P.eval₂ e.toRingHom (e (e.symm x)) = 0
    simpa only [RingEquiv.apply_symm_apply] using hx
  rcases hK with ⟨e,_⟩ | ⟨p,hp,h⟩
  · exact transfer ℂ e
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e,_⟩ := h
    exact transfer (PadicComplex p) e

variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponOperatorEvaluation

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem coordinate_coeff_analytic (chart : TranslationChart A g)
    (v : G.ambient.Variable) (e : G.ambient.Variable →₀ ℕ) :
    AnalyticAt K ((chart.coordinates v).coeff e) 0 := by
  by_cases he : e ∈ (chart.coordinates v).support
  · exact chart.coefficient_analytic v e he
  · have he0 : (chart.coordinates v).coeff e = 0 := by
      simpa only [mem_support_iff, not_not] using he
    rw [he0]
    exact analyticAt_const

theorem substituted_coeff_analytic (chart : TranslationChart A g)
    (P : G.CoordinateRing) (e : G.ambient.Variable →₀ ℕ) :
    AnalyticAt K ((substitutedPolynomial chart P).coeff e) 0 := by
  classical
  induction P using MvPolynomial.induction_on generalizing e with
  | C a =>
    simp only [substitutedPolynomial, eval₂Hom_C, RingHom.comp_apply, coeff_C]
    split_ifs <;> exact analyticAt_const
  | add P Q hP hQ =>
    simp only [substitutedPolynomial, map_add, coeff_add]
    exact (hP e).add (hQ e)
  | mul_X P v hP =>
    simp only [substitutedPolynomial, map_mul, eval₂Hom_X']
    change AnalyticAt K ((substitutedPolynomial chart P * chart.coordinates v).coeff e) 0
    rw [coeff_mul]
    exact Finset.analyticAt_sum _ fun p _ => (hP p.1).mul (coordinate_coeff_analytic chart v p.2)

theorem evaluate_substituted (chart : TranslationChart A g) (P : G.CoordinateRing)
    (x : G.Point) (z : A.ParameterSpace) :
    evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x z =
      MvPolynomial.eval (fun v => evaluateCoefficientPolynomial A (chart.coordinates v) x z) P := by
  unfold evaluateCoefficientPolynomial substitutedPolynomial
  rw [MvPolynomial.map_eval₂Hom]
  change eval₂Hom _ _ P = eval₂Hom (RingHom.id K) _ P
  congr 2
  ext a
  simp

theorem polynomialOperator_eval (chart : TranslationChart A g) (P : G.CoordinateRing)
    (x : G.Point) (n : ℕ) (directions : Fin n → Fin A.parameterDimension) :
    G.ambient.eval (polynomialOperator chart n directions P) (G.embedding x) =
      iteratedFDeriv K n
        (fun z => MvPolynomial.eval
          (fun v => evaluateCoefficientPolynomial A (chart.coordinates v) x z) P) 0
        (fun i => Pi.single (directions i) 1) := by
  classical
  let F := substitutedPolynomial chart P
  let v := G.ambient.coordinate (G.embedding x)
  have heval : (fun z => MvPolynomial.eval
      (fun w => evaluateCoefficientPolynomial A (chart.coordinates w) x z) P) =
      fun z => ∑ e ∈ F.support, (∏ i ∈ e.support, v i ^ e i) * F.coeff e z := by
    funext z
    rw [← evaluate_substituted]
    change eval₂ _ v F = _
    simp only [eval₂_eq, Pi.evalRingHom_apply, mul_comm]
  rw [heval, iteratedFDeriv_fun_sum_apply
    (f := fun e z => (∏ i ∈ e.support, v i ^ e i) * F.coeff e z)
    (fun e _ => (analyticAt_const.mul (substituted_coeff_analytic chart P e)).contDiffAt)]
  simp only [ContinuousMultilinearMap.sum_apply]
  unfold polynomialOperator MultiProjectiveSpace.eval
  change MvPolynomial.eval v ((AddMonoidAlgebra.coeff F).sum _) = _
  rw [Finsupp.sum]
  simp only [map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro e _
  rw [show (fun z => (∏ i ∈ e.support, v i ^ e i) * F.coeff e z) =
    (fun z => (∏ i ∈ e.support, v i ^ e i) • F.coeff e z) from rfl,
    iteratedFDeriv_const_smul_apply' (substituted_coeff_analytic chart P e).contDiffAt]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul, Finsupp.prod]
  exact mul_comm _ _

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Reused implementation: Solutions.PhilipponOperatorAlgebra

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem polynomialOperator_coeff (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (P : G.CoordinateRing)
    (e : G.ambient.Variable →₀ ℕ) :
    (polynomialOperator chart n directions P).coeff e =
      iteratedFDeriv K n ((substitutedPolynomial chart P).coeff e) 0
        (fun i => Pi.single (directions i) 1) := by
  classical
  unfold polynomialOperator
  rw [Finsupp.sum]
  simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with he
  · rfl
  · have hz : (substitutedPolynomial chart P).coeff e = 0 := by
      exact Finsupp.notMem_support_iff.mp he
    simp [hz]

theorem substitutedPolynomial_homogeneous (chart : TranslationChart A g)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    (substitutedPolynomial chart P).IsWeightedHomogeneous
      (Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension)
      (fun i => chart.degree i * D i) := by
  classical
  let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
  let c : G.ambient.Variable → G.FactorIndex → ℕ := fun v i =>
    chart.degree i * w v i
  have hc (v : G.ambient.Variable) : (chart.coordinates v).IsWeightedHomogeneous w (c v) := by
    intro e he
    funext i
    rw [G.ambient.blockWeight_apply]
    obtain ⟨h₁, h₂⟩ := chart.coordinate_homogeneous v e (mem_support_iff.mpr he)
    by_cases hi : i = v.1
    · subst i
      simpa [c, w, Hilbert.blockWeight] using h₁
    · simpa [c, w, Hilbert.blockWeight, Ne.symm hi] using h₂ i hi
  have hwP : P.IsWeightedHomogeneous w D := (G.ambient.degreePiece_iff P D).mpr hP
  apply IsWeightedHomogeneous.induction_on (motive := fun Q _ =>
    (substitutedPolynomial chart Q).IsWeightedHomogeneous w
      (fun i => chart.degree i * D i)) ?_ ?_ ?_ hwP
  · simpa [substitutedPolynomial] using
      isWeightedHomogeneous_zero (AnalyticCoefficientRing A) w (fun i => chart.degree i * D i)
  · intro P Q hP hQ ihP ihQ
    simpa only [substitutedPolynomial, map_add] using ihP.add ihQ
  · intro e a he
    have hweight : (∑ v ∈ e.support, e v • c v) = fun i => chart.degree i * D i := by
      funext i
      have hwi := congrFun he i
      rw [Finsupp.weight_eq_sum] at hwi
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hwi ⊢
      calc
        ∑ v ∈ e.support, e v * c v i =
            chart.degree i * ∑ v ∈ e.support, e v * w v i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          dsimp [c]
          ring
        _ = chart.degree i * D i := by
          congr 1
          rw [← hwi]
          apply Finset.sum_subset (Finset.subset_univ _)
          intro v _ hv
          rw [Finsupp.notMem_support_iff.mp hv, zero_mul]
    unfold substitutedPolynomial
    rw [eval₂Hom_monomial, Finsupp.prod]
    change IsWeightedHomogeneous w (C _ * _) _
    have hprod := (IsWeightedHomogeneous.prod e.support
      (fun v => chart.coordinates v ^ e v) (fun v => e v • c v)
        (fun v _ => (hc v).pow (e v))).C_mul ((Pi.constRingHom A.ParameterSpace K) a)
    exact hweight ▸ hprod

theorem polynomialOperator_homogeneous (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    G.ambient.IsHomogeneous (polynomialOperator chart n directions P)
      (fun i => chart.degree i * D i) := by
  intro e he i
  have hc : (substitutedPolynomial chart P).coeff e ≠ 0 := by
    intro hz
    have := mem_support_iff.mp he
    rw [polynomialOperator_coeff, hz] at this
    simpa using this
  have hw := substitutedPolynomial_homogeneous chart P D hP hc
  exact (G.ambient.blockWeight_apply e i).symm.trans (congrFun hw i)

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Reused implementation: Solutions.PhilipponAlgebraicSubgroupClosure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section
open Set
open scoped Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

theorem EmbeddedGroupProduct.zariski_separatelyContinuousAdd (G : EmbeddedGroupProduct K) :
    @SeparatelyContinuousAdd G.Point G.zariskiTopology _ := by
  let := G.zariskiTopology
  have hc (a : G.Point) : Continuous (fun x : G.Point => x + a) :=
    continuous_induced_rng.mpr (G.translation_regular a).continuous
  exact
    { continuous_add_const := hc _
      continuous_const_add := by intro a; simpa only [add_comm a] using hc a }

theorem EmbeddedGroupProduct.zariski_continuousNeg (G : EmbeddedGroupProduct K) :
    @ContinuousNeg G.Point G.zariskiTopology _ := by
  let := G.zariskiTopology
  exact ⟨continuous_induced_rng.mpr G.negation_regular.continuous⟩

end PhilipponMultiplicity
end
end

section
-- Reused implementation: Solutions.PhilipponTranslationGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Topology
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [Field K] (G : EmbeddedGroupProduct K)

theorem EmbeddedGroupProduct.continuous_translation (g : G.Point) :
    @Continuous _ _ G.zariskiTopology G.zariskiTopology (fun x : G.Point => g+x) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  have hh : Continuous (fun x : G.Point => x+g) :=
    continuous_induced_rng.mpr (G.translation_regular g).continuous
  simpa only [add_comm] using hh

def EmbeddedGroupProduct.translationHomeomorph (g : G.Point) :
    @Homeomorph G.Point G.Point G.zariskiTopology G.zariskiTopology := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact {
    toEquiv :=
      { toFun := fun x => g+x
        invFun := fun x => -g+x
        left_inv := fun x => by simp only [← add_assoc,neg_add_cancel,zero_add]
        right_inv := fun x => by simp only [← add_assoc,add_neg_cancel,zero_add] }
    continuous_toFun := G.continuous_translation g
    continuous_invFun := G.continuous_translation (-g) }

theorem PolynomialTranslationChart.pullback_homogeneous {g : G.Point}
    (chart : PolynomialTranslationChart G g) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    G.ambient.IsHomogeneous (MvPolynomial.eval₂ MvPolynomial.C chart.coordinates P)
      (fun i => chart.degree i * D i) := by
  classical
  have hh := hP.eval₂_blocks G.ambient G.ambient chart.coordinates
    (fun j i => if i=j then chart.degree i else 0) chart.homogeneous
  simpa [mul_ite,mul_comm] using hh

theorem PolynomialTranslationChart.pullback_eval_zero_iff {g : G.Point}
    (chart : PolynomialTranslationChart G g) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : G.Point) (hx : x ∈ chart.domain) :
    G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C chart.coordinates P) (G.embedding x) = 0 ↔
      G.ambient.eval P (G.embedding (g+x)) = 0 := by
  have heval : G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C chart.coordinates P) (G.embedding x) =
      MvPolynomial.eval (fun v => G.ambient.eval (chart.coordinates v) (G.embedding x)) P := by
    dsimp only [MultiProjectiveSpace.eval]
    rw [← MvPolynomial.eval_assoc]
    rfl
  rw [heval]
  exact G.ambient.eval_eq_zero_iff_of_lift (G.embedding (g+x))
    (fun v => G.ambient.eval (chart.coordinates v) (G.embedding x))
    (chart.represents x hx) P D hP

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponDifferentialVanishing

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem chartDomain_isOpen (b : CoordinateChart G) :
    @IsOpen _ G.zariskiTopology (chartDomain G b) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  have h (i : G.FactorIndex) : @IsOpen _ G.zariskiTopology
      {x | (G.embedding x i).rep (b i) ≠ 0} := by
    let v : G.ambient.Variable := ⟨i, b i⟩
    have hh : G.ambient.IsHomogeneous (X v) (Pi.single i 1) := by
      apply (G.ambient.degreePiece_iff _ _).mp
      exact isWeightedHomogeneous_X K _ v
    have ho := G.ambient.isOpen_basic (X v) (Pi.single i 1) hh
    have hp := ho.preimage (continuous_induced_dom :
      @Continuous _ _ G.zariskiTopology G.ambient.zariskiTopology G.embedding)
    simpa [MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate, v] using hp
  have heq : chartDomain G b = ⋂ i, {x | (G.embedding x i).rep (b i) ≠ 0} := by
    ext x
    simp [chartDomain]
  rw [heq]
  exact isOpen_iInter_of_finite h

theorem exists_chartDomain (x : G.Point) : ∃ b : CoordinateChart G, x ∈ chartDomain G b := by
  have h (i : G.FactorIndex) : ∃ j, (G.embedding x i).rep j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using (G.embedding x i).rep_nonzero
  choose b hb using h
  exact ⟨b, hb⟩

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Reused implementation: Solutions.PhilipponLocalPolynomialSections

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

def pivotPolynomial (b : CoordinateChart G) (D : G.FactorIndex → ℕ) : G.CoordinateRing :=
  ∏ i, X ⟨i, b i⟩ ^ D i

theorem pivotPolynomial_homogeneous (b : CoordinateChart G) (D : G.FactorIndex → ℕ) :
    G.ambient.IsHomogeneous (pivotPolynomial b D) D :=
  Hilbert.variable_product_homogeneous G.ambient b D

theorem pivotPolynomial_eval_ne_zero (b : CoordinateChart G) (D : G.FactorIndex → ℕ)
    (x : G.Point) (hx : x ∈ chartDomain G b) :
    G.ambient.eval (pivotPolynomial b D) (G.embedding x) ≠ 0 := by
  classical
  simp only [pivotPolynomial, MultiProjectiveSpace.eval, map_prod, map_pow, eval_X]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hx i))

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Reused implementation: Solutions.PhilipponLocalRational

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem exists_basic_subset (U : Set G.Point) (hU : @IsOpen _ G.zariskiTopology U)
    (x : G.Point) (hx : x ∈ U) :
    ∃ s : G.CoordinateRing, ∃ E : G.FactorIndex → ℕ, G.ambient.IsHomogeneous s E ∧
      G.ambient.eval s (G.embedding x) ≠ 0 ∧
      {y : G.Point | G.ambient.eval s (G.embedding y) ≠ 0} ⊆ U := by
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨W, ⟨s,E,hs,rfl⟩, hxW, hWV⟩ :=
    G.ambient.isTopologicalBasis_basic.exists_subset_of_mem_open hx hV
  exact ⟨s,E,hs,hxW,fun y hy => hWV hy⟩

end PhilipponMultiplicity.OperatorSupport
end
end

section
-- Reused implementation: Solutions.PhilipponTranslationSeparation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Set MvPolynomial TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem noetherian_induced {X : Type*} (e : X → M.Point) :
    @NoetherianSpace X (TopologicalSpace.induced e M.zariskiTopology) := by
  letI : TopologicalSpace M.Point := M.zariskiTopology
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  apply noetherianSpace_iff_isCompact.mpr
  intro S
  apply isCompact_iff_finite_subcover.mpr
  intro ι U hU hcover
  choose W hW heq using fun i => isOpen_induced_iff.mp (hU i)
  obtain ⟨t,ht⟩ := M.finite_open_subcover (fun x : S => e x.val) W hW (by
    intro x
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover x.property)
    exact ⟨i,by change x.val ∈ e ⁻¹' W i; rwa [heq i]⟩)
  refine ⟨t,?_⟩
  intro x hx
  obtain ⟨i,hi,hxi⟩ := ht ⟨x,hx⟩
  exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,by rw [← heq i]; exact hxi⟩⟩

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.TranslationSupport
universe u
variable {K : Type u} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
local instance : TopologicalSpace G.Point := G.zariskiTopology

structure SeparatingCharts (V : Set G.Point) {g : G.Point}
    (atlas : PolynomialTranslationAtlas G g) where
  Index : Type u
  finite : Fintype Index
  component : Index → Set V
  irreducible : ∀ i, IsIrreducible (component i)
  covers : ∀ x : V, ∃ i, x ∈ component i
  chart : Index → atlas.Index
  weight : Index → G.CoordinateRing
  degree : Index → G.FactorIndex → ℕ
  homogeneous : ∀ i, G.ambient.IsHomogeneous (weight i) (degree i)
  point : Index → V
  point_mem : ∀ i, point i ∈ component i
  nonzero : ∀ i, G.ambient.eval (weight i) (G.embedding (point i).val) ≠ 0
  support_chart : ∀ i (x : V), G.ambient.eval (weight i) (G.embedding x.val) ≠ 0 →
    x.val ∈ (atlas.chart (chart i)).domain
  zero_other : ∀ i j, i ≠ j → ∀ x : V, x ∈ component i →
    G.ambient.eval (weight j) (G.embedding x.val) = 0
  pivot : Index → CoordinateChart G
  point_pivot : ∀ i, (point i).val ∈ chartDomain G (pivot i)

attribute [instance] SeparatingCharts.finite

theorem exists_separating_charts (V : Set G.Point) {g : G.Point}
    (atlas : PolynomialTranslationAtlas G g) : Nonempty (SeparatingCharts V atlas) := by
  classical
  letI : NoetherianSpace G.Point := G.ambient.noetherian_induced G.embedding
  let C := irreducibleComponents V
  have hC : C.Finite := NoetherianSpace.finite_irreducibleComponents
  letI : Fintype C := hC.fintype
  have hdata (i : C) : ∃ x : V, x ∈ i.val ∧ ∃ a : atlas.Index,
      ∃ P : G.CoordinateRing, ∃ D : G.FactorIndex → ℕ,
        G.ambient.IsHomogeneous P D ∧ G.ambient.eval P (G.embedding x.val) ≠ 0 ∧
          (∀ y : V, G.ambient.eval P (G.embedding y.val) ≠ 0 →
            y.val ∈ (atlas.chart a).domain ∧ ∀ j : C, j ≠ i → y ∉ j.val) := by
    let O : Set V := (⋃₀ (C \ {i.val}))ᶜ
    have hO : IsOpen O := by
      dsimp only [O]
      rw [Set.sUnion_eq_biUnion,isOpen_compl_iff]
      exact hC.sdiff.isClosed_biUnion (fun W hW => isClosed_of_mem_irreducibleComponents W hW.1)
    have hclosure : closure O = i.val := closure_sUnion_irreducibleComponents_sdiff_singleton hC i.val i.property
    have hOne : O.Nonempty := by
      rw [← closure_nonempty_iff,hclosure]
      exact i.property.1.nonempty
    obtain ⟨x,hx⟩ := hOne
    obtain ⟨a,ha⟩ := atlas.covers x.val
    obtain ⟨W,hW,heq⟩ := isOpen_induced_iff.mp (hO.inter
      ((atlas.chart a).domain_open.preimage continuous_subtype_val))
    have hxW : x.val ∈ W := by
      change x ∈ Subtype.val ⁻¹' W
      rw [heq]
      exact ⟨hx,ha⟩
    obtain ⟨P,D,hP,hPx,hPW⟩ := OperatorSupport.exists_basic_subset W hW x.val hxW
    refine ⟨x,?_,a,P,D,hP,hPx,?_⟩
    · rw [← hclosure]
      exact subset_closure hx
    · intro y hy
      have hyO : y ∈ O ∩ {q : V | q.val ∈ (atlas.chart a).domain} := by
        change y ∈ O ∩ Subtype.val ⁻¹' (atlas.chart a).domain
        rw [← heq]
        exact hPW hy
      refine ⟨hyO.2,?_⟩
      intro j hji hj
      apply hyO.1
      exact Set.mem_sUnion.mpr ⟨j.val,⟨j.property,by
        simp only [Set.mem_singleton_iff]
        exact fun h => hji (Subtype.ext h)⟩,hj⟩
  choose x hx a P D hP hn hs using hdata
  choose b hb using fun i => OperatorSupport.exists_chartDomain (x i).val
  refine ⟨⟨C,inferInstance,(fun i => i.val),(fun i => i.property.1),?_,a,P,D,hP,x,hx,hn,
    (fun i y hy => (hs i y hy).1),?_,b,hb⟩⟩
  · intro y
    exact ⟨⟨irreducibleComponent y,irreducibleComponent_mem_irreducibleComponents y⟩,mem_irreducibleComponent⟩
  · intro i j hij y hy
    by_contra hn
    exact (hs j y hn).2 i hij hy

end PhilipponMultiplicity.TranslationSupport
end
end

section
-- Reused implementation: Solutions.PhilipponConnectedGroupIrreducible

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity

theorem irreducible_of_transitive_homeomorphisms {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [ConnectedSpace X]
    (htrans : ∀ x y : X, ∃ e : X ≃ₜ X, e x = y) : IrreducibleSpace X := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨U,hU,⟨p,hp⟩,hUC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  have hCopen : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨e,he⟩ := htrans p y
    have hopen : IsOpen (e '' U) := e.isOpenMap _ hU
    have hclosed : IsClosed (e '' C) := e.isClosedMap _
      (isClosed_of_mem_irreducibleComponents C hC)
    have hydense : C ⊆ closure (C ∩ e '' U) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 hopen
        ⟨y,hy,p,hp,he⟩
    have hCeC : C ⊆ e '' C := hydense.trans (closure_minimal
      (fun z hz => Set.image_mono hUC hz.2) hclosed)
    have heCC : e '' C ⊆ C := hC.2 (hC.1.image e e.continuous.continuousOn) hCeC
    exact Filter.mem_of_superset (hopen.mem_nhds ⟨p,hp,he⟩)
      ((Set.image_mono hUC).trans heCC)
  have hfull : C = univ := (show IsClopen C from
    ⟨isClosed_of_mem_irreducibleComponents C hC,hCopen⟩).eq_univ hC.1.nonempty
  exact { isPreirreducible_univ := by simpa only [hfull] using hC.1.2
          toNonempty := inferInstance }

variable {K : Type*} [Field K] {G : EmbeddedGroupProduct K}

def AlgebraicSubgroup.translationHomeomorph (H : AlgebraicSubgroup G)
    (a : H.toAddSubgroup) :
    @Homeomorph H.carrier H.carrier
      (TopologicalSpace.induced Subtype.val G.zariskiTopology)
      (TopologicalSpace.induced Subtype.val G.zariskiTopology) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact (G.translationHomeomorph a.val).subtype (by
    intro x
    change x ∈ H.toAddSubgroup ↔ a.val+x ∈ H.toAddSubgroup
    exact ⟨fun hx => H.toAddSubgroup.add_mem a.property hx,fun hx => by
      have h := H.toAddSubgroup.add_mem (H.toAddSubgroup.neg_mem a.property) hx
      simpa only [← add_assoc,neg_add_cancel,zero_add] using h⟩)

theorem AlgebraicSubgroup.isIrreducible_of_isConnected (H : AlgebraicSubgroup G)
    (hH : H.IsConnected) : @IsIrreducible _ G.zariskiTopology H.carrier := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : NoetherianSpace G.Point := G.ambient.noetherian_induced G.embedding
  letI : ConnectedSpace H.carrier := isConnected_iff_connectedSpace.mp hH
  apply isIrreducible_iff_irreducibleSpace.mpr
  apply irreducible_of_transitive_homeomorphisms
  intro x y
  let a : H.toAddSubgroup := ⟨y.val-x.val,H.toAddSubgroup.sub_mem y.property x.property⟩
  refine ⟨H.translationHomeomorph a,?_⟩
  apply Subtype.ext
  change y.val-x.val+x.val = y.val
  exact sub_add_cancel _ _

theorem AlgebraicSubgroup.isIrreducible_translate (H : AlgebraicSubgroup G)
    (hH : H.IsConnected) (g : G.Point) :
    @IsIrreducible _ G.zariskiTopology (translate g H.carrier) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact (H.isIrreducible_of_isConnected hH).image _ (G.continuous_translation g).continuousOn

theorem MultiProjectiveSpace.vanishingIdeal_isPrime_of_isIrreducible
    (M : MultiProjectiveSpace K) (S : Set M.Point)
    (hS : @IsIrreducible _ M.zariskiTopology S) : (M.vanishingIdeal S).IsPrime := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  apply Hilbert.prime_of_homogeneous_products M _ (vanishingIdeal_multihomogeneous K M S)
  · intro htop
    obtain ⟨x,hx⟩ := hS.nonempty
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal
      (show (1 : M.CoordinateRing) ∈ M.vanishingIdeal S by rw [htop]; trivial) hx
    exact one_ne_zero (by simpa only [MultiProjectiveSpace.eval,map_one] using hz)
  · rintro P Q ⟨D,hP⟩ ⟨E,hQ⟩ hPQ
    by_contra! hn
    have hnzero (R : M.CoordinateRing) (d : M.FactorIndex → ℕ)
        (hR : M.IsHomogeneous R d) (hRI : R ∉ M.vanishingIdeal S) :
        (S ∩ {x | M.eval R x ≠ 0}).Nonempty := by
      by_contra hz
      apply hRI
      exact Ideal.subset_span ⟨⟨d,hR⟩,fun x hx => by
        by_contra hxR
        exact hz ⟨x,hx,hxR⟩⟩
    obtain ⟨x,hx,hxP,hxQ⟩ := hS.2 _ _ (M.isOpen_basic P D hP)
      (M.isOpen_basic Q E hQ) (hnzero P D hP hn.1) (hnzero Q E hQ hn.2)
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal hPQ hx
    exact (mul_ne_zero hxP hxQ) (by simpa only [MultiProjectiveSpace.eval,map_mul] using hz)

theorem AlgebraicSubgroup.translated_vanishingIdeal_isPrime (H : AlgebraicSubgroup G)
    (hH : H.IsConnected) (g : G.Point) :
    (G.vanishingIdeal (translate g H.carrier)).IsPrime := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  exact G.ambient.vanishingIdeal_isPrime_of_isIrreducible _
    ((H.isIrreducible_translate hH g).image G.embedding
      (show Continuous G.embedding from continuous_induced_dom).continuousOn)

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponTranslationPullback

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Set MvPolynomial TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertFunction_le_of_linear_pullback (S T : Set M.Point)
    (D E : M.FactorIndex → ℕ) (L : M.CoordinateRing →ₗ[K] M.CoordinateRing)
    (hhom : ∀ P, M.IsHomogeneous P D → M.IsHomogeneous (L P) E)
    (hker : ∀ P, M.IsHomogeneous P D →
      ((∀ x ∈ S, M.eval P x = 0) ↔ ∀ x ∈ T, M.eval (L P) x = 0)) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal S) D ≤
      Hilbert.hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal T) E := by
  let V := Hilbert.degreePiece K M.factorCount M.ambientDimension D
  let W := Hilbert.degreePiece K M.factorCount M.ambientDimension E
  let I := M.vanishingIdeal S
  let J := M.vanishingIdeal T
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let q := (Ideal.Quotient.mkₐ K J).toLinearMap
  let g := (q.comp L).domRestrict V
  have hmem (U : Set M.Point) (P : M.CoordinateRing) (d : M.FactorIndex → ℕ)
      (hP : M.IsHomogeneous P d) :
      P ∈ M.vanishingIdeal U ↔ ∀ x ∈ U, M.eval P x = 0 := by
    constructor
    · intro h x hx
      exact M.eval_eq_zero_of_mem_vanishingIdeal h hx
    · intro h
      exact Ideal.subset_span ⟨⟨d,hP⟩,h⟩
  have hfg : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ Ideal.Quotient.mk J (L P.val) = 0
    have hP := (M.degreePiece_iff _ _).mp P.property
    rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.Quotient.eq_zero_iff_mem,
      hmem S P.val D hP,hmem T (L P.val) E (hhom _ hP)]
    exact hker _ hP
  have hf : LinearMap.range f = V.map (Ideal.Quotient.mkₐ K I).toLinearMap := by
    ext x
    constructor
    · rintro ⟨P,rfl⟩
      exact ⟨P.val,P.property,rfl⟩
    · rintro ⟨P,hP,rfl⟩
      exact ⟨⟨P,hP⟩,rfl⟩
  have hg : LinearMap.range g ≤ W.map q := by
    rintro _ ⟨P,rfl⟩
    exact ⟨L P.val,(M.degreePiece_iff _ _).mpr
      (hhom _ ((M.degreePiece_iff _ _).mp P.property)),rfl⟩
  have he := (f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hfg).trans g.quotKerEquivRange)).finrank_eq
  rw [hf] at he
  letI : Module.Finite K (Hilbert.quotientPiece K M.factorCount M.ambientDimension J E) := by
    dsimp [Hilbert.quotientPiece]
    infer_instance
  exact he.trans_le (Submodule.finrank_mono hg)

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.TranslationSupport
universe u
variable {K : Type u} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
local instance : TopologicalSpace G.Point := G.zariskiTopology
local instance : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
open OperatorSupport

variable {V : Set G.Point} {g : G.Point} {atlas : PolynomialTranslationAtlas G g}

def SeparatingCharts.shift (s : SeparatingCharts V atlas) (k : G.FactorIndex) : ℕ :=
  ∑ i, s.degree i k

theorem SeparatingCharts.degree_le_shift (s : SeparatingCharts V atlas)
    (i : s.Index) (k : G.FactorIndex) : s.degree i k ≤ s.shift k := by
  classical
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (s.degree j k)) (Finset.mem_univ i)

def SeparatingCharts.padding (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) (i : s.Index) (k : G.FactorIndex) : ℕ :=
  s.shift k - s.degree i k + (c k - (atlas.chart (s.chart i)).degree k) * D k

def SeparatingCharts.pullback (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) : G.CoordinateRing →ₗ[K] G.CoordinateRing :=
  ∑ i, (LinearMap.mulLeft K (s.weight i * pivotPolynomial (s.pivot i) (s.padding c D i))).comp
    (MvPolynomial.aeval (atlas.chart (s.chart i)).coordinates).toLinearMap

theorem SeparatingCharts.pullback_apply (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) (P : G.CoordinateRing) :
    s.pullback c D P = ∑ i, s.weight i * pivotPolynomial (s.pivot i) (s.padding c D i) *
      MvPolynomial.eval₂ MvPolynomial.C (atlas.chart (s.chart i)).coordinates P := by
  simp only [SeparatingCharts.pullback,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem SeparatingCharts.pullback_homogeneous (s : SeparatingCharts V atlas)
    (c : G.FactorIndex → ℕ) (hc : ∀ a k, (atlas.chart a).degree k ≤ c k)
    (D : G.FactorIndex → ℕ) (P : G.CoordinateRing) (hP : G.ambient.IsHomogeneous P D) :
    G.ambient.IsHomogeneous (s.pullback c D P) (fun k => c k * D k + s.shift k) := by
  classical
  rw [s.pullback_apply]
  apply (G.ambient.degreePiece_iff _ _).mp
  apply Submodule.sum_mem
  intro i _
  apply (G.ambient.degreePiece_iff _ _).mpr
  have ht := ((s.homogeneous i).mul G.ambient
    (pivotPolynomial_homogeneous (s.pivot i) (s.padding c D i))).mul G.ambient
    ((atlas.chart (s.chart i)).pullback_homogeneous G P D hP)
  convert ht using 1
  funext k
  have h₁ := s.degree_le_shift i k
  have h₂ := Nat.mul_le_mul_right (D k) (hc (s.chart i) k)
  simp only [Pi.add_apply,SeparatingCharts.padding,Nat.sub_mul]
  omega

theorem SeparatingCharts.eval_pullback (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) (P : G.CoordinateRing) (x : G.Point) :
    G.ambient.eval (s.pullback c D P) (G.embedding x) =
      ∑ i, G.ambient.eval (s.weight i) (G.embedding x) *
        G.ambient.eval (pivotPolynomial (s.pivot i) (s.padding c D i)) (G.embedding x) *
        G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C
          (atlas.chart (s.chart i)).coordinates P) (G.embedding x) := by
  rw [s.pullback_apply]
  simp only [MultiProjectiveSpace.eval,map_sum,map_mul]

theorem SeparatingCharts.pullback_vanishing_iff (s : SeparatingCharts V atlas)
    (c D : G.FactorIndex → ℕ) (P : G.CoordinateRing) (hP : G.ambient.IsHomogeneous P D) :
    (∀ x ∈ translate g V, G.ambient.eval P (G.embedding x) = 0) ↔
      ∀ x ∈ V, G.ambient.eval (s.pullback c D P) (G.embedding x) = 0 := by
  classical
  constructor
  · intro h x hx
    rw [s.eval_pullback]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : G.ambient.eval (s.weight i) (G.embedding x) = 0
    · rw [hi,zero_mul,zero_mul]
    · have hz := ((atlas.chart (s.chart i)).pullback_eval_zero_iff G P D hP x
        (s.support_chart i ⟨x,hx⟩ hi)).mpr (h (g+x) ⟨x,hx,rfl⟩)
      rw [hz,mul_zero]
  · intro h y hy
    obtain ⟨x,hx,rfl⟩ := hy
    let Z : Set V := {x | G.ambient.eval P (G.embedding (g+x.val)) = 0}
    have he : Continuous (G.embedding : G.Point → G.ambient.Point) := continuous_induced_dom
    have hv : Continuous (Subtype.val : V → G.Point) := continuous_subtype_val
    have hZ : IsClosed Z := (G.ambient.isClosed_zero P D hP).preimage
      (he.comp ((G.continuous_translation g).comp hv))
    obtain ⟨i,hi⟩ := s.covers ⟨x,hx⟩
    suffices hs : s.component i ⊆ Z by
      exact hs (a := (⟨x,hx⟩ : V)) hi
    let U : Set V := {x | G.ambient.eval (s.weight i) (G.embedding x.val) ≠ 0} ∩
      Subtype.val ⁻¹' chartDomain G (s.pivot i)
    have hU : IsOpen U := ((G.ambient.isOpen_basic (s.weight i) (s.degree i)
      (s.homogeneous i)).preimage (he.comp hv)).inter
      ((chartDomain_isOpen (s.pivot i)).preimage hv)
    have hdense : s.component i ⊆ closure (s.component i ∩ U) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen (s.irreducible i).2 hU
        ⟨s.point i,s.point_mem i,s.nonzero i,s.point_pivot i⟩
    apply hdense.trans
    apply closure_minimal _ hZ
    intro z hz
    have heval := h z.val z.property
    rw [s.eval_pullback,Finset.sum_eq_single i] at heval
    · have hzpull : G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C
          (atlas.chart (s.chart i)).coordinates P) (G.embedding z.val) = 0 :=
        (mul_eq_zero.mp heval).resolve_left (mul_ne_zero hz.2.1
          (pivotPolynomial_eval_ne_zero (s.pivot i) (s.padding c D i) z.val hz.2.2))
      exact ((atlas.chart (s.chart i)).pullback_eval_zero_iff G P D hP z.val
        (s.support_chart i z hz.2.1)).mp hzpull
    · intro j _ hji
      rw [s.zero_other i j hji.symm z hz.1,zero_mul,zero_mul]
    · simp

theorem translated_hilbertFunction_le (V : Set G.Point) (g : G.Point)
    (c : G.FactorIndex → ℕ) (atlas : PolynomialTranslationAtlas G g)
    (hc : ∀ a k, (atlas.chart a).degree k ≤ c k) :
    ∃ E : G.FactorIndex → ℕ, ∀ D : G.FactorIndex → ℕ,
      Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal (translate g V)) D ≤
      Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal V) (fun k => c k * D k + E k) := by
  obtain ⟨s⟩ := exists_separating_charts V atlas
  refine ⟨s.shift,fun D => ?_⟩
  apply G.ambient.hilbertFunction_le_of_linear_pullback
    (G.embedding '' translate g V) (G.embedding '' V) D _ (s.pullback c D)
    (fun P hP => s.pullback_homogeneous c hc D P hP)
  intro P hP
  simpa only [Set.forall_mem_image] using s.pullback_vanishing_iff c D P hP

end PhilipponMultiplicity.TranslationSupport

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

theorem natDegree_le_of_eventual_eval_le (P Q : Polynomial ℚ)
    (hP : 0 < P.leadingCoeff) (hQ : 0 < Q.leadingCoeff)
    (hle : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  obtain ⟨c,C,hc,hC,hboundsP⟩ := polynomial_eventually_two_sided P hP
  obtain ⟨c',C',hc',hC',hboundsQ⟩ := polynomial_eventually_two_sided Q hQ
  apply exponent_le_of_eventual_power_bound hc (C := C')
  filter_upwards [hboundsP,hboundsQ,hle] with n hnP hnQ hn
  exact hnP.1.trans (hn.trans hnQ.2)

theorem leadingCoeff_le_of_eventual_eval_le (P Q : Polynomial ℚ)
    (hP : 0 < P.leadingCoeff) (hQ : 0 < Q.leadingCoeff)
    (hdeg : P.natDegree = Q.natDegree)
    (hle : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.leadingCoeff ≤ Q.leadingCoeff := by
  have hlim (R : Polynomial ℚ) (hR : 0 < R.leadingCoeff) :
      Tendsto (fun n : ℕ => R.eval (n : ℚ) / (n : ℚ) ^ R.natDegree)
        atTop (𝓝 R.leadingCoeff) := by
    have hne : R ≠ 0 := by intro h; simpa [h] using hR
    have hd : R.degree = (Polynomial.X ^ R.natDegree : Polynomial ℚ).degree := by
      rw [Polynomial.degree_X_pow,Polynomial.degree_eq_natDegree hne]
    simpa [Function.comp_def] using (R.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
      (Polynomial.X ^ R.natDegree) hd).comp (tendsto_natCast_atTop_atTop (R := ℚ))
  apply le_of_tendsto_of_tendsto (hlim P hP) (hlim Q hQ)
  filter_upwards [hle] with n hn
  rw [hdeg]
  exact div_le_div_of_nonneg_right hn (pow_nonneg (Nat.cast_nonneg _) _)

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

theorem exists_ray_hilbertPolynomial {S : Set M.Point} (hS : S.Nonempty)
    (a E : M.FactorIndex → ℕ) (ha : ∀ i, 1 ≤ a i) :
    ∃ P : Polynomial ℚ,
      P.natDegree = (hilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal S)).totalDegree ∧
      P.leadingCoeff = eval (fun i => (a i : ℚ))
        (homogeneousComponent (hilbertPolynomial K M.factorCount M.ambientDimension
          (M.vanishingIdeal S)).totalDegree
          (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S))) ∧
      0 < P.leadingCoeff ∧ ∃ N : ℕ, ∀ n ≥ N,
        P.eval (n : ℚ) = (hilbertFunction K M.factorCount M.ambientDimension
          (M.vanishingIdeal S) (fun i => a i * n + E i) : ℚ) := by
  classical
  let F := hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S)
  have hhom := vanishingIdeal_multihomogeneous K M S
  have htop : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F := by
    intro e he
    have h := (multigraded_hilbert_polynomial_top_coefficients K M _ hhom).1 e
    rwa [coeff_homogeneousComponent,if_pos he] at h
  have hap (i : M.FactorIndex) : 0 < (a i : ℚ) := by
    exact_mod_cast (show 0 < a i by have := ha i; omega)
  obtain ⟨hd,hlc,hpos⟩ := rayPolynomial_degree_and_leadingCoeff F
    (vanishing_hilbertPolynomial_ne_zero M hS) htop
    (fun i => (a i : ℚ)) (fun i => (E i : ℚ)) hap
  refine ⟨rayPolynomial F (fun i => (a i : ℚ)) (fun i => (E i : ℚ)),hd,hlc,hpos,?_⟩
  obtain ⟨d₀,hd₀⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension
    (M.vanishingIdeal S) (multigraded_hilbert_polynomial_exists K M _ hhom)
  refine ⟨Finset.univ.sup d₀,fun n hn => ?_⟩
  rw [rayPolynomial_eval]
  have h := hd₀ (fun i => a i * n + E i) (fun i =>
    (Finset.le_sup (Finset.mem_univ i)).trans (hn.trans
      ((Nat.le_mul_of_pos_left n (by have := ha i; omega)).trans (Nat.le_add_right _ _))))
  simpa only [Nat.cast_add,Nat.cast_mul] using h

theorem dimension_le_of_shifted_hilbertFunction_le (S T : Set M.Point)
    (hS : S.Nonempty) (hT : T.Nonempty) (c E : M.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i)
    (hle : ∀ D : M.FactorIndex → ℕ,
      hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal S) D ≤
      hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal T)
        (fun i => c i * D i + E i)) :
    (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S)).totalDegree ≤
      (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal T)).totalDegree := by
  obtain ⟨P,hPd,hPlc,hPpos,NP,hP⟩ := exists_ray_hilbertPolynomial M hS (fun _ => 1) 0
    (fun _ => le_rfl)
  obtain ⟨Q,hQd,hQlc,hQpos,NQ,hQ⟩ := exists_ray_hilbertPolynomial M hT c E hc
  rw [← hPd,← hQd]
  apply natDegree_le_of_eventual_eval_le P Q hPpos hQpos
  apply eventually_atTop.mpr
  refine ⟨max NP NQ,fun n hn => ?_⟩
  rw [hP n ((le_max_left _ _).trans hn),hQ n ((le_max_right _ _).trans hn)]
  simpa only [Pi.zero_apply,one_mul,add_zero,Nat.cast_le] using hle (fun _ => n)

theorem degreeValue_le_of_shifted_hilbertFunction_le (S T : Set M.Point)
    (hS : S.Nonempty) (hT : T.Nonempty) (c E : M.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i)
    (hle : ∀ D : M.FactorIndex → ℕ,
      hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal S) D ≤
      hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal T)
        (fun i => c i * D i + E i))
    (hdim : (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S)).totalDegree =
      (hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal T)).totalDegree)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    degreeValue K M.factorCount M.ambientDimension (M.vanishingIdeal S) D ≤
      degreeValue K M.factorCount M.ambientDimension (M.vanishingIdeal T) (fun i => c i * D i) := by
  obtain ⟨P,hPd,hPlc,hPpos,NP,hP⟩ := exists_ray_hilbertPolynomial M hS D 0 hD
  obtain ⟨Q,hQd,hQlc,hQpos,NQ,hQ⟩ := exists_ray_hilbertPolynomial M hT (fun i => c i * D i) E
    (fun i => by have := hc i; have := hD i; nlinarith)
  have hlc : P.leadingCoeff ≤ Q.leadingCoeff := by
    apply leadingCoeff_le_of_eventual_eval_le P Q hPpos hQpos (by rw [hPd,hQd,hdim])
    apply eventually_atTop.mpr
    refine ⟨max NP NQ,fun n hn => ?_⟩
    rw [hP n ((le_max_left _ _).trans hn),hQ n ((le_max_right _ _).trans hn)]
    simpa only [Pi.zero_apply,add_zero,mul_assoc,Nat.cast_le] using hle (fun i => D i * n)
  rw [hPlc,hQlc] at hlc
  unfold degreeValue degreeForm
  simp only [MvPolynomial.smul_eq_C_mul,map_mul,eval_C]
  rw [hdim]
  exact mul_le_mul_of_nonneg_left (by simpa only [hdim] using hlc) (Nat.cast_nonneg _)

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponTranslatedDegree

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

theorem translated_dimension_and_degree (c : G.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hbound : TranslationDegreeBound G c)
    (g : G.Point) (V : Set G.Point) :
    varietyDimension G V = varietyDimension G (translate g V) ∧
    ∀ D : G.FactorIndex → ℕ, (∀ i, 1 ≤ D i) →
      hilbertDegreeForm G V D ≤
        hilbertDegreeForm G (translate g V) (fun i => c i * D i) := by
  classical
  by_cases hV : V.Nonempty
  · have hW : (translate g V).Nonempty := hV.image (fun x => g+x)
    have hS := hV.image G.embedding
    have hT := hW.image G.embedding
    have hback : translate (-g) (translate g V) = V := by
      ext x
      constructor
      · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
        simpa only [← add_assoc,neg_add_cancel,zero_add] using hz
      · intro hx
        exact ⟨g+x,⟨x,hx,rfl⟩,by simp only [← add_assoc,neg_add_cancel,zero_add]⟩
    obtain ⟨atlas,ha⟩ := hbound g
    obtain ⟨atlas',ha'⟩ := hbound (-g)
    obtain ⟨E,hE⟩ := TranslationSupport.translated_hilbertFunction_le V g c atlas ha
    obtain ⟨E',hE'⟩ := TranslationSupport.translated_hilbertFunction_le (translate g V) (-g)
      c atlas' ha'
    rw [hback] at hE'
    have hd₁ := Hilbert.dimension_le_of_shifted_hilbertFunction_le G.ambient
      (G.embedding '' translate g V) (G.embedding '' V) hT hS c E hc hE
    have hd₂ := Hilbert.dimension_le_of_shifted_hilbertFunction_le G.ambient
      (G.embedding '' V) (G.embedding '' translate g V) hS hT c E' hc hE'
    have heq : varietyDimension G V = varietyDimension G (translate g V) :=
      le_antisymm hd₂ hd₁
    refine ⟨heq,fun D hD => ?_⟩
    have hdeg := Hilbert.degreeValue_le_of_shifted_hilbertFunction_le G.ambient
      (G.embedding '' V) (G.embedding '' translate g V) hS hT c E' hc hE' heq D hD
    change (Hilbert.degreeValue K G.ambient.factorCount G.ambient.ambientDimension
      (G.ambient.vanishingIdeal (G.embedding '' V)) D : ℝ) ≤
      (Hilbert.degreeValue K G.ambient.factorCount G.ambient.ambientDimension
        (G.ambient.vanishingIdeal (G.embedding '' translate g V)) (fun i => c i * D i) : ℝ)
    exact_mod_cast hdeg
  · have hV' : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hV
    subst V
    have hW : translate g (∅ : Set G.Point) = ∅ := Set.image_empty _
    have hzero : Hilbert.hilbertPolynomial K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal ∅) = 0 := by
      change Hilbert.hilbertPolynomial K G.ambient.factorCount G.ambient.ambientDimension
        (G.ambient.vanishingIdeal (G.embedding '' ∅)) = 0
      rw [Set.image_empty]
      exact G.ambient.hilbertPolynomial_empty
    rw [hW]
    refine ⟨rfl,fun D hD => ?_⟩
    simp only [hilbertDegreeForm,Hilbert.degreeValue,Hilbert.degreeForm,hzero,
      map_zero,smul_zero,Rat.cast_zero,le_refl]

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponConnectedComponents

set_option autoImplicit false
set_option maxHeartbeats 600000
open Set TopologicalSpace
open scoped Topology Pointwise
noncomputable section

namespace PhilipponMultiplicity

theorem finite_connectedComponents_of_noetherian (X : Type*) [TopologicalSpace X]
    [NoetherianSpace X] : Finite (ConnectedComponents X) := by
  classical
  let C := irreducibleComponents X
  letI : Fintype C := NoetherianSpace.finite_irreducibleComponents.fintype
  choose point hpoint using fun c : C => c.property.1.nonempty
  apply Finite.of_surjective (fun c : C => ConnectedComponents.mk (point c))
  intro q
  obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe q
  let c : C := ⟨irreducibleComponent x,irreducibleComponent_mem_irreducibleComponents x⟩
  refine ⟨c,ConnectedComponents.coe_eq_coe'.mpr ?_⟩
  exact irreducibleComponent_subset_connectedComponent (hpoint c)

def connectedZeroSubgroup (X : Type*) [TopologicalSpace X] [AddGroup X]
    [SeparatelyContinuousAdd X] [ContinuousNeg X] : AddSubgroup X where
  carrier := connectedComponent (0 : X)
  zero_mem' := mem_connectedComponent
  add_mem' {x y} hx hy := by
    rw [connectedComponent_eq hx]
    have h : x ∈ connectedComponent (x+y) := by
      apply Continuous.image_connectedComponent_subset (continuous_const_add x)
      rw [← connectedComponent_eq hy]
      exact ⟨0,mem_connectedComponent,add_zero x⟩
    simpa only [← connectedComponent_eq h] using (mem_connectedComponent (x := x+y))
  neg_mem' := neg_mem_connectedComponent_zero

variable {K : Type*} [Field K] {G : EmbeddedGroupProduct K}

theorem AlgebraicSubgroup.exists_identityAlgebraicSubgroup (H : AlgebraicSubgroup G) :
    ∃ H₀ : AlgebraicSubgroup G, H₀.carrier = H.identityComponent ∧ H₀.IsConnected ∧
      @IsIrreducible _ G.zariskiTopology H₀.carrier := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : SeparatelyContinuousAdd G.Point := G.zariski_separatelyContinuousAdd
  letI : ContinuousNeg G.Point := G.zariski_continuousNeg
  letI : SeparatelyContinuousAdd H.toAddSubgroup :=
    separatelyContinuousAdd_induced H.toAddSubgroup.subtype
  letI : ContinuousNeg H.toAddSubgroup :=
    ⟨continuous_induced_rng.mpr (continuous_neg.comp continuous_subtype_val)⟩
  let J := connectedZeroSubgroup H.toAddSubgroup
  let H₀ : AlgebraicSubgroup G :=
    { toAddSubgroup := J.map H.toAddSubgroup.subtype
      isClosed := H.isClosed.isClosedMap_subtype_val _ isClosed_connectedComponent }
  have heq : H₀.carrier = H.identityComponent := by
    change Subtype.val '' connectedComponent (0 : H.toAddSubgroup) =
      connectedComponentIn H.carrier 0
    exact (connectedComponentIn_eq_image H.toAddSubgroup.zero_mem).symm
  have hconn : H₀.IsConnected := by
    rw [AlgebraicSubgroup.IsConnected,heq]
    exact isConnected_connectedComponentIn_iff.mpr H.toAddSubgroup.zero_mem
  exact ⟨H₀,heq,hconn,H₀.isIrreducible_of_isConnected hconn⟩

theorem AlgebraicSubgroup.exists_finite_identity_cosets (H : AlgebraicSubgroup G) :
    ∃ H₀ : AlgebraicSubgroup G,
      H₀.carrier = H.identityComponent ∧ H₀.IsConnected ∧
      @IsIrreducible _ G.zariskiTopology H₀.carrier ∧
      ∃ representatives : Finset G.Point,
        (∀ x ∈ representatives, x ∈ H.carrier) ∧
        H.carrier = ⋃ x ∈ representatives, translate x H₀.carrier ∧
        (representatives : Set G.Point).Pairwise (fun x y => Disjoint
          (translate x H₀.carrier) (translate y H₀.carrier)) := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : SeparatelyContinuousAdd G.Point := G.zariski_separatelyContinuousAdd
  letI : SeparatelyContinuousAdd H.toAddSubgroup :=
    separatelyContinuousAdd_induced H.toAddSubgroup.subtype
  letI : NoetherianSpace G.Point := G.ambient.noetherian_induced G.embedding
  letI : NoetherianSpace H.toAddSubgroup := Topology.IsInducing.subtypeVal.noetherianSpace
  letI : Finite (ConnectedComponents H.toAddSubgroup) :=
    finite_connectedComponents_of_noetherian H.toAddSubgroup
  letI := Fintype.ofFinite (ConnectedComponents H.toAddSubgroup)
  choose point hpoint using (ConnectedComponents.surjective_coe (α := H.toAddSubgroup))
  obtain ⟨H₀,heq,hconn,hirr⟩ := H.exists_identityAlgebraicSubgroup
  have hcoset (c : ConnectedComponents H.toAddSubgroup) :
      translate (point c).val H₀.carrier = Subtype.val '' connectedComponent (point c) := by
    calc
      translate (point c).val H₀.carrier = Subtype.val ''
          ((fun x : H.toAddSubgroup => point c + x) '' connectedComponent (0 : H.toAddSubgroup)) := by
        rw [heq]
        change translate (point c).val (connectedComponentIn (H.toAddSubgroup : Set G.Point) 0) = _
        rw [connectedComponentIn_eq_image H.toAddSubgroup.zero_mem]
        simp only [translate,image_image]
        rfl
      _ = Subtype.val '' connectedComponent (point c) := by
        congr 1
        have hh := vadd_connectedComponent (point c) (0 : H.toAddSubgroup)
        change (fun x : H.toAddSubgroup => point c + x) '' connectedComponent 0 =
          connectedComponent (point c + 0) at hh
        simpa only [add_zero] using hh
  let reps := Finset.univ.image (fun c => (point c).val)
  refine ⟨H₀,heq,hconn,hirr,reps,?_,?_,?_⟩
  · intro x hx
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hx
    exact (point c).property
  · ext x
    constructor
    · intro hx
      let c := ConnectedComponents.mk (⟨x,hx⟩ : H.toAddSubgroup)
      apply mem_iUnion.mpr
      refine ⟨(point c).val,mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩,?_⟩⟩
      rw [hcoset]
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      exact ConnectedComponents.coe_eq_coe'.mp (hpoint c).symm
    · intro hx
      obtain ⟨y,hy⟩ := mem_iUnion.mp hx
      obtain ⟨hy,hx⟩ := mem_iUnion.mp hy
      obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hy
      rw [hcoset] at hx
      obtain ⟨z,_,rfl⟩ := hx
      exact z.property
  · intro x hx y hy hxy
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hy
    rw [hcoset,hcoset]
    apply Set.disjoint_image_of_injective Subtype.val_injective
    apply connectedComponent_disjoint
    intro he
    have hcd : c = d := by
      rw [← hpoint c,← hpoint d]
      exact ConnectedComponents.coe_eq_coe.mpr he
    exact hxy (congrArg (fun q => (point q).val) hcd)

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponContactCosets

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

def TranslationChart.polynomialChart [CompleteSpace K] {g : G.Point}
    (chart : TranslationChart A g) : PolynomialTranslationChart G g where
  domain := chart.domain
  domain_open := chart.domain_isOpen
  degree := chart.degree
  coordinates v := polynomialOperator chart 0 Fin.elim0 (MvPolynomial.X v)
  homogeneous v := by
    have h := polynomialOperator_homogeneous chart 0 Fin.elim0 (MvPolynomial.X v)
      (fun i => if i = v.1 then 1 else 0) (G.ambient.isHomogeneous_X v)
    simpa only [mul_ite,mul_one,mul_zero] using h
  represents x hx := by
    have he (v : G.ambient.Variable) :
        G.ambient.eval (polynomialOperator chart 0 Fin.elim0 (MvPolynomial.X v))
          (G.embedding x) = evaluateCoefficientPolynomial A (chart.coordinates v) x 0 := by
      rw [polynomialOperator_eval]
      simp only [iteratedFDeriv_zero_apply,MvPolynomial.eval_X]
    simp_rw [he]
    have hh := Filter.Eventually.self_of_nhds (chart.represents x hx)
    simpa only [A.map_zero,add_zero,add_comm x g] using hh.2

def TranslationAtlas.polynomialAtlas [CompleteSpace K] {g : G.Point}
    (atlas : TranslationAtlas A g) : PolynomialTranslationAtlas G g where
  Index := atlas.Index
  chart a := (atlas.chart a).polynomialChart
  covers := atlas.covers

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponGroupEquidimensional

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K]

def AnalyticSubgroup.trivial (G : EmbeddedGroupProduct K) : AnalyticSubgroup G where
  parameterDimension := 1
  parameterDimension_pos := by decide
  radius := 1
  radius_pos := by norm_num
  domain := Metric.ball 0 1
  domain_eq_ball := rfl
  domain_open := Metric.isOpen_ball
  zero_mem := by simp
  map := fun _ => 0
  map_zero := rfl
  map_add := by intros; exact (zero_add 0).symm
  lift := fun g _ => G.ambient.coordinate (G.embedding g)
  lift_analytic := fun _ _ => analyticAt_const
  base_series := fun _ => ⟨_, hasFPowerSeriesOnBall_const.mono (by simp) le_top⟩
  base_represents := fun _ i => ⟨Projectivization.rep_nonzero (G.embedding 0 i),
    Projectivization.mk_rep (G.embedding 0 i)⟩
  lift_represents := by
    intro g
    filter_upwards [Metric.isOpen_ball.mem_nhds (show (0 : Fin 1 → K) ∈ Metric.ball 0 1 by simp)]
      with z hz
    refine ⟨hz, fun i => ⟨Projectivization.rep_nonzero (G.embedding g i), ?_⟩⟩
    simpa only [add_zero, MultiProjectiveSpace.coordinate] using
      Projectivization.mk_rep (G.embedding g i)

theorem exists_translationDegreeBound [CompleteSpace K] (G : EmbeddedGroupProduct K) :
    ∃ c : G.FactorIndex → ℕ, (∀ i, 1 ≤ c i) ∧ TranslationDegreeBound G c := by
  obtain ⟨c,hc,hatlas⟩ := AtlasSupport.exists_uniformly_bounded_translation_atlas (K := K)
  refine ⟨fun i => c (G.factor i), fun i => hc _, fun g => ?_⟩
  obtain ⟨atlas,hbound⟩ := hatlas G (AnalyticSubgroup.trivial G) g
  exact ⟨atlas.polynomialAtlas,hbound⟩

theorem varietyDimension_translate [CompleteSpace K] (G : EmbeddedGroupProduct K)
    (g : G.Point) (V : Set G.Point) :
    varietyDimension G (translate g V) = varietyDimension G V := by
  obtain ⟨c,hc,hbound⟩ := exists_translationDegreeBound G
  exact (translated_dimension_and_degree G c hc hbound g V).1.symm

theorem group_vanishingIdeal_iUnion (G : EmbeddedGroupProduct K) {ι : Type*}
    (V : ι → Set G.Point) :
    G.vanishingIdeal (⋃ i, V i) = ⨅ i, G.vanishingIdeal (V i) := by
  apply le_antisymm
  · exact le_iInf (fun i => G.ambient.vanishingIdeal_antitone
      (Set.image_mono (Set.subset_iUnion V i)))
  · let J := ⨅ i, G.vanishingIdeal (V i)
    have hJ : IsMultihomogeneousIdeal G.ambient J := by
      intro P hP D
      exact Ideal.mem_iInf.mpr (fun i =>
        vanishingIdeal_multihomogeneous K _ _ P (Ideal.mem_iInf.mp hP i) D)
    change J ≤ _
    rw [G.ambient.homogeneousIdeal_eq_span J hJ]
    apply Ideal.span_le.mpr
    rintro P ⟨hP,D,hD⟩
    apply Ideal.subset_span
    refine ⟨⟨D,hD⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,hxi⟩ := Set.mem_iUnion.mp hx
    exact G.ambient.eval_eq_zero_of_mem_vanishingIdeal
      (Ideal.mem_iInf.mp hP i) ⟨x,hxi,rfl⟩

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponSubgroupEquidimensional

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K]

theorem AlgebraicSubgroup.vanishingIdeal_equidimensional [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (H : AlgebraicSubgroup G) :
    ∀ q ∈ (G.vanishingIdeal H.carrier).minimalPrimes,
      SectionThree.idealDimension G.ambient q =
        SectionThree.idealDimension G.ambient (G.vanishingIdeal H.carrier) := by
  classical
  obtain ⟨H₀,_,hconn,_,R,_,hcover,_⟩ := H.exists_finite_identity_cosets
  let V (g : R) := translate g.val H₀.carrier
  have hcover' : H.carrier = ⋃ g : R, V g := by
    simpa only [V, Set.iUnion_subtype] using hcover
  let I := G.vanishingIdeal H.carrier
  have hI : IsMultihomogeneousIdeal G.ambient I := vanishingIdeal_multihomogeneous K _ _
  have heq : I = ⨅ g : R, G.vanishingIdeal (V g) := by
    change G.vanishingIdeal H.carrier = _
    rw [hcover', group_vanishingIdeal_iUnion]
  have hle (g : R) : I ≤ G.vanishingIdeal (V g) := heq ▸ iInf_le _ g
  have hprime (g : R) : (G.vanishingIdeal (V g)).IsPrime :=
    H₀.translated_vanishingIdeal_isPrime hconn g.val
  have hselect : ∀ q ∈ I.minimalPrimes, ∃ g : R, q = G.vanishingIdeal (V g) := by
    intro q hq
    have hinf : (Finset.univ : Finset R).inf (fun g => G.vanishingIdeal (V g)) ≤ q := by
      simpa only [Finset.inf_univ_eq_iInf, ← heq] using hq.le
    obtain ⟨g,_,hg⟩ := hq.isPrime.inf_le'.mp hinf
    exact ⟨g,le_antisymm (hq.2 ⟨hprime g,hle g⟩ hg) hg⟩
  have hdim (g : R) : SectionThree.idealDimension G.ambient (G.vanishingIdeal (V g)) =
      varietyDimension G H₀.carrier := varietyDimension_translate G g.val H₀.carrier
  intro q hq
  obtain ⟨g,rfl⟩ := hselect q hq
  apply le_antisymm
  · exact Hilbert.idealDimension_antitone G.ambient I _ hI
      (vanishingIdeal_multihomogeneous K _ _) (hle g)
  · apply Hilbert.idealDimension_le_of_minimalPrimes G.ambient I hI
    intro p hp _
    obtain ⟨h,rfl⟩ := hselect p hp
    exact le_of_eq ((hdim h).trans (hdim g).symm)

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponContactHilbertSubadditivity

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
namespace Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertFunction_inf_le_add (I J : Ideal M.CoordinateRing)
    (D : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension (I ⊓ J) D ≤
      hilbertFunction K M.factorCount M.ambientDimension I D +
        hilbertFunction K M.factorCount M.ambientDimension J D := by
  let W := degreePiece K M.factorCount M.ambientDimension D
  let f (L : Ideal M.CoordinateRing) :=
    (Ideal.Quotient.mkₐ K L).toLinearMap.domRestrict W
  have hr (L : Ideal M.CoordinateRing) : Module.finrank K (LinearMap.range (f L)) =
      hilbertFunction K M.factorCount M.ambientDimension L D := by
    rw [LinearMap.range_domRestrict]
    rfl
  have hk : LinearMap.ker (f (I ⊓ J)) = LinearMap.ker (f I) ⊓ LinearMap.ker (f J) := by
    ext P
    change Ideal.Quotient.mk (I ⊓ J) P.val = 0 ↔
      Ideal.Quotient.mk I P.val = 0 ∧ Ideal.Quotient.mk J P.val = 0
    simp only [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_inf]
  have hI := (f I).finrank_range_add_finrank_ker
  have hJ := (f J).finrank_range_add_finrank_ker
  have hIJ := (f (I ⊓ J)).finrank_range_add_finrank_ker
  rw [hr I] at hI
  rw [hr J] at hJ
  rw [hr (I ⊓ J), hk] at hIJ
  have hdim := (LinearMap.ker (f I)).finrank_sup_add_finrank_inf_eq (LinearMap.ker (f J))
  have hle := Submodule.finrank_le (LinearMap.ker (f I) ⊔ LinearMap.ker (f J))
  omega

theorem hilbertFunction_top (D : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension (⊤ : Ideal M.CoordinateRing) D = 0 := by
  exact Module.finrank_zero_of_subsingleton

theorem hilbertFunction_finset_iInf_le_sum {ι : Type*} (s : Finset ι)
    (I : ι → Ideal M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension (⨅ i ∈ s, I i) D ≤
      ∑ i ∈ s, hilbertFunction K M.factorCount M.ambientDimension (I i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hilbertFunction_top M]
  | @insert a s ha ih =>
    simp only [Finset.iInf_insert, Finset.sum_insert ha]
    exact (hilbertFunction_inf_le_add M _ _ D).trans (Nat.add_le_add_left ih _)

end Hilbert

open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

end PhilipponMultiplicity
end
end

section
-- Reused implementation: Solutions.PhilipponMasserWustholzComponentCounting

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MWComponentCounting

theorem localLength_one_le {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    1 ≤ (Hilbert.localLength K M.factorCount M.ambientDimension I q).toNat := by
  let A := Localization.AtPrime q.asIdeal
  let J := I.map (algebraMap M.CoordinateRing A)
  have hle : J ≤ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal A]
    exact Ideal.map_mono hq.le
  have hne : J ≠ ⊤ := ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hle
  letI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact Nat.succ_le_of_lt (ENat.toNat_pos (Module.length_pos (R := A) (M := A ⧸ J)).ne'
    (Hilbert.localLength_ne_top K M.factorCount M.ambientDimension I q hq))

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsAlgClosed K]
  (G : EmbeddedGroupProduct K)

end PhilipponMultiplicity.MWComponentCounting

end
end

section
-- Reused implementation: Solutions.PhilipponGroupReduced

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem Hilbert.radical_multihomogeneous (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) : IsMultihomogeneousIdeal M I.radical := by
  classical
  let w : M.Variable → Lex (M.FactorIndex → ℕ) :=
    fun x => toLex (Hilbert.blockWeight M.factorCount M.ambientDimension x)
  letI : DecidableEq (Lex (M.FactorIndex → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra K w
  have hproj (f : M.CoordinateRing) (d : Lex (M.FactorIndex → ℕ)) :
      weightedHomogeneousComponent w d f =
        weightedHomogeneousComponent (Hilbert.blockWeight M.factorCount M.ambientDimension)
          (ofLex d) f := by
    ext e
    simp only [coeff_weightedHomogeneousComponent]
    rfl
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    rw [MvPolynomial.decompose'_apply, hproj]
    exact hI f hf (ofLex d)
  intro f hf d
  have h := weightedHomogeneousComponent_mem_of_mem K w hIg.radical hf (toLex d)
  rwa [hproj] at h

theorem MultiProjectiveSpace.vanishingIdeal_isRadical (S : Set M.Point) :
    (M.vanishingIdeal S).IsRadical := by
  apply Ideal.radical_eq_iff.mp
  apply le_antisymm ?_ Ideal.le_radical
  rw [M.homogeneousIdeal_eq_span _
    (Hilbert.radical_multihomogeneous M _ (vanishingIdeal_multihomogeneous K M S))]
  apply Ideal.span_le.mpr
  rintro P ⟨hP, D, hD⟩
  obtain ⟨n, hn⟩ := hP
  refine Ideal.subset_span ⟨⟨D, hD⟩, ?_⟩
  intro x hx
  have h := M.eval_eq_zero_of_mem_vanishingIdeal hn hx
  change MvPolynomial.eval (M.coordinate x) (P ^ n) = 0 at h
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponSubgroupHilbertUpperReduction

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem irrelevant_prime_hilbertFunction_zero (Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hirr : ¬ IsRelevant K M.factorCount M.ambientDimension Q)
    (d : M.FactorIndex → ℕ) (hd : ∀ i, 1 ≤ d i) :
    hilbertFunction K M.factorCount M.ambientDimension Q d = 0 := by
  classical
  have hle : irrelevantIdeal K M.factorCount M.ambientDimension ≤ Q := not_not.mp hirr
  have hfin : Finset.univ.inf (blockIdeal K M.factorCount M.ambientDimension) ≤ Q := by
    simpa only [irrelevantIdeal, Finset.inf_eq_iInf, Finset.mem_univ, iInf_true] using hle
  obtain ⟨i, _, hi⟩ := hQ.inf_le'.mp hfin
  have hz : quotientPiece K M.factorCount M.ambientDimension Q d = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨P, hP, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hi (homogeneous_mem_blockIdeal M i d (hd i) P ((M.degreePiece_iff _ _).mp hP)))
  rw [hilbertFunction, hz, finrank_bot]

theorem radical_equidimensional_upper_of_prime_bounds
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hrad : I.IsRadical)
    (hdim : ∀ q ∈ I.minimalPrimes, IsRelevant K M.factorCount M.ambientDimension q →
      idealDimension M q = idealDimension M I)
    (d D : M.FactorIndex → ℕ) (hd : ∀ i, 1 ≤ d i)
    (C : ℚ) (hC : 0 ≤ C)
    (hprime : ∀ q ∈ I.minimalPrimes, IsRelevant K M.factorCount M.ambientDimension q →
      (hilbertFunction K M.factorCount M.ambientDimension q d : ℚ) ≤
        C * idealDegreeValue M q D) :
    (hilbertFunction K M.factorCount M.ambientDimension I d : ℚ) ≤
      C * idealDegreeValue M I D := by
  classical
  let T := MinimalComponent K M.factorCount M.ambientDimension I
  letI := Fintype.ofFinite T
  have hIeq : I = ⨅ q : T, q.val.asIdeal := by
    apply le_antisymm (le_iInf fun q => q.property.le)
    have hle : (⨅ q : T, q.val.asIdeal) ≤ sInf I.minimalPrimes := by
      apply le_sInf
      intro q hq
      exact iInf_le (fun q : T => q.val.asIdeal) ⟨⟨q, hq.isPrime⟩, hq⟩
    exact hle.trans_eq (Ideal.sInf_minimalPrimes.trans hrad.radical)
  have hrank : hilbertFunction K M.factorCount M.ambientDimension I d ≤
      ∑ q : T, hilbertFunction K M.factorCount M.ambientDimension q.val.asIdeal d := by
    have h := hilbertFunction_finset_iInf_le_sum M (Finset.univ : Finset T)
      (fun q => q.val.asIdeal) d
    simpa only [Finset.mem_univ, iInf_true, ← hIeq] using h
  calc
    _ ≤ ((∑ q : T, hilbertFunction K M.factorCount M.ambientDimension q.val.asIdeal d : ℕ) : ℚ) := by
      exact_mod_cast hrank
    _ ≤ C * topComponentLengthSum M I D := by
      rw [Nat.cast_sum]
      unfold topComponentLengthSum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q _
      by_cases hrel : IsRelevant K M.factorCount M.ambientDimension q.val.asIdeal
      · rw [if_pos ⟨hrel, hdim _ q.property hrel⟩]
        apply (hprime _ q.property hrel).trans
        apply mul_le_mul_of_nonneg_left _ hC
        have hlen : (1 : ℚ) ≤ (localLength K M.factorCount M.ambientDimension I q.val).toNat := by
          exact_mod_cast MWComponentCounting.localLength_one_le M I q.val q.property
        have hdeg := PrimaryComponentSupport.degreeValue_nonneg M q.val.asIdeal
          (minimalPrime_homogeneous M I _ hI q.property) D
        simpa only [one_mul, idealDegreeValue] using mul_le_mul_of_nonneg_right hlen hdeg
      · rw [if_neg (fun h => hrel h.1), mul_zero,
          irrelevant_prime_hilbertFunction_zero M _ q.val.isPrime hrel d hd, Nat.cast_zero]
    _ = _ := by rw [← component_length_formula M I hI D]

theorem multigraded_upper_of_ordinary_prime_bound
    (hOrdinary : ∀ (N : ℕ) (p : Ideal (projectiveSpace K N).CoordinateRing),
      p.IsPrime → IsMultihomogeneousIdeal (projectiveSpace K N) p →
      (hilbertFunction K 1 (fun _ => N) p (fun _ => 2) : ℚ) ≤
        (Nat.choose (idealDimension (projectiveSpace K N) p + 2)
          (idealDimension (projectiveSpace K N) p) : ℚ) *
          idealDegreeValue (projectiveSpace K N) p (fun _ => 1))
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hrad : I.IsRadical)
    (hdim : ∀ q ∈ I.minimalPrimes,
      idealDimension M q = idealDimension M I)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    (hilbertFunction K M.factorCount M.ambientDimension I (fun i => 2 * D i) : ℚ) ≤
      (Nat.choose (idealDimension M I + 2) (idealDimension M I) : ℚ) * idealDegreeValue M I D := by
  classical
  apply radical_equidimensional_upper_of_prime_bounds M I hI hrad
    (fun q hq _ => hdim q hq) _ D (fun i => by have := hD i; omega) _ (Nat.cast_nonneg _)
  intro q hq hrel
  have hqhom := minimalPrime_homogeneous M I q hI hq
  have hqne := relevant_prime_hilbertPolynomial_ne_zero M q hq.isPrime hqhom hrel
  obtain ⟨N, ⟨b⟩⟩ := SegreVeronese.exists_coordinate_basis M D
  have h := hOrdinary N (SegreVeronese.diagonalIdeal M D b q)
    (SegreVeronese.diagonalIdeal_isPrime M D b q hq.isPrime)
    (SegreVeronese.diagonalIdeal_homogeneous M D b hD q hqhom)
  rw [SegreVeronese.hilbertFunction_diagonal,
    SegreVeronese.dimension_diagonal M D b hD q hqhom hqne,
    SegreVeronese.degreeValue_diagonal M D b hD q hqhom hqne, hdim q hq] at h
  exact h

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity
open SectionThree

theorem subgroup_hilbert_upper_of_ordinary_prime_bound
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hOrdinary : ∀ (N : ℕ) (p : Ideal (projectiveSpace K N).CoordinateRing),
      p.IsPrime → IsMultihomogeneousIdeal (projectiveSpace K N) p →
      (Hilbert.hilbertFunction K 1 (fun _ => N) p (fun _ => 2) : ℚ) ≤
        (Nat.choose (idealDimension (projectiveSpace K N) p + 2)
          (idealDimension (projectiveSpace K N) p) : ℚ) *
          idealDegreeValue (projectiveSpace K N) p (fun _ => 1))
    (G : EmbeddedGroupProduct K) (H : AlgebraicSubgroup G)
    (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
      (G.vanishingIdeal H.carrier) (fun i => 2 * D i) : ℝ) ≤
      (Nat.choose (varietyDimension G H.carrier + 2) (varietyDimension G H.carrier) : ℝ) *
        hilbertDegreeForm G H.carrier D := by
  letI : CompleteSpace K := hK.completeSpace
  have h := Hilbert.multigraded_upper_of_ordinary_prime_bound G.ambient hOrdinary
    (G.vanishingIdeal H.carrier) (vanishingIdeal_multihomogeneous K _ _)
    (G.ambient.vanishingIdeal_isRadical _) (H.vanishingIdeal_equidimensional G) D hD
  change (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
      (G.vanishingIdeal H.carrier) (fun i => 2 * D i) : ℝ) ≤
      (Nat.choose (varietyDimension G H.carrier + 2) (varietyDimension G H.carrier) : ℝ) *
        (idealDegreeValue G.ambient (G.vanishingIdeal H.carrier) D : ℝ)
  exact_mod_cast h

end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponGenericFreeAlgebra

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped nonZeroDivisors TensorProduct
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {R A F L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A]
  [Field F] [Field L] [Algebra R F] [Algebra R L] [Algebra A L] [Algebra F L]
  [IsScalarTower R A L] [IsScalarTower R F L]
  [IsFractionRing R F] [IsFractionRing A L]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem exists_basis_base_open :
    ∃ s : R, s ≠ 0 ∧ Nonempty (Module.Basis (Fin (Module.finrank F L))
      (Localization.Away s) (Localization.Away s ⊗[R] A)) := by
  let : Module.Finite F L := .of_isLocalization R A R⁰
  let : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  let f := (IsScalarTower.toAlgHom R A L).toLinearMap
  obtain ⟨s, hs, b, _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    R⁰ f F (Module.finBasis F L)
  refine ⟨s, mem_nonZeroDivisors_iff_ne_zero.mp hs, ?_⟩
  let S := Localization.Away s
  let B := S ⊗[R] A
  let g := (IsScalarTower.toAlgHom R A B).toLinearMap
  let e := IsLocalizedModule.iso (.powers s) g
  let e' : LocalizedModule.Away s A ≃ₗ[S] B :=
    { __ := e,
      toLinearMap := e.toLinearMap.extendScalarsOfIsLocalization (.powers s) S }
  exact ⟨b.map e'⟩

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponGenericEtaleBaseOpen

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped nonZeroDivisors
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {R A F L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A]
  [Field F] [Field L] [Algebra R F] [Algebra R L] [Algebra A L] [Algebra F L]
  [IsScalarTower R A L] [IsScalarTower R F L]
  [IsFractionRing R F] [IsFractionRing A L] [Algebra.IsSeparable F L]

include F L

theorem exists_etale_base_open :
    ∃ s : R, s ≠ 0 ∧ Algebra.FormallyEtale R
      (Localization.Away (algebraMap R A s)) := by
  let : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.FormallyEtale R F := Algebra.FormallyEtale.of_isLocalization R⁰
  let : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  let : Algebra.FormallyEtale R L := Algebra.FormallyEtale.comp R F L
  let : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    have he : (⊥ : Ideal A).primeCompl = A⁰ := by
      ext x
      simp [mem_nonZeroDivisors_iff_ne_zero]
    change IsLocalization A⁰ (Localization.AtPrime (⊥ : Ideal A))
    rw [← he]
    infer_instance
  let e := (IsLocalization.algEquiv A⁰ L (Localization.AtPrime (⊥ : Ideal A))).restrictScalars R
  let : Algebra.IsEtaleAt R (⊥ : Ideal A) := Algebra.FormallyEtale.of_equiv e
  obtain ⟨a, ha, het⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) (⊥ : Ideal A)
  have hane : a ≠ 0 := ha
  have hI : (Ideal.span ({a} : Set A)).under R ≠ ⊥ :=
    Ideal.under_ne_bot R (by simpa using hane)
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine ⟨s, hs0, ?_⟩
  have hd : PrimeSpectrum.basicOpen (algebraMap R A s) ≤ PrimeSpectrum.basicOpen a := by
    change algebraMap R A s ∈ Ideal.span ({a} : Set A) at hs
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hs
    rw [hb, PrimeSpectrum.basicOpen_mul]
    exact inf_le_left
  have hsource : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) ⊆
      Algebra.etaleLocus R A :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr het
  exact Algebra.basicOpen_subset_etaleLocus_iff.mp (fun p hp => hsource (hd hp))

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponFiniteFreeEtaleOpen

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped nonZeroDivisors TensorProduct
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {R A F L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A]
  [Field F] [Field L] [Algebra R F] [Algebra R L] [Algebra A L] [Algebra F L]
  [IsScalarTower R A L] [IsScalarTower R F L]
  [IsFractionRing R F] [IsFractionRing A L] [Algebra.IsSeparable F L]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem exists_finite_free_etale_base_open :
    ∃ t : R, t ≠ 0 ∧
      Nonempty (Module.Basis (Fin (Module.finrank F L))
        (Localization.Away t) (Localization.Away t ⊗[R] A)) ∧
      Algebra.FormallyEtale (Localization.Away t) (Localization.Away t ⊗[R] A) := by
  obtain ⟨q, hq, ⟨b⟩⟩ := exists_basis_base_open (R := R) (A := A) (F := F) (L := L)
  obtain ⟨s, hs, het⟩ := exists_etale_base_open (R := R) (A := A) (F := F) (L := L)
  let t := q * s
  let S := Localization.Away q
  let T := Localization.Away t
  let B := T ⊗[R] A
  let : Algebra S T := (IsLocalization.Away.awayToAwayRight (S := S) (P := T) q s).toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.awayToAwayRight_eq q s x).symm
  let bT : Module.Basis (Fin (Module.finrank F L)) T B :=
    (Algebra.TensorProduct.basis T b).map
      (Algebra.TensorProduct.cancelBaseChange R S T T A).toLinearEquiv
  refine ⟨t, mul_ne_zero hq hs, ⟨bT⟩, ?_⟩
  have hd : PrimeSpectrum.basicOpen (algebraMap R A t) ≤
      PrimeSpectrum.basicOpen (algebraMap R A s) := by
    rw [show algebraMap R A t = algebraMap R A q * algebraMap R A s from map_mul _ _ _,
      PrimeSpectrum.basicOpen_mul]
    exact inf_le_right
  have hsource := Algebra.basicOpen_subset_etaleLocus_iff.mpr het
  let : Algebra.FormallyEtale R (Localization.Away (algebraMap R A t)) :=
    Algebra.basicOpen_subset_etaleLocus_iff.mp (fun p hp => hsource (hd hp))
  let : IsLocalization.Away (algebraMap R A t) B := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid A (.powers t)) B)
  let e := (IsLocalization.algEquiv (.powers (algebraMap R A t))
    (Localization.Away (algebraMap R A t)) B).restrictScalars R
  let : Algebra.FormallyEtale R B := Algebra.FormallyEtale.of_equiv e
  exact Algebra.FormallyEtale.localization_base (.powers t)

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponPowerSeriesResidue

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Chardin
open MvPowerSeries

theorem powerSeries_constantCoeff_ker (σ R : Type*) [Finite σ] [CommRing R] :
    RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R) =
      Ideal.span (Set.range X) := by
  let I := MvPolynomial.idealOfVars σ R
  let e := toAdicCompletionAlgEquiv σ R
  have hmap : Ideal.map e.toRingEquiv (Ideal.span (Set.range X)) =
      I.map (algebraMap (MvPolynomial σ R) (AdicCompletion I (MvPolynomial σ R))) := by
    change Ideal.map e.toRingEquiv (Ideal.span (Set.range X)) =
      Ideal.map _ (Ideal.span (Set.range MvPolynomial.X))
    simp_rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp [e, I, AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X,
      toAdicCompletion_coe]
  have hpre : (RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom).comap e.toRingEquiv =
      Ideal.span (Set.range X) := by
    rw [AdicCompletion.ker_evalOneₐ_eq_map I (MvPolynomial.idealOfVars_fg σ R), ← hmap]
    exact Ideal.comap_map_of_bijective e.toRingEquiv e.bijective
  rw [← hpre]
  ext f
  change constantCoeff f = 0 ↔ AdicCompletion.evalOneₐ I (e f) = 0
  have heval : AdicCompletion.evalOneₐ I (e f) = Ideal.Quotient.mk I (truncTotal 1 f) := rfl
  rw [heval, Ideal.Quotient.eq_zero_iff_mem]
  change constantCoeff f = 0 ↔ truncTotal 1 f ∈ MvPolynomial.idealOfVars σ R
  rw [← pow_one (MvPolynomial.idealOfVars σ R), MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro hf d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst d
    rw [coeff_truncTotal f (by simp), coeff_zero_eq_constantCoeff]
    exact hf
  · intro hf
    have h := hf 0 (by simp)
    rwa [coeff_truncTotal f (by simp), coeff_zero_eq_constantCoeff] at h

theorem powerSeries_complete_constantCoeff_ker (σ R : Type*) [Finite σ] [CommRing R] :
    IsAdicComplete (RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R))
      (MvPowerSeries σ R) := by
  rw [powerSeries_constantCoeff_ker]
  infer_instance

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponBranchProductNorm

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {R A S ι : Type*} [CommRing R] [CommRing A] [CommRing S]
  [Algebra R A] [Algebra R S] [Fintype ι] [DecidableEq ι]

theorem branch_matrix_mul (b : Module.Basis ι R A) (f : ι → A →ₐ[R] S) (x : A) :
    (Matrix.of fun i j => f i (b j)) *
        ((Algebra.leftMulMatrix b x).map (algebraMap R S)) =
      Matrix.diagonal (fun i => f i x) * (Matrix.of fun i j => f i (b j)) := by
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply,
    Algebra.leftMulMatrix_eq_repr_mul]
  calc
    _ = f i (∑ k, b.repr (x * b j) k • b k) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_smul, Algebra.smul_def, mul_comm]
    _ = f i x * f i (b j) := by rw [b.sum_repr, map_mul]

theorem norm_eq_branch_product (b : Module.Basis ι R A) (f : ι → A →ₐ[R] S)
    (hdet : IsUnit (Matrix.det (fun i j => f i (b j)))) (x : A) :
    algebraMap R S (Algebra.norm R x) = ∏ i, f i x := by
  have h := congrArg Matrix.det (branch_matrix_mul b f x)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h
  have hm : Matrix.det ((Algebra.leftMulMatrix b x).map (algebraMap R S)) =
      algebraMap R S (Algebra.norm R x) := by
    rw [Algebra.norm_eq_matrix_det b]
    exact (RingHom.map_det (algebraMap R S) _).symm
  rw [hm] at h
  apply hdet.mul_left_cancel
  exact h.trans (mul_comm _ _)

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponEtaleFiberMatrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators TensorProduct Matrix
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {R A K ι : Type*} [CommRing R] [CommRing A] [Field K] [IsSepClosed K]
  [Algebra R A] [Algebra R K] [Fintype ι] [DecidableEq ι]

theorem exists_etale_fiber_matrix [Algebra.FormallyEtale R A]
    (b : Module.Basis ι R A) :
    ∃ φ : ι → A →ₐ[R] K, Matrix.det (fun i j => φ i (b j)) ≠ 0 := by
  classical
  let : Module.Finite R A := Module.Finite.of_basis b
  let C := K ⊗[R] A
  let bK : Module.Basis ι K C := Algebra.TensorProduct.basis K b
  let : IsArtinianRing C := isArtinian_of_tower K inferInstance
  let κ := PrimeSpectrum C
  letI : Fintype κ := Fintype.ofFinite κ
  let e : C ≃ₐ[K] (κ → K) := Algebra.FormallyEtale.equivPiOfIsSepClosed K C
  have hc : Fintype.card κ = Fintype.card ι := by
    rw [← Module.finrank_fintype_fun_eq_card K]
    exact e.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_eq_card_basis bK)
  let w : κ ≃ ι := Fintype.equivOfCardEq hc
  let e' : C ≃ₐ[K] (ι → K) := e.trans (AlgEquiv.piCongrLeft K (fun _ : ι => K) w)
  let φ (i : ι) : A →ₐ[R] K := ((Pi.evalAlgHom R (fun _ : ι => K) i).comp
    (e'.toAlgHom.restrictScalars R)).comp Algebra.TensorProduct.includeRight
  refine ⟨φ, ?_⟩
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  have hLI := (bK.map e'.toLinearEquiv).linearIndependent
  convert hLI using 1
  funext j i
  change e' (1 ⊗ₜ[R] b j) i = e' ((Algebra.TensorProduct.basis K b) j) i
  exact congrArg (fun y => e' y i) (Algebra.TensorProduct.basis_apply b j).symm
  all_goals rfl

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponFormalBranchFamily

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {K R A ι : Type*} [Field K] [CommRing R] [CommRing A]
  [Algebra R A] [Algebra R K] [Fintype ι] [DecidableEq ι]

theorem exists_formal_branches_of_residue_matrix
    [Algebra.FormallySmooth R A] (r : ℕ)
    [Algebra R (MvPowerSeries (Fin r) K)]
    (hbase : ∀ t : R, MvPowerSeries.constantCoeff
      (algebraMap R (MvPowerSeries (Fin r) K) t) = algebraMap R K t)
    (b : Module.Basis ι R A) (φ : ι → A →ₐ[R] K)
    (hdet : Matrix.det (fun i j => φ i (b j)) ≠ 0) :
    ∃ f : ι → A →ₐ[R] MvPowerSeries (Fin r) K,
      (∀ i x, MvPowerSeries.constantCoeff (f i x) = φ i x) ∧
      ∀ x : A, algebraMap R (MvPowerSeries (Fin r) K) (Algebra.norm R x) =
        ∏ i, f i x := by
  let ρ : MvPowerSeries (Fin r) K →ₐ[R] K :=
    { __ := MvPowerSeries.constantCoeff, commutes' := hbase }
  have hρ : Function.Surjective ρ := fun k =>
    ⟨MvPowerSeries.C k, MvPowerSeries.constantCoeff_C k⟩
  let I := RingHom.ker ρ
  let : IsAdicComplete I (MvPowerSeries (Fin r) K) :=
    powerSeries_complete_constantCoeff_ker (Fin r) K
  let e := Ideal.quotientKerAlgEquivOfSurjective hρ
  have hlift (i : ι) : ∃ f : A →ₐ[R] MvPowerSeries (Fin r) K,
      ∀ x, ρ (f x) = φ i x := by
    obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
      (e.symm.toAlgHom.comp (φ i))
    refine ⟨f, fun x => ?_⟩
    calc
      ρ (f x) = e (Ideal.Quotient.mk I (f x)) :=
        (Ideal.quotientKerAlgEquivOfSurjective_mk hρ (f x)).symm
      _ = e (e.symm (φ i x)) := congrArg e (DFunLike.congr_fun hf x)
      _ = φ i x := e.apply_symm_apply _
  choose f hf using hlift
  refine ⟨f, hf, fun x => norm_eq_branch_product b f ?_ x⟩
  apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
  change IsUnit (ρ (Matrix.det (fun i j => f i (b j))))
  have hmatrix : ρ.toRingHom.mapMatrix (fun i j => f i (b j)) =
      (fun i j => φ i (b j) : Matrix ι ι K) := by
    ext i j
    exact hf i (b j)
  have he : ρ (Matrix.det (fun i j => f i (b j))) =
      Matrix.det (fun i j => φ i (b j)) :=
    (ρ.toRingHom.map_det _).trans (congrArg Matrix.det hmatrix)
  exact he.symm ▸ hdet.isUnit

theorem exists_formal_norm_branches [IsSepClosed K] [Algebra.FormallyEtale R A]
    (r : ℕ) [Algebra R (MvPowerSeries (Fin r) K)]
    (hbase : ∀ t : R, MvPowerSeries.constantCoeff
      (algebraMap R (MvPowerSeries (Fin r) K) t) = algebraMap R K t)
    (b : Module.Basis ι R A) :
    ∃ f : ι → A →ₐ[R] MvPowerSeries (Fin r) K,
      ∀ x : A, algebraMap R (MvPowerSeries (Fin r) K) (Algebra.norm R x) =
        ∏ i, f i x := by
  obtain ⟨φ, hφ⟩ := exists_etale_fiber_matrix (K := K) b
  obtain ⟨f, _, hf⟩ := exists_formal_branches_of_residue_matrix r hbase b φ hφ
  exact ⟨f, hf⟩

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponHomogeneousNormalization

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.HomogeneousNormalization
universe u v w
variable {R : Type u} [CommSemiring R] {K : Type v} [Field K]
  {σ : Type w} [Fintype σ]

theorem eval₂_scale (φ : R →+* K) (P : MvPolynomial σ R) (d : ℕ)
    (hP : ∀ m ∈ P.support, ∑ j, m j = d) (v : σ → K) (a : K) :
    eval₂ φ (fun j => a * v j) P = a ^ d * eval₂ φ v P := by
  classical
  simp only [eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hP m hm]
  ring

theorem eval₂_normalize (φ : R →+* K) (P : MvPolynomial σ R) (d : ℕ)
    (hP : ∀ m ∈ P.support, ∑ j, m j = d) (v : σ → K) (c : σ) :
    eval₂ φ (fun j => v j / v c) P = (v c)⁻¹ ^ d * eval₂ φ v P := by
  simpa only [div_eq_mul_inv, mul_comm] using eval₂_scale φ P d hP v (v c)⁻¹

end PhilipponMultiplicity.HomogeneousNormalization
end
end

section
-- Reused implementation: Solutions.PhilipponLinearShear

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.LinearNormalization
variable {K : Type*} [Field K] {n : ℕ}

def shearHom (a : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  aeval (Fin.cons (X 0) (fun i => X i.succ + C (a i) * X 0))

theorem shearHom_comp_neg (a : Fin n → K) :
    (shearHom a).comp (shearHom (-a)) = AlgHom.id _ _ := by
  ext i
  cases i using Fin.cases <;> simp [shearHom, Fin.cons_zero, Fin.cons_succ]

def shear (a : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  AlgEquiv.ofAlgHom (shearHom a) (shearHom (-a)) (shearHom_comp_neg a)
    (by simpa only [neg_neg] using shearHom_comp_neg (-a))

theorem shear_homogeneous (a : Fin n → K) {P : MvPolynomial (Fin (n + 1)) K}
    {d : ℕ} (hP : P.IsHomogeneous d) : (shear a P).IsHomogeneous d := by
  change (shearHom a P).IsHomogeneous d
  unfold shearHom
  simpa only [one_mul] using hP.aeval
    (Fin.cons (X 0) (fun i => X i.succ + C (a i) * X 0)) (n := 1) (fun i => by
      cases i using Fin.cases
      · exact isHomogeneous_X _ _
      · exact (isHomogeneous_X _ _).add
          (by simpa only [zero_add] using (isHomogeneous_C _ _).mul (isHomogeneous_X _ _)))

theorem eval_shear (a : Fin n → K) (P : MvPolynomial (Fin (n + 1)) K)
    (x : Fin (n + 1) → K) :
    eval x (shear a P) = eval (Fin.cons (x 0) (fun i => x i.succ + a i * x 0)) P := by
  change eval x (shearHom a P) = _
  unfold shearHom
  change eval x (eval₂ C (Fin.cons (X 0) (fun i => X i.succ + C (a i) * X 0)) P) = _
  rw [← eval_assoc]
  apply congrArg (fun v => eval v P)
  funext i
  cases i using Fin.cases <;> simp

theorem top_coefficient_eq_eval {P : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hP : P.IsHomogeneous d) :
    (finSuccEquiv K n P).coeff d = C (eval (Fin.cons 1 0) P) := by
  by_cases hzero : P = 0
  · simp [hzero]
  have hdeg : (finSuccEquiv K n P).natDegree < d + 1 := by
    rw [natDegree_finSuccEquiv]
    exact Nat.lt_succ_of_le ((degreeOf_le_totalDegree P 0).trans (le_of_eq (hP.totalDegree hzero)))
  have hlow : ∀ i ∈ Finset.range d, constantCoeff ((finSuccEquiv K n P).coeff i) = 0 := by
    intro i hi
    apply (hP.finSuccEquiv_coeff_isHomogeneous i (d - i) (by
      have := Finset.mem_range.mp hi; omega)).coeff_eq_zero
    simp only [map_zero]
    have := Finset.mem_range.mp hi
    omega
  have heval : eval (Fin.cons 1 0) P = constantCoeff ((finSuccEquiv K n P).coeff d) := by
    simp_rw [eval_eq_eval_mv_eval', Polynomial.eval_one_map,
      Polynomial.eval_eq_sum_range' hdeg, eval_zero, one_pow, mul_one,
      map_sum, Finset.sum_range_succ, Finset.sum_eq_zero hlow, zero_add]
  rw [heval]
  exact totalDegree_eq_zero_iff_eq_C.mp
    (Nat.eq_zero_of_le_zero (hP.finSuccEquiv_coeff_isHomogeneous d 0 (Nat.add_zero d)).totalDegree_le)

theorem exists_normalized_nonzero [Infinite K]
    {P : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hP : P.IsHomogeneous d) (hne : P ≠ 0) :
    ∃ a : Fin n → K, eval (Fin.cons 1 a) P ≠ 0 := by
  have hPX : P * X (0 : Fin (n + 1)) ≠ 0 := mul_ne_zero hne (X_ne_zero _)
  obtain ⟨x, hx⟩ : ∃ x : Fin (n + 1) → K, eval x (P * X 0) ≠ 0 := by
    by_contra! h
    exact hPX (MvPolynomial.funext (fun x => by rw [h x, map_zero]))
  simp only [map_mul, eval_X, mul_ne_zero_iff] at hx
  have hsupport : ∀ m ∈ P.support, ∑ j, m j = d := by
    intro m hm
    have h := hP (mem_support_iff.mp hm)
    change Finsupp.weight (fun _ => 1) m = d at h
    rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum] at h
    exact h
  have hscale := HomogeneousNormalization.eval₂_normalize (RingHom.id K) P d hsupport x 0
  change eval (fun j => x j / x 0) P = (x 0)⁻¹ ^ d * eval x P at hscale
  refine ⟨fun i => x i.succ / x 0, ?_⟩
  have heq : Fin.cons 1 (fun i : Fin n => x i.succ / x 0) = fun j => x j / x 0 := by
    funext i
    cases i using Fin.cases <;> simp [hx.2]
  rw [heq, hscale]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hx.2)) hx.1

theorem exists_shear_unit_leadingCoeff [Infinite K]
    {P : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hP : P.IsHomogeneous d) (hne : P ≠ 0) :
    ∃ a : Fin n → K, IsUnit (finSuccEquiv K n (shear a P)).leadingCoeff := by
  obtain ⟨a, ha⟩ := exists_normalized_nonzero hP hne
  refine ⟨a, ?_⟩
  have hs := shear_homogeneous a hP
  have heval : eval (Fin.cons 1 0) (shear a P) = eval (Fin.cons 1 a) P := by
    rw [eval_shear]
    simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, mul_one, zero_add]
  have hc : (finSuccEquiv K n (shear a P)).coeff d = C (eval (Fin.cons 1 a) P) :=
    (top_coefficient_eq_eval hs).trans (congrArg C heval)
  have hcn : (finSuccEquiv K n (shear a P)).coeff d ≠ 0 := by
    rw [hc]
    intro hz
    exact ha (by simpa using congrArg (coeff (0 : Fin n →₀ ℕ)) hz)
  have hsne : shear a P ≠ 0 := (shear a).injective.ne (by simpa using hne)
  have hdeg : (finSuccEquiv K n (shear a P)).natDegree = d :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (by rw [natDegree_finSuccEquiv]; exact (degreeOf_le_totalDegree _ _).trans (le_of_eq (hs.totalDegree hsne))) hcn
  rw [← Polynomial.coeff_natDegree, hdeg, hc]
  exact ha.isUnit.map C

end PhilipponMultiplicity.LinearNormalization

end
end

section
-- Reused implementation: Solutions.PhilipponHomogeneousChartDetection

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {K : Type*} [Field K]

theorem totalDegree_aeval_linear {σ τ : Type*} [Fintype σ]
    (U : σ → MvPolynomial τ K) (hU : ∀ i, (U i).totalDegree ≤ 1)
    (P : MvPolynomial σ K) : (aeval U P).totalDegree ≤ P.totalDegree := by
  classical
  change (eval₂ C U P).totalDegree ≤ _
  rw [eval₂_eq]
  apply totalDegree_finsetSum_le
  intro e he
  have hprod : (e.prod (fun i n => U i ^ n)).totalDegree ≤ e.degree := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    apply (totalDegree_finsetProd _ _).trans
    rw [Finsupp.degree_eq_sum]
    apply Finset.sum_le_sum
    intro i _
    exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (e i) (hU i))
  exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add, Finsupp.prod] using
    (hprod.trans (le_totalDegree he)))

def translatedChart {r : ℕ} (b : K) (a : Fin r → K) :
    MvPolynomial (Fin (r + 1)) K →ₐ[K] MvPolynomial (Fin r) K :=
  aeval (Fin.cons (C b) (fun i => X i + C (a i)))

theorem translatedChart_totalDegree {r : ℕ} (b : K) (a : Fin r → K)
    (P : MvPolynomial (Fin (r + 1)) K) :
    (translatedChart b a P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_aeval_linear
  intro i
  cases i using Fin.cases
  · simp
  · exact (totalDegree_add _ _).trans (by simp)

theorem eval_translatedChart {r : ℕ} (b : K) (a z : Fin r → K)
    (P : MvPolynomial (Fin (r + 1)) K) :
    eval z (translatedChart b a P) = eval (Fin.cons b (fun i => z i + a i)) P := by
  change eval z (eval₂ C (Fin.cons (C b) (fun i => X i + C (a i))) P) = _
  rw [← eval_assoc]
  apply congrArg (fun v => eval v P)
  funext i
  cases i using Fin.cases <;> simp

theorem translatedChart_eq_zero_iff [Infinite K] {r d : ℕ}
    (b : K) (hb : b ≠ 0) (a : Fin r → K)
    (P : MvPolynomial (Fin (r + 1)) K) (hP : P.IsHomogeneous d) :
    translatedChart b a P = 0 ↔ P = 0 := by
  constructor
  · intro hz
    by_contra hne
    obtain ⟨c, hc⟩ := LinearNormalization.exists_normalized_nonzero hP hne
    have hs : ∀ e ∈ P.support, ∑ j, e j = d := by
      intro e he
      have hh := hP (mem_support_iff.mp he)
      change Finsupp.weight (fun _ => 1) e = d at hh
      rwa [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum] at hh
    let v : Fin (r + 1) → K := Fin.cons 1 c
    have hscale := HomogeneousNormalization.eval₂_scale (RingHom.id K) P d hs v b
    change eval (fun j => b * v j) P = b ^ d * eval v P at hscale
    have hv : (fun j : Fin (r + 1) => b * v j) =
        Fin.cons b (fun i => b * c i) := by
      funext i
      cases i using Fin.cases <;> simp [v]
    rw [hv] at hscale
    have heval := congrArg (eval (fun i => b * c i - a i)) hz
    rw [eval_translatedChart, map_zero] at heval
    simp only [sub_add_cancel] at heval
    rw [hscale] at heval
    exact mul_ne_zero (pow_ne_zero _ hb) hc heval
  · intro hz
    rw [hz, map_zero]

end PhilipponMultiplicity.Chardin

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

end PhilipponMultiplicity.GenericChoice

end
end

section
-- Reused implementation: Solutions.PhilipponLocalizedFormalChart

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {K : Type*} [Field K]

def polynomialSeriesHom (r : ℕ) :
    MvPolynomial (Fin r) K →ₐ[K] MvPowerSeries (Fin r) K :=
  { __ := MvPolynomial.coeToMvPowerSeries.ringHom,
    commutes' := fun k => by
      simp [MvPolynomial.algebraMap_eq, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        MvPowerSeries.algebraMap_apply] }

theorem constantCoeff_translatedChart {r : ℕ} (b : K) (a : Fin r → K)
    (P : MvPolynomial (Fin (r + 1)) K) :
    MvPowerSeries.constantCoeff (polynomialSeriesHom r (translatedChart b a P)) =
      eval (Fin.cons b a) P := by
  change MvPowerSeries.constantCoeff
    (MvPolynomial.coeToMvPowerSeries.ringHom (translatedChart b a P)) = _
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
  change MvPolynomial.constantCoeff (translatedChart b a P) = _
  rw [← MvPolynomial.eval_zero, eval_translatedChart]
  simp

theorem exists_localized_formal_chart [Infinite K] (r : ℕ)
    (t : MvPolynomial (Fin (r + 1)) K) (ht : t ≠ 0) :
    ∃ b : K, b ≠ 0 ∧ ∃ a : Fin r → K,
      ∃ ψ : Localization.Away t →ₐ[K] MvPowerSeries (Fin r) K,
        ∀ P : MvPolynomial (Fin (r + 1)) K,
          ψ (algebraMap _ (Localization.Away t) P) =
            polynomialSeriesHom r (translatedChart b a P) := by
  obtain ⟨x, hx⟩ := GenericChoice.exists_eval_ne_zero (t * X (0 : Fin (r + 1)))
    (mul_ne_zero ht (X_ne_zero _))
  simp only [map_mul, eval_X, mul_ne_zero_iff] at hx
  let b := x 0
  let a : Fin r → K := fun i => x i.succ
  let φ := (polynomialSeriesHom r).comp (translatedChart b a)
  have hunit : IsUnit (φ t) := by
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    change IsUnit (MvPowerSeries.constantCoeff
      (polynomialSeriesHom r (translatedChart b a t)))
    rw [constantCoeff_translatedChart]
    have he : Fin.cons b a = x := by
      funext i
      cases i using Fin.cases <;> rfl
    rw [he]
    exact hx.1.isUnit
  let ψ : Localization.Away t →ₐ[K] MvPowerSeries (Fin r) K :=
    IsLocalization.Away.liftAlgHom t hunit
  refine ⟨b, hx.2, a, ψ, fun P => ?_⟩
  exact IsLocalization.Away.lift_eq t hunit P

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponLocalizedNormComparison

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped nonZeroDivisors TensorProduct
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {R A F L ι : Type*} [CommRing R] [IsDomain R]
  [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A]
  [Field F] [Field L] [Algebra R F] [Algebra R L] [Algebra A L] [Algebra F L]
  [IsScalarTower R A L] [IsScalarTower R F L]
  [IsFractionRing R F] [IsFractionRing A L] [Fintype ι]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem localized_norm_eq_polynomial (t : R) (ht : t ≠ 0)
    (b : Module.Basis ι (Localization.Away t) (Localization.Away t ⊗[R] A))
    (x : A) (P : R)
    (hP : algebraMap R F P = Algebra.norm F (algebraMap A L x)) :
    Algebra.norm (Localization.Away t)
        (algebraMap A (Localization.Away t ⊗[R] A) x) =
      algebraMap R (Localization.Away t) P := by
  let S := Localization.Away t
  let B := S ⊗[R] A
  have htF : algebraMap R F t ≠ 0 := by
    intro h
    exact ht ((IsFractionRing.injective R F) (h.trans (map_zero _).symm))
  let f : S →ₐ[R] F := IsLocalization.Away.liftAlgHom (f := Algebra.ofId R F) t htF.isUnit
  let : Algebra S F := f.toAlgebra
  let : IsScalarTower R S F := .of_algebraMap_eq' f.comp_algebraMap.symm
  let g : S →ₐ[R] L := (IsScalarTower.toAlgHom R F L).comp f
  let : Algebra S L := g.toAlgebra
  let : IsScalarTower R S L := .of_algebraMap_eq' g.comp_algebraMap.symm
  let : IsScalarTower S F L := .of_algebraMap_eq' rfl
  let h : B →ₐ[R] L := Algebra.TensorProduct.lift g
    (IsScalarTower.toAlgHom R A L) (fun _ _ => Commute.all _ _)
  let : Algebra B L := h.toAlgebra
  let : IsScalarTower R B L := .of_algebraMap_eq' h.comp_algebraMap.symm
  let : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A L a = h (1 ⊗ₜ[R] a)
    exact (Algebra.TensorProduct.lift_tmul g
      (IsScalarTower.toAlgHom R A L) (fun _ _ => Commute.all _ _) 1 a).trans
        (by simp) |>.symm
  let : IsScalarTower S B L := IsScalarTower.of_algebraMap_eq fun a => by
    change g a = h (a ⊗ₜ[R] (1 : A))
    exact (Algebra.TensorProduct.lift_tmul g
      (IsScalarTower.toAlgHom R A L) (fun _ _ => Commute.all _ _) a 1).trans
        (by simp) |>.symm
  let : IsFractionRing S F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (.powers t) S F
  let : IsFractionRing B L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Algebra.algebraMapSubmonoid A (.powers t)) B L
  let : IsDomain S := IsLocalization.Away.isDomain S ht
  let : IsDomain B := (IsFractionRing.injective B L).isDomain
  let : Module.Free S B := Module.Free.of_basis b
  let : Module.Finite S B := Module.Finite.of_basis b
  let : FaithfulSMul S B := (faithfulSMul_iff_algebraMap_injective S B).mpr (by
    apply Function.Injective.of_comp (f := algebraMap B L)
    simpa only [Function.comp_def, ← IsScalarTower.algebraMap_apply S B L,
      IsScalarTower.algebraMap_apply S F L] using
      (algebraMap F L).injective.comp (IsFractionRing.injective S F))
  apply IsFractionRing.injective S F
  have hn := Algebra.norm_localization (Rₘ := F) (S := B) (Sₘ := L)
    S S⁰ (algebraMap A B x)
  rw [← hn, ← IsScalarTower.algebraMap_apply A B L,
    ← IsScalarTower.algebraMap_apply R S F, hP]

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponHomogeneousScalarAction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.HomogeneousScalarAction
variable {K σ : Type*} [Field K] [Fintype σ]

def scaleHom (t : K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval (fun i => C t * X i)

def scaleEquiv (t : Kˣ) : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (scaleHom (t : K)) (scaleHom (↑t⁻¹ : K))
    (by
      ext i : 1
      simp only [AlgHom.comp_apply, AlgHom.id_apply, scaleHom, aeval_X, map_mul, aeval_C,
        algebraMap_eq]
      rw [← mul_assoc, ← map_mul]
      simp)
    (by
      ext i : 1
      simp only [AlgHom.comp_apply, AlgHom.id_apply, scaleHom, aeval_X, map_mul, aeval_C,
        algebraMap_eq]
      rw [← mul_assoc, ← map_mul]
      simp)

theorem scaleHom_homogeneous [Infinite K] (t : K)
    {P : MvPolynomial σ K} {d : ℕ} (hP : P.IsHomogeneous d) :
    scaleHom t P = C (t ^ d) * P := by
  have hsupport : ∀ m ∈ P.support, ∑ j, m j = d := by
    intro m hm
    have h := hP (mem_support_iff.mp hm)
    change Finsupp.weight (fun _ => 1) m = d at h
    rwa [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum] at h
  apply MvPolynomial.funext
  intro x
  change eval x (eval₂ C (fun i => C t * X i) P) = _
  rw [← eval_assoc]
  have hf : (eval x ∘ fun i => C t * X i) = fun i => t * x i := by
    funext i
    simp
  rw [hf]
  simpa only [map_mul, eval_C, eval₂_id] using
    HomogeneousNormalization.eval₂_scale (RingHom.id K) P d hsupport x t

theorem coeff_scaleHom [Infinite K] (t : K) (P : MvPolynomial σ K) (e : σ →₀ ℕ) :
    coeff e (scaleHom t P) = t ^ e.degree * coeff e P := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, coeff_sum, scaleHom_homogeneous t (isHomogeneous_monomial _ rfl),
    coeff_C_mul, coeff_monomial]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq']
  split_ifs with he
  · rfl
  · simp [notMem_support_iff.mp he]

theorem homogeneous_of_scale [Infinite K] (P : MvPolynomial σ K) (d : ℕ)
    (hscale : ∀ t : Kˣ, scaleHom (t : K) P = C ((t : K) ^ d) * P) :
    P.IsHomogeneous d := by
  intro e he
  have hpow (t : K) (ht : t ≠ 0) : t ^ e.degree = t ^ d := by
    have h := congrArg (coeff e) (hscale (Units.mk0 t ht))
    simp only [coeff_scaleHom, Units.val_mk0, coeff_C_mul] at h
    exact mul_right_cancel₀ he h
  have hpoly : (Polynomial.X : Polynomial K) ^ e.degree = Polynomial.X ^ d := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_univ.sdiff (Set.finite_singleton (0 : K))).mono
    intro t ht
    change Polynomial.eval t (Polynomial.X ^ e.degree) = Polynomial.eval t (Polynomial.X ^ d)
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using hpow t ht.2
  have hdeg := congrArg Polynomial.natDegree hpoly
  change Finsupp.weight (fun _ => 1) e = d
  simpa only [Polynomial.natDegree_X_pow, ← Finsupp.degree_eq_weight_one] using hdeg

theorem scaleHom_mapsIdeal [Infinite K] (t : K) (I : Ideal (MvPolynomial σ K))
    (hI : ∀ P ∈ I, ∀ d, homogeneousComponent d P ∈ I) :
    I.map (scaleHom t).toRingHom ≤ I := by
  rw [Ideal.map_le_iff_le_comap]
  intro P hP
  change scaleHom t P ∈ I
  rw [← sum_homogeneousComponent P, map_sum]
  apply Ideal.sum_mem
  intro d _
  rw [scaleHom_homogeneous t (homogeneousComponent_isHomogeneous d P)]
  exact Ideal.mul_mem_left I _ (hI P hP d)

theorem scaleEquiv_mapsIdeal [Infinite K] (t : Kˣ) (I : Ideal (MvPolynomial σ K))
    (hI : ∀ P ∈ I, ∀ d, homogeneousComponent d P ∈ I) :
    I.map (scaleEquiv t).toRingEquiv.toRingHom = I := by
  apply le_antisymm (scaleHom_mapsIdeal (t : K) I hI)
  have h := Ideal.map_mono (f := (scaleEquiv t).toRingEquiv.toRingHom)
    (scaleHom_mapsIdeal (↑t⁻¹ : K) I hI)
  rw [Ideal.map_map, show (scaleEquiv t).toRingEquiv.toRingHom.comp
    (scaleHom (↑t⁻¹ : K)).toRingHom = RingHom.id _ from
      RingHom.ext (fun P => (scaleEquiv t).apply_symm_apply P), Ideal.map_id] at h
  exact h

def quotientScale [Infinite K] (t : Kˣ) (I : Ideal (MvPolynomial σ K))
    (hI : ∀ P ∈ I, ∀ d, homogeneousComponent d P ∈ I) :
    (MvPolynomial σ K ⧸ I) ≃ₐ[K] (MvPolynomial σ K ⧸ I) :=
  Ideal.quotientEquivAlg I I (scaleEquiv t) (scaleEquiv_mapsIdeal t I hI).symm

theorem quotientScale_homogeneous [Infinite K] (t : Kˣ)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ P ∈ I, ∀ d, homogeneousComponent d P ∈ I)
    {P : MvPolynomial σ K} {d : ℕ} (hP : P.IsHomogeneous d) :
    quotientScale t I hI (Ideal.Quotient.mk I P) =
      (t : K) ^ d • Ideal.Quotient.mk I P := by
  rw [quotientScale, Ideal.quotientEquivAlg_mk]
  change Ideal.Quotient.mk I (scaleHom (t : K) P) = _
  rw [scaleHom_homogeneous (t : K) hP, ← smul_eq_C_mul]
  exact map_smul (Ideal.Quotient.mkₐ K I) _ _

end PhilipponMultiplicity.HomogeneousScalarAction

end
end

section
-- Reused implementation: Solutions.PhilipponFractionNormScaling

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Chardin

theorem exists_integral_norm_representative
    {R F L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field F] [Field L] [Algebra R F] [IsFractionRing R F]
    [Algebra R L] [Algebra F L] [IsScalarTower R F L]
    (x : L) (hx : IsIntegral R x) :
    ∃ P : R, algebraMap R F P = Algebra.norm F x :=
  IsIntegrallyClosed.algebraMap_eq_of_integral (Algebra.isIntegral_norm F hx)

theorem norm_representative_scaling
    {K R A F L : Type*} [Field K] [CommRing R] [IsDomain R]
    [CommRing A] [IsDomain A] [Field F] [Field L]
    [Algebra K R] [Algebra K A] [Algebra K F] [Algebra K L]
    [Algebra R A] [Algebra R F] [Algebra R L] [Algebra A L] [Algebra F L]
    [IsScalarTower K R F] [IsScalarTower K A L] [IsScalarTower K F L]
    [IsScalarTower R A L] [IsScalarTower R F L]
    [IsFractionRing R F] [IsFractionRing A L]
    (eR : R ≃ₐ[K] R) (eA : A ≃ₐ[K] A)
    (he : ∀ r, eA (algebraMap R A r) = algebraMap R A (eR r))
    (x : A) (c : K) (hx : eA x = c • x) (P : R)
    (hP : algebraMap R F P = Algebra.norm F (algebraMap A L x)) :
    eR P = c ^ Module.finrank F L • P := by
  let eF : F ≃ₐ[K] F := IsFractionRing.algEquivOfAlgEquiv eR
  let eL : L ≃ₐ[K] L := IsFractionRing.algEquivOfAlgEquiv eA
  have hbase (r : R) : algebraMap F L (eF (algebraMap R F r)) =
      eL (algebraMap F L (algebraMap R F r)) := by
    rw [show eF (algebraMap R F r) = algebraMap R F (eR r) from
      IsFractionRing.algEquivOfAlgEquiv_algebraMap eR r]
    rw [← IsScalarTower.algebraMap_apply R F L,
      ← IsScalarTower.algebraMap_apply R F L,
      IsScalarTower.algebraMap_apply R A L,
      IsScalarTower.algebraMap_apply R A L]
    rw [show eL (algebraMap A L (algebraMap R A r)) =
      algebraMap A L (eA (algebraMap R A r)) from
        IsFractionRing.algEquivOfAlgEquiv_algebraMap eA _, he]
  have hcompat : (algebraMap F L).comp eF.toRingEquiv.toRingHom =
      eL.toRingEquiv.toRingHom.comp (algebraMap F L) := by
    apply RingHom.ext
    intro z
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R z
    change algebraMap F L (eF (algebraMap R F a / algebraMap R F b)) =
      eL (algebraMap F L (algebraMap R F a / algebraMap R F b))
    simp only [map_div₀, hbase]
  have hxe : eL (algebraMap A L x) =
      algebraMap F L (algebraMap K F c) * algebraMap A L x := by
    rw [show eL (algebraMap A L x) = algebraMap A L (eA x) from
      IsFractionRing.algEquivOfAlgEquiv_algebraMap eA x, hx]
    rw [← IsScalarTower.algebraMap_apply K F L]
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K A L]
  have hn := congrArg eF (Algebra.norm_eq_of_equiv_equiv
    eF.toRingEquiv eL.toRingEquiv hcompat (algebraMap A L x))
  have hn' : eF (Algebra.norm F (algebraMap A L x)) =
      algebraMap K F c ^ Module.finrank F L * Algebra.norm F (algebraMap A L x) := by
    change eF (Algebra.norm F (algebraMap A L x)) =
      eF (eF.symm (Algebra.norm F (eL (algebraMap A L x)))) at hn
    rwa [AlgEquiv.apply_symm_apply, hxe, map_mul, Algebra.norm_algebraMap] at hn
  apply IsFractionRing.injective R F
  calc
    algebraMap R F (eR P) = eF (algebraMap R F P) :=
      (IsFractionRing.algEquivOfAlgEquiv_algebraMap eR P).symm
    _ = algebraMap K F c ^ Module.finrank F L * algebraMap R F P := by
      rw [hP, hn']
    _ = algebraMap R F (c ^ Module.finrank F L • P) := by
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K R F, map_pow]

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponHomogeneousNormPolynomial

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Chardin
open HomogeneousScalarAction

theorem exists_homogeneous_norm_representative
    {K σ A F L : Type*} [Field K] [Infinite K] [Fintype σ]
    [CommRing A] [IsDomain A] [Field F] [Field L]
    [Algebra K A] [Algebra K F] [Algebra K L]
    [Algebra (MvPolynomial σ K) A] [Algebra (MvPolynomial σ K) F]
    [Algebra (MvPolynomial σ K) L] [Algebra A L] [Algebra F L]
    [IsScalarTower K (MvPolynomial σ K) F] [IsScalarTower K A L]
    [IsScalarTower K F L] [IsScalarTower (MvPolynomial σ K) A L]
    [IsScalarTower (MvPolynomial σ K) F L]
    [IsFractionRing (MvPolynomial σ K) F] [IsFractionRing A L]
    (x : A) (m : ℕ) (hx : IsIntegral (MvPolynomial σ K) (algebraMap A L x))
    (hscale : ∀ t : Kˣ, ∃ e : A ≃ₐ[K] A,
      (∀ Q, e (algebraMap (MvPolynomial σ K) A Q) =
        algebraMap (MvPolynomial σ K) A (scaleEquiv t Q)) ∧ e x = (t : K) ^ m • x) :
    ∃ P : MvPolynomial σ K,
      P.IsHomogeneous (m * Module.finrank F L) ∧
        algebraMap (MvPolynomial σ K) F P = Algebra.norm F (algebraMap A L x) := by
  let : IsIntegrallyClosed (MvPolynomial σ K) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  obtain ⟨P, hP⟩ := exists_integral_norm_representative (F := F) _ hx
  refine ⟨P, homogeneous_of_scale P _ ?_, hP⟩
  intro t
  obtain ⟨e, he, hxscale⟩ := hscale t
  have h := norm_representative_scaling (scaleEquiv t) e he x ((t : K) ^ m) hxscale P hP
  change scaleHom (t : K) P = _ at h
  simpa only [pow_mul, smul_eq_C_mul] using h

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponQuotientNormPolynomial

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Chardin
open HomogeneousScalarAction
variable {K σ τ A F L : Type*} [Field K] [Infinite K] [Fintype σ] [Fintype τ]
  [CommRing A] [IsDomain A] [Field F] [Field L]
  [Algebra K A] [Algebra K F] [Algebra K L]
  [Algebra (MvPolynomial τ K) A] [Algebra (MvPolynomial τ K) F]
  [Algebra (MvPolynomial τ K) L] [Algebra A L] [Algebra F L]
  [IsScalarTower K (MvPolynomial τ K) A] [IsScalarTower K (MvPolynomial τ K) F]
  [IsScalarTower K A L] [IsScalarTower K F L]
  [IsScalarTower (MvPolynomial τ K) A L] [IsScalarTower (MvPolynomial τ K) F L]
  [IsFractionRing (MvPolynomial τ K) F] [IsFractionRing A L]

theorem exists_quotient_norm_polynomial
    (q : MvPolynomial σ K →ₐ[K] A) (hq : Function.Surjective q)
    (hhom : ∀ P ∈ RingHom.ker q.toRingHom, ∀ d,
      homogeneousComponent d P ∈ RingHom.ker q.toRingHom)
    [Algebra.IsIntegral (MvPolynomial τ K) A]
    (hlinear : ∀ i, ∃ Q : MvPolynomial σ K, Q.IsHomogeneous 1 ∧
      algebraMap (MvPolynomial τ K) A (X i) = q Q)
    (P : MvPolynomial σ K) (m : ℕ) (hP : P.IsHomogeneous m) :
    ∃ Q : MvPolynomial τ K,
      Q.IsHomogeneous (m * Module.finrank F L) ∧
      algebraMap (MvPolynomial τ K) F Q = Algebra.norm F (algebraMap A L (q P)) := by
  let R := MvPolynomial τ K
  have hx : IsIntegral R (algebraMap A L (q P)) :=
    (Algebra.IsIntegral.isIntegral (R := R) (q P)).map (IsScalarTower.toAlgHom R A L)
  apply exists_homogeneous_norm_representative (F := F) (L := L) (q P) m hx
  intro t
  let e := Ideal.quotientKerAlgEquivOfSurjective hq
  let s := quotientScale t (RingHom.ker q.toRingHom) hhom
  let v : A ≃ₐ[K] A := (e.symm.trans s).trans e
  have hv (Q : MvPolynomial σ K) (d : ℕ) (hQ : Q.IsHomogeneous d) :
      v (q Q) = (t : K) ^ d • q Q := by
    change e (s (e.symm (q Q))) = _
    rw [show e.symm (q Q) = Ideal.Quotient.mk (RingHom.ker q.toRingHom) Q from
      Ideal.quotientKerAlgEquivOfSurjective_symm_apply hq Q]
    rw [show s (Ideal.Quotient.mk (RingHom.ker q.toRingHom) Q) =
      (t : K) ^ d • Ideal.Quotient.mk (RingHom.ker q.toRingHom) Q from
        quotientScale_homogeneous t _ hhom hQ, map_smul]
    rw [show e (Ideal.Quotient.mk (RingHom.ker q.toRingHom) Q) = q Q from
      Ideal.quotientKerAlgEquivOfSurjective_mk hq Q]
  refine ⟨v, ?_, hv P m hP⟩
  have hc : v.toAlgHom.comp (IsScalarTower.toAlgHom K R A) =
      (IsScalarTower.toAlgHom K R A).comp (scaleEquiv t).toAlgHom := by
    ext i : 1
    change v (algebraMap R A (X i)) = algebraMap R A (scaleHom (t : K) (X i))
    obtain ⟨Q, hQ, hi⟩ := hlinear i
    rw [hi, hv Q 1 hQ, scaleHom_homogeneous (t : K) (isHomogeneous_X K i)]
    change (t : K) ^ 1 • q Q =
      (IsScalarTower.toAlgHom K R A) (C ((t : K) ^ 1) * X i)
    rw [← smul_eq_C_mul, map_smul]
    exact congrArg ((t : K) ^ 1 • ·) hi.symm
  intro Q
  exact DFunLike.congr_fun hc Q

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponSymmetricJets

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

abbrev SymmetricJetIndex (b T : ℕ) := Σ n : Fin (T + 1), Sym (Fin b) n.val

theorem symmetricJetIndex_card (b T : ℕ) :
    Fintype.card (SymmetricJetIndex b T) = Nat.choose (T + b) b := by
  rw [Fintype.card_sigma]
  simp only [Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range, Nat.sum_range_multichoose]

namespace OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

end OperatorSupport

namespace JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

end JetSupport

namespace OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

end OperatorSupport
end PhilipponMultiplicity

end
end

section
-- Reused implementation: Solutions.PhilipponChardinJetBound

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {K : Type*} [Field K]

def jetExponent {r m : ℕ} (j : SymmetricJetIndex r m) : Fin r →₀ ℕ :=
  (Sym.equivNatSum (Fin r) j.1.val j.2).val

theorem exists_jetExponent {r m : ℕ} (a : Fin r →₀ ℕ) (ha : a.degree ≤ m) :
    ∃ j : SymmetricJetIndex r m, jetExponent j = a := by
  let n : Fin (m + 1) := ⟨a.degree, by omega⟩
  exact ⟨⟨n, (Sym.equivNatSum (Fin r) n.val).symm ⟨a, rfl⟩⟩,
    congrArg Subtype.val ((Sym.equivNatSum (Fin r) n.val).apply_symm_apply ⟨a, rfl⟩)⟩

theorem polynomial_product_eq_zero {r m δ : ℕ} (hδ : 0 < δ)
    (f : Fin δ → MvPowerSeries (Fin r) K)
    (hf : ∀ i a, a.degree ≤ m → MvPowerSeries.coeff a (f i) = 0)
    (P : MvPolynomial (Fin r) K) (hP : P.totalDegree ≤ δ * m)
    (hprod : (P : MvPowerSeries (Fin r) K) = ∏ i, f i) : P = 0 := by
  have hi (i : Fin δ) : ((m + 1 : ℕ) : ℕ∞) ≤ (f i).order :=
    MvPowerSeries.nat_le_order fun a ha => hf i a (by omega)
  have hs : ((δ * (m + 1) : ℕ) : ℕ∞) ≤ (∏ i, f i).order := by
    calc
      _ = ∑ i : Fin δ, ((m + 1 : ℕ) : ℕ∞) := by simp [Nat.cast_mul, mul_add]
      _ ≤ ∑ i : Fin δ, (f i).order := Finset.sum_le_sum fun i _ => hi i
      _ ≤ _ := MvPowerSeries.le_order_prod f Finset.univ
  apply MvPolynomial.ext
  intro a
  simp only [MvPolynomial.coeff_zero]
  by_cases ha : a ∈ P.support
  · have had : a.degree ≤ δ * m := (MvPolynomial.le_totalDegree ha).trans hP
    have halt : (a.degree : ℕ∞) < ((δ * (m + 1) : ℕ) : ℕ∞) := by
      exact_mod_cast (show a.degree < δ * (m + 1) by nlinarith)
    have hz := MvPowerSeries.coeff_of_lt_order (halt.trans_le hs)
    rw [← hprod, MvPolynomial.coeff_coe] at hz
    exact hz
  · exact MvPolynomial.notMem_support_iff.mp ha

variable {V : Type*} [AddCommGroup V] [Module K V]

def branchJetMap {r m δ : ℕ} (f : Fin δ → V →ₗ[K] MvPowerSeries (Fin r) K) :
    V →ₗ[K] ((Fin δ × SymmetricJetIndex r m) → K) :=
  LinearMap.pi fun j => (MvPowerSeries.coeff (jetExponent j.2)).comp (f j.1)

theorem branchJetMap_injective_of_polynomial_detection {r m δ : ℕ} (hδ : 0 < δ)
    (f : Fin δ → V →ₗ[K] MvPowerSeries (Fin r) K)
    (hpoly : ∀ x : V, ∃ P : MvPolynomial (Fin r) K,
      P.totalDegree ≤ δ * m ∧ (P : MvPowerSeries (Fin r) K) = ∏ i, f i x ∧
        (P = 0 → x = 0)) :
    Function.Injective (branchJetMap (m := m) f) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨P, hP, hprod, hdetect⟩ := hpoly x
  apply hdetect
  apply polynomial_product_eq_zero hδ (fun i => f i x) _ P hP hprod
  intro i a ha
  obtain ⟨j, rfl⟩ := exists_jetExponent a ha
  exact congrFun (LinearMap.mem_ker.mp hx) (i, j)

theorem finrank_le_of_polynomial_detection {r m δ : ℕ} (hδ : 0 < δ)
    (f : Fin δ → V →ₗ[K] MvPowerSeries (Fin r) K)
    (hpoly : ∀ x : V, ∃ P : MvPolynomial (Fin r) K,
      P.totalDegree ≤ δ * m ∧ (P : MvPowerSeries (Fin r) K) = ∏ i, f i x ∧
        (P = 0 → x = 0)) :
    Module.finrank K V ≤ δ * Nat.choose (m + r) r := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (branchJetMap_injective_of_polynomial_detection hδ f hpoly)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
    symmetricJetIndex_card] using h

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponSeparableHilbertUpper

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators nonZeroDivisors TensorProduct
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {K σ A F L : Type*} [Field K] [IsAlgClosed K] [Fintype σ]
  [CommRing A] [IsDomain A] [Field F] [Field L]
  [Algebra K A] [Algebra K F] [Algebra K L]
  (r : ℕ)
  [Algebra (MvPolynomial (Fin (r + 1)) K) A]
  [Algebra (MvPolynomial (Fin (r + 1)) K) F]
  [Algebra (MvPolynomial (Fin (r + 1)) K) L]
  [Algebra A L] [Algebra F L]
  [IsScalarTower K (MvPolynomial (Fin (r + 1)) K) A]
  [IsScalarTower K (MvPolynomial (Fin (r + 1)) K) F]
  [IsScalarTower K A L] [IsScalarTower K F L]
  [IsScalarTower (MvPolynomial (Fin (r + 1)) K) A L]
  [IsScalarTower (MvPolynomial (Fin (r + 1)) K) F L]
  [IsFractionRing (MvPolynomial (Fin (r + 1)) K) F] [IsFractionRing A L]
  [FaithfulSMul (MvPolynomial (Fin (r + 1)) K) A]
  [Module.Finite (MvPolynomial (Fin (r + 1)) K) A]
  [Algebra.IsSeparable F L]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem homogeneous_image_finrank_upper_of_separable_normalization
    (q : MvPolynomial σ K →ₐ[K] A) (hq : Function.Surjective q)
    (hhom : ∀ P ∈ RingHom.ker q.toRingHom, ∀ d,
      homogeneousComponent d P ∈ RingHom.ker q.toRingHom)
    (hlinear : ∀ i, ∃ Q : MvPolynomial σ K, Q.IsHomogeneous 1 ∧
      algebraMap (MvPolynomial (Fin (r + 1)) K) A (X i) = q Q)
    (m : ℕ) :
    Module.finrank K ((homogeneousSubmodule σ K m).map q.toLinearMap) ≤
      Module.finrank F L * Nat.choose (m + r) r := by
  classical
  let R := MvPolynomial (Fin (r + 1)) K
  let : Module.Finite F L := Module.Finite.of_isLocalization R A R⁰
  obtain ⟨t, ht, ⟨b⟩, het⟩ :=
    exists_finite_free_etale_base_open (R := R) (A := A) (F := F) (L := L)
  obtain ⟨c, hc, a, ψ, hψ⟩ := exists_localized_formal_chart r t ht
  let S := Localization.Away t
  let B := S ⊗[R] A
  let PS := MvPowerSeries (Fin r) K
  let : Algebra S PS := ψ.toAlgebra
  let : IsScalarTower K S PS := .of_algebraMap_eq' ψ.comp_algebraMap.symm
  let ρ : S →+* K := MvPowerSeries.constantCoeff.comp ψ.toRingHom
  let : Algebra S K := ρ.toAlgebra
  let : Algebra.FormallyEtale S B := het
  obtain ⟨f, hf⟩ := exists_formal_norm_branches (K := K) r (fun _ => rfl) b
  let j : A →ₐ[K] B := (Algebra.TensorProduct.includeRight : A →ₐ[R] B).restrictScalars K
  let V := (homogeneousSubmodule σ K m).map q.toLinearMap
  let φ : Fin (Module.finrank F L) → V →ₗ[K] PS := fun i =>
    ((f i).restrictScalars K).toLinearMap.comp (j.toLinearMap.comp V.subtype)
  apply finrank_le_of_polynomial_detection (r := r) (m := m)
    (Module.finrank_pos (R := F) (M := L)) φ
  intro x
  obtain ⟨P, hP, he⟩ := x.property
  obtain ⟨Q, hQ, hnorm⟩ := exists_quotient_norm_polynomial (F := F) (L := L)
    q hq hhom hlinear P m hP
  refine ⟨translatedChart c a Q, ?_, ?_, ?_⟩
  · exact (translatedChart_totalDegree c a Q).trans
      (hQ.totalDegree_le.trans_eq (Nat.mul_comm m (Module.finrank F L)))
  · have hlocal := localized_norm_eq_polynomial (F := F) (L := L) t ht b (q P) Q hnorm
    have hp := hf (j (q P))
    change ψ (Algebra.norm S (algebraMap A B (q P))) = _ at hp
    rw [hlocal, hψ] at hp
    change (translatedChart c a Q : PS) = ∏ i, f i (j (x : A))
    have he' : q P = (x : A) := he
    rw [← he']
    exact hp
  · intro hz
    have hzero : Q = 0 := (translatedChart_eq_zero_iff c hc a Q hQ).mp hz
    have hnzero : Algebra.norm F (algebraMap A L (q P)) = 0 := by
      rw [← hnorm, hzero, map_zero]
    have hxzero : q P = 0 := (IsFractionRing.injective A L)
      ((Algebra.norm_eq_zero_iff.mp hnzero).trans (map_zero _).symm)
    apply Subtype.ext
    exact he.symm.trans hxzero

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponHomogeneousFractionBasis

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators nonZeroDivisors
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {K σ R A : Type*} [Field K] [Fintype σ] [CommRing R] [IsDomain R]
  [Algebra K R] [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower K R A]

theorem quotient_monomials_span (q : MvPolynomial σ K →ₐ[K] A)
    (hq : Function.Surjective q) :
    Submodule.span R (Set.range (fun e : σ →₀ ℕ =>
      q (monomial e 1))) = ⊤ := by
  have hK : Submodule.span K (Set.range (fun e : σ →₀ ℕ =>
      q (monomial e 1))) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨P, rfl⟩ := hq x
    rw [P.as_sum, map_sum]
    apply Submodule.sum_mem
    intro e _
    have hs := (Submodule.span K (Set.range (fun e : σ →₀ ℕ =>
      q (monomial e 1)))).smul_mem (coeff e P)
        (Submodule.subset_span (Set.mem_range_self e))
    simpa only [← map_smul q,
      smul_monomial, smul_eq_mul, mul_one] using hs
  apply top_unique
  intro x hx
  exact Submodule.span_subset_span K R _ (by rw [hK]; exact hx)

theorem exists_monomial_fraction_basis [IsDomain A]
    [FaithfulSMul R A] [Module.Finite R A]
    {F L : Type*} [Field F] [Field L] [Algebra R F] [IsFractionRing R F]
    [Algebra R L] [Algebra A L] [Algebra F L]
    [IsScalarTower R A L] [IsScalarTower R F L] [IsFractionRing A L]
    (q : MvPolynomial σ K →ₐ[K] A) (hq : Function.Surjective q) :
    ∃ e : Fin (Module.finrank F L) →
        (σ →₀ ℕ),
      LinearIndependent F (fun i =>
        algebraMap A L
          (q (monomial (e i) 1))) := by
  classical
  let : Module.Finite F L := .of_isLocalization R A R⁰
  let v : (σ →₀ ℕ) → A := fun e => q (monomial e 1)
  have hsR : Submodule.span R (Set.range v) = ⊤ := quotient_monomials_span (R := R) q hq
  have hsF : Submodule.span F (Set.range (algebraMap A L ∘ v)) = ⊤ := by
    simpa only [← Set.range_comp] using
      span_eq_top_localization_localization F R⁰ L hsR
  obtain ⟨n, b, hb⟩ : ∃ n, ∃ b : Module.Basis (Fin n) F L,
      Set.range b ⊆ Set.range (algebraMap A L ∘ v) := by
    let b := Module.Basis.ofSpan (le_of_eq hsF.symm)
    letI := FiniteDimensional.fintypeBasisIndex b
    refine ⟨_, b.reindex (Fintype.equivFin _), ?_⟩
    rw [Module.Basis.range_reindex]
    exact Module.Basis.ofSpan_subset _
  have hn : n = Module.finrank F L := by
    simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis b).symm
  subst n
  choose e he using fun i => hb (Set.mem_range_self i)
  refine ⟨e, ?_⟩
  have hv : (fun i => algebraMap A L (v (e i))) = b := by
    funext i
    exact he i
  change LinearIndependent F (fun i => algebraMap A L (v (e i)))
  rw [hv]
  exact b.linearIndependent

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponUniformHomogeneousBasis

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators nonZeroDivisors
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Chardin
variable {K σ τ A F L : Type*} [Field K] [Fintype σ] [Fintype τ]
  [CommRing A] [IsDomain A] [Field F] [Field L] [Algebra K A]
  [Algebra (MvPolynomial τ K) A] [Algebra (MvPolynomial τ K) F]
  [Algebra (MvPolynomial τ K) L] [Algebra A L] [Algebra F L]
  [IsScalarTower K (MvPolynomial τ K) A]
  [IsScalarTower (MvPolynomial τ K) A L] [IsScalarTower (MvPolynomial τ K) F L]
  [IsFractionRing (MvPolynomial τ K) F] [IsFractionRing A L]
  [FaithfulSMul (MvPolynomial τ K) A] [Module.Finite (MvPolynomial τ K) A]

theorem exists_uniform_homogeneous_fraction_basis
    (q : MvPolynomial σ K →ₐ[K] A) (hq : Function.Surjective q)
    (j : τ) (H : MvPolynomial σ K) (hH : H.IsHomogeneous 1)
    (hlinear : algebraMap (MvPolynomial τ K) A (X j) = q H) :
    ∃ E : ℕ, ∃ P : Fin (Module.finrank F L) → MvPolynomial σ K,
      (∀ i, (P i).IsHomogeneous E) ∧
      LinearIndependent F (fun i => algebraMap A L (q (P i))) := by
  classical
  obtain ⟨e, he⟩ := exists_monomial_fraction_basis (R := MvPolynomial τ K)
    (F := F) (L := L) q hq
  let E := Finset.univ.sup (fun i => (e i).degree)
  have hdeg (i) : (e i).degree ≤ E := Finset.le_sup (f := fun i => (e i).degree)
    (Finset.mem_univ i)
  let P (i : Fin (Module.finrank F L)) := monomial (e i) 1 * H ^ (E - (e i).degree)
  have hP (i) : (P i).IsHomogeneous E := by
    have h := (isHomogeneous_monomial (1 : K) (rfl : (e i).degree = (e i).degree)).mul
      (hH.pow (E - (e i).degree))
    simpa only [one_mul, Nat.add_sub_of_le (hdeg i)] using h
  have hX : algebraMap (MvPolynomial τ K) F (X j) ≠ 0 := by
    intro h
    apply (X_ne_zero j : (X j : MvPolynomial τ K) ≠ 0)
    exact (IsFractionRing.injective (MvPolynomial τ K) F)
      (h.trans (map_zero _).symm)
  let u (i : Fin (Module.finrank F L)) : Fˣ :=
    Units.mk0 (algebraMap (MvPolynomial τ K) F (X j) ^ (E - (e i).degree))
      (pow_ne_zero _ hX)
  have hmul (i) : algebraMap A L (q (P i)) =
      u i • algebraMap A L (q (monomial (e i) 1)) := by
    simp only [P, map_mul, map_pow]
    rw [← hlinear, ← IsScalarTower.algebraMap_apply (MvPolynomial τ K) A L,
      IsScalarTower.algebraMap_apply (MvPolynomial τ K) F L]
    rw [Units.smul_def, Algebra.smul_def]
    change algebraMap A L (q (monomial (e i) 1)) *
        algebraMap F L (algebraMap (MvPolynomial τ K) F (X j)) ^ (E - (e i).degree) =
      algebraMap F L (algebraMap (MvPolynomial τ K) F (X j) ^ (E - (e i).degree)) *
        algebraMap A L (q (monomial (e i) 1))
    rw [map_pow, mul_comm]
  refine ⟨E, P, hP, ?_⟩
  have hv : (fun i => algebraMap A L (q (P i))) =
      u • (fun i => algebraMap A L (q (monomial (e i) 1))) := by
    funext i
    exact hmul i
  rw [hv]
  exact he.units_smul u

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponHomogeneousModuleInjection

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators nonZeroDivisors
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Chardin

theorem homogeneousSubmodule_finrank (K : Type*) [Field K] (r m : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin (r + 1)) K m) =
      (m + r).choose r := by
  classical
  rw [homogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K) _).finrank_eq]
  let e : {a : Fin (r + 1) →₀ ℕ // a.degree = m} ≃ Sym (Fin (r + 1)) m :=
    (Sym.equivNatSum (Fin (r + 1)) m).symm
  change Module.finrank K ({a : Fin (r + 1) →₀ ℕ // a.degree = m} →₀ K) = _
  rw [(Finsupp.domLCongr e : (_ →₀ K) ≃ₗ[K] (Sym (Fin (r + 1)) m →₀ K)).finrank_eq,
    Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card,
    Sym.natCard_sym_eq_multichoose, Nat.card_fin, Nat.multichoose_eq]
  have heq : r + 1 + m - 1 = m + r := by omega
  rw [heq, ← Nat.choose_symm (show m ≤ m + r by omega)]
  simp

variable {K σ τ A F L : Type*} [Field K] [Fintype σ] [Fintype τ]
  [CommRing A] [IsDomain A] [Field F] [Field L] [Algebra K A]
  [Algebra (MvPolynomial τ K) A] [Algebra (MvPolynomial τ K) F]
  [Algebra (MvPolynomial τ K) L] [Algebra A L] [Algebra F L]
  [IsScalarTower K (MvPolynomial τ K) A]
  [IsScalarTower (MvPolynomial τ K) A L] [IsScalarTower (MvPolynomial τ K) F L]
  [IsFractionRing (MvPolynomial τ K) F] [IsFractionRing A L]

theorem homogeneous_image_finrank_lower
    (q : MvPolynomial σ K →ₐ[K] A)
    (U : τ → MvPolynomial σ K) (hU : ∀ j, (U j).IsHomogeneous 1)
    (hlinear : ∀ j, algebraMap (MvPolynomial τ K) A (X j) = q (U j))
    {δ E : ℕ} (P : Fin δ → MvPolynomial σ K)
    (hP : ∀ i, (P i).IsHomogeneous E)
    (hLI : LinearIndependent F (fun i => algebraMap A L (q (P i)))) (m : ℕ) :
    δ * Module.finrank K (homogeneousSubmodule τ K m) ≤
      Module.finrank K ((homogeneousSubmodule σ K (m + E)).map q.toLinearMap) := by
  classical
  let B := homogeneousSubmodule τ K m
  let V := (homogeneousSubmodule σ K (m + E)).map q.toLinearMap
  letI : Module.Finite K B := Module.Finite.of_fg (homogeneousSubmodule_fg τ K m)
  letI : Module.Finite K V := Module.Finite.of_fg
    ((homogeneousSubmodule_fg σ K (m + E)).map q.toLinearMap)
  let g : MvPolynomial τ K →ₐ[K] A := IsScalarTower.toAlgHom K (MvPolynomial τ K) A
  have hg : g = q.comp (aeval U) := by
    ext j : 1
    change algebraMap (MvPolynomial τ K) A (X j) = q (aeval U (X j))
    simpa only [aeval_X] using hlinear j
  let f : (Fin δ → B) →ₗ[K] A :=
    ∑ i : Fin δ, ((LinearMap.mulRight K (q (P i))).comp
      (g.toLinearMap.comp B.subtype)).comp (LinearMap.proj i)
  have hf (c : Fin δ → B) : f c = ∑ i, g (c i) * q (P i) := by
    simp [f]
  have hfmem (c : Fin δ → B) : f c ∈ V := by
    refine ⟨∑ i, aeval U (c i : MvPolynomial τ K) * P i, ?_, ?_⟩
    · apply Submodule.sum_mem
      intro i _
      have hi : (aeval U (c i : MvPolynomial τ K)).IsHomogeneous m := by
        simpa only [one_mul] using (c i).property.aeval U (n := 1) hU
      exact hi.mul (hP i)
    · simp only [map_sum, map_mul, hf, hg, AlgHom.comp_apply, AlgHom.toLinearMap_apply]
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro c hc
    have hs := congrArg (algebraMap A L) (LinearMap.mem_ker.mp hc)
    rw [hf, map_sum, map_zero] at hs
    have hs' : ∑ i, algebraMap (MvPolynomial τ K) F (c i) •
        algebraMap A L (q (P i)) = 0 := by
      simpa only [map_mul, g, IsScalarTower.toAlgHom_apply, Algebra.smul_def,
        ← IsScalarTower.algebraMap_apply (MvPolynomial τ K) A L,
        ← IsScalarTower.algebraMap_apply (MvPolynomial τ K) F L] using hs
    have hz := Fintype.linearIndependent_iff.mp hLI _ hs'
    funext i
    apply Subtype.ext
    exact (IsFractionRing.injective (MvPolynomial τ K) F)
      ((hz i).trans (map_zero _).symm)
  let fV : (Fin δ → B) →ₗ[K] V := f.codRestrict V hfmem
  have hV : Function.Injective fV := fun c d h => hfi (congrArg Subtype.val h)
  have hr := LinearMap.finrank_le_finrank_of_injective hV
  simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] using hr

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponHilbertLeadingComparison

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert

theorem polynomial_div_pow_tendsto (P : Polynomial ℚ) (r : ℕ)
    (hdeg : P.natDegree ≤ r) :
    Tendsto (fun n : ℕ => P.eval (n : ℚ) / (n : ℚ) ^ r) atTop (𝓝 (P.coeff r)) := by
  by_cases hP : P = 0
  · simp [hP]
  by_cases heq : P.natDegree = r
  · have hd : P.degree = (Polynomial.X ^ r : Polynomial ℚ).degree := by
      rw [Polynomial.degree_eq_natDegree hP, heq, Polynomial.degree_X_pow]
    have ht := (P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
      (Polynomial.X ^ r) hd).comp (tendsto_natCast_atTop_atTop (R := ℚ))
    simpa [Function.comp_def, Polynomial.leadingCoeff, heq] using ht
  · have hlt : P.natDegree < r := lt_of_le_of_ne hdeg heq
    have hd : P.degree < (Polynomial.X ^ r : Polynomial ℚ).degree := by
      rw [Polynomial.degree_eq_natDegree hP, Polynomial.degree_X_pow]
      exact_mod_cast hlt
    have ht := (P.div_tendsto_atTop_zero_of_degree_lt
      (Polynomial.X ^ r) hd).comp (tendsto_natCast_atTop_atTop (R := ℚ))
    simpa [Function.comp_def, Polynomial.coeff_eq_zero_of_natDegree_lt hlt] using ht

theorem top_coeff_le_of_eventually_eval_le (P Q : Polynomial ℚ) (r : ℕ)
    (hP : P.natDegree ≤ r) (hQ : Q.natDegree ≤ r)
    (hle : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.coeff r ≤ Q.coeff r := by
  apply le_of_tendsto_of_tendsto (polynomial_div_pow_tendsto P r hP)
    (polynomial_div_pow_tendsto Q r hQ)
  filter_upwards [hle] with n hn
  exact div_le_div_of_nonneg_right hn (by positivity)

theorem rank_le_degree_of_shifted_hilbert_lower
    {K : Type*} [Field K] (N : ℕ)
    (I : Ideal (projectiveSpace K N).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (projectiveSpace K N) I)
    (δ E : ℕ)
    (hlower : ∀ m : ℕ,
      δ * (m + SectionThree.idealDimension (projectiveSpace K N) I).choose
        (SectionThree.idealDimension (projectiveSpace K N) I) ≤
      hilbertFunction K 1 (fun _ => N) I (fun _ => m + E)) :
    (δ : ℚ) ≤ SectionThree.idealDegreeValue (projectiveSpace K N) I (fun _ => 1) := by
  let F := hilbertPolynomial K 1 (fun _ => N) I
  let r := F.totalDegree
  let B : MvPolynomial (Fin 1) ℚ := (δ : ℚ) • BinomialPolynomial.block (0 : Fin 1) r 0
  let P := rayPolynomial B (fun _ => 1) (fun _ => 0)
  let Q := rayPolynomial F (fun _ => 1) (fun _ => (E : ℚ))
  have hP : P.natDegree ≤ r := (rayPolynomial_natDegree_le B _ _ (by simp)).trans
    (by exact (totalDegree_smul_le (δ : ℚ) _).trans_eq (BinomialPolynomial.block_degree (0 : Fin 1) r 0))
  have hQ : Q.natDegree ≤ r := rayPolynomial_natDegree_le F _ _ (by simp)
  obtain ⟨D, hD⟩ := hilbertPolynomial_spec K 1 (fun _ => N) I
    (multigraded_hilbert_polynomial_exists K (projectiveSpace K N) I hI)
  have hevent : ∀ᶠ m : ℕ in atTop, P.eval (m : ℚ) ≤ Q.eval (m : ℚ) := by
    filter_upwards [eventually_ge_atTop (D 0)] with m hm
    have hd : ∀ i : Fin 1, D i ≤ m + E := by
      intro i
      rw [Subsingleton.elim i (0 : Fin 1)]
      exact hm.trans (Nat.le_add_right m E)
    have hs := hD (fun _ => m + E) hd
    have hp : P.eval (m : ℚ) = (δ : ℚ) * ((m + r).choose r : ℚ) := by
      simp only [P, B, rayPolynomial_eval, one_mul, add_zero, smul_eq_C_mul,
        map_mul, eval_C]
      rw [BinomialPolynomial.block_eval 0 r 0 (fun _ => m) (Nat.zero_le m)]
      simp
    have hq : Q.eval (m : ℚ) =
        (hilbertFunction K 1 (fun _ => N) I (fun _ => m + E) : ℚ) := by
      simpa only [Q, F, rayPolynomial_eval, one_mul, Nat.cast_add] using hs
    rw [hp, hq]
    exact_mod_cast hlower m
  have hcoeff := top_coeff_le_of_eventually_eval_le P Q r hP hQ hevent
  have hpc : P.coeff r = (δ : ℚ) * (r.factorial : ℚ)⁻¹ := by
    change (rayPolynomial B (fun _ => 1) (fun _ => 0)).coeff r = _
    have hscale : rayPolynomial B (fun _ => 1) (fun _ => 0) =
        (δ : ℚ) • rayPolynomial (BinomialPolynomial.block (0 : Fin 1) r 0)
          (fun _ => 1) (fun _ => 0) := by
      simp [rayPolynomial, B, smul_eq_C_mul, Polynomial.smul_eq_C_mul]
    have hc := rayPolynomial_top_coeff (BinomialPolynomial.block (0 : Fin 1) r 0)
      (fun _ => 1) (fun _ => 0) (by simp)
    rw [BinomialPolynomial.block_degree, BinomialPolynomial.block_top] at hc
    simp only [eval_monomial, Finsupp.prod_single_index, one_pow, mul_one] at hc
    rw [hscale, Polynomial.coeff_smul, hc, smul_eq_mul]
  have hqc : Q.coeff r = eval (fun _ : Fin 1 => (1 : ℚ)) (homogeneousComponent r F) :=
    rayPolynomial_top_coeff F _ _ (by simp)
  rw [hpc, hqc] at hcoeff
  have hf : (0 : ℚ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hmul := mul_le_mul_of_nonneg_left hcoeff hf.le
  change (δ : ℚ) ≤ eval (fun _ : Fin 1 => (1 : ℚ))
    ((r.factorial : ℚ) • homogeneousComponent r F)
  rw [smul_eq_C_mul, map_mul, eval_C]
  have hc : (r.factorial : ℚ) * ((δ : ℚ) * (r.factorial : ℚ)⁻¹) = δ := by
    field_simp
  rwa [hc] at hmul

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponNormalizationRankDegree

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators nonZeroDivisors
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Chardin
open Hilbert SectionThree
variable {K A F L : Type*} [Field K] [CommRing A] [IsDomain A]
  [Field F] [Field L] [Algebra K A]

theorem hilbertFunction_kernel_eq_finrank_image (N : ℕ)
    (q : (projectiveSpace K N).CoordinateRing →ₐ[K] A)
    (hq : Function.Surjective q) (m : ℕ) :
    hilbertFunction K 1 (fun _ => N) (RingHom.ker q.toRingHom) (fun _ => m) =
      Module.finrank K ((homogeneousSubmodule (projectiveSpace K N).Variable K m).map
        q.toLinearMap) := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hq
  have he := e.toLinearEquiv.finrank_map_eq
    (quotientPiece K 1 (fun _ => N) (RingHom.ker q.toRingHom) (fun _ => m))
  have hcomp : e.toLinearEquiv.toLinearMap.comp
      (Ideal.Quotient.mkₐ K (RingHom.ker q.toRingHom)).toLinearMap = q.toLinearMap := by
    apply LinearMap.ext
    intro P
    exact Ideal.quotientKerAlgEquivOfSurjective_mk hq P
  change Module.finrank K (((degreePiece K 1 (fun _ => N) (fun _ => m)).map
      (Ideal.Quotient.mkₐ K (RingHom.ker q.toRingHom)).toLinearMap).map
      e.toLinearEquiv.toLinearMap) =
    hilbertFunction K 1 (fun _ => N) (RingHom.ker q.toRingHom) (fun _ => m) at he
  rw [← Submodule.map_comp, hcomp, ordinary_degreePiece_eq] at he
  exact he.symm

variable (r : ℕ)
  [Algebra (MvPolynomial (Fin (r + 1)) K) A]
  [Algebra (MvPolynomial (Fin (r + 1)) K) F]
  [Algebra (MvPolynomial (Fin (r + 1)) K) L]
  [Algebra A L] [Algebra F L]
  [IsScalarTower K (MvPolynomial (Fin (r + 1)) K) A]
  [IsScalarTower (MvPolynomial (Fin (r + 1)) K) A L]
  [IsScalarTower (MvPolynomial (Fin (r + 1)) K) F L]
  [IsFractionRing (MvPolynomial (Fin (r + 1)) K) F] [IsFractionRing A L]
  [FaithfulSMul (MvPolynomial (Fin (r + 1)) K) A]
  [Module.Finite (MvPolynomial (Fin (r + 1)) K) A]

theorem normalization_rank_le_degree (N : ℕ)
    (q : (projectiveSpace K N).CoordinateRing →ₐ[K] A)
    (hq : Function.Surjective q)
    (hhom : IsMultihomogeneousIdeal (projectiveSpace K N) (RingHom.ker q.toRingHom))
    (hdim : idealDimension (projectiveSpace K N) (RingHom.ker q.toRingHom) = r)
    (hlinear : ∀ j : Fin (r + 1), ∃ U : (projectiveSpace K N).CoordinateRing,
      U.IsHomogeneous 1 ∧ algebraMap (MvPolynomial (Fin (r + 1)) K) A (X j) = q U) :
    (Module.finrank F L : ℚ) ≤
      idealDegreeValue (projectiveSpace K N) (RingHom.ker q.toRingHom) (fun _ => 1) := by
  classical
  choose U hU hlinear using hlinear
  obtain ⟨E, P, hP, hLI⟩ := exists_uniform_homogeneous_fraction_basis
    (F := F) (L := L) q hq (0 : Fin (r + 1)) (U 0) (hU 0) (hlinear 0)
  apply rank_le_degree_of_shifted_hilbert_lower N _ hhom (Module.finrank F L) E
  intro m
  rw [hdim, hilbertFunction_kernel_eq_finrank_image N q hq]
  have h := homogeneous_image_finrank_lower (F := F) (L := L) q U hU hlinear P hP hLI m
  simpa only [homogeneousSubmodule_finrank] using h

end PhilipponMultiplicity.Chardin

end
end

section
-- Reused implementation: Solutions.PhilipponLinearNormalizationStep

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.LinearNormalization
variable {K : Type*} [Field K] {n : ℕ}

def polynomialEquiv (a : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin n) K) :=
  (shear a).trans (finSuccEquiv K n)

def transformedIdeal (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (a : Fin n → K) :
    Ideal (Polynomial (MvPolynomial (Fin n) K)) := I.map (polynomialEquiv a)

def quotientEquiv (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (a : Fin n → K) :
    (MvPolynomial (Fin (n + 1)) K ⧸ I) ≃ₐ[K]
      (Polynomial (MvPolynomial (Fin n) K) ⧸ transformedIdeal I a) :=
  Ideal.quotientEquivAlg I (transformedIdeal I a) (polynomialEquiv a) rfl

def coefficientHom (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (a : Fin n → K) :
    MvPolynomial (Fin n) K →ₐ[MvPolynomial (Fin n) K]
      (Polynomial (MvPolynomial (Fin n) K) ⧸ transformedIdeal I a) :=
  (Ideal.Quotient.mkₐ _ (transformedIdeal I a)).comp (Algebra.ofId _ _)

def projectionHom (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (a : Fin n → K) :
    MvPolynomial (Fin n) K →ₐ[K] (MvPolynomial (Fin (n + 1)) K ⧸ I) :=
  (quotientEquiv I a).symm.toAlgHom.comp ((coefficientHom I a).restrictScalars K)

def linearSubstitution (a : Fin n → K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  aeval (fun i => X i.succ - C (a i) * X 0)

theorem projectionHom_eq (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (a : Fin n → K) :
    projectionHom I a = (Ideal.Quotient.mkₐ K I).comp (linearSubstitution a) := by
  ext i
  apply (quotientEquiv I a).injective
  change quotientEquiv I a ((quotientEquiv I a).symm ((coefficientHom I a) (X i))) = _
  rw [AlgEquiv.apply_symm_apply]
  change (coefficientHom I a) (X i) =
    quotientEquiv I a (Ideal.Quotient.mk I (linearSubstitution a (X i)))
  rw [quotientEquiv, Ideal.quotientEquivAlg_mk]
  change Ideal.Quotient.mk (transformedIdeal I a) (Polynomial.C (X i)) = _
  congr 1
  simp [polynomialEquiv, linearSubstitution, shear, shearHom, finSuccEquiv_X_succ]

theorem linearSubstitution_homogeneous (a : Fin n → K)
    {P : MvPolynomial (Fin n) K} {d : ℕ} (hP : P.IsHomogeneous d) :
    (linearSubstitution a P).IsHomogeneous d := by
  unfold linearSubstitution
  simpa only [one_mul] using hP.aeval _ (n := 1) (fun i =>
    (isHomogeneous_X _ i.succ).sub
      (by simpa only [zero_add] using (isHomogeneous_C _ _).mul (isHomogeneous_X _ _)))

theorem linearSubstitution_component (a : Fin n → K) (P : MvPolynomial (Fin n) K) (d : ℕ) :
    homogeneousComponent d (linearSubstitution a P) =
      linearSubstitution a (homogeneousComponent d P) := by
  classical
  rw [P.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hh := isHomogeneous_monomial (coeff e P) (rfl : e.degree = e.degree)
  have hs := linearSubstitution_homogeneous a hh
  rw [homogeneousComponent_of_mem hs, homogeneousComponent_of_mem hh]
  split_ifs <;> simp

theorem projection_kernel_homogeneous
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : ∀ P ∈ I, ∀ d, homogeneousComponent d P ∈ I) (a : Fin n → K) :
    ∀ P ∈ RingHom.ker (projectionHom I a).toRingHom,
      ∀ d, homogeneousComponent d P ∈ RingHom.ker (projectionHom I a).toRingHom := by
  intro P hP d
  rw [projectionHom_eq] at hP ⊢
  change Ideal.Quotient.mk I (linearSubstitution a P) = 0 at hP
  change Ideal.Quotient.mk I (linearSubstitution a (homogeneousComponent d P)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← linearSubstitution_component]
  exact hI _ (Ideal.Quotient.eq_zero_iff_mem.mp hP) d

theorem exists_integral_linear_projection [Infinite K]
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    {P : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hP : P.IsHomogeneous d) (hPI : P ∈ I) (hne : P ≠ 0) :
    ∃ a : Fin n → K, (projectionHom I a).IsIntegral := by
  obtain ⟨a, ha⟩ := exists_shear_unit_leadingCoeff hP hne
  have hmem : finSuccEquiv K n (shear a P) ∈ transformedIdeal I a :=
    Ideal.mem_map_of_mem (polynomialEquiv a) hPI
  have hint : (coefficientHom I a).IsIntegral :=
    (Polynomial.monic_of_isUnit_leadingCoeff_inv_smul ha).quotient_isIntegral
      (Submodule.smul_of_tower_mem _ ha.unit⁻¹.val hmem)
  refine ⟨a, ?_⟩
  change ((quotientEquiv I a).symm.toAlgHom.toRingHom.comp
    (coefficientHom I a).toRingHom).IsIntegral
  have he : RingHom.IsIntegral
      (R := Polynomial (MvPolynomial (Fin n) K) ⧸ transformedIdeal I a)
      (A := MvPolynomial (Fin (n + 1)) K ⧸ I)
      (quotientEquiv I a).symm.toAlgHom.toRingHom := by
    apply RingHom.isIntegral_of_surjective
    exact (quotientEquiv I a).symm.surjective
  exact RingHom.IsIntegral.trans (R := MvPolynomial (Fin n) K)
    (S := Polynomial (MvPolynomial (Fin n) K) ⧸ transformedIdeal I a)
    (T := MvPolynomial (Fin (n + 1)) K ⧸ I) (coefficientHom I a).toRingHom
    (quotientEquiv I a).symm.toAlgHom.toRingHom hint he

end PhilipponMultiplicity.LinearNormalization

end
end

section
-- Reused implementation: Solutions.PhilipponLinearNoetherNormalization

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.LinearNormalization
variable {K : Type*} [Field K] [Infinite K]

theorem exists_integral_injective_linear_hom (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) (hne : I ≠ ⊤)
    (hI : ∀ P ∈ I, ∀ d, homogeneousComponent d P ∈ I) :
    ∃ s ≤ n, ∃ g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial (Fin n) K ⧸ I),
      Function.Injective g ∧ g.IsIntegral ∧
        ∀ i : Fin s, ∃ P : MvPolynomial (Fin n) K,
          P.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk I P := by
  induction n with
  | zero =>
    obtain ⟨s, hs, g, hg, hint⟩ := exists_integral_inj_algHom_of_quotient I hne
    have hs0 : s = 0 := by omega
    subst s
    exact ⟨0, le_rfl, g, hg, hint, fun i => Fin.elim0 i⟩
  | succ n ih =>
    let : Nontrivial (MvPolynomial (Fin (n + 1)) K ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr hne
    by_cases hbot : I = ⊥
    · have hbij : Function.Bijective (Ideal.Quotient.mkₐ K I) :=
        (Ideal.Quotient.mk_bijective_iff_eq_bot I).mpr hbot
      exact ⟨n + 1, le_rfl, Ideal.Quotient.mkₐ K I, hbij.1,
        RingHom.isIntegral_of_surjective _ hbij.2,
        fun i => ⟨X i, isHomogeneous_X _ i, rfl⟩⟩
    · obtain ⟨P, hPI, hP⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨d, hd⟩ : ∃ d, homogeneousComponent d P ≠ 0 := by
        by_contra! h
        apply hP
        rw [← sum_homogeneousComponent P]
        simp only [h, Finset.sum_const_zero]
      obtain ⟨a, ha⟩ := exists_integral_linear_projection I
        (homogeneousComponent_isHomogeneous d P) (hI P hPI d) hd
      let f := projectionHom I a
      let J := RingHom.ker f.toRingHom
      have hJ : ∀ P ∈ J, ∀ d, homogeneousComponent d P ∈ J :=
        projection_kernel_homogeneous I hI a
      obtain ⟨s, hs, g, hg, hint, hlinear⟩ := ih J (RingHom.ker_ne_top f.toRingHom) hJ
      let φ := Ideal.kerLiftAlg f
      have hcomp : φ.comp (Ideal.Quotient.mkₐ K J) = f := by
        apply AlgHom.ext
        intro P
        exact Ideal.kerLiftAlg_mk f P
      refine ⟨s, hs.trans (Nat.le_succ n), φ.comp g,
        (Ideal.kerLiftAlg_injective f).comp hg, ?_, ?_⟩
      · have ht : (φ.comp (Ideal.Quotient.mkₐ K J)).IsIntegral := by
          rw [hcomp]
          exact ha
        exact hint.trans _ _ (ht.tower_top _ _)
      · intro i
        obtain ⟨Q, hQ, hgQ⟩ := hlinear i
        refine ⟨linearSubstitution a Q, linearSubstitution_homogeneous a hQ, ?_⟩
        change φ (g (X i)) = _
        rw [hgQ]
        change projectionHom I a Q = _
        rw [projectionHom_eq]
        rfl

end PhilipponMultiplicity.LinearNormalization

end
end

section
-- Reused implementation: Solutions.NoetherIntegralDimension

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace PolynomialGrowth.IntegralDimension

private lemma exists_ltSeries_comap_eq_last {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R S x
    exact ⟨RelSeries.singleton _ q, rfl, hq⟩
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      have h1 : PrimeSpectrum.comap (algebraMap R S) L.last ≤ x := hlast ▸ le_of_lt hx
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h1
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal L.last.asIdeal hle
    have hlx : l.last < x := hx
    have hQlt : L.last < (⟨Q, hQprime⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
      intro h
      refine absurd ?_ (ne_of_lt hlx)
      calc l.last = PrimeSpectrum.comap (algebraMap R S) L.last := hlast.symm
        _ = PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQprime⟩ := by rw [h]
        _ = x := PrimeSpectrum.ext hQcomap
    refine ⟨L.snoc ⟨Q, hQprime⟩ hQlt, by simp [hlen], ?_⟩
    simp only [RelSeries.last_snoc]
    exact PrimeSpectrum.ext hQcomap

theorem ringKrullDim_eq_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := by
  refine le_antisymm ?_ ?_
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    refine iSup_le fun l => ?_
    obtain ⟨L, hlen, -⟩ := exists_ltSeries_comap_eq_last hinj l
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim L
  · change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)

end PolynomialGrowth.IntegralDimension

end

section
-- Reused implementation: Solutions.PhilipponLinearFiniteNormalization

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.LinearNormalization
variable {K : Type*} [Field K] [Infinite K]

theorem exists_finite_injective_linear_hom_fin (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) (hne : I ≠ ⊤)
    (hI : ∀ P ∈ I, ∀ d, homogeneousComponent d P ∈ I) :
    ∃ s ≤ n, ∃ g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial (Fin n) K ⧸ I),
      Function.Injective g ∧ g.Finite ∧
        ringKrullDim (MvPolynomial (Fin n) K ⧸ I) = (s : WithBot ℕ∞) ∧
        ∀ i : Fin s, ∃ P : MvPolynomial (Fin n) K,
          P.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk I P := by
  obtain ⟨s, hs, g, hg, hint, hlinear⟩ :=
    exists_integral_injective_linear_hom n I hne hI
  let A := MvPolynomial (Fin n) K ⧸ I
  let B := MvPolynomial (Fin s) K
  have hbase : algebraMap K A = g.toRingHom.comp (algebraMap K B) := by
    ext k
    exact (g.commutes k).symm
  have hfinite : g.Finite := hint.to_finite
    (hbase ▸ RingHom.finiteType_algebraMap.mpr
      (inferInstance : Algebra.FiniteType K A)).of_comp_finiteType
  letI : Algebra B A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral B A := ⟨hint⟩
  have hdim := PolynomialGrowth.IntegralDimension.ringKrullDim_eq_of_isIntegral_of_injective
    (R := B) (S := A) hg
  have hd : ringKrullDim A = (s : WithBot ℕ∞) := by
    rw [← hdim]
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact ⟨s, hs, g, hg, hfinite, hd, hlinear⟩

theorem exists_finite_injective_linear_hom {σ : Type*} [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (hne : I ≠ ⊤)
    (hI : ∀ P ∈ I, ∀ d, homogeneousComponent d P ∈ I) :
    ∃ s ≤ Fintype.card σ, ∃ g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial σ K ⧸ I),
      Function.Injective g ∧ g.Finite ∧
        ringKrullDim (MvPolynomial σ K ⧸ I) = (s : WithBot ℕ∞) ∧
        ∀ i : Fin s, ∃ P : MvPolynomial σ K,
          P.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk I P := by
  classical
  let e := renameEquiv K (Fintype.equivFin σ)
  let J := I.map e.toRingEquiv.toRingHom
  have hJne : J ≠ ⊤ := by
    intro h
    exact hne ((Ideal.map_eq_top_of_bijective e.toRingEquiv.toRingHom e.bijective).mp h)
  have hJ : ∀ P ∈ J, ∀ d, homogeneousComponent d P ∈ J := by
    intro P hP d
    obtain ⟨Q, hQ, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ e.surjective).mp hP
    change homogeneousComponent d (rename (Fintype.equivFin σ) Q) ∈ J
    rw [← rename_homogeneousComponent]
    exact Ideal.mem_map_of_mem e.toRingEquiv.toRingHom (hI Q hQ d)
  obtain ⟨s, hs, g, hg, hfin, hdim, hlinear⟩ :=
    exists_finite_injective_linear_hom_fin _ J hJne hJ
  let φ := Ideal.quotientEquivAlg I J e rfl
  refine ⟨s, hs, φ.symm.toAlgHom.comp g, φ.symm.injective.comp hg,
    (AlgHom.Finite.of_surjective φ.symm.toAlgHom φ.symm.surjective).comp hfin,
    ?_, ?_⟩
  · exact (ringKrullDim_eq_of_ringEquiv φ.toRingEquiv).trans hdim
  · intro i
    obtain ⟨P, hP, hgP⟩ := hlinear i
    refine ⟨e.symm P, hP.rename_isHomogeneous, ?_⟩
    change φ.symm (g (X i)) = _
    rw [hgP]
    apply φ.injective
    rw [AlgEquiv.apply_symm_apply]
    change Ideal.Quotient.mk J P = φ (Ideal.Quotient.mk I (e.symm P))
    change Ideal.Quotient.mk J P = (Ideal.quotientEquivAlg I J e rfl)
      (Ideal.Quotient.mk I (e.symm P))
    rw [Ideal.quotientEquivAlg_mk, AlgEquiv.apply_symm_apply]

end PhilipponMultiplicity.LinearNormalization

end
end

section
-- Reused implementation: Solutions.PhilipponProjectiveLinearNormalization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] [Infinite K]

theorem exists_projective_linear_normalization (N : ℕ)
    (p : Ideal (projectiveSpace K N).CoordinateRing) (hp : p.IsPrime)
    (hhom : IsMultihomogeneousIdeal (projectiveSpace K N) p)
    (hrel : IsRelevant K 1 (fun _ => N) p) :
    ∃ g : MvPolynomial (Fin (idealDimension (projectiveSpace K N) p + 1)) K →ₐ[K]
        ((projectiveSpace K N).CoordinateRing ⧸ p),
      Function.Injective g ∧ g.Finite ∧
        ∀ i, ∃ L : (projectiveSpace K N).CoordinateRing,
          L.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk p L := by
  have hc : ∀ P ∈ p, ∀ d, homogeneousComponent d P ∈ p := by
    intro P hP d
    exact Eq.mp (congrArg (fun Q : (projectiveSpace K N).CoordinateRing => Q ∈ p)
      (ordinary_component_eq N P (fun _ => d))) (hhom P hP (fun _ => d))
  obtain ⟨s, _, g, hg, hfin, hdim, hlinear⟩ :=
    LinearNormalization.exists_finite_injective_linear_hom p hp.ne_top hc
  have hs : s = idealDimension (projectiveSpace K N) p + 1 := by
    have hh := hdim.symm.trans
      (relevant_prime_krull_dimension_formula (projectiveSpace K N) p hp hhom hrel)
    exact_mod_cast hh
  subst s
  exact ⟨g, hg, hfin, hlinear⟩

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponProjectiveHilbertUpperCharZero

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped nonZeroDivisors
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Chardin
open Hilbert SectionThree
variable {K A : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [CommRing A] [IsDomain A] [Algebra K A]

theorem hilbert_upper_of_finite_linear_normalization (N r : ℕ)
    (q : (projectiveSpace K N).CoordinateRing →ₐ[K] A)
    (hq : Function.Surjective q)
    (hhom : IsMultihomogeneousIdeal (projectiveSpace K N) (RingHom.ker q.toRingHom))
    (hdim : idealDimension (projectiveSpace K N) (RingHom.ker q.toRingHom) = r)
    (g : MvPolynomial (Fin (r + 1)) K →ₐ[K] A)
    (hg : Function.Injective g) (hfin : g.Finite)
    (hlinear : ∀ i, ∃ Q : (projectiveSpace K N).CoordinateRing,
      Q.IsHomogeneous 1 ∧ g (X i) = q Q) (m : ℕ) :
    (hilbertFunction K 1 (fun _ => N) (RingHom.ker q.toRingHom) (fun _ => m) : ℚ) ≤
      (Nat.choose (m + r) r : ℚ) *
        idealDegreeValue (projectiveSpace K N) (RingHom.ker q.toRingHom) (fun _ => 1) := by
  let R := MvPolynomial (Fin (r + 1)) K
  let : Algebra R A := g.toAlgebra
  let : IsScalarTower K R A := .of_algebraMap_eq' g.comp_algebraMap.symm
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  let : Module.Finite R A := hfin
  let F := FractionRing R
  let L := FractionRing A
  let : Algebra F L := FractionRing.liftAlgebra R L
  let : IsScalarTower R F L := FractionRing.isScalarTower_liftAlgebra R L
  let : Module.Finite F L := Module.Finite.of_isLocalization R A R⁰
  let : CharZero F := inferInstance
  let : Algebra.IsIntegral F L := Algebra.IsIntegral.of_finite F L
  let : Algebra.IsSeparable F L := Algebra.IsSeparable.of_integral F L
  have hc : ∀ P ∈ RingHom.ker q.toRingHom, ∀ d,
      homogeneousComponent d P ∈ RingHom.ker q.toRingHom := by
    intro P hP d
    exact Eq.mp (congrArg (fun Q : (projectiveSpace K N).CoordinateRing =>
      Q ∈ RingHom.ker q.toRingHom) (ordinary_component_eq N P (fun _ => d)))
        (hhom P hP (fun _ => d))
  have hu := homogeneous_image_finrank_upper_of_separable_normalization
    (F := F) (L := L) r q hq hc hlinear m
  have hd := normalization_rank_le_degree (F := F) (L := L) r N q hq hhom hdim hlinear
  rw [hilbertFunction_kernel_eq_finrank_image N q hq]
  calc
    _ ≤ ((Module.finrank F L * Nat.choose (m + r) r : ℕ) : ℚ) := by exact_mod_cast hu
    _ = (Nat.choose (m + r) r : ℚ) * Module.finrank F L := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)

end PhilipponMultiplicity.Chardin

namespace PhilipponMultiplicity.Hilbert
open SectionThree

theorem projective_prime_hilbert_upper_bound_charZero
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] (N : ℕ)
    (p : Ideal (projectiveSpace K N).CoordinateRing) (hp : p.IsPrime)
    (hhom : IsMultihomogeneousIdeal (projectiveSpace K N) p)
    (hrel : IsRelevant K 1 (fun _ => N) p) (m : ℕ) :
    (hilbertFunction K 1 (fun _ => N) p (fun _ => m) : ℚ) ≤
      (Nat.choose (m + idealDimension (projectiveSpace K N) p)
        (idealDimension (projectiveSpace K N) p) : ℚ) *
        idealDegreeValue (projectiveSpace K N) p (fun _ => 1) := by
  letI : p.IsPrime := hp
  obtain ⟨g, hg, hfin, hlinear⟩ := exists_projective_linear_normalization N p hp hhom hrel
  let q := Ideal.Quotient.mkₐ K p
  have hker : RingHom.ker q.toRingHom = p := Ideal.mk_ker
  have hh : IsMultihomogeneousIdeal (projectiveSpace K N) (RingHom.ker q.toRingHom) :=
    hker.symm ▸ hhom
  have hd : idealDimension (projectiveSpace K N) (RingHom.ker q.toRingHom) =
      idealDimension (projectiveSpace K N) p := congrArg _ hker
  have h := Chardin.hilbert_upper_of_finite_linear_normalization
    N _ q (Ideal.Quotient.mk_surjective) hh hd g hg hfin hlinear m
  simpa only [hker] using h

end PhilipponMultiplicity.Hilbert

end
end

section
-- Reused implementation: Solutions.PhilipponJacobianPresentation

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity.PolynomialJacobian

theorem basefield_facts {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K ∧ IsAlgClosed K ∧ CharZero K := by
  have hcomplete : CompleteSpace K := by
    rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
    · exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
    · letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨e, he⟩ := h
      exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
  have hchar : CharZero K := by
    rcases hK with ⟨e, _⟩ | ⟨p, hp, h⟩
    · exact e.toRingHom.charZero
    · letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨e, _⟩ := h
      exact e.toRingHom.charZero
  have hclosed : IsAlgClosed K := by
    have transfer (F : Type) [Field F] [IsAlgClosed F] (e : K ≃+* F) : IsAlgClosed K := by
      apply IsAlgClosed.of_exists_root K
      intro P _ hP
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_eval₂_eq_zero e.toRingHom P
        (ne_of_gt (Polynomial.degree_pos_of_irreducible hP))
      refine ⟨e.symm x, ?_⟩
      apply e.injective
      rw [map_zero]
      change e.toRingHom (P.eval (e.symm x)) = 0
      rw [← Polynomial.eval₂_at_apply]
      change P.eval₂ e.toRingHom (e (e.symm x)) = 0
      simpa only [RingEquiv.apply_symm_apply] using hx
    rcases hK with ⟨e, _⟩ | ⟨p, hp, h⟩
    · exact transfer ℂ e
    · letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨e, _⟩ := h
      exact transfer (PadicComplex p) e
  exact ⟨hcomplete, hclosed, hchar⟩

end PhilipponMultiplicity.PolynomialJacobian

end
end

section
-- Reused implementation: Solutions.PhilipponSubgroupHilbertUpperProof

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

theorem subgroup_hilbert_upper_proof
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (H : AlgebraicSubgroup G)
    (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal H.carrier) (fun i => 2 * D i) : ℝ) ≤
      (Nat.choose (varietyDimension G H.carrier + 2) (varietyDimension G H.carrier) : ℝ) *
        hilbertDegreeForm G H.carrier D := by
  letI : IsAlgClosed K := hK.isAlgClosed
  letI : CharZero K := (PolynomialJacobian.basefield_facts hK).2.2
  apply subgroup_hilbert_upper_of_ordinary_prime_bound K hK ?_ G H D hD
  intro N p hp hhom
  by_cases hrel : Hilbert.IsRelevant K 1 (fun _ => N) p
  · simpa only [Nat.add_comm] using
      Hilbert.projective_prime_hilbert_upper_bound_charZero K N p hp hhom hrel 2
  · have hz : Hilbert.hilbertFunction K 1 (fun _ => N) p (fun _ => 2) = 0 :=
      Hilbert.irrelevant_prime_hilbertFunction_zero (projectiveSpace K N)
        p hp hrel (fun _ => 2) (fun _ => by norm_num)
    rw [hz, Nat.cast_zero]
    apply mul_nonneg (Nat.cast_nonneg _)
    exact PrimaryComponentSupport.degreeValue_nonneg (projectiveSpace K N) p hhom _

end PhilipponMultiplicity

end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (H : AlgebraicSubgroup G)
    (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal H.carrier) (fun i => 2 * D i) : ℝ) ≤
      (Nat.choose (varietyDimension G H.carrier + 2) (varietyDimension G H.carrier) : ℝ) *
        hilbertDegreeForm G H.carrier D := by
  exact subgroup_hilbert_upper_proof K hK G H D hD
