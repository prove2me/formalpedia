-- Prove2me | solution 1 for PhilipponMultiplicity.subgroup_hilbert_upper_at_double_degree
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-10T20:28:42.109007+00:00
-- url     : https://prove2.me/submissions/dff46539-3260-439c-8376-2fb6f76bc67d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_SectionFive
import Definitions.Def_PhilipponMultiplicity_SectionFour
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.KrullDimension
import Theorems.Thm_PhilipponMultiplicity_Hilbert_component_length_formula
import Theorems.Thm_PhilipponMultiplicity_Hilbert_hilbertPolynomial_filtration_sum
import Theorems.Thm_PhilipponMultiplicity_Hilbert_homogeneous_prime_filtration
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_antitone
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_projective_prime_hilbert_upper_bound
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
-- Reused implementation: Solutions.PhilipponSubgroupHilbertUpperLocal

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

theorem subgroup_hilbert_upper_chardin_reduction
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (H : AlgebraicSubgroup G)
    (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal H.carrier) (fun i => 2 * D i) : ℝ) ≤
      (Nat.choose (varietyDimension G H.carrier + 2) (varietyDimension G H.carrier) : ℝ) *
        hilbertDegreeForm G H.carrier D := by
  letI : IsAlgClosed K := hK.isAlgClosed
  apply subgroup_hilbert_upper_of_ordinary_prime_bound K hK ?_ G H D hD
  intro N p hp hhom
  by_cases hrel : Hilbert.IsRelevant K 1 (fun _ => N) p
  · simpa only [Nat.add_comm] using
      Hilbert.projective_prime_hilbert_upper_bound K N p hp hhom hrel 2
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
  exact subgroup_hilbert_upper_chardin_reduction K hK G H D hD
