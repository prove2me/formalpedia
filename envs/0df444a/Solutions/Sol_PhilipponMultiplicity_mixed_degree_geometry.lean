-- Prove2me | solution 1 for PhilipponMultiplicity.mixed_degree_geometry
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T13:24:50.796468+00:00
-- url     : https://prove2.me/submissions/dee01410-e996-4ae0-a36f-559883fe4b37

import Theorems.Thm_PhilipponMultiplicity_isolated_mixed_linear_section_bound
import Theorems.Thm_PhilipponMultiplicity_generic_mixed_linear_section_avoiding_boundary
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

section

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

theorem isClosed_zeroLocus_vanishingIdeal (S : Set M.Point) :
    @IsClosed _ M.zariskiTopology (M.zeroLocus (M.vanishingIdeal S)) := by
  letI := M.zariskiTopology
  have hset : M.zeroLocus (M.vanishingIdeal S) =
      ⋂ P : {P : M.CoordinateRing // (∃ D, M.IsHomogeneous P D) ∧
        ∀ x ∈ S, M.eval P x = 0}, {x | M.eval P.val x = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, zeroLocus]
    constructor
    · intro hx P
      exact hx P (Ideal.subset_span P.property)
    · intro hx P hP
      have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
        apply Ideal.span_le.mpr
        intro Q hQ
        exact hx ⟨Q, hQ⟩
      exact hle hP
  rw [hset]
  apply isClosed_iInter
  intro P
  obtain ⟨D, hD⟩ := P.property.1
  exact M.isClosed_zero P.val D hD

/-- The chosen-representative ideal agrees with Zariski closure. -/
theorem zeroLocus_vanishingIdeal_eq_closure (S : Set M.Point) :
    M.zeroLocus (M.vanishingIdeal S) = @closure _ M.zariskiTopology S := by
  letI := M.zariskiTopology
  apply Set.Subset.antisymm
  · intro x hx
    apply M.isTopologicalBasis_basic.mem_closure_iff.mpr
    rintro U ⟨P, D, hP, rfl⟩ hxU
    by_contra hn
    have hPS : ∀ y ∈ S, M.eval P y = 0 := by
      intro y hy
      by_contra hp
      exact hn ⟨y, hp, hy⟩
    exact hxU (hx P (Ideal.subset_span ⟨⟨D, hP⟩, hPS⟩))
  · apply closure_minimal
    · intro x hx P hP
      exact M.eval_eq_zero_of_mem_vanishingIdeal hP hx
    · exact M.isClosed_zeroLocus_vanishingIdeal S

end MultiProjectiveSpace
end PhilipponMultiplicity
end
end

section

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
end

section

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

/-- The genuine multigraded quotient Hilbert function of a projective point is one. -/
theorem hilbertFunction_singleton (p : M.Point) (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal {p}) D = 1 := by
  classical
  let V := Hilbert.degreePiece K M.factorCount M.ambientDimension D
  let I := M.vanishingIdeal {p}
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let g := (aeval (M.coordinate p) : M.CoordinateRing →ₐ[K] K).toLinearMap.domRestrict V
  have hker : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ M.eval P.val p = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro h
      exact M.eval_eq_zero_of_mem_vanishingIdeal h (Set.mem_singleton p)
    · intro h
      apply Ideal.subset_span
      refine ⟨⟨D, (M.degreePiece_iff P.val D).mp P.property⟩, ?_⟩
      rintro x rfl
      exact h
  obtain ⟨Q, hQ, hQp⟩ := M.exists_form_nonzero_at p D
  have hQg : Q ∈ V := (M.degreePiece_iff Q D).mpr hQ
  have hg : LinearMap.range g = ⊤ := LinearMap.range_eq_top.mpr (by
    intro c
    refine ⟨⟨(c / M.eval Q p) • Q, V.smul_mem _ hQg⟩, ?_⟩
    change MvPolynomial.eval (M.coordinate p) ((c / M.eval Q p) • Q) = c
    rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
    change (c / M.eval Q p) * M.eval Q p = c
    exact div_mul_cancel₀ _ hQp)
  let E := f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans g.quotKerEquivRange)
  have hdim := E.finrank_eq
  have hf : LinearMap.range f = Hilbert.quotientPiece K M.factorCount M.ambientDimension I D := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  rw [hf, hg, finrank_top, Module.finrank_self] at hdim
  exact hdim

theorem hilbertPolynomial_singleton (p : M.Point) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal {p}) = 1 := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, ?_⟩
  intro D _
  rw [M.hilbertFunction_singleton]
  simp

theorem degreeValue_singleton (p : M.Point) (D : M.FactorIndex → ℕ) :
    Hilbert.degreeValue K M.factorCount M.ambientDimension (M.vanishingIdeal {p}) D = 1 := by
  simp [Hilbert.degreeValue, Hilbert.degreeForm, M.hilbertPolynomial_singleton]

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
theorem hilbertDegreeForm_singleton {K : Type*} [Field K]
    (G : EmbeddedGroupProduct K) (x : G.Point) (D : G.FactorIndex → ℕ) :
    hilbertDegreeForm G {x} D = 1 := by
  unfold hilbertDegreeForm EmbeddedGroupProduct.vanishingIdeal
  rw [Set.image_singleton]
  exact_mod_cast G.ambient.degreeValue_singleton (G.embedding x) D
end PhilipponMultiplicity
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Compute a genuine quotient Hilbert function through a parametrization whose
polynomial kernel agrees with the homogeneous equations of the image. -/
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
end
end

section

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

@[simp] theorem evaluationMap_apply {X : Type*} (p : X → M.Point)
    (P : M.CoordinateRing) (x : X) : M.evaluationMap p P x = M.eval P (p x) := rfl

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
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MvPolynomial
namespace PhilipponMultiplicity.MultiProjectiveSpace

/-- Multihomogeneous equations distinguish actual projective points. -/
theorem point_eq_of_homogeneous_implication {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (x y : M.Point)
    (h : ∀ (P : M.CoordinateRing) (D : M.FactorIndex → ℕ),
      M.IsHomogeneous P D → M.eval P y = 0 → M.eval P x = 0) : x = y := by
  classical
  funext i
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (Projectivization.rep_nonzero (y i))
  change (y i).rep k ≠ 0 at hk
  have heq (j : Fin (M.ambientDimension i + 1)) :
      (y i).rep k * (x i).rep j - (y i).rep j * (x i).rep k = 0 := by
    have hP := (M.isHomogeneous_X ⟨i, j⟩).C_mul M ((y i).rep k)
    have hQ := (M.isHomogeneous_X ⟨i, k⟩).C_mul M ((y i).rep j)
    have hh := h _ _ (hP.sub M hQ) (by simp [eval, coordinate, mul_comm])
    simpa [eval, coordinate] using hh
  rw [← Projectivization.mk_rep (x i), ← Projectivization.mk_rep (y i)]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  exact ⟨(x i).rep k / (y i).rep k, by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hk).mpr
    simpa only [mul_comm] using (sub_eq_zero.mp (heq j)).symm⟩

end PhilipponMultiplicity.MultiProjectiveSpace

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem exists_homogeneous_separator (x y : M.Point) (hne : x ≠ y) :
    ∃ P : M.CoordinateRing, ∃ D : M.FactorIndex → ℕ,
      M.IsHomogeneous P D ∧ M.eval P y = 0 ∧ M.eval P x ≠ 0 := by
  by_contra! h
  exact hne (M.point_eq_of_homogeneous_implication x y h)

/-- A homogeneous section separates one point from any finite collection of
other points. The multidegree is allowed to depend on that collection. -/
theorem exists_homogeneous_finite_separator (x : M.Point) (S : Finset M.Point)
    (hx : x ∉ S) :
    ∃ P : M.CoordinateRing, ∃ D : M.FactorIndex → ℕ,
      M.IsHomogeneous P D ∧ M.eval P x ≠ 0 ∧ ∀ y ∈ S, M.eval P y = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨1,0,M.isHomogeneous_one,by simp [eval],by simp⟩
  | @insert y S hy ih =>
    have hxS : x ∉ S := fun h => hx (Finset.mem_insert_of_mem h)
    have hxy : x ≠ y := fun h => hx (h ▸ Finset.mem_insert_self _ _)
    obtain ⟨P,D,hP,hPx,hPS⟩ := ih hxS
    obtain ⟨Q,E,hQ,hQy,hQx⟩ := M.exists_homogeneous_separator x y hxy
    refine ⟨P*Q,D+E,hP.mul M hQ,?_,?_⟩
    · simpa only [eval,map_mul,mul_ne_zero_iff] using And.intro hPx hQx
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simpa only [eval,map_mul] using mul_eq_zero_of_right (M.eval P z) hQy
      · simpa only [eval,map_mul] using mul_eq_zero_of_left (hPS z hz) (M.eval Q z)

/-- In all sufficiently large block degrees the evaluation map onto a
finite set of multiprojective points is surjective. -/
theorem finite_sectionSpace_eventually_top (S : Set M.Point) (hS : S.Finite) :
    ∃ B : M.FactorIndex → ℕ, ∀ D : M.FactorIndex → ℕ, (∀ i, B i ≤ D i) →
      M.sectionSpace (fun x : S => x.val) D = ⊤ := by
  classical
  let : Fintype S := hS.fintype
  have hsep (a : S) :
      ∃ P : M.CoordinateRing, ∃ E : M.FactorIndex → ℕ,
        M.IsHomogeneous P E ∧ M.eval P a.val ≠ 0 ∧
          ∀ b : S, b ≠ a → M.eval P b.val = 0 := by
    obtain ⟨P,E,hP,hPa,hPS⟩ := M.exists_homogeneous_finite_separator a.val
      (hS.toFinset.erase a.val) (Finset.notMem_erase _ _)
    refine ⟨P,E,hP,hPa,?_⟩
    intro b hba
    exact hPS b.val (Finset.mem_erase.mpr
      ⟨fun he => hba (Subtype.ext he),hS.mem_toFinset.mpr b.property⟩)
  choose P E hP hPa hPS using hsep
  let B : M.FactorIndex → ℕ := fun i => ∑ a : S, E a i
  refine ⟨B,?_⟩
  intro D hD
  apply (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun K S)).mpr
  intro a
  have hEa (i : M.FactorIndex) : E a i ≤ D i :=
    (Finset.single_le_sum (fun b _ => Nat.zero_le (E b i)) (Finset.mem_univ a)).trans (hD i)
  obtain ⟨Q,hQ,hQa⟩ := M.exists_form_nonzero_at a.val (fun i => D i - E a i)
  let F : M.CoordinateRing := P a * Q
  have hF : M.IsHomogeneous F D := by
    have h := (hP a).mul M hQ
    have heq : E a + (fun i => D i - E a i) = D := by
      funext i
      exact Nat.add_sub_of_le (hEa i)
    exact heq ▸ h
  have hFa : M.eval F a.val ≠ 0 := by
    simpa only [F,eval,map_mul,mul_ne_zero_iff] using And.intro (hPa a) hQa
  let R : M.CoordinateRing := C (M.eval F a.val)⁻¹ * F
  have hR : M.IsHomogeneous R D := hF.C_mul M _
  rw [Pi.basisFun_apply]
  change (Pi.single a (1 : K)) ∈
    (Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
      (M.evaluationMap (fun x : S => x.val)).toLinearMap
  refine ⟨R,(M.degreePiece_iff _ _).mpr hR,?_⟩
  ext b
  change M.eval R b.val = Pi.single (M := fun _ : S => K) a (1 : K) b
  by_cases hba : b = a
  · subst b
    change (MvPolynomial.eval (M.coordinate a.val)) F ≠ 0 at hFa
    simp [R,eval, hFa]
  · have hzero : M.eval F b.val = 0 := by
      change M.eval (P a * Q) b.val = 0
      simpa only [eval,map_mul] using mul_eq_zero_of_left (hPS a b hba) (M.eval Q b.val)
    change (MvPolynomial.eval (M.coordinate b.val)) F = 0 at hzero
    simp [R,eval, hzero, hba]

theorem hilbertFunction_finite_eventually (S : Set M.Point) (hS : S.Finite) :
    ∃ B : M.FactorIndex → ℕ, ∀ D : M.FactorIndex → ℕ, (∀ i, B i ≤ D i) →
      Hilbert.hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal S) D =
        S.ncard := by
  classical
  let : Fintype S := hS.fintype
  obtain ⟨B,hB⟩ := M.finite_sectionSpace_eventually_top S hS
  refine ⟨B,?_⟩
  intro D hD
  have h := M.hilbertFunction_eq_sectionSpace (fun x : S => x.val) D
  rw [Subtype.range_val,hB D hD,finrank_top] at h
  simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    smul_eq_mul,mul_one,Set.fintypeCard_eq_ncard] using h

/-- The full eventual Hilbert polynomial of a finite set is its cardinality,
including the empty set. This is proved by homogeneous interpolation. -/
theorem hilbertPolynomial_finite (S : Set M.Point) (hS : S.Finite) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S) =
      C (S.ncard : ℚ) := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  obtain ⟨B,hB⟩ := M.hilbertFunction_finite_eventually S hS
  refine ⟨B,?_⟩
  intro D hD
  rw [hB D hD,eval_C]

theorem locusDegreeValue_finite (S : Set M.Point) (hS : S.Finite)
    (D : M.FactorIndex → ℕ) :
    SectionThree.locusDegreeValue M S D = (S.ncard : ℚ) := by
  unfold SectionThree.locusDegreeValue SectionThree.idealDegreeValue
    Hilbert.degreeValue Hilbert.degreeForm
  rw [M.hilbertPolynomial_finite S hS]
  dsimp only
  rw [MvPolynomial.totalDegree_C]
  simp
  change coeff 0 (C (S.ncard : ℚ)) = (S.ncard : ℚ)
  rw [MvPolynomial.coeff_C, if_pos rfl]

end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section
namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K] (M : MultiProjectiveSpace K)

theorem vanishingIdeal_closure (V : Set M.Point) :
    M.vanishingIdeal (@closure _ M.zariskiTopology V) = M.vanishingIdeal V := by
  letI := M.zariskiTopology
  apply le_antisymm (M.vanishingIdeal_antitone subset_closure)
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  exact Ideal.subset_span ⟨⟨D,hD⟩,closure_minimal hP (M.isClosed_zero P D hD)⟩

theorem locusDegreeValue_closure (V : Set M.Point) (D : M.FactorIndex → ℕ) :
    SectionThree.locusDegreeValue M (@closure _ M.zariskiTopology V) D =
      SectionThree.locusDegreeValue M V D := by
  unfold SectionThree.locusDegreeValue
  rw [M.vanishingIdeal_closure]

end PhilipponMultiplicity.MultiProjectiveSpace

end

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

/-- Pass from closed intersection estimates to the geometric interpretation
on a locally closed locus. Boundary components may have positive dimension,
so the upper estimate uses local isolation, not finiteness on the closure. -/
theorem mixed_degree_geometry_of_closed_section_estimates
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hisolated : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) →
      ∀ S : Set M.Point, S.Finite → S ⊆ linearSlice M W L →
      (∀ x ∈ S, ∃ U : Set M.Point, @IsOpen _ M.zariskiTopology U ∧ x ∈ U ∧
        U ∩ linearSlice M W L ⊆ S) →
      locusDegreeValue M S (fun _ => 1) ≤ idealMixedDegree M (M.vanishingIdeal W) α)
    (hgeneric : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        locusDegreeValue M (linearSlice M W L) (fun _ => 1) =
          idealMixedDegree M (M.vanishingIdeal W) α)
    (M : MultiProjectiveSpace K) (V : Set M.Point)
    (hV : @IsLocallyClosed _ M.zariskiTopology V)
    (hirr : @IsIrreducible _ M.zariskiTopology V)
    (α : M.FactorIndex → ℕ) (hα : ∀ i, α i ≤ M.ambientDimension i)
    (hsum : ∑ i, α i = locusDimension M V) :
    (∀ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) →
      (linearSlice M V L).Finite →
      ((linearSlice M V L).ncard : ℚ) ≤ idealMixedDegree M (M.vanishingIdeal V) α) ∧
    (∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
      (linearSlice M V L).Finite ∧
      ((linearSlice M V L).ncard : ℚ) = idealMixedDegree M (M.vanishingIdeal V) α) := by
  letI := M.zariskiTopology
  let W := closure V
  have hW : IsClosed W := isClosed_closure
  have hWirr : IsIrreducible W := hirr.closure
  have hI : M.vanishingIdeal W = M.vanishingIdeal V := M.vanishingIdeal_closure V
  have hsumW : ∑ i, α i = locusDimension M W := by
    simpa only [locusDimension,hI] using hsum
  have hsub (L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K)) :
      linearSlice M V L ⊆ linearSlice M W L :=
    fun x hx => ⟨subset_closure hx.1,hx.2⟩
  constructor
  · intro L hL hfinite
    have hlocal : ∀ x ∈ linearSlice M V L, ∃ U : Set M.Point,
        IsOpen U ∧ x ∈ U ∧ U ∩ linearSlice M W L ⊆ linearSlice M V L := by
      intro x hx
      refine ⟨coborder V,hV.isOpen_coborder,subset_coborder hx.1,?_⟩
      rintro y ⟨hyU,hyW,hyL⟩
      refine ⟨?_,hyL⟩
      exact (Set.ext_iff.mp (coborder_inter_closure (s := V)) y).mp ⟨hyU,hyW⟩
    have hbound := hisolated M W hW hWirr α hα hsumW L hL
      (linearSlice M V L) hfinite (hsub L) hlocal
    rwa [M.locusDegreeValue_finite _ hfinite (fun _ => 1),hI] at hbound
  · let B := W \ V
    have hB : IsClosed B := by
      have h := hV.isOpen_coborder.isClosed_compl
      simpa only [coborder,compl_compl] using h
    have hBW : B ⊆ W := Set.sdiff_subset
    have hproper : (W \ B).Nonempty := by
      obtain ⟨x,hx⟩ := hirr.nonempty
      exact ⟨x,subset_closure hx,fun h => h.2 hx⟩
    obtain ⟨L,hL,hfinite,hdisjoint,hdegree⟩ :=
      hgeneric M W hW hWirr α hα hsumW B hB hBW hproper
    have heq : linearSlice M V L = linearSlice M W L := by
      apply Set.Subset.antisymm (hsub L)
      intro x hx
      refine ⟨?_,hx.2⟩
      by_contra hnot
      exact Set.disjoint_left.mp hdisjoint hx ⟨hx.1,hnot⟩
    refine ⟨L,hL,heq.symm ▸ hfinite,?_⟩
    rw [heq,← M.locusDegreeValue_finite _ hfinite (fun _ => 1),hdegree,hI]

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity PhilipponMultiplicity.SectionThree

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K) (V : Set M.Point)
    (hV : @IsLocallyClosed _ M.zariskiTopology V)
    (hirr : @IsIrreducible _ M.zariskiTopology V)
    (α : M.FactorIndex → ℕ) (hα : ∀ i, α i ≤ M.ambientDimension i)
    (hsum : ∑ i, α i = locusDimension M V) :
    (∀ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) →
      (linearSlice M V L).Finite →
      ((linearSlice M V L).ncard : ℚ) ≤ idealMixedDegree M (M.vanishingIdeal V) α) ∧
    (∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
      (linearSlice M V L).Finite ∧
      ((linearSlice M V L).ncard : ℚ) = idealMixedDegree M (M.vanishingIdeal V) α) := by
  exact mixed_degree_geometry_of_closed_section_estimates K hK
    (isolated_mixed_linear_section_bound K hK)
    (generic_mixed_linear_section_avoiding_boundary K hK) M V hV hirr α hα hsum
