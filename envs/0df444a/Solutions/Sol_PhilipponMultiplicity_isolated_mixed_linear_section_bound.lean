-- Prove2me | solution 1 for PhilipponMultiplicity.isolated_mixed_linear_section_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T15:31:31.707748+00:00
-- url     : https://prove2.me/submissions/168d7585-26ca-49e9-99fb-22ad7c314e19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_filter_regular_mixed_section_preserving_isolated_points
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_exists
import Theorems.Thm_PhilipponMultiplicity_Hilbert_hilbertFunction_colon_add
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

/-- Colon by a multihomogeneous element preserves the actual grading. -/
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

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertPolynomial_colon_add
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    hilbertPolynomial K M.factorCount M.ambientDimension I =
      hilbertPolynomial K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) +
        aeval (fun i => X i - C (D i : ℚ))
          (hilbertPolynomial K M.factorCount M.ambientDimension (I.colon {P})) := by
  let J := I ⊔ Ideal.span {P}
  let Q := I.colon {P}
  obtain ⟨a, ha⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension J
    (multigraded_hilbert_polynomial_exists K M J (homogeneous_sup_span M I hI P D hP))
  obtain ⟨b, hb⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q (homogeneous_colon M I hI P D hP))
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨D + a + b, fun n hn => ?_⟩
  have hDn : ∀ i, D i ≤ n i := by intro i; have := hn i; change D i + a i + b i ≤ n i at this; omega
  have han : ∀ i, a i ≤ n i := by intro i; have := hn i; change D i + a i + b i ≤ n i at this; omega
  have hbsub : ∀ i, b i ≤ (n - D) i := by
    intro i; have := hn i; change D i + a i + b i ≤ n i at this; change b i ≤ n i - D i; omega
  have hnsub : D + (n - D) = n := by
    funext i; exact Nat.add_sub_of_le (hDn i)
  have heval (F : MvPolynomial M.FactorIndex ℚ) :
      eval (fun i => (n i : ℚ)) (aeval (fun i => X i - C (D i : ℚ)) F) =
        eval (fun i => (((n - D) i : ℕ) : ℚ)) F := by
    clear ha hb
    induction F using MvPolynomial.induction_on with
    | C c => simp
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F i hF =>
      simp only [map_mul, hF, aeval_X, map_sub, eval_X, eval_C]
      simp only [Pi.sub_apply, Nat.cast_sub (hDn i)]
  rw [map_add, heval, ha n han, hb (n - D) hbsub]
  have h := hilbertFunction_colon_add M I hI P D hP (n - D)
  rw [hnsub] at h
  exact_mod_cast h


end PhilipponMultiplicity.Hilbert
end
end

section

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
    rw [M.blockWeight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d


end PhilipponMultiplicity
end
end

section

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

/-- Translation subtracts the top degree, and its next homogeneous part is
the directional derivative of the old top part. -/
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

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.FiniteDifference
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def countIndex (l : List ι) : ι →₀ ℕ :=
  (l.map (fun i => Finsupp.single i 1)).sum

def mixedDifference (l : List ι) (F : MvPolynomial ι ℚ) : MvPolynomial ι ℚ :=
  l.foldl (fun P i => P - shift (Pi.single i 1) P) F

theorem countIndex_apply (l : List ι) (i : ι) : countIndex l i = l.count i := by
  induction l with
  | nil => simp [countIndex]
  | cons j l ih =>
    by_cases h : i = j
    · subst j
      simp [countIndex, List.count_cons, ← ih, Nat.add_comm]
    · simp [countIndex, List.count_cons, h, Ne.symm h, ← ih]

theorem countIndex_cons (i : ι) (l : List ι) :
    countIndex (i :: l) = countIndex l + Finsupp.single i 1 := by
  simp [countIndex, add_comm]

theorem degree_countIndex (l : List ι) : (countIndex l).degree = l.length := by
  induction l with
  | nil => simp [countIndex]
  | cons i l ih => simp [countIndex_cons, ih]

theorem sum_count (l : List ι) : ∑ i, l.count i = l.length := by
  simpa only [← countIndex_apply, ← Finsupp.degree_eq_sum] using degree_countIndex l

theorem factorial_count_cons (i : ι) (l : List ι) :
    (∏ j : ι, (((i :: l).count j).factorial : ℚ)) =
      (l.count i + 1 : ℚ) * ∏ j : ι, ((l.count j).factorial : ℚ) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun j => ((l.count j).factorial : ℚ))
        (Finset.mem_univ i)]
  have hprod : (∏ j ∈ Finset.univ.erase i, (((i :: l).count j).factorial : ℚ)) =
      ∏ j ∈ Finset.univ.erase i, ((l.count j).factorial : ℚ) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp [List.count_cons, hji, Ne.symm hji]
  rw [hprod, List.count_cons_self, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  ring

theorem deriv_single (i : ι) (F : MvPolynomial ι ℚ) :
    deriv (Pi.single i 1) F = pderiv i F := by
  classical
  rw [deriv_apply]
  simp [Pi.single_apply]

/-- A full mixed finite difference extracts the normalized top coefficient.
Lower total degrees vanish; zero coefficients and repeated block directions
are allowed, with no positivity hypothesis. -/
theorem mixedDifference_eq_constant (l : List ι) (F : MvPolynomial ι ℚ)
    (hF : F.totalDegree ≤ l.length) :
    mixedDifference l F =
      C (coeff (countIndex l) F * ∏ i, ((l.count i).factorial : ℚ)) := by
  induction l generalizing F with
  | nil =>
    have h0 : F.totalDegree = 0 := Nat.eq_zero_of_le_zero hF
    simpa [mixedDifference, countIndex] using
      (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0)
  | cons i l ih =>
    have htop := top_difference (Pi.single i 1) F (l.length + 1) (by omega) hF
    have hdeg : (F - shift (Pi.single i 1) F).totalDegree ≤ l.length := by
      simpa using htop.1
    change mixedDifference l (F - shift (Pi.single i 1) F) = _
    rw [ih _ hdeg]
    have hc : coeff (countIndex l) (F - shift (Pi.single i 1) F) =
        coeff (countIndex (i :: l)) F * (l.count i + 1 : ℚ) := by
      have h := congrArg (coeff (countIndex l)) htop.2
      simp only [Nat.add_sub_cancel, deriv_single, coeff_pderiv,
        coeff_homogeneousComponent, degree_countIndex, if_pos rfl,
        countIndex_apply] at h
      simpa [countIndex_cons, degree_countIndex] using h
    rw [hc, factorial_count_cons]
    congr 1
    ring

end PhilipponMultiplicity.FiniteDifference
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Only membership on the selected homogeneous piece matters for its
quotient Hilbert function. No global equality of the two ideals is needed. -/
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

/-- Equality in all sufficiently large block degrees preserves the actual
eventual quotient Hilbert polynomial. -/
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

/-- Filter regularity removes the multiplication kernel in large degrees,
even if the equation is a zero divisor on irrelevant components. -/
theorem hilbertPolynomial_colon_eq_of_eventual_injective
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing)
    (hinj : ∃ B : M.FactorIndex → ℕ, ∀ D, (∀ i, B i ≤ D i) →
      ∀ Q, M.IsHomogeneous Q D → P * Q ∈ I → Q ∈ I) :
    hilbertPolynomial K M.factorCount M.ambientDimension (I.colon {P}) =
      hilbertPolynomial K M.factorCount M.ambientDimension I := by
  symm
  apply hilbertPolynomial_eq_of_eventual_homogeneous_mem_iff M I _ hI
  obtain ⟨B,hB⟩ := hinj
  refine ⟨B,?_⟩
  intro D hD Q hQ
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm Q P]
  exact ⟨fun h => I.mul_mem_left P h,hB D hD Q hQ⟩

theorem hilbertPolynomial_filter_regular_cut
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hinj : ∃ B : M.FactorIndex → ℕ, ∀ E, (∀ i, B i ≤ E i) →
      ∀ Q, M.IsHomogeneous Q E → P * Q ∈ I → Q ∈ I) :
    hilbertPolynomial K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) =
      hilbertPolynomial K M.factorCount M.ambientDimension I -
        FiniteDifference.shift (fun i => (D i : ℚ))
          (hilbertPolynomial K M.factorCount M.ambientDimension I) := by
  have h := hilbertPolynomial_colon_add M I hI P D hP
  rw [hilbertPolynomial_colon_eq_of_eventual_injective M I hI P hinj] at h
  exact (eq_sub_iff_add_eq).mpr h.symm

theorem homogeneous_cut_chain (l : List M.FactorIndex)
    (J : ℕ → Ideal M.CoordinateRing) (P : ℕ → M.CoordinateRing)
    (hzero : IsMultihomogeneousIdeal M (J 0))
    (hstep : ∀ k (hk : k < l.length),
      M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧ J (k+1) = J k ⊔ Ideal.span {P k}) :
    ∀ k ≤ l.length, IsMultihomogeneousIdeal M (J k) := by
  intro k
  induction k with
  | zero => exact fun _ => hzero
  | succ k ih =>
    intro hk
    obtain ⟨hP,hJ⟩ := hstep k (by omega)
    rw [hJ]
    exact homogeneous_sup_span M _ (ih (by omega)) _ _ hP

/-- Iterate the exact-sequence computation along a flag, retaining the full
Hilbert polynomial until the final coefficient extraction. -/
theorem hilbertPolynomial_filter_regular_chain (l : List M.FactorIndex)
    (J : ℕ → Ideal M.CoordinateRing) (P : ℕ → M.CoordinateRing)
    (hzero : IsMultihomogeneousIdeal M (J 0))
    (hstep : ∀ k (hk : k < l.length),
      M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
      J (k+1) = J k ⊔ Ideal.span {P k} ∧
      ∃ B : M.FactorIndex → ℕ, ∀ D, (∀ i, B i ≤ D i) →
        ∀ Q, M.IsHomogeneous Q D → P k * Q ∈ J k → Q ∈ J k) :
    hilbertPolynomial K M.factorCount M.ambientDimension (J l.length) =
      FiniteDifference.mixedDifference l
        (hilbertPolynomial K M.factorCount M.ambientDimension (J 0)) := by
  classical
  have hhom := homogeneous_cut_chain M l J P hzero
    (fun k hk => ⟨(hstep k hk).1,(hstep k hk).2.1⟩)
  have haux : ∀ k ≤ l.length,
      hilbertPolynomial K M.factorCount M.ambientDimension (J k) =
        FiniteDifference.mixedDifference (l.take k)
          (hilbertPolynomial K M.factorCount M.ambientDimension (J 0)) := by
    intro k
    induction k with
    | zero => intro _; simp [FiniteDifference.mixedDifference]
    | succ k ih =>
      intro hk
      have hkl : k < l.length := by omega
      obtain ⟨hP,hJ,hinj⟩ := hstep k hkl
      rw [hJ,hilbertPolynomial_filter_regular_cut M _ (hhom k (by omega)) _ _ hP hinj,
        ih (by omega),List.take_succ_eq_append_getElem hkl]
      have hcast : (fun i => ((Pi.single (M := fun _ : M.FactorIndex => ℕ) l[k] 1 i : ℕ) : ℚ)) =
          Pi.single (M := fun _ : M.FactorIndex => ℚ) l[k] 1 := by
        funext i
        simp [Pi.single_apply]
      rw [hcast]
      simp only [FiniteDifference.mixedDifference,List.foldl_append,List.foldl_cons,List.foldl_nil]
  simpa only [List.take_length] using haux l.length le_rfl

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

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

/-- Any actual filter-regular flag with reduced final homogeneous pieces
computes the mixed degree. This theorem makes no generic-choice assumption. -/
theorem mixed_section_degree_of_filter_regular_flag
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (W : Set M.Point)
    (α : M.FactorIndex → ℕ) (hsum : ∑ i, α i = locusDimension M W)
    (L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K))
    (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing) (J : ℕ → Ideal M.CoordinateRing)
    (hcount : ∀ i, l.count i = α i) (hfirst : J 0 = M.vanishingIdeal W)
    (hstep : ∀ k (hk : k < l.length),
      M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧ J (k+1) = J k ⊔ Ideal.span {P k} ∧
      ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
        ∀ Q, M.IsHomogeneous Q D → P k * Q ∈ J k → Q ∈ J k)
    (hlast : ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
      ∀ Q, M.IsHomogeneous Q D →
        (Q ∈ J l.length ↔ Q ∈ M.vanishingIdeal (linearSlice M W L))) :
    locusDegreeValue M (linearSlice M W L) (fun _ => 1) =
      idealMixedDegree M (M.vanishingIdeal W) α := by
  classical
  have hhom0 : IsMultihomogeneousIdeal M (J 0) := by
    rw [hfirst]
    exact vanishingIdeal_multihomogeneous K M W
  have hhom := Hilbert.homogeneous_cut_chain M l J P hhom0
    (fun k hk => ⟨(hstep k hk).1,(hstep k hk).2.1⟩)
  have heq := Hilbert.hilbertPolynomial_eq_of_eventual_homogeneous_mem_iff M
    (J l.length) (M.vanishingIdeal (linearSlice M W L)) (hhom _ le_rfl) hlast
  have hpoly := Hilbert.hilbertPolynomial_filter_regular_chain M l J P hhom0 hstep
  have hlen : l.length = ∑ i, α i := by
    rw [← FiniteDifference.sum_count l]
    exact Finset.sum_congr rfl (fun i _ => hcount i)
  have hdegree : (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
      (J 0)).totalDegree ≤ l.length := by
    rw [hfirst,hlen,hsum]
    exact le_rfl
  rw [FiniteDifference.mixedDifference_eq_constant l _ hdegree,hfirst] at hpoly
  have hindex : FiniteDifference.countIndex l = Finsupp.equivFunOnFinite.symm α := by
    ext i
    change FiniteDifference.countIndex l i = α i
    rw [FiniteDifference.countIndex_apply,hcount i]
  have hconst : Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
      (M.vanishingIdeal (linearSlice M W L)) =
        C (idealMixedDegree M (M.vanishingIdeal W) α) := by
    rw [← heq,hpoly,hindex]
    unfold idealMixedDegree
    change ∑ i, α i = idealDimension M (M.vanishingIdeal W) at hsum
    rw [if_pos hsum]
    simp only [hcount]
  exact Hilbert.degreeValue_of_constant_hilbertPolynomial M _ _ hconst (fun _ => 1)


/-- Persistence of isolated points in a reduced filter-regular deformation
implies the numerical mixed intersection bound. -/
theorem isolated_mixed_bound_of_persistent_filter_regular_section
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hpersist : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) →
      ∀ S : Set M.Point, S.Finite → S ⊆ linearSlice M W L →
      (∀ x ∈ S, ∃ U : Set M.Point, @IsOpen _ M.zariskiTopology U ∧ x ∈ U ∧
        U ∩ linearSlice M W L ⊆ S) →
      ∃ L' : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L' i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L').Finite ∧
        Nonempty (S ↪ linearSlice M W L') ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
              ∀ Q, M.IsHomogeneous Q D → P k * Q ∈ J k → Q ∈ J k) ∧
          (∃ E : M.FactorIndex → ℕ, ∀ D, (∀ i, E i ≤ D i) →
            ∀ Q, M.IsHomogeneous Q D →
              (Q ∈ J l.length ↔ Q ∈ M.vanishingIdeal (linearSlice M W L')))) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) →
      ∀ S : Set M.Point, S.Finite → S ⊆ linearSlice M W L →
      (∀ x ∈ S, ∃ U : Set M.Point, @IsOpen _ M.zariskiTopology U ∧ x ∈ U ∧
        U ∩ linearSlice M W L ⊆ S) →
      locusDegreeValue M S (fun _ => 1) ≤ idealMixedDegree M (M.vanishingIdeal W) α := by
  classical
  intro M W hW hirr α hα hsum L hL S hS hsub hisolated
  obtain ⟨L',hL',hfinite,⟨f⟩,l,P,J,hcount,hfirst,hstep,hlast⟩ :=
    hpersist M W hW hirr α hα hsum L hL S hS hsub hisolated
  have hdegree := mixed_section_degree_of_filter_regular_flag M W α hsum L'
    l P J hcount hfirst hstep hlast
  let : Fintype S := hS.fintype
  let : Fintype (linearSlice M W L') := hfinite.fintype
  have hcard : S.ncard ≤ (linearSlice M W L').ncard := by
    simpa only [Set.fintypeCard_eq_ncard] using Fintype.card_le_of_injective f f.injective
  rw [M.locusDegreeValue_finite _ hfinite (fun _ => 1)] at hdegree
  rw [M.locusDegreeValue_finite S hS (fun _ => 1), ← hdegree]
  exact_mod_cast hcard

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity PhilipponMultiplicity.SectionThree

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) →
      ∀ S : Set M.Point, S.Finite → S ⊆ linearSlice M W L →
      (∀ x ∈ S, ∃ U : Set M.Point, @IsOpen _ M.zariskiTopology U ∧ x ∈ U ∧
        U ∩ linearSlice M W L ⊆ S) →
      locusDegreeValue M S (fun _ => 1) ≤ idealMixedDegree M (M.vanishingIdeal W) α := by
  exact isolated_mixed_bound_of_persistent_filter_regular_section K hK
    (exists_filter_regular_mixed_section_preserving_isolated_points K hK)
