-- Prove2me | solution 1 for PhilipponMultiplicity.source_boundary_counterexamples
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T14:51:20.217281+00:00
-- url     : https://prove2.me/submissions/a4b52ba6-8d83-4fda-8dbb-e21954b81a9e

import Mathlib
import Definitions.Def_PhilipponMultiplicity_Support
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_antitone
import Theorems.Thm_PhilipponMultiplicity_Hilbert_exists_relevant_minimalPrime_dimension_eq
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_prime_dimension_strict
import Theorems.Thm_PhilipponMultiplicity_product_projective_hilbert_function


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

theorem singleBlock_isHomogeneous {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    (projectiveSpace K N).IsHomogeneous
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => d) := by
  classical
  intro a ha i
  have h := hP.rename_isHomogeneous (f := fun j => (⟨(0 : Fin 1), j⟩ :
    (projectiveSpace K N).Variable)) (MvPolynomial.mem_support_iff.mp ha)
  change Finsupp.weight (1 : (projectiveSpace K N).Variable → ℕ) a = d at h
  rw [Finsupp.weight_eq_sum] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma] at h
  change (∑ x : Fin 1, ∑ y : Fin (N + 1), a ⟨x, y⟩) = d at h
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change (∑ j : Fin (N + 1), a ⟨(0 : Fin 1), j⟩) = d
  exact (Fin.sum_univ_one _).symm.trans h

theorem projective_isClosed_zero {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    @IsClosed _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | MvPolynomial.eval p.rep P = 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isClosed_zero _ _
    (singleBlock_isHomogeneous hP)).preimage hcont
  convert h using 1
  ext p
  change MvPolynomial.eval p.rep P = 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => p) = 0
  simp only [MultiProjectiveSpace.eval, MvPolynomial.eval_rename]
  rfl

theorem projective_isOpen_coordinate {K : Type*} [Field K] {N : ℕ}
    (j : Fin (N + 1)) :
    @IsOpen _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | p.rep j ≠ 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isOpen_basic _ _
    (singleBlock_isHomogeneous (MvPolynomial.isHomogeneous_X K j))).preimage
      hcont
  convert h using 1
  ext p
  change p.rep j ≠ 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) (MvPolynomial.X j)) (fun _ => p) ≠ 0
  simp [MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate]

theorem projective_regular_of_homogeneous
    {K X : Type u} [Field K] {N N' d : ℕ}
    (e : X → Projectivization K (Fin (N + 1) → K))
    (f : X → Projectivization K (Fin (N' + 1) → K))
    (P : Fin (N' + 1) → MvPolynomial (Fin (N + 1)) K)
    (hP : ∀ j, (P j).IsHomogeneous d)
    (hf : ∀ x, ∃ h : (fun j => MvPolynomial.eval (e x).rep (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval (e x).rep (P j)) h = f x) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K N) (projectiveSpace K N')
      (fun x => fun _ => e x) (fun x => fun _ => f x) := by
  letI := (projectiveSpace K N).zariskiTopology
  intro x b
  let Q : Fin (N' + 1) → (projectiveSpace K N).CoordinateRing :=
    fun j => MvPolynomial.rename (fun k => ⟨(0 : Fin 1), k⟩) (P j)
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => d,
    Q,
    (fun j => singleBlock_isHomogeneous (hP j)), ?_⟩
  intro y _
  have heq : (fun j => (projectiveSpace K N).eval (Q j) (fun _ => e y)) =
      (fun j => MvPolynomial.eval (e y).rep (P j)) := by
    ext j
    change MvPolynomial.eval _ (MvPolynomial.rename _ (P j)) = _
    rw [MvPolynomial.eval_rename]
    rfl
  obtain ⟨hne, hmk⟩ := hf y
  change ∃ h : (fun j : Fin (N' + 1) =>
      (projectiveSpace K N).eval (Q j) (fun _ => e y)) ≠ 0,
    Projectivization.mk K
      (fun j : Fin (N' + 1) => (projectiveSpace K N).eval (Q j) (fun _ => e y)) h = f y
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hne
  · simpa only [heq] using hmk

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

namespace PhilipponMultiplicity
theorem vanishingIdeal_multihomogeneous (K : Type*) [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) :=
  OperatorSupport.homogeneous_span M _ (fun _ h => h.1)
end PhilipponMultiplicity



set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The multigraded and homogeneous-generator formulations agree. -/
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

namespace PhilipponMultiplicity
theorem MultiProjectiveSpace.relevant_of_zeroLocus_nonempty {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (hne : (M.zeroLocus I).Nonempty) :
    Hilbert.IsRelevant K M.factorCount M.ambientDimension I := by
  classical
  obtain ⟨x,hx⟩ := hne
  have hj (i : M.FactorIndex) : ∃ j, (x i).rep j ≠ 0 := by
    simpa only [ne_eq,funext_iff,Pi.zero_apply,not_forall] using
      (Projectivization.rep_nonzero (x i))
  choose j hj using hj
  let F : M.CoordinateRing := ∏ i, X ⟨i,j i⟩
  have hF : F ∈ Hilbert.irrelevantIdeal K M.factorCount M.ambientDimension := by
    apply Ideal.mem_iInf.mpr
    intro i
    apply Ideal.prod_mem _ (Finset.mem_univ i)
    exact Ideal.subset_span ⟨j i,rfl⟩
  intro hle
  have hz := hx F (hle hF)
  have hneF : M.eval F x ≠ 0 := by
    change MvPolynomial.eval (M.coordinate x) (∏ i, X ⟨i,j i⟩) ≠ 0
    simp only [map_prod,eval_X,MultiProjectiveSpace.coordinate]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hj i)
  exact hneF hz

end PhilipponMultiplicity


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [NontriviallyNormedField K]

/-- The constant parametrization supplies analytic charts without imposing
any extra hypothesis on the algebraic group. -/
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

end PhilipponMultiplicity
end


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

end PhilipponMultiplicity
end


set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_lift_eq_zero_of_mem_vanishingIdeal
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    {V : Set M.Point} {p : M.Point} (hp : p ∈ V)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal V) :
    MvPolynomial.eval v P = 0 := by
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
  have hideal : M.vanishingIdeal V ≤ RingHom.ker (MvPolynomial.eval v) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨⟨D, hD⟩, hz⟩
    change MvPolynomial.eval v Q = 0
    rw [hv', M.eval_block_scale Q D hD (M.coordinate p) (fun i => (a i : K)),
      show MvPolynomial.eval (M.coordinate p) Q = 0
      from hz p hp, mul_zero]
  exact hideal hP

/-- Containment forces every defining equation to have zero first derivative along A. -/
theorem analyticCodimension_eq_zero_of_carrier_subset
    {K : Type*} [NontriviallyNormedField K]
    {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hsub : A.carrier ⊆ H.carrier) : analyticCodimension A H.carrier = 0 := by
  have hker : A.tangentKernel H.carrier = ⊤ := by
    apply top_unique
    intro t _
    apply (Submodule.mem_iInf _).mpr
    intro P
    have hpull : A.pullback P.val 0 =ᶠ[𝓝 0] (fun _ => (0 : K)) := by
      filter_upwards [A.lift_represents 0] with z hz
      obtain ⟨hz, hlift⟩ := hz
      have hmem : A.map ⟨z, hz⟩ ∈ H.carrier :=
        hsub (AddSubgroup.subset_closure ⟨⟨z, hz⟩, rfl⟩)
      apply G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
        (Set.mem_image_of_mem G.embedding hmem) (A.lift 0 z) _ P.property
      intro i
      obtain ⟨h, he⟩ := hlift i
      exact ⟨h, by simpa only [zero_add] using he⟩
    change fderiv K (A.pullback P.val 0) 0 t = 0
    rw [hpull.fderiv_eq]
    simp
  unfold analyticCodimension
  rw [hker, finrank_top]
  simp [AnalyticSubgroup.ParameterSpace]

end PhilipponMultiplicity
end


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

theorem AlgebraicSubgroup.mem_of_homogeneous_equations
    {K : Type*} [Field K] {G : EmbeddedGroupProduct K}
    (H : AlgebraicSubgroup G) (x : G.Point)
    (hx : ∀ (P : G.CoordinateRing) (D : G.FactorIndex → ℕ),
      G.ambient.IsHomogeneous P D →
      (∀ y ∈ H.carrier, G.ambient.eval P (G.embedding y) = 0) →
      G.ambient.eval P (G.embedding x) = 0) : x ∈ H.carrier := by
  letI := G.ambient.zariskiTopology
  letI := G.zariskiTopology
  have hcl : @closure _ G.zariskiTopology H.carrier =
      G.embedding ⁻¹' G.ambient.zeroLocus (G.vanishingIdeal H.carrier) := by
    ext y
    rw [EmbeddedGroupProduct.zariskiTopology, closure_induced,
      ← G.ambient.zeroLocus_vanishingIdeal_eq_closure]
    rfl
  have hclosed : closure H.carrier = H.carrier := H.isClosed.closure_eq
  rw [← hclosed, hcl]
  intro P hP
  have hideal : G.vanishingIdeal H.carrier ≤
      RingHom.ker (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨⟨D, hD⟩, hQ⟩
    exact hx Q D hD (fun y hy => hQ _ ⟨y, hy, rfl⟩)
  exact hideal hP

end PhilipponMultiplicity
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity
universe u

variable (K : Type u) [Field K]

private theorem homogeneous_X (M : MultiProjectiveSpace K) (v : M.Variable) :
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

private theorem homogeneous_add (M : MultiProjectiveSpace K)
    {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

def additiveCarrier : Set (Projectivization K (Fin 2 → K)) := {p | p.rep 0 ≠ 0}

def additivePoint (z : K) : Projectivization K (Fin 2 → K) :=
  Projectivization.mk K ![1, z] (by intro h; have := congrFun h 0; simpa using this)

theorem additivePoint_mem (z : K) : additivePoint K z ∈ additiveCarrier K := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K ![1, z]
    (by intro h; have := congrFun h 0; simpa using this)
  change (Projectivization.mk K ![1, z] _).rep 0 ≠ 0
  rw [← hc]
  simpa [Units.smul_def] using c.ne_zero

def additiveCoordinateEquiv : additiveCarrier K ≃ K where
  toFun p := p.val.rep 1 / p.val.rep 0
  invFun z := ⟨additivePoint K z, additivePoint_mem K z⟩
  left_inv p := by
    apply Subtype.ext
    apply Eq.trans ?_ p.val.mk_rep
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨(p.val.rep 0)⁻¹, ?_⟩
    have hp0 : p.val.rep 0 ≠ 0 := p.property
    ext j
    fin_cases j
    · simp [hp0]
    · simp [div_eq_mul_inv, mul_comm]
  right_inv z := by
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K ![1, z]
      (by intro h; have := congrFun h 0; simpa using this)
    change (Projectivization.mk K ![1, z] _).rep 1 /
      (Projectivization.mk K ![1, z] _).rep 0 = z
    rw [← hc]
    simp [Units.smul_def, c.ne_zero]

def additiveCarrierGroup : AddCommGroup (additiveCarrier K) :=
  (additiveCoordinateEquiv K).addCommGroup

private theorem additivePoint_eq_mk {v : Fin 2 → K} (hv : v 0 ≠ 0) :
    additivePoint K (v 1 / v 0) =
      Projectivization.mk K v (by intro h; exact hv (congrFun h 0)) := by
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨(v 0)⁻¹, ?_⟩
  ext j
  fin_cases j <;> simp [hv, div_eq_mul_inv, mul_comm]

theorem additiveCarrier_negation_regular :
    letI := additiveCarrierGroup K
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K 1) (projectiveSpace K 1)
      (fun x : additiveCarrier K => fun _ => x.val)
      (fun x : additiveCarrier K => fun _ => (-x).val) := by
  letI := additiveCarrierGroup K
  let P : Fin 2 → MvPolynomial (Fin 2) K := ![MvPolynomial.X 0, -MvPolynomial.X 1]
  apply projective_regular_of_homogeneous _ _ P (d := 1)
  · intro j
    fin_cases j
    · exact MvPolynomial.isHomogeneous_X K 0
    · exact (MvPolynomial.isHomogeneous_X K 1).neg
  · intro x
    have hx : x.val.rep 0 ≠ 0 := x.property
    have hn : ![x.val.rep 0, -x.val.rep 1] ≠ 0 := by
      intro h
      exact hx (by simpa using congrFun h 0)
    have he : (fun j => MvPolynomial.eval x.val.rep (P j)) =
        ![x.val.rep 0, -x.val.rep 1] := by
      ext j
      fin_cases j <;> simp [P]
    refine ⟨by simpa only [he] using hn, ?_⟩
    change Projectivization.mk K _ _ = additivePoint K (-(x.val.rep 1 / x.val.rep 0))
    have hpoint := additivePoint_eq_mk K (v := ![x.val.rep 0, -x.val.rep 1]) hx
    simpa only [he, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      neg_div] using hpoint.symm


theorem additiveCarrier_locallyClosed :
    @IsLocallyClosed _
      (TopologicalSpace.induced (fun p : Projectivization K (Fin 2 → K) =>
          (fun _ => p : (projectiveSpace K 1).Point))
        (projectiveSpace K 1).zariskiTopology) (additiveCarrier K) := by
  letI := TopologicalSpace.induced
    (fun p : Projectivization K (Fin 2 → K) => (fun _ => p : (projectiveSpace K 1).Point))
      (projectiveSpace K 1).zariskiTopology
  exact (projective_isOpen_coordinate (K := K) (0 : Fin 2)).isLocallyClosed

private theorem homogeneous_bilinear (a b : Fin 2) :
    (projectiveSquare K 1).IsHomogeneous
      (MvPolynomial.X ⟨(0 : Fin 2), a⟩ * MvPolynomial.X ⟨(1 : Fin 2), b⟩) (fun _ => 1) := by
  have h := (homogeneous_X K (projectiveSquare K 1) ⟨(0 : Fin 2), a⟩).mul (projectiveSquare K 1)
    (homogeneous_X K (projectiveSquare K 1) ⟨(1 : Fin 2), b⟩)
  convert h using 1
  funext i
  fin_cases i <;> rfl

theorem additiveCarrier_addition_regular :
    letI := additiveCarrierGroup K
    MultiProjectiveSpace.IsRegularAlong (projectiveSquare K 1) (projectiveSpace K 1)
      (fun xy : additiveCarrier K × additiveCarrier K =>
        fun i => if i.val = 0 then xy.1.val else xy.2.val)
      (fun xy : additiveCarrier K × additiveCarrier K => fun _ => (xy.1 + xy.2).val) := by
  letI := additiveCarrierGroup K
  letI := (projectiveSquare K 1).zariskiTopology
  let P : Fin 2 → (projectiveSquare K 1).CoordinateRing :=
    ![MvPolynomial.X ⟨(0 : Fin 2), 0⟩ * MvPolynomial.X ⟨(1 : Fin 2), 0⟩,
      MvPolynomial.X ⟨(0 : Fin 2), 1⟩ * MvPolynomial.X ⟨(1 : Fin 2), 0⟩ +
        MvPolynomial.X ⟨(0 : Fin 2), 0⟩ * MvPolynomial.X ⟨(1 : Fin 2), 1⟩]
  intro x b
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 1, P, ?_, ?_⟩
  · intro j
    change (projectiveSquare K 1).IsHomogeneous (P j) (fun _ => 1)
    fin_cases j
    · exact homogeneous_bilinear K 0 0
    · exact homogeneous_add K _ (homogeneous_bilinear K 1 0) (homogeneous_bilinear K 0 1)
  · intro y _
    let v : Fin 2 → K :=
      ![y.1.val.rep 0 * y.2.val.rep 0,
        y.1.val.rep 1 * y.2.val.rep 0 + y.1.val.rep 0 * y.2.val.rep 1]
    have hv : v 0 ≠ 0 := mul_ne_zero y.1.property y.2.property
    have he : (fun j : Fin 2 => (projectiveSquare K 1).eval (P j)
        (fun i => if i.val = 0 then y.1.val else y.2.val)) = v := by
      ext j
      fin_cases j <;>
        simp [P, v, MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate, projectiveSquare]
    change ∃ h : (fun j : Fin 2 => (projectiveSquare K 1).eval (P j)
        (fun i => if i.val = 0 then y.1.val else y.2.val)) ≠ 0,
      Projectivization.mk K _ h = (y.1 + y.2).val
    refine ⟨by rw [he]; intro h; exact hv (congrFun h 0), ?_⟩
    change Projectivization.mk K _ _ =
      additivePoint K (y.1.val.rep 1 / y.1.val.rep 0 + y.2.val.rep 1 / y.2.val.rep 0)
    have hs : v 1 / v 0 =
        y.1.val.rep 1 / y.1.val.rep 0 + y.2.val.rep 1 / y.2.val.rep 0 := by
      dsimp [v]
      exact (div_add_div _ _ y.1.property y.2.property).symm
    simpa only [he, hs] using (additivePoint_eq_mk K hv).symm

/-- The additive group in its standard open projective-line chart, with
regular addition and negation proved by homogeneous coordinate formulae. -/
def additiveEmbeddedGroup : EmbeddedCommutativeGroup K where
  ambientDimension := 1
  carrier := additiveCarrier K
  group := additiveCarrierGroup K
  locallyClosed := additiveCarrier_locallyClosed K
  addition_regular := additiveCarrier_addition_regular K
  negation_regular := additiveCarrier_negation_regular K

def additiveEmbeddedGroupEquiv : (additiveEmbeddedGroup K).Point ≃+ K :=
  letI := additiveCarrierGroup K
  (additiveCoordinateEquiv K).addEquiv

/-- Existence of the standard additive group law, with both operations regular
in the projective embedding and with the ordinary affine coordinate. -/
theorem additive_projective_realization :
    let U : Set (Projectivization K (Fin 2 → K)) := {p | p.rep 0 ≠ 0}
    @IsLocallyClosed _
      (TopologicalSpace.induced (fun p : Projectivization K (Fin 2 → K) =>
        (fun _ => p : (projectiveSpace K 1).Point)) (projectiveSpace K 1).zariskiTopology) U ∧
    ∃ group : AddCommGroup U,
      letI := group
      MultiProjectiveSpace.IsRegularAlong (projectiveSquare K 1) (projectiveSpace K 1)
        (fun xy : U × U => fun i => if i.val = 0 then xy.1.val else xy.2.val)
        (fun xy : U × U => fun _ => (xy.1 + xy.2).val) ∧
      MultiProjectiveSpace.IsRegularAlong (projectiveSpace K 1) (projectiveSpace K 1)
        (fun x : U => fun _ => x.val) (fun x : U => fun _ => (-x).val) ∧
      ∃ e : U ≃+ K, ∀ p : U, e p = p.val.rep 1 / p.val.rep 0 := by
  refine ⟨additiveCarrier_locallyClosed K, additiveCarrierGroup K, ?_⟩
  letI := additiveCarrierGroup K
  exact ⟨additiveCarrier_addition_regular K, additiveCarrier_negation_regular K,
    additiveEmbeddedGroupEquiv K, fun _ => rfl⟩

end PhilipponMultiplicity

end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace PhilipponMultiplicity.Hilbert

private abbrev BinaryVariable := (i : Fin 1) × Fin ((fun _ : Fin 1 => 1) i + 1)

private theorem binary_weight (m : BinaryVariable →₀ ℕ) :
    Finsupp.weight (blockWeight 1 (fun _ => 1)) m =
      fun _ => m ⟨0, 0⟩ + m ⟨0, 1⟩ := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [Finsupp.weight_eq_sum, blockWeight, Fintype.sum_sigma, Fin.sum_univ_two]

private def binaryMonomialEquiv (n : ℕ) :
    {m : BinaryVariable →₀ ℕ //
      Finsupp.weight (blockWeight 1 (fun _ => 1)) m = fun _ => n} ≃ Fin (n + 1) where
  toFun m := ⟨m.val ⟨0, 1⟩, by
    have h := congrFun m.property 0
    rw [binary_weight] at h
    dsimp at h
    omega⟩
  invFun k := ⟨Finsupp.equivFunOnFinite.symm (fun j => if j.2 = 0 then n - k.val else k.val), by
    rw [binary_weight]
    ext i
    simp
    omega⟩
  left_inv m := by
    apply Subtype.ext
    ext j
    rcases j with ⟨i, j⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have h := congrFun m.property 0
    rw [binary_weight] at h
    dsimp at h
    fin_cases j <;> simp <;> omega
  right_inv k := by
    apply Fin.ext
    simp

/-- Binary homogeneous forms of degree `n` have exactly `n+1` independent
coefficients, for the actual one-block degree-piece definition. -/
theorem binary_degreePiece_finrank (K : Type*) [Field K] (n : ℕ) :
    Module.finrank K (degreePiece K 1 (fun _ => 1) (fun _ => n)) = n + 1 := by
  classical
  unfold degreePiece
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  let e := binaryMonomialEquiv n
  rw [(AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K) _).finrank_eq]
  have h := (Finsupp.domLCongr e : (_ →₀ K) ≃ₗ[K] (Fin (n + 1) →₀ K)).finrank_eq
  exact h.trans (by simp)

/-- The quotient by the zero ideal has the same homogeneous-piece dimension. -/
theorem binary_hilbertFunction_bot (K : Type*) [Field K] (n : ℕ) :
    hilbertFunction K 1 (fun _ => 1) ⊥ (fun _ => n) = n + 1 := by
  let e := (AlgEquiv.quotientBot K (CoordinateRing K 1 (fun _ => 1))).symm.toLinearEquiv
  have h := e.finrank_map_eq (degreePiece K 1 (fun _ => 1) (fun _ => n))
  change Module.finrank K (quotientPiece K 1 (fun _ => 1) ⊥ (fun _ => n)) = _
  exact h.trans (binary_degreePiece_finrank K n)

theorem binary_hilbertPolynomial_bot (K : Type*) [Field K] :
    hilbertPolynomial K 1 (fun _ => 1) ⊥ = MvPolynomial.X 0 + 1 := by
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, ?_⟩
  intro d _
  have hd : d = fun _ => d 0 := by ext i; congr 1; exact Subsingleton.elim _ _
  rw [hd, binary_hilbertFunction_bot]
  simp

end PhilipponMultiplicity.Hilbert

end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace PhilipponMultiplicity

private theorem single_block_eval_scale {K : Type*} [Field K] {n : ℕ}
    {P : (projectiveSpace K n).CoordinateRing} {D : Fin 1 → ℕ}
    (hP : (projectiveSpace K n).IsHomogeneous P D)
    (X : (projectiveSpace K n).Variable → K) (c : K) :
    MvPolynomial.eval (fun i => c * X i) P = c ^ D 0 * MvPolynomial.eval X P := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hd : (∑ i, m i) = D 0 := by
    rw [Fintype.sum_sigma]
    change (∑ i : Fin 1, ∑ j : Fin (n + 1), m ⟨i, j⟩) = D 0
    rw [Fin.sum_univ_one]
    exact hP m hm (0 : Fin 1)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem additiveCarrier_vanishingIdeal_eq_bot (K : Type*) [Field K] [Infinite K] :
    (projectiveSpace K 1).vanishingIdeal
      ((fun p => fun _ => p) '' additiveCarrier K) = ⊥ := by
  classical
  apply le_antisymm ?_ bot_le
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D, hP⟩, hzero⟩
  change P = 0
  apply MvPolynomial.funext_set (fun _ => ({0} : Set K)ᶜ)
    (fun _ => (Set.finite_singleton (0 : K)).infinite_compl)
  intro X hX
  have h0 : X ⟨(0 : Fin 1), 0⟩ ≠ 0 := hX _ (Set.mem_univ _)
  let V : Fin 2 → K := fun j => X ⟨(0 : Fin 1), j⟩
  have hV : V ≠ 0 := by intro hz; exact h0 (congrFun hz 0)
  let p := Projectivization.mk K V hV
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K V hV
  have hp : p ∈ additiveCarrier K := by
    change p.rep 0 ≠ 0
    dsimp only [p]
    rw [← hc]
    exact mul_ne_zero c.ne_zero h0
  have hz := hzero (fun _ => p) ⟨p, hp, rfl⟩
  have hcoords : (projectiveSpace K 1).coordinate (fun _ => p) =
      fun i => c.val * X i := by
    funext i
    rcases i with ⟨i, j⟩
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change p.rep j = _
    dsimp only [p]
    rw [← hc]
    rfl
  change MvPolynomial.eval _ P = 0 at hz
  rw [hcoords, single_block_eval_scale hP] at hz
  have heval := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ c.ne_zero)
  simpa only [map_zero] using heval

theorem additiveEmbeddedGroup_dimension (K : Type*) [Field K] [Infinite K] :
    (additiveEmbeddedGroup K).dimension = 1 := by
  change (Hilbert.hilbertPolynomial K 1 (fun _ => 1)
    ((projectiveSpace K 1).vanishingIdeal ((fun p => fun _ => p) '' additiveCarrier K))).totalDegree = 1
  rw [additiveCarrier_vanishingIdeal_eq_bot, Hilbert.binary_hilbertPolynomial_bot]
  rw [MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt (by simp)]
  simp

/-- The actual projective-closure Hilbert polynomial of the standard affine line. -/
theorem additive_projective_hilbert_polynomial (K : Type*) [Field K] [Infinite K] :
    Hilbert.hilbertPolynomial K 1 (fun _ => 1)
      ((projectiveSpace K 1).vanishingIdeal
        ((fun p : Projectivization K (Fin 2 → K) => fun _ : Fin 1 => p) ''
          {p : Projectivization K (Fin 2 → K) | p.rep 0 ≠ 0})) =
      MvPolynomial.X 0 + 1 := by
  exact (congrArg (Hilbert.hilbertPolynomial K 1 (fun _ => 1))
    (additiveCarrier_vanishingIdeal_eq_bot K)).trans (Hilbert.binary_hilbertPolynomial_bot K)

end PhilipponMultiplicity

end


set_option autoImplicit false
noncomputable section
open scoped Topology
namespace PhilipponMultiplicity

/-- Every neighborhood ball generates a connected normed additive group.
Here closure means algebraic subgroup generation, not topological closure. -/
theorem additive_closure_ball_eq_top {E : Type*} [SeminormedAddCommGroup E]
    [PreconnectedSpace E] (r : ℝ) (hr : 0 < r) :
    AddSubgroup.closure (Metric.ball (0 : E) r) = ⊤ := by
  let H := AddSubgroup.closure (Metric.ball (0 : E) r)
  have hopen : IsOpen (H : Set E) := H.isOpen_of_mem_nhds
    (Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) hr) AddSubgroup.subset_closure)
  have huniv : (H : Set E) = Set.univ :=
    IsClopen.eq_univ ⟨H.isClosed_of_isOpen hopen, hopen⟩ ⟨0, H.zero_mem⟩
  exact SetLike.coe_injective huniv

/-- If an analytic subgroup's local map restricts a global additive curve,
its generated carrier is exactly the range of that global curve. -/
theorem AnalyticSubgroup.carrier_eq_range_of_global_curve
    {G : EmbeddedGroupProduct ℂ} (A : AnalyticSubgroup G)
    (f : A.ParameterSpace →+ G.Point) (hf : ∀ z : A.domain, A.map z = f z.val) :
    A.carrier = Set.range f := by
  have hlocal : Set.range A.map = f '' A.domain := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, z.property, (hf z).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, hf ⟨z, hz⟩⟩
  unfold AnalyticSubgroup.carrier
  rw [hlocal, A.domain_eq_ball, ← AddMonoidHom.map_closure,
    additive_closure_ball_eq_top A.radius A.radius_pos]
  simp

end PhilipponMultiplicity

end


set_option autoImplicit false
noncomputable section
open scoped Topology
namespace PhilipponMultiplicity

/-- An injective differential of one equation through the identity forces the
analytic tangent kernel to be zero. -/
theorem AnalyticSubgroup.tangentKernel_eq_bot_of_linear_pullback
    {G : EmbeddedGroupProduct ℂ} (A : AnalyticSubgroup G)
    (ev : A.ParameterSpace ≃L[ℂ] ℂ) (P : G.CoordinateRing)
    (hP : P ∈ G.vanishingIdeal {0}) (hf : A.pullback P 0 = ev) :
    A.tangentKernel {0} = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro t ht
  change t = 0
  change t ∈ ⨅ Q : {Q : G.CoordinateRing // Q ∈ G.vanishingIdeal {0}},
    LinearMap.ker (fderiv ℂ (A.pullback Q.val 0) 0).toLinearMap at ht
  have hp := ((Submodule.mem_iInf _).mp ht) ⟨P, hP⟩
  change (fderiv ℂ (A.pullback P 0) 0) t = 0 at hp
  rw [hf] at hp
  have hd : fderiv ℂ ev 0 = ev.toContinuousLinearMap := ev.hasFDerivAt.fderiv
  rw [hd] at hp
  exact ev.injective (hp.trans ev.map_zero.symm)

/-- A finite family of analytic germs has a common positive real power-series ball. -/
theorem finite_analytic_common_ball {ι : Type*} [Fintype ι]
    (f : ι → (Fin 1 → ℂ) → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, ∃ p : FormalMultilinearSeries ℂ (Fin 1 → ℂ) ℂ,
      HasFPowerSeriesOnBall (f i) p 0 (ENNReal.ofReal r) := by
  choose p hp using hf
  obtain ⟨r, hr⟩ := HasFPowerSeriesAt.pi hp
  obtain ⟨s, hs, hsr⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := 1) (b := r) (by simp) hr.r_pos.ne'
  have hsr' : (s : ENNReal) ≤ r := by simpa using hsr.le
  refine ⟨s, hs, fun i => ⟨p i, ?_⟩⟩
  exact (hasFPowerSeriesOnBall_pi_iff (by simpa using hs)).mp
    (hr.mono (by simpa using hs) (by simpa using hsr')) i

variable {G : EmbeddedGroupProduct ℂ}
    (curve : ℂ →+ G.Point)
    (lift : G.Point → (Fin 1 → ℂ) → G.ambient.Variable → ℂ)
    (ha : ∀ g v, AnalyticAt ℂ (fun z => lift g z v) 0)
    (hr : ∀ g t i, ∃ h : (fun j => lift g t ⟨i, j⟩) ≠ 0,
      Projectivization.mk ℂ (fun j => lift g t ⟨i, j⟩) h =
        G.embedding (g + curve (t 0)) i)

/-- Restrict a global additive curve with analytic translated lifts to a genuine
common power-series ball. -/
def AnalyticSubgroup.ofGlobalCurve : AnalyticSubgroup G :=
  let hb := finite_analytic_common_ball (fun v t => lift 0 t v) (ha 0)
  let r := Classical.choose hb
  let h := Classical.choose_spec hb
  { parameterDimension := 1
    parameterDimension_pos := by decide
    radius := r
    radius_pos := h.1
    domain := Metric.ball 0 r
    domain_eq_ball := rfl
    domain_open := Metric.isOpen_ball
    zero_mem := Metric.mem_ball_self h.1
    map := fun t => curve (t.val 0)
    map_zero := curve.map_zero
    map_add := fun x y _ => curve.map_add (x.val 0) (y.val 0)
    lift := lift
    lift_analytic := ha
    base_series := h.2
    base_represents := fun t i => by simpa using hr 0 t.val i
    lift_represents := fun g => by
      filter_upwards [Metric.ball_mem_nhds (0 : Fin 1 → ℂ) h.1] with t ht
      exact ⟨ht, hr g t⟩ }

theorem AnalyticSubgroup.ofGlobalCurve_carrier :
    (AnalyticSubgroup.ofGlobalCurve curve lift ha hr).carrier = Set.range curve := by
  let ev : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)
  rw [AnalyticSubgroup.carrier_eq_range_of_global_curve _
    (curve.comp ev.toLinearEquiv.toAddEquiv.toAddMonoidHom) (fun _ => rfl)]
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨ev t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨ev.symm t, congrArg curve (ev.apply_symm_apply t)⟩

end PhilipponMultiplicity
end


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
namespace MultiProjectiveSpace
universe u
variable {K : Type u} [Field K] (M : MultiProjectiveSpace K)

theorem zariski_t1 : @T1Space M.Point M.zariskiTopology := by
  letI := M.zariskiTopology
  constructor
  intro x
  have heq : M.zeroLocus (M.vanishingIdeal {x}) = {x} := by
    ext y
    constructor
    · intro hy
      apply Set.mem_singleton_iff.mpr
      apply M.point_eq_of_homogeneous_implication
      intro P D hP hx
      exact hy P (Ideal.subset_span ⟨⟨D,hP⟩, by simpa using hx⟩)
    · intro hy
      have hyx := Set.mem_singleton_iff.mp hy
      subst y
      exact fun P hP => M.eval_eq_zero_of_mem_vanishingIdeal hP (Set.mem_singleton x)
  rw [← heq]
  exact M.isClosed_zeroLocus_vanishingIdeal {x}

theorem isRegularAlong_of_finite {X : Type u} [Finite X]
    (Q : MultiProjectiveSpace K) (e : X → M.Point) (he : Function.Injective e)
    (f : X → Q.Point) : M.IsRegularAlong Q e f := by
  classical
  letI := M.zariskiTopology
  letI : T1Space M.Point := M.zariski_t1
  intro x b
  let U := (e '' ({x}ᶜ : Set X))ᶜ
  refine ⟨U, (Set.toFinite _).isClosed.isOpen_compl, ?_, 0,
    fun j => C ((f x b).rep j), fun j => M.isHomogeneous_C _, ?_⟩
  · rintro ⟨y,hy,hxy⟩
    exact hy (Set.mem_singleton_iff.mpr (he hxy))
  · intro y hy
    have hyx : y = x := by
      by_contra hn
      exact hy ⟨y,hn,rfl⟩
    subst y
    simpa only [eval,eval_C] using
      (show ∃ h : (f x b).rep ≠ 0, Projectivization.mk K (f x b).rep h = f x b
        from ⟨(f x b).rep_nonzero,(f x b).mk_rep⟩)

theorem vanishingIdeal_range_eq_iInf {B : Type*} (p : B → M.Point) :
    M.vanishingIdeal (Set.range p) = ⨅ b, M.vanishingIdeal {p b} := by
  apply le_antisymm
  · exact le_iInf (fun b => M.vanishingIdeal_antitone
      (Set.singleton_subset_iff.mpr (Set.mem_range_self b)))
  · let J := ⨅ b, M.vanishingIdeal {p b}
    have hJ : IsMultihomogeneousIdeal M J := by
      intro P hP D
      exact Ideal.mem_iInf.mpr (fun b => vanishingIdeal_multihomogeneous K M _
        P (Ideal.mem_iInf.mp hP b) D)
    change J ≤ _
    rw [M.homogeneousIdeal_eq_span J hJ]
    apply Ideal.span_le.mpr
    rintro P ⟨hP,D,hD⟩
    apply Ideal.subset_span
    refine ⟨⟨D,hD⟩,?_⟩
    rintro _ ⟨b,rfl⟩
    exact M.eval_eq_zero_of_mem_vanishingIdeal (Ideal.mem_iInf.mp hP b) (Set.mem_singleton _)

theorem finite_range_dimension_zero {B : Type*} [Finite B] [Nonempty B]
    (p : B → M.Point) :
    SectionThree.idealDimension M (M.vanishingIdeal (Set.range p)) = 0 := by
  classical
  letI := Fintype.ofFinite B
  let I := M.vanishingIdeal (Set.range p)
  have hI : IsMultihomogeneousIdeal M I := vanishingIdeal_multihomogeneous K M _
  have hnontriv : SectionThree.IsNontrivialIdeal M I := by
    apply M.relevant_of_zeroLocus_nonempty I.radical
    obtain ⟨b⟩ := ‹Nonempty B›
    refine ⟨p b,?_⟩
    rintro P ⟨n,hn⟩
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal hn (Set.mem_range_self b)
    exact eq_zero_of_pow_eq_zero (by simpa only [eval,map_pow] using hz)
  obtain ⟨q,hq,_,hdim⟩ := Hilbert.exists_relevant_minimalPrime_dimension_eq M I hI hnontriv
  have hle : (Finset.univ : Finset B).inf (fun b => M.vanishingIdeal {p b}) ≤ q := by
    simpa only [Finset.inf_univ_eq_iInf, ← M.vanishingIdeal_range_eq_iInf p] using hq.le
  obtain ⟨b,_,hb⟩ := hq.isPrime.inf_le'.mp hle
  have hdimle := Hilbert.idealDimension_antitone M _ q
    (vanishingIdeal_multihomogeneous K M _) (Hilbert.minimalPrime_homogeneous M I q hI hq) hb
  simp only [SectionThree.idealDimension, M.hilbertPolynomial_singleton, totalDegree_one] at hdimle
  rw [← hdim]
  exact Nat.eq_zero_of_le_zero hdimle

end MultiProjectiveSpace

namespace FiniteEmbedded
variable {K : Type*} [Field K] {B : Type*} [AddCommGroup B] [Finite B]
  {n : ℕ} (p : B → Projectivization K (Fin (n+1) → K)) (hp : Function.Injective p)

/-- Every finite commutative group embedded as distinct projective points has
regular group operations for the induced Zariski topology. -/
def group : EmbeddedCommutativeGroup K := by
  let e := Equiv.ofInjective p hp
  letI : AddCommGroup (Set.range p) := e.symm.addCommGroup
  letI : Finite (Set.range p) := Finite.of_equiv B e
  letI : TopologicalSpace (projectiveSpace K n).Point := (projectiveSpace K n).zariskiTopology
  letI : T1Space (projectiveSpace K n).Point := (projectiveSpace K n).zariski_t1
  let f : Projectivization K (Fin (n+1) → K) → (projectiveSpace K n).Point := fun x _ => x
  letI : TopologicalSpace (Projectivization K (Fin (n+1) → K)) :=
    TopologicalSpace.induced f (projectiveSpace K n).zariskiTopology
  letI : T1Space (Projectivization K (Fin (n+1) → K)) :=
    @t1Space_of_injective_of_continuous _ (projectiveSpace K n).Point _
      (projectiveSpace K n).zariskiTopology f
      (fun x y h => congrFun h (0 : Fin 1))
      (@continuous_induced_dom _ _ f (projectiveSpace K n).zariskiTopology)
      (projectiveSpace K n).zariski_t1
  refine {
    ambientDimension := n
    carrier := Set.range p
    group := inferInstance
    locallyClosed := (Set.finite_range p).isClosed.isLocallyClosed
    addition_regular := ?_
    negation_regular := ?_ }
  · apply (projectiveSquare K n).isRegularAlong_of_finite
    intro x y h
    apply Prod.ext
    · exact Subtype.ext (by simpa [projectiveSquare] using congrFun h (0 : Fin 2))
    · exact Subtype.ext (by simpa [projectiveSquare] using congrFun h (1 : Fin 2))
  · apply (projectiveSpace K n).isRegularAlong_of_finite
    intro x y h
    exact Subtype.ext (congrFun h (0 : Fin 1))

def equiv : (group p hp).Point ≃+ B := (Equiv.ofInjective p hp).symm.addEquiv

@[simp] theorem equiv_symm_val (b : B) : ((equiv p hp).symm b).val = p b := rfl

theorem dimension_zero : (group p hp).dimension = 0 := by
  change SectionThree.idealDimension (projectiveSpace K n)
    ((projectiveSpace K n).vanishingIdeal ((fun x => fun _ => x) '' Set.range p)) = 0
  rw [← Set.range_comp]
  exact (projectiveSpace K n).finite_range_dimension_zero _

end FiniteEmbedded
end PhilipponMultiplicity
end


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SourceBoundary

variable (m : ℕ) [NeZero m]

def cyclicPoint (b : ZMod m) : Projectivization ℂ (Fin 2 → ℂ) :=
  additivePoint ℂ (b.val : ℂ)

theorem cyclicPoint_injective : Function.Injective (cyclicPoint m) := by
  intro a b h
  have h' : (a.val : ℂ) = (b.val : ℂ) := by
    have hh : (additiveCoordinateEquiv ℂ).symm (a.val : ℂ) =
        (additiveCoordinateEquiv ℂ).symm (b.val : ℂ) := Subtype.ext h
    exact (additiveCoordinateEquiv ℂ).symm.injective hh
  exact ZMod.val_injective m (Nat.cast_injective h')

def cyclicFactor : EmbeddedCommutativeGroup ℂ :=
  FiniteEmbedded.group (cyclicPoint m) (cyclicPoint_injective m)

def cyclicGroup : EmbeddedGroupProduct ℂ := singleGroupProduct (cyclicFactor m)

def cyclicEquiv : (cyclicGroup m).Point ≃+ ZMod m where
  toFun x := FiniteEmbedded.equiv (cyclicPoint m) (cyclicPoint_injective m) (x (0 : Fin 1))
  invFun b := fun _ => (FiniteEmbedded.equiv (cyclicPoint m) (cyclicPoint_injective m)).symm b
  left_inv x := by
    funext i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (FiniteEmbedded.equiv (cyclicPoint m) (cyclicPoint_injective m)).symm_apply_apply _
  right_inv b := (FiniteEmbedded.equiv (cyclicPoint m) (cyclicPoint_injective m)).apply_symm_apply _
  map_add' x y := (FiniteEmbedded.equiv (cyclicPoint m) (cyclicPoint_injective m)).map_add _ _

@[simp] theorem cyclic_embedding (b : ZMod m) :
    (cyclicGroup m).embedding ((cyclicEquiv m).symm b) (0 : Fin 1) = cyclicPoint m b := rfl

theorem cyclic_dimension : (cyclicGroup m).dimension = 0 := by
  change (∑ _ : Fin 1, (cyclicFactor m).dimension) = 0
  rw [Fin.sum_univ_one]
  exact FiniteEmbedded.dimension_zero _ _

theorem trivial_carrier (G : EmbeddedGroupProduct ℂ) :
    (AnalyticSubgroup.trivial G).carrier = {0} := by
  change (AddSubgroup.closure (Set.range (fun _ : (AnalyticSubgroup.trivial G).domain =>
    (0 : G.Point))) : Set G.Point) = _
  haveI : Nonempty (AnalyticSubgroup.trivial G).domain :=
    ⟨⟨0,(AnalyticSubgroup.trivial G).zero_mem⟩⟩
  simp [AddSubgroup.closure_singleton_zero]

theorem trivial_order_top (G : EmbeddedGroupProduct ℂ) (P : G.CoordinateRing) (g : G.Point)
    (h : G.ambient.eval P (G.embedding g) = 0) :
    vanishingOrder (AnalyticSubgroup.trivial G) P g = ⊤ := by
  have heq : (AnalyticSubgroup.trivial G).pullback P g = 0 := by
    funext z
    exact h
  simp [vanishingOrder,heq]

theorem trivial_order_zero (G : EmbeddedGroupProduct ℂ) (P : G.CoordinateRing) (g : G.Point)
    (h : G.ambient.eval P (G.embedding g) ≠ 0) :
    vanishingOrder (AnalyticSubgroup.trivial G) P g = 0 := by
  apply le_antisymm ?_ bot_le
  apply sInf_le
  refine ⟨0,?_,rfl⟩
  intro hz
  have he := congrArg (fun L => L (fun i => Fin.elim0 i)) hz
  apply h
  simpa [iteratedFDeriv_zero_apply, AnalyticSubgroup.pullback, AnalyticSubgroup.trivial,
    MultiProjectiveSpace.eval] using he

def coordinatePolynomial : (cyclicGroup m).CoordinateRing := X ⟨(0 : Fin 1),1⟩

theorem coordinatePolynomial_homogeneous :
    IsMultihomogeneousOfDegree (cyclicGroup m) (coordinatePolynomial m) (fun _ => 1) := by
  change (cyclicGroup m).ambient.IsHomogeneous (X ⟨(0 : Fin 1),1⟩) (fun _ => 1)
  have h := (cyclicGroup m).ambient.isHomogeneous_X ⟨(0 : Fin 1),1⟩
  convert h using 1
  funext i
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp

theorem coordinatePolynomial_zero_iff (b : ZMod m) :
    (cyclicGroup m).ambient.eval (coordinatePolynomial m)
      ((cyclicGroup m).embedding ((cyclicEquiv m).symm b)) = 0 ↔ b = 0 := by
  simp only [coordinatePolynomial, MultiProjectiveSpace.eval, MvPolynomial.eval_X,
    MultiProjectiveSpace.coordinate, cyclic_embedding]
  change (cyclicPoint m b).rep 1 = 0 ↔ b = 0
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ ![1,(b.val : ℂ)]
    (by intro h; have := congrFun h 0; simpa using this)
  change (additivePoint ℂ (b.val : ℂ)).rep 1 = 0 ↔ _
  unfold additivePoint
  rw [← hc]
  simp only [Pi.smul_apply,Units.smul_def,smul_eq_mul,Matrix.cons_val_one,Matrix.head_cons,
    mul_eq_zero, c.ne_zero,false_or,Nat.cast_eq_zero]
  change (b.val : ℂ) = 0 ↔ b = 0
  rw [Nat.cast_eq_zero]
  exact ZMod.val_eq_zero b

theorem trivial_counterexample :
    ∃ (G : EmbeddedGroupProduct ℂ) (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G),
      Subsingleton G.Point ∧ G.dimension = 0 ∧ H.carrier = Set.univ ∧
      A.carrier = {0} ∧ analyticCodimension A H.carrier = 0 ∧
      hilbertDegreeForm G Set.univ (fun _ => 1) = 1 ∧
      hilbertDegreeForm G H.carrier (fun _ => 1) = 1 ∧
      (Nat.choose (0 + analyticCodimension A H.carrier)
          (analyticCodimension A H.carrier) : ℝ) *
        (cosetCount {0} H.carrier : ℝ) * hilbertDegreeForm G H.carrier (fun _ => 1) ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ (fun _ => 1) ∧
      ¬ ∃ P : G.CoordinateRing,
        (∀ h ∈ H.carrier, (1 : WithTop ℕ) ≤ vanishingOrder A P h) ∧
        (∃ x : G.Point, x ∉ zeroLocusOnGroup G P) := by
  let G := cyclicGroup 1
  let A := AnalyticSubgroup.trivial G
  let H : AlgebraicSubgroup G := ⟨⊤,@isClosed_univ _ G.zariskiTopology⟩
  haveI : Subsingleton G.Point := (cyclicEquiv 1).injective.subsingleton
  have hcarrier : H.carrier = Set.univ := rfl
  have hdim : G.dimension = 0 := cyclic_dimension 1
  have hcodim : analyticCodimension A H.carrier = 0 :=
    analyticCodimension_eq_zero_of_carrier_subset A H (by rw [hcarrier]; exact Set.subset_univ _)
  have hpoint : (Set.univ : Set G.Point) = {0} := Set.eq_singleton_iff_unique_mem.mpr
    ⟨Set.mem_univ _,fun x _ => Subsingleton.elim _ _⟩
  have hdegree : hilbertDegreeForm G Set.univ (fun _ => 1) = 1 := by
    rw [hpoint,hilbertDegreeForm_singleton]
  refine ⟨G,A,H,inferInstance,hdim,hcarrier,trivial_carrier G,hcodim,hdegree,?_,?_,?_⟩
  · simpa only [hcarrier] using hdegree
  · rw [hcodim,hdim,hcarrier,hdegree]
    simp [cosetCount]
  · rintro ⟨P,horder,x,hx⟩
    have ho := horder x (by rw [hcarrier]; trivial)
    rw [trivial_order_zero G P x hx] at ho
    norm_num at ho

theorem two_point_counterexample :
    ∃ (G : EmbeddedGroupProduct ℂ) (A : AnalyticSubgroup G)
        (sample : Finset G.Point) (P : G.CoordinateRing),
      G.dimension = 0 ∧ sample.card = 2 ∧ 0 ∈ sample ∧ A.carrier = {0} ∧
      P ≠ 0 ∧ IsMultihomogeneousOfDegree G P (fun _ => 1) ∧
      (∀ g ∈ sumset sample G.dimension, vanishingOrder A P g = ⊤) ∧
      ¬ ∃ H : AlgebraicSubgroup G,
        ∀ g ∈ sample, translate g H.carrier ⊆ zeroLocusOnGroup G P := by
  classical
  let G := cyclicGroup 2
  let A := AnalyticSubgroup.trivial G
  let x := (cyclicEquiv 2).symm 1
  let sample : Finset G.Point := {0,x}
  let P := coordinatePolynomial 2
  have hx : x ≠ 0 := by
    intro h
    have := congrArg (cyclicEquiv 2) h
    exact one_ne_zero (by simpa only [x,AddEquiv.apply_symm_apply,map_zero] using this)
  have hP0 : G.ambient.eval P (G.embedding 0) = 0 := by
    simpa only [map_zero] using (coordinatePolynomial_zero_iff 2 0).mpr rfl
  have hPx : G.ambient.eval P (G.embedding x) ≠ 0 := by
    exact fun h => one_ne_zero ((coordinatePolynomial_zero_iff 2 1).mp h)
  refine ⟨G,A,sample,P,cyclic_dimension 2,?_,by simp [sample],trivial_carrier G,
    X_ne_zero _,coordinatePolynomial_homogeneous 2,?_,?_⟩
  · simp [sample,hx,Ne.symm hx]
  · intro g hg
    rw [cyclic_dimension] at hg
    have hg0 : g = 0 := by simpa [sumset] using hg
    subst g
    exact trivial_order_top G P 0 hP0
  · rintro ⟨H,hH⟩
    have hz := hH x (by simp [sample]) (show x ∈ translate x H.carrier from
      ⟨0,H.toAddSubgroup.zero_mem,add_zero x⟩)
    exact hPx hz

end PhilipponMultiplicity.SourceBoundary
end


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SourceBoundary

def plane : EmbeddedGroupProduct ℂ := ⟨2,by decide,fun _ => additiveEmbeddedGroup ℂ⟩

def planeEquiv : plane.Point ≃+ (Fin 2 → ℂ) where
  toFun x i := additiveEmbeddedGroupEquiv ℂ (x i)
  invFun z i := (additiveEmbeddedGroupEquiv ℂ).symm (z i)
  left_inv x := by funext i; exact (additiveEmbeddedGroupEquiv ℂ).symm_apply_apply _
  right_inv z := by funext i; exact (additiveEmbeddedGroupEquiv ℂ).apply_symm_apply _
  map_add' x y := by funext i; exact (additiveEmbeddedGroupEquiv ℂ).map_add _ _

theorem plane_embedding (x : plane.Point) (i : Fin 2) :
    plane.embedding x i = additivePoint ℂ (planeEquiv x i) := by
  exact congrArg Subtype.val ((additiveEmbeddedGroupEquiv ℂ).symm_apply_apply (x i)).symm

def diagonalCurve : ℂ →+ plane.Point :=
  planeEquiv.symm.toAddMonoidHom.comp
    { toFun := fun z _ => z
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

@[simp] theorem planeEquiv_diagonalCurve (z : ℂ) (i : Fin 2) :
    planeEquiv (diagonalCurve z) i = z := by
  exact congrFun (planeEquiv.apply_symm_apply (fun _ => z)) i

def diagonalLift (g : plane.Point) (z : Fin 1 → ℂ) (v : plane.ambient.Variable) : ℂ :=
  if v.2 = 0 then 1 else planeEquiv g v.1 + z 0

theorem diagonalLift_analytic (g : plane.Point) (v : plane.ambient.Variable) :
    AnalyticAt ℂ (fun z => diagonalLift g z v) 0 := by
  unfold diagonalLift
  split_ifs
  · exact analyticAt_const
  · exact analyticAt_const.add
      ((ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt 0)

theorem diagonalLift_represents (g : plane.Point) (z : Fin 1 → ℂ) (i : plane.FactorIndex) :
    ∃ h : (fun j => diagonalLift g z ⟨i,j⟩) ≠ 0,
      Projectivization.mk ℂ (fun j => diagonalLift g z ⟨i,j⟩) h =
        plane.embedding (g+diagonalCurve (z 0)) i := by
  have heq : (fun j : Fin 2 => diagonalLift g z ⟨i,j⟩) = ![1,planeEquiv g i+z 0] := by
    funext j
    fin_cases j <;> simp [diagonalLift,plane]
  refine ⟨by intro h; have := congrFun h (0 : Fin 2); simpa [diagonalLift] using this,?_⟩
  rw [plane_embedding]
  simp only [map_add,Pi.add_apply,planeEquiv_diagonalCurve]
  change Projectivization.mk ℂ (fun j : Fin 2 => diagonalLift g z ⟨i,j⟩) _ =
    Projectivization.mk ℂ ![1,planeEquiv g i+z 0] _
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
  exact ⟨1, by simpa using heq.symm⟩

def diagonalAnalytic : AnalyticSubgroup plane :=
  AnalyticSubgroup.ofGlobalCurve diagonalCurve diagonalLift diagonalLift_analytic diagonalLift_represents

theorem diagonal_carrier : diagonalAnalytic.carrier = Set.range diagonalCurve :=
  AnalyticSubgroup.ofGlobalCurve_carrier _ _ _ _

def planePolynomial : plane.CoordinateRing := X ⟨(0 : Fin 2),(1 : Fin 2)⟩

def boundaryDegrees (i : plane.FactorIndex) : ℕ := if i.val = 0 then 1 else 0

theorem planePolynomial_homogeneous :
    IsMultihomogeneousOfDegree plane planePolynomial boundaryDegrees := by
  change plane.ambient.IsHomogeneous (X ⟨(0 : Fin 2),(1 : Fin 2)⟩) boundaryDegrees
  have h := plane.ambient.isHomogeneous_X ⟨(0 : Fin 2),(1 : Fin 2)⟩
  convert h using 1
  funext i
  change Fin 2 at i
  fin_cases i <;> simp [boundaryDegrees]

theorem planePolynomial_eval_zero_iff (x : plane.Point) :
    plane.ambient.eval planePolynomial (plane.embedding x) = 0 ↔ planeEquiv x 0 = 0 := by
  simp only [planePolynomial, MultiProjectiveSpace.eval, MvPolynomial.eval_X,
    MultiProjectiveSpace.coordinate]
  change (x (0 : Fin 2)).val.rep 1 = 0 ↔
    (x (0 : Fin 2)).val.rep 1 / (x (0 : Fin 2)).val.rep 0 = 0
  have hx : (x (0 : Fin 2)).val.rep 0 ≠ 0 := (x (0 : Fin 2)).property
  simp [div_eq_zero_iff,hx]

theorem planePolynomial_pullback :
    diagonalAnalytic.pullback planePolynomial 0 =
      (ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)) := by
  funext z
  change MvPolynomial.eval (diagonalLift 0 z) (X ⟨(0 : Fin 2),(1 : Fin 2)⟩) = _
  rw [MvPolynomial.eval_X]
  change diagonalLift 0 z ⟨(0 : Fin 2),(1 : Fin 2)⟩ = z (0 : Fin 1)
  simp [diagonalLift,plane]

theorem diagonal_dimension : diagonalAnalytic.dimension = 1 := by
  have hmem : planePolynomial ∈ plane.vanishingIdeal {0} := by
    apply Ideal.subset_span
    refine ⟨⟨boundaryDegrees,planePolynomial_homogeneous⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    rw [Set.mem_singleton_iff.mp hx]
    exact (planePolynomial_eval_zero_iff 0).mpr (by simp)
  have hker := diagonalAnalytic.tangentKernel_eq_bot_of_linear_pullback
    (ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)) planePolynomial hmem planePolynomial_pullback
  rw [AnalyticSubgroup.dimension,hker]
  simp only [finrank_bot,Nat.sub_zero]
  rfl

theorem planePolynomial_order : vanishingOrder diagonalAnalytic planePolynomial 0 = 1 := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨1,?_,rfl⟩
    intro hz
    have h := congrArg (fun L => L (fun _ => fun _ => (1 : ℂ))) hz
    rw [planePolynomial_pullback] at h
    let ev := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)
    have hd : fderiv ℂ ev 0 = ev.toContinuousLinearMap := ev.hasFDerivAt.fderiv
    change (iteratedFDeriv ℂ 1 ev 0) (fun _ => fun _ => (1 : ℂ)) = 0 at h
    rw [iteratedFDeriv_one_apply,hd] at h
    exact one_ne_zero h
  · apply le_sInf
    rintro _ ⟨n,hn,rfl⟩
    have hn0 : n ≠ 0 := by
      intro h
      subst n
      apply hn
      rw [planePolynomial_pullback]
      ext v
      simp
    change (↑(1 : ℕ) : WithTop ℕ) ≤ ↑n
    exact WithTop.coe_le_coe.mpr (Nat.one_le_iff_ne_zero.mpr hn0)

theorem plane_no_translate :
    ¬ ∃ g : plane.Point, translate g diagonalAnalytic.carrier ⊆ zeroLocusOnGroup plane planePolynomial := by
  rintro ⟨g,hg⟩
  let z : ℂ := 1-planeEquiv g 0
  have hm : diagonalCurve z ∈ diagonalAnalytic.carrier := by
    rw [diagonal_carrier]
    exact Set.mem_range_self z
  have hz := (planePolynomial_eval_zero_iff _).mp (hg ⟨diagonalCurve z,hm,rfl⟩)
  simp only [map_add,Pi.add_apply,planeEquiv_diagonalCurve] at hz
  dsimp [z] at hz
  have h : (1 : ℂ) = 0 := by linear_combination hz
  exact one_ne_zero h

theorem plane_vanishingIdeal_univ : plane.vanishingIdeal Set.univ = ⊥ := by
  classical
  apply le_antisymm ?_ bot_le
  intro P hP
  change P = 0
  apply MvPolynomial.funext_set (fun _ => ({0} : Set ℂ)ᶜ)
    (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl)
  intro X hX
  have hX0 (i : Fin 2) : X ⟨i,(0 : Fin 2)⟩ ≠ 0 := hX _ (Set.mem_univ _)
  have hn (i : Fin 2) : (fun j : Fin 2 => X ⟨i,j⟩) ≠ 0 :=
    fun h => hX0 i (congrFun h 0)
  let p (i : Fin 2) := Projectivization.mk ℂ (fun j : Fin 2 => X ⟨i,j⟩) (hn i)
  have hp (i : Fin 2) : p i ∈ additiveCarrier ℂ := by
    obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
      (fun j : Fin 2 => X ⟨i,j⟩) (hn i)
    change (p i).rep 0 ≠ 0
    dsimp only [p]
    rw [← hc]
    exact mul_ne_zero c.ne_zero (hX0 i)
  let g : plane.Point := fun i => ⟨p i,hp i⟩
  have hz := plane.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
    (Set.mem_image_of_mem plane.embedding (Set.mem_univ g)) X
    (fun i => ⟨hn i,rfl⟩) hP
  simpa only [map_zero] using hz

theorem plane_hilbertFunction_bot (d : Fin 2 → ℕ) :
    Hilbert.hilbertFunction ℂ 2 (fun _ => 1) ⊥ d = (d 0+1)*(d 1+1) := by
  let V (i : plane.ambient.FactorIndex) :
      SectionThree.ProjectiveSubvariety ℂ (plane.ambient.ambientDimension i) :=
    ⟨additiveCarrier ℂ,additiveCarrier_locallyClosed ℂ⟩
  have heq : plane.embedding '' Set.univ = SectionThree.productCarrier plane.ambient V := by
    ext x
    constructor
    · rintro ⟨g,_,rfl⟩ i
      exact (g i).property
    · intro hx
      exact ⟨(fun i => ⟨x i,hx i⟩),Set.mem_univ _,rfl⟩
  have h := product_projective_hilbert_function ℂ plane.ambient V d
  rw [← heq] at h
  change Hilbert.hilbertFunction ℂ 2 (fun _ => 1) (plane.vanishingIdeal Set.univ) d = _ at h
  rw [plane_vanishingIdeal_univ] at h
  change Hilbert.hilbertFunction ℂ 2 (fun _ => 1) ⊥ d =
    ∏ i : Fin 2, Hilbert.hilbertFunction ℂ 1 (fun _ => 1)
      ((projectiveSpace ℂ 1).vanishingIdeal ((fun p => fun _ => p) '' additiveCarrier ℂ))
      (fun _ => d i) at h
  simp only [additiveCarrier_vanishingIdeal_eq_bot,Fin.prod_univ_two] at h
  rw [Hilbert.binary_hilbertFunction_bot ℂ (d 0),
    Hilbert.binary_hilbertFunction_bot ℂ (d 1)] at h
  exact h

theorem plane_hilbertPolynomial_bot :
    Hilbert.hilbertPolynomial ℂ 2 (fun _ => 1) ⊥ =
      (X (0 : Fin 2)+1)*(X (1 : Fin 2)+1) := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0,fun d _ => ?_⟩
  rw [plane_hilbertFunction_bot]
  simp

theorem plane_idealDimension_bot : SectionThree.idealDimension plane.ambient ⊥ = 2 := by
  change (Hilbert.hilbertPolynomial ℂ 2 (fun _ => 1) ⊥).totalDegree = 2
  rw [plane_hilbertPolynomial_bot]
  have hd (i : Fin 2) : (X i+1 : MvPolynomial (Fin 2) ℚ).totalDegree = 1 := by
    rw [totalDegree_add_eq_left_of_totalDegree_lt (by simp)]
    simp
  have hn (i : Fin 2) : (X i+1 : MvPolynomial (Fin 2) ℚ) ≠ 0 := by
    intro h
    have := hd i
    rw [h,totalDegree_zero] at this
    contradiction
  rw [totalDegree_mul_of_isDomain (hn 0) (hn 1),hd,hd]

theorem plane_proper_dimension (H : AlgebraicSubgroup plane)
    (hnot : ¬ diagonalAnalytic.carrier ⊆ H.carrier) :
    varietyDimension plane H.carrier ≤ 1 := by
  let I := plane.vanishingIdeal H.carrier
  have hI : IsMultihomogeneousIdeal plane.ambient I := vanishingIdeal_multihomogeneous ℂ _ _
  have hne : I ≠ ⊥ := by
    intro hz
    apply hnot
    intro x _
    apply H.mem_of_homogeneous_equations x
    intro P D hP hp
    have hmem : P ∈ I := Ideal.subset_span ⟨⟨D,hP⟩,by
      rintro _ ⟨y,hy,rfl⟩; exact hp y hy⟩
    rw [hz] at hmem
    have hP0 : P = 0 := hmem
    rw [hP0]
    rfl
  have hnontriv : SectionThree.IsNontrivialIdeal plane.ambient I := by
    apply plane.ambient.relevant_of_zeroLocus_nonempty I.radical
    refine ⟨plane.embedding 0,?_⟩
    rintro P ⟨n,hn⟩
    have hz := plane.ambient.eval_eq_zero_of_mem_vanishingIdeal hn
      (Set.mem_image_of_mem plane.embedding H.toAddSubgroup.zero_mem)
    exact eq_zero_of_pow_eq_zero (by simpa only [MultiProjectiveSpace.eval,map_pow] using hz)
  obtain ⟨q,hq,hrel,hdim⟩ := Hilbert.exists_relevant_minimalPrime_dimension_eq
    plane.ambient I hI hnontriv
  have hq0 : q ≠ ⊥ := fun hz => hne (le_antisymm (hz ▸ hq.le) bot_le)
  have hbot : IsMultihomogeneousIdeal plane.ambient ⊥ := by
    intro P hP d
    have hP0 : P = 0 := hP
    simp [hP0]
  have hlt := Hilbert.relevant_prime_dimension_strict plane.ambient ⊥ q
    Ideal.bot_prime hq.isPrime hbot (Hilbert.minimalPrime_homogeneous _ I q hI hq)
    hrel (bot_lt_iff_ne_bot.mpr hq0)
  rw [plane_idealDimension_bot,hdim] at hlt
  exact Nat.le_of_lt_succ hlt

theorem mixedDegree_nonneg {K : Type*} [Field K] (G : EmbeddedGroupProduct K)
    (V : Set G.Point) (a : G.FactorIndex → ℕ) : 0 ≤ mixedDegree G V a := by
  classical
  unfold mixedDegree
  split_ifs with h
  · apply mul_nonneg ?_ (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _)
    have hc := (multigraded_hilbert_polynomial_top_coefficients K G.ambient
      (G.vanishingIdeal V) (vanishingIdeal_multihomogeneous K _ _)).1
      (Finsupp.equivFunOnFinite.symm a)
    have hd : (Finsupp.equivFunOnFinite.symm a).degree =
        (Hilbert.hilbertPolynomial K G.factorCount G.ambient.ambientDimension
          (G.vanishingIdeal V)).totalDegree := by
      simpa [Finsupp.degree_eq_sum,varietyDimension] using h
    change 0 ≤ coeff (Finsupp.equivFunOnFinite.symm a)
      (homogeneousComponent
        (Hilbert.hilbertPolynomial K G.factorCount G.ambient.ambientDimension
          (G.vanishingIdeal V)).totalDegree
        (Hilbert.hilbertPolynomial K G.factorCount G.ambient.ambientDimension
          (G.vanishingIdeal V))) at hc
    rw [coeff_homogeneousComponent,if_pos hd] at hc
    exact_mod_cast hc
  · exact le_rfl

theorem plane_factor_dimension (i : plane.FactorIndex) : (plane.factor i).dimension = 1 :=
  additiveEmbeddedGroup_dimension ℂ

theorem plane_dimension : plane.dimension = 2 := by
  change (∑ i : Fin 2, (plane.factor i).dimension) = 2
  simp only [plane_factor_dimension,Fin.sum_univ_two]

theorem plane_numerical_inequality (c : ℝ) (H : AlgebraicSubgroup plane)
    (hnot : ¬ diagonalAnalytic.carrier ⊆ H.carrier) :
    ∃ r : SourceMixedCodimensionIndex plane H,
      c*r.degreeMonomial boundaryDegrees ≤
        (cosetCount {0} H.carrier : ℝ) * mixedDegree plane H.carrier r.complementIndex := by
  have hd := plane_proper_dimension H hnot
  let r : SourceMixedCodimensionIndex plane H := {
    exponent := ![1-varietyDimension plane H.carrier,1]
    bounded := by
      intro i
      rw [plane_factor_dimension]
      change Fin 2 at i
      fin_cases i <;> simp
    sum_eq := by
      change (∑ i : Fin 2, ![1-varietyDimension plane H.carrier,1] i) + _ = _
      rw [Fin.sum_univ_two,plane_dimension]
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      omega }
  refine ⟨r,?_⟩
  have hz : r.degreeMonomial boundaryDegrees = 0 := by
    change (∏ i : Fin 2, (boundaryDegrees i : ℝ)^r.exponent i) = 0
    simp [Fin.prod_univ_two,r,boundaryDegrees,plane]
  rw [hz,mul_zero]
  exact mul_nonneg (Nat.cast_nonneg _) (mixedDegree_nonneg _ _ _)

theorem zero_degree_counterexample :
    ∃ (G : EmbeddedGroupProduct ℂ) (A : AnalyticSubgroup G) (P : G.CoordinateRing),
      G.factorCount = 2 ∧ (∀ i, (G.factor i).dimension = 1) ∧
      A.dimension = 1 ∧ P ≠ 0 ∧
      IsMultihomogeneousOfDegree G P (fun i => if i.val = 0 then 1 else 0) ∧
      vanishingOrder A P 0 = 1 ∧
      (∀ c : ℝ, 0 < c → ∀ H : AlgebraicSubgroup G,
        H.IsConnected → ¬ A.carrier ⊆ H.carrier →
        ∃ r : SourceMixedCodimensionIndex G H,
          c * r.degreeMonomial (fun i => if i.val = 0 then 1 else 0) ≤
            (cosetCount {0} H.carrier : ℝ) *
              (mixedDegree G H.carrier r.complementIndex : ℝ)) ∧
      ¬ ∃ g : G.Point, translate g A.carrier ⊆ zeroLocusOnGroup G P := by
  exact ⟨plane,diagonalAnalytic,planePolynomial,rfl,plane_factor_dimension,
    diagonal_dimension,X_ne_zero _,planePolynomial_homogeneous,planePolynomial_order,
    fun c _ H _ hn => plane_numerical_inequality c H hn,plane_no_translate⟩

end PhilipponMultiplicity.SourceBoundary
end

open PhilipponMultiplicity

theorem solution :
    (∃ (G : EmbeddedGroupProduct ℂ) (A : AnalyticSubgroup G)
        (H : AlgebraicSubgroup G),
      Subsingleton G.Point ∧ G.dimension = 0 ∧ H.carrier = Set.univ ∧
      A.carrier = {0} ∧ analyticCodimension A H.carrier = 0 ∧
      hilbertDegreeForm G Set.univ (fun _ => 1) = 1 ∧
      hilbertDegreeForm G H.carrier (fun _ => 1) = 1 ∧
      (Nat.choose (0 + analyticCodimension A H.carrier)
          (analyticCodimension A H.carrier) : ℝ) *
        (cosetCount {0} H.carrier : ℝ) * hilbertDegreeForm G H.carrier (fun _ => 1) ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ (fun _ => 1) ∧
      ¬ ∃ P : G.CoordinateRing,
        (∀ h ∈ H.carrier, (1 : WithTop ℕ) ≤ vanishingOrder A P h) ∧
        (∃ x : G.Point, x ∉ zeroLocusOnGroup G P)) ∧
    (∃ (G : EmbeddedGroupProduct ℂ) (A : AnalyticSubgroup G)
        (sample : Finset G.Point) (P : G.CoordinateRing),
      G.dimension = 0 ∧ sample.card = 2 ∧ 0 ∈ sample ∧ A.carrier = {0} ∧
      P ≠ 0 ∧ IsMultihomogeneousOfDegree G P (fun _ => 1) ∧
      (∀ g ∈ sumset sample G.dimension, vanishingOrder A P g = ⊤) ∧
      ¬ ∃ H : AlgebraicSubgroup G,
        ∀ g ∈ sample, PhilipponMultiplicity.translate g H.carrier ⊆ zeroLocusOnGroup G P) ∧
    (∃ (G : EmbeddedGroupProduct ℂ) (A : AnalyticSubgroup G)
        (P : G.CoordinateRing),
      G.factorCount = 2 ∧ (∀ i, (G.factor i).dimension = 1) ∧
      A.dimension = 1 ∧ P ≠ 0 ∧
      IsMultihomogeneousOfDegree G P (fun i => if i.val = 0 then 1 else 0) ∧
      vanishingOrder A P 0 = 1 ∧
      (∀ c : ℝ, 0 < c → ∀ H : AlgebraicSubgroup G,
        H.IsConnected → ¬ A.carrier ⊆ H.carrier →
        ∃ r : SourceMixedCodimensionIndex G H,
          c * r.degreeMonomial (fun i => if i.val = 0 then 1 else 0) ≤
            (cosetCount {0} H.carrier : ℝ) *
              (mixedDegree G H.carrier r.complementIndex : ℝ)) ∧
      ¬ ∃ g : G.Point, PhilipponMultiplicity.translate g A.carrier ⊆ zeroLocusOnGroup G P) := by
  exact ⟨SourceBoundary.trivial_counterexample, SourceBoundary.two_point_counterexample,
    SourceBoundary.zero_degree_counterexample⟩
