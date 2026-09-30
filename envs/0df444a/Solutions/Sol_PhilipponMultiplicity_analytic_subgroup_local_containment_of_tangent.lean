-- Prove2me | solution 1 for PhilipponMultiplicity.analytic_subgroup_local_containment_of_tangent
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T06:00:40.827138+00:00
-- url     : https://prove2.me/submissions/c1af8822-6580-47ea-8e96-40ecd13524ce

import Theorems.Thm_PhilipponMultiplicity_proposition_4_3
import Theorems.Thm_PhilipponMultiplicity_proposition_4_4
import Theorems.Thm_PhilipponMultiplicity_exists_uniformly_bounded_translation_atlas
import Theorems.Thm_PhilipponMultiplicity_first_prolongation_preserves_subgroup_vanishingIdeal
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial PhilipponMultiplicity
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


theorem IsPhilipponBaseField.charZero {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CharZero K := by
  rcases hK with ⟨e,_⟩ | ⟨p,hp,h⟩
  · exact e.toRingHom.charZero
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e,_⟩ := h
    exact e.toRingHom.charZero


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


namespace TangentLocalContainmentProof


private theorem block_weight_apply {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (e : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) e) i =
      ∑ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex, ∑ j : Fin (M.ambientDimension b + 1),
    e ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

private theorem vanishing_homogeneous {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  let := MvPolynomial.weightedGradedAlgebra K w
  have hh : (M.vanishingIdeal S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D, hD⟩ := hP.1
    refine ⟨D, ?_⟩
    intro e he
    funext i
    rw [block_weight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d


/-- Vanishing of every derivative forces an analytic germ to be zero. -/
private theorem analytic_germ_zero_of_all_jets
    {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
    [NormedAddCommGroup E] [NormedSpace K E]
    {f : E → K} (hf : AnalyticAt K f 0)
    (hjets : ∀ n : ℕ, iteratedFDeriv K n f 0 = 0) :
    ∀ᶠ z in 𝓝 (0 : E), f z = 0 := by
  obtain ⟨p, r, hp⟩ := hf
  filter_upwards [Metric.eball_mem_nhds (0 : E) hp.r_pos] with z hz
  have hs := hp.hasSum_iteratedFDeriv hz
  simp only [hjets, ContinuousMultilinearMap.zero_apply, smul_zero, zero_add] at hs
  exact hs.unique hasSum_zero

/-- Composition propagates first-order invariance to every positive order. -/
private theorem all_prolongations_fixed
    {K : Type*} [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (atlas : TranslationAtlas A (0 : G.Point))
    (hfirst : retainedPolynomialOperatorIdeal atlas 1 (G.vanishingIdeal H.carrier) =
      G.vanishingIdeal H.carrier) :
    ∀ n : ℕ, retainedPolynomialOperatorIdeal atlas (n + 1)
      (G.vanishingIdeal H.carrier) = G.vanishingIdeal H.carrier := by
  intro n
  induction n with
  | zero => exact hfirst
  | succ n ih =>
    have hcomp := (proposition_4_3 K hK G A 0 0 (n + 1) 1
      (G.vanishingIdeal H.carrier)
      (vanishing_homogeneous G.ambient (G.embedding '' H.carrier)) atlas atlas).2 atlas
    have hcomp' : ∀ combined : TranslationAtlas A (0 : G.Point),
        retainedPolynomialOperatorIdeal atlas (n + 1)
          (retainedPolynomialOperatorIdeal atlas 1 (G.vanishingIdeal H.carrier)) =
        retainedPolynomialOperatorIdeal combined (n + 1 + 1)
          (G.vanishingIdeal H.carrier) := by
      exact Eq.mp (congrArg (fun g : G.Point =>
        ∀ combined : TranslationAtlas A g,
          retainedPolynomialOperatorIdeal atlas (n + 1)
            (retainedPolynomialOperatorIdeal atlas 1 (G.vanishingIdeal H.carrier)) =
          retainedPolynomialOperatorIdeal combined (n + 1 + 1)
            (G.vanishingIdeal H.carrier)) (zero_add (0 : G.Point))) hcomp
    simpa only [hfirst, ih] using (hcomp' atlas).symm

/-- Every ideal equation has a zero analytic germ once the retained ideal is fixed. -/
private theorem equation_germ_zero
    {K : Type*} [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (atlas : TranslationAtlas A (0 : G.Point))
    (hfirst : retainedPolynomialOperatorIdeal atlas 1 (G.vanishingIdeal H.carrier) =
      G.vanishingIdeal H.carrier)
    (Q : G.CoordinateRing) (hQ : Q ∈ G.vanishingIdeal H.carrier) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), A.pullback Q 0 z = 0 := by
  letI : CompleteSpace K := hK.completeSpace
  letI : CharZero K := hK.charZero
  apply analytic_germ_zero_of_all_jets
  · exact AnalyticAt.aeval_mvPolynomial (A.lift_analytic 0) Q
  · intro n
    by_contra hn
    have hle : vanishingOrder A Q 0 ≤ (n : WithTop ℕ) :=
      sInf_le ⟨n, hn, rfl⟩
    have hhigh := (proposition_4_4 K hK G A 0 0 (n + 1)
      (G.vanishingIdeal H.carrier)
      (vanishing_homogeneous G.ambient (G.embedding '' H.carrier)) atlas).mp
      (by
        rw [all_prolongations_fixed hK G A H atlas hfirst n]
        intro P hP
        exact G.ambient.eval_eq_zero_of_mem_vanishingIdeal hP
          ⟨0, H.toAddSubgroup.zero_mem, rfl⟩) Q hQ
    simp only [zero_add] at hhigh
    exact (not_lt_of_ge (hle.trans (by exact_mod_cast Nat.le_succ n))) hhigh

/-- A finite basis provides one neighborhood on which every ideal equation vanishes. -/
private theorem local_containment_of_equation_germs
    {K : Type*} [NontriviallyNormedField K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hzero : ∀ Q ∈ G.vanishingIdeal H.carrier,
      ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), A.pullback Q 0 z = 0) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ hz : z ∈ A.domain, A.map ⟨z, hz⟩ ∈ H.carrier := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (G.vanishingIdeal H.carrier))
  have hnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ Q ∈ s, A.pullback Q 0 z = 0 := by
    apply (Filter.eventually_all_finset s).mpr
    intro Q hQ
    apply hzero Q
    rw [← hs]
    exact Ideal.subset_span hQ
  filter_upwards [hnear] with z hz hdomain
  have hideal : G.vanishingIdeal H.carrier ≤
      RingHom.ker (MvPolynomial.eval (A.lift 0 z)) := by
    rw [← hs]
    apply Ideal.span_le.mpr
    intro Q hQ
    exact hz Q hQ
  apply H.mem_of_homogeneous_equations
  intro P D hP hvan
  apply (G.ambient.eval_eq_zero_iff_of_lift
    (G.embedding (A.map ⟨z, hdomain⟩)) (A.lift 0 z)
    (A.base_represents ⟨z, hdomain⟩) P D hP).mp
  exact hideal (Ideal.subset_span ⟨⟨D, hP⟩, by
    rintro _ ⟨y, hy, rfl⟩
    exact hvan y hy⟩)

end TangentLocalContainmentProof
end PhilipponMultiplicity

/-- Tangent containment reduces to stability of the first retained prolongation. -/
theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (htangent : A.tangentKernel H.carrier = ⊤) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ hz : z ∈ A.domain, A.map ⟨z, hz⟩ ∈ H.carrier := by
  obtain ⟨c, hc, hatlas⟩ := exists_uniformly_bounded_translation_atlas K hK
  obtain ⟨atlas, _⟩ := hatlas G A 0
  have hfirst := first_prolongation_preserves_subgroup_vanishingIdeal
    K hK G A H htangent atlas
  apply TangentLocalContainmentProof.local_containment_of_equation_germs G A H
  exact TangentLocalContainmentProof.equation_germ_zero hK G A H atlas hfirst
