-- Prove2me | solution 1 for PhilipponMultiplicity.section_five_bounded_translated_chain
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-29T10:01:20.992408+00:00
-- url     : https://prove2.me/submissions/db991f36-03cf-410f-b044-74c2bfaf5f5a

import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Differential
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_Hilbert
import Definitions.Def_PhilipponMultiplicity_IteratedJets
import Definitions.Def_PhilipponMultiplicity_Operators
import Definitions.Def_PhilipponMultiplicity_SectionFive
import Definitions.Def_PhilipponMultiplicity_SectionFour
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionChartLocus
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionLocus
import Mathlib
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Lasker
import Mathlib.RingTheory.Polynomial.Basic

section
-- Implementation: Solutions/PhilipponAnalyticUnitOrder.lean

set_option autoImplicit false
open scoped Topology BigOperators ContDiff
open Filter
noncomputable section

namespace PhilipponMultiplicity
variable {K E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]

/-- Multiplication preserves a vanishing finite jet. -/
theorem iteratedFDeriv_mul_eq_zero_of_vanishing_jet
    {f u : E → K} {x : E} {n : ℕ}
    (hf : ContDiffAt K n f x) (hu : ContDiffAt K n u x)
    (hz : ∀ i ≤ n, iteratedFDeriv K i f x = 0) :
    iteratedFDeriv K n (fun y => u y * f y) x = 0 := by
  obtain ⟨s, hs, hopen, hxs⟩ := eventually_nhds_iff.mp
    ((hf.eventually (by simp)).and (hu.eventually (by simp)))
  have hfs : ContDiffOn K n f s := fun y hy => (hs y hy).1.contDiffWithinAt
  have hus : ContDiffOn K n u s := fun y hy => (hs y hy).2.contDiffWithinAt
  have hbound := norm_iteratedFDerivWithin_mul_le hus hfs hopen.uniqueDiffOn hxs
    (le_refl (n : ℕ∞ω))
  simp only [iteratedFDerivWithin_of_isOpen _ hopen hxs] at hbound
  have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ‖iteratedFDeriv K i u x‖ * ‖iteratedFDeriv K (n - i) f x‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hz (n - i) (Nat.sub_le _ _)]
  rw [hsum] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

def jetOrder (f : E → K) (x : E) : WithTop ℕ :=
  sInf ((fun n : ℕ => (n : WithTop ℕ)) '' {n | iteratedFDeriv K n f x ≠ 0})

theorem natCast_le_jetOrder_iff {f : E → K} {x : E} {n : ℕ} :
    (n : WithTop ℕ) ≤ jetOrder f x ↔
      ∀ i < n, iteratedFDeriv K i f x = 0 := by
  constructor
  · intro h i hi
    by_contra hne
    have hle : jetOrder f x ≤ (i : WithTop ℕ) := sInf_le ⟨i, hne, rfl⟩
    have : n ≤ i := by exact_mod_cast h.trans hle
    omega
  · intro h
    apply le_sInf
    rintro _ ⟨i, hi, rfl⟩
    by_contra! hlt
    have hin : i < n := by exact_mod_cast hlt
    exact hi (h i hin)

theorem jetOrder_congr {f g : E → K} {x : E} (h : f =ᶠ[𝓝 x] g) :
    jetOrder f x = jetOrder g x := by
  unfold jetOrder
  congr 3
  ext n
  rw [(h.iteratedFDeriv K n).eq_of_nhds]

/-- An analytic unit does not change the order defined by iterated Fréchet derivatives. -/
theorem jetOrder_mul_unit [CompleteSpace K] {f u : E → K} {x : E}
    (hf : AnalyticAt K f x) (hu : AnalyticAt K u x) (hu0 : u x ≠ 0) :
    jetOrder (fun y => u y * f y) x = jetOrder f x := by
  apply WithTop.eq_of_forall_coe_le_iff
  intro n
  change ((n : WithTop ℕ) ≤ jetOrder (fun y => u y * f y) x) ↔
    (n : WithTop ℕ) ≤ jetOrder f x
  rw [natCast_le_jetOrder_iff, natCast_le_jetOrder_iff]
  have hunit : ∀ᶠ y in 𝓝 x, u y ≠ 0 := hu.continuousAt.eventually_ne hu0
  have hinv : (fun y => (u y)⁻¹ * (u y * f y)) =ᶠ[𝓝 x] f := by
    filter_upwards [hunit] with y hy
    simp [hy]
  constructor
  · intro h i hi
    have hz := iteratedFDeriv_mul_eq_zero_of_vanishing_jet
      (hu.mul hf).contDiffAt (hu.inv hu0).contDiffAt
      (fun j hj => h j (hj.trans_lt hi))
    change iteratedFDeriv K i (fun y => (u y)⁻¹ * (u y * f y)) x = 0 at hz
    rw [(hinv.iteratedFDeriv K i).eq_of_nhds] at hz
    exact hz
  · intro h i hi
    exact iteratedFDeriv_mul_eq_zero_of_vanishing_jet hf.contDiffAt hu.contDiffAt
      (fun j hj => h j (hj.trans_lt hi))

end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponProjectiveContact.lean

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

private theorem coordinate_ratio {K : Type*} [Field K] {ι : Type*}
    {f g : ι → K} {hf : f ≠ 0} {hg : g ≠ 0}
    (h : Projectivization.mk K f hf = Projectivization.mk K g hg)
    (j : ι) (hj : g j ≠ 0) :
    f j / g j ≠ 0 ∧ ∀ k, f k = (f j / g j) * g k := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K f g hf hg).mp h
  have hj' : f j = (a : K) * g j := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  have hratio : f j / g j = (a : K) := by rw [hj']; exact mul_div_cancel_right₀ _ hj
  rw [hratio]
  refine ⟨a.ne_zero, ?_⟩
  intro k
  simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha k).symm

/-- Locally equal projective lifts change a multihomogeneous pullback by an analytic unit. -/
theorem MultiProjectiveSpace.jetOrder_eq_of_projective_lifts
    {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace K E]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (f g : E → M.Variable → K) (x : E)
    (hf : ∀ v, AnalyticAt K (fun z => f z v) x)
    (hg : ∀ v, AnalyticAt K (fun z => g z v) x)
    (hrep : ∀ᶠ z in 𝓝 x, ∀ i : M.FactorIndex,
      ∃ hfi : (fun j => f z ⟨i, j⟩) ≠ 0,
      ∃ hgi : (fun j => g z ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i, j⟩) hfi =
          Projectivization.mk K (fun j => g z ⟨i, j⟩) hgi) :
    jetOrder (fun z => MvPolynomial.eval (f z) P) x = jetOrder (fun z => MvPolynomial.eval (g z) P) x := by
  classical
  have hpivot (i : M.FactorIndex) : ∃ j, g x ⟨i, j⟩ ≠ 0 := by
    obtain ⟨_, hgi, _⟩ := hrep.self_of_nhds i
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hgi
  choose j hj using hpivot
  let a (z : E) (i : M.FactorIndex) := f z ⟨i, j i⟩ / g z ⟨i, j i⟩
  let u (z : E) := ∏ i, a z i ^ D i
  have ha (i : M.FactorIndex) : AnalyticAt K (fun z => a z i) x :=
    (hf _).div (hg _) (hj i)
  have hu : AnalyticAt K u x := by
    exact Finset.analyticAt_fun_prod _ (fun i _ => (ha i).pow (D i))
  have hax (i : M.FactorIndex) : a x i ≠ 0 := by
    obtain ⟨hfi, hgi, heq⟩ := hrep.self_of_nhds i
    exact (coordinate_ratio heq (j i) (hj i)).1
  have hux : u x ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hax i))
  have hjnear : ∀ᶠ z in 𝓝 x, ∀ i : M.FactorIndex, g z ⟨i, j i⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (hg _).continuousAt.eventually_ne (hj i)
  have hfg : (fun z => MvPolynomial.eval (f z) P) =ᶠ[𝓝 x]
      (fun z => u z * MvPolynomial.eval (g z) P) := by
    filter_upwards [hrep, hjnear] with z hz hjz
    have hcoords : f z = fun v => a z v.1 * g z v := by
      funext v
      obtain ⟨hfi, hgi, heq⟩ := hz v.1
      exact (coordinate_ratio heq (j v.1) (hjz v.1)).2 v.2
    rw [hcoords, M.eval_block_scale P D hP]
  have hgP : AnalyticAt K (fun z => MvPolynomial.eval (g z) P) x := by
    change AnalyticAt K (fun z => aeval (g z) P) x
    exact AnalyticAt.aeval_mvPolynomial hg P
  exact (jetOrder_congr hfg).trans (jetOrder_mul_unit hgP hu hux)

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

/-- The independence assertion in Philippon's definition of contact order, p. 358. -/
theorem projective_lift_contact_invariance
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g : G.Point) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : IsMultihomogeneousOfDegree G P D)
    (f : A.ParameterSpace → G.ambient.Variable → K)
    (hf : ∀ v, AnalyticAt K (fun z => f z v) 0)
    (hrep : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      ∀ i : G.FactorIndex, ∃ h : (fun j => f z ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i, j⟩) h =
          G.embedding (g + A.map ⟨z, hz⟩) i) :
    vanishingOrder A P g = sInf ((fun n : ℕ => (n : WithTop ℕ)) ''
      {n | iteratedFDeriv K n (fun z => MvPolynomial.eval (f z) P) 0 ≠ 0}) := by
  letI : CompleteSpace K := hK.completeSpace
  apply G.ambient.jetOrder_eq_of_projective_lifts P D hP
    (A.lift g) f 0 (A.lift_analytic g) hf
  filter_upwards [A.lift_represents g, hrep] with z hz hfz
  obtain ⟨hz, hAz⟩ := hz
  obtain ⟨hfz, hFz⟩ := hfz
  intro i
  obtain ⟨hA, heqA⟩ := hAz i
  obtain ⟨hF, heqF⟩ := hFz i
  exact ⟨hA, hF, heqA.trans heqF.symm⟩

end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponOperatorEvaluation.lean

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

theorem evaluated_coefficients_analytic
    (F : MvPolynomial G.ambient.Variable (AnalyticCoefficientRing A))
    (hF : ∀ e, AnalyticAt K (F.coeff e) 0) (x : G.Point) :
    AnalyticAt K (evaluateCoefficientPolynomial A F x) 0 := by
  classical
  change AnalyticAt K (fun z => eval₂ (Pi.evalRingHom (fun _ : A.ParameterSpace => K) z)
    (G.ambient.coordinate (G.embedding x)) F) 0
  simp only [eval₂_eq, Pi.evalRingHom_apply]
  exact Finset.analyticAt_fun_sum _ fun e _ => (hF e).mul analyticAt_const

theorem chart_evaluation_analytic (chart : TranslationChart A g)
    (x : G.Point) (v : G.ambient.Variable) :
    AnalyticAt K (evaluateCoefficientPolynomial A (chart.coordinates v) x) 0 :=
  evaluated_coefficients_analytic _ (coordinate_coeff_analytic chart v) x

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

/-- Evaluation of the actual coefficientwise polynomial operator is the
corresponding mixed derivative of the actual evaluated chart polynomial. -/
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
-- Implementation: Solutions/PhilipponProjectiveGeometry.lean

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

namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

theorem projective_extension_locallyClosed (g₂ g₃ : ℂ) :
    @IsLocallyClosed _
      (TopologicalSpace.induced (fun p _ => p) (projectiveSpace ℂ 4).zariskiTopology)
      {p : Projectivization ℂ (Fin 5 → ℂ) |
        MvPolynomial.eval p.rep extensionQuadric = 0 ∧
        MvPolynomial.eval p.rep (extensionCubic g₂ g₃) = 0 ∧
        (p.rep 0 ≠ 0 ∨ p.rep 2 ≠ 0)} := by
  letI := TopologicalSpace.induced (fun (p : Projectivization ℂ (Fin 5 → ℂ)) =>
    (fun _ => p : (projectiveSpace ℂ 4).Point)) (projectiveSpace ℂ 4).zariskiTopology
  have hq : extensionQuadric.IsHomogeneous 2 := by
    exact ((MvPolynomial.isHomogeneous_X ℂ 0).mul
      (MvPolynomial.isHomogeneous_X ℂ 4)).sub
      ((MvPolynomial.isHomogeneous_X ℂ 2).mul (MvPolynomial.isHomogeneous_X ℂ 3)) |>.sub
        (MvPolynomial.isHomogeneous_C_mul_X_pow 2 1 2)
  have hc : (extensionCubic g₂ g₃).IsHomogeneous 3 := by
    exact (((MvPolynomial.isHomogeneous_X ℂ 0).mul
      (MvPolynomial.isHomogeneous_X_pow 2 2)).sub
      (MvPolynomial.isHomogeneous_C_mul_X_pow 4 1 3)).add
        ((MvPolynomial.isHomogeneous_C_mul_X_pow g₂ 0 2).mul
          (MvPolynomial.isHomogeneous_X ℂ 1)) |>.add
        (MvPolynomial.isHomogeneous_C_mul_X_pow g₃ 0 3)
  convert
    ((projective_isClosed_zero hq).inter (projective_isClosed_zero hc)).isLocallyClosed.inter
      ((projective_isOpen_coordinate (K := ℂ) (0 : Fin 5)).union
        (projective_isOpen_coordinate (K := ℂ) (2 : Fin 5))).isLocallyClosed using 1
  ext p
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, and_assoc]

theorem projective_extension_fiber_action_regular (g₂ g₃ u : ℂ)
    (F : ProjectiveExtensionFiberModel g₂ g₃) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun p : ProjectiveExtensionChartLocus g₂ g₃ => fun _ => extensionProjectivePoint p)
      (fun p => fun _ => extensionProjectivePoint (F.action u p)) := by
  let P : Fin 5 → MvPolynomial (Fin 5) ℂ :=
    ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
      MvPolynomial.X 3 + MvPolynomial.C u * MvPolynomial.X 0,
      MvPolynomial.X 4 + MvPolynomial.C u * MvPolynomial.X 2]
  apply projective_regular_of_homogeneous _ _ P (d := 1)
  · intro j
    fin_cases j
    · exact MvPolynomial.isHomogeneous_X ℂ 0
    · exact MvPolynomial.isHomogeneous_X ℂ 1
    · exact MvPolynomial.isHomogeneous_X ℂ 2
    · exact (MvPolynomial.isHomogeneous_X ℂ 3).add
        ((MvPolynomial.isHomogeneous_C (Fin 5) u).mul (MvPolynomial.isHomogeneous_X ℂ 0))
    · exact (MvPolynomial.isHomogeneous_X ℂ 4).add
        ((MvPolynomial.isHomogeneous_C (Fin 5) u).mul (MvPolynomial.isHomogeneous_X ℂ 2))
  · intro p
    have heq : (fun j => MvPolynomial.eval (extensionProjectivePoint p).rep (P j)) =
        extensionFiberShear u (extensionProjectivePoint p).rep := by
      ext j
      fin_cases j <;> simp [P, extensionFiberShear]
    obtain ⟨h, hh⟩ := F.action_coords u p
    exact ⟨by simpa only [heq] using h, by simpa only [heq] using hh.symm⟩

end WeierstrassEllipticZeta
end
end


section
-- Implementation: Solutions/PhilipponPointHilbert.lean

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
-- Implementation: Solutions/PhilipponOperatorAlgebra.lean

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

theorem polynomialOperator_add (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (P Q : G.CoordinateRing) :
    polynomialOperator chart n directions (P + Q) =
      polynomialOperator chart n directions P + polynomialOperator chart n directions Q := by
  ext e
  simp only [coeff_add, polynomialOperator_coeff]
  have heq : (substitutedPolynomial chart (P + Q)).coeff e =
      fun z => (substitutedPolynomial chart P).coeff e z +
        (substitutedPolynomial chart Q).coeff e z := by
    simp [substitutedPolynomial]
    rfl
  rw [heq, fun_iteratedFDeriv_add_apply (substituted_coeff_analytic chart P e).contDiffAt
    (substituted_coeff_analytic chart Q e).contDiffAt]
  rfl

theorem polynomialOperator_C_mul (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (a : K) (P : G.CoordinateRing) :
    polynomialOperator chart n directions (C a * P) =
      C a * polynomialOperator chart n directions P := by
  ext e
  simp only [coeff_C_mul, polynomialOperator_coeff]
  have heq : (substitutedPolynomial chart (C a * P)).coeff e =
      fun z => a • (substitutedPolynomial chart P).coeff e z := by
    simp [substitutedPolynomial, coeff_C_mul, smul_eq_mul]
    rfl
  rw [heq, iteratedFDeriv_const_smul_apply' (substituted_coeff_analytic chart P e).contDiffAt]
  rfl

theorem polynomialOperator_zero_order (chart : TranslationChart A g)
    (directions : Fin 0 → Fin A.parameterDimension) (P : G.CoordinateRing) :
    polynomialOperator chart 0 directions P =
      MvPolynomial.map (Pi.evalRingHom (fun _ : A.ParameterSpace => K) 0)
        (substitutedPolynomial chart P) := by
  ext e
  simp [polynomialOperator_coeff, coeff_map]

theorem polynomialOperator_zero_algHom (chart : TranslationChart A g)
    (directions : Fin 0 → Fin A.parameterDimension) :
    ∃ f : G.CoordinateRing →ₐ[K] G.CoordinateRing,
      ∀ P, f P = polynomialOperator chart 0 directions P := by
  let f : G.CoordinateRing →+* G.CoordinateRing :=
    (MvPolynomial.map (Pi.evalRingHom (fun _ : A.ParameterSpace => K) 0)).comp
      (MvPolynomial.eval₂Hom
        (MvPolynomial.C.comp (Pi.constRingHom A.ParameterSpace K)) chart.coordinates)
  have hf (a : K) : f (algebraMap K G.CoordinateRing a) = algebraMap K G.CoordinateRing a := by
    simp [f, MvPolynomial.algebraMap_eq]
  refine ⟨{ f with commutes' := hf }, fun P => ?_⟩
  exact (polynomialOperator_zero_order chart directions P).symm

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
-- Implementation: Solutions/PhilipponOperatorIdeals.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

theorem retainOnGroup_mono {I J : Ideal G.CoordinateRing} (h : I ≤ J) :
    retainOnGroup G I ≤ retainOnGroup G J := by
  apply iInf_mono
  intro x
  exact Ideal.comap_mono (Ideal.map_mono h)

/-- Retention preserves the localized ideal at every genuine group representative. -/
theorem retainOnGroup_localization (I : Ideal G.CoordinateRing)
    (x : GroupHomogeneousRepresentative G) :
    (retainOnGroup G I).map (algebraMap G.CoordinateRing
      (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal)) =
    I.map (algebraMap G.CoordinateRing
      (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal)) := by
  apply le_antisymm
  · have h : retainOnGroup G I ≤ retainAtRepresentative G I x :=
      iInf_le (fun y : GroupHomogeneousRepresentative G => retainAtRepresentative G I y) x
    exact (Ideal.map_mono h).trans (le_of_eq (Ideal.map_comap_map _ I))
  · exact Ideal.map_mono (le_retainOnGroup G I)

theorem retainOnGroup_idempotent (I : Ideal G.CoordinateRing) :
    retainOnGroup G (retainOnGroup G I) = retainOnGroup G I := by
  unfold retainOnGroup retainAtRepresentative
  congr 1
  funext x
  change ((retainOnGroup G I).map _).under G.CoordinateRing = _
  rw [retainOnGroup_localization]

theorem retainOnGroup_sup (I J : Ideal G.CoordinateRing) :
    retainOnGroup G (retainOnGroup G I ⊔ retainOnGroup G J) =
      retainOnGroup G (I ⊔ J) := by
  apply le_antisymm
  · apply le_trans (retainOnGroup_mono G (sup_le
      (retainOnGroup_mono G le_sup_left) (retainOnGroup_mono G le_sup_right)))
    exact (retainOnGroup_idempotent G (I ⊔ J)).le
  · exact retainOnGroup_mono G (sup_le_sup (le_retainOnGroup G I) (le_retainOnGroup G J))

variable {G} {A : AnalyticSubgroup G} {g : G.Point}

theorem polynomialOperatorIdeal_mono (atlas : TranslationAtlas A g) (T : ℕ)
    {I J : Ideal G.CoordinateRing} (h : I ≤ J) :
    polynomialOperatorIdeal atlas T I ≤ polynomialOperatorIdeal atlas T J := by
  apply sup_le_sup_left
  apply Ideal.span_mono
  rintro Q ⟨P, hP, hhom, a, n, hn, dirs, rfl⟩
  exact ⟨P, h hP, hhom, a, n, hn, dirs, rfl⟩

theorem retainedPolynomialOperatorIdeal_mono (atlas : TranslationAtlas A g) (T : ℕ)
    {I J : Ideal G.CoordinateRing} (h : I ≤ J) :
    retainedPolynomialOperatorIdeal atlas T I ≤ retainedPolynomialOperatorIdeal atlas T J :=
  retainOnGroup_mono G (polynomialOperatorIdeal_mono atlas T h)

variable [CompleteSpace K]

theorem polynomialOperatorIdeal_sup (atlas : TranslationAtlas A g) (T : ℕ)
    (I J : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (hJ : IsMultihomogeneousIdeal G.ambient J) :
    polynomialOperatorIdeal atlas T (I ⊔ J) =
      polynomialOperatorIdeal atlas T I ⊔ polynomialOperatorIdeal atlas T J := by
  classical
  apply le_antisymm
  · apply sup_le
    · exact le_sup_of_le_left le_sup_left
    · apply Ideal.span_le.mpr
      rintro Q ⟨P, hP, ⟨D, hD⟩, a, n, hn, dirs, rfl⟩
      obtain ⟨P₁, h₁, P₂, h₂, heq⟩ := Submodule.mem_sup.mp hP
      let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
      let Q₁ := weightedHomogeneousComponent w D P₁
      let Q₂ := weightedHomogeneousComponent w D P₂
      have hQ₁ : Q₁ ∈ I := hI P₁ h₁ D
      have hQ₂ : Q₂ ∈ J := hJ P₂ h₂ D
      have hD₁ : G.ambient.IsHomogeneous Q₁ D :=
        (G.ambient.degreePiece_iff Q₁ D).mp (weightedHomogeneousComponent_mem w P₁ D)
      have hD₂ : G.ambient.IsHomogeneous Q₂ D :=
        (G.ambient.degreePiece_iff Q₂ D).mp (weightedHomogeneousComponent_mem w P₂ D)
      have hsum : P = Q₁ + Q₂ := by
        have hp : weightedHomogeneousComponent w D P = P :=
          weightedHomogeneousComponent_eq_self ((G.ambient.degreePiece_iff P D).mpr hD)
        rw [← hp, ← heq, map_add]
      rw [hsum, polynomialOperator_add]
      apply Ideal.add_mem
      · apply Ideal.mem_sup_left
        apply Ideal.mem_sup_right
        exact Ideal.subset_span ⟨Q₁, hQ₁, ⟨D, hD₁⟩, a, n, hn, dirs, rfl⟩
      · apply Ideal.mem_sup_right
        apply Ideal.mem_sup_right
        exact Ideal.subset_span ⟨Q₂, hQ₂, ⟨D, hD₂⟩, a, n, hn, dirs, rfl⟩
  · exact sup_le (polynomialOperatorIdeal_mono atlas T le_sup_left)
      (polynomialOperatorIdeal_mono atlas T le_sup_right)

theorem retainedPolynomialOperatorIdeal_sup (atlas : TranslationAtlas A g) (T : ℕ)
    (I J : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (hJ : IsMultihomogeneousIdeal G.ambient J) :
    retainedPolynomialOperatorIdeal atlas T (I ⊔ J) =
      retainOnGroup G (retainedPolynomialOperatorIdeal atlas T I ⊔
        retainedPolynomialOperatorIdeal atlas T J) := by
  rw [retainedPolynomialOperatorIdeal, polynomialOperatorIdeal_sup atlas T I J hI hJ]
  exact (retainOnGroup_sup G _ _).symm

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponMixedLeibniz.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology ContDiff
open Filter
noncomputable section

namespace PhilipponMultiplicity.JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

/-- Ordered directional differentiation; the head direction is applied last. -/
def mixedDeriv : List E → (E → K) → E → K
  | [], f => f
  | v :: w, f => fun x => fderiv K (mixedDeriv w f) x v

theorem mixedDeriv_analytic {f : E → K} {x : E} (hf : AnalyticAt K f x)
    (w : List E) : AnalyticAt K (mixedDeriv w f) x := by
  induction w with
  | nil => exact hf
  | cons v w ih =>
    exact ((ContinuousLinearMap.apply K K v).analyticAt _).comp ih.fderiv

theorem mixedDeriv_congr {f g : E → K} {x : E} (h : f =ᶠ[𝓝 x] g)
    (w : List E) : mixedDeriv w f =ᶠ[𝓝 x] mixedDeriv w g := by
  induction w with
  | nil => exact h
  | cons v w ih =>
    filter_upwards [ih.fderiv (𝕜 := K)] with y hy
    exact congrArg (fun L : E →L[K] K => L v) hy

theorem mixedDeriv_eq_iteratedFDeriv {f : E → K} {x : E}
    (hf : AnalyticAt K f x) (w : List E) :
    mixedDeriv w f x = iteratedFDeriv K w.length f x w.get := by
  induction w generalizing x with
  | nil => simp [mixedDeriv]
  | cons v w ih =>
    have hn : (mixedDeriv w f) =ᶠ[𝓝 x]
        (fun y => iteratedFDeriv K w.length f y w.get) := by
      have he : ∀ᶠ y in 𝓝 x, AnalyticAt K f y := hf.eventually_analyticAt
      filter_upwards [he] with y hy
      exact ih hy
    change fderiv K (mixedDeriv w f) x v = _
    rw [hn.fderiv_eq]
    have hd := (hf.contDiffAt : ContDiffAt K (⊤ : ℕ∞ω) f x).differentiableAt_iteratedFDeriv
      (m := w.length) (by simp)
    have htail : Fin.tail (v::w).get = w.get := by funext i; rfl
    simpa only [List.length_cons,htail,List.get_cons_zero] using
      (hd.iteratedFDeriv_succ_apply_left' (m := (v::w).get)).symm

/-- All product-rule terms except the term with no derivative on the first factor. -/
def properSplits : List E → List (List E × List E)
  | [] => []
  | v :: w => ([v],w) ::
      ((properSplits w).map (fun p => (v :: p.1,p.2)) ++
       (properSplits w).map (fun p => (p.1,v :: p.2)))

omit [NormedAddCommGroup E] in
theorem properSplits_lengths (w : List E) (p : List E × List E)
    (hp : p ∈ properSplits w) :
    0 < p.1.length ∧ p.1.length + p.2.length = w.length ∧ p.2.length < w.length := by
  induction w generalizing p with
  | nil => simp [properSplits] at hp
  | cons v w ih =>
    simp only [properSplits,List.mem_cons,List.mem_append,List.mem_map] at hp
    rcases hp with rfl | ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
    · simp [Nat.add_comm]
    · obtain ⟨h₁,h₂,h₃⟩ := ih q hq
      simp only [List.length_cons,Prod.fst,Prod.snd]
      omega
    · obtain ⟨h₁,h₂,h₃⟩ := ih q hq
      simp only [List.length_cons,Prod.fst,Prod.snd]
      omega

theorem differentiableAt_list_sum {ι : Type*} (s : List ι) (f : ι → E → K) (x : E)
    (hf : ∀ i ∈ s, DifferentiableAt K (f i) x) :
    DifferentiableAt K (fun y => (s.map fun i => f i y).sum) x := by
  induction s with
  | nil => simpa using (differentiableAt_const (c := (0 : K)))
  | cons i s ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (hf i (by simp)).fun_add (ih (fun j hj => hf j (by simp [hj])))

theorem fderiv_list_sum_apply {ι : Type*} (s : List ι) (f : ι → E → K) (x v : E)
    (hf : ∀ i ∈ s, DifferentiableAt K (f i) x) :
    fderiv K (fun y => (s.map fun i => f i y).sum) x v =
      (s.map fun i => fderiv K (f i) x v).sum := by
  induction s with
  | nil => simp
  | cons i s ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [fderiv_fun_add (hf i (by simp))
      (differentiableAt_list_sum s f x (fun j hj => hf j (by simp [hj]))),
      ContinuousLinearMap.add_apply,ih (fun j hj => hf j (by simp [hj]))]

/-- A triangular finite Leibniz formula: every term in the remainder uses a
strictly lower derivative of the second factor. -/
theorem mixedDeriv_mul {f g : E → K} {x : E}
    (hf : AnalyticAt K f x) (hg : AnalyticAt K g x) (w : List E) :
    mixedDeriv w (fun y => f y * g y) x =
      f x * mixedDeriv w g x +
        ((properSplits w).map fun p => mixedDeriv p.1 f x * mixedDeriv p.2 g x).sum := by
  induction w generalizing x with
  | nil => simp [mixedDeriv,properSplits]
  | cons v w ih =>
    have heq : mixedDeriv w (fun y => f y * g y) =ᶠ[𝓝 x]
        (fun y => f y * mixedDeriv w g y +
          ((properSplits w).map fun p => mixedDeriv p.1 f y * mixedDeriv p.2 g y).sum) := by
      filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with y hfy hgy
      exact ih hfy hgy
    have hd (p : List E × List E) :
        DifferentiableAt K (fun y => mixedDeriv p.1 f y * mixedDeriv p.2 g y) x :=
      ((mixedDeriv_analytic hf p.1).mul (mixedDeriv_analytic hg p.2)).differentiableAt
    have hmain : DifferentiableAt K (fun y => f y * mixedDeriv w g y) x :=
      (hf.mul (mixedDeriv_analytic hg w)).differentiableAt
    change fderiv K (mixedDeriv w (fun y => f y * g y)) x v = _
    rw [heq.fderiv_eq,fderiv_fun_add hmain
      (differentiableAt_list_sum _ _ x (fun p _ => hd p)),ContinuousLinearMap.add_apply,
      fderiv_fun_mul hf.differentiableAt (mixedDeriv_analytic hg w).differentiableAt,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,
      fderiv_list_sum_apply _ _ x v (fun p _ => hd p)]
    have hterm (p : List E × List E) :
        fderiv K (fun y => mixedDeriv p.1 f y * mixedDeriv p.2 g y) x v =
          mixedDeriv (v::p.1) f x * mixedDeriv p.2 g x +
            mixedDeriv p.1 f x * mixedDeriv (v::p.2) g x := by
      rw [fderiv_fun_mul (mixedDeriv_analytic hf p.1).differentiableAt
        (mixedDeriv_analytic hg p.2).differentiableAt]
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,mixedDeriv]
      ring
    simp only [hterm,properSplits,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
      List.map_map,Function.comp_def,List.sum_map_add,smul_eq_mul]
    simp only [mixedDeriv]
    ring

end PhilipponMultiplicity.JetSupport

namespace PhilipponMultiplicity.JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

omit [NormedAddCommGroup E] in
theorem properSplits_map {ι : Type*} (v : ι → E) (w : List ι) :
    properSplits (w.map v) = (properSplits w).map (fun p => (p.1.map v,p.2.map v)) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [properSplits,ih,List.map_map,Function.comp_def]

theorem iteratedFDeriv_apply_congr {n m : ℕ} (h : n = m) (f : E → K) (x : E)
    (v : Fin n → E) (w : Fin m → E) (hv : ∀ i, v i = w (Fin.cast h i)) :
    iteratedFDeriv K n f x v = iteratedFDeriv K m f x w := by
  subst m
  congr 1
  funext i
  exact hv i

theorem mixedDeriv_map_eq_iteratedFDeriv {ι : Type*} (v : ι → E)
    {f : E → K} {x : E} (hf : AnalyticAt K f x) (w : List ι) :
    mixedDeriv (w.map v) f x = iteratedFDeriv K w.length f x (fun i => v (w.get i)) := by
  rw [mixedDeriv_eq_iteratedFDeriv hf]
  apply iteratedFDeriv_apply_congr (List.length_map ..)
  intro i
  simp

theorem mixedDeriv_map_mul {ι : Type*} (v : ι → E)
    {f g : E → K} {x : E} (hf : AnalyticAt K f x) (hg : AnalyticAt K g x) (w : List ι) :
    mixedDeriv (w.map v) (fun y => f y * g y) x =
      f x * mixedDeriv (w.map v) g x +
        ((properSplits w).map fun p =>
          mixedDeriv (p.1.map v) f x * mixedDeriv (p.2.map v) g x).sum := by
  simpa only [properSplits_map,List.map_map,Function.comp_def] using mixedDeriv_mul hf hg (w.map v)

end PhilipponMultiplicity.JetSupport
end
end


section
-- Implementation: Solutions/PhilipponAnalyticContainment.lean

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
end


section
-- Implementation: Solutions/PhilipponAdditiveSubgroups.lean

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

/-- Closed algebraic subgroups pull back to linear subspaces under additive
parametrizations with affine-linear projective coordinates, in characteristic zero. -/
theorem AlgebraicSubgroup.smul_mem_of_affine_linear_lift
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    {G : EmbeddedGroupProduct K} (H : AlgebraicSubgroup G)
    (q : V →+ G.Point) (b : G.ambient.Variable → K)
    (ell : G.ambient.Variable → V →ₗ[K] K)
    (hrep : ∀ v : V, ∀ i : G.FactorIndex,
      ∃ h : (fun j => b ⟨i, j⟩ + ell ⟨i, j⟩ v) ≠ 0,
        Projectivization.mk K (fun j => b ⟨i, j⟩ + ell ⟨i, j⟩ v) h =
          G.embedding (q v) i)
    (v : V) (hv : q v ∈ H.carrier) (c : K) : q (c • v) ∈ H.carrier := by
  classical
  apply H.mem_of_homogeneous_equations
  intro P D hP hzero
  let F : MvPolynomial (Fin 1) K := eval₂ C
    (fun j => C (b j) + C (ell j v) * X 0) P
  have hEval (a : K) : MvPolynomial.eval (fun _ : Fin 1 => a) F =
      MvPolynomial.eval (fun j => b j + ell j (a • v)) P := by
    dsimp only [F]
    rw [← eval_assoc]
    apply congrArg (fun w => MvPolynomial.eval w P)
    funext j
    simp [map_smul, mul_comm]
  have hF : F = 0 := by
    apply MvPolynomial.funext_set (fun _ : Fin 1 => Set.range (fun n : ℕ => (n : K)))
      (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
    intro w hw
    obtain ⟨n, hn⟩ := hw 0 (Set.mem_univ _)
    have hw' : w = fun _ => (n : K) := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using hn.symm
    rw [hw', hEval, map_zero]
    apply (G.ambient.eval_eq_zero_iff_of_lift (G.embedding (q ((n : K) • v)))
      (fun j => b j + ell j ((n : K) • v)) (hrep _) P D hP).mpr
    apply hzero
    change q ((n : K) • v) ∈ H.toAddSubgroup
    simpa only [Nat.cast_smul_eq_nsmul K, map_nsmul] using H.toAddSubgroup.nsmul_mem hv n
  have hfinal := hEval c
  rw [hF, map_zero] at hfinal
  exact (G.ambient.eval_eq_zero_iff_of_lift (G.embedding (q (c • v)))
    (fun j => b j + ell j (c • v)) (hrep _) P D hP).mp hfinal.symm

/-- In the additive cases, the actual preimage subgroup is a vector subspace;
linearity is proved from closedness and the coordinate formulas. -/
theorem AlgebraicSubgroup.exists_linear_pullback_of_affine_linear_lift
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    {G : EmbeddedGroupProduct K} (H : AlgebraicSubgroup G)
    (q : V →+ G.Point) (b : G.ambient.Variable → K)
    (ell : G.ambient.Variable → V →ₗ[K] K)
    (hrep : ∀ v : V, ∀ i : G.FactorIndex,
      ∃ h : (fun j => b ⟨i, j⟩ + ell ⟨i, j⟩ v) ≠ 0,
        Projectivization.mk K (fun j => b ⟨i, j⟩ + ell ⟨i, j⟩ v) h =
          G.embedding (q v) i) :
    ∃ W : Submodule K V, ∀ v, v ∈ W ↔ q v ∈ H.carrier := by
  refine ⟨{
    carrier := {v | q v ∈ H.carrier}
    zero_mem' := by
      change q 0 ∈ H.toAddSubgroup
      rw [map_zero]
      exact H.toAddSubgroup.zero_mem
    add_mem' := ?_
    smul_mem' := ?_
  }, fun _ => Iff.rfl⟩
  · intro v w hv hw
    change q (v + w) ∈ H.toAddSubgroup
    rw [map_add]
    exact H.toAddSubgroup.add_mem hv hw
  · intro c v hv
    exact H.smul_mem_of_affine_linear_lift q b ell hrep v hv c

end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponProjectiveNullstellensatz.lean

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

theorem homogeneousIdeal_le_vanishingIdeal_zeroLocus (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) : I ≤ M.vanishingIdeal (M.zeroLocus I) := by
  nth_rw 1 [M.homogeneousIdeal_eq_span I hI]
  apply Ideal.span_le.mpr
  rintro P ⟨hP, D, hD⟩
  exact Ideal.subset_span ⟨⟨D, hD⟩, fun x hx => hx P hP⟩

theorem mem_zeroLocus_iff_homogeneous (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (x : M.Point) :
    x ∈ M.zeroLocus I ↔
      ∀ P ∈ I, ∀ D, M.IsHomogeneous P D → M.eval P x = 0 := by
  constructor
  · exact fun h P hP _ _ => h P hP
  · intro h
    have hle : I ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
      rw [M.homogeneousIdeal_eq_span I hI]
      exact Ideal.span_le.mpr (by rintro P ⟨hP,D,hD⟩; exact h P hP D hD)
    exact fun P hP => hle hP

theorem isClosed_zeroLocus (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    @IsClosed _ M.zariskiTopology (M.zeroLocus I) := by
  letI := M.zariskiTopology
  have heq : M.zeroLocus I = M.zeroLocus (M.vanishingIdeal (M.zeroLocus I)) := by
    apply Set.Subset.antisymm
    · exact fun x hx P hP => M.eval_eq_zero_of_mem_vanishingIdeal hP hx
    · exact fun x hx P hP => hx P (M.homogeneousIdeal_le_vanishingIdeal_zeroLocus I hI hP)
  rw [heq]
  exact M.isClosed_zeroLocus_vanishingIdeal _

/-- Multiprojective Nullstellensatz for relevant homogeneous prime ideals.
An affine zero with a zero coordinate block is killed by the product of one
variable per block; on all other affine zeros, projectivization applies. -/
theorem vanishingIdeal_zeroLocus_of_relevant_prime [IsAlgClosed K]
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M q)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q) :
    M.vanishingIdeal (M.zeroLocus q) = q := by
  classical
  letI := hq
  apply le_antisymm ?_ (M.homogeneousIdeal_le_vanishingIdeal_zeroLocus q hhom)
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  have hx (i : M.FactorIndex) : ∃ j : Fin (M.ambientDimension i + 1), X ⟨i,j⟩ ∉ q := by
    by_contra! h
    apply hrel
    apply (iInf_le (Hilbert.blockIdeal K M.factorCount M.ambientDimension) i).trans
    rw [Hilbert.blockIdeal, Ideal.span_le]
    rintro _ ⟨j,rfl⟩
    exact h j
  choose j hj using hx
  let F : M.CoordinateRing := ∏ i, X ⟨i,j i⟩
  have hF : F ∉ q := by
    intro h
    obtain ⟨i,_,hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hj i hi
  have hPF : P * F ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K q) := by
    intro v hv
    change MvPolynomial.eval v (P * F) = 0
    rw [map_mul]
    by_cases hb : ∀ i : M.FactorIndex, (fun k => v ⟨i,k⟩) ≠ 0
    · apply mul_eq_zero.mpr
      left
      let x : M.Point := fun i => Projectivization.mk K (fun k => v ⟨i,k⟩) (hb i)
      have hrep : ∀ i, ∃ h : (fun k => v ⟨i,k⟩) ≠ 0,
          Projectivization.mk K (fun k => v ⟨i,k⟩) h = x i := fun i => ⟨hb i,rfl⟩
      have hxq : x ∈ M.zeroLocus q := by
        apply (M.mem_zeroLocus_iff_homogeneous q hhom x).mpr
        intro Q hQ E hE
        exact (M.eval_eq_zero_iff_of_lift x v hrep Q E hE).mp (hv Q hQ)
      exact (M.eval_eq_zero_iff_of_lift x v hrep P D hD).mpr (hP x hxq)
    · apply mul_eq_zero.mpr
      right
      push Not at hb
      obtain ⟨i,hi⟩ := hb
      change MvPolynomial.eval v (∏ k, X ⟨k,j k⟩) = 0
      rw [map_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simpa only [eval_X, Pi.zero_apply] using congrFun hi (j i)
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hPF
  exact (hq.mem_or_mem hPF).resolve_right hF

theorem zeroLocus_nonempty_of_relevant_prime [IsAlgClosed K]
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M q)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q) :
    (M.zeroLocus q).Nonempty := by
  by_contra h
  have h1 : (1 : M.CoordinateRing) ∈ M.vanishingIdeal (M.zeroLocus q) :=
    Ideal.subset_span ⟨⟨0,M.isHomogeneous_one⟩,fun x hx => (h ⟨x,hx⟩).elim⟩
  rw [M.vanishingIdeal_zeroLocus_of_relevant_prime q hq hhom hrel] at h1
  exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q h1 isUnit_one)

theorem zeroLocus_irreducible_of_relevant_prime [IsAlgClosed K]
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M q)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q) :
    @IsIrreducible _ M.zariskiTopology (M.zeroLocus q) := by
  classical
  letI := M.zariskiTopology
  refine ⟨M.zeroLocus_nonempty_of_relevant_prime q hq hhom hrel,?_⟩
  intro U V hU hV ⟨x,hx,hxU⟩ ⟨y,hy,hyV⟩
  obtain ⟨B,hB,hxB,hBU⟩ := M.isTopologicalBasis_basic.mem_nhds_iff.mp (hU.mem_nhds hxU)
  obtain ⟨C,hC,hyC,hCV⟩ := M.isTopologicalBasis_basic.mem_nhds_iff.mp (hV.mem_nhds hyV)
  obtain ⟨P,D,hP,rfl⟩ := hB
  obtain ⟨Q,E,hQ,rfl⟩ := hC
  have hPq : P ∉ q := fun h => hxB (hx P h)
  have hQq : Q ∉ q := fun h => hyC (hy Q h)
  have hPQq : P * Q ∉ q := fun h => (hq.mem_or_mem h).elim hPq hQq
  have hex : ∃ z ∈ M.zeroLocus q, M.eval (P * Q) z ≠ 0 := by
    by_contra! h
    apply hPQq
    rw [← M.vanishingIdeal_zeroLocus_of_relevant_prime q hq hhom hrel]
    exact Ideal.subset_span ⟨⟨D+E,hP.mul M hQ⟩,h⟩
  obtain ⟨z,hz,hzPQ⟩ := hex
  have hzPQ' : M.eval P z ≠ 0 ∧ M.eval Q z ≠ 0 := by
    simpa only [eval,map_mul,mul_ne_zero_iff] using hzPQ
  exact ⟨z,hz,hBU hzPQ'.1,hCV hzPQ'.2⟩

/-- A locally closed set meeting a prime component is dense in that component
when its closure contains the component. This is the restriction needed for G. -/
theorem vanishingIdeal_inter_zeroLocus_of_relevant_prime [IsAlgClosed K]
    (S : Set M.Point) (hS : @IsLocallyClosed _ M.zariskiTopology S)
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M q)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q)
    (hSq : M.vanishingIdeal S ≤ q) (hne : (S ∩ M.zeroLocus q).Nonempty) :
    M.vanishingIdeal (S ∩ M.zeroLocus q) = q := by
  letI := M.zariskiTopology
  have hzcl : M.zeroLocus q ⊆ closure S := by
    rw [← M.zeroLocus_vanishingIdeal_eq_closure]
    exact fun x hx P hP => hx P (hSq hP)
  have hinter : M.zeroLocus q ∩ coborder S = S ∩ M.zeroLocus q := by
    ext x
    constructor
    · rintro ⟨hx,hxc⟩
      exact ⟨(closure_inter_coborder (s := S) ▸ ⟨hzcl hx,hxc⟩),hx⟩
    · rintro ⟨hxS,hx⟩
      exact ⟨hx,subset_coborder hxS⟩
  have hdense : M.zeroLocus q ⊆ closure (S ∩ M.zeroLocus q) := by
    rw [← hinter]
    apply subset_closure_inter_of_isPreirreducible_of_isOpen
      (M.zeroLocus_irreducible_of_relevant_prime q hq hhom hrel).2 hS.isOpen_coborder
    rwa [hinter]
  apply le_antisymm
  · conv_rhs => rw [← M.vanishingIdeal_zeroLocus_of_relevant_prime q hq hhom hrel]
    apply Ideal.span_le.mpr
    rintro P ⟨⟨D,hD⟩,hP⟩
    exact Ideal.subset_span ⟨⟨D,hD⟩, fun x hx =>
      (closure_minimal hP (M.isClosed_zero P D hD)) (hdense hx)⟩
  · conv_lhs => rw [← M.vanishingIdeal_zeroLocus_of_relevant_prime q hq hhom hrel]
    exact M.vanishingIdeal_antitone Set.inter_subset_right

end PhilipponMultiplicity.MultiProjectiveSpace

end
end


section
-- Implementation: Solutions/PhilipponPolynomialIdealHomogeneous.lean

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

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem polynomialOperatorIdeal_homogeneous (atlas : TranslationAtlas A g) (T : ℕ)
    (I : Ideal G.CoordinateRing) : IsMultihomogeneousIdeal G.ambient (polynomialOperatorIdeal atlas T I) := by
  unfold polynomialOperatorIdeal EmbeddedGroupProduct.vanishingIdeal MultiProjectiveSpace.vanishingIdeal
  rw [← Ideal.span_union]
  apply homogeneous_span
  rintro Q (hQ | ⟨P,hPI,⟨D,hD⟩,a,n,hn,dirs,rfl⟩)
  · exact hQ.1
  · exact ⟨fun i => (atlas.chart a).degree i * D i,
      polynomialOperator_homogeneous (atlas.chart a) n dirs P D hD⟩

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponProjectiveHilbertExistence.lean

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
-- Implementation: Solutions/PhilipponPrimeFiltration.lean

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

/-- The homogeneous product criterion also detects ordinary primality for
the block grading. A lexicographic order is used only to apply that criterion. -/
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
-- Implementation: Solutions/PhilipponHomogeneousOperations.lean

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
-- Implementation: Solutions/PhilipponJetIdeal.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem natCast_lt_jetOrder_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    (f : E → K) (x : E) (k : ℕ) :
    (k : WithTop ℕ) < jetOrder f x ↔ ∀ n ≤ k, iteratedFDeriv K n f x = 0 := by
  have h (r : WithTop ℕ) : (k : WithTop ℕ) < r ↔ ((k + 1 : ℕ) : WithTop ℕ) ≤ r := by
    exact (ENat.natCast_add_one_le_iff (m := k) (n := r)).symm
  rw [h, natCast_le_jetOrder_iff]
  simp only [Nat.lt_succ_iff]

theorem derivative_eq_zero_iff_basis {d n : ℕ}
    (L : ContinuousMultilinearMap K (fun _ : Fin n => Fin d → K) K) :
    L = 0 ↔ ∀ directions : Fin n → Fin d, L (fun i => Pi.single (directions i) 1) = 0 := by
  constructor
  · intro h
    simp [h]
  · intro h
    have heq : L.toMultilinearMap = (0 : MultilinearMap K (fun _ : Fin n => Fin d → K) K) := by
      apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun K (Fin d))
      intro directions
      simpa using h directions
    ext x
    exact congrArg (fun f : MultilinearMap K (fun _ : Fin n => Fin d → K) K => f x) heq

theorem pullback_analytic (A : AnalyticSubgroup G) (P : G.CoordinateRing) (g : G.Point) :
    AnalyticAt K (A.pullback P g) 0 := by
  exact AnalyticAt.aeval_mvPolynomial (A.lift_analytic g) P

/-- Polynomials whose full finite jets vanish at the specified translate. -/
def jetIdeal (A : AnalyticSubgroup G) (g : G.Point) (k : ℕ) : Ideal G.CoordinateRing where
  carrier := {P | ∀ n ≤ k, iteratedFDeriv K n (A.pullback P g) 0 = 0}
  zero_mem' := by
    intro n hn
    change iteratedFDeriv K n (fun z => MvPolynomial.eval (A.lift g z) (0 : G.CoordinateRing)) 0 = 0
    simp
  add_mem' := by
    intro P Q hP hQ n hn
    change iteratedFDeriv K n (fun z => MvPolynomial.eval (A.lift g z) (P + Q)) 0 = 0
    simp only [map_add]
    calc
      _ = iteratedFDeriv K n (A.pullback P g) 0 + iteratedFDeriv K n (A.pullback Q g) 0 :=
        fun_iteratedFDeriv_add_apply (pullback_analytic A P g).contDiffAt
          (pullback_analytic A Q g).contDiffAt
      _ = 0 := by rw [hP n hn, hQ n hn, add_zero]
  smul_mem' := by
    intro Q P hP n hn
    change iteratedFDeriv K n (fun z => MvPolynomial.eval (A.lift g z) (Q * P)) 0 = 0
    simp only [map_mul]
    exact iteratedFDeriv_mul_eq_zero_of_vanishing_jet
      (pullback_analytic A P g).contDiffAt (pullback_analytic A Q g).contDiffAt
      (fun i hi => hP i (hi.trans hn))

theorem mem_jetIdeal_iff (A : AnalyticSubgroup G) (g : G.Point) (k : ℕ)
    (P : G.CoordinateRing) : P ∈ jetIdeal A g k ↔ (k : WithTop ℕ) < vanishingOrder A P g :=
  (natCast_lt_jetOrder_iff (A.pullback P g) 0 k).symm

/-- Closure under homogeneous projections reduces ideal containment to
homogeneous polynomials, without adding any hypothesis on the ideal. -/
theorem homogeneousIdeal_le_of_homogeneous (M : MultiProjectiveSpace K)
    (I J : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (h : ∀ P ∈ I, (∃ D, M.IsHomogeneous P D) → P ∈ J) : I ≤ J := by
  classical
  intro P hP
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  rw [← sum_weightedHomogeneousComponent w P,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) P)]
  apply J.sum_mem
  intro D _
  apply h _ (hI P hP D)
  exact ⟨D,(M.degreePiece_iff _ D).mp (weightedHomogeneousComponent_mem w P D)⟩

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponRetentionZeros.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

/-- Retention preserves the vanishing test at each genuine homogeneous
representative. This follows from the literal localization definition. -/
theorem retainOnGroup_le_point_iff (J : Ideal G.CoordinateRing)
    (x : GroupHomogeneousRepresentative G) :
    retainOnGroup G J ≤ (representativeMaximalIdeal G x).asIdeal ↔
      J ≤ (representativeMaximalIdeal G x).asIdeal := by
  constructor
  · exact fun h => (le_retainOnGroup G J).trans h
  · intro hJ P hP
    let m := representativeMaximalIdeal G x
    have hle : retainOnGroup G J ≤ retainAtRepresentative G J x :=
      iInf_le (fun y : GroupHomogeneousRepresentative G => retainAtRepresentative G J y) x
    have hx : P ∈ retainAtRepresentative G J x := hle hP
    change algebraMap G.CoordinateRing (Localization.AtPrime m.asIdeal) P ∈
      J.map (algebraMap G.CoordinateRing (Localization.AtPrime m.asIdeal)) at hx
    obtain ⟨s,hs,hsp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      m.asIdeal.primeCompl (Localization.AtPrime m.asIdeal) J P).mp hx
    exact (m.isMaximal.isPrime.mem_or_mem (hJ hsp)).resolve_left hs

theorem retainOnGroup_zero_iff (J : Ideal G.CoordinateRing) (x : G.Point) :
    (∀ P ∈ retainOnGroup G J, G.ambient.eval P (G.embedding x) = 0) ↔
      ∀ P ∈ J, G.ambient.eval P (G.embedding x) = 0 := by
  change (retainOnGroup G J ≤ (representativeMaximalIdeal G (representativeOfPoint G x)).asIdeal) ↔
    J ≤ (representativeMaximalIdeal G (representativeOfPoint G x)).asIdeal
  exact retainOnGroup_le_point_iff G J (representativeOfPoint G x)

theorem retainedOperator_zero_iff {A : AnalyticSubgroup G} {g : G.Point}
    (atlas : TranslationAtlas A g) (k : ℕ) (I : Ideal G.CoordinateRing) (x : G.Point) :
    (∀ Q ∈ retainedPolynomialOperatorIdeal atlas k I, G.ambient.eval Q (G.embedding x) = 0) ↔
    ∀ P ∈ I, (∃ D, G.ambient.IsHomogeneous P D) → ∀ a : atlas.Index,
      ∀ n ≤ k, ∀ directions : Fin n → Fin A.parameterDimension,
        G.ambient.eval (polynomialOperator (atlas.chart a) n directions P) (G.embedding x) = 0 := by
  rw [retainedPolynomialOperatorIdeal, retainOnGroup_zero_iff]
  change polynomialOperatorIdeal atlas k I ≤ RingHom.ker
    (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) ↔ _
  rw [polynomialOperatorIdeal, sup_le_iff, Ideal.span_le]
  have hG : G.vanishingIdeal Set.univ ≤ RingHom.ker
      (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
    apply Ideal.span_le.mpr
    rintro P ⟨_,hP⟩
    exact hP (G.embedding x) ⟨x,Set.mem_univ _,rfl⟩
  constructor
  · rintro ⟨_,h⟩ P hPI hPh a n hn directions
    exact h ⟨P,hPI,hPh,a,n,hn,directions,rfl⟩
  · intro h
    refine ⟨hG,?_⟩
    rintro Q ⟨P,hPI,hPh,a,n,hn,directions,rfl⟩
    exact h P hPI hPh a n hn directions

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponOperatorContact.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

/-- Even off its own domain, a chart gives an analytic scalar multiple of
the intrinsic pullback. The scalar need not be a unit off the chart. -/
theorem chart_pullback_analytic_multiple (chart : TranslationChart A g)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : G.Point) :
    ∃ u : A.ParameterSpace → K, AnalyticAt K u 0 ∧
      (fun z => MvPolynomial.eval
        (fun v => evaluateCoefficientPolynomial A (chart.coordinates v) x z) P) =ᶠ[𝓝 0]
        (fun z => u z * A.pullback P (g + x) z) := by
  classical
  have hpivot (i : G.FactorIndex) : ∃ j, A.lift (g + x) 0 ⟨i,j⟩ ≠ 0 := by
    obtain ⟨_,hi⟩ := (A.lift_represents (g + x)).self_of_nhds
    obtain ⟨hne,_⟩ := hi i
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hne
  choose b hb using hpivot
  let a (z : A.ParameterSpace) (i : G.FactorIndex) :=
    evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z / A.lift (g + x) z ⟨i,b i⟩
  let u (z : A.ParameterSpace) := ∏ i, a z i ^ D i
  have ha (i : G.FactorIndex) : AnalyticAt K (fun z => a z i) 0 :=
    (chart_evaluation_analytic chart x _).div (A.lift_analytic (g + x) _) (hb i)
  refine ⟨u,Finset.analyticAt_fun_prod _ (fun i _ => (ha i).pow _),?_⟩
  have hnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ i : G.FactorIndex, A.lift (g + x) z ⟨i,b i⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (A.lift_analytic (g + x) _).continuousAt.eventually_ne (hb i)
  have hcompat : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ v : G.ambient.Variable,
      evaluateCoefficientPolynomial A (chart.coordinates v) x z * A.lift (g + x) z ⟨v.1,b v.1⟩ =
        evaluateCoefficientPolynomial A (chart.coordinates ⟨v.1,b v.1⟩) x z * A.lift (g + x) z v := by
    rw [Filter.eventually_all]
    intro v
    exact chart.coordinate_compatible x v.1 v.2 (b v.1)
  filter_upwards [hnear,hcompat] with z hz hc
  have hcoords : (fun v => evaluateCoefficientPolynomial A (chart.coordinates v) x z) =
      fun v => a z v.1 * A.lift (g + x) z v := by
    funext v
    dsimp [a]
    apply (mul_right_cancel₀ (hz v.1))
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (hz v.1)]
    exact hc v
  rw [hcoords,G.ambient.eval_block_scale P D hP]
  rfl

theorem operator_zero_of_contact (chart : TranslationChart A g)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : G.Point) (k : ℕ) (hcontact : (k : WithTop ℕ) < vanishingOrder A P (g + x))
    (n : ℕ) (hn : n ≤ k) (directions : Fin n → Fin A.parameterDimension) :
    G.ambient.eval (polynomialOperator chart n directions P) (G.embedding x) = 0 := by
  obtain ⟨u,hu,heq⟩ := chart_pullback_analytic_multiple chart P D hP x
  have hj := (natCast_lt_jetOrder_iff (A.pullback P (g + x)) 0 k).mp hcontact
  rw [polynomialOperator_eval, (heq.iteratedFDeriv K n).eq_of_nhds,
    iteratedFDeriv_mul_eq_zero_of_vanishing_jet (pullback_analytic A P (g + x)).contDiffAt
      hu.contDiffAt (fun i hi => hj i (hi.trans hn))]
  rfl

end PhilipponMultiplicity.OperatorSupport

namespace PhilipponMultiplicity
open OperatorSupport

/-- Proposition 4.4: zeros of the actual retained polynomial operator ideal
are exactly the points where every original equation has the required contact. -/
theorem proposition_4_4
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g h : G.Point) (k : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (atlas : TranslationAtlas A g) :
    (∀ Q ∈ retainedPolynomialOperatorIdeal atlas k I,
      G.ambient.eval Q (G.embedding h) = 0) ↔
    (∀ Q ∈ I, (k : WithTop ℕ) < vanishingOrder A Q (g + h)) := by
  letI : CompleteSpace K := hK.completeSpace
  rw [retainedOperator_zero_iff]
  constructor
  · intro hop
    have hle : I ≤ jetIdeal A (g + h) k := by
      apply homogeneousIdeal_le_of_homogeneous G.ambient I _ hI
      rintro P hPI ⟨D,hP⟩
      apply (mem_jetIdeal_iff A (g + h) k P).mpr
      obtain ⟨a,ha⟩ := atlas.covers h
      rw [projective_lift_contact_invariance K hK G A (g + h) P D hP
        (fun z v => evaluateCoefficientPolynomial A ((atlas.chart a).coordinates v) h z)
        (chart_evaluation_analytic (atlas.chart a) h)
        (by simpa only [add_comm h g] using (atlas.chart a).represents h ha)]
      apply (natCast_lt_jetOrder_iff _ 0 k).mpr
      intro n hn
      apply (derivative_eq_zero_iff_basis _).mpr
      intro directions
      rw [← polynomialOperator_eval]
      exact hop P hPI ⟨D,hP⟩ a n hn directions
    exact fun Q hQ => (mem_jetIdeal_iff A (g + h) k Q).mp (hle hQ)
  · intro hcontact P hPI hPh a n hn directions
    obtain ⟨D,hP⟩ := hPh
    exact operator_zero_of_contact (atlas.chart a) P D hP h k (hcontact P hPI) n hn directions

end PhilipponMultiplicity

end
end


section
-- Implementation: Solutions/PhilipponSectionFiveChain.lean
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem zero_mem_sumset {X : Type*} [AddCommGroup X]
    (S : Finset X) (h0 : 0 ∈ S) (n : ℕ) : 0 ∈ sumset S n := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(fun _ => ⟨0,h0⟩),Finset.mem_univ _,by simp⟩

theorem sumset_mono {X : Type*} [AddCommGroup X]
    (S : Finset X) (h0 : 0 ∈ S) : Monotone (sumset S) := by
  classical
  apply monotone_nat_of_le_succ
  intro n x hx
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  refine ⟨Fin.cons ⟨0,h0⟩ f,Finset.mem_univ _,?_⟩
  simp [Fin.sum_univ_succ]

variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}
open OperatorSupport

theorem groupIdeal_le_pointKernel (x : G.Point) :
    G.vanishingIdeal Set.univ ≤ RingHom.ker
      (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
  exact fun P hP => G.ambient.eval_eq_zero_of_mem_vanishingIdeal hP
    (Set.mem_image_of_mem G.embedding (Set.mem_univ x))

theorem SectionFiveInput.groupIdeal_le_chain (C : SectionFiveInput G A) (n : ℕ) :
    G.vanishingIdeal Set.univ ≤ C.idealChain n := by
  cases n with
  | zero => exact le_rfl
  | succ n => cases n <;> exact le_sup_left

theorem SectionFiveInput.chain_homogeneous [CompleteSpace K]
    (C : SectionFiveInput G A) (n : ℕ) :
    IsMultihomogeneousIdeal G.ambient (C.idealChain n) := by
  cases n with
  | zero => exact vanishingIdeal_multihomogeneous K _ _
  | succ n =>
    cases n with
    | zero =>
      exact Hilbert.homogeneous_sup_span G.ambient _ (vanishingIdeal_multihomogeneous K _ _)
        C.polynomial C.degrees C.polynomial_homogeneous
    | succ n =>
      simp only [idealChain]
      unfold EmbeddedGroupProduct.vanishingIdeal MultiProjectiveSpace.vanishingIdeal
      rw [← Ideal.span_union]
      apply homogeneous_span
      rintro Q (hQ | ⟨g,hg,a,k,hk,dirs,rfl⟩)
      · exact hQ.1
      · exact ⟨_,polynomialOperator_homogeneous _ _ _ _ _ C.polynomial_homogeneous⟩


end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponHomogeneousPrimary.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.PrimarySupport

variable {R S : Type*} [CommRing R] [CommRing S]

theorem primary_bot_of_injective (f : R →+* S) (hf : Function.Injective f)
    (h : (⊥ : Ideal S).IsPrimary) : (⊥ : Ideal R).IsPrimary := by
  have heq : (⊥ : Ideal S).comap f = ⊥ := by
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact map_eq_zero_iff f hf
  rw [← heq]
  exact h.comap f

theorem primary_bot_quotient (Q : Ideal R) (hQ : Q.IsPrimary) :
    (⊥ : Ideal (R ⧸ Q)).IsPrimary := by
  haveI : Nontrivial (R ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr hQ.ne_top
  refine Ideal.isPrimary_iff.mpr ⟨bot_ne_top, ?_⟩
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hab : a * b ∈ Q := by
    simpa only [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] using hxy
  rcases (Ideal.isPrimary_iff.mp hQ).2 hab with ha | hb
  · left
    simpa only [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] using ha
  · right
    obtain ⟨n, hn⟩ := hb
    exact ⟨n, by simpa only [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] using hn⟩

/-- McCoy's theorem makes zero-primaryness stable under adjoining one variable. -/
theorem primary_bot_polynomial (hR : (⊥ : Ideal R).IsPrimary) :
    (⊥ : Ideal (Polynomial R)).IsPrimary := by
  haveI : Nontrivial R := nontrivial_of_ne (x := (0 : R)) (y := 1) (by
    intro h
    exact (Ideal.ne_top_iff_one _).mp hR.ne_top h.symm)
  refine Ideal.isPrimary_iff.mpr ⟨bot_ne_top, ?_⟩
  intro P Q hPQ
  by_cases hP : P = 0
  · exact Or.inl hP
  right
  have hQ : Q ∉ nonZeroDivisors (Polynomial R) := by
    intro hQ
    exact hP (hQ.2 P hPQ)
  obtain ⟨a, ha, h⟩ := Polynomial.notMem_nonZeroDivisors_iff.mp hQ
  have hnil : IsNilpotent Q := by
    apply Polynomial.isNilpotent_iff.mpr
    intro i
    have hzero : a * Q.coeff i = 0 := by
      simpa only [Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_zero] using
        congrArg (fun f : Polynomial R => f.coeff i) h
    have hm := ((Ideal.isPrimary_iff.mp hR).2 hzero).resolve_left ha
    exact hm
  exact hnil

/-- Polynomial extension in finitely many variables preserves a primary zero ideal. -/
theorem primary_bot_mvPolynomial {σ : Type*} [Finite σ]
    (hR : (⊥ : Ideal R).IsPrimary) : (⊥ : Ideal (MvPolynomial σ R)).IsPrimary := by
  classical
  refine have := Fintype.ofFinite σ; Fintype.induction_empty_option ?_ ?_ ?_ σ
  · intro α β _ e ih
    exact primary_bot_of_injective (MvPolynomial.renameEquiv R e.symm).toRingHom
      (MvPolynomial.renameEquiv R e.symm).injective ih
  · exact primary_bot_of_injective (MvPolynomial.isEmptyRingEquiv R PEmpty).toRingHom
      (MvPolynomial.isEmptyRingEquiv R PEmpty).injective hR
  · intro α _ ih
    exact primary_bot_of_injective (MvPolynomial.optionEquivLeft R α).toRingHom
      (MvPolynomial.optionEquivLeft R α).injective (primary_bot_polynomial ih)

open MvPolynomial
open Finsupp (weight weight_apply)
variable {σ τ : Type*} {K : Type*} [CommRing K]

/-- The coefficient of the auxiliary monomial of degree `d` is the actual
weighted homogeneous component of degree `d`. -/
def degreeTag (w : σ → (τ →₀ ℕ)) :
    MvPolynomial σ K →+* MvPolynomial τ (MvPolynomial σ K) :=
  eval₂Hom (C.comp C) (fun x => monomial (w x) (X x))

theorem degreeTag_monomial (w : σ → (τ →₀ ℕ)) (e : σ →₀ ℕ) (c : K) :
    degreeTag w (monomial e c) = monomial (weight w e) (monomial e c) := by
  classical
  simp only [degreeTag, eval₂Hom_monomial, RingHom.coe_comp, Function.comp_apply,
    monomial_pow, weight_apply, Finsupp.sum, Finsupp.prod]
  rw [← monomial_sum_prod]
  rw [monomial_eq (s := e) (a := c), C_mul_monomial]
  rfl

theorem degreeTag_coeff (w : σ → (τ →₀ ℕ)) (f : MvPolynomial σ K) (d : τ →₀ ℕ) :
    coeff d (degreeTag w f) = weightedHomogeneousComponent w d f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, coeff_add, hf, hg]
  | monomial e c =>
    rw [degreeTag_monomial, coeff_monomial]
    ext a
    simp only [coeff_weightedHomogeneousComponent, coeff_monomial]
    split_ifs <;> simp_all <;> aesop

/-- Homogeneous core expressed as the kernel of a map into a polynomial ring
with coefficients in the quotient by `Q`. -/
def weightedCore (w : σ → (τ →₀ ℕ)) (Q : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial σ K) :=
  RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk Q)).comp (degreeTag w))

theorem mem_weightedCore (w : σ → (τ →₀ ℕ)) (Q : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) :
    f ∈ weightedCore w Q ↔ ∀ d, weightedHomogeneousComponent w d f ∈ Q := by
  simp only [weightedCore, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
    MvPolynomial.ext_iff, coeff_map, coeff_zero, degreeTag_coeff,
    Ideal.Quotient.eq_zero_iff_mem]

theorem weightedCore_primary [Finite τ] (w : σ → (τ →₀ ℕ))
    (Q : Ideal (MvPolynomial σ K)) (hQ : Q.IsPrimary) :
    (weightedCore w Q).IsPrimary :=
  (primary_bot_mvPolynomial (σ := τ) (primary_bot_quotient Q hQ)).comap
    ((MvPolynomial.map (Ideal.Quotient.mk Q)).comp (degreeTag w))

theorem weightedCore_le (w : σ → (τ →₀ ℕ)) (Q : Ideal (MvPolynomial σ K)) :
    weightedCore w Q ≤ Q := by
  classical
  intro f hf
  have h := (mem_weightedCore w Q f).mp hf
  rw [← sum_weightedHomogeneousComponent w f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) f)]
  exact Q.sum_mem fun d _ => h d

/-- A homogeneous decomposition can be made irredundant and have distinct
radicals without losing any property closed under finite intersections. -/
theorem minimal_primary_with_property (P : Ideal R → Prop)
    (hP : ∀ s : Finset (Ideal R), (∀ J ∈ s, P J) → P (s.inf id))
    {I : Ideal R} {s : Finset (Ideal R)} (hs : s.inf id = I)
    (hsprimary : ∀ J ∈ s, J.IsPrimary) (hsP : ∀ J ∈ s, P J) :
    ∃ t : Finset (Ideal R), Submodule.IsMinimalPrimaryDecomposition I t ∧ ∀ J ∈ t, P J := by
  classical
  let t : Finset (Ideal R) :=
    (s.image fun J => s.filter fun Q => Q.radical = J.radical).image fun u => u.inf id
  have ht : t.inf id = I := by
    ext x
    simp only [t, Finset.inf_image, Submodule.mem_finsetInf, Finset.mem_filter,
      Function.comp_def, id_eq]
    rw [← hs]
    simp only [Submodule.mem_finsetInf, id_eq]
    constructor
    · intro h Q hQ
      exact h Q hQ Q ⟨hQ, rfl⟩
    · intro h J hJ Q hQ
      exact h Q hQ.1
  have htprimary : ∀ J ∈ t, J.IsPrimary := by
    intro J hJ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
    apply Ideal.isPrimary_finsetInf (i := Q) (by simp [hQ])
    · intro T hT
      exact hsprimary T (Finset.mem_filter.mp hT).1
    · simp
  have htP : ∀ J ∈ t, P J := by
    intro J hJ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
    exact hP _ fun T hT => hsP T (Finset.mem_filter.mp hT).1
  have htdistinct : (t : Set (Ideal R)).Pairwise
      (fun A B => (A.colon Set.univ).radical ≠ (B.colon Set.univ).radical) := by
    intro A hA B hB hne heq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hv
    have hrQ : ((s.filter fun U => U.radical = Q.radical).inf id).radical = Q.radical := by
      exact Ideal.radical_finset_inf (i := Q) (by simp [hQ]) (by simp)
    have hrT : ((s.filter fun U => U.radical = T.radical).inf id).radical = T.radical := by
      exact Ideal.radical_finset_inf (i := T) (by simp [hT]) (by simp)
    simp only [Submodule.colon_univ, hrQ, hrT] at heq
    exact hne (by simp only [heq])
  obtain ⟨u, hut, hu, humin⟩ := Submodule.decomposition_erase_inf ht
  exact ⟨u, ⟨hu, fun _ h => htprimary _ (hut h), htdistinct.mono hut, humin⟩,
    fun J hJ => htP J (hut hJ)⟩

end PhilipponMultiplicity.PrimarySupport


namespace PhilipponMultiplicity.PrimarySupport
open MvPolynomial
open Finsupp (weight weight_apply)
open Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

def blockCore (Q : Ideal M.CoordinateRing) : Ideal M.CoordinateRing :=
  weightedCore (fun x => (Finsupp.equivFunOnFinite).symm
    (blockWeight M.factorCount M.ambientDimension x)) Q

theorem blockCore_projection (f : M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    weightedHomogeneousComponent
      (fun x => (Finsupp.equivFunOnFinite).symm
        (blockWeight M.factorCount M.ambientDimension x))
      ((Finsupp.equivFunOnFinite).symm d) f =
    weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d f := by
  classical
  have hw (e : M.Variable →₀ ℕ) :
      weight (fun x => (Finsupp.equivFunOnFinite).symm
          (blockWeight M.factorCount M.ambientDimension x)) e =
        (Finsupp.equivFunOnFinite).symm
          (weight (blockWeight M.factorCount M.ambientDimension) e) := by
    ext i
    simp [weight_apply, Finsupp.sum, Finset.sum_apply]
  ext e
  simp only [coeff_weightedHomogeneousComponent, hw, Equiv.apply_eq_iff_eq]

theorem mem_blockCore (Q : Ideal M.CoordinateRing) (f : M.CoordinateRing) :
    f ∈ blockCore M Q ↔ ∀ d : M.FactorIndex → ℕ,
      weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d f ∈ Q := by
  rw [blockCore, mem_weightedCore]
  constructor
  · intro h d
    simpa only [blockCore_projection M] using h ((Finsupp.equivFunOnFinite).symm d)
  · intro h d
    obtain ⟨d, rfl⟩ := (Finsupp.equivFunOnFinite).symm.surjective d
    simpa only [blockCore_projection M] using h d

theorem blockCore_homogeneous (Q : Ideal M.CoordinateRing) :
    IsMultihomogeneousIdeal M (blockCore M Q) := by
  classical
  intro f hf d
  apply (mem_blockCore M Q _).mpr
  intro e
  rw [weightedHomogeneousComponent_of_mem (weightedHomogeneousComponent_mem _ f d)]
  split_ifs
  · exact (mem_blockCore M Q f).mp hf d
  · exact Q.zero_mem

theorem homogeneous_finsetInf (s : Finset (Ideal M.CoordinateRing))
    (hs : ∀ J ∈ s, IsMultihomogeneousIdeal M J) :
    IsMultihomogeneousIdeal M (s.inf id) := by
  intro f hf d
  simp only [Submodule.mem_finsetInf, id_eq] at hf ⊢
  exact fun J hJ => hs J hJ f (hf J hJ) d

theorem exists_minimal_homogeneous_primary (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    ∃ t : Finset (Ideal M.CoordinateRing),
      Submodule.IsMinimalPrimaryDecomposition I t ∧
      ∀ J ∈ t, IsMultihomogeneousIdeal M J := by
  classical
  obtain ⟨s, hs, hsprimary⟩ := Submodule.isLasker M.CoordinateRing M.CoordinateRing I
  let t := s.image (blockCore M)
  have ht : t.inf id = I := by
    apply le_antisymm
    · rw [← hs]
      apply Finset.le_inf_iff.mpr
      intro J hJ
      exact (Finset.inf_le (Finset.mem_image.mpr ⟨J, hJ, rfl⟩)).trans
        (weightedCore_le _ J)
    · apply Finset.le_inf_iff.mpr
      intro J hJ
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hJ
      intro f hf
      apply (mem_blockCore M Q f).mpr
      intro d
      have hIQ : I ≤ Q := hs.symm.le.trans (Finset.inf_le hQ)
      exact hIQ (hI f hf d)
  apply minimal_primary_with_property (IsMultihomogeneousIdeal M) (homogeneous_finsetInf M) ht
  · intro J hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hJ
    exact weightedCore_primary _ Q (hsprimary hQ)
  · intro J hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hJ
    exact blockCore_homogeneous M Q

end PhilipponMultiplicity.PrimarySupport


namespace PhilipponMultiplicity.SectionThreeSupport
open PrimarySupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- A finite minimal decomposition by actual multihomogeneous primary ideals,
over any field and including the whole-ring case with an empty family. -/
theorem exists_primaryDecomposition (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) : Nonempty (PrimaryDecomposition M I) := by
  classical
  obtain ⟨s, hs, hshom⟩ := exists_minimal_homogeneous_primary M I hI
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  have hiInf : (⨅ i : Fin (Fintype.card s), (e i).1) = s.inf id := by
    ext f
    simp only [Submodule.mem_iInf, Submodule.mem_finsetInf, id_eq]
    constructor
    · intro h J hJ
      obtain ⟨i, hi⟩ := e.surjective ⟨J, hJ⟩
      have := h i
      simpa only [hi] using this
    · intro h i
      exact h _ (e i).2
  refine ⟨{
    count := Fintype.card s
    component := fun i => (e i).1
    primary := fun i => hs.primary (e i).2
    homogeneous := fun i => hshom _ (e i).2
    intersection_eq := hs.inf_eq.symm.trans hiInf.symm
    irredundant := ?_
    radicals_injective := ?_ }⟩
  · intro i heq
    apply hs.minimal (e i).2
    calc
      (s.erase (e i).1).inf id ≤ ⨅ j : {j : Fin (Fintype.card s) // j ≠ i},
          (e j.1).1 := by
        apply le_iInf
        intro j
        apply Finset.inf_le
        refine Finset.mem_erase.mpr ⟨?_, (e j.1).2⟩
        exact fun h => j.2 (e.injective (Subtype.ext h))
      _ = I := heq
      _ ≤ (e i).1 := hs.inf_eq.symm.le.trans (Finset.inf_le (e i).2)
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    apply hs.injOn I s (e i).2 (e j).2
    simpa only [Submodule.colon_univ] using hij

end PhilipponMultiplicity.SectionThreeSupport

end
end


section
-- Implementation: Solutions/PhilipponRetentionPrimary.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
open SectionThreeSupport
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

theorem retainAtRepresentative_iInf {ι : Type*} [Finite ι]
    (J : ι → Ideal G.CoordinateRing) (x : GroupHomogeneousRepresentative G) :
    retainAtRepresentative G (⨅ i, J i) x = ⨅ i, retainAtRepresentative G (J i) x := by
  classical
  letI := Fintype.ofFinite ι
  let S := (representativeMaximalIdeal G x).asIdeal.primeCompl
  let B := Localization.AtPrime (representativeMaximalIdeal G x).asIdeal
  have hm : (⨅ i, J i).map (algebraMap G.CoordinateRing B) =
      ⨅ i, (J i).map (algebraMap G.CoordinateRing B) := by
    simpa only [Finset.inf_univ_eq_iInf, Function.comp_def, IsLocalization.mapFrameHom_apply]
      using map_finset_inf (IsLocalization.mapFrameHom S B) Finset.univ J
  unfold retainAtRepresentative
  rw [hm]
  exact Ideal.comap_iInf _ _

theorem retainAtRepresentative_primary (J : Ideal G.CoordinateRing) (hJ : J.IsPrimary)
    (x : GroupHomogeneousRepresentative G) :
    retainAtRepresentative G J x = (by
      classical
      exact if J ≤ (representativeMaximalIdeal G x).asIdeal then J else ⊤) := by
  classical
  split_ifs with hx
  · exact IsLocalization.under_map_of_isPrimary_disjoint
      (representativeMaximalIdeal G x).asIdeal.primeCompl
      (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal) hJ
      (Set.disjoint_left.mpr fun s hs hsi => hs (hx hsi))
  · unfold retainAtRepresentative
    rw [IsLocalization.AtPrime.map_eq_top_of_not_le
      (S := Localization.AtPrime (representativeMaximalIdeal G x).asIdeal) hx]
    exact Ideal.comap_top

/-- Definition 4.2: retention keeps exactly the actual primary components
whose support contains a genuine homogeneous representative of a group point. -/
theorem retainOnGroup_eq_primaryDecomposition (I : Ideal G.CoordinateRing)
    (D : PrimaryDecomposition G.ambient I) :
    retainOnGroup G I =
      ⨅ i : {i : Fin D.count // ∃ x : GroupHomogeneousRepresentative G,
        D.component i ≤ (representativeMaximalIdeal G x).asIdeal}, D.component i.1 := by
  classical
  conv_lhs => rw [D.intersection_eq]
  unfold retainOnGroup
  simp_rw [retainAtRepresentative_iInf]
  rw [iInf_comm]
  apply le_antisymm
  · apply le_iInf
    rintro ⟨i, x, hx⟩
    apply le_trans (iInf_le (fun j => ⨅ x, retainAtRepresentative G (D.component j) x) i)
    apply le_trans (iInf_le (fun y => retainAtRepresentative G (D.component i) y) x)
    rw [retainAtRepresentative_primary G _ (D.primary i) x, if_pos hx]
  · apply le_iInf
    intro i
    apply le_iInf
    intro x
    rw [retainAtRepresentative_primary G _ (D.primary i) x]
    split_ifs with hx
    · exact iInf_le (fun j : {j : Fin D.count // ∃ x : GroupHomogeneousRepresentative G,
        D.component j ≤ (representativeMaximalIdeal G x).asIdeal} => D.component j.1) ⟨i,x,hx⟩
    · exact le_top

theorem retainOnGroup_homogeneous (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) :
    IsMultihomogeneousIdeal G.ambient (retainOnGroup G I) := by
  obtain ⟨D⟩ := exists_primaryDecomposition G.ambient I hI
  rw [retainOnGroup_eq_primaryDecomposition G I D]
  intro P hP d
  simp only [Submodule.mem_iInf] at hP ⊢
  intro i
  exact D.homogeneous i.1 P (hP i) d

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponColonHilbert.lean

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
-- Implementation: Solutions/PhilipponDifferentialVanishing.lean

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

theorem chartValue_homogeneous (b : CoordinateChart G) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) (x : G.Point) :
    chartValue G b P x =
      (∏ i, ((G.embedding x i).rep (b i))⁻¹ ^ D i) * G.ambient.eval P (G.embedding x) := by
  unfold chartValue
  calc
    _ = MvPolynomial.eval
        (fun v : G.ambient.Variable =>
          ((G.embedding x v.1).rep (b v.1))⁻¹ * (G.embedding x v.1).rep v.2) P := by
      apply congrArg (fun v : G.ambient.Variable → K => MvPolynomial.eval v P)
      funext v
      exact div_eq_inv_mul _ _
    _ = _ := G.ambient.eval_block_scale P D hP (G.ambient.coordinate (G.embedding x))
      (fun i : G.FactorIndex => ((G.embedding x i).rep (b i))⁻¹)

theorem locallyGeneratedIdeal_of_zero_sections (S : Set (LocalSection G))
    (hS : ∀ f ∈ S, ∀ x ∈ f.domain, f.value x = 0) :
    locallyGeneratedIdeal G S = G.vanishingIdeal Set.univ := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro P ⟨⟨D, hD⟩, hP⟩
    apply Ideal.subset_span
    refine ⟨⟨D, hD⟩, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    obtain ⟨b, U, hU, hx, hsub, n, f, r, hfr, heq⟩ := hP x
    have hz : chartValue G b P x = 0 := by
      rw [heq x hx]
      apply Finset.sum_eq_zero
      intro i _
      rw [hS _ (f i).property x (hfr i x hx).1, mul_zero]
    rw [chartValue_homogeneous b P D hD x] at hz
    exact (mul_eq_zero.mp hz).resolve_left
      (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (inv_ne_zero (hsub hx i))))
  · apply Ideal.span_le.mpr
    rintro P ⟨⟨D, hD⟩, hP⟩
    apply Ideal.subset_span
    refine ⟨⟨D, hD⟩, ?_⟩
    intro x
    obtain ⟨b, hb⟩ := exists_chartDomain x
    refine ⟨b, chartDomain G b, chartDomain_isOpen b, hb, Set.Subset.rfl,
      0, Fin.elim0, Fin.elim0, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro y hy
      rw [chartValue_homogeneous b P D hD y, hP _ ⟨y, Set.mem_univ y, rfl⟩, mul_zero]
      simp

theorem normalizedJet_vanishingIdeal (A : AnalyticSubgroup G) (g : G.Point)
    (P : G.CoordinateRing) (hP : P ∈ G.vanishingIdeal Set.univ)
    (D : G.FactorIndex → ℕ) (hD : G.ambient.IsHomogeneous P D)
    (b : CoordinateChart G) {T : ℕ} (j : JetIndex A.parameterDimension T) (x : G.Point) :
    normalizedJet A g b P j x = 0 := by
  have hz : normalizedPullback A g b P x =ᶠ[𝓝 0] (fun _ => (0 : K)) := by
    filter_upwards [A.lift_represents (g + x)] with z hz
    obtain ⟨hz, hlift⟩ := hz
    have hzero : MvPolynomial.eval (A.lift (g + x) z) P = 0 :=
      G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
        (Set.mem_image_of_mem G.embedding (Set.mem_univ _)) _ hlift hP
    unfold normalizedPullback
    calc
      _ = MvPolynomial.eval
          (fun v : G.ambient.Variable =>
            (A.lift (g + x) z ⟨v.1, b v.1⟩)⁻¹ * A.lift (g + x) z v) P := by
        apply congrArg (fun v : G.ambient.Variable → K => MvPolynomial.eval v P)
        funext v
        exact div_eq_inv_mul _ _
      _ = _ := (G.ambient.eval_block_scale P D hD (A.lift (g + x) z)
        (fun i => (A.lift (g + x) z ⟨i, b i⟩)⁻¹)).trans (by rw [hzero, mul_zero])
  unfold normalizedJet
  rw [(hz.iteratedFDeriv K j.order).eq_of_nhds]
  simp

/-- Every intrinsic differential ideal of the group's defining ideal is itself. -/
theorem differentialIdeal_vanishingIdeal (A : AnalyticSubgroup G) (g : G.Point) (T : ℕ) :
    differentialIdeal A g T (G.vanishingIdeal Set.univ) = G.vanishingIdeal Set.univ := by
  apply locallyGeneratedIdeal_of_zero_sections
  rintro f ⟨P, hP, ⟨D, hD⟩, b, j, rfl⟩ x hx
  exact normalizedJet_vanishingIdeal A g P hP D hD b j x

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalDenominators.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem exists_homogeneous_nonzero_evaluation (J : Ideal G.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal G.ambient J) (v : G.ambient.Variable → K)
    (P : G.CoordinateRing) (hP : P ∈ J) (hn : MvPolynomial.eval v P ≠ 0) :
    ∃ Q ∈ J, ∃ D : G.FactorIndex → ℕ,
      G.ambient.IsHomogeneous Q D ∧ MvPolynomial.eval v Q ≠ 0 := by
  classical
  let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
  rw [← sum_weightedHomogeneousComponent w P,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) P), map_sum] at hn
  obtain ⟨D, _, hD⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact ⟨weightedHomogeneousComponent w D P, hJ P hP D, D,
    (G.ambient.degreePiece_iff _ D).mp (weightedHomogeneousComponent_mem w P D), hD⟩

/-- A homogeneous equation belongs to a point localization precisely when
one homogeneous denominator, nonzero at that representative, clears it. -/
theorem mem_retainAtRepresentative_iff_homogeneous_denominator
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : GroupHomogeneousRepresentative G) :
    P ∈ retainAtRepresentative G I x ↔
      ∃ s : G.CoordinateRing, ∃ E : G.FactorIndex → ℕ, G.ambient.IsHomogeneous s E ∧
        representativeEvaluation G x s ≠ 0 ∧ s * P ∈ I := by
  let m := representativeMaximalIdeal G x
  change algebraMap G.CoordinateRing (Localization.AtPrime m.asIdeal) P ∈
      I.map (algebraMap G.CoordinateRing (Localization.AtPrime m.asIdeal)) ↔ _
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff m.asIdeal.primeCompl]
  constructor
  · rintro ⟨s, hs, hsp⟩
    have hsI : s ∈ I.colon {P} := by
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using hsp
    obtain ⟨t, ht, E, htE, htx⟩ := exists_homogeneous_nonzero_evaluation
      (I.colon {P}) (Hilbert.homogeneous_colon G.ambient I hI P D hP) x.coordinates s hsI hs
    exact ⟨t, E, htE, htx, by simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using ht⟩
  · rintro ⟨s, E, hsE, hs, hsp⟩
    exact ⟨s, hs, hsp⟩

theorem mem_retainOnGroup_iff_homogeneous_denominators
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    P ∈ retainOnGroup G I ↔
      ∀ x : GroupHomogeneousRepresentative G,
        ∃ s : G.CoordinateRing, ∃ E : G.FactorIndex → ℕ, G.ambient.IsHomogeneous s E ∧
          representativeEvaluation G x s ≠ 0 ∧ s * P ∈ I := by
  simp only [retainOnGroup, Submodule.mem_iInf,
    mem_retainAtRepresentative_iff_homogeneous_denominator I hI P D hP]

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponRelevantHilbert.lean

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


end PhilipponMultiplicity.Hilbert
end
end


section
-- Implementation: Solutions/PhilipponLocalPolynomialSections.lean

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

theorem chartValue_eq_div_pivot (b : CoordinateChart G) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) (x : G.Point) :
    chartValue G b P x = G.ambient.eval P (G.embedding x) /
      G.ambient.eval (pivotPolynomial b D) (G.embedding x) := by
  rw [chartValue_homogeneous b P D hP x]
  simp only [pivotPolynomial, MultiProjectiveSpace.eval, map_prod, map_pow, eval_X,
    MultiProjectiveSpace.coordinate, div_eq_mul_inv, Finset.prod_inv_distrib, inv_pow]
  exact mul_comm _ _

theorem locallyGenerated_translationSections_of_mem_retained
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (hmem : P ∈ retainOnGroup G I) : LocallyGenerated G (translationSections G 0 I) P := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  intro x
  obtain ⟨b, hb⟩ := exists_chartDomain x
  obtain ⟨s, E, hsE, hsx, hsp⟩ :=
    (mem_retainOnGroup_iff_homogeneous_denominators I hI P D hP).mp hmem (representativeOfPoint G x)
  have hsopen : IsOpen {y : G.Point | G.ambient.eval s (G.embedding y) ≠ 0} :=
    (G.ambient.isOpen_basic s E hsE).preimage continuous_induced_dom
  let U := chartDomain G b ∩ {y : G.Point | G.ambient.eval s (G.embedding y) ≠ 0}
  let f : (translationSections G 0 I) := ⟨
    ⟨chartDomain G b, chartValue G b (s * P)⟩,
    s * P, hsp, ⟨E + D, hsE.mul G.ambient hP⟩, b, by simp⟩
  let r : RationalCoefficient G :=
    ⟨pivotPolynomial b E, s, E, pivotPolynomial_homogeneous b E, hsE⟩
  refine ⟨b, U, (chartDomain_isOpen b).inter hsopen, ⟨hb, hsx⟩,
    Set.inter_subset_left, 1, (fun _ => f), (fun _ => r), ?_, ?_⟩
  · intro i y hy
    exact ⟨hy.1, hy.2⟩
  · intro y hy
    simp only [Fintype.sum_unique, f, r, RationalCoefficient.value]
    have hmul : chartValue G b (s * P) y = chartValue G b s y * chartValue G b P y := map_mul _ _ _
    rw [hmul, chartValue_eq_div_pivot b s E hsE y]
    have hpivot := pivotPolynomial_eval_ne_zero b E y hy.1
    have hsy : G.ambient.eval s (G.embedding y) ≠ 0 := hy.2
    field_simp

theorem retainOnGroup_le_translatedIdeal_zero
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I) :
    retainOnGroup G I ≤ translatedIdeal G 0 I := by
  classical
  intro P hP
  let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
  rw [← sum_weightedHomogeneousComponent w P,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) P)]
  apply Ideal.sum_mem
  intro D _
  have hD := (G.ambient.degreePiece_iff _ D).mp (weightedHomogeneousComponent_mem w P D)
  apply Ideal.subset_span
  exact ⟨⟨D,hD⟩,locallyGenerated_translationSections_of_mem_retained I hI _ D hD
    (retainOnGroup_homogeneous G I hI P hP D)⟩

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalRational.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem representativeEvaluation_zero_iff (x : GroupHomogeneousRepresentative G)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    representativeEvaluation G x P = 0 ↔ G.ambient.eval P (G.embedding x.point) = 0 := by
  classical
  have ha (i : G.FactorIndex) : ∃ a : Kˣ,
      ∀ j, x.coordinates ⟨i,j⟩ = (a : K) * (G.embedding x.point i).rep j := by
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ (x.nonzero i)
      (G.embedding x.point i).rep_nonzero).mp
      ((x.represents i).trans (G.embedding x.point i).mk_rep.symm)
    exact ⟨a,fun j => by simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm⟩
  choose a ha using ha
  have hcoords : x.coordinates = fun v => (a v.1 : K) * G.ambient.coordinate (G.embedding x.point) v := by
    funext v
    exact ha v.1 v.2
  have heval : representativeEvaluation G x P =
      (∏ i, (a i : K) ^ D i) * G.ambient.eval P (G.embedding x.point) := by
    unfold representativeEvaluation
    rw [hcoords]
    exact G.ambient.eval_block_scale P D hP (G.ambient.coordinate (G.embedding x.point))
      (fun i => (a i : K))
  rw [heval]
  exact mul_eq_zero_iff_left (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero))

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

def rationalZero : RationalCoefficient G :=
  ⟨0, 1, 0, by simp [MultiProjectiveSpace.IsHomogeneous], G.ambient.isHomogeneous_one⟩

def rationalAdd (r s : RationalCoefficient G) : RationalCoefficient G :=
  ⟨r.numerator * s.denominator + s.numerator * r.denominator,
    r.denominator * s.denominator, r.degree + s.degree,
    (r.numerator_homogeneous.mul G.ambient s.denominator_homogeneous).add G.ambient
      (by simpa only [add_comm] using s.numerator_homogeneous.mul G.ambient r.denominator_homogeneous),
    r.denominator_homogeneous.mul G.ambient s.denominator_homogeneous⟩

theorem rationalAdd_value (r s : RationalCoefficient G) (x : G.Point)
    (hr : G.ambient.eval r.denominator (G.embedding x) ≠ 0)
    (hs : G.ambient.eval s.denominator (G.embedding x) ≠ 0) :
    (rationalAdd r s).value x = r.value x + s.value x := by
  simp only [RationalCoefficient.value, rationalAdd, MultiProjectiveSpace.eval, map_add, map_mul]
  change (G.ambient.eval r.numerator (G.embedding x) * G.ambient.eval s.denominator (G.embedding x) +
    G.ambient.eval s.numerator (G.embedding x) * G.ambient.eval r.denominator (G.embedding x)) /
    (G.ambient.eval r.denominator (G.embedding x) * G.ambient.eval s.denominator (G.embedding x)) =
    G.ambient.eval r.numerator (G.embedding x) / G.ambient.eval r.denominator (G.embedding x) +
      G.ambient.eval s.numerator (G.embedding x) / G.ambient.eval s.denominator (G.embedding x)
  field_simp

theorem exists_rational_sum {n : ℕ} (r : Fin n → RationalCoefficient G)
    (I : Ideal G.CoordinateRing) (hrI : ∀ i, (r i).numerator ∈ I) :
    ∃ s : RationalCoefficient G, s.numerator ∈ I ∧
      ∀ x : G.Point, (∀ i, G.ambient.eval (r i).denominator (G.embedding x) ≠ 0) →
        G.ambient.eval s.denominator (G.embedding x) ≠ 0 ∧ s.value x = ∑ i, (r i).value x := by
  induction n with
  | zero =>
    refine ⟨rationalZero, I.zero_mem, ?_⟩
    intro x hx
    simp [rationalZero, RationalCoefficient.value, MultiProjectiveSpace.eval]
  | succ n ih =>
    obtain ⟨s,hsI,hs⟩ := ih (fun i => r i.succ) (fun i => hrI i.succ)
    refine ⟨rationalAdd (r 0) s, ?_, ?_⟩
    · exact I.add_mem (I.mul_mem_right _ (hrI 0)) (I.mul_mem_right _ hsI)
    · intro x hx
      obtain ⟨hsx,hseq⟩ := hs x (fun i => hx i.succ)
      refine ⟨?_, ?_⟩
      · change G.ambient.eval ((r 0).denominator * s.denominator) (G.embedding x) ≠ 0
        simp only [MultiProjectiveSpace.eval, map_mul]
        exact mul_ne_zero (hx 0) hsx
      · rw [rationalAdd_value _ _ x (hx 0) hsx, hseq, Fin.sum_univ_succ]

/-- Clear an identity on a Zariski neighborhood using one homogeneous basic
open equation, preserving actual ideal membership modulo the group ideal. -/
theorem local_fraction_identity_mem_retained
    (I : Ideal G.CoordinateRing) (hG : G.vanishingIdeal Set.univ ≤ I)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : GroupHomogeneousRepresentative G) (b : CoordinateChart G)
    (U : Set G.Point) (hU : @IsOpen _ G.zariskiTopology U) (hx : x.point ∈ U)
    (hUb : U ⊆ chartDomain G b) (r : RationalCoefficient G) (hrI : r.numerator ∈ I)
    (hr : ∀ y ∈ U, G.ambient.eval r.denominator (G.embedding y) ≠ 0)
    (heq : ∀ y ∈ U, chartValue G b P y = r.value y) :
    P ∈ retainAtRepresentative G I x := by
  classical
  obtain ⟨s,E,hsE,hsx,hsU⟩ := exists_basic_subset U hU x.point hx
  let B := pivotPolynomial b D
  let L := P * r.denominator - r.numerator * B
  have hL : G.ambient.IsHomogeneous L (D + r.degree) :=
    (hP.mul G.ambient r.denominator_homogeneous).sub G.ambient (by
      simpa only [add_comm] using r.numerator_homogeneous.mul G.ambient (pivotPolynomial_homogeneous b D))
  have hzero : ∀ y ∈ U, G.ambient.eval L (G.embedding y) = 0 := by
    intro y hy
    have h := heq y hy
    rw [chartValue_eq_div_pivot b P D hP y] at h
    have hb := pivotPolynomial_eval_ne_zero b D y (hUb hy)
    change _ / _ = _ / _ at h
    have hc := (div_eq_div_iff hb (hr y hy)).mp h
    change G.ambient.eval (P * r.denominator - r.numerator * B) (G.embedding y) = 0
    simpa only [MultiProjectiveSpace.eval, map_sub, map_mul, sub_eq_zero, B] using hc
  have hsL : s * L ∈ I := by
    apply hG
    apply Ideal.subset_span
    refine ⟨⟨E + (D + r.degree), hsE.mul G.ambient hL⟩, ?_⟩
    rintro _ ⟨y,_,rfl⟩
    change MvPolynomial.eval (G.ambient.coordinate (G.embedding y)) (s * L) = 0
    rw [map_mul]
    change G.ambient.eval s (G.embedding y) * G.ambient.eval L (G.embedding y) = 0
    by_cases hsy : G.ambient.eval s (G.embedding y) = 0
    · rw [hsy, zero_mul]
    · rw [hzero y (hsU hsy), mul_zero]
  have hclear : (s * r.denominator) * P ∈ I := by
    have h := I.add_mem hsL (I.mul_mem_left (s * B) hrI)
    convert h using 1 <;> dsimp [L] <;> ring
  have hsx' : representativeEvaluation G x s ≠ 0 := by
    exact fun h => hsx ((representativeEvaluation_zero_iff x s E hsE).mp h)
  have hdx' : representativeEvaluation G x r.denominator ≠ 0 := by
    exact fun h => hr x.point hx ((representativeEvaluation_zero_iff x _ _ r.denominator_homogeneous).mp h)
  change algebraMap G.CoordinateRing (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal) P ∈
    I.map (algebraMap G.CoordinateRing (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal))
  apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (representativeMaximalIdeal G x).asIdeal.primeCompl _ I P).mpr
  refine ⟨s * r.denominator, ?_, hclear⟩
  change representativeEvaluation G x (s * r.denominator) ≠ 0
  rw [map_mul]
  exact mul_ne_zero hsx' hdx'

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponRationalOperations.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

def rationalMul (r s : RationalCoefficient G) : RationalCoefficient G :=
  ⟨r.numerator * s.numerator,r.denominator * s.denominator,r.degree + s.degree,
    r.numerator_homogeneous.mul G.ambient s.numerator_homogeneous,
    r.denominator_homogeneous.mul G.ambient s.denominator_homogeneous⟩

def rationalNeg (r : RationalCoefficient G) : RationalCoefficient G :=
  ⟨-r.numerator,r.denominator,r.degree,r.numerator_homogeneous.neg G.ambient,r.denominator_homogeneous⟩

theorem rationalMul_value (r s : RationalCoefficient G) (x : G.Point) :
    (rationalMul r s).value x = r.value x * s.value x := by
  simp only [rationalMul,RationalCoefficient.value,MultiProjectiveSpace.eval,map_mul]
  exact (div_mul_div_comm _ _ _ _).symm

theorem rationalNeg_value (r : RationalCoefficient G) (x : G.Point) :
    (rationalNeg r).value x = -r.value x := by
  simp only [rationalNeg,RationalCoefficient.value,MultiProjectiveSpace.eval,map_neg,neg_div]

theorem rationalMul_denominator_ne_zero (r s : RationalCoefficient G) (x : G.Point)
    (hr : G.ambient.eval r.denominator (G.embedding x) ≠ 0)
    (hs : G.ambient.eval s.denominator (G.embedding x) ≠ 0) :
    G.ambient.eval (rationalMul r s).denominator (G.embedding x) ≠ 0 := by
  simp only [rationalMul,MultiProjectiveSpace.eval,map_mul]
  exact mul_ne_zero hr hs

theorem rationalAdd_denominator_ne_zero (r s : RationalCoefficient G) (x : G.Point)
    (hr : G.ambient.eval r.denominator (G.embedding x) ≠ 0)
    (hs : G.ambient.eval s.denominator (G.embedding x) ≠ 0) :
    G.ambient.eval (rationalAdd r s).denominator (G.embedding x) ≠ 0 := by
  simp only [rationalAdd,MultiProjectiveSpace.eval,map_mul]
  exact mul_ne_zero hr hs

theorem rationalAdd_numerator_mem (I : Ideal G.CoordinateRing) (r s : RationalCoefficient G)
    (hr : r.numerator ∈ I) (hs : s.numerator ∈ I) : (rationalAdd r s).numerator ∈ I :=
  I.add_mem (I.mul_mem_right _ hr) (I.mul_mem_right _ hs)

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponChartRational.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

/-- Even a nonhomogeneous polynomial, evaluated in normalized coordinates,
is a balanced homogeneous rational function regular on that coordinate chart. -/
theorem chartValue_rational (b : CoordinateChart G) (P : G.CoordinateRing) :
    ∃ r : RationalCoefficient G, ∀ x ∈ chartDomain G b,
      G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧ r.value x = chartValue G b P x := by
  classical
  have hX (v : G.ambient.Variable) : G.ambient.IsHomogeneous (X v) (Pi.single v.1 1) := by
    apply (G.ambient.degreePiece_iff _ _).mp
    exact isWeightedHomogeneous_X K _ v
  have hv (v : G.ambient.Variable) : ∃ r : RationalCoefficient G,
      ∀ x ∈ chartDomain G b, G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧
        r.value x = chartValue G b (X v) x := by
    let r : RationalCoefficient G := ⟨X v,X ⟨v.1,b v.1⟩,Pi.single v.1 1,hX v,hX _⟩
    refine ⟨r,?_⟩
    intro x hx
    refine ⟨?_,?_⟩
    · simpa only [r,MultiProjectiveSpace.eval,eval_X,MultiProjectiveSpace.coordinate] using hx v.1
    · simp only [r,RationalCoefficient.value,MultiProjectiveSpace.eval,chartValue,eval_X]
      rfl
  induction P using MvPolynomial.induction_on with
  | C a =>
    have ha : G.ambient.IsHomogeneous (C a) 0 := by
      simpa using G.ambient.isHomogeneous_one.C_mul G.ambient a
    refine ⟨⟨C a,1,0,ha,G.ambient.isHomogeneous_one⟩,?_⟩
    intro x hx
    simp [RationalCoefficient.value,MultiProjectiveSpace.eval,chartValue]
  | add P Q hP hQ =>
    obtain ⟨r,hr⟩ := hP
    obtain ⟨s,hs⟩ := hQ
    refine ⟨rationalAdd r s,?_⟩
    intro x hx
    refine ⟨rationalAdd_denominator_ne_zero r s x (hr x hx).1 (hs x hx).1,?_⟩
    rw [rationalAdd_value r s x (hr x hx).1 (hs x hx).1,(hr x hx).2,(hs x hx).2]
    exact (map_add _ P Q).symm
  | mul_X P v hP =>
    obtain ⟨r,hr⟩ := hP
    obtain ⟨s,hs⟩ := hv v
    refine ⟨rationalMul r s,?_⟩
    intro x hx
    refine ⟨rationalMul_denominator_ne_zero r s x (hr x hx).1 (hs x hx).1,?_⟩
    rw [rationalMul_value,(hr x hx).2,(hs x hx).2]
    exact (map_mul _ P (X v)).symm

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalJetSpan.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

/-- A finite regular rational expression in sections on a neighborhood of a point. -/
def LocalSpanAt (S : Set (LocalSection G)) (h : G.Point → K) (x : G.Point) : Prop :=
  ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧
    ∃ n : ℕ, ∃ f : Fin n → S, ∃ r : Fin n → RationalCoefficient G,
      (∀ i, ∀ y ∈ U, y ∈ (f i).val.domain ∧ G.ambient.eval (r i).denominator (G.embedding y) ≠ 0) ∧
      ∀ y ∈ U, h y = ∑ i, (r i).value y * (f i).val.value y

theorem localSpanAt_zero (S : Set (LocalSection G)) (x : G.Point) :
    LocalSpanAt S (fun _ => 0) x := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ x,0,Fin.elim0,Fin.elim0,?_,?_⟩
  · intro i
    exact Fin.elim0 i
  · intro y hy
    simp

theorem LocalSpanAt.congr_on {S : Set (LocalSection G)} {f h : G.Point → K} {x : G.Point}
    (hf : LocalSpanAt S f x) (V : Set G.Point) (hV : @IsOpen _ G.zariskiTopology V)
    (hxV : x ∈ V) (heq : ∀ y ∈ V, f y = h y) : LocalSpanAt S h x := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  obtain ⟨U,hU,hx,n,s,r,hr,hf⟩ := hf
  refine ⟨U ∩ V,hU.inter hV,⟨hx,hxV⟩,n,s,r,?_,?_⟩
  · intro i y hy
    exact hr i y hy.1
  · intro y hy
    exact (heq y hy.2).symm.trans (hf y hy.1)

theorem LocalSpanAt.add {S : Set (LocalSection G)} {f h : G.Point → K} {x : G.Point}
    (hf : LocalSpanAt S f x) (hh : LocalSpanAt S h x) :
    LocalSpanAt S (fun y => f y + h y) x := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  obtain ⟨U,hU,hxU,n,s,r,hs,hf⟩ := hf
  obtain ⟨V,hV,hxV,m,t,q,ht,hh⟩ := hh
  refine ⟨U ∩ V,hU.inter hV,⟨hxU,hxV⟩,n+m,Fin.addCases s t,Fin.addCases r q,?_,?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j y hy
      simpa only [Fin.addCases_left] using hs j y hy.1
    · intro j y hy
      simpa only [Fin.addCases_right] using ht j y hy.2
  · intro y hy
    change f y + h y = _
    rw [hf y hy.1,hh y hy.2,Fin.sum_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right]

theorem LocalSpanAt.rational_mul {S : Set (LocalSection G)} {f : G.Point → K} {x : G.Point}
    (hf : LocalSpanAt S f x) (q : RationalCoefficient G)
    (V : Set G.Point) (hV : @IsOpen _ G.zariskiTopology V) (hxV : x ∈ V)
    (hq : ∀ y ∈ V, G.ambient.eval q.denominator (G.embedding y) ≠ 0) :
    LocalSpanAt S (fun y => q.value y * f y) x := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  obtain ⟨U,hU,hxU,n,s,r,hs,heq⟩ := hf
  refine ⟨U ∩ V,hU.inter hV,⟨hxU,hxV⟩,n,s,(fun i => rationalMul q (r i)),?_,?_⟩
  · intro i y hy
    exact ⟨(hs i y hy.1).1,
      rationalMul_denominator_ne_zero _ _ y (hq y hy.2) (hs i y hy.1).2⟩
  · intro y hy
    change q.value y * f y = _
    rw [heq y hy.1,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [rationalMul_value,mul_assoc]

theorem LocalSpanAt.fin_sum {S : Set (LocalSection G)} {n : ℕ}
    (f : Fin n → G.Point → K) (x : G.Point) (hf : ∀ i, LocalSpanAt S (f i) x) :
    LocalSpanAt S (fun y => ∑ i, f i y) x := by
  induction n with
  | zero => simpa using localSpanAt_zero S x
  | succ n ih =>
    have hh := (hf 0).add (ih (fun i => f i.succ) (fun i => hf i.succ))
    simpa only [Fin.sum_univ_succ] using hh

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalSectionIdeal.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem localSpanAt_section (S : Set (LocalSection G)) (f : S) (x : G.Point)
    (U : Set G.Point) (hU : @IsOpen _ G.zariskiTopology U) (hx : x ∈ U)
    (hUf : U ⊆ f.val.domain) : LocalSpanAt S f.val.value x := by
  let r : RationalCoefficient G :=
    ⟨1,1,0,G.ambient.isHomogeneous_one,G.ambient.isHomogeneous_one⟩
  refine ⟨U,hU,hx,1,(fun _ => f),(fun _ => r),?_,?_⟩
  · intro i y hy
    refine ⟨hUf hy,?_⟩
    simp only [r,MultiProjectiveSpace.eval,map_one,ne_eq,one_ne_zero,not_false_eq_true]
  · intro y hy
    simp [r,RationalCoefficient.value,MultiProjectiveSpace.eval]

theorem LocalSpanAt.list_sum {ι : Type*} {S : Set (LocalSection G)} (s : List ι)
    (f : ι → G.Point → K) (x : G.Point) (hf : ∀ i ∈ s, LocalSpanAt S (f i) x) :
    LocalSpanAt S (fun y => (s.map (fun i => f i y)).sum) x := by
  induction s with
  | nil => simpa using localSpanAt_zero S x
  | cons i s ih =>
    exact (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

theorem locallyGenerated_iff_localSpan (S : Set (LocalSection G)) (P : G.CoordinateRing) :
    LocallyGenerated G S P ↔
      ∀ x : G.Point, ∃ b : CoordinateChart G, x ∈ chartDomain G b ∧
        LocalSpanAt S (chartValue G b P) x := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  constructor
  · intro h x
    obtain ⟨b,U,hU,hx,hUb,n,f,r,hfr,heq⟩ := h x
    exact ⟨b,hUb hx,U,hU,hx,n,f,r,hfr,heq⟩
  · intro h x
    obtain ⟨b,hb,U,hU,hx,n,f,r,hfr,heq⟩ := h x
    refine ⟨b,U ∩ chartDomain G b,hU.inter (chartDomain_isOpen b),⟨hx,hb⟩,
      Set.inter_subset_right,n,f,r,?_,?_⟩
    · intro i y hy
      exact hfr i y hy.1
    · intro y hy
      exact heq y hy.1

/-- At a fixed source chart and point, membership in the local section span
pulls back to an actual polynomial ideal. -/
def localSectionIdeal (S : Set (LocalSection G)) (b : CoordinateChart G)
    (x : G.Point) (hx : x ∈ chartDomain G b) : Ideal G.CoordinateRing where
  carrier := {P | LocalSpanAt S (chartValue G b P) x}
  zero_mem' := by
    change LocalSpanAt S (chartValue G b 0) x
    have heq : chartValue G b 0 = fun _ => 0 := by
      funext y
      exact map_zero _
    rw [heq]
    exact localSpanAt_zero S x
  add_mem' := by
    intro P Q hP hQ
    change LocalSpanAt S (chartValue G b (P + Q)) x
    have heq : chartValue G b (P + Q) = fun y => chartValue G b P y + chartValue G b Q y := by
      funext y
      exact map_add _ P Q
    rw [heq]
    exact hP.add hQ
  smul_mem' := by
    intro a P hP
    obtain ⟨r,hr⟩ := chartValue_rational b a
    have h := hP.rational_mul r (chartDomain G b) (chartDomain_isOpen b) hx
      (fun y hy => (hr y hy).1)
    apply h.congr_on (chartDomain G b) (chartDomain_isOpen b) hx
    intro y hy
    rw [(hr y hy).2]
    exact (map_mul _ a P).symm

theorem mem_localSectionIdeal (S : Set (LocalSection G)) (b : CoordinateChart G)
    (x : G.Point) (hx : x ∈ chartDomain G b) (P : G.CoordinateRing) :
    P ∈ localSectionIdeal S b x hx ↔ LocalSpanAt S (chartValue G b P) x := Iff.rfl

theorem groupIdeal_le_localSectionIdeal (S : Set (LocalSection G)) (b : CoordinateChart G)
    (x : G.Point) (hx : x ∈ chartDomain G b) :
    G.vanishingIdeal Set.univ ≤ localSectionIdeal S b x hx := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  apply (localSpanAt_zero S x).congr_on Set.univ isOpen_univ (Set.mem_univ x)
  intro y hy
  rw [chartValue_homogeneous b P D hD y,hP _ ⟨y,Set.mem_univ y,rfl⟩,mul_zero]

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponRegularMapTopology.lean

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

/-- Substituting tuples homogeneous in each source block preserves
multihomogeneity, with the expected linear transformation of degrees. -/
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

/-- Two projective lifts represent the same point precisely when all their
two-by-two cross products vanish. -/
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

/-- Regular maps into a multiprojective space have a closed equalizer, even
though the Zariski topology on the target is not Hausdorff. -/
theorem IsRegularAlong.isClosed_equalizer
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g) :
    @IsClosed X (TopologicalSpace.induced e M.zariskiTopology) {x | f x = g x} := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hx
  obtain ⟨U, hU, hxU, D, P, hP, hflift⟩ := hf x b
  obtain ⟨V, hV, hxV, E, Q, hQ, hglift⟩ := hg x b
  obtain ⟨hp, hpx⟩ := hflift x hxU
  obtain ⟨hq, hqx⟩ := hglift x hxV
  have hcross : ∃ j k, M.eval (P j * Q k - P k * Q j) (e x) ≠ 0 := by
    by_contra! hn
    apply hb
    rw [← hpx, ← hqx, projectivization_mk_eq_iff_cross]
    intro j k
    simpa only [eval, map_sub, map_mul, sub_eq_zero] using hn j k
  obtain ⟨j, k, hjk⟩ := hcross
  have hhom := ((hP j).mul M (hQ k)).sub M ((hP k).mul M (hQ j))
  let W := U ∩ V ∩ {p | M.eval (P j * Q k - P k * Q j) p ≠ 0}
  have hopen : IsOpen (e ⁻¹' W) :=
    ((hU.inter hV).inter (M.isOpen_basic _ _ hhom)).preimage continuous_induced_dom
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨⟨hxU, hxV⟩, hjk⟩) ?_
  intro y hy heq
  obtain ⟨hpy, hpy'⟩ := hflift y hy.1.1
  obtain ⟨hqy, hqy'⟩ := hglift y hy.1.2
  have hmk := hpy'.trans ((congrFun heq b).trans hqy'.symm)
  have hz := (projectivization_mk_eq_iff_cross _ _ hpy hqy).mp hmk j k
  exact hy.2 (by simpa only [eval, map_sub, map_mul, sub_eq_zero] using hz)

theorem IsRegularAlong.eq_of_dense
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g)
    (A : Set X) (hA : @Dense X (TopologicalSpace.induced e M.zariskiTopology) A)
    (hfg : Set.EqOn f g A) : f = g := by
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  have hh : closure A ⊆ {x | f x = g x} :=
    closure_minimal hfg (hf.isClosed_equalizer M N hg)
  funext x
  exact hh (hA x)

/-- Regular maps are continuous for the actual polynomial Zariski topologies. -/
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
-- Implementation: Solutions/PhilipponProjectiveTranslations.lean

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

/-- Fixing one projective argument of a regular map gives a regular map. -/
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

/-- The regular group law supplies regular translations. -/
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
-- Implementation: Solutions/PhilipponRegularMapComposition.lean

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

/-- Composition of regular maps, including maps given along arbitrary embedded domains. -/
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
-- Implementation: Solutions/PhilipponProductRegularity.lean

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

theorem EmbeddedGroupProduct.embedding_injective (G : EmbeddedGroupProduct K) :
    Function.Injective G.embedding := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

theorem EmbeddedGroupProduct.embedding_locallyClosed (G : EmbeddedGroupProduct K) :
    @IsLocallyClosed _ G.ambient.zariskiTopology (range G.embedding) := by
  classical
  let := G.ambient.zariskiTopology
  have hloc (i : G.FactorIndex) : IsLocallyClosed {p : G.ambient.Point | p i ∈ (G.factor i).carrier} := by
    let := (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology
    let := TopologicalSpace.induced
      (fun (x : Projectivization K (Fin ((G.factor i).ambientDimension + 1) → K)) (_ : Fin 1) => x)
      (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology
    apply (G.factor i).locallyClosed.preimage
    apply continuous_induced_rng.mpr
    have h := (G.ambient.projection_regular i).continuous
    rw [induced_id] at h
    exact h
  choose U Z hU hZ hUZ using hloc
  refine ⟨⋂ i, U i, ⋂ i, Z i, isOpen_iInter_of_finite hU, isClosed_iInter hZ, ?_⟩
  have heq : range G.embedding = ⋂ i, {p : G.ambient.Point | p i ∈ (G.factor i).carrier} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_iInter.mpr (fun i => (x i).property)
    · intro hp
      exact ⟨(fun i => ⟨p i, mem_iInter.mp hp i⟩), rfl⟩
  rw [heq]
  simp only [hUZ, iInter_inter_distrib]

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
-- Implementation: Solutions/PhilipponLocalGenerationCharts.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem translation_preimage_isOpen (g : G.Point) (U : Set G.Point)
    (hU : @IsOpen _ G.zariskiTopology U) :
    @IsOpen _ G.zariskiTopology {x | g+x ∈ U} := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  have hc : Continuous (fun x : G.Point => x+g) :=
    continuous_induced_rng.mpr (G.translation_regular g).continuous
  have hc' : Continuous (fun x : G.Point => g+x) := by simpa only [add_comm] using hc
  exact hU.preimage hc'

/-- Homogeneous local expressions may be read in any chart through the point.
The chart-change factor is an actual balanced rational function. -/
theorem LocalSpanAt.change_chart {S : Set (LocalSection G)}
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (b c : CoordinateChart G) (x : G.Point)
    (hb : x ∈ chartDomain G b) (hc : x ∈ chartDomain G c)
    (h : LocalSpanAt S (chartValue G b P) x) :
    LocalSpanAt S (chartValue G c P) x := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  let r : RationalCoefficient G :=
    ⟨pivotPolynomial b D,pivotPolynomial c D,D,
      pivotPolynomial_homogeneous b D,pivotPolynomial_homogeneous c D⟩
  have hh := h.rational_mul r (chartDomain G c) (chartDomain_isOpen c) hc
    (fun y hy => pivotPolynomial_eval_ne_zero c D y hy)
  apply hh.congr_on (chartDomain G b ∩ chartDomain G c)
    ((chartDomain_isOpen b).inter (chartDomain_isOpen c)) ⟨hb,hc⟩
  intro y hy
  rw [chartValue_eq_div_pivot b P D hP,chartValue_eq_div_pivot c P D hP]
  change (_ / _) * (_ / _) = _ / _
  dsimp only [r]
  have hn := pivotPolynomial_eval_ne_zero b D y hy.1
  field_simp

/-- The ideal span in the global definition does not lose the local expression:
every polynomial in it has a finite expression in every chart through x. -/
theorem locallyGeneratedIdeal_le_localSectionIdeal (S : Set (LocalSection G))
    (b : CoordinateChart G) (x : G.Point) (hx : x ∈ chartDomain G b) :
    locallyGeneratedIdeal G S ≤ localSectionIdeal S b x hx := by
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  obtain ⟨c,hc,hh⟩ := (locallyGenerated_iff_localSpan S P).mp hP x
  exact hh.change_chart P D hD c b x hc hx

theorem LocalSpanAt.trans {S R : Set (LocalSection G)} {f : G.Point → K}
    {x : G.Point} (h : LocalSpanAt S f x)
    (hS : ∀ s : S, x ∈ s.val.domain → LocalSpanAt R s.val.value x) :
    LocalSpanAt R f x := by
  obtain ⟨U,hU,hx,n,s,r,hs,heq⟩ := h
  have ht (i : Fin n) := (hS (s i) (hs i x hx).1).rational_mul (r i) U hU hx
    (fun y hy => (hs i y hy).2)
  exact (LocalSpanAt.fin_sum (fun i y => (r i).value y * (s i).val.value y) x ht).congr_on
    U hU hx (fun y hy => (heq y hy).symm)

theorem locallyGeneratedIdeal_le_of_localSpan (S R : Set (LocalSection G))
    (hS : ∀ s : S, ∀ x ∈ s.val.domain, LocalSpanAt R s.val.value x) :
    locallyGeneratedIdeal G S ≤ locallyGeneratedIdeal G R := by
  apply Ideal.span_le.mpr
  rintro P ⟨hP,h⟩
  apply Ideal.subset_span
  refine ⟨hP,(locallyGenerated_iff_localSpan R P).mpr ?_⟩
  intro x
  obtain ⟨b,hb,hh⟩ := (locallyGenerated_iff_localSpan S P).mp h x
  exact ⟨b,hb,hh.trans (fun s hs => hS s x hs)⟩

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponOrbitLocality.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem polynomialPullback_analytic (A : AnalyticSubgroup G)
    (g : G.Point) (P : G.CoordinateRing) :
    AnalyticAt K (A.pullback P g) 0 :=
  AnalyticAt.aeval_mvPolynomial (fun v => A.lift_analytic g v) P

theorem lift_zero_represents (A : AnalyticSubgroup G) (g : G.Point) :
    ∀ i : G.FactorIndex, ∃ h : (fun j => A.lift g 0 ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => A.lift g 0 ⟨i,j⟩) h = G.embedding g i := by
  obtain ⟨hz,hrep⟩ := (A.lift_represents g).self_of_nhds
  have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
  simpa only [hz',A.map_zero,add_zero] using hrep

/-- A sufficiently short orbit stays in any prescribed Zariski neighborhood
of its initial point. This justifies pulling back local ideal expressions. -/
theorem orbit_eventually_mem_open (A : AnalyticSubgroup G) (g : G.Point)
    (U : Set G.Point) (hU : @IsOpen _ G.zariskiTopology U) (hg : g ∈ U) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      g + A.map ⟨z,hz⟩ ∈ U := by
  obtain ⟨P,D,hP,hgP,hPU⟩ := exists_basic_subset U hU g hg
  have h0 : A.pullback P g 0 ≠ 0 := by
    exact (not_congr (G.ambient.eval_eq_zero_iff_of_lift (G.embedding g)
      (A.lift g 0) (lift_zero_represents A g) P D hP)).mpr hgP
  filter_upwards [(polynomialPullback_analytic A g P).continuousAt.eventually_ne h0,
      A.lift_represents g] with z hz hrep
  obtain ⟨hzdom,hrep⟩ := hrep
  refine ⟨hzdom,hPU ?_⟩
  exact (not_congr (G.ambient.eval_eq_zero_iff_of_lift
    (G.embedding (g+A.map ⟨z,hzdom⟩)) (A.lift g z) hrep P D hP)).mp hz

theorem rationalCoefficient_value_of_lift (r : RationalCoefficient G) (g : G.Point)
    (v : G.ambient.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = G.embedding g i) :
    MvPolynomial.eval v r.numerator / MvPolynomial.eval v r.denominator = r.value g := by
  classical
  have ha (i : G.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i,j⟩ = (a : K) * (G.embedding g i).rep j := by
    obtain ⟨h,heq⟩ := hv i
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (G.embedding g i).rep_nonzero).mp (heq.trans (G.embedding g i).mk_rep.symm)
    exact ⟨a,fun j => by
      simpa only [Pi.smul_apply,Units.smul_def,smul_eq_mul] using (congrFun ha j).symm⟩
  choose a ha using ha
  have hcoords : v = fun q => (a q.1 : K) * G.ambient.coordinate (G.embedding g) q := by
    funext q
    exact ha q.1 q.2
  rw [hcoords,G.ambient.eval_block_scale r.numerator r.degree r.numerator_homogeneous
      (G.ambient.coordinate (G.embedding g)) (fun i => (a i : K)),
    G.ambient.eval_block_scale r.denominator r.degree r.denominator_homogeneous
      (G.ambient.coordinate (G.embedding g)) (fun i => (a i : K))]
  exact mul_div_mul_left _ _
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero))

theorem rational_orbit_pullback_germ (A : AnalyticSubgroup G) (g : G.Point)
    (r : RationalCoefficient G) :
    (fun z : A.ParameterSpace => if hz : z ∈ A.domain then r.value (g+A.map ⟨z,hz⟩) else 0)
      =ᶠ[𝓝 0] (fun z => A.pullback r.numerator g z / A.pullback r.denominator g z) := by
  filter_upwards [A.lift_represents g] with z hrep
  obtain ⟨hz,hrep⟩ := hrep
  rw [dif_pos hz]
  exact (rationalCoefficient_value_of_lift r _ _ hrep).symm

/-- Regular rational coefficients become analytic coefficients along the
orbit germ, provided their actual denominator is nonzero at the initial point. -/
theorem rational_orbit_pullback_analytic (A : AnalyticSubgroup G) (g : G.Point)
    (r : RationalCoefficient G) (hr : G.ambient.eval r.denominator (G.embedding g) ≠ 0) :
    AnalyticAt K
      (fun z : A.ParameterSpace => if hz : z ∈ A.domain then r.value (g+A.map ⟨z,hz⟩) else 0) 0 := by
  have h0 : A.pullback r.denominator g 0 ≠ 0 :=
    (not_congr (G.ambient.eval_eq_zero_iff_of_lift (G.embedding g) (A.lift g 0)
      (lift_zero_represents A g) r.denominator r.degree r.denominator_homogeneous)).mpr hr
  exact ((polynomialPullback_analytic A g r.numerator).div
    (polynomialPullback_analytic A g r.denominator) h0).congr
      (rational_orbit_pullback_germ A g r).symm

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponNormalizedChartGerms.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem projective_pivot_ne_zero {ι : Type*} (v : ι → K) (hv : v ≠ 0)
    (p : Projectivization K (ι → K)) (hp : Projectivization.mk K v hv = p)
    (j : ι) (hj : p.rep j ≠ 0) : v j ≠ 0 := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K v p.rep hv p.rep_nonzero).mp
    (hp.trans p.mk_rep.symm)
  have hj' : v j = (a : K) * p.rep j := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  rw [hj']
  exact mul_ne_zero a.ne_zero hj

theorem projective_pivot_ne_zero_iff {ι : Type*} (v : ι → K) (hv : v ≠ 0)
    (p : Projectivization K (ι → K)) (hp : Projectivization.mk K v hv = p)
    (j : ι) : v j ≠ 0 ↔ p.rep j ≠ 0 := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K v p.rep hv p.rep_nonzero).mp
    (hp.trans p.mk_rep.symm)
  have hj : v j = (a : K) * p.rep j := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  simp [hj,a.ne_zero]

theorem lift_pivot_ne_zero (A : AnalyticSubgroup G) (g : G.Point)
    (b : CoordinateChart G) (hg : g ∈ chartDomain G b) (i : G.FactorIndex) :
    A.lift g 0 ⟨i,b i⟩ ≠ 0 := by
  obtain ⟨hz,hi⟩ := (A.lift_represents g).self_of_nhds
  have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
  rw [hz',A.map_zero,add_zero] at hi
  obtain ⟨hne,heq⟩ := hi i
  exact projective_pivot_ne_zero _ hne _ heq _ (hg i)

theorem normalizedPullback_analytic (A : AnalyticSubgroup G) (g : G.Point)
    (b : CoordinateChart G) (P : G.CoordinateRing) (x : G.Point)
    (hx : g + x ∈ chartDomain G b) :
    AnalyticAt K (normalizedPullback A g b P x) 0 := by
  apply AnalyticAt.aeval_mvPolynomial
  intro v
  exact (A.lift_analytic (g+x) v).div (A.lift_analytic (g+x) ⟨v.1,b v.1⟩)
    (lift_pivot_ne_zero A (g+x) b hx v.1)

/-- The source coordinate-ratio identity, including charts whose own domain
does not contain x. Only the intrinsic target pivots must be nonzero. -/
theorem chart_normalized_factorization (chart : TranslationChart A g)
    (b : CoordinateChart G) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (x : G.Point)
    (hx : g+x ∈ chartDomain G b) :
    evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x =ᶠ[𝓝 0]
      (fun z => (∏ i, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z ^ D i) *
        normalizedPullback A g b P x z) := by
  classical
  have hnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ i : G.FactorIndex, A.lift (g+x) z ⟨i,b i⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (A.lift_analytic (g+x) _).continuousAt.eventually_ne
      (lift_pivot_ne_zero A (g+x) b hx i)
  have hcompat : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∀ v : G.ambient.Variable,
      evaluateCoefficientPolynomial A (chart.coordinates v) x z * A.lift (g+x) z ⟨v.1,b v.1⟩ =
        evaluateCoefficientPolynomial A (chart.coordinates ⟨v.1,b v.1⟩) x z * A.lift (g+x) z v := by
    rw [Filter.eventually_all]
    intro v
    exact chart.coordinate_compatible x v.1 v.2 (b v.1)
  filter_upwards [hnear,hcompat] with z hz hc
  rw [evaluate_substituted]
  have heq : (fun v : G.ambient.Variable => evaluateCoefficientPolynomial A (chart.coordinates v) x z) =
      fun v : G.ambient.Variable => evaluateCoefficientPolynomial A (chart.coordinates ⟨v.1,b v.1⟩) x z *
        (A.lift (g+x) z v / A.lift (g+x) z ⟨v.1,b v.1⟩) := by
    funext v
    apply (mul_right_cancel₀ (hz v.1))
    rw [mul_assoc,div_mul_cancel₀ _ (hz v.1)]
    exact hc v
  rw [heq]
  exact G.ambient.eval_block_scale P D hP
    (fun v : G.ambient.Variable => A.lift (g+x) z v / A.lift (g+x) z ⟨v.1,b v.1⟩)
    (fun i : G.FactorIndex => evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z)

theorem chart_pivot_ne_zero (chart : TranslationChart A g) (x : G.Point)
    (hchart : x ∈ chart.domain) (b : CoordinateChart G)
    (hx : g+x ∈ chartDomain G b) (i : G.FactorIndex) :
    evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x 0 ≠ 0 := by
  obtain ⟨hz,hi⟩ := (chart.represents x hchart).self_of_nhds
  have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
  rw [hz',A.map_zero,add_zero] at hi
  obtain ⟨hne,heq⟩ := hi i
  apply projective_pivot_ne_zero _ hne _ heq
  simpa only [add_comm x g] using hx i

theorem normalizedPullback_eq_chart_quotient (chart : TranslationChart A g)
    (b : CoordinateChart G) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (x : G.Point) (hchart : x ∈ chart.domain)
    (hx : g+x ∈ chartDomain G b) :
    normalizedPullback A g b P x =ᶠ[𝓝 0]
      (fun z => evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x z /
        ∏ i, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z ^ D i) := by
  classical
  have hnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ i : G.FactorIndex, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (chart_evaluation_analytic chart x _).continuousAt.eventually_ne
      (chart_pivot_ne_zero chart x hchart b hx i)
  filter_upwards [chart_normalized_factorization chart b P D hP x hx,hnear] with z heq hz
  rw [heq]
  exact (mul_div_cancel_left₀ _ (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hz i))).symm

theorem evaluate_pivot_substitution (chart : TranslationChart A g)
    (b : CoordinateChart G) (D : G.FactorIndex → ℕ) (x : G.Point) (z : A.ParameterSpace) :
    evaluateCoefficientPolynomial A (substitutedPolynomial chart (pivotPolynomial b D)) x z =
      ∏ i, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) x z ^ D i := by
  rw [evaluate_substituted]
  simp only [pivotPolynomial,map_prod,map_pow,eval_X]
  rfl

/-- A genuine Zariski neighborhood with simultaneous nonvanishing target pivots. -/
theorem exists_translation_pivot_neighborhood (chart : TranslationChart A g)
    (b : CoordinateChart G) (x : G.Point) (hchart : x ∈ chart.domain)
    (hx : g+x ∈ chartDomain G b) :
    ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧ U ⊆ chart.domain ∧
      ∀ y ∈ U, g+y ∈ chartDomain G b ∧
        ∀ i : G.FactorIndex, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) y 0 ≠ 0 := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  let B := pivotPolynomial b (fun _ => 1)
  let Q := polynomialOperator chart 0 Fin.elim0 B
  have hQ : G.ambient.IsHomogeneous Q chart.degree := by
    simpa only [mul_one] using polynomialOperator_homogeneous chart 0 Fin.elim0 B (fun _ => 1)
      (pivotPolynomial_homogeneous b (fun _ => 1))
  have hQeval (y : G.Point) : G.ambient.eval Q (G.embedding y) =
      ∏ i, evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) y 0 := by
    rw [polynomialOperator_eval]
    simp only [iteratedFDeriv_zero_apply]
    rw [← evaluate_substituted]
    simpa only [pow_one] using evaluate_pivot_substitution chart b (fun _ => 1) y 0
  let U := chart.domain ∩ {y : G.Point | G.ambient.eval Q (G.embedding y) ≠ 0}
  have ho : @IsOpen _ G.zariskiTopology {y : G.Point | G.ambient.eval Q (G.embedding y) ≠ 0} :=
    (G.ambient.isOpen_basic Q chart.degree hQ).preimage continuous_induced_dom
  refine ⟨U,chart.domain_isOpen.inter ho,⟨hchart,?_⟩,Set.inter_subset_left,?_⟩
  · change G.ambient.eval Q (G.embedding x) ≠ 0
    rw [hQeval]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => chart_pivot_ne_zero chart x hchart b hx i)
  · intro y hy
    have hn : ∀ i : G.FactorIndex,
        evaluateCoefficientPolynomial A (chart.coordinates ⟨i,b i⟩) y 0 ≠ 0 := by
      have hh : G.ambient.eval Q (G.embedding y) ≠ 0 := hy.2
      rw [hQeval] at hh
      exact fun i => Finset.prod_ne_zero_iff.mp hh i (Finset.mem_univ i)
    refine ⟨?_,hn⟩
    intro i
    obtain ⟨hz,hi⟩ := (chart.represents y hy.1).self_of_nhds
    have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
    rw [hz',A.map_zero,add_zero] at hi
    obtain ⟨hne,heq⟩ := hi i
    have hh := (projective_pivot_ne_zero_iff _ hne _ heq (b i)).mp (hn i)
    simpa only [add_comm y g] using hh

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponRationalJetRecursion.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem exists_rational_list_sum {ι : Type*} (s : List ι) (f : ι → G.Point → K)
    (I : Ideal G.CoordinateRing) (U : Set G.Point)
    (hf : ∀ i ∈ s, ∃ r : RationalCoefficient G, r.numerator ∈ I ∧
      ∀ x ∈ U, G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧ r.value x = f i x) :
    ∃ r : RationalCoefficient G, r.numerator ∈ I ∧
      ∀ x ∈ U, G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧
        r.value x = (s.map (fun i => f i x)).sum := by
  induction s with
  | nil =>
    refine ⟨rationalZero,I.zero_mem,?_⟩
    intro x hx
    simp [rationalZero,RationalCoefficient.value,MultiProjectiveSpace.eval]
  | cons i s ih =>
    obtain ⟨r,hrI,hr⟩ := hf i (by simp)
    obtain ⟨t,htI,ht⟩ := ih (fun j hj => hf j (by simp [hj]))
    refine ⟨rationalAdd r t,rationalAdd_numerator_mem I r t hrI htI,?_⟩
    intro x hx
    obtain ⟨hrx,heqr⟩ := hr x hx
    obtain ⟨htx,heqt⟩ := ht x hx
    exact ⟨rationalAdd_denominator_ne_zero r t x hrx htx,by
      rw [rationalAdd_value r t x hrx htx,heqr,heqt,List.map_cons,List.sum_cons]⟩

/-- A triangular jet identity yields honest homogeneous fractions. The
numerators remain in the given ideal, without taking radicals. -/
theorem rational_jet_recursion {ι : Type*}
    (F Q : List ι → G.CoordinateRing) (H : List ι → G.Point → K)
    (E : G.FactorIndex → ℕ) (I : Ideal G.CoordinateRing) (U : Set G.Point) (T : ℕ)
    (hF : ∀ w, G.ambient.IsHomogeneous (F w) E)
    (hQ : ∀ w, G.ambient.IsHomogeneous (Q w) E)
    (hFI : ∀ w, w.length ≤ T → F w ∈ I)
    (hQ0 : ∀ x ∈ U, G.ambient.eval (Q []) (G.embedding x) ≠ 0)
    (heq : ∀ w, w.length ≤ T → ∀ x ∈ U,
      G.ambient.eval (F w) (G.embedding x) =
        G.ambient.eval (Q []) (G.embedding x) * H w x +
          ((properSplits w).map (fun p =>
            G.ambient.eval (Q p.1) (G.embedding x) * H p.2 x)).sum)
    (w : List ι) (hw : w.length ≤ T) :
    ∃ r : RationalCoefficient G, r.numerator ∈ I ∧
      ∀ x ∈ U, G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧ r.value x = H w x := by
  classical
  suffices hall : ∀ n, ∀ w : List ι, w.length = n → w.length ≤ T →
      ∃ r : RationalCoefficient G, r.numerator ∈ I ∧
        ∀ x ∈ U, G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧ r.value x = H w x from
    hall w.length w rfl hw
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn hw
    let a : RationalCoefficient G := ⟨F w,Q [],E,hF w,hQ []⟩
    let q : List ι → RationalCoefficient G := fun v => ⟨Q v,Q [],E,hQ v,hQ []⟩
    have hterms : ∀ p ∈ properSplits w, ∃ r : RationalCoefficient G, r.numerator ∈ I ∧
        ∀ x ∈ U, G.ambient.eval r.denominator (G.embedding x) ≠ 0 ∧
          r.value x = G.ambient.eval (Q p.1) (G.embedding x) /
            G.ambient.eval (Q []) (G.embedding x) * H p.2 x := by
      intro p hp
      have hlen := (properSplits_lengths w p hp).2.2
      obtain ⟨r,hrI,hr⟩ := ih p.2.length (by omega) p.2 rfl (by omega)
      refine ⟨rationalMul (q p.1) r,I.mul_mem_left _ hrI,?_⟩
      intro x hx
      obtain ⟨hrx,heqr⟩ := hr x hx
      exact ⟨rationalMul_denominator_ne_zero _ _ x (hQ0 x hx) hrx,by
        rw [rationalMul_value,heqr]; rfl⟩
    obtain ⟨s,hsI,hs⟩ := exists_rational_list_sum (properSplits w)
      (fun p x => G.ambient.eval (Q p.1) (G.embedding x) /
        G.ambient.eval (Q []) (G.embedding x) * H p.2 x) I U hterms
    refine ⟨rationalAdd a (rationalNeg s),
      rationalAdd_numerator_mem I _ _ (hFI w hw) (I.neg_mem hsI),?_⟩
    intro x hx
    obtain ⟨hsx,heqs⟩ := hs x hx
    have hax : G.ambient.eval a.denominator (G.embedding x) ≠ 0 := hQ0 x hx
    refine ⟨rationalAdd_denominator_ne_zero _ _ x hax hsx,?_⟩
    rw [rationalAdd_value a (rationalNeg s) x hax hsx,rationalNeg_value,heqs]
    change G.ambient.eval (F w) (G.embedding x) / G.ambient.eval (Q []) (G.embedding x) + -_ = _
    rw [heq w hw x hx,add_div,mul_div_cancel_left₀ _ (hQ0 x hx)]
    have hsum : ((properSplits w).map (fun p =>
        G.ambient.eval (Q p.1) (G.embedding x) / G.ambient.eval (Q []) (G.embedding x) * H p.2 x)).sum =
        ((properSplits w).map (fun p => G.ambient.eval (Q p.1) (G.embedding x) * H p.2 x)).sum /
          G.ambient.eval (Q []) (G.embedding x) := by
      induction properSplits w with
      | nil => simp
      | cons p ps ih => simp only [List.map_cons,List.sum_cons,add_div,ih]; ring
    rw [hsum]
    ring

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponNormalizedJetFractions.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem polynomialOperator_eval_mixed (chart : TranslationChart A g) (P : G.CoordinateRing)
    (x : G.Point) (w : List (Fin A.parameterDimension)) :
    G.ambient.eval (polynomialOperator chart w.length w.get P) (G.embedding x) =
      mixedDeriv (w.map (fun i => Pi.single i (1 : K)))
        (evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x) 0 := by
  rw [mixedDeriv_map_eq_iteratedFDeriv _
    (evaluated_coefficients_analytic _ (substituted_coeff_analytic chart P) x)]
  rw [polynomialOperator_eval]
  congr 2
  funext z
  exact (evaluate_substituted chart P x z).symm

/-- Every intrinsic normalized jet has, on a genuine neighborhood, a balanced
homogeneous fraction whose numerator belongs to the polynomial-operator ideal. -/
theorem normalizedJet_rational_fraction (atlas : TranslationAtlas A g)
    (T : ℕ) (I : Ideal G.CoordinateRing) (P : G.CoordinateRing) (hPI : P ∈ I)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (b : CoordinateChart G) (j : JetIndex A.parameterDimension T)
    (x : G.Point) (hx : g+x ∈ chartDomain G b) :
    ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧
      ∃ r : RationalCoefficient G, r.numerator ∈ polynomialOperatorIdeal atlas T I ∧
        ∀ y ∈ U, G.ambient.eval r.denominator (G.embedding y) ≠ 0 ∧
          r.value y = normalizedJet A g b P j y := by
  classical
  obtain ⟨a,ha⟩ := atlas.covers x
  let chart := atlas.chart a
  obtain ⟨U,hU,hxU,hUc,hUb⟩ := exists_translation_pivot_neighborhood chart b x ha hx
  let B := pivotPolynomial b D
  let F := fun w : List (Fin A.parameterDimension) => polynomialOperator chart w.length w.get P
  let Q := fun w : List (Fin A.parameterDimension) => polynomialOperator chart w.length w.get B
  let H := fun (w : List (Fin A.parameterDimension)) (y : G.Point) =>
    mixedDeriv (w.map (fun i => Pi.single i (1 : K))) (normalizedPullback A g b P y) 0
  have hF (w) : G.ambient.IsHomogeneous (F w) (fun i => chart.degree i * D i) :=
    polynomialOperator_homogeneous chart _ _ P D hP
  have hQ (w) : G.ambient.IsHomogeneous (Q w) (fun i => chart.degree i * D i) :=
    polynomialOperator_homogeneous chart _ _ B D (pivotPolynomial_homogeneous b D)
  have hFI (w : List (Fin A.parameterDimension)) (hw : w.length ≤ T) :
      F w ∈ polynomialOperatorIdeal atlas T I :=
    Ideal.mem_sup_right (Ideal.subset_span ⟨P,hPI,⟨D,hP⟩,a,w.length,hw,w.get,rfl⟩)
  have hQ0 (y : G.Point) (hy : y ∈ U) : G.ambient.eval (Q []) (G.embedding y) ≠ 0 := by
    rw [polynomialOperator_eval_mixed]
    simp only [List.map_nil,mixedDeriv]
    rw [evaluate_pivot_substitution]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ ((hUb y hy).2 i))
  have heq (w : List (Fin A.parameterDimension)) (_hw : w.length ≤ T)
      (y : G.Point) (hy : y ∈ U) :
      G.ambient.eval (F w) (G.embedding y) = G.ambient.eval (Q []) (G.embedding y) * H w y +
        ((properSplits w).map (fun p => G.ambient.eval (Q p.1) (G.embedding y) * H p.2 y)).sum := by
    have hfactor : evaluateCoefficientPolynomial A (substitutedPolynomial chart P) y =ᶠ[𝓝 0]
        (fun z => evaluateCoefficientPolynomial A (substitutedPolynomial chart B) y z *
          normalizedPullback A g b P y z) := by
      simpa only [B,evaluate_pivot_substitution] using
        chart_normalized_factorization chart b P D hP y (hUb y hy).1
    have hderiv := (mixedDeriv_congr hfactor (w.map (fun i => Pi.single i (1 : K)))).self_of_nhds
    rw [mixedDeriv_map_mul _
      (evaluated_coefficients_analytic _ (substituted_coeff_analytic chart B) y)
      (normalizedPullback_analytic A g b P y (hUb y hy).1)] at hderiv
    simpa only [F,Q,H,polynomialOperator_eval_mixed,List.map_nil,mixedDeriv] using hderiv
  obtain ⟨r,hrI,hr⟩ := rational_jet_recursion F Q H _ (polynomialOperatorIdeal atlas T I) U T
    hF hQ hFI hQ0 heq (List.ofFn j.directions) (by simpa using j.order_le)
  refine ⟨U,hU,hxU,r,hrI,?_⟩
  intro y hy
  refine ⟨(hr y hy).1,(hr y hy).2.trans ?_⟩
  dsimp only [H,normalizedJet]
  rw [mixedDeriv_map_eq_iteratedFDeriv _ (normalizedPullback_analytic A g b P y (hUb y hy).1)]
  apply iteratedFDeriv_apply_congr (List.length_ofFn ..)
  intro i
  simp only [List.get_ofFn]

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponRationalOrbitJets.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem chart_rational_orbit_germ (chart : TranslationChart A g)
    (r : RationalCoefficient G) (x : G.Point) (hx : x ∈ chart.domain) :
    (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
      r.value (g+x+A.map ⟨z,hz⟩) else 0) =ᶠ[𝓝 0]
      (fun z => evaluateCoefficientPolynomial A (substitutedPolynomial chart r.numerator) x z /
        evaluateCoefficientPolynomial A (substitutedPolynomial chart r.denominator) x z) := by
  filter_upwards [chart.represents x hx] with z hrep
  obtain ⟨hz,hrep⟩ := hrep
  rw [dif_pos hz,evaluate_substituted,evaluate_substituted]
  simpa only [add_comm x g] using
    (rationalCoefficient_value_of_lift r (x+g+A.map ⟨z,hz⟩)
      (fun q => evaluateCoefficientPolynomial A (chart.coordinates q) x z) hrep).symm

/-- Arbitrary regular rational orbit derivatives are locally balanced rational
functions, and a numerator in I produces a numerator in the actual operator
ideal. This is the coefficient control needed in the local-generation step. -/
theorem rational_orbit_jet_fraction (atlas : TranslationAtlas A g)
    (T : ℕ) (I : Ideal G.CoordinateRing) (r : RationalCoefficient G)
    (hrI : r.numerator ∈ I) (w : List (Fin A.parameterDimension)) (hw : w.length ≤ T)
    (x : G.Point) (hx : G.ambient.eval r.denominator (G.embedding (g+x)) ≠ 0) :
    ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧
      ∃ s : RationalCoefficient G, s.numerator ∈ polynomialOperatorIdeal atlas T I ∧
        ∀ y ∈ U, G.ambient.eval s.denominator (G.embedding y) ≠ 0 ∧
          s.value y = mixedDeriv (w.map (fun i => Pi.single i (1 : K)))
            (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
              r.value (g+y+A.map ⟨z,hz⟩) else 0) 0 := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  obtain ⟨a,ha⟩ := atlas.covers x
  let chart := atlas.chart a
  let F := fun v : List (Fin A.parameterDimension) =>
    polynomialOperator chart v.length v.get r.numerator
  let Q := fun v : List (Fin A.parameterDimension) =>
    polynomialOperator chart v.length v.get r.denominator
  let H := fun (v : List (Fin A.parameterDimension)) (y : G.Point) =>
    mixedDeriv (v.map (fun i => Pi.single i (1 : K)))
      (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
        r.value (g+y+A.map ⟨z,hz⟩) else 0) 0
  have hF (v) : G.ambient.IsHomogeneous (F v) (fun i => chart.degree i * r.degree i) :=
    polynomialOperator_homogeneous chart _ _ r.numerator r.degree r.numerator_homogeneous
  have hQ (v) : G.ambient.IsHomogeneous (Q v) (fun i => chart.degree i * r.degree i) :=
    polynomialOperator_homogeneous chart _ _ r.denominator r.degree r.denominator_homogeneous
  have hQ0 (y : G.Point) (hy : y ∈ chart.domain) :
      G.ambient.eval (Q []) (G.embedding y) = 0 ↔
        G.ambient.eval r.denominator (G.embedding (g+y)) = 0 := by
    rw [polynomialOperator_eval_mixed]
    simp only [List.map_nil,mixedDeriv,evaluate_substituted]
    obtain ⟨hz,hrep⟩ := (chart.represents y hy).self_of_nhds
    have hz' : (⟨0,hz⟩ : A.domain) = ⟨0,A.zero_mem⟩ := Subtype.ext rfl
    rw [hz',A.map_zero,add_zero] at hrep
    simpa only [add_comm y g] using G.ambient.eval_eq_zero_iff_of_lift
      (G.embedding (y+g)) (fun q => evaluateCoefficientPolynomial A (chart.coordinates q) y 0)
      hrep r.denominator r.degree r.denominator_homogeneous
  let U := chart.domain ∩ {y : G.Point | G.ambient.eval (Q []) (G.embedding y) ≠ 0}
  have hU : IsOpen U := chart.domain_isOpen.inter
    ((G.ambient.isOpen_basic (Q []) _ (hQ [])).preimage continuous_induced_dom)
  have hxU : x ∈ U := ⟨ha,(not_congr (hQ0 x ha)).mpr hx⟩
  have hFI (v : List (Fin A.parameterDimension)) (hv : v.length ≤ T) :
      F v ∈ polynomialOperatorIdeal atlas T I :=
    Ideal.mem_sup_right (Ideal.subset_span
      ⟨r.numerator,hrI,⟨r.degree,r.numerator_homogeneous⟩,a,v.length,hv,v.get,rfl⟩)
  have heq (v : List (Fin A.parameterDimension)) (_hv : v.length ≤ T)
      (y : G.Point) (hy : y ∈ U) :
      G.ambient.eval (F v) (G.embedding y) = G.ambient.eval (Q []) (G.embedding y) * H v y +
        ((properSplits v).map (fun p => G.ambient.eval (Q p.1) (G.embedding y) * H p.2 y)).sum := by
    have hn : evaluateCoefficientPolynomial A (substitutedPolynomial chart r.denominator) y 0 ≠ 0 := by
      have he : G.ambient.eval (Q []) (G.embedding y) =
          evaluateCoefficientPolynomial A (substitutedPolynomial chart r.denominator) y 0 := by
        simpa only [List.map_nil,mixedDeriv] using
          polynomialOperator_eval_mixed chart r.denominator y []
      exact ne_of_eq_of_ne he.symm hy.2
    have hqanalytic := evaluated_coefficients_analytic _ (substituted_coeff_analytic chart r.denominator) y
    have hanalytic := rational_orbit_pullback_analytic A (g+y) r ((not_congr (hQ0 y hy.1)).mp hy.2)
    have hfactor : evaluateCoefficientPolynomial A (substitutedPolynomial chart r.numerator) y =ᶠ[𝓝 0]
        (fun z => evaluateCoefficientPolynomial A (substitutedPolynomial chart r.denominator) y z *
          (if hz : z ∈ A.domain then r.value (g+y+A.map ⟨z,hz⟩) else 0)) := by
      filter_upwards [chart_rational_orbit_germ chart r y hy.1,
        hqanalytic.continuousAt.eventually_ne hn] with z hz hne
      rw [hz,mul_div_cancel₀ _ hne]
    have hd := (mixedDeriv_congr hfactor (v.map (fun i => Pi.single i (1 : K)))).self_of_nhds
    rw [mixedDeriv_map_mul _ hqanalytic hanalytic] at hd
    simpa only [F,Q,H,polynomialOperator_eval_mixed,List.map_nil,mixedDeriv] using hd
  obtain ⟨s,hsI,hs⟩ := rational_jet_recursion F Q H _ (polynomialOperatorIdeal atlas T I) U T
    hF hQ hFI (fun y hy => hy.2) heq w hw
  exact ⟨U,hU,hxU,s,hsI,hs⟩

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponTranslatedJetGerms.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

theorem mixedDeriv_append (u v : List E) (f : E → K) :
    mixedDeriv (u ++ v) f = mixedDeriv u (mixedDeriv v f) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, mixedDeriv, ih]

theorem mixedDeriv_comp_add_left (w : List E) (f : E → K) (a : E) :
    mixedDeriv w (fun z => f (a + z)) = fun z => mixedDeriv w f (a + z) := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    funext z
    simp only [mixedDeriv, ih, fderiv_comp_add_left]

end PhilipponMultiplicity.JetSupport

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem projective_ratios_eq {ι : Type*} (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk K v hv = Projectivization.mk K w hw) (i j : ι) :
    v i / v j = w i / w j := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K v w hv hw).mp h
  have he (k : ι) : v k = (a : K) * w k := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha k).symm
  rw [he i,he j,mul_div_mul_left _ _ a.ne_zero]

/-- Move the base point of a normalized analytic lift by a small group parameter.
The equality is a germ in the second parameter; its neighborhood may depend on
the first one, exactly as allowed by the original analytic-subgroup data. -/
theorem normalizedPullback_shift_germ (A : AnalyticSubgroup G)
    (g g' x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      normalizedPullback A g' b P (g + x + A.map ⟨z,hz⟩) =ᶠ[𝓝 0]
        (fun w => normalizedPullback A (g + g') b P x (z + w)) := by
  let q := g + g' + x
  have hrep := A.lift_represents q
  have hrepnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ᶠ t in 𝓝 z, ∃ ht : t ∈ A.domain, ∀ i : G.FactorIndex,
        ∃ h : (fun j => A.lift q t ⟨i,j⟩) ≠ 0,
          Projectivization.mk K (fun j => A.lift q t ⟨i,j⟩) h =
            G.embedding (q + A.map ⟨t,ht⟩) i := hrep.eventually_nhds
  filter_upwards [A.domain_open.mem_nhds A.zero_mem,hrepnear] with z hz hrepsz
  refine ⟨hz,?_⟩
  have hadd : Tendsto (fun w : A.ParameterSpace => z + w) (𝓝 0) (𝓝 z) := by
    have hc : ContinuousAt (fun w : A.ParameterSpace => z + w) 0 :=
      continuousAt_const.add continuousAt_id
    simpa only [add_zero] using hc.tendsto
  filter_upwards [A.lift_represents (g' + (g + x + A.map ⟨z,hz⟩)),
      hadd.eventually hrepsz] with w hleft hright
  obtain ⟨hw,hl⟩ := hleft
  obtain ⟨hzw,hr⟩ := hright
  have heq : g' + (g + x + A.map ⟨z,hz⟩) + A.map ⟨w,hw⟩ =
      q + A.map ⟨z+w,hzw⟩ := by
    rw [A.map_add ⟨z,hz⟩ ⟨w,hw⟩ hzw]
    dsimp only [q]
    abel
  unfold normalizedPullback
  apply congrArg (fun f : G.ambient.Variable → K => MvPolynomial.eval f P)
  funext v
  obtain ⟨hvl,hpl⟩ := hl v.1
  obtain ⟨hvr,hpr⟩ := hr v.1
  exact projective_ratios_eq _ _ hvl hvr
    (hpl.trans ((congrArg (fun y => G.embedding y v.1) heq).trans hpr.symm)) v.2 (b v.1)

/-- A translated normalized jet is the same jet of the original orbit germ
at the displaced parameter. This is the analytic step on printed p. 374. -/
theorem normalizedJet_translate_germ (A : AnalyticSubgroup G)
    (g g' x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing)
    {T : ℕ} (j : JetIndex A.parameterDimension T) :
    (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
      normalizedJet A g' b P j (g + x + A.map ⟨z,hz⟩) else 0) =ᶠ[𝓝 0]
      (fun z => iteratedFDeriv K j.order (normalizedPullback A (g+g') b P x) z
        (fun i => Pi.single (j.directions i) 1)) := by
  filter_upwards [normalizedPullback_shift_germ A g g' x b P] with z hz
  obtain ⟨hz,he⟩ := hz
  rw [dif_pos hz]
  unfold normalizedJet
  rw [(he.iteratedFDeriv (𝕜 := K) j.order).self_of_nhds]
  rw [iteratedFDeriv_comp_add_left]
  simp only [add_zero]

/-- Two successive ordered derivatives of translated orbit sections combine
by concatenating their direction lists. -/
theorem normalizedJet_composition (A : AnalyticSubgroup G)
    (g g' x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing)
    (hx : g + g' + x ∈ chartDomain G b)
    (u v : List (Fin A.parameterDimension)) :
    JetSupport.mixedDeriv (u.map (fun i => Pi.single i (1 : K)))
      (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
        normalizedJet A g' b P
          (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)
          (g + x + A.map ⟨z,hz⟩) else 0) 0 =
      JetSupport.mixedDeriv ((u ++ v).map (fun i => Pi.single i (1 : K)))
        (normalizedPullback A (g + g') b P x) 0 := by
  have ha := normalizedPullback_analytic A (g+g') b P x hx
  have he := normalizedJet_translate_germ A g g' x b P
    (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)
  have hv : (fun z => iteratedFDeriv K v.length (normalizedPullback A (g+g') b P x) z
      (fun i => Pi.single (v.get i) (1 : K))) =ᶠ[𝓝 0]
      JetSupport.mixedDeriv (v.map (fun i => Pi.single i (1 : K)))
        (normalizedPullback A (g+g') b P x) := by
    filter_upwards [ha.eventually_analyticAt] with z hz
    exact (JetSupport.mixedDeriv_map_eq_iteratedFDeriv
      (fun i : Fin A.parameterDimension => Pi.single i (1 : K)) hz v).symm
  rw [List.map_append,JetSupport.mixedDeriv_append]
  exact (JetSupport.mixedDeriv_congr (he.trans hv) _).self_of_nhds

theorem normalizedJet_composition_finite (A : AnalyticSubgroup G)
    (g g' x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing)
    (hx : g + g' + x ∈ chartDomain G b)
    (u v : List (Fin A.parameterDimension)) :
    iteratedFDeriv K u.length
      (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
        normalizedJet A g' b P
          (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)
          (g + x + A.map ⟨z,hz⟩) else 0) 0
        (fun i => Pi.single (u.get i) 1) =
      normalizedJet A (g+g') b P
        (⟨(u++v).length,le_rfl,(u++v).get⟩ :
          JetIndex A.parameterDimension (u++v).length) x := by
  have ha := normalizedPullback_analytic A (g+g') b P x hx
  have he := normalizedJet_translate_germ A g g' x b P
    (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)
  have hv : (fun z => iteratedFDeriv K v.length (normalizedPullback A (g+g') b P x) z
      (fun i => Pi.single (v.get i) (1 : K))) =ᶠ[𝓝 0]
      JetSupport.mixedDeriv (v.map (fun i => Pi.single i (1 : K)))
        (normalizedPullback A (g+g') b P x) := by
    filter_upwards [ha.eventually_analyticAt] with z hz
    exact (JetSupport.mixedDeriv_map_eq_iteratedFDeriv
      (fun i : Fin A.parameterDimension => Pi.single i (1 : K)) hz v).symm
  have hf := (JetSupport.mixedDeriv_analytic ha
    (v.map (fun i => Pi.single i (1 : K)))).congr (he.trans hv).symm
  rw [← JetSupport.mixedDeriv_map_eq_iteratedFDeriv
    (fun i : Fin A.parameterDimension => Pi.single i (1 : K)) hf u,
    normalizedJet_composition A g g' x b P hx u v]
  exact JetSupport.mixedDeriv_map_eq_iteratedFDeriv
    (fun i : Fin A.parameterDimension => Pi.single i (1 : K)) ha (u++v)

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponOrbitLocalExpressions.lean

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.JetSupport
variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E]

theorem mixedDeriv_fin_sum {n : ℕ} (f : Fin n → E → K) (x : E)
    (hf : ∀ i, AnalyticAt K (f i) x) (w : List E) :
    mixedDeriv w (fun y => ∑ i, f i y) x = ∑ i, mixedDeriv w (f i) x := by
  induction w generalizing x with
  | nil => rfl
  | cons v w ih =>
    have heq : mixedDeriv w (fun y => ∑ i, f i y) =ᶠ[𝓝 x]
        (fun y => ∑ i, mixedDeriv w (f i) y) := by
      filter_upwards [Filter.eventually_all.mpr (fun i => (hf i).eventually_analyticAt)] with y hy
      exact ih y hy
    change fderiv K _ x v = ∑ i, fderiv K _ x v
    rw [heq.fderiv_eq,fderiv_fun_sum (fun i _ => (mixedDeriv_analytic (hf i) w).differentiableAt)]
    simp only [ContinuousLinearMap.sum_apply]

end PhilipponMultiplicity.JetSupport

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

def orbitPullback (A : AnalyticSubgroup G) (f : G.Point → K) (p : G.Point)
    (z : A.ParameterSpace) : K :=
  if hz : z ∈ A.domain then f (p+A.map ⟨z,hz⟩) else 0

def orbitJet (A : AnalyticSubgroup G) (g : G.Point)
    (w : List (Fin A.parameterDimension)) (f : G.Point → K) (x : G.Point) : K :=
  mixedDeriv (w.map (fun i => Pi.single i (1 : K))) (orbitPullback A f (g+x)) 0

theorem orbitPullback_zero (A : AnalyticSubgroup G) (f : G.Point → K) (p : G.Point) :
    orbitPullback A f p 0 = f p := by
  simp only [orbitPullback,dif_pos A.zero_mem,A.map_zero,add_zero]

theorem orbitPullback_congr_on (A : AnalyticSubgroup G) (f h : G.Point → K)
    (p : G.Point) (U : Set G.Point) (hU : @IsOpen _ G.zariskiTopology U) (hp : p ∈ U)
    (heq : ∀ y ∈ U, f y = h y) :
    orbitPullback A f p =ᶠ[𝓝 0] orbitPullback A h p := by
  filter_upwards [orbit_eventually_mem_open A p U hU hp] with z hz
  obtain ⟨hz,hy⟩ := hz
  simp only [orbitPullback,dif_pos hz]
  exact heq _ hy

theorem orbitPullback_mul (A : AnalyticSubgroup G) (f h : G.Point → K) (p : G.Point) :
    orbitPullback A (fun y => f y * h y) p =
      fun z => orbitPullback A f p z * orbitPullback A h p z := by
  funext z
  unfold orbitPullback
  split_ifs <;> simp

theorem orbitPullback_fin_sum (A : AnalyticSubgroup G) {n : ℕ}
    (f : Fin n → G.Point → K) (p : G.Point) :
    orbitPullback A (fun y => ∑ i, f i y) p = fun z => ∑ i, orbitPullback A (f i) p z := by
  funext z
  unfold orbitPullback
  split_ifs <;> simp

theorem orbitPullback_chartValue_germ (A : AnalyticSubgroup G) (g x : G.Point)
    (b : CoordinateChart G) (P : G.CoordinateRing) :
    orbitPullback A (chartValue G b P) (g+x) =ᶠ[𝓝 0] normalizedPullback A g b P x := by
  filter_upwards [A.lift_represents (g+x)] with z hz
  obtain ⟨hz,hrep⟩ := hz
  simp only [orbitPullback,dif_pos hz,chartValue,normalizedPullback]
  apply congrArg (fun v : G.ambient.Variable → K => MvPolynomial.eval v P)
  funext v
  obtain ⟨hv,heq⟩ := hrep v.1
  exact (projective_ratios_eq _ _ hv (G.embedding (g+x+A.map ⟨z,hz⟩) v.1).rep_nonzero
    (heq.trans (G.embedding (g+x+A.map ⟨z,hz⟩) v.1).mk_rep.symm) v.2 (b v.1)).symm

theorem orbitPullback_chartValue_analytic (A : AnalyticSubgroup G) (g x : G.Point)
    (b : CoordinateChart G) (P : G.CoordinateRing) (hx : g+x ∈ chartDomain G b) :
    AnalyticAt K (orbitPullback A (chartValue G b P) (g+x)) 0 :=
  (normalizedPullback_analytic A g b P x hx).congr
    (orbitPullback_chartValue_germ A g x b P).symm

theorem orbitJet_chartValue (A : AnalyticSubgroup G) (g : G.Point)
    (w : List (Fin A.parameterDimension)) (b : CoordinateChart G) (P : G.CoordinateRing)
    (x : G.Point) (hx : g+x ∈ chartDomain G b) :
    orbitJet A g w (chartValue G b P) x = normalizedJet A g b P
      (⟨w.length,le_rfl,w.get⟩ : JetIndex A.parameterDimension w.length) x := by
  unfold orbitJet
  rw [(mixedDeriv_congr (orbitPullback_chartValue_germ A g x b P) _).self_of_nhds]
  exact mixedDeriv_map_eq_iteratedFDeriv
    (fun i : Fin A.parameterDimension => Pi.single i (1 : K))
    (normalizedPullback_analytic A g b P x hx) w

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponDifferentiateLocalSpan.lean

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

/-- Differentiation preserves finite local generation. Every Leibniz coefficient
is a genuine regular rational orbit derivative on a neighborhood, rather than
an arbitrarily assigned pointwise scalar. -/
theorem LocalSpanAt.orbitJet (atlas : TranslationAtlas A g)
    {S R : Set (LocalSection G)} {f : G.Point → K} {x : G.Point}
    (T : ℕ) (h : LocalSpanAt S f (g+x))
    (ha : ∀ s : S, ∀ y : G.Point, g+y ∈ s.val.domain →
      AnalyticAt K (orbitPullback A s.val.value (g+y)) 0)
    (hd : ∀ s : S, ∀ y : G.Point, g+y ∈ s.val.domain →
      ∀ v : List (Fin A.parameterDimension), v.length ≤ T →
        LocalSpanAt R (OperatorSupport.orbitJet A g v s.val.value) y)
    (w : List (Fin A.parameterDimension)) (hw : w.length ≤ T) :
    LocalSpanAt R (OperatorSupport.orbitJet A g w f) x := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  obtain ⟨U,hU,hx,n,s,r,hs,heq⟩ := h
  let V : Set G.Point := {y | g+y ∈ U}
  have hV : IsOpen V := translation_preimage_isOpen g U hU
  have hxV : x ∈ V := hx
  have hterm (i : Fin n) (a b : List (Fin A.parameterDimension))
      (ha' : a.length ≤ T) (hb : b.length ≤ T) :
      LocalSpanAt R (fun y => OperatorSupport.orbitJet A g a (r i).value y *
        OperatorSupport.orbitJet A g b (s i).val.value y) x := by
    obtain ⟨W,hW,hxW,q,hqI,hq⟩ := rational_orbit_jet_fraction atlas T ⊤ (r i)
      (by trivial) a ha' x (hs i (g+x) hx).2
    have hh := (hd (s i) x (hs i (g+x) hx).1 b hb).rational_mul q W hW hxW
      (fun y hy => (hq y hy).1)
    apply hh.congr_on W hW hxW
    intro y hy
    exact congrArg (fun c => c * OperatorSupport.orbitJet A g b (s i).val.value y)
      (hq y hy).2
  have hprod (i : Fin n) :
      LocalSpanAt R (OperatorSupport.orbitJet A g w
        (fun y => (r i).value y * (s i).val.value y)) x := by
    have hmain := hterm i [] w (Nat.zero_le _) hw
    have hrest := LocalSpanAt.list_sum (properSplits w)
      (fun p y => OperatorSupport.orbitJet A g p.1 (r i).value y *
        OperatorSupport.orbitJet A g p.2 (s i).val.value y) x (by
          intro p hp
          obtain ⟨hp₁,hp₂,hp₃⟩ := properSplits_lengths w p hp
          exact hterm i p.1 p.2 (by omega) (by omega))
    apply (hmain.add hrest).congr_on V hV hxV
    intro y hy
    have hr := rational_orbit_pullback_analytic A (g+y) (r i) (hs i (g+y) hy).2
    have hf := ha (s i) y (hs i (g+y) hy).1
    dsimp only [OperatorSupport.orbitJet]
    rw [orbitPullback_mul]
    exact (mixedDeriv_map_mul (fun i : Fin A.parameterDimension => Pi.single i (1 : K))
      hr hf w).symm
  apply (LocalSpanAt.fin_sum _ x hprod).congr_on V hV hxV
  intro y hy
  have hgerm := orbitPullback_congr_on A f
    (fun y => ∑ i, (r i).value y * (s i).val.value y) (g+y) U hU hy heq
  have he := (mixedDeriv_congr hgerm
    (w.map (fun i => Pi.single i (1 : K)))).self_of_nhds
  rw [orbitPullback_fin_sum] at he
  have hh (i : Fin n) : AnalyticAt K
      (orbitPullback A (fun y => (r i).value y * (s i).val.value y) (g+y)) 0 := by
    rw [orbitPullback_mul]
    exact (rational_orbit_pullback_analytic A (g+y) (r i) (hs i (g+y) hy).2).mul
      (ha (s i) y (hs i (g+y) hy).1)
  exact (he.trans (mixedDeriv_fin_sum _ 0 hh _)).symm

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponIteratedJetSections.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

/-- Replacing a local generator by an equal section on its domain preserves
local ideal membership. Equality outside the domain is unnecessary. -/
theorem locallyGeneratedIdeal_le_of_section_replacements
    (S T : Set (LocalSection G))
    (h : ∀ f : S, ∃ t : T, f.val.domain ⊆ t.val.domain ∧
      ∀ x ∈ f.val.domain, f.val.value x = t.val.value x) :
    locallyGeneratedIdeal G S ≤ locallyGeneratedIdeal G T := by
  classical
  apply Ideal.span_le.mpr
  rintro P ⟨hP,hlocal⟩
  apply Ideal.subset_span
  refine ⟨hP,?_⟩
  intro x
  obtain ⟨b,U,hU,hx,hUb,n,f,r,hfr,heq⟩ := hlocal x
  choose t hdom hval using (fun i => h (f i))
  refine ⟨b,U,hU,hx,hUb,n,t,r,?_,?_⟩
  · intro i y hy
    exact ⟨hdom i (hfr i y hy).1,(hfr i y hy).2⟩
  · intro y hy
    rw [heq y hy]
    apply Finset.sum_congr rfl
    intro i _
    rw [hval i y (hfr i y hy).1]

variable [CompleteSpace K]

/-- The ideal generated by the paper's two-parameter jets is exactly the
ideal generated by jets of total order at most the sum. -/
theorem iterated_jet_sections_eq_differentialIdeal
    (A : AnalyticSubgroup G) (g g' : G.Point) (T T' : ℕ) (I : Ideal G.CoordinateRing) :
    locallyGeneratedIdeal G (iteratedDifferentialSections A g g' T T' I) =
      differentialIdeal A (g+g') (T+T') I := by
  apply le_antisymm
  · apply locallyGeneratedIdeal_le_of_section_replacements
    rintro ⟨f,P,hPI,hP,b,u,hu,v,hv,rfl⟩
    let j : JetIndex A.parameterDimension (T+T') :=
      ⟨(u++v).length,by simpa only [List.length_append] using Nat.add_le_add hu hv,(u++v).get⟩
    refine ⟨⟨⟨{x | g+g'+x ∈ chartDomain G b},normalizedJet A (g+g') b P j⟩,
      P,hPI,hP,b,j,rfl⟩,fun x hx => hx,?_⟩
    intro x hx
    exact normalizedJet_composition_finite A g g' x b P hx u v
  · apply locallyGeneratedIdeal_le_of_section_replacements
    rintro ⟨f,P,hPI,hP,b,j,rfl⟩
    let w := List.ofFn j.directions
    let u := w.take T
    let v := w.drop T
    have hu : u.length ≤ T := List.length_take_le _ _
    have hv : v.length ≤ T' := by
      dsimp [v,w]
      rw [List.length_drop,List.length_ofFn]
      have hj := j.order_le
      omega
    let s : LocalSection G :=
      ⟨{x | g+g'+x ∈ chartDomain G b}, fun x =>
        iteratedFDeriv K u.length
          (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
            normalizedJet A g' b P
              (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)
              (g + x + A.map ⟨z,hz⟩) else 0) 0
            (fun i => Pi.single (u.get i) 1)⟩
    refine ⟨⟨s,P,hPI,hP,b,u,hu,v,hv,rfl⟩,fun x hx => hx,?_⟩
    intro x hx
    change normalizedJet A (g+g') b P j x = _
    dsimp only [s]
    have hw : normalizedJet A (g+g') b P
        (⟨w.length,le_rfl,w.get⟩ : JetIndex A.parameterDimension w.length) x =
        normalizedJet A (g+g') b P j x := by
      unfold normalizedJet
      apply JetSupport.iteratedFDeriv_apply_congr (List.length_ofFn (f := j.directions))
      intro i
      simp only [w,List.get_ofFn]
    have hs := congrArg
      (fun a : List (Fin A.parameterDimension) => normalizedJet A (g+g') b P
        (⟨a.length,le_rfl,a.get⟩ : JetIndex A.parameterDimension a.length) x)
      (List.take_append_drop T w)
    exact hw.symm.trans (hs.symm.trans (normalizedJet_composition_finite A g g' x b P hx u v).symm)

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalGenerationForward.lean

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem normalizedJet_eq_word (A : AnalyticSubgroup G) (g : G.Point)
    (b : CoordinateChart G) (P : G.CoordinateRing)
    {T : ℕ} (j : JetIndex A.parameterDimension T) :
    normalizedJet A g b P j = normalizedJet A g b P
      (⟨(List.ofFn j.directions).length,le_rfl,(List.ofFn j.directions).get⟩ :
        JetIndex A.parameterDimension (List.ofFn j.directions).length) := by
  funext x
  symm
  apply iteratedFDeriv_apply_congr (List.length_ofFn (f := j.directions))
  intro i
  simp only [List.get_ofFn]

theorem orbitPullback_normalizedJet_analytic (A : AnalyticSubgroup G)
    (g g' x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing)
    {T : ℕ} (j : JetIndex A.parameterDimension T)
    (hx : g+g'+x ∈ chartDomain G b) :
    AnalyticAt K (orbitPullback A (normalizedJet A g' b P j) (g+x)) 0 := by
  rw [normalizedJet_eq_word A g' b P j]
  let v := List.ofFn j.directions
  have ha := normalizedPullback_analytic A (g+g') b P x hx
  have he := normalizedJet_translate_germ A g g' x b P
    (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)
  have hv : (fun z => iteratedFDeriv K v.length (normalizedPullback A (g+g') b P x) z
      (fun i => Pi.single (v.get i) (1 : K))) =ᶠ[𝓝 0]
      mixedDeriv (v.map (fun i => Pi.single i (1 : K)))
        (normalizedPullback A (g+g') b P x) := by
    filter_upwards [ha.eventually_analyticAt] with z hz
    exact (mixedDeriv_map_eq_iteratedFDeriv
      (fun i : Fin A.parameterDimension => Pi.single i (1 : K)) hz v).symm
  exact (mixedDeriv_analytic ha _).congr (he.trans hv).symm

theorem inner_section_orbitJet_localSpan (A : AnalyticSubgroup G)
    (g g' : G.Point) (T T' : ℕ) (I : Ideal G.CoordinateRing)
    (s : differentialSections A g' T' I) (x : G.Point) (hx : g+x ∈ s.val.domain)
    (w : List (Fin A.parameterDimension)) (hw : w.length ≤ T) :
    LocalSpanAt (iteratedDifferentialSections A g g' T T' I)
      (orbitJet A g w s.val.value) x := by
  obtain ⟨s,P,hPI,hP,b,j,rfl⟩ := s
  let v := List.ofFn j.directions
  have hv : v.length ≤ T' := by simpa only [v,List.length_ofFn] using j.order_le
  let f : LocalSection G :=
    ⟨{y | g+g'+y ∈ chartDomain G b}, fun y => iteratedFDeriv K w.length
      (orbitPullback A (normalizedJet A g' b P
        (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)) (g+y)) 0
          (fun i => Pi.single (w.get i) 1)⟩
  have hf : f ∈ iteratedDifferentialSections A g g' T T' I := ⟨P,hPI,hP,b,w,hw,v,hv,rfl⟩
  have hx' : g+g'+x ∈ chartDomain G b := by
    simpa only [Set.mem_setOf_eq,add_assoc,add_left_comm,add_comm] using hx
  have hU := translation_preimage_isOpen (g+g') (chartDomain G b) (chartDomain_isOpen b)
  have hh := localSpanAt_section _ ⟨f,hf⟩ x f.domain hU hx' (fun _ h => h)
  apply hh.congr_on f.domain hU hx'
  intro y hy
  change iteratedFDeriv K w.length _ 0 _ = orbitJet A g w (normalizedJet A g' b P j) y
  rw [normalizedJet_eq_word A g' b P j]
  exact (mixedDeriv_map_eq_iteratedFDeriv
    (fun i : Fin A.parameterDimension => Pi.single i (1 : K))
    (orbitPullback_normalizedJet_analytic A g g' y b P _ hy) w).symm

theorem differentialIdeal_le_iterated_jet_sections (A : AnalyticSubgroup G)
    (g g' : G.Point) (atlas : TranslationAtlas A g)
    (T T' : ℕ) (I : Ideal G.CoordinateRing) :
    differentialIdeal A g T (differentialIdeal A g' T' I) ≤
      locallyGeneratedIdeal G (iteratedDifferentialSections A g g' T T' I) := by
  apply locallyGeneratedIdeal_le_of_localSpan
  rintro ⟨s,P,hPI,hP,b,j,rfl⟩ x hx
  have hlocal : LocalSpanAt (differentialSections A g' T' I) (chartValue G b P) (g+x) :=
    locallyGeneratedIdeal_le_localSectionIdeal _ b (g+x) hx hPI
  let w := List.ofFn j.directions
  have hw : w.length ≤ T := by simpa only [w,List.length_ofFn] using j.order_le
  have hh := hlocal.orbitJet atlas T (R := iteratedDifferentialSections A g g' T T' I)
    (by
      rintro ⟨f,Q,hQI,hQ,c,k,rfl⟩ y hy
      apply orbitPullback_normalizedJet_analytic A g g' y c Q k
      simpa only [Set.mem_setOf_eq,add_assoc,add_comm,add_left_comm] using hy)
    (fun f y hy u hu => inner_section_orbitJet_localSpan A g g' T T' I f y hy u hu) w hw
  apply hh.congr_on {y | g+y ∈ chartDomain G b}
    (translation_preimage_isOpen g _ (chartDomain_isOpen b)) hx
  intro y hy
  exact (orbitJet_chartValue A g w b P y hy).trans
    (congrFun (normalizedJet_eq_word A g b P j).symm y)

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponPolynomialJetLeibniz.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

/-- The opposite Leibniz expansion holds for every polynomial chart, whether
or not its chart domain contains the point. -/
theorem polynomialOperator_normalized_jet_expansion (chart : TranslationChart A g)
    (b : CoordinateChart G) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (w : List (Fin A.parameterDimension))
    (x : G.Point) (hx : g+x ∈ chartDomain G b) :
    G.ambient.eval (polynomialOperator chart w.length w.get P) (G.embedding x) =
      G.ambient.eval (polynomialOperator chart 0 Fin.elim0 (pivotPolynomial b D)) (G.embedding x) *
        normalizedJet A g b P (⟨w.length,le_rfl,w.get⟩ : JetIndex A.parameterDimension w.length) x +
      ((properSplits w).map (fun p =>
        G.ambient.eval (polynomialOperator chart p.1.length p.1.get (pivotPolynomial b D)) (G.embedding x) *
          normalizedJet A g b P (⟨p.2.length,le_rfl,p.2.get⟩ : JetIndex A.parameterDimension p.2.length) x)).sum := by
  have hfactor : evaluateCoefficientPolynomial A (substitutedPolynomial chart P) x =ᶠ[𝓝 0]
      (fun z => evaluateCoefficientPolynomial A (substitutedPolynomial chart (pivotPolynomial b D)) x z *
        normalizedPullback A g b P x z) := by
    simpa only [evaluate_pivot_substitution] using chart_normalized_factorization chart b P D hP x hx
  have hderiv := (mixedDeriv_congr hfactor (w.map (fun i => Pi.single i (1 : K)))).self_of_nhds
  rw [mixedDeriv_map_mul _
    (evaluated_coefficients_analytic _ (substituted_coeff_analytic chart (pivotPolynomial b D)) x)
    (normalizedPullback_analytic A g b P x hx)] at hderiv
  have hj (v : List (Fin A.parameterDimension)) :
      mixedDeriv (v.map (fun i => Pi.single i (1 : K))) (normalizedPullback A g b P x) 0 =
        normalizedJet A g b P (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length) x :=
    mixedDeriv_map_eq_iteratedFDeriv _ (normalizedPullback_analytic A g b P x hx) v
  have hzero : polynomialOperator chart 0 Fin.elim0 (pivotPolynomial b D) =
      polynomialOperator chart ([] : List (Fin A.parameterDimension)).length [].get (pivotPolynomial b D) := by
    congr 1
    exact Subsingleton.elim _ _
  rw [hzero]
  simpa only [polynomialOperator_eval_mixed,List.map_nil,mixedDeriv,hj] using hderiv

/-- The coefficients in the reverse generator expansion are balanced
homogeneous fractions on any source coordinate chart. -/
def polynomialJetCoefficient (chart : TranslationChart A g) (b c : CoordinateChart G)
    (D : G.FactorIndex → ℕ) (w : List (Fin A.parameterDimension)) : RationalCoefficient G :=
  ⟨polynomialOperator chart w.length w.get (pivotPolynomial b D),
    pivotPolynomial c (fun i => chart.degree i * D i),fun i => chart.degree i * D i,
    polynomialOperator_homogeneous chart _ _ _ D (pivotPolynomial_homogeneous b D),
    pivotPolynomial_homogeneous c _⟩

theorem polynomialJetCoefficient_regular (chart : TranslationChart A g) (b c : CoordinateChart G)
    (D : G.FactorIndex → ℕ) (w : List (Fin A.parameterDimension)) (x : G.Point)
    (hx : x ∈ chartDomain G c) :
    G.ambient.eval (polynomialJetCoefficient chart b c D w).denominator (G.embedding x) ≠ 0 :=
  pivotPolynomial_eval_ne_zero c _ x hx

theorem chartValue_polynomialOperator_jet_expansion (chart : TranslationChart A g)
    (b c : CoordinateChart G) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (w : List (Fin A.parameterDimension))
    (x : G.Point) (hx : g+x ∈ chartDomain G b) :
    chartValue G c (polynomialOperator chart w.length w.get P) x =
      (polynomialJetCoefficient chart b c D []).value x *
        normalizedJet A g b P (⟨w.length,le_rfl,w.get⟩ : JetIndex A.parameterDimension w.length) x +
      ((properSplits w).map (fun p =>
        (polynomialJetCoefficient chart b c D p.1).value x *
          normalizedJet A g b P (⟨p.2.length,le_rfl,p.2.get⟩ : JetIndex A.parameterDimension p.2.length) x)).sum := by
  rw [chartValue_eq_div_pivot c _ _ (polynomialOperator_homogeneous chart _ _ P D hP),
    polynomialOperator_normalized_jet_expansion chart b P D hP w x hx,add_div]
  have hzero : polynomialOperator chart 0 Fin.elim0 (pivotPolynomial b D) =
      polynomialOperator chart ([] : List (Fin A.parameterDimension)).length [].get (pivotPolynomial b D) := by
    congr 1
    exact Subsingleton.elim _ _
  rw [hzero]
  dsimp only [polynomialJetCoefficient,RationalCoefficient.value]
  congr 1
  · exact mul_div_right_comm _ _ _
  · induction properSplits w with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons,List.sum_cons,add_div,ih,mul_div_right_comm]
      rfl

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponReverseJetGenerators.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem polynomialOperator_order_congr (chart : TranslationChart A g) (P : G.CoordinateRing)
    {n m : ℕ} (h : n = m) (u : Fin n → Fin A.parameterDimension)
    (v : Fin m → Fin A.parameterDimension) (huv : ∀ i, u i = v (Fin.cast h i)) :
    polynomialOperator chart n u P = polynomialOperator chart m v P := by
  subst m
  have heq : u = v := by funext i; exact huv i
  rw [heq]

theorem polynomialOperator_ofFn (chart : TranslationChart A g) (P : G.CoordinateRing)
    (n : ℕ) (directions : Fin n → Fin A.parameterDimension) :
    polynomialOperator chart (List.ofFn directions).length (List.ofFn directions).get P =
      polynomialOperator chart n directions P := by
  apply polynomialOperator_order_congr chart P (List.length_ofFn ..)
  intro i
  simp only [List.get_ofFn]

theorem normalized_word_jet_localSpan (atlas : TranslationAtlas A g)
    (T : ℕ) (I : Ideal G.CoordinateRing) (P : G.CoordinateRing) (hPI : P ∈ I)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (b : CoordinateChart G) (w : List (Fin A.parameterDimension)) (hw : w.length ≤ T)
    (x : G.Point) (hx : g+x ∈ chartDomain G b) :
    LocalSpanAt (differentialSections A g T I)
      (normalizedJet A g b P (⟨w.length,le_rfl,w.get⟩ : JetIndex A.parameterDimension w.length)) x := by
  obtain ⟨a,ha⟩ := atlas.covers x
  obtain ⟨U,hU,hxU,hUa,hUb⟩ := exists_translation_pivot_neighborhood (atlas.chart a) b x ha hx
  let j : JetIndex A.parameterDimension T := ⟨w.length,hw,w.get⟩
  let f : differentialSections A g T I :=
    ⟨⟨{y | g+y ∈ chartDomain G b},normalizedJet A g b P j⟩,P,hPI,⟨D,hP⟩,b,j,rfl⟩
  exact localSpanAt_section _ f x U hU hxU (fun y hy => (hUb y hy).1)

theorem polynomialOperator_localSpan (atlas : TranslationAtlas A g)
    (T : ℕ) (I : Ideal G.CoordinateRing) (chart : TranslationChart A g)
    (P : G.CoordinateRing) (hPI : P ∈ I) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (w : List (Fin A.parameterDimension)) (hw : w.length ≤ T)
    (c : CoordinateChart G) (x : G.Point) (hx : x ∈ chartDomain G c) :
    LocalSpanAt (differentialSections A g T I)
      (chartValue G c (polynomialOperator chart w.length w.get P)) x := by
  classical
  obtain ⟨b,hb⟩ := exists_chartDomain (g+x)
  have hterm (u v : List (Fin A.parameterDimension)) (hv : v.length ≤ T) :
      LocalSpanAt (differentialSections A g T I)
        (fun y => (polynomialJetCoefficient chart b c D u).value y *
          normalizedJet A g b P (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length) y) x :=
    (normalized_word_jet_localSpan atlas T I P hPI D hP b v hv x hb).rational_mul
      (polynomialJetCoefficient chart b c D u) (chartDomain G c) (chartDomain_isOpen c) hx
      (fun y hy => polynomialJetCoefficient_regular chart b c D u y hy)
  have hrest := LocalSpanAt.list_sum (properSplits w)
    (fun p y => (polynomialJetCoefficient chart b c D p.1).value y *
      normalizedJet A g b P (⟨p.2.length,le_rfl,p.2.get⟩ : JetIndex A.parameterDimension p.2.length) y) x
    (fun p hp => hterm p.1 p.2 (by have hh := (properSplits_lengths w p hp).2.2; omega))
  have hsum := (hterm [] w hw).add hrest
  obtain ⟨a,ha⟩ := atlas.covers x
  obtain ⟨U,hU,hxU,hUa,hUb⟩ := exists_translation_pivot_neighborhood (atlas.chart a) b x ha hb
  apply hsum.congr_on U hU hxU
  intro y hy
  exact (chartValue_polynomialOperator_jet_expansion chart b c P D hP w y (hUb y hy).1).symm

theorem polynomialOperatorIdeal_le_localSectionIdeal (atlas : TranslationAtlas A g)
    (T : ℕ) (I : Ideal G.CoordinateRing) (b : CoordinateChart G) (x : G.Point)
    (hx : x ∈ chartDomain G b) :
    polynomialOperatorIdeal atlas T I ≤ localSectionIdeal (differentialSections A g T I) b x hx := by
  apply sup_le (groupIdeal_le_localSectionIdeal _ b x hx)
  apply Ideal.span_le.mpr
  rintro Q ⟨P,hPI,⟨D,hP⟩,a,n,hn,dirs,rfl⟩
  change LocalSpanAt _ (chartValue G b (polynomialOperator (atlas.chart a) n dirs P)) x
  rw [← polynomialOperator_ofFn]
  exact polynomialOperator_localSpan atlas T I (atlas.chart a) P hPI D hP
    (List.ofFn dirs) (by simpa using hn) b x hx

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponReverseJetComparison.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

/-- Local sections of the polynomial operator ideal are locally generated by
the actual normalized analytic jets, preserving the full ideal structure. -/
theorem local_polynomial_jet_ideal_le_differentialIdeal
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    translatedIdeal G 0 (polynomialOperatorIdeal atlas T I) ≤ differentialIdeal A g T I := by
  classical
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  apply Ideal.subset_span
  refine ⟨⟨D,hD⟩,(locallyGenerated_iff_localSpan _ P).mpr ?_⟩
  intro x
  obtain ⟨b,U,hU,hx,hUb,n,f,r,hfr,heq⟩ := hP x
  have hsec (i : Fin n) :
      LocalSpanAt (differentialSections A g T I) (f i).val.value x := by
    obtain ⟨Q,hQ,⟨E,hE⟩,c,hfeq⟩ := (f i).property
    have hc : x ∈ chartDomain G c := by
      simpa only [hfeq,zero_add,Set.mem_setOf_eq] using (hfr i x hx).1
    have hh := polynomialOperatorIdeal_le_localSectionIdeal atlas T I c x hc hQ
    change LocalSpanAt (differentialSections A g T I) (chartValue G c Q) x at hh
    simpa only [hfeq,zero_add] using hh
  have hterms (i : Fin n) :=
    (hsec i).rational_mul (r i) U hU hx (fun y hy => (hfr i y hy).2)
  have hsum := LocalSpanAt.fin_sum
    (fun i y => (r i).value y * (f i).val.value y) x hterms
  refine ⟨b,hUb hx,hsum.congr_on U hU hx ?_⟩
  intro y hy
  exact (heq y hy).symm

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalIdealComparison.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem translatedIdeal_zero_le_retainOnGroup
    (I : Ideal G.CoordinateRing) (hG : G.vanishingIdeal Set.univ ≤ I) :
    translatedIdeal G 0 I ≤ retainOnGroup G I := by
  classical
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  apply (Submodule.mem_iInf _).mpr
  intro x
  obtain ⟨b,U,hU,hx,hUb,n,f,r,hfr,heq⟩ := hP x.point
  have hf (i : Fin n) : ∃ Q ∈ I, ∃ E : G.FactorIndex → ℕ,
      G.ambient.IsHomogeneous Q E ∧ ∃ c : CoordinateChart G,
        (f i).val = ⟨{y | 0 + y ∈ chartDomain G c}, fun y => chartValue G c Q (0 + y)⟩ := by
    obtain ⟨Q,hQI,⟨E,hQE⟩,c,hc⟩ := (f i).property
    exact ⟨Q,hQI,E,hQE,c,hc⟩
  choose Q hQI E hQE c hfeq using hf
  let R : Fin n → RationalCoefficient G := fun i =>
    ⟨(r i).numerator * Q i, (r i).denominator * pivotPolynomial (c i) (E i),
      (r i).degree + E i, (r i).numerator_homogeneous.mul G.ambient (hQE i),
      (r i).denominator_homogeneous.mul G.ambient (pivotPolynomial_homogeneous (c i) (E i))⟩
  have hRden (i : Fin n) (y : G.Point) (hy : y ∈ U) :
      G.ambient.eval (R i).denominator (G.embedding y) ≠ 0 := by
    have hdom : y ∈ chartDomain G (c i) := by
      simpa only [hfeq i, zero_add, Set.mem_setOf_eq] using (hfr i y hy).1
    change G.ambient.eval ((r i).denominator * pivotPolynomial (c i) (E i)) (G.embedding y) ≠ 0
    simp only [MultiProjectiveSpace.eval, map_mul]
    exact mul_ne_zero (hfr i y hy).2 (pivotPolynomial_eval_ne_zero (c i) (E i) y hdom)
  have hRval (i : Fin n) (y : G.Point) :
      (R i).value y = (r i).value y * (f i).val.value y := by
    simp only [hfeq i, zero_add]
    rw [chartValue_eq_div_pivot (c i) (Q i) (E i) (hQE i) y]
    simp only [R, RationalCoefficient.value, MultiProjectiveSpace.eval, map_mul]
    exact (div_mul_div_comm _ _ _ _).symm
  obtain ⟨s,hsI,hs⟩ := exists_rational_sum R I (fun i => I.mul_mem_left _ (hQI i))
  apply local_fraction_identity_mem_retained I hG P D hD x b U hU hx hUb s hsI
  · intro y hy
    exact (hs y (fun i => hRden i y hy)).1
  · intro y hy
    rw [(hs y (fun i => hRden i y hy)).2,heq y hy]
    apply Finset.sum_congr rfl
    intro i _
    exact (hRval i y).symm

/-- Local polynomial-section generation equals primary-component retention,
as actual ideals including nilpotent multiplicities. -/
theorem retainOnGroup_eq_translatedIdeal_zero
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (hG : G.vanishingIdeal Set.univ ≤ I) :
    retainOnGroup G I = translatedIdeal G 0 I :=
  le_antisymm (retainOnGroup_le_translatedIdeal_zero I hI)
    (translatedIdeal_zero_le_retainOnGroup I hG)

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponJetIdealInclusion.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem locallyGeneratedIdeal_le_retention_of_fractions
    (I : Ideal G.CoordinateRing) (hG : G.vanishingIdeal Set.univ ≤ I)
    (S : Set (LocalSection G))
    (hS : ∀ f ∈ S, ∀ x ∈ f.domain,
      ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧
        ∃ r : RationalCoefficient G, r.numerator ∈ I ∧
          ∀ y ∈ U, G.ambient.eval r.denominator (G.embedding y) ≠ 0 ∧ r.value y = f.value y) :
    locallyGeneratedIdeal G S ≤ retainOnGroup G I := by
  classical
  letI : TopologicalSpace G.Point := G.zariskiTopology
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩
  apply (Submodule.mem_iInf _).mpr
  intro x
  obtain ⟨b,U,hU,hx,hUb,n,f,r,hfr,heq⟩ := hP x.point
  have hf (i : Fin n) := hS (f i).val (f i).property x.point (hfr i x.point hx).1
  choose V hVo hxV s hsI hs using hf
  let W := U ∩ ⋂ i, V i
  have hWo : @IsOpen _ G.zariskiTopology W := hU.inter (isOpen_iInter_of_finite hVo)
  have hxW : x.point ∈ W := ⟨hx,Set.mem_iInter.mpr hxV⟩
  have hWV (y : G.Point) (hy : y ∈ W) (i : Fin n) : y ∈ V i := Set.mem_iInter.mp hy.2 i
  let R := fun i => rationalMul (r i) (s i)
  have hRI (i : Fin n) : (R i).numerator ∈ I := I.mul_mem_left _ (hsI i)
  have hRden (i : Fin n) (y : G.Point) (hy : y ∈ W) :
      G.ambient.eval (R i).denominator (G.embedding y) ≠ 0 :=
    rationalMul_denominator_ne_zero _ _ y (hfr i y hy.1).2 (hs i y (hWV y hy i)).1
  have hRval (i : Fin n) (y : G.Point) (hy : y ∈ W) :
      (R i).value y = (r i).value y * (f i).val.value y := by
    rw [rationalMul_value,(hs i y (hWV y hy i)).2]
  obtain ⟨t,htI,ht⟩ := exists_rational_sum R I hRI
  apply local_fraction_identity_mem_retained I hG P D hD x b W hWo hxW
    (fun _ hy => hUb hy.1) t htI
  · intro y hy
    exact (ht y (fun i => hRden i y hy)).1
  · intro y hy
    rw [(ht y (fun i => hRden i y hy)).2,heq y hy.1]
    exact Finset.sum_congr rfl (fun i _ => (hRval i y hy).symm)

variable [CompleteSpace K] {A : AnalyticSubgroup G} {g : G.Point}

theorem differentialIdeal_le_retainedPolynomialOperatorIdeal
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    differentialIdeal A g T I ≤ retainedPolynomialOperatorIdeal atlas T I := by
  apply locallyGeneratedIdeal_le_retention_of_fractions _ le_sup_left
  rintro f ⟨P,hPI,⟨D,hP⟩,b,j,rfl⟩ x hx
  exact normalizedJet_rational_fraction atlas T I P hPI D hP b j x hx

theorem differentialIdeal_le_local_polynomial_jet_ideal
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    differentialIdeal A g T I ≤ translatedIdeal G 0 (polynomialOperatorIdeal atlas T I) := by
  have h := differentialIdeal_le_retainedPolynomialOperatorIdeal atlas T I
  unfold retainedPolynomialOperatorIdeal at h
  rwa [retainOnGroup_eq_translatedIdeal_zero _ (polynomialOperatorIdeal_homogeneous atlas T I)
    le_sup_left] at h

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponJetComparisonCompleted.lean

set_option autoImplicit false
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

theorem differentialIdeal_eq_local_polynomial_jet_ideal
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    differentialIdeal A g T I = translatedIdeal G 0 (polynomialOperatorIdeal atlas T I) :=
  le_antisymm (differentialIdeal_le_local_polynomial_jet_ideal atlas T I)
    (local_polynomial_jet_ideal_le_differentialIdeal atlas T I)

theorem retainedPolynomialOperatorIdeal_eq_differentialIdeal
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    retainedPolynomialOperatorIdeal atlas T I = differentialIdeal A g T I :=
  (retainOnGroup_eq_translatedIdeal_zero _ (polynomialOperatorIdeal_homogeneous atlas T I)
    le_sup_left).trans (differentialIdeal_eq_local_polynomial_jet_ideal atlas T I).symm

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponLocalGenerationReverse.lean

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g g' : G.Point}

/-- An iterated section is locally a regular fraction whose numerator lies in
the genuine outer polynomial operator ideal. The inner numerator belongs to
the whole inner differential ideal by the already proved retention comparison. -/
theorem iterated_section_rational_fraction (atlas : TranslationAtlas A g)
    (atlas' : TranslationAtlas A g') (T T' : ℕ) (I : Ideal G.CoordinateRing)
    (f : LocalSection G) (hf : f ∈ iteratedDifferentialSections A g g' T T' I)
    (x : G.Point) (hx : x ∈ f.domain) :
    ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧
      ∃ s : RationalCoefficient G,
        s.numerator ∈ polynomialOperatorIdeal atlas T (differentialIdeal A g' T' I) ∧
          ∀ y ∈ U, G.ambient.eval s.denominator (G.embedding y) ≠ 0 ∧ s.value y = f.value y := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  obtain ⟨P,hPI,⟨D,hP⟩,b,u,hu,v,hv,rfl⟩ := hf
  let j : JetIndex A.parameterDimension T' := ⟨v.length,hv,v.get⟩
  have hx' : g'+(g+x) ∈ chartDomain G b := by
    simpa only [Set.mem_setOf_eq,add_assoc,add_comm,add_left_comm] using hx
  obtain ⟨V,hV,hxV,r,hrI,hr⟩ := normalizedJet_rational_fraction atlas' T' I P hPI D hP b j (g+x) hx'
  have hrDI : r.numerator ∈ differentialIdeal A g' T' I := by
    rw [← retainedPolynomialOperatorIdeal_eq_differentialIdeal atlas' T' I]
    exact le_retainOnGroup G _ hrI
  obtain ⟨W,hW,hxW,s,hsI,hs⟩ := rational_orbit_jet_fraction atlas T
    (differentialIdeal A g' T' I) r hrDI u hu x (hr (g+x) hxV).1
  refine ⟨W ∩ {y | g+y ∈ V},hW.inter (translation_preimage_isOpen g V hV),
    ⟨hxW,hxV⟩,s,hsI,?_⟩
  intro y hy
  refine ⟨(hs y hy.1).1,?_⟩
  have he := orbitPullback_congr_on A r.value (normalizedJet A g' b P j)
    (g+y) V hV hy.2 (fun q hq => (hr q hq).2)
  have ha : AnalyticAt K (orbitPullback A (normalizedJet A g' b P j) (g+y)) 0 :=
    (rational_orbit_pullback_analytic A (g+y) r (hr (g+y) hy.2).1).congr he
  exact (hs y hy.1).2.trans
    (((mixedDeriv_congr he (u.map (fun i => Pi.single i (1 : K)))).self_of_nhds).trans
      (mixedDeriv_map_eq_iteratedFDeriv
        (fun i : Fin A.parameterDimension => Pi.single i (1 : K)) ha u))

theorem iterated_jet_sections_le_differentialIdeal (atlas : TranslationAtlas A g)
    (atlas' : TranslationAtlas A g') (T T' : ℕ) (I : Ideal G.CoordinateRing) :
    locallyGeneratedIdeal G (iteratedDifferentialSections A g g' T T' I) ≤
      differentialIdeal A g T (differentialIdeal A g' T' I) := by
  rw [← retainedPolynomialOperatorIdeal_eq_differentialIdeal atlas T
    (differentialIdeal A g' T' I)]
  apply locallyGeneratedIdeal_le_retention_of_fractions _ le_sup_left
  exact iterated_section_rational_fraction atlas atlas' T T' I

theorem differentialIdeal_eq_iterated_jet_sections_with_atlases
    (atlas : TranslationAtlas A g) (atlas' : TranslationAtlas A g')
    (T T' : ℕ) (I : Ideal G.CoordinateRing) :
    differentialIdeal A g T (differentialIdeal A g' T' I) =
      locallyGeneratedIdeal G (iteratedDifferentialSections A g g' T T' I) :=
  le_antisymm (differentialIdeal_le_iterated_jet_sections A g g' atlas T T' I)
    (iterated_jet_sections_le_differentialIdeal atlas atlas' T T' I)

end PhilipponMultiplicity.OperatorSupport
end
end


section
-- Implementation: Solutions/PhilipponAnalyticPolynomialSubstitution.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AtlasSupport

/-- Polynomial substitution preserves analyticity of every coefficient. -/
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

/-- A substitution homogeneous block by block has the exact transformed degree,
including when its coefficients belong to a ring of analytic functions. -/
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
-- Implementation: Solutions/PhilipponFiniteBasicCover.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity

/-- A nonvanishing cover by finite-variable polynomials has a finite subcover,
even on an arbitrary subset of affine coordinate tuples. -/
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

/-- Every open cover of an arbitrary multiprojective locus admits a finite
subcover. This supplies the finite family needed for uniform chart degrees. -/
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
-- Implementation: Solutions/PhilipponPolynomialMapCharts.lean

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

/-- Polynomial formulas for one target block, with a homogeneous basic domain.
The entire tuple vanishes off that domain, giving global compatibility. -/
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

theorem PolynomialMapChart.compatible {b : N.FactorIndex}
    (chart : PolynomialMapChart M N e f b) (x : X)
    (j k : Fin (N.ambientDimension b + 1)) :
    M.eval (chart.coordinates j) (e x) * (f x b).rep k =
      M.eval (chart.coordinates k) (e x) * (f x b).rep j := by
  by_cases hx : M.eval chart.cut (e x) = 0
  · rw [chart.zero_off x hx j,chart.zero_off x hx k,zero_mul,zero_mul]
  · obtain ⟨hn,heq⟩ := chart.represents x hx
    exact (projectivization_mk_eq_iff_cross _ _ hn (f x b).rep_nonzero).mp
      (heq.trans (f x b).mk_rep.symm) j k

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

/-- A finite family of globally compatible polynomial formulas covers an
arbitrary regular map into a chosen target projective block. -/
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
-- Implementation: Solutions/PhilipponBoundedAdditionCharts.lean

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

/-- The algebraic addition law has a finite homogeneous polynomial cover with
one positive degree bound depending only on the embedded group. -/
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
-- Implementation: Solutions/PhilipponAdditionSubstitution.lean

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
-- Implementation: Solutions/PhilipponPolynomialChartLifts.lean

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

/-- The chart cross-product identity survives arbitrary genuine homogeneous
lifts of both source and target, including outside the chart domain. -/
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
-- Implementation: Solutions/PhilipponAdditionChartGerms.lean

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
-- Implementation: Solutions/PhilipponBoundedTranslationAtlas.lean

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

/-- A choice of one algebraic addition chart in every factor gives a genuine
polynomial translation chart with analytic coefficients. -/
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

/-- The finite addition-law charts are chosen once for each embedded factor;
their degree bounds are independent of the analytic subgroup and translation. -/
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
-- Implementation: Solutions/PhilipponLocalGenerationCompleted.lean

set_option autoImplicit false
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem differentialIdeal_eq_iterated_jet_sections (A : AnalyticSubgroup G)
    (g g' : G.Point) (T T' : ℕ) (I : Ideal G.CoordinateRing) :
    differentialIdeal A g T (differentialIdeal A g' T' I) =
      locallyGeneratedIdeal G (iteratedDifferentialSections A g g' T T' I) := by
  obtain ⟨c,hc,ha⟩ := AtlasSupport.exists_uniformly_bounded_translation_atlas (K := K)
  obtain ⟨atlas,hatlas⟩ := ha G A g
  obtain ⟨atlas',hatlas'⟩ := ha G A g'
  exact differentialIdeal_eq_iterated_jet_sections_with_atlases atlas atlas' T T' I

end PhilipponMultiplicity.OperatorSupport

end
end


section
-- Implementation: Solutions/PhilipponProposition43Completed.lean
set_option autoImplicit false
open scoped BigOperators Topology
namespace PhilipponMultiplicity

theorem OperatorSupport.proposition_4_3_completed
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g g' : G.Point) (k k' : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I)
    (atlas atlas' : TranslationAtlas A g) :
    (retainedPolynomialOperatorIdeal atlas k I =
      retainedPolynomialOperatorIdeal atlas' k I) ∧
    (∀ other : TranslationAtlas A g', ∀ combined : TranslationAtlas A (g + g'),
      retainedPolynomialOperatorIdeal atlas k
        (retainedPolynomialOperatorIdeal other k' I) =
      retainedPolynomialOperatorIdeal combined (k + k') I) := by
  letI : CompleteSpace K := hK.completeSpace
  constructor
  · exact (OperatorSupport.retainedPolynomialOperatorIdeal_eq_differentialIdeal atlas k I).trans
      (OperatorSupport.retainedPolynomialOperatorIdeal_eq_differentialIdeal atlas' k I).symm
  · intro other combined
    rw [OperatorSupport.retainedPolynomialOperatorIdeal_eq_differentialIdeal other k' I,
      OperatorSupport.retainedPolynomialOperatorIdeal_eq_differentialIdeal atlas k,
      OperatorSupport.differentialIdeal_eq_iterated_jet_sections A g g' k k' I,
      OperatorSupport.iterated_jet_sections_eq_differentialIdeal A g g' k k' I,
      OperatorSupport.retainedPolynomialOperatorIdeal_eq_differentialIdeal combined (k+k') I]


end PhilipponMultiplicity
end


section
-- Implementation: Solutions/PhilipponPrimaryContact.lean
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

/-- Every equation of the ambient group vanishes to all orders along every
analytic orbit; this is proved using the actual projective lifts. -/
theorem groupIdeal_le_jetIdeal (A : AnalyticSubgroup G) (x : G.Point) (T : ℕ) :
    G.vanishingIdeal Set.univ ≤ jetIdeal A x T := by
  intro P hP n hn
  have hz : A.pullback P x =ᶠ[𝓝 0] (fun _ => (0 : K)) := by
    filter_upwards [A.lift_represents x] with z hz
    obtain ⟨hz,hlift⟩ := hz
    exact G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
      (Set.mem_image_of_mem G.embedding (Set.mem_univ _)) _ hlift hP
  rw [(hz.iteratedFDeriv K n).eq_of_nhds]
  simp


end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponSectionFiveContact.lean
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport

variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem differentialIdeal_homogeneous (g : G.Point) (T : ℕ) (I : Ideal G.CoordinateRing) :
    IsMultihomogeneousIdeal G.ambient (differentialIdeal A g T I) := by
  apply homogeneous_span
  exact fun _ h => h.1


end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponSectionFiveDifferentialContainment.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

/-- Pointwise vanishing of a homogeneous ideal gives containment in the
homogeneous vanishing ideal, although arbitrary evaluation kernels need not
be multihomogeneous. -/
theorem homogeneousIdeal_le_group_vanishingIdeal
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (V : Set G.Point) (h : ∀ x ∈ V, ∀ P ∈ I, G.ambient.eval P (G.embedding x) = 0) :
    I ≤ G.vanishingIdeal V := by
  rw [G.ambient.homogeneousIdeal_eq_span I hI]
  apply Ideal.span_le.mpr
  rintro P ⟨hP,D,hD⟩
  apply Ideal.subset_span
  refine ⟨⟨D,hD⟩,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact h x hx P hP


end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponOperatorGenerators.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
open JetSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}

/-- The coefficientwise operator can be evaluated at arbitrary affine coordinates. -/
theorem polynomialOperator_eval_coordinates (chart : TranslationChart A g)
    (P : G.CoordinateRing) (v : G.ambient.Variable → K)
    (n : ℕ) (directions : Fin n → Fin A.parameterDimension) :
    MvPolynomial.eval v (polynomialOperator chart n directions P) =
      iteratedFDeriv K n
        (fun z => MvPolynomial.eval₂ (Pi.evalRingHom (fun _ : A.ParameterSpace => K) z)
          v (substitutedPolynomial chart P)) 0 (fun i => Pi.single (directions i) 1) := by
  classical
  let F := substitutedPolynomial chart P
  have heval : (fun z => MvPolynomial.eval₂
      (Pi.evalRingHom (fun _ : A.ParameterSpace => K) z) v F) =
      fun z => ∑ e ∈ F.support, (∏ i ∈ e.support, v i ^ e i) * F.coeff e z := by
    funext z
    simp only [eval₂_eq, Pi.evalRingHom_apply, mul_comm]
  rw [heval, iteratedFDeriv_fun_sum_apply
    (f := fun e z => (∏ i ∈ e.support, v i ^ e i) * F.coeff e z)
    (fun e _ => (analyticAt_const.mul (substituted_coeff_analytic chart P e)).contDiffAt)]
  simp only [ContinuousMultilinearMap.sum_apply]
  unfold polynomialOperator
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

theorem substituted_eval_analytic (chart : TranslationChart A g) (P : G.CoordinateRing)
    (v : G.ambient.Variable → K) :
    AnalyticAt K (fun z => MvPolynomial.eval₂
      (Pi.evalRingHom (fun _ : A.ParameterSpace => K) z) v
      (substitutedPolynomial chart P)) 0 := by
  classical
  simp only [eval₂_eq, Pi.evalRingHom_apply]
  exact Finset.analyticAt_fun_sum _ fun e _ =>
    (substituted_coeff_analytic chart P e).mul analyticAt_const

theorem polynomialOperator_eval_coordinates_mixed (chart : TranslationChart A g)
    (P : G.CoordinateRing) (v : G.ambient.Variable → K)
    (w : List (Fin A.parameterDimension)) :
    MvPolynomial.eval v (polynomialOperator chart w.length w.get P) =
      mixedDeriv (w.map (fun i => Pi.single i (1 : K)))
        (fun z => MvPolynomial.eval₂ (Pi.evalRingHom (fun _ : A.ParameterSpace => K) z)
          v (substitutedPolynomial chart P)) 0 := by
  rw [mixedDeriv_map_eq_iteratedFDeriv _ (substituted_eval_analytic chart P v),
    polynomialOperator_eval_coordinates]

/-- Polynomial Leibniz rule, before restricting to the group or discarding components. -/
theorem polynomialOperator_mul_list (chart : TranslationChart A g)
    (P Q : G.CoordinateRing) (w : List (Fin A.parameterDimension)) :
    polynomialOperator chart w.length w.get (P*Q) =
      polynomialOperator chart 0 Fin.elim0 P * polynomialOperator chart w.length w.get Q +
      ((properSplits w).map fun p => polynomialOperator chart p.1.length p.1.get P *
        polynomialOperator chart p.2.length p.2.get Q).sum := by
  apply MvPolynomial.funext
  intro v
  simp only [map_add, map_mul, map_list_sum, List.map_map, Function.comp_def]
  simp only [polynomialOperator_eval_coordinates_mixed]
  have hz : MvPolynomial.eval v (polynomialOperator chart 0 Fin.elim0 P) =
      MvPolynomial.eval₂ (Pi.evalRingHom (fun _ : A.ParameterSpace => K) 0) v
        (substitutedPolynomial chart P) := by
    rw [polynomialOperator_eval_coordinates]
    simp
  rw [hz]
  have heq : (fun z => MvPolynomial.eval₂
      (Pi.evalRingHom (fun _ : A.ParameterSpace => K) z) v
        (substitutedPolynomial chart (P*Q))) =
      fun z => MvPolynomial.eval₂ (Pi.evalRingHom (fun _ : A.ParameterSpace => K) z) v
          (substitutedPolynomial chart P) *
        MvPolynomial.eval₂ (Pi.evalRingHom (fun _ : A.ParameterSpace => K) z) v
          (substitutedPolynomial chart Q) := by
    funext z
    simp [substitutedPolynomial]
  rw [heq]
  exact mixedDeriv_map_mul _ (substituted_eval_analytic chart P v)
    (substituted_eval_analytic chart Q v) w

/-- All polynomials whose operators of order at most T lie in a fixed ideal. -/
def operatorPreimageIdeal (chart : TranslationChart A g) (T : ℕ)
    (J : Ideal G.CoordinateRing) : Ideal G.CoordinateRing where
  carrier := {P | ∀ n ≤ T, ∀ directions : Fin n → Fin A.parameterDimension,
    polynomialOperator chart n directions P ∈ J}
  zero_mem' := by
    intro n hn dirs
    have h := polynomialOperator_add chart n dirs (0 : G.CoordinateRing) 0
    simp only [add_zero] at h
    have hz : polynomialOperator chart n dirs 0 = 0 := by
      apply add_left_cancel (a := polynomialOperator chart n dirs 0)
      simpa only [add_zero] using h.symm
    rw [hz]
    exact J.zero_mem
  add_mem' := by
    intro P Q hP hQ n hn dirs
    rw [polynomialOperator_add]
    exact J.add_mem (hP n hn dirs) (hQ n hn dirs)
  smul_mem' := by
    intro P Q hQ n hn dirs
    change polynomialOperator chart n dirs (P*Q) ∈ J
    let w := List.ofFn dirs
    have heq : polynomialOperator chart n dirs (P*Q) =
        polynomialOperator chart w.length w.get (P*Q) := by
      ext e
      simp only [polynomialOperator_coeff]
      apply iteratedFDeriv_apply_congr (List.length_ofFn (f := dirs)).symm
      intro i
      simp [w]
    rw [heq, polynomialOperator_mul_list]
    apply J.add_mem
    · exact J.mul_mem_left _ (hQ w.length (by simpa [w] using hn) w.get)
    · apply J.list_sum_mem
      intro R hR
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hR
      have hl := (properSplits_lengths w p hp).2.2
      apply J.mul_mem_left
      apply hQ
      exact (Nat.le_of_lt hl).trans (by simpa [w] using hn)

/-- One needs to differentiate generators only: ideal coefficients are handled by Leibniz. -/
theorem polynomialOperator_mem_of_span (chart : TranslationChart A g)
    (T : ℕ) (S : Set G.CoordinateRing) (J : Ideal G.CoordinateRing)
    (hS : ∀ P ∈ S, ∀ n ≤ T, ∀ dirs : Fin n → Fin A.parameterDimension,
      polynomialOperator chart n dirs P ∈ J)
    (P : G.CoordinateRing) (hP : P ∈ Ideal.span S)
    (n : ℕ) (hn : n ≤ T) (dirs : Fin n → Fin A.parameterDimension) :
    polynomialOperator chart n dirs P ∈ J := by
  have hle : Ideal.span S ≤ operatorPreimageIdeal chart T J := Ideal.span_le.mpr hS
  exact hle hP n hn dirs

/-- Operators preserve the actual homogeneous defining ideal of the group. -/
theorem groupIdeal_le_operatorPreimageIdeal (chart : TranslationChart A g)
    (T : ℕ) : G.vanishingIdeal Set.univ ≤
      operatorPreimageIdeal chart T (G.vanishingIdeal Set.univ) := by
  apply Ideal.span_le.mpr
  rintro P ⟨⟨D,hD⟩,hP⟩ n hn dirs
  apply Ideal.subset_span
  refine ⟨⟨_,polynomialOperator_homogeneous chart n dirs P D hD⟩,?_⟩
  rintro _ ⟨x,_,rfl⟩
  apply operator_zero_of_contact chart P D hD x T _ n hn dirs
  apply (mem_jetIdeal_iff A (g+x) T P).mp
  exact groupIdeal_le_jetIdeal A (g+x) T (Ideal.subset_span ⟨⟨D,hD⟩,hP⟩)

/-- Polynomial-generator formula underlying the bounded ideal J′ in Section 5. -/
theorem polynomialOperatorIdeal_generated (atlas : TranslationAtlas A g)
    (T : ℕ) (S : Set G.CoordinateRing)
    (hS : ∀ P ∈ S, ∃ D, G.ambient.IsHomogeneous P D) :
    polynomialOperatorIdeal atlas T (G.vanishingIdeal Set.univ ⊔ Ideal.span S) =
      G.vanishingIdeal Set.univ ⊔ Ideal.span
        {Q | ∃ P ∈ S, ∃ a : atlas.Index, ∃ n : ℕ, n ≤ T ∧
          ∃ dirs : Fin n → Fin A.parameterDimension,
            Q = polynomialOperator (atlas.chart a) n dirs P} := by
  let J := G.vanishingIdeal Set.univ ⊔ Ideal.span
        {Q | ∃ P ∈ S, ∃ a : atlas.Index, ∃ n : ℕ, n ≤ T ∧
          ∃ dirs : Fin n → Fin A.parameterDimension,
            Q = polynomialOperator (atlas.chart a) n dirs P}
  change polynomialOperatorIdeal atlas T _ = J
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    rintro Q ⟨P,hP,hD,a,n,hn,dirs,rfl⟩
    have hle : G.vanishingIdeal Set.univ ⊔ Ideal.span S ≤
        operatorPreimageIdeal (atlas.chart a) T J := by
      apply sup_le
      · intro R hR m hm d
        exact Ideal.mem_sup_left (groupIdeal_le_operatorPreimageIdeal (atlas.chart a) T hR m hm d)
      · apply Ideal.span_le.mpr
        intro R hR m hm d
        exact Ideal.mem_sup_right (Ideal.subset_span ⟨R,hR,a,m,hm,d,rfl⟩)
    exact hle hP n hn dirs
  · apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    rintro Q ⟨P,hP,a,n,hn,dirs,rfl⟩
    exact Ideal.mem_sup_right (Ideal.subset_span
      ⟨P,Ideal.mem_sup_right (Ideal.subset_span hP),hS P hP,a,n,hn,dirs,rfl⟩)

/-- Arbitrary sums of homogeneous ideals commute with polynomial operators,
up to the fixed ambient group ideal. -/
theorem polynomialOperatorIdeal_iSup {ι : Type*} (atlas : TranslationAtlas A g)
    (T : ℕ) (I : ι → Ideal G.CoordinateRing)
    (hI : ∀ i, IsMultihomogeneousIdeal G.ambient (I i)) :
    polynomialOperatorIdeal atlas T (⨆ i, I i) =
      G.vanishingIdeal Set.univ ⊔ ⨆ i, polynomialOperatorIdeal atlas T (I i) := by
  let J := G.vanishingIdeal Set.univ ⊔ ⨆ i, polynomialOperatorIdeal atlas T (I i)
  change polynomialOperatorIdeal atlas T _ = J
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    rintro Q ⟨P,hP,hD,a,n,hn,dirs,rfl⟩
    have hle : (⨆ i, I i) ≤ operatorPreimageIdeal (atlas.chart a) T J := by
      apply iSup_le
      intro i
      apply homogeneousIdeal_le_of_homogeneous G.ambient _ _ (hI i)
      intro R hR hRh m hm d
      exact Ideal.mem_sup_right ((le_iSup (fun i => polynomialOperatorIdeal atlas T (I i)) i)
        (Ideal.mem_sup_right (Ideal.subset_span ⟨R,hR,hRh,a,m,hm,d,rfl⟩)))
    exact hle hP n hn dirs
  · apply sup_le le_sup_left
    exact iSup_le (fun i => polynomialOperatorIdeal_mono atlas T (le_iSup I i))

/-- Retention can be performed before or after taking an arbitrary sum. -/
theorem retainOnGroup_iSup {ι : Type*} (I : ι → Ideal G.CoordinateRing) :
    retainOnGroup G (⨆ i, retainOnGroup G (I i)) = retainOnGroup G (⨆ i, I i) := by
  apply le_antisymm
  · apply le_trans (retainOnGroup_mono G (iSup_le (fun i =>
      retainOnGroup_mono G (le_iSup I i))))
    exact (retainOnGroup_idempotent G _).le
  · exact retainOnGroup_mono G (iSup_mono (fun i => le_retainOnGroup G (I i)))

end PhilipponMultiplicity.OperatorSupport

end
end


section
-- Implementation: Solutions/PhilipponSectionFiveTransporter.lean

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem normalizedPullback_zero (g x : G.Point) (b : CoordinateChart G)
    (P : G.CoordinateRing) :
    normalizedPullback A g b P x 0 = chartValue G b P (g+x) := by
  obtain ⟨hz,hrep⟩ := (A.lift_represents (g+x)).self_of_nhds
  unfold normalizedPullback chartValue
  apply congrArg (fun f : G.ambient.Variable → K => MvPolynomial.eval f P)
  funext v
  obtain ⟨hv,he⟩ := hrep v.1
  have he' : Projectivization.mk K (fun j => A.lift (g+x) 0 ⟨v.1,j⟩) hv =
      G.embedding (g+x) v.1 := by simpa only [A.map_zero,add_zero] using he
  exact projective_ratios_eq _ _ hv (G.embedding (g+x) v.1).rep_nonzero
    (he'.trans (G.embedding (g+x) v.1).mk_rep.symm) v.2 (b v.1)

/-- At order zero the intrinsic differential ideal is the actual translated
local ideal, with arbitrary projective representatives normalized away. -/
theorem differentialIdeal_zero_eq_translatedIdeal (g : G.Point)
    (I : Ideal G.CoordinateRing) : differentialIdeal A g 0 I = translatedIdeal G g I := by
  have heq : differentialSections A g 0 I = translationSections G g I := by
    ext f
    constructor
    · rintro ⟨P,hP,hD,b,j,rfl⟩
      rcases j with ⟨k,hk,directions⟩
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      refine ⟨P,hP,hD,b,?_⟩
      congr 1
      funext x
      simp only [normalizedJet,iteratedFDeriv_zero_apply]
      exact normalizedPullback_zero g x b P
    · rintro ⟨P,hP,hD,b,rfl⟩
      refine ⟨P,hP,hD,b,⟨0,le_rfl,Fin.elim0⟩,?_⟩
      congr 1
      funext x
      simp only [normalizedJet,iteratedFDeriv_zero_apply]
      exact (normalizedPullback_zero g x b P).symm
  exact congrArg (locallyGeneratedIdeal G) heq


end PhilipponMultiplicity
end
end


section
-- Implementation: Solutions/PhilipponBoundedOperatorIdeal.lean

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G}

theorem multihomogeneous_iSup {ι : Type*} (I : ι → Ideal G.CoordinateRing)
    (hI : ∀ i, IsMultihomogeneousIdeal G.ambient (I i)) :
    IsMultihomogeneousIdeal G.ambient (⨆ i, I i) := by
  classical
  let w := Hilbert.blockWeight G.ambient.factorCount G.ambient.ambientDimension
  letI := weightedGradedAlgebra K w
  have h (i : ι) : (I i).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : G.CoordinateRing) ∈ I i
    simpa only [GradedRing.proj_apply, MvPolynomial.decompose'_apply] using hI i f hf d
  intro f hf d
  exact weightedHomogeneousComponent_mem_of_mem K w (Ideal.IsHomogeneous.iSup h) hf d

/-- Differential ideals commute with nonempty sums after retention. -/
theorem differentialIdeal_iSup {ι : Type*} [Nonempty ι]
    (g : G.Point) (atlas : TranslationAtlas A g) (T : ℕ)
    (I : ι → Ideal G.CoordinateRing)
    (hI : ∀ i, IsMultihomogeneousIdeal G.ambient (I i)) :
    differentialIdeal A g T (⨆ i, I i) =
      retainOnGroup G (⨆ i, differentialIdeal A g T (I i)) := by
  simp_rw [← retainedPolynomialOperatorIdeal_eq_differentialIdeal atlas]
  unfold retainedPolynomialOperatorIdeal
  rw [polynomialOperatorIdeal_iSup atlas T I hI, retainOnGroup_iSup]
  congr 1
  apply sup_eq_right.mpr
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (le_sup_left : G.vanishingIdeal Set.univ ≤ polynomialOperatorIdeal atlas T (I i)).trans
    (le_iSup (fun i => polynomialOperatorIdeal atlas T (I i)) i)

/-- Differentiation only uses the retained local ideal, including its nilpotents. -/
theorem differentialIdeal_retain (g : G.Point) (T : ℕ)
    (I : Ideal G.CoordinateRing) (hI : IsMultihomogeneousIdeal G.ambient I)
    (hG : G.vanishingIdeal Set.univ ≤ I) :
    differentialIdeal A g T (retainOnGroup G I) = differentialIdeal A g T I := by
  rw [retainOnGroup_eq_translatedIdeal_zero I hI hG,
    ← differentialIdeal_zero_eq_translatedIdeal (A := A),
    differentialIdeal_eq_iterated_jet_sections,iterated_jet_sections_eq_differentialIdeal,
    add_zero,Nat.add_zero]

/-- A nonempty family of operators applied to the single original polynomial. -/
def SectionFiveInput.operatorFamily (C : SectionFiveInput G A)
    {ι : Type*} (centers : ι → G.Point) (T : ℕ) : Ideal G.CoordinateRing :=
  ⨆ i, polynomialOperatorIdeal (C.atlas (centers i)) T (C.idealChain 1)

theorem SectionFiveInput.operatorFamily_generators (C : SectionFiveInput G A)
    {ι : Type*} [Nonempty ι] (centers : ι → G.Point) (T : ℕ) :
    C.operatorFamily centers T = G.vanishingIdeal Set.univ ⊔ Ideal.span
      {Q | ∃ i : ι, ∃ a : (C.atlas (centers i)).Index, ∃ n : ℕ, n ≤ T ∧
        ∃ dirs : Fin n → Fin A.parameterDimension,
          Q = polynomialOperator ((C.atlas (centers i)).chart a) n dirs C.polynomial} := by
  have hp (i : ι) := polynomialOperatorIdeal_generated (C.atlas (centers i)) T
    {C.polynomial} (by rintro P rfl; exact ⟨C.degrees,C.polynomial_homogeneous⟩)
  unfold operatorFamily
  apply le_antisymm
  · apply iSup_le
    intro i
    change polynomialOperatorIdeal (C.atlas (centers i)) T
      (G.vanishingIdeal Set.univ ⊔ Ideal.span {C.polynomial}) ≤ _
    rw [hp i]
    apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    rintro Q ⟨P,rfl,a,n,hn,dirs,rfl⟩
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨i,a,n,hn,dirs,rfl⟩)
  · apply sup_le
    · obtain ⟨i⟩ := ‹Nonempty ι›
      exact (le_sup_left : G.vanishingIdeal Set.univ ≤
        polynomialOperatorIdeal (C.atlas (centers i)) T (C.idealChain 1)).trans
        (le_iSup (fun j => polynomialOperatorIdeal (C.atlas (centers j)) T (C.idealChain 1)) i)
    · apply Ideal.span_le.mpr
      rintro Q ⟨i,a,n,hn,dirs,rfl⟩
      apply (le_iSup (fun j => polynomialOperatorIdeal (C.atlas (centers j)) T (C.idealChain 1)) i)
      exact Ideal.mem_sup_right (Ideal.subset_span
        ⟨C.polynomial,Ideal.mem_sup_right (Ideal.subset_span rfl),
          ⟨C.degrees,C.polynomial_homogeneous⟩,a,n,hn,dirs,rfl⟩)

theorem SectionFiveInput.operatorFamily_groupIdeal_le (C : SectionFiveInput G A)
    {ι : Type*} [Nonempty ι] (centers : ι → G.Point) (T : ℕ) :
    G.vanishingIdeal Set.univ ≤ C.operatorFamily centers T := by
  rw [C.operatorFamily_generators centers T]
  exact le_sup_left

theorem SectionFiveInput.operatorFamily_homogeneous (C : SectionFiveInput G A)
    {ι : Type*} (centers : ι → G.Point) (T : ℕ) :
    IsMultihomogeneousIdeal G.ambient (C.operatorFamily centers T) :=
  multihomogeneous_iSup _ (fun i => polynomialOperatorIdeal_homogeneous _ _ _)

/-- Noetherianity selects finitely many of the actual bounded operators. -/
theorem SectionFiveInput.operatorFamily_bounded (C : SectionFiveInput G A)
    {ι : Type*} [Nonempty ι] (centers : ι → G.Point) (T : ℕ) :
    Hilbert.HasEquationsOfDegreeAtMost K G.factorCount G.ambient.ambientDimension
      (G.vanishingIdeal Set.univ) (C.operatorFamily centers T) C.scaledDegrees := by
  classical
  let S := {Q | ∃ i : ι, ∃ a : (C.atlas (centers i)).Index, ∃ n : ℕ, n ≤ T ∧
        ∃ dirs : Fin n → Fin A.parameterDimension,
          Q = polynomialOperator ((C.atlas (centers i)).chart a) n dirs C.polynomial}
  obtain ⟨s,hs,heq⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp
    (IsNoetherian.noetherian (Ideal.span S))
  refine ⟨s,?_,?_⟩
  · intro Q hQ
    obtain ⟨i,a,n,hn,dirs,rfl⟩ := hs hQ
    refine ⟨(fun j => ((C.atlas (centers i)).chart a).degree j * C.degrees j),?_,?_⟩
    · intro j
      exact Nat.mul_le_mul_right (C.degrees j) (C.atlas_bound (centers i) a j)
    · exact (G.ambient.degreePiece_iff _ _).mpr
        (polynomialOperator_homogeneous _ _ _ _ C.degrees C.polynomial_homogeneous)
  · rw [C.operatorFamily_generators centers T, ← sup_assoc, sup_idem]
    exact congrArg (fun J => G.vanishingIdeal Set.univ ⊔ J) heq

/-- Composition keeps the single factor c in the equation-degree bound. -/
theorem SectionFiveInput.translate_operatorFamily (C : SectionFiveInput G A)
    {ι : Type*} [Nonempty ι] (centers : ι → G.Point) (T : ℕ) (v : G.Point) :
    translatedIdeal G v (C.operatorFamily centers T) =
      retainOnGroup G (C.operatorFamily (fun i => v + centers i) T) := by
  rw [← differentialIdeal_zero_eq_translatedIdeal (A := A),
    ← differentialIdeal_retain v 0 _ (C.operatorFamily_homogeneous centers T)
      (C.operatorFamily_groupIdeal_le centers T)]
  have hret (centers : ι → G.Point) :
      retainOnGroup G (C.operatorFamily centers T) =
        retainOnGroup G (⨆ i, differentialIdeal A (centers i) T (C.idealChain 1)) := by
    simp_rw [← retainedPolynomialOperatorIdeal_eq_differentialIdeal (C.atlas _)]
    exact (retainOnGroup_iSup _).symm
  rw [hret, differentialIdeal_retain v 0 _
    (multihomogeneous_iSup _ (fun i => differentialIdeal_homogeneous _ _ _))]
  · rw [differentialIdeal_iSup v (C.atlas v) 0 _
      (fun i => differentialIdeal_homogeneous _ _ _)]
    simp_rw [differentialIdeal_eq_iterated_jet_sections,
      iterated_jet_sections_eq_differentialIdeal,Nat.zero_add]
    exact (hret (fun i => v + centers i)).symm
  · obtain ⟨i⟩ := ‹Nonempty ι›
    apply le_trans ?_ (le_iSup (fun j => differentialIdeal A (centers j) T (C.idealChain 1)) i)
    rw [← retainedPolynomialOperatorIdeal_eq_differentialIdeal (C.atlas (centers i)) T]
    exact le_sup_left.trans (le_retainOnGroup G _)

/-- Retention cannot enlarge the reduced defining ideal of the group. -/
theorem retainOnGroup_groupIdeal :
    retainOnGroup G (G.vanishingIdeal Set.univ) = G.vanishingIdeal Set.univ := by
  apply le_antisymm
  · apply homogeneousIdeal_le_group_vanishingIdeal _
      (retainOnGroup_homogeneous G _ (vanishingIdeal_multihomogeneous K G.ambient _))
    intro x hx
    exact (retainOnGroup_zero_iff G _ x).mpr
      (fun P hP => G.ambient.eval_eq_zero_of_mem_vanishingIdeal hP ⟨x,Set.mem_univ x,rfl⟩)
  · exact le_retainOnGroup G _

theorem translatedIdeal_groupIdeal (g : G.Point) (atlas : TranslationAtlas A g) :
    translatedIdeal G g (G.vanishingIdeal Set.univ) = G.vanishingIdeal Set.univ := by
  rw [← differentialIdeal_zero_eq_translatedIdeal (A := A),
    ← retainedPolynomialOperatorIdeal_eq_differentialIdeal atlas]
  have heq : polynomialOperatorIdeal atlas 0 (G.vanishingIdeal Set.univ) =
      G.vanishingIdeal Set.univ := by
    apply le_antisymm
    · apply sup_le le_rfl
      apply Ideal.span_le.mpr
      rintro Q ⟨P,hP,hD,a,n,hn,dirs,rfl⟩
      exact groupIdeal_le_operatorPreimageIdeal (atlas.chart a) 0 hP n hn dirs
    · exact le_sup_left
  rw [retainedPolynomialOperatorIdeal,heq,retainOnGroup_groupIdeal]

/-- The bounded replacement ideal used on pp. 381--382. This statement applies
to every chain stage and every nonempty translating set, not only the selected
component. It preserves actual local ideals rather than only zero sets. -/
theorem SectionFiveInput.exists_bounded_translated_chain (C : SectionFiveInput G A)
    (n : ℕ) (V : Set G.Point) (hV : V.Nonempty) :
    ∃ J' : Ideal G.CoordinateRing,
      G.vanishingIdeal Set.univ ≤ J' ∧ IsMultihomogeneousIdeal G.ambient J' ∧
      Hilbert.HasEquationsOfDegreeAtMost K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) J' C.scaledDegrees ∧
      retainOnGroup G J' = retainOnGroup G (⨆ v : V, translatedIdeal G v.val (C.idealChain n)) := by
  classical
  letI : Nonempty V := hV.to_subtype
  cases n with
  | zero =>
    refine ⟨G.vanishingIdeal Set.univ,le_rfl,vanishingIdeal_multihomogeneous K G.ambient _,?_,?_⟩
    · refine ⟨∅,by simp,?_⟩
      simp
    · simp only [SectionFiveInput.idealChain]
      simp_rw [translatedIdeal_groupIdeal _ (C.atlas _)]
      simp
  | succ n =>
    cases n with
    | zero =>
      refine ⟨C.operatorFamily (fun v : V => v.val) 0,
        C.operatorFamily_groupIdeal_le _ _,C.operatorFamily_homogeneous _ _,
        C.operatorFamily_bounded _ _,?_⟩
      simp_rw [← differentialIdeal_zero_eq_translatedIdeal (A := A),
        ← retainedPolynomialOperatorIdeal_eq_differentialIdeal (C.atlas _)]
      exact (retainOnGroup_iSup _).symm
    | succ n =>
      let S := sumset C.samplingSet (n+1)
      letI : Nonempty S := ⟨⟨0,zero_mem_sumset C.samplingSet C.zero_mem (n+1)⟩⟩
      let centers : S → G.Point := fun g => g.val
      have hchain : C.idealChain (n+2) = C.operatorFamily centers ((n+1)*C.contactParameter) := by
        rw [C.operatorFamily_generators centers]
        simp only [SectionFiveInput.idealChain]
        congr 2
        ext Q
        simp only [Set.mem_setOf_eq,Subtype.exists]
        simp only [S,centers]
        constructor <;> rintro ⟨g,hg,a,m,hm,dirs,hQ⟩ <;> exact ⟨g,hg,a,m,hm,dirs,hQ⟩
      let combined : V × S → G.Point := fun p => p.1.val + p.2.val
      refine ⟨C.operatorFamily combined ((n+1)*C.contactParameter),
        C.operatorFamily_groupIdeal_le _ _,C.operatorFamily_homogeneous _ _,
        C.operatorFamily_bounded _ _,?_⟩
      change _ = retainOnGroup G (⨆ v : V, translatedIdeal G v.val (C.idealChain (n+2)))
      rw [hchain]
      simp_rw [C.translate_operatorFamily centers]
      rw [retainOnGroup_iSup]
      unfold operatorFamily
      congr 1
      simp only [iSup_prod,combined,centers]

/-- Equality of retained ideals gives equality of the localized ideals at every
actual homogeneous representative. In particular, nilpotent multiplicities are
not lost by the bounded replacement. -/
theorem SectionFiveInput.exists_bounded_translated_chain_local (C : SectionFiveInput G A)
    (n : ℕ) (V : Set G.Point) (hV : V.Nonempty) :
    ∃ J' : Ideal G.CoordinateRing,
      G.vanishingIdeal Set.univ ≤ J' ∧ IsMultihomogeneousIdeal G.ambient J' ∧
      Hilbert.HasEquationsOfDegreeAtMost K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) J' C.scaledDegrees ∧
      retainOnGroup G J' = retainOnGroup G (⨆ v : V, translatedIdeal G v.val (C.idealChain n)) ∧
      ∀ x : GroupHomogeneousRepresentative G,
        J'.map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal)) =
        (⨆ v : V, translatedIdeal G v.val (C.idealChain n)).map
          (algebraMap G.CoordinateRing
            (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal)) := by
  obtain ⟨J',hG,hhom,hbounded,heq⟩ := C.exists_bounded_translated_chain n V hV
  refine ⟨J',hG,hhom,hbounded,heq,?_⟩
  intro x
  rw [← retainOnGroup_localization G J' x,heq,retainOnGroup_localization]

end PhilipponMultiplicity

end
end


section
-- Implementation: Solutions/PhilipponRetentionMultiplicity.lean

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

/-- Retention preserves containment in every prime meeting the group. -/
theorem retainOnGroup_le_prime_iff (I q : Ideal G.CoordinateRing)
    (hq : q.IsPrime) (hx : ComponentMeetsGroup G q) :
    retainOnGroup G I ≤ q ↔ I ≤ q := by
  classical
  constructor
  · exact fun h => (le_retainOnGroup G I).trans h
  · intro hI
    obtain ⟨x,hx⟩ := hx
    let r := representativeOfPoint G x
    have hqr : q ≤ (representativeMaximalIdeal G r).asIdeal := hx
    apply (retainOnGroup_mono G hI).trans
    apply (iInf_le (fun y => retainAtRepresentative G q y) r).trans
    rw [retainAtRepresentative_primary G q hq.isPrimary r, if_pos hqr]

/-- Isolated prime components meeting the group are unchanged by retention. -/
theorem minimalPrime_retainOnGroup_iff (I q : Ideal G.CoordinateRing)
    (hx : ComponentMeetsGroup G q) :
    q ∈ (retainOnGroup G I).minimalPrimes ↔ q ∈ I.minimalPrimes := by
  constructor
  · intro h
    refine ⟨⟨h.isPrime,(le_retainOnGroup G I).trans h.le⟩,?_⟩
    intro p hp hpq
    have hpx : ComponentMeetsGroup G p := by
      obtain ⟨x,hx⟩ := hx
      exact ⟨x,fun P hP => hx P (hpq hP)⟩
    exact h.2 ⟨hp.1,(retainOnGroup_le_prime_iff I p hp.1 hpx).mpr hp.2⟩ hpq
  · intro h
    refine ⟨⟨h.isPrime,(retainOnGroup_le_prime_iff I q h.isPrime hx).mpr h.le⟩,?_⟩
    intro p hp hpq
    exact h.2 ⟨hp.1,(le_retainOnGroup G I).trans hp.2⟩ hpq

/-- Retention preserves the ideal in the local ring at every prime meeting G. -/
theorem retainOnGroup_prime_localization (I : Ideal G.CoordinateRing)
    (q : PrimeSpectrum G.CoordinateRing) (hx : ComponentMeetsGroup G q.asIdeal) :
    (retainOnGroup G I).map (algebraMap G.CoordinateRing (Localization.AtPrime q.asIdeal)) =
      I.map (algebraMap G.CoordinateRing (Localization.AtPrime q.asIdeal)) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    obtain ⟨x,hx⟩ := hx
    let r := representativeOfPoint G x
    have hr : P ∈ retainAtRepresentative G I r :=
      (iInf_le (fun y => retainAtRepresentative G I y) r) hP
    obtain ⟨s,hs,hsP⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (representativeMaximalIdeal G r).asIdeal.primeCompl
      (Localization.AtPrime (representativeMaximalIdeal G r).asIdeal) I P).mp hr
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
      q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) I P).mpr
    exact ⟨s,fun hsq => hs (hx s hsq),hsP⟩
  · exact Ideal.map_mono (le_retainOnGroup G I)

theorem localLength_retainOnGroup (I : Ideal G.CoordinateRing)
    (q : PrimeSpectrum G.CoordinateRing) (hx : ComponentMeetsGroup G q.asIdeal) :
    Hilbert.localLength K G.factorCount G.ambient.ambientDimension (retainOnGroup G I) q =
      Hilbert.localLength K G.factorCount G.ambient.ambientDimension I q := by
  exact congrArg (fun J : Ideal (Localization.AtPrime q.asIdeal) =>
    Module.length (Localization.AtPrime q.asIdeal) ((Localization.AtPrime q.asIdeal) ⧸ J))
    (retainOnGroup_prime_localization I q hx)

/-- Equal retained local data preserve the complete component and multiplicity
conditions of Definition 3.5; no radical or reduced replacement is used. -/
theorem incompleteMultiplicity_iff_of_retain_eq (I J : Ideal G.CoordinateRing)
    (heq : retainOnGroup G I = retainOnGroup G J) (V : Set G.Point) (ell : ℕ) :
    IncompletelyDefinesWithMultiplicityAtLeast G I V ell ↔
      IncompletelyDefinesWithMultiplicityAtLeast G J V ell := by
  have hsup : retainOnGroup G (G.vanishingIdeal Set.univ ⊔ I) =
      retainOnGroup G (G.vanishingIdeal Set.univ ⊔ J) := by
    rw [← retainOnGroup_sup,heq,retainOnGroup_sup]
  have hprime (q : Ideal G.CoordinateRing) (hx : ComponentMeetsGroup G q) :
      q ∈ (G.vanishingIdeal Set.univ ⊔ I).minimalPrimes ↔
        q ∈ (G.vanishingIdeal Set.univ ⊔ J).minimalPrimes := by
    rw [← minimalPrime_retainOnGroup_iff _ _ hx,hsup,minimalPrime_retainOnGroup_iff _ _ hx]
  have hlen (q : PrimeSpectrum G.CoordinateRing) (hx : ComponentMeetsGroup G q.asIdeal) :
      Hilbert.localLength K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ ⊔ I) q =
      Hilbert.localLength K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ ⊔ J) q := by
    rw [← localLength_retainOnGroup _ q hx,hsup,localLength_retainOnGroup _ q hx]
  constructor
  · rintro ⟨⟨hV,hcomp⟩,hm⟩
    exact ⟨⟨hV,fun q hq hx => (hprime q hx).mp (hcomp q hq hx)⟩,
      fun q hq hx => (hlen q hx) ▸ hm q hq hx⟩
  · rintro ⟨⟨hV,hcomp⟩,hm⟩
    exact ⟨⟨hV,fun q hq hx => (hprime q hx).mpr (hcomp q hq hx)⟩,
      fun q hq hx => (hlen q hx).symm ▸ hm q hq hx⟩

end PhilipponMultiplicity.OperatorSupport

end
end


section
-- Implementation: Solutions/PhilipponSectionFiveBoundedReplacement.lean

set_option autoImplicit false
noncomputable section
namespace PhilipponMultiplicity

theorem section_five_bounded_replacement_established
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveInput G A) (n : ℕ) (V : Set G.Point) (hV : V.Nonempty) :
    ∃ J' : Ideal G.CoordinateRing,
      G.vanishingIdeal Set.univ ≤ J' ∧ IsMultihomogeneousIdeal G.ambient J' ∧
      Hilbert.HasEquationsOfDegreeAtMost K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) J' C.scaledDegrees ∧
      retainOnGroup G J' = retainOnGroup G (⨆ v : V, translatedIdeal G v.val (C.idealChain n)) ∧
      (∀ x : GroupHomogeneousRepresentative G,
        J'.map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal)) =
        (⨆ v : V, translatedIdeal G v.val (C.idealChain n)).map
          (algebraMap G.CoordinateRing
            (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal))) ∧
      (∀ W : Set G.Point, ∀ ell : ℕ,
        IncompletelyDefinesWithMultiplicityAtLeast G J' W ell ↔
        IncompletelyDefinesWithMultiplicityAtLeast G
          (⨆ v : V, translatedIdeal G v.val (C.idealChain n)) W ell) := by
  obtain ⟨J',hG,hhom,hbounded,heq,hloc⟩ := C.exists_bounded_translated_chain_local n V hV
  exact ⟨J',hG,hhom,hbounded,heq,hloc,
    fun W ell => OperatorSupport.incompleteMultiplicity_iff_of_retain_eq _ _ heq W ell⟩

end PhilipponMultiplicity

end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveInput G A) (n : ℕ) (V : Set G.Point) (hV : V.Nonempty) :
    ∃ J' : Ideal G.CoordinateRing,
      G.vanishingIdeal Set.univ ≤ J' ∧ IsMultihomogeneousIdeal G.ambient J' ∧
      Hilbert.HasEquationsOfDegreeAtMost K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) J' C.scaledDegrees ∧
      retainOnGroup G J' = retainOnGroup G (⨆ v : V, translatedIdeal G v.val (C.idealChain n)) ∧
      (∀ x : GroupHomogeneousRepresentative G,
        J'.map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal)) =
        (⨆ v : V, translatedIdeal G v.val (C.idealChain n)).map
          (algebraMap G.CoordinateRing
            (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal))) ∧
      (∀ W : Set G.Point, ∀ ell : ℕ,
        IncompletelyDefinesWithMultiplicityAtLeast G J' W ell ↔
        IncompletelyDefinesWithMultiplicityAtLeast G
          (⨆ v : V, translatedIdeal G v.val (C.idealChain n)) W ell) := by
  exact section_five_bounded_replacement_established K G A C n V hV
