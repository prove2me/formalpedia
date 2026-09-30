-- Prove2me | solution 1 for PhilipponMultiplicity.differentialIdeal_eq_iterated_jet_sections
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-28T12:28:20.46035+00:00
-- url     : https://prove2.me/submissions/fd33de84-43e6-410f-835b-748fbf4d0fb4

import Definitions.Def_PhilipponMultiplicity_IteratedJets
import Theorems.Thm_PhilipponMultiplicity_retained_ideal_eq_locally_generated_sections
import Theorems.Thm_PhilipponMultiplicity_normalized_jet_rational_presentation
import Theorems.Thm_PhilipponMultiplicity_differentialIdeal_le_local_polynomial_jet_ideal
import Theorems.Thm_PhilipponMultiplicity_exists_uniformly_bounded_translation_atlas
import Theorems.Thm_PhilipponMultiplicity_translation_operator_algebra
import Definitions.Def_PhilipponMultiplicity_SectionFour
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Analytic.Polynomial
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology ContDiff
open Filter MvPolynomial PhilipponMultiplicity
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace

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


end PhilipponMultiplicity.MultiProjectiveSpace

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

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

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


end PhilipponMultiplicity.Hilbert

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


end PhilipponMultiplicity.OperatorSupport

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


end PhilipponMultiplicity.OperatorSupport

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}
theorem polynomialOperator_homogeneous (chart : TranslationChart A g) (n : ℕ)
    (directions : Fin n → Fin A.parameterDimension) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    G.ambient.IsHomogeneous (polynomialOperator chart n directions P)
      (fun i => chart.degree i * D i) :=
  ((translation_operator_algebra K).1 G A g chart n directions).2 P D hP

end PhilipponMultiplicity.OperatorSupport

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

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

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


end PhilipponMultiplicity.OperatorSupport

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


end PhilipponMultiplicity.OperatorSupport

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

namespace PhilipponMultiplicity
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

attribute [local instance] Classical.propDecidable
open Set

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


end PhilipponMultiplicity

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

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K} {A : AnalyticSubgroup G} {g : G.Point}
theorem normalizedJet_rational_fraction (atlas : TranslationAtlas A g)
    (T : ℕ) (I : Ideal G.CoordinateRing) (P : G.CoordinateRing) (hPI : P ∈ I)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (b : CoordinateChart G) (j : JetIndex A.parameterDimension T)
    (x : G.Point) (hx : g+x ∈ chartDomain G b) :
    ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧
      ∃ r : RationalCoefficient G, r.numerator ∈ polynomialOperatorIdeal atlas T I ∧
        ∀ y ∈ U, G.ambient.eval r.denominator (G.embedding y) ≠ 0 ∧
          r.value y = normalizedJet A g b P j y := by
  exact PhilipponMultiplicity.normalized_jet_rational_presentation K G A g atlas T I P hPI D hP b j x hx

theorem differentialIdeal_le_local_polynomial_jet_ideal
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing) :
    differentialIdeal A g T I ≤ translatedIdeal G 0 (polynomialOperatorIdeal atlas T I) :=
  PhilipponMultiplicity.differentialIdeal_le_local_polynomial_jet_ideal K G A g atlas T I

theorem retainOnGroup_eq_translatedIdeal_zero (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (hG : G.vanishingIdeal Set.univ ≤ I) :
    retainOnGroup G I = translatedIdeal G 0 I :=
  PhilipponMultiplicity.retained_ideal_eq_locally_generated_sections K G I hI hG

end PhilipponMultiplicity.OperatorSupport

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


end PhilipponMultiplicity.OperatorSupport

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

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g g' : G.Point) (T T' : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) :
    differentialIdeal A g T (differentialIdeal A g' T' I) =
      locallyGeneratedIdeal G (iteratedDifferentialSections A g g' T T' I) := by
  letI : CompleteSpace K := hK.completeSpace
  obtain ⟨c,hc,ha⟩ := PhilipponMultiplicity.exists_uniformly_bounded_translation_atlas K hK
  obtain ⟨atlas,hatlas⟩ := ha G A g
  obtain ⟨atlas',hatlas'⟩ := ha G A g'
  exact OperatorSupport.differentialIdeal_eq_iterated_jet_sections_with_atlases atlas atlas' T T' I
