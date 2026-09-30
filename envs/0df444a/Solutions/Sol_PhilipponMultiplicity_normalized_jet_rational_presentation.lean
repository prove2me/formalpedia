-- Prove2me | solution 1 for PhilipponMultiplicity.normalized_jet_rational_presentation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-28T06:40:31.941596+00:00
-- url     : https://prove2.me/submissions/f48143c4-5a86-4293-a3f5-a1fd11231ee6

import Theorems.Thm_PhilipponMultiplicity_translation_operator_algebra
import Definitions.Def_PhilipponMultiplicity_SectionFour
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Analytic.Polynomial
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff
open Filter MvPolynomial
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

theorem solution
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing)
    (P : G.CoordinateRing) (hPI : P ∈ I) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (b : CoordinateChart G)
    (j : JetIndex A.parameterDimension T) (x : G.Point)
    (hx : g+x ∈ chartDomain G b) :
    ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧
      ∃ r : RationalCoefficient G, r.numerator ∈ polynomialOperatorIdeal atlas T I ∧
        ∀ y ∈ U, G.ambient.eval r.denominator (G.embedding y) ≠ 0 ∧
          r.value y = normalizedJet A g b P j y := by
  exact OperatorSupport.normalizedJet_rational_fraction atlas T I P hPI D hP b j x hx
