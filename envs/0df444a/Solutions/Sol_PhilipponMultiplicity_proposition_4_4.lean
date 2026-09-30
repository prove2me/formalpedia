-- Prove2me | solution 1 for PhilipponMultiplicity.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T16:39:36.195673+00:00
-- url     : https://prove2.me/submissions/377009cb-6d61-4834-afb9-f7edfd60b9cd

import Definitions.Def_PhilipponMultiplicity_SectionFour
import Theorems.Thm_PhilipponMultiplicity_projective_lift_contact_invariance
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology ContDiff
open Filter MvPolynomial PhilipponMultiplicity
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


end PhilipponMultiplicity

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

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g h : G.Point) (k : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (atlas : TranslationAtlas A g) :
    (∀ Q ∈ retainedPolynomialOperatorIdeal atlas k I,
      G.ambient.eval Q (G.embedding h) = 0) ↔
    (∀ Q ∈ I, (k : WithTop ℕ) < vanishingOrder A Q (g + h)) := by
  exact PhilipponMultiplicity.proposition_4_4 K hK G A g h k I hI atlas
