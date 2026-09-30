-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_jet_section_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-21T07:18:50.752185+00:00
-- url     : https://prove2.me/submissions/01f7a305-cc42-4701-a1f3-bede8fe773dc

import Definitions.Def_WeierstrassEllipticZeta_SectionJetEvaluation
import Theorems.Thm_TranscendenceTheory_finite_quotient_degree_stabilization
import Theorems.Thm_TranscendenceTheory_bihomogeneous_lift_four_variables
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_first_chart_section_dimension
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

noncomputable section
namespace WeierstrassEllipticZeta
open MvPolynomial TranscendenceTheory

private lemma finite_chart_quotient {L : PeriodPair} {ι : Type}
    (J : FiniteJetChartIdealData L ι) (i : ι) :
    Module.Finite ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal i) := by
  apply Module.finite_of_finrank_pos
  by_contra h
  have he := Nat.eq_zero_of_not_pos h
  have hpow := J.power_le i
  rw [he, pow_zero, Ideal.one_eq_top] at hpow
  exact (inferInstance : (vanishingIdeal ℂ {J.point i}).IsMaximal).ne_top
    (top_le_iff.mp (hpow.trans (J.le_point i)))

private lemma point_ideals_ne {ι : Type} (x : ι → Fin 4 → ℂ)
    (hx : Function.Injective x) {i j : ι} (hij : i ≠ j) :
    vanishingIdeal ℂ {x i} ≠ vanishingIdeal ℂ {x j} := by
  intro h
  apply hij
  apply hx
  funext k
  have hp : X k - C (x i k) ∈ vanishingIdeal ℂ {x i} := by
    rw [mem_vanishingIdeal_singleton_iff]
    simp
  rw [h, mem_vanishingIdeal_singleton_iff] at hp
  simpa using (sub_eq_zero.mp (by simpa using hp : x j k - x i k = 0)).symm

private lemma finite_chart_coprime {L : PeriodPair} {ι : Type}
    (J : FiniteJetChartIdealData L ι) : Pairwise (Function.onFun IsCoprime J.ideal) := by
  intro i j hij
  have hm : IsCoprime (vanishingIdeal ℂ {J.point i}) (vanishingIdeal ℂ {J.point j}) :=
    Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne
      (inferInstance : (vanishingIdeal ℂ {J.point i}).IsMaximal)
      (inferInstance : (vanishingIdeal ℂ {J.point j}).IsMaximal)
      (point_ideals_ne J.point J.point_injective hij))
  have hp := hm.pow
    (m := Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal i))
    (n := Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal j))
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_unique
  rw [← hp.sup_eq]
  exact sup_le_sup (J.power_le i) (J.power_le j)

private lemma low_degree_section (L : PeriodPair) (p : MvPolynomial (Fin 4) ℂ)
    (m n : ℕ) (hm : p.totalDegree ≤ m) (hn : p.totalDegree ≤ n) :
    firstCubicQuotient L p ∈ firstChartSectionSpace L m n := by
  have hdeg : ∀ d ∈ p.support, d 0 ≤ m ∧ d 1 + d 2 + d 3 ≤ n := by
    intro d hd
    have hs : d 0 + d 1 + d 2 + d 3 ≤ p.totalDegree := by
      simpa only [Finsupp.sum_fintype d (fun (_ : Fin 4) (e : ℕ) => e) (fun _ => rfl), Fin.sum_univ_four] using
        (le_totalDegree hd)
    constructor <;> omega
  obtain ⟨Q, hQ, heval⟩ := bihomogeneous_lift_four_variables ℂ p m n hdeg
  have hnormalize : extensionChartNormalize 0 Q = p := by
    apply MvPolynomial.funext
    intro x
    have hx := heval x 1 1 (x 2 * x 3 + 2 * x 1 ^ 2)
    change (aeval x) ((aeval (extensionChartSubstitution 0)) Q) = _
    rw [comp_aeval_apply]
    have hv : (fun i => aeval x (extensionChartSubstitution 0 i)) =
        ![1, x 0, 1, x 1, x 2, x 3, x 2 * x 3 + 2 * x 1 ^ 2] := by
      funext i
      fin_cases i <;> simp [extensionChartSubstitution]
    rw [hv]
    simpa only [one_mul, one_pow, mul_one, aeval_eq_eval] using hx
  apply Submodule.subset_span
  exact ⟨Q, fun d hd => ⟨(hQ d hd).1, (hQ d hd).2.1⟩, congrArg (firstCubicQuotient L) hnormalize⟩


end WeierstrassEllipticZeta

open WeierstrassEllipticZeta MvPolynomial TranscendenceTheory

theorem solution
    (L : PeriodPair) (ι : Type) [Fintype ι] (J : FiniteJetChartIdealData L ι)
    (m n : ℕ) (hm : J.totalDimension - 1 ≤ m) (hn : J.totalDimension - 1 ≤ n) :
    Function.Surjective (J.sectionEvaluation m n) ∧
    Module.finrank ℂ (LinearMap.range (J.sectionEvaluation m n)) = J.totalDimension ∧
    J.totalDimension ≤ Module.finrank ℂ (firstChartSectionSpace L m n) := by
  classical
  let : ∀ i, Module.Finite ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal i) :=
    finite_chart_quotient J
  have hcop := finite_chart_coprime J
  let e := Ideal.quotientInfRingEquivPiQuotient J.ideal hcop
  let a : (MvPolynomial (Fin 4) ℂ ⧸ ⨅ i, J.ideal i) ≃ₐ[ℂ]
      (∀ i, MvPolynomial (Fin 4) ℂ ⧸ J.ideal i) :=
    { e with commutes' := by intro r; ext i; rfl }
  let hfinite : Module.Finite ℂ (MvPolynomial (Fin 4) ℂ ⧸ ⨅ i, J.ideal i) :=
    Module.Finite.of_injective a.toLinearMap a.injective
  have hdimension : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ ⨅ i, J.ideal i) =
      J.totalDimension :=
    a.toLinearEquiv.finrank_eq.trans (Module.finrank_pi_fintype ℂ)
  have hsurj : Function.Surjective (J.sectionEvaluation m n) := by
    intro b
    obtain ⟨p, hp⟩ := Ideal.pi_quotient_surjective hcop b
    obtain ⟨q, hq, hqp⟩ :=
      ((finite_quotient_degree_stabilization ℂ (Fin 4) (⨅ i, J.ideal i)).2 hfinite).2 p
    rw [hdimension] at hq
    refine ⟨⟨firstCubicQuotient L q, low_degree_section L q m n (hq.trans hm) (hq.trans hn)⟩, ?_⟩
    funext i
    change Ideal.Quotient.mk (J.ideal i) q = b i
    have heq : Ideal.Quotient.mk (J.ideal i) q = Ideal.Quotient.mk (J.ideal i) p :=
      (Ideal.Quotient.eq (I := J.ideal i)).mpr (Ideal.mem_iInf.mp hqp i)
    exact heq.trans (hp i)
  refine ⟨hsurj, ?_, ?_⟩
  · rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi_fintype]
    rfl
  · let : Module.Finite ℂ (firstChartSectionSpace L m n) :=
      (elliptic_first_chart_section_dimension L m n).1
    change (∑ i, Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J.ideal i)) ≤ _
    rw [← Module.finrank_pi_fintype]
    exact LinearMap.finrank_le_finrank_of_surjective hsurj
