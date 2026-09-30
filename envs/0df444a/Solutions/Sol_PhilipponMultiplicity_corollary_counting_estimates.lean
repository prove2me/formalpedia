-- Prove2me | solution 1 for PhilipponMultiplicity.corollary_counting_estimates
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T07:51:28.364925+00:00
-- url     : https://prove2.me/submissions/91f1066b-b66d-47ac-a555-7378a42db5c5

import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Theorems.Thm_PhilipponMultiplicity_lemma_3_4
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_exists
import Theorems.Thm_PhilipponMultiplicity_idealMixedDegree_integral
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.Submodule


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity
noncomputable section
namespace PhilipponMultiplicity.CountingProof

-- Reuse the homogeneous-span argument from PhilipponProjectiveHilbertExistence.
theorem block_weight_apply {K : Type*} [Field K]
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

theorem vanishing_homogeneous {K : Type*} [Field K]
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

theorem eval_nonneg {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℚ) (hF : ∀ b, 0 ≤ coeff b F) (D : ι → ℕ) :
    0 ≤ eval (fun i => (D i : ℚ)) F := by
  classical
  rw [eval_eq']
  exact Finset.sum_nonneg fun b _ => mul_nonneg (hF b)
    (Finset.prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) _)

theorem term_le_eval {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℚ) (hF : ∀ b, 0 ≤ coeff b F)
    (D : ι → ℕ) (b : ι →₀ ℕ) :
    coeff b F * (∏ i, (D i : ℚ) ^ b i) ≤ eval (fun i => (D i : ℚ)) F := by
  classical
  by_cases hb : b ∈ F.support
  · rw [eval_eq']
    exact Finset.single_le_sum (fun e _ => mul_nonneg (hF e)
      (Finset.prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) _)) hb
  · have hz : coeff b F = 0 := by simpa only [mem_support_iff, not_not] using hb
    rw [hz, zero_mul]
    exact eval_nonneg F hF D

/-- The complementary exponents have exactly the subgroup's Hilbert dimension. -/
theorem complement_sum {K : Type*} [NontriviallyNormedField K]
    {G : EmbeddedGroupProduct K} {H : AlgebraicSubgroup G}
    (r : SourceMixedCodimensionIndex G H) :
    ∑ i, r.complementIndex i = varietyDimension G H.carrier := by
  classical
  change (∑ i, ((G.factor i).dimension - r.exponent i)) = _
  rw [Finset.sum_tsub_distrib _ (fun i _ => r.bounded i)]
  change G.dimension - (∑ i, r.exponent i) = varietyDimension G H.carrier
  rw [← r.sum_eq, Nat.add_sub_cancel_left]

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

end PhilipponMultiplicity.CountingProof
namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

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
namespace PhilipponMultiplicity.CountingProof

/-- A nonempty multiprojective locus has a nonzero Hilbert polynomial. -/
theorem hilbertPolynomial_ne_zero {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) (hne : S.Nonempty) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal S) ≠ 0 := by
  intro hz
  obtain ⟨b,hb⟩ := Hilbert.hilbertPolynomial_spec K M.factorCount M.ambientDimension
    (M.vanishingIdeal S) (multigraded_hilbert_polynomial_exists K M _
      (vanishing_homogeneous M S))
  have heq := hb b (fun _ => le_rfl)
  rw [hz,map_zero] at heq
  have hzero : Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal S) b = 0 := by exact_mod_cast heq.symm
  exact (Nat.ne_of_gt (M.hilbertFunction_pos hne b)) hzero

/-- The lower binomial estimate includes zero codimension and zero contact. -/
theorem binomial_lower (T s : ℕ) :
    ((T+1 : ℕ) : ℝ)^s / (s.factorial : ℝ) ≤ ((T+s).choose s : ℝ) := by
  simpa [show T+s+1-s = T+1 by omega] using (Nat.pow_le_choose (α := ℝ) s (T+s))

/-- A single nonnegative top Hilbert monomial is bounded by the whole form. -/
theorem mixed_lower {K : Type*} [NontriviallyNormedField K]
    (G : EmbeddedGroupProduct K) (H : AlgebraicSubgroup G)
    (r : SourceMixedCodimensionIndex G H) (D : G.FactorIndex → ℕ) :
    mixedDegree G H.carrier r.complementIndex *
      (Nat.factorial (varietyDimension G H.carrier) : ℝ) /
      (∏ i, (Nat.factorial (r.complementIndex i) : ℝ)) *
      (∏ i, (D i : ℝ)^r.complementIndex i) ≤ hilbertDegreeForm G H.carrier D := by
  classical
  let F := Hilbert.hilbertPolynomial K G.factorCount G.ambient.ambientDimension
    (G.vanishingIdeal H.carrier)
  let b : G.FactorIndex →₀ ℕ := Finsupp.equivFunOnFinite.symm r.complementIndex
  let Q := homogeneousComponent F.totalDegree F
  have hb : b.degree = F.totalDegree := by
    simpa [b, F, Finsupp.degree_eq_sum, varietyDimension] using complement_sum r
  have hcoeff : coeff b Q = coeff b F := by simp [Q, coeff_homogeneousComponent, hb]
  have hQ := (multigraded_hilbert_polynomial_top_coefficients K G.ambient
    (G.vanishingIdeal H.carrier)
    (vanishing_homogeneous G.ambient (G.embedding '' H.carrier))).1
  change ∀ e, 0 ≤ coeff e Q at hQ
  have hterm := mul_le_mul_of_nonneg_left (term_le_eval Q hQ D b)
    (Nat.cast_nonneg F.totalDegree.factorial : (0:ℚ) ≤ _)
  have hterm' : (F.totalDegree.factorial : ℚ) * coeff b F *
      (∏ i, (D i : ℚ)^r.complementIndex i) ≤
      Hilbert.degreeValue K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal H.carrier) D := by
    change _ ≤ eval (fun i => (D i : ℚ)) ((F.totalDegree.factorial : ℚ) • Q)
    rw [smul_eq_C_mul, map_mul, eval_C]
    simpa [hcoeff, b, mul_assoc] using hterm
  have htermR : (F.totalDegree.factorial : ℝ) * ((coeff b F : ℚ) : ℝ) *
      (∏ i, (D i : ℝ)^r.complementIndex i) ≤ hilbertDegreeForm G H.carrier D := by
    unfold hilbertDegreeForm
    exact_mod_cast hterm'
  have hfac : (∏ i, ((r.complementIndex i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.factorial_ne_zero _)
  rw [mixedDegree, if_pos (complement_sum r)]
  change (((coeff b F : ℚ) : ℝ) * _) * _ / _ * _ ≤ _
  change (((coeff b F : ℚ) : ℝ) * _) * (F.totalDegree.factorial : ℝ) / _ * _ ≤ _
  convert htermR using 1 <;> field_simp <;> ring

/-- A nonempty projective locus has degree at least one and bounded dimension. -/
theorem single_factor_degree {K : Type*} [Field K] {N : ℕ}
    (V : SectionThree.ProjectiveSubvariety K N) (hne : V.carrier.Nonempty) :
    1 ≤ V.degree ∧ V.dimension ≤ N := by
  classical
  let M := projectiveSpace K N
  let I := M.vanishingIdeal V.carrierInSingleFactor
  let F := Hilbert.hilbertPolynomial K 1 (fun _ => N) I
  let e : Fin 1 →₀ ℕ := Finsupp.single 0 F.totalDegree
  have hF : F ≠ 0 := hilbertPolynomial_ne_zero M _ (hne.image (fun x => fun _ => x))
  have hce : coeff e F ≠ 0 := by
    intro hz
    have ht : homogeneousComponent F.totalDegree F = 0 := by rw [top_fin_one, hz, monomial_zero]
    obtain ⟨b, hb, hd⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF) Finsupp.degree
    have hd' : b.degree = F.totalDegree := hd.symm
    have hc := congrArg (coeff b) ht
    rw [coeff_homogeneousComponent, if_pos hd', coeff_zero] at hc
    exact (mem_support_iff.mp hb) hc
  have het : e.degree = F.totalDegree := by simp [e, degree_fin_one]
  have hI := vanishing_homogeneous M V.carrierInSingleFactor
  have htop := multigraded_hilbert_polynomial_top_coefficients K M I hI
  have hdegree : V.degree = (F.totalDegree.factorial : ℚ) * coeff e F := by
    change eval (fun _ => (1:ℚ)) ((F.totalDegree.factorial : ℚ) •
      homogeneousComponent F.totalDegree F) = _
    rw [smul_eq_C_mul,map_mul,eval_C,eval_top_fin_one]
    simp [e]
  have hpos : 0 < V.degree := by
    rw [hdegree]
    apply mul_pos (by exact_mod_cast Nat.factorial_pos F.totalDegree)
    have hc := htop.1 e
    change 0 ≤ coeff e (homogeneousComponent F.totalDegree F) at hc
    rw [coeff_homogeneousComponent, if_pos het] at hc
    exact lt_of_le_of_ne hc (Ne.symm hce)
  obtain ⟨n,hn⟩ := idealMixedDegree_integral M I hI (fun _ => F.totalDegree)
  have he : Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => F.totalDegree) = e := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp [e]
  have hn' : V.degree = (n:ℚ) := by
    change (if (∑ _ : Fin 1, F.totalDegree) = F.totalDegree then
      coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => F.totalDegree)) F *
        (∏ _ : Fin 1, (F.totalDegree.factorial : ℚ)) else 0) = (n:ℚ) at hn
    simpa [he, hdegree, mul_comm] using hn
  refine ⟨?_, ?_⟩
  · rw [hn'] at hpos ⊢
    exact_mod_cast Nat.succ_le_of_lt (show 0<n by exact_mod_cast hpos)
  · by_contra h
    have hN : N < e 0 := by
      change ¬ F.totalDegree ≤ N at h
      simpa [e] using Nat.lt_of_not_ge h
    have hz := htop.2 e ⟨(0 : Fin 1),hN⟩
    change coeff e (homogeneousComponent F.totalDegree F) = 0 at hz
    rw [coeff_homogeneousComponent, if_pos het] at hz
    exact hce hz

/-- Uniform lower degree bound for a product of nonempty projective loci. -/
theorem product_degree_lower {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, SectionThree.ProjectiveSubvariety K (M.ambientDimension i))
    (hne : ∀ i, (V i).carrier.Nonempty) (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    0 < SectionThree.locusDegreeValue M (SectionThree.productCarrier M V) D ∧
    (∏ i, (D i : ℚ)^(V i).dimension) ≤
      (∏ i, ((M.ambientDimension i).factorial : ℚ)) *
        SectionThree.locusDegreeValue M (SectionThree.productCarrier M V) D := by
  classical
  have hV := fun i => single_factor_degree (V i) (hne i)
  have hfac : (∏ i, ((V i).dimension.factorial : ℚ)) > 0 :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
  have hdeg : (1:ℚ) ≤ ∏ i, (V i).degree := Finset.one_le_prod fun i _ => (hV i).1
  have hdim : (1:ℚ) ≤ ((SectionThree.locusDimension M
      (SectionThree.productCarrier M V)).factorial : ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
  have hmon : 0 < ∏ i, (D i : ℚ)^(V i).dimension :=
    Finset.prod_pos fun i _ => pow_pos (by exact_mod_cast hD i) _
  have hform := lemma_3_4 K hK M V D hD
  have hpos : 0 < SectionThree.locusDegreeValue M (SectionThree.productCarrier M V) D := by
    rw [hform]
    exact mul_pos (mul_pos (div_pos (lt_of_lt_of_le zero_lt_one hdim) hfac)
      (lt_of_lt_of_le zero_lt_one hdeg)) hmon
  refine ⟨hpos, ?_⟩
  have hscale : (∏ i, ((V i).dimension.factorial : ℚ)) ≤
      ∏ i, ((M.ambientDimension i).factorial : ℚ) :=
    Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => by
      exact_mod_cast Nat.factorial_le (hV i).2)
  have heq : (∏ i, ((V i).dimension.factorial : ℚ)) *
      SectionThree.locusDegreeValue M (SectionThree.productCarrier M V) D =
      ((SectionThree.locusDimension M (SectionThree.productCarrier M V)).factorial : ℚ) *
        (∏ i, (V i).degree) * (∏ i, (D i : ℚ)^(V i).dimension) := by
    rw [hform]
    field_simp
  calc
    (∏ i, (D i : ℚ)^(V i).dimension) ≤
      (∏ i, ((V i).dimension.factorial : ℚ)) *
        SectionThree.locusDegreeValue M (SectionThree.productCarrier M V) D := by
          rw [heq]
          exact le_mul_of_one_le_left hmon.le (one_le_mul_of_one_le_of_one_le hdim hdeg)
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale hpos.le

/-- A closed factor projection is locally closed in its projective space. -/
theorem projection_locallyClosed {K : Type*} [NontriviallyNormedField K]
    (G : EmbeddedGroupProduct K) (hdisjoint : HasDisjointFactors G)
    (H : AlgebraicSubgroup G) (i : G.FactorIndex) :
    @IsLocallyClosed _ (TopologicalSpace.induced (fun x _ => x)
      (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology)
      (Subtype.val '' factorProjection G H i) := by
  letI : TopologicalSpace (G.factor i).Point := factorTopology (G.factor i)
  letI : TopologicalSpace (Projectivization K (Fin ((G.factor i).ambientDimension + 1) → K)) :=
    TopologicalSpace.induced (fun x _ => x)
      (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology
  have he : Topology.IsInducing (Subtype.val : (G.factor i).Point → _) := by
    constructor
    change TopologicalSpace.induced (fun x : (G.factor i).Point => fun _ : Fin 1 => x.val)
      (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology =
      TopologicalSpace.induced Subtype.val (TopologicalSpace.induced
        (fun x : Projectivization K (Fin ((G.factor i).ambientDimension + 1) → K) =>
          fun _ : Fin 1 => x) (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology)
    rw [induced_compose]
    rfl
  apply ((hdisjoint H).2 i).isLocallyClosed.image he
  simpa only [Subtype.range_coe] using (G.factor i).locallyClosed

/-- The uniform degree-ratio estimate uses only the genuine product property.
Ambient factorials bound every subgroup's denominator in Lemma 3.4. -/
theorem disjoint_degree_ratio {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) (G : EmbeddedGroupProduct K)
    (hdisjoint : HasDisjointFactors G) :
    ∃ c : ℝ, 0 < c ∧ ∀ (H : AlgebraicSubgroup G) (D : G.FactorIndex → ℕ),
      (∀ i, 1 ≤ D i) → 0 < hilbertDegreeForm G H.carrier D ∧
      hilbertDegreeForm G Set.univ D / hilbertDegreeForm G H.carrier D ≤
        c * ∏ i, (D i : ℝ)^factorCodimension G H i := by
  classical
  let F : ℝ := ∏ i, ((G.ambient.ambientDimension i).factorial : ℝ)
  let B : ℝ := hilbertDegreeForm G Set.univ (fun _ => 1)
  have hF : 0 < F := Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
  refine ⟨(|B|+1)*F, mul_pos (by positivity) hF, ?_⟩
  intro H D hD
  let V (i : G.ambient.FactorIndex) : SectionThree.ProjectiveSubvariety K
      (G.ambient.ambientDimension i) :=
    ⟨Subtype.val '' factorProjection G H i, projection_locallyClosed G hdisjoint H i⟩
  have hV (i : G.FactorIndex) : (V i).carrier.Nonempty :=
    ⟨((0 : G.Point) i).val, ⟨(0 : G.Point) i, ⟨0,H.toAddSubgroup.zero_mem,rfl⟩,rfl⟩⟩
  have hcarrier : G.embedding '' H.carrier = SectionThree.productCarrier G.ambient V := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩ i
      exact ⟨y i,⟨y,hy,rfl⟩,rfl⟩
    · intro hx
      choose y hy heq using hx
      have hm : (fun i => y i) ∈ H.carrier := (hdisjoint H).1 _ |>.mpr hy
      exact ⟨y,hm,funext heq⟩
  have hcod (i : G.FactorIndex) : factorCodimension G H i =
      (G.factor i).dimension - (V i).dimension := by
    unfold factorCodimension SectionThree.ProjectiveSubvariety.dimension
      SectionThree.idealDimension SectionThree.ProjectiveSubvariety.carrierInSingleFactor
    simp only [V, Set.image_image, Function.comp_def]
    rfl
  obtain ⟨hpos,hlower⟩ := product_degree_lower hK G.ambient V hV D hD
  have hform : hilbertDegreeForm G H.carrier D =
      (SectionThree.locusDegreeValue G.ambient (SectionThree.productCarrier G.ambient V) D : ℝ) := by
    unfold hilbertDegreeForm EmbeddedGroupProduct.vanishingIdeal
    rw [hcarrier]
    rfl
  have hposR : 0 < hilbertDegreeForm G H.carrier D := by rw [hform]; exact_mod_cast hpos
  have hlowR : (∏ i, (D i : ℝ)^(V i).dimension) ≤ F * hilbertDegreeForm G H.carrier D := by
    rw [hform]
    dsimp only [F]
    exact_mod_cast hlower
  refine ⟨hposR, (div_le_iff₀ hposR).mpr ?_⟩
  let W : ∀ i : G.ambient.FactorIndex,
      SectionThree.ProjectiveSubvariety K (G.ambient.ambientDimension i) :=
    fun i => ⟨(G.factor i).carrier,(G.factor i).locallyClosed⟩
  have hfull : G.embedding '' Set.univ = SectionThree.productCarrier G.ambient W := by
    ext x
    constructor
    · rintro ⟨y,_,rfl⟩ i
      exact (y i).property
    · intro hx
      exact ⟨fun i => ⟨x i,hx i⟩,Set.mem_univ _,rfl⟩
  have hmain : hilbertDegreeForm G Set.univ D = B *
      ∏ i, (D i : ℝ)^(G.factor i).dimension := by
    have hd := lemma_3_4 K hK G.ambient W D hD
    have h1 := lemma_3_4 K hK G.ambient W (fun _ => 1) (fun _ => le_rfl)
    have heq : SectionThree.locusDegreeValue G.ambient (SectionThree.productCarrier G.ambient W) D =
        SectionThree.locusDegreeValue G.ambient (SectionThree.productCarrier G.ambient W) (fun _ => 1) *
          ∏ i, (D i : ℚ)^(G.factor i).dimension := by
      rw [hd,h1]
      simp only [Nat.cast_one,one_pow,Finset.prod_const_one,mul_one]
      rfl
    unfold B hilbertDegreeForm EmbeddedGroupProduct.vanishingIdeal
    rw [hfull]
    exact_mod_cast heq
  have hmon : (∏ i, (D i : ℝ)^(G.factor i).dimension) ≤
      (∏ i, (D i : ℝ)^factorCodimension G H i) *
        (∏ i, (D i : ℝ)^(V i).dimension) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun i _ => pow_nonneg (Nat.cast_nonneg _) _)
    intro i _
    rw [hcod,← pow_add]
    exact pow_le_pow_right₀ (by exact_mod_cast hD i) (by omega)
  have hc : 0 ≤ ∏ i, (D i : ℝ)^factorCodimension G H i := by positivity
  calc
    hilbertDegreeForm G Set.univ D = B * ∏ i, (D i : ℝ)^(G.factor i).dimension := hmain
    _ ≤ (|B|+1) * ∏ i, (D i : ℝ)^(G.factor i).dimension :=
      mul_le_mul_of_nonneg_right (le_trans (le_abs_self B) (by linarith)) (by positivity)
    _ ≤ (|B|+1) * ((∏ i, (D i : ℝ)^factorCodimension G H i) *
        (∏ i, (D i : ℝ)^(V i).dimension)) := mul_le_mul_of_nonneg_left hmon (by positivity)
    _ ≤ (|B|+1) * ((∏ i, (D i : ℝ)^factorCodimension G H i) *
        (F * hilbertDegreeForm G H.carrier D)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlowR hc) (by positivity)
    _ = _ := by ring

end PhilipponMultiplicity.CountingProof
end


set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators
open Submodule
noncomputable section
namespace PhilipponMultiplicity.CountingProof

/-- A finite generating family contains as many independent elements as its rank,
even when its integer span has torsion. -/
theorem independent_subfamily {M : Type*} [AddCommGroup M] {m : ℕ}
    (v : Fin m → M) :
    ∃ s : Finset (Fin m), s.card = Module.finrank ℤ (span ℤ (Set.range v)) ∧
      LinearIndependent ℤ (fun i : s => v i) := by
  classical
  let N := span ℤ (Set.range v)
  let w (i : Fin m) : N := ⟨v i,subset_span (Set.mem_range_self i)⟩
  letI : Module.Finite ℤ N := Module.Finite.span_of_finite ℤ (Set.finite_range v)
  have hw : span ℤ (Set.range w) = ⊤ :=
    (span_range_subtype_eq_top_iff N (fun i => subset_span (Set.mem_range_self i))).mpr rfl
  obtain ⟨s,hs,hmax⟩ := exists_maximal_linearIndepOn ℤ w
  letI : Fintype s := Fintype.ofFinite s
  let L := span ℤ (w '' s)
  have htor : Module.IsTorsion ℤ (N ⧸ L) := by
    have hgen (i : Fin m) : L.mkQ (w i) ∈ torsion ℤ (N ⧸ L) := by
      rw [mem_torsion_iff]
      by_cases hi : i ∈ s
      · refine ⟨1, ?_⟩
        simp only [one_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact subset_span (Set.mem_image_of_mem w hi)
      · obtain ⟨a,ha,hmem⟩ := hmax i hi
        refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
        change a • L.mkQ (w i) = 0
        rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hmem
    have hall : (⊤ : Submodule ℤ N) ≤ (torsion ℤ (N ⧸ L)).comap L.mkQ := by
      rw [← hw]
      apply span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hgen i
    intro q
    obtain ⟨x,rfl⟩ := L.mkQ_surjective q
    exact hall (show x ∈ (⊤ : Submodule ℤ N) from trivial)
  have hrank : Module.finrank ℤ L = Module.finrank ℤ N := by
    have h := L.finrank_quotient_add_finrank
    rw [htor.finrank_eq_zero,zero_add] at h
    exact h
  have hind : LinearIndependent ℤ (fun i : s => w i) := hs
  have hcard : Module.finrank ℤ L = Fintype.card s := by
    have hspan : span ℤ (Set.range (fun i : s => w i)) = L := by
      congr 1
      ext x
      simp only [Set.mem_range, Set.mem_image, Subtype.exists, exists_prop]
    rw [← hspan]
    exact Module.finrank_eq_card_basis (Module.Basis.span hind)
  refine ⟨s.toFinite.toFinset, ?_, ?_⟩
  · simpa only [Set.toFinite_toFinset, Set.toFinset_card] using hcard.symm.trans hrank
  · have h := hind.map' N.subtype (ker_subtype N)
    have hh : LinearIndepOn ℤ v s := h
    change LinearIndepOn ℤ v (↑s.toFinite.toFinset : Set (Fin m))
    simpa only [Set.Finite.coe_toFinset] using hh

/-- Natural-coefficient grid in an arbitrary abelian group. -/
def nonnegativeGrid {M : Type*} [AddCommGroup M] {m : ℕ}
    (v : Fin m → M) (S : ℝ) : Set M :=
  {x | ∃ a : Fin m → ℕ, (∀ i, (a i : ℝ) ≤ S) ∧ x = ∑ i, a i • v i}

theorem nonnegativeGrid_finite {M : Type*} [AddCommGroup M] {m : ℕ}
    (v : Fin m → M) (S : ℝ) (hS : 0 ≤ S) : (nonnegativeGrid v S).Finite := by
  let f (a : Fin m → Fin (⌊S⌋₊+1)) : M := ∑ i, (a i).val • v i
  have heq : nonnegativeGrid v S = Set.range f := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨fun i => ⟨a i,Nat.lt_succ_of_le ((Nat.le_floor_iff hS).mpr (ha i))⟩,rfl⟩
    · rintro ⟨a,rfl⟩
      refine ⟨fun i => (a i).val, ?_,rfl⟩
      intro i
      exact (Nat.le_floor_iff hS).mp (Nat.le_of_lt_succ (a i).isLt)
  rw [heq]
  exact Set.finite_range f

/-- A rank-sized independent subfamily gives an injective integer cube in the grid. -/
theorem nonnegativeGrid_card_lower {M : Type*} [AddCommGroup M] {m : ℕ}
    (v : Fin m → M) (S : ℝ) (hS : 0 ≤ S) :
    S ^ Module.finrank ℤ (span ℤ (Set.range v)) ≤ ((nonnegativeGrid v S).ncard : ℝ) := by
  classical
  obtain ⟨s,hcard,hlin⟩ := independent_subfamily v
  let f (a : s → Fin (⌊S⌋₊+1)) : M := ∑ i, (a i).val • v i
  have hf : Function.Injective f := by
    intro a b hab
    have h := hlin.fintypeLinearCombination_injective (a₁ := fun i => ((a i).val : ℤ))
      (a₂ := fun i => ((b i).val : ℤ)) (by
        simpa only [Fintype.linearCombination_apply,natCast_zsmul,f] using hab)
    funext i
    apply Fin.ext
    exact_mod_cast congrFun h i
  have hsub : Set.range f ⊆ nonnegativeGrid v S := by
    rintro _ ⟨a,rfl⟩
    let b (i : Fin m) : ℕ := if hi : i ∈ s then (a ⟨i,hi⟩).val else 0
    refine ⟨b,?_,?_⟩
    · intro i
      dsimp only [b]
      split_ifs with hi
      · exact (Nat.le_floor_iff hS).mp (Nat.le_of_lt_succ (a ⟨i,hi⟩).isLt)
      · simpa using hS
    · change (∑ i : s, (a i).val • v i) = ∑ i : Fin m, b i • v i
      have heq : (∑ i : Fin m, b i • v i) = ∑ i ∈ s, b i • v i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro i _ hi
        simp [b,hi]
      rw [heq, Finset.sum_subtype s (fun _ => Iff.rfl)]
      apply Finset.sum_congr rfl
      intro i _
      simp [b,i.property]
  have hnat : (⌊S⌋₊+1)^s.card ≤ (nonnegativeGrid v S).ncard := by
    have h := Set.ncard_le_ncard hsub (nonnegativeGrid_finite v S hS)
    rw [Set.ncard_range_of_injective hf] at h
    simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using h
  rw [← hcard]
  calc
    S^s.card ≤ ((⌊S⌋₊+1 : ℕ) : ℝ)^s.card :=
      pow_le_pow_left₀ hS (by exact_mod_cast (Nat.lt_floor_add_one S).le) _
    _ ≤ _ := by exact_mod_cast hnat

theorem nonnegativeGrid_map {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {m : ℕ} (f : M →+ N) (v : Fin m → M) (S : ℝ) :
    f '' nonnegativeGrid v S = nonnegativeGrid (fun i => f (v i)) S := by
  ext x
  constructor
  · rintro ⟨y,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨a,ha,by simp⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨∑ i, a i • v i,⟨a,ha,rfl⟩,by simp⟩

/-- The quotient grid and the set of translated subgroup carriers have equal cardinality. -/
theorem coset_grid_card_lower {M : Type*} [AddCommGroup M] {m : ℕ}
    (H : AddSubgroup M) (v : Fin m → M) (S : ℝ) (hS : 0 ≤ S) :
    S ^ Module.finrank ℤ (span ℤ (Set.range (fun i => QuotientAddGroup.mk' H (v i)))) ≤
      (((fun x => (fun y => x+y) '' (H : Set M)) '' nonnegativeGrid v S).ncard : ℝ) := by
  classical
  let q := QuotientAddGroup.mk' H
  let fiber (z : M ⧸ H) : Set M := q ⁻¹' {z}
  have hf : Function.Injective fiber := by
    intro x y h
    obtain ⟨a,rfl⟩ := QuotientAddGroup.mk_surjective x
    have ha : a ∈ fiber (q a) := rfl
    change fiber (q a) = fiber y at h
    rw [h] at ha
    exact ha
  have hcoset (x : M) : (fun y => x+y) '' (H : Set M) = fiber (q x) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change q (x+z) = q x
      rw [map_add, show q z = 0 from (QuotientAddGroup.eq_zero_iff z).mpr hz,add_zero]
    · intro hy
      have hz : y-x ∈ H := (QuotientAddGroup.eq_zero_iff (y-x)).mp (by
        change q (y-x) = 0
        rw [map_sub, show q y = q x from hy,sub_self])
      exact ⟨y-x,hz,by abel⟩
  have heq : (fun x => (fun y => x+y) '' (H : Set M)) '' nonnegativeGrid v S =
      fiber '' nonnegativeGrid (fun i => q (v i)) S := by
    simp_rw [hcoset]
    rw [← nonnegativeGrid_map q,Set.image_image]
  rw [heq, Set.ncard_image_of_injective _ hf]
  exact nonnegativeGrid_card_lower (fun i => q (v i)) S hS

end PhilipponMultiplicity.CountingProof

end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) :
    (∀ (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (T : ℕ),
      (((T + 1 : ℕ) : ℝ) ^ analyticCodimension A H.carrier) /
          (Nat.factorial (analyticCodimension A H.carrier) : ℝ) ≤
        (Nat.choose (T + analyticCodimension A H.carrier)
          (analyticCodimension A H.carrier) : ℝ)) ∧
    (∀ (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G),
      ¬ A.carrier ⊆ H.carrier →
      ∀ (m : ℕ) (γ : Fin m → G.Point) (S : ℝ), 0 ≤ S →
        S ^ samplingQuotientRank γ H ≤
          (((fun x => PhilipponMultiplicity.translate x H.carrier) '' samplingGrid γ S).ncard : ℝ)) ∧
    (∀ (H : AlgebraicSubgroup G) (r : SourceMixedCodimensionIndex G H)
        (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
      (mixedDegree G H.carrier r.complementIndex : ℝ) *
        (Nat.factorial (varietyDimension G H.carrier) : ℝ) /
        (∏ i, (Nat.factorial (r.complementIndex i) : ℝ)) *
        (∏ i, (D i : ℝ) ^ r.complementIndex i) ≤ hilbertDegreeForm G H.carrier D) ∧
    (HasDisjointFactors G → ∃ c : ℝ, 0 < c ∧
      ∀ (H : AlgebraicSubgroup G) (D : G.FactorIndex → ℕ), (∀ i, 1 ≤ D i) →
        0 < hilbertDegreeForm G H.carrier D ∧
        hilbertDegreeForm G Set.univ D / hilbertDegreeForm G H.carrier D ≤
          c * ∏ i, (D i : ℝ) ^ factorCodimension G H i)  := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A H T
    exact CountingProof.binomial_lower T (analyticCodimension A H.carrier)
  · intro A H _ m γ S hS
    exact CountingProof.coset_grid_card_lower H.toAddSubgroup γ S hS
  · intro H r D _
    exact CountingProof.mixed_lower G H r D
  · exact CountingProof.disjoint_degree_ratio hK G

