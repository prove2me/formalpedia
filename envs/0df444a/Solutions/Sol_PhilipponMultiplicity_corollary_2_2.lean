-- Prove2me | solution 1 for PhilipponMultiplicity.corollary_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T05:11:53.366221+00:00
-- url     : https://prove2.me/submissions/ade087c4-317d-4a84-94d2-f14e8857aaae

import Definitions.Def_PhilipponMultiplicity_Corollaries
import Theorems.Thm_PhilipponMultiplicity_theorem_2_1
import Theorems.Thm_PhilipponMultiplicity_lemma_3_4
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
import Theorems.Thm_PhilipponMultiplicity_analyticCodimension_le_dimension
import Theorems.Thm_PhilipponMultiplicity_analytic_subgroup_containment_of_codimension_zero

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity
noncomputable section

namespace PhilipponMultiplicity.Corollary22Proof

-- Reuse the homogeneous-span argument from PhilipponProjectiveHilbertExistence.
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

private theorem eval_nonneg {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℚ) (hF : ∀ b, 0 ≤ coeff b F) (D : ι → ℕ) :
    0 ≤ eval (fun i => (D i : ℚ)) F := by
  classical
  rw [eval_eq']
  exact Finset.sum_nonneg fun b _ => mul_nonneg (hF b)
    (Finset.prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) _)

private theorem term_le_eval {ι : Type*} [Fintype ι]
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
private theorem complement_sum {K : Type*} [NontriviallyNormedField K]
    {G : EmbeddedGroupProduct K} {H : AlgebraicSubgroup G}
    (r : SourceMixedCodimensionIndex G H) :
    ∑ i, r.complementIndex i = varietyDimension G H.carrier := by
  classical
  change (∑ i, ((G.factor i).dimension - r.exponent i)) = _
  rw [Finset.sum_tsub_distrib _ (fun i _ => r.bounded i)]
  change G.dimension - (∑ i, r.exponent i) = varietyDimension G H.carrier
  rw [← r.sum_eq, Nat.add_sub_cancel_left]

/-- One nonnegative top coefficient is bounded by the full Hilbert form.
The fixed factorial product makes the bound uniform over all mixed indices. -/
private theorem mixed_term_bound {K : Type*} [NontriviallyNormedField K]
    (G : EmbeddedGroupProduct K) (H : AlgebraicSubgroup G)
    (r : SourceMixedCodimensionIndex G H) (D : G.FactorIndex → ℕ) :
    mixedDegree G H.carrier r.complementIndex *
        (∏ i, (D i : ℝ) ^ r.complementIndex i) ≤
      (∏ i, ((G.factor i).dimension.factorial : ℝ)) *
        hilbertDegreeForm G H.carrier D := by
  classical
  let F := Hilbert.hilbertPolynomial K G.factorCount G.ambient.ambientDimension
    (G.vanishingIdeal H.carrier)
  let b : G.FactorIndex →₀ ℕ := Finsupp.equivFunOnFinite.symm r.complementIndex
  let Q := homogeneousComponent F.totalDegree F
  have hb : b.degree = F.totalDegree := by
    simpa [b, F, Finsupp.degree_eq_sum, varietyDimension] using complement_sum r
  have hcoeff : coeff b Q = coeff b F := by
    simp [Q, coeff_homogeneousComponent, hb]
  have hQ := (multigraded_hilbert_polynomial_top_coefficients K G.ambient
    (G.vanishingIdeal H.carrier)
    (vanishing_homogeneous G.ambient (G.embedding '' H.carrier))).1
  change ∀ e, 0 ≤ coeff e Q at hQ
  have hterm := term_le_eval Q hQ D b
  have heval := eval_nonneg Q hQ D
  have hfac : (1 : ℚ) ≤ (F.totalDegree.factorial : ℚ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos F.totalDegree)
  have hterm' : coeff b F * (∏ i, (D i : ℚ) ^ r.complementIndex i) ≤
      Hilbert.degreeValue K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal H.carrier) D := by
    change _ ≤ eval (fun i => (D i : ℚ)) ((F.totalDegree.factorial : ℚ) • Q)
    rw [smul_eq_C_mul, map_mul, eval_C]
    have hterm0 : coeff b F * (∏ i, (D i : ℚ) ^ r.complementIndex i) ≤
        eval (fun i => (D i : ℚ)) Q := by simpa [hcoeff, b] using hterm
    exact hterm0.trans (le_mul_of_one_le_left heval hfac)
  have htermR : ((coeff b F : ℚ) : ℝ) * (∏ i, (D i : ℝ) ^ r.complementIndex i) ≤
      hilbertDegreeForm G H.carrier D := by
    unfold hilbertDegreeForm
    exact_mod_cast hterm'
  have hcoefR : 0 ≤ ((coeff b F : ℚ) : ℝ) := by
    exact_mod_cast (hcoeff ▸ hQ b)
  have hmono : 0 ≤ (∏ i, (D i : ℝ) ^ r.complementIndex i) := by positivity
  have hprod : (∏ i, ((r.complementIndex i).factorial : ℝ)) ≤
      ∏ i, ((G.factor i).dimension.factorial : ℝ) := by
    apply Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _)
    intro i _
    exact_mod_cast Nat.factorial_le (Nat.sub_le (G.factor i).dimension (r.exponent i))
  rw [mixedDegree, if_pos (complement_sum r)]
  change (((coeff b F : ℚ) : ℝ) * _) * _ ≤ _
  calc
    (((coeff b F : ℚ) : ℝ) * (∏ i, ((r.complementIndex i).factorial : ℝ))) *
        (∏ i, (D i : ℝ) ^ r.complementIndex i) =
      (∏ i, ((r.complementIndex i).factorial : ℝ)) *
        (((coeff b F : ℚ) : ℝ) * (∏ i, (D i : ℝ) ^ r.complementIndex i)) := by ring
    _ ≤ (∏ i, ((G.factor i).dimension.factorial : ℝ)) *
        (((coeff b F : ℚ) : ℝ) * (∏ i, (D i : ℝ) ^ r.complementIndex i)) :=
      mul_le_mul_of_nonneg_right hprod (mul_nonneg hcoefR hmono)
    _ ≤ _ := mul_le_mul_of_nonneg_left htermR (by positivity)

/-- Lemma 3.4 factors out the degree monomial for the product group. -/
private theorem product_degree_scaling {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) (G : EmbeddedGroupProduct K)
    (c D : G.FactorIndex → ℕ) (hc : ∀ i, 1 ≤ c i) (hD : ∀ i, 1 ≤ D i) :
    hilbertDegreeForm G Set.univ (fun i => c i * D i) =
      hilbertDegreeForm G Set.univ c * ∏ i, (D i : ℝ) ^ (G.factor i).dimension := by
  classical
  let V : ∀ i : G.ambient.FactorIndex,
      SectionThree.ProjectiveSubvariety K (G.ambient.ambientDimension i) :=
    fun i => ⟨(G.factor i).carrier, (G.factor i).locallyClosed⟩
  have hcarrier : G.embedding '' Set.univ = SectionThree.productCarrier G.ambient V := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩ i
      exact (y i).property
    · intro hx
      exact ⟨fun i => ⟨x i, hx i⟩, Set.mem_univ _, rfl⟩
  have hmul := lemma_3_4 K hK G.ambient V (fun i => c i * D i)
    (fun i => Nat.mul_pos (hc i) (hD i))
  have hbase := lemma_3_4 K hK G.ambient V c hc
  have heq : SectionThree.locusDegreeValue G.ambient
      (SectionThree.productCarrier G.ambient V) (fun i => c i * D i) =
      SectionThree.locusDegreeValue G.ambient (SectionThree.productCarrier G.ambient V) c *
        ∏ i, (D i : ℚ) ^ (G.factor i).dimension := by
    rw [hmul, hbase]
    simp only [Nat.cast_mul, mul_pow, Finset.prod_mul_distrib]
    exact (mul_assoc _ _ _).symm
  unfold hilbertDegreeForm EmbeddedGroupProduct.vanishingIdeal
  rw [hcarrier]
  exact_mod_cast heq

end PhilipponMultiplicity.Corollary22Proof

open PhilipponMultiplicity.Corollary22Proof

/-- Philippon, pp. 359–360: the formal reduction retains the existing
zero-codimension containment theorem as its only open geometric dependency. -/
theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : AnalyticSubgroup G), A.dimension = 1 →
      ∀ (sample : Finset G.Point), 0 ∈ sample →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        (∀ i, 1 ≤ D i) →
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ sumset sample G.dimension,
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        (∀ H : AlgebraicSubgroup G, H.IsConnected → ¬ A.carrier ⊆ H.carrier →
          ∃ r : SourceMixedCodimensionIndex G H,
            c * r.degreeMonomial D ≤
              ((T + 1 : ℕ) : ℝ) * (cosetCount sample H.carrier : ℝ) *
                (mixedDegree G H.carrier r.complementIndex : ℝ)) →
        ∃ g : G.Point, PhilipponMultiplicity.translate g A.carrier ⊆ zeroLocusOnGroup G P := by
  classical
  obtain ⟨c, hc, hmain⟩ := theorem_2_1 K hK
  let F : ℝ := ∏ i, ((G.factor i).dimension.factorial : ℝ)
  let B : ℝ := hilbertDegreeForm G Set.univ (fun i => c (G.factor i))
  have hF : 0 < F := Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
  refine ⟨(|B| + 1) * F, mul_pos (by positivity) hF, ?_⟩
  intro A hdim sample hzero T D P hD hP hhom hcontact hlarge
  obtain ⟨H, hconn, _, ⟨g, hg⟩, hbound⟩ := hmain G A sample hzero T D P hP hhom hcontact
  have hAH : A.carrier ⊆ H.carrier := by
    by_contra hnot
    have hcodim : analyticCodimension A H.carrier = 1 := by
      have hle := analyticCodimension_le_dimension A H
      rw [hdim] at hle
      have hne : analyticCodimension A H.carrier ≠ 0 :=
        fun hz => hnot (analytic_subgroup_containment_of_codimension_zero K hK G A H hz)
      omega
    obtain ⟨r, hr⟩ := hlarge H hconn hnot
    let W : ℝ := ((T + 1 : ℕ) : ℝ) * (cosetCount sample H.carrier : ℝ)
    let M : ℝ := ∏ i, (D i : ℝ) ^ (G.factor i).dimension
    let N : ℝ := ∏ i, (D i : ℝ) ^ r.complementIndex i
    have hM : 0 < M := Finset.prod_pos fun i _ =>
      pow_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hD i))) _
    have hN : 0 ≤ N := by dsimp [N]; positivity
    have hW : 0 ≤ W := by dsimp [W]; positivity
    have hsplit : r.degreeMonomial D * N = M := by
      dsimp [SourceMixedCodimensionIndex.degreeMonomial, N, M]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [← pow_add]
      congr 1
      exact Nat.add_sub_of_le (r.bounded i)
    have hlower := mul_le_mul_of_nonneg_right hr hN
    have hmixed := mul_le_mul_of_nonneg_left (mixed_term_bound G H r D) hW
    have hlow : ((|B| + 1) * F) * M ≤ W * (F * hilbertDegreeForm G H.carrier D) := by
      calc
        ((|B| + 1) * F) * M = (((|B| + 1) * F) * r.degreeMonomial D) * N := by
          rw [mul_assoc ((|B| + 1) * F), hsplit]
        _ ≤ (W * mixedDegree G H.carrier r.complementIndex) * N := hlower
        _ = W * (mixedDegree G H.carrier r.complementIndex * N) := by ring
        _ ≤ _ := hmixed
    have hupper : W * hilbertDegreeForm G H.carrier D ≤ B * M := by
      simpa only [hcodim, Nat.choose_one_right,
        product_degree_scaling hK G (fun i => c (G.factor i)) D
          (fun i => hc (G.factor i)) hD] using hbound
    have hfinal := mul_le_mul_of_nonneg_left hupper hF.le
    have hcontra : ((|B| + 1) * F) * M ≤ F * (B * M) := by
      calc
        _ ≤ W * (F * hilbertDegreeForm G H.carrier D) := hlow
        _ = F * (W * hilbertDegreeForm G H.carrier D) := by ring
        _ ≤ _ := hfinal
    have hBM : B < |B| + 1 := lt_of_le_of_lt (le_abs_self B) (lt_add_one _)
    have hstrict := mul_lt_mul_of_pos_right hBM (mul_pos hF hM)
    nlinarith only [hstrict, hcontra]
  refine ⟨-g, ?_⟩
  rintro x ⟨a, ha, rfl⟩
  obtain ⟨z, hz, hza⟩ := hg (hAH ha)
  have hx : -g + a = z := by rw [← hza]; simp
  change -g + a ∈ zeroLocusOnGroup G P
  rw [hx]
  exact hz
