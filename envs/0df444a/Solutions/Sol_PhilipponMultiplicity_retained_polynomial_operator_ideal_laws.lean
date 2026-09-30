-- Prove2me | solution 1 for PhilipponMultiplicity.retained_polynomial_operator_ideal_laws
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T17:46:48.07222+00:00
-- url     : https://prove2.me/submissions/e27b5594-3c9e-451e-9e76-0f38138357bb

import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter MvPolynomial
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


end PhilipponMultiplicity.OperatorSupport

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

theorem solution
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
    (atlas : TranslationAtlas A g) (T : ℕ) (I J : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (hJ : IsMultihomogeneousIdeal G.ambient J) :
    (I ≤ J → retainedPolynomialOperatorIdeal atlas T I ≤
      retainedPolynomialOperatorIdeal atlas T J) ∧
    (retainedPolynomialOperatorIdeal atlas T (I ⊔ J) =
      retainOnGroup G (retainedPolynomialOperatorIdeal atlas T I ⊔
        retainedPolynomialOperatorIdeal atlas T J)) := by
  exact ⟨OperatorSupport.retainedPolynomialOperatorIdeal_mono atlas T,
    OperatorSupport.retainedPolynomialOperatorIdeal_sup atlas T I J hI hJ⟩
