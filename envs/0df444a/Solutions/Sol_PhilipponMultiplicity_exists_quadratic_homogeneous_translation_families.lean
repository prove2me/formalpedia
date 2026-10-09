-- Prove2me | solution 1 for PhilipponMultiplicity.exists_quadratic_homogeneous_translation_families
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T23:47:15.418722+00:00
-- url     : https://prove2.me/submissions/abac97f6-6670-4530-b398-cab514549a23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_quadratic_localized_parameter_families
import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_ParameterChart
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib


section

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.HomogeneousNormalization
universe u v w
variable {R : Type u} [CommSemiring R] {K : Type v} [Field K]
  {σ : Type w} [Fintype σ]

/-- Scaling variables in a form over an arbitrary coefficient ring. -/
theorem eval₂_scale (φ : R →+* K) (P : MvPolynomial σ R) (d : ℕ)
    (hP : ∀ m ∈ P.support, ∑ j, m j = d) (v : σ → K) (a : K) :
    eval₂ φ (fun j => a * v j) P = a ^ d * eval₂ φ v P := by
  classical
  simp only [eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hP m hm]
  ring

theorem eval₂_normalize (φ : R →+* K) (P : MvPolynomial σ R) (d : ℕ)
    (hP : ∀ m ∈ P.support, ∑ j, m j = d) (v : σ → K) (c : σ) :
    eval₂ φ (fun j => v j / v c) P = (v c)⁻¹ ^ d * eval₂ φ v P := by
  simpa only [div_eq_mul_inv, mul_comm] using eval₂_scale φ P d hP v (v c)⁻¹

/-- A homogeneous fraction of equal numerator/denominator degree is chart invariant. -/
theorem fraction_normalize (A B : MvPolynomial σ K) (d : ℕ)
    (hA : ∀ m ∈ A.support, ∑ j, m j = d)
    (hB : ∀ m ∈ B.support, ∑ j, m j = d)
    (v : σ → K) (c : σ) (hc : v c ≠ 0) (hden : eval v B ≠ 0) :
    eval (fun j => v j / v c) B ≠ 0 ∧
      eval (fun j => v j / v c) A / eval (fun j => v j / v c) B =
        eval v A / eval v B := by
  have hs : (v c)⁻¹ ^ d ≠ 0 := pow_ne_zero _ (inv_ne_zero hc)
  have hAs := eval₂_normalize (RingHom.id K) A d hA v c
  have hBs := eval₂_normalize (RingHom.id K) B d hB v c
  change eval (fun j => v j / v c) A = _ at hAs
  change eval (fun j => v j / v c) B = _ at hBs
  rw [hAs, hBs]
  exact ⟨mul_ne_zero hs hden, mul_div_mul_left _ _ hs⟩

/-- Normalizing the input of a tuple of equal-degree forms preserves its projective value. -/
theorem projective_normalize {ι : Type*} (φ : R →+* K)
    (P : ι → MvPolynomial σ R) (d : ℕ)
    (hP : ∀ t, ∀ m ∈ (P t).support, ∑ j, m j = d)
    (v : σ → K) (c : σ) (hc : v c ≠ 0)
    (hn : (fun t => eval₂ φ v (P t)) ≠ 0) :
    ∃ hn' : (fun t => eval₂ φ (fun j => v j / v c) (P t)) ≠ 0,
      Projectivization.mk K (fun t => eval₂ φ (fun j => v j / v c) (P t)) hn' =
        Projectivization.mk K (fun t => eval₂ φ v (P t)) hn := by
  have hs : (v c)⁻¹ ^ d ≠ 0 := pow_ne_zero _ (inv_ne_zero hc)
  have heq : (fun t => eval₂ φ (fun j => v j / v c) (P t)) =
      ((v c)⁻¹ ^ d) • (fun t => eval₂ φ v (P t)) := by
    funext t
    exact eval₂_normalize φ (P t) d (hP t) v c
  have hn' : (fun t => eval₂ φ (fun j => v j / v c) (P t)) ≠ 0 := by
    rw [heq]
    exact smul_ne_zero hs hn
  refine ⟨hn', (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ?_⟩
  exact ⟨(v c)⁻¹ ^ d, heq.symm⟩

def parameterPullback (X : Type*) : (X → K) →+* ((X × X) → K) :=
  RingHom.pi (fun xy : X × X => Pi.evalRingHom (fun _ : X => K) xy.2)

@[simp] theorem parameterPullback_apply (X : Type*) (f : X → K) (xy : X × X) :
    parameterPullback X f xy = f xy.2 := rfl

theorem pullback_degree (X : Type*) (P : MvPolynomial σ (X → K)) (d : ℕ)
    (hP : ∀ m ∈ P.support, ∑ j, m j = d) :
    ∀ m ∈ (map (parameterPullback X) P).support, ∑ j, m j = d := by
  intro m hm
  exact hP m (support_map_subset _ _ hm)

@[simp] theorem pullback_coeff (X : Type*) (P : MvPolynomial σ (X → K))
    (m : σ →₀ ℕ) (xy : X × X) :
    (map (parameterPullback X) P).coeff m xy = P.coeff m xy.2 := by
  rw [coeff_map]
  rfl

@[simp] theorem pullback_eval (X : Type*) (P : MvPolynomial σ (X → K))
    (xy : X × X) (v : σ → K) :
    eval₂ (Pi.evalRingHom (fun _ : X × X => K) xy) v (map (parameterPullback X) P) =
      eval₂ (Pi.evalRingHom (fun _ : X => K) xy.2) v P := by
  rw [eval₂_map]
  rfl

end PhilipponMultiplicity.HomogeneousNormalization
end
end


section

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ParameterLocalization
universe u v
variable {K : Type u} [Field K] {σ : Type v} [Fintype σ]

/-- Pad monomials in the pivot variable to homogenize an affine polynomial. -/
theorem exists_homogeneous_chart_lift (P : MvPolynomial σ K) (d : ℕ) (c : σ)
    (hbound : ∀ m ∈ P.support, (∑ j, m j) ≤ d) :
    ∃ Q : MvPolynomial σ K,
      (∀ m ∈ Q.support, (∑ j, m j) = d) ∧
      ∀ v : σ → K, v c = 1 → eval v Q = eval v P := by
  classical
  let e (m : σ →₀ ℕ) := m + Finsupp.single c (d - ∑ j, m j)
  refine ⟨∑ m ∈ P.support, monomial (e m) (P.coeff m), ?_, ?_⟩
  · intro n hn
    obtain ⟨m, hm, hnm⟩ := Finset.mem_biUnion.mp (support_sum hn)
    have hne : n = e m := Finset.mem_singleton.mp (support_monomial_subset hnm)
    rw [hne]
    simp only [e, Finsupp.add_apply, Finset.sum_add_distrib]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact Nat.add_sub_of_le (hbound m hm)
  · intro v hv
    rw [map_sum]
    calc
      (∑ m ∈ P.support, eval v (monomial (e m) (P.coeff m))) =
          ∑ m ∈ P.support, eval v (monomial m (P.coeff m)) := by
        apply Finset.sum_congr rfl
        intro m hm
        have he : monomial (e m) (P.coeff m) =
            monomial m (P.coeff m) * X c ^ (d - ∑ j, m j) := by
          simp [e, X_pow_eq_monomial, monomial_mul]
        rw [he]
        simp [hv]
      _ = eval v P := by rw [← map_sum, support_sum_monomial_coeff]

/-- Numerator and denominator can be homogenized to the same degree. -/
theorem exists_homogeneous_fraction (A B : MvPolynomial σ K) (c : σ) :
    ∃ (d : ℕ) (A' B' : MvPolynomial σ K),
      (∀ m ∈ A'.support, (∑ j, m j) = d) ∧
      (∀ m ∈ B'.support, (∑ j, m j) = d) ∧
      ∀ v : σ → K, v c ≠ 0 → eval (fun j => v j / v c) B ≠ 0 →
        eval v B' ≠ 0 ∧
          eval (fun j => v j / v c) A / eval (fun j => v j / v c) B =
            eval v A' / eval v B' := by
  classical
  let d := (∑ m ∈ A.support, ∑ j, m j) + (∑ m ∈ B.support, ∑ j, m j)
  have hA : ∀ m ∈ A.support, (∑ j, m j) ≤ d := by
    intro m hm
    exact (Finset.single_le_sum (fun a _ => Nat.zero_le (∑ j, a j)) hm).trans
      (Nat.le_add_right _ _)
  have hB : ∀ m ∈ B.support, (∑ j, m j) ≤ d := by
    intro m hm
    exact (Finset.single_le_sum (fun a _ => Nat.zero_le (∑ j, a j)) hm).trans
      (Nat.le_add_left _ _)
  obtain ⟨A', hA', eA⟩ := exists_homogeneous_chart_lift A d c hA
  obtain ⟨B', hB', eB⟩ := exists_homogeneous_chart_lift B d c hB
  refine ⟨d, A', B', hA', hB', ?_⟩
  intro v hc hden
  have hnorm : (fun j => v j / v c) c = 1 := div_self hc
  have hcoords : (fun j => v c * (v j / v c)) = v := by
    funext j
    exact mul_div_cancel₀ (v j) hc
  have hsA := HomogeneousNormalization.eval₂_scale (RingHom.id K) A' d hA'
    (fun j => v j / v c) (v c)
  have hsB := HomogeneousNormalization.eval₂_scale (RingHom.id K) B' d hB'
    (fun j => v j / v c) (v c)
  change eval _ A' = v c ^ d * eval (fun j => v j / v c) A' at hsA
  change eval _ B' = v c ^ d * eval (fun j => v j / v c) B' at hsB
  rw [hcoords, eA (fun j => v j / v c) hnorm] at hsA
  rw [hcoords, eB (fun j => v j / v c) hnorm] at hsB
  have hpow : v c ^ d ≠ 0 := pow_ne_zero _ hc
  rw [hsA, hsB]
  exact ⟨mul_ne_zero hpow hden, (mul_div_mul_left _ _ hpow).symm⟩

end PhilipponMultiplicity.ParameterLocalization

namespace PhilipponMultiplicity.ParameterChart
universe u
variable {K : Type u} [Field K] (F : EmbeddedCommutativeGroup K)

/-- Every localized coefficient has one polynomial-over-power presentation. -/
theorem exists_fraction (c : Fin (F.ambientDimension + 1)) (H : PolynomialRing F)
    (a : LocalRing F c H) :
    ∃ (A : PolynomialRing F) (n : ℕ), ∀ (y : F.Point) (hy : Valid F c H y),
      specialize F c H y hy a =
        MvPolynomial.eval (coordinates F c y) A /
          MvPolynomial.eval (coordinates F c y) (H ^ n) := by
  obtain ⟨n, b, hab⟩ := IsLocalization.Away.surj
    (Ideal.Quotient.mk (ideal F c) H) a
  obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨A, n, ?_⟩
  intro y hy
  apply (eq_div_iff (by simpa using pow_ne_zero n hy.2)).mpr
  have h := congrArg (specialize F c H y hy) hab
  have heval (Q : PolynomialRing F) :
      specialize F c H y hy (algebraMap (CoordinateRing F c) (LocalRing F c H)
        (Ideal.Quotient.mk (ideal F c) Q)) = MvPolynomial.eval (coordinates F c y) Q := by
    rw [specialize, IsLocalization.Away.lift_eq]
    rfl
  simpa only [map_mul, map_pow, heval] using h

/-- Localized coefficients specialize to homogeneous fractions in raw projective coordinates. -/
theorem exists_homogeneous_fraction (c : Fin (F.ambientDimension + 1))
    (H : PolynomialRing F) (a : LocalRing F c H) :
    ∃ (d : ℕ) (A B : PolynomialRing F),
      (∀ m ∈ A.support, (∑ j, m j) = d) ∧
      (∀ m ∈ B.support, (∑ j, m j) = d) ∧
      ∀ (y : F.Point) (hy : Valid F c H y),
        MvPolynomial.eval y.val.rep B ≠ 0 ∧
          specialize F c H y hy a =
            MvPolynomial.eval y.val.rep A / MvPolynomial.eval y.val.rep B := by
  obtain ⟨A, n, ha⟩ := exists_fraction F c H a
  obtain ⟨d, A', B', hA', hB', hfrac⟩ :=
    ParameterLocalization.exists_homogeneous_fraction A (H ^ n) c
  refine ⟨d, A', B', hA', hB', ?_⟩
  intro y hy
  have hn : MvPolynomial.eval (coordinates F c y) (H ^ n) ≠ 0 := by
    simpa only [map_pow] using pow_ne_zero n hy.2
  have hf := hfrac y.val.rep hy.1 hn
  exact ⟨hf.1, (ha y hy).trans hf.2⟩

/-- Use a fixed valid point off the chart, retaining a ring homomorphism to all functions. -/
def functionHom (c : Fin (F.ambientDimension + 1)) (H : PolynomialRing F)
    (y₀ : F.Point) (hy₀ : Valid F c H y₀) : LocalRing F c H →+* (F.Point → K) := by
  classical
  exact RingHom.pi (fun y => if hy : Valid F c H y then specialize F c H y hy
    else specialize F c H y₀ hy₀)

@[simp] theorem functionHom_apply (c : Fin (F.ambientDimension + 1))
    (H : PolynomialRing F) (y₀ : F.Point) (hy₀ : Valid F c H y₀)
    (a : LocalRing F c H) (y : F.Point) (hy : Valid F c H y) :
    functionHom F c H y₀ hy₀ a y = specialize F c H y hy a := by
  simp [functionHom, hy]

end PhilipponMultiplicity.ParameterChart
end
end


section
set_option autoImplicit false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section
namespace PhilipponMultiplicity

theorem homogeneous_families_of_localized_parameters
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (hgeometry : ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ (c : Fin (F.ambientDimension+1)) (H : ParameterChart.PolynomialRing F)
            (hvalid : ∀ xy ∈ U, ParameterChart.Valid F c H xy.2),
          ∃ P : Fin (F.ambientDimension+1) →
              MvPolynomial (Fin (F.ambientDimension+1)) (ParameterChart.LocalRing F c H),
          (∀ t, ∀ m ∈ (P t).support, (∑ j, m j) = 2) ∧
          ∀ (xy : F.Point × F.Point) (hxy : xy ∈ U),
            ∃ h : (fun t => MvPolynomial.eval₂
                (ParameterChart.specialize F c H xy.2 (hvalid xy hxy)) xy.1.val.rep (P t)) ≠ 0,
              Projectivization.mk K (fun t => MvPolynomial.eval₂
                (ParameterChart.specialize F c H xy.2 (hvalid xy hxy)) xy.1.val.rep (P t)) h =
                  (xy.1+xy.2).val) :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ P : Fin (F.ambientDimension+1) →
              MvPolynomial (Fin (F.ambientDimension+1)) (F.Point → K),
          (∀ t, ∀ m ∈ (P t).support, (∑ j, m j) = 2) ∧
          (∀ t, ∀ m ∈ (P t).support, ∀ xy ∈ U,
            ∃ V : Set (F.Point × F.Point),
              @IsOpen _ (TopologicalSpace.induced (fun zw => F.additionPair zw.1 zw.2)
                (projectiveSquare K F.ambientDimension).zariskiTopology) V ∧ xy ∈ V ∧
              ∃ (d : ℕ) (A B : MvPolynomial (Fin (F.ambientDimension+1)) K),
                (∀ a ∈ A.support, (∑ j, a j) = d) ∧
                (∀ a ∈ B.support, (∑ j, a j) = d) ∧
                ∀ zw ∈ U ∩ V,
                  MvPolynomial.eval zw.2.val.rep B ≠ 0 ∧
                    (P t).coeff m zw.2 = MvPolynomial.eval zw.2.val.rep A /
                      MvPolynomial.eval zw.2.val.rep B) ∧
          ∀ xy ∈ U,
            ∃ h : (fun t => MvPolynomial.eval₂
                (Pi.evalRingHom (fun _ : F.Point => K) xy.2) xy.1.val.rep (P t)) ≠ 0,
              Projectivization.mk K (fun t => MvPolynomial.eval₂
                (Pi.evalRingHom (fun _ : F.Point => K) xy.2) xy.1.val.rep (P t)) h =
                  (xy.1+xy.2).val := by
  classical
  intro E hE
  obtain ⟨F, hF, hfamily⟩ := hgeometry E hE
  refine ⟨F, hF, ?_⟩
  intro x y
  letI : TopologicalSpace (F.Point × F.Point) :=
    TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
      (projectiveSquare K F.ambientDimension).zariskiTopology
  obtain ⟨U, hU, hxyU, c, H, hvalid, P, hP, hrep⟩ := hfamily x y
  let φ := ParameterChart.functionHom F c H y (hvalid (x,y) hxyU)
  let Q := fun t => map φ (P t)
  refine ⟨U, hU, hxyU, Q, ?_, ?_, ?_⟩
  · intro t m hm
    exact hP t m (support_map_subset _ _ hm)
  · intro t m hm xy hxy
    obtain ⟨d, A, B, hA, hB, hfrac⟩ :=
      ParameterChart.exists_homogeneous_fraction F c H ((P t).coeff m)
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, d, A, B, hA, hB, ?_⟩
    intro zw hzw
    obtain ⟨hden, heq⟩ := hfrac zw.2 (hvalid zw hzw.1)
    refine ⟨hden, ?_⟩
    change (map φ (P t)).coeff m zw.2 = _
    rw [coeff_map]
    exact (ParameterChart.functionHom_apply F c H y (hvalid (x,y) hxyU)
      ((P t).coeff m) zw.2 (hvalid zw hzw.1)).trans heq
  · intro xy hxy
    obtain ⟨hn, heq⟩ := hrep xy hxy
    have hφ : (Pi.evalRingHom (fun _ : F.Point => K) xy.2).comp φ =
        ParameterChart.specialize F c H xy.2 (hvalid xy hxy) := by
      ext a
      exact ParameterChart.functionHom_apply F c H y (hvalid (x,y) hxyU)
        a xy.2 (hvalid xy hxy)
    have heval : (fun t => eval₂ (Pi.evalRingHom (fun _ : F.Point => K) xy.2)
        xy.1.val.rep (Q t)) = (fun t => eval₂
          (ParameterChart.specialize F c H xy.2 (hvalid xy hxy)) xy.1.val.rep (P t)) := by
      funext t
      change eval₂ _ _ (map φ (P t)) = _
      rw [eval₂_map, hφ]
    rw [heval]
    exact ⟨hn, heq⟩

end PhilipponMultiplicity
end
end

set_option autoImplicit false
open PhilipponMultiplicity
open scoped BigOperators Topology

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ P : Fin (F.ambientDimension+1) →
              MvPolynomial (Fin (F.ambientDimension+1)) (F.Point → K),
          (∀ t, ∀ m ∈ (P t).support, (∑ j, m j) = 2) ∧
          (∀ t, ∀ m ∈ (P t).support, ∀ xy ∈ U,
            ∃ V : Set (F.Point × F.Point),
              @IsOpen _ (TopologicalSpace.induced (fun zw => F.additionPair zw.1 zw.2)
                (projectiveSquare K F.ambientDimension).zariskiTopology) V ∧ xy ∈ V ∧
              ∃ (d : ℕ) (A B : MvPolynomial (Fin (F.ambientDimension+1)) K),
                (∀ a ∈ A.support, (∑ j, a j) = d) ∧
                (∀ a ∈ B.support, (∑ j, a j) = d) ∧
                ∀ zw ∈ U ∩ V,
                  MvPolynomial.eval zw.2.val.rep B ≠ 0 ∧
                    (P t).coeff m zw.2 = MvPolynomial.eval zw.2.val.rep A /
                      MvPolynomial.eval zw.2.val.rep B) ∧
          ∀ xy ∈ U,
            ∃ h : (fun t => MvPolynomial.eval₂
                (Pi.evalRingHom (fun _ : F.Point => K) xy.2) xy.1.val.rep (P t)) ≠ 0,
              Projectivization.mk K (fun t => MvPolynomial.eval₂
                (Pi.evalRingHom (fun _ : F.Point => K) xy.2) xy.1.val.rep (P t)) h =
                  (xy.1+xy.2).val := by
  exact homogeneous_families_of_localized_parameters K
    (exists_quadratic_localized_parameter_families K)
