-- Prove2me | solution 1 for PhilipponMultiplicity.exists_quadratic_localized_parameter_families
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-09T01:00:42.244983+00:00
-- url     : https://prove2.me/submissions/3ab310ee-ba69-428b-9bb1-0d3781ce0b0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_quadratic_parameter_stalk_germs
import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_ParameterChart
import Definitions.Def_PhilipponMultiplicity_ParameterStalk
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring


section
set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.FiniteStalkFractions
variable {R K ι : Type*} [CommRing R] [Field K] [Fintype ι] [DecidableEq ι]

def clearedNumerator (a s : ι → R) (i : ι) : R :=
  a i * ∏ j ∈ Finset.univ.erase i, s j

def coefficient (H : R) (a s : ι → R) (i : ι) : Localization.Away H :=
  algebraMap R (Localization.Away H) (clearedNumerator a s i) *
    IsLocalization.Away.invSelf H

theorem coefficient_relation (H : R) (a s : ι → R) (i : ι) :
    coefficient H a s i * algebraMap R (Localization.Away H) H =
      algebraMap R (Localization.Away H) (clearedNumerator a s i) := by
  simp [coefficient, mul_assoc, mul_comm (IsLocalization.Away.invSelf H)]

/-- Evaluation of a finite common-denominator lift agrees with each original fraction. -/
theorem coefficient_eval (H : R) (a s : ι → R) (hH : H = ∏ j, s j)
    (f : R →+* K) (e : Localization.Away H →+* K)
    (he : ∀ r, e (algebraMap R (Localization.Away H) r) = f r)
    (h : f H ≠ 0) (i : ι) :
    e (coefficient H a s i) = f (a i) / f (s i) := by
  have hs : f (s i) ≠ 0 := by
    have hp : (∏ j, f (s j)) ≠ 0 := by simpa [hH] using h
    exact Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ _)
  have hnum : f (clearedNumerator a s i) = (f (a i) / f (s i)) * f H := by
    simp only [clearedNumerator, map_mul, map_prod, hH]
    rw [← Finset.prod_erase_mul Finset.univ (fun j => f (s j)) (Finset.mem_univ i)]
    field_simp
  apply mul_right_cancel₀ h
  have hr := congrArg e (coefficient_relation H a s i)
  simpa only [map_mul, he, hnum] using hr

end PhilipponMultiplicity.FiniteStalkFractions
end

end


section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ParameterStalk
universe u
variable {K : Type u} [Field K] (F : EmbeddedCommutativeGroup K)
  (c : Fin (F.ambientDimension + 1)) (y : F.Point) (hy : y.val.rep c ≠ 0)

theorem denominator_at_point (a : Ring F c y hy) :
    ParameterChart.quotientEval F c y hy (denominator F c y hy a).val ≠ 0 :=
  (denominator F c y hy a).property

/-- One principal parameter localization represents all coefficients of a finite
family of stalk forms, preserving support degree and exact specialization. -/
theorem spread_forms {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial (Fin (F.ambientDimension + 1)) (Ring F c y hy))
    (d : ℕ) (hP : ∀ t, ∀ m ∈ (P t).support, ∑ j, m j = d) :
    ∃ H : ParameterChart.PolynomialRing F, ParameterChart.Valid F c H y ∧
      ∃ Q : ι → MvPolynomial (Fin (F.ambientDimension + 1)) (ParameterChart.LocalRing F c H),
        (∀ t, ∀ m ∈ (Q t).support, ∑ j, m j = d) ∧
        ∀ (z : F.Point) (hz : ParameterChart.Valid F c H z) (x : F.Point) (t : ι),
          eval₂ (ParameterChart.specialize F c H z hz) x.val.rep (Q t) =
            formValue F c y hy (P t) x z := by
  classical
  let J := Σ t : ι, (P t).support
  let a (i : J) := numerator F c y hy ((P i.1).coeff i.2.val)
  let s (i : J) := (denominator F c y hy ((P i.1).coeff i.2.val)).val
  obtain ⟨H, hH⟩ := Ideal.Quotient.mk_surjective (∏ i : J, s i)
  have hHy : ParameterChart.Valid F c H y := by
    refine ⟨hy, ?_⟩
    change ParameterChart.quotientEval F c y hy (Ideal.Quotient.mk (ParameterChart.ideal F c) H) ≠ 0
    rw [hH, map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => denominator_at_point F c y hy _)
  let Q (t : ι) : MvPolynomial (Fin (F.ambientDimension + 1)) (ParameterChart.LocalRing F c H) :=
    ∑ m : (P t).support, monomial m.val
      (FiniteStalkFractions.coefficient (Ideal.Quotient.mk (ParameterChart.ideal F c) H)
        a s ⟨t, m⟩)
  refine ⟨H, hHy, Q, ?_, ?_⟩
  · intro t m hm
    obtain ⟨v, _, hmv⟩ := Finset.mem_biUnion.mp (support_sum hm)
    have he : m = v.val := Finset.mem_singleton.mp (support_monomial_subset hmv)
    exact he ▸ hP t v.val v.property
  · intro z hz x t
    have hev (r : ParameterChart.CoordinateRing F c) :
        ParameterChart.specialize F c H z hz
          (algebraMap (ParameterChart.CoordinateRing F c) (ParameterChart.LocalRing F c H) r) =
          ParameterChart.quotientEval F c z hz.1 r := by
      exact IsLocalization.Away.lift_eq _ _ _
    have hc (m : (P t).support) :
        ParameterChart.specialize F c H z hz
          (FiniteStalkFractions.coefficient (Ideal.Quotient.mk (ParameterChart.ideal F c) H)
            a s ⟨t, m⟩) = value F c y hy ((P t).coeff m.val) z := by
      rw [value, dif_pos hz.1]
      exact FiniteStalkFractions.coefficient_eval _ a s hH
        (ParameterChart.quotientEval F c z hz.1) (ParameterChart.specialize F c H z hz)
        hev hz.2 ⟨t, m⟩
    simp only [Q, eval₂_sum, eval₂_monomial, hc, formValue]
    exact Finset.sum_attach (P t).support
      (fun m => value F c y hy ((P t).coeff m) z * m.prod (fun j n => x.val.rep j ^ n))

end PhilipponMultiplicity.ParameterStalk
end

end


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
namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

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

/-- Every point of an induced multiprojective topology has a simultaneous pivot chart. -/
theorem exists_pivot_neighborhood {X : Type*} (e : X → M.Point) (x : X) :
    ∃ (c : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) (U : Set X),
      @IsOpen _ (TopologicalSpace.induced e M.zariskiTopology) U ∧ x ∈ U ∧
      ∀ z ∈ U, ∀ i, M.coordinate (e z) ⟨i,c i⟩ ≠ 0 := by
  classical
  letI := M.zariskiTopology
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  have hex (i : M.FactorIndex) : ∃ j, M.coordinate (e x) ⟨i,j⟩ ≠ 0 := by
    simpa only [coordinate, ne_eq, _root_.funext_iff, Pi.zero_apply, not_forall]
      using (e x i).rep_nonzero
  choose c hc using hex
  let U : Set X := ⋂ i, {z | M.coordinate (e z) ⟨i,c i⟩ ≠ 0}
  refine ⟨c, U, ?_, ?_, ?_⟩
  · apply isOpen_iInter_of_finite
    intro i
    have h := (M.isOpen_basic (MvPolynomial.X ⟨i,c i⟩) _
      (M.isHomogeneous_X ⟨i,c i⟩)).preimage (continuous_induced_dom (f := e))
    simpa only [Set.preimage_setOf_eq, eval, MvPolynomial.eval_X] using h
  · exact Set.mem_iInter.mpr hc
  · intro z hz i
    exact Set.mem_iInter.mp hz i

end PhilipponMultiplicity.MultiProjectiveSpace
end

end


section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K]

/-- Homogeneous equations in a single factor give opens in the multiprojective topology. -/
theorem isOpen_factor_form (M : MultiProjectiveSpace K) (b : M.FactorIndex)
    (P : MvPolynomial (Fin (M.ambientDimension b + 1)) K) (d : ℕ)
    (hP : ∀ m ∈ P.support, ∑ j, m j = d) :
    @IsOpen _ M.zariskiTopology {x : M.Point | MvPolynomial.eval (x b).rep P ≠ 0} := by
  classical
  let f : Fin (M.ambientDimension b + 1) → M.Variable := fun j => ⟨b,j⟩
  have hf : Function.Injective f := by
    intro j k h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hhom : M.IsHomogeneous (rename f P) (fun i => if i = b then d else 0) := by
    intro a ha i
    rw [support_rename_of_injective hf] at ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    by_cases hi : i = b
    · subst i
      simpa [f, Finsupp.mapDomain_apply hf] using hP m hm
    · simp only [if_neg hi]
      apply Finset.sum_eq_zero
      intro j _
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨k, hk⟩
      exact hi (congrArg Sigma.fst hk).symm
  have ho := M.isOpen_basic (rename f P) _ hhom
  simpa only [MultiProjectiveSpace.eval, eval_rename, Function.comp_def,
    MultiProjectiveSpace.coordinate, f] using ho

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.ParameterChart
variable {K : Type*} [Field K] (F : EmbeddedCommutativeGroup K)

/-- A principal normalized parameter chart is open for the actual pair topology. -/
theorem valid_pair_isOpen (c : Fin (F.ambientDimension + 1)) (H : PolynomialRing F) :
    @IsOpen _ (TopologicalSpace.induced (fun xy : F.Point × F.Point =>
      F.additionPair xy.1 xy.2) (projectiveSquare K F.ambientDimension).zariskiTopology)
      {xy : F.Point × F.Point | Valid F c H xy.2} := by
  classical
  let M := projectiveSquare K F.ambientDimension
  let := M.zariskiTopology
  let : TopologicalSpace (F.Point × F.Point) :=
    TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2) M.zariskiTopology
  have hopen (P : PolynomialRing F) (d : ℕ)
      (hP : ∀ m ∈ P.support, ∑ j, m j = d) :
      IsOpen {xy : F.Point × F.Point | eval xy.2.val.rep P ≠ 0} := by
    have ho := (M.isOpen_factor_form (1 : Fin 2) P d hP).preimage
      (continuous_induced_dom (f := fun xy : F.Point × F.Point => F.additionPair xy.1 xy.2))
    change IsOpen {xy : F.Point × F.Point | eval (F.additionPair xy.1 xy.2 (1 : Fin 2)).rep P ≠ 0} at ho
    simpa [EmbeddedCommutativeGroup.additionPair, projectiveSquare] using ho
  have hc : IsOpen {xy : F.Point × F.Point | xy.2.val.rep c ≠ 0} := by
    have hx : ∀ m ∈ (X c : PolynomialRing F).support, ∑ j, m j = 1 := by
      intro m hm
      simp only [support_X, Finset.mem_singleton] at hm
      subst m
      simp [Finsupp.single_apply]
    simpa only [eval_X] using hopen (X c) 1 hx
  let d := ∑ m ∈ H.support, ∑ j, m j
  have hbound : ∀ m ∈ H.support, ∑ j, m j ≤ d := by
    intro m hm
    exact Finset.single_le_sum (fun a _ => Nat.zero_le (∑ j, a j)) hm
  obtain ⟨Q, hQ, hQeval⟩ := ParameterLocalization.exists_homogeneous_chart_lift H d c hbound
  have heq : {xy : F.Point × F.Point | Valid F c H xy.2} =
      {xy | xy.2.val.rep c ≠ 0} ∩ {xy | eval xy.2.val.rep Q ≠ 0} := by
    ext xy
    by_cases hp : xy.2.val.rep c = 0
    · simp [Valid, hp]
    · have hn : (coordinates F c xy.2) c = 1 := div_self hp
      have hnorm := HomogeneousNormalization.eval₂_normalize (RingHom.id K) Q d hQ
        xy.2.val.rep c
      change eval (coordinates F c xy.2) Q =
        (xy.2.val.rep c)⁻¹ ^ d * eval xy.2.val.rep Q at hnorm
      rw [hQeval _ hn] at hnorm
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Valid]
      rw [hnorm]
      simp [hp]
  rw [heq]
  exact hc.inter (hopen Q d hQ)

end PhilipponMultiplicity.ParameterChart
end

end


section
set_option autoImplicit false
open scoped BigOperators Topology
noncomputable section
namespace PhilipponMultiplicity

theorem localized_families_of_stalk_germs
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (hgeometry : ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point,
          ∃ (c : Fin (F.ambientDimension + 1)) (hy : y.val.rep c ≠ 0),
          ∃ P : Fin (F.ambientDimension + 1) →
              MvPolynomial (Fin (F.ambientDimension + 1)) (ParameterStalk.Ring F c y hy),
            (∀ t, ∀ m ∈ (P t).support, ∑ j, m j = 2) ∧
            ∀ᶠ xy : F.Point × F.Point in
              @nhds _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
                (projectiveSquare K F.ambientDimension).zariskiTopology) (x,y),
              ∃ h : (fun t => ParameterStalk.formValue F c y hy (P t) xy.1 xy.2) ≠ 0,
                Projectivization.mk K (fun t => ParameterStalk.formValue F c y hy (P t) xy.1 xy.2) h =
                  (xy.1 + xy.2).val) :
    ∀ (E : EmbeddedCommutativeGroup K),
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
                  (xy.1+xy.2).val := by
  classical
  intro E hE
  obtain ⟨F, hEF, hF⟩ := hgeometry E hE
  refine ⟨F, hEF, ?_⟩
  intro x y
  obtain ⟨c, hy, P, hP, hrep⟩ := hF x y
  obtain ⟨H, hHy, Q, hQ, heval⟩ := ParameterStalk.spread_forms F c y hy P 2 hP
  letI : TopologicalSpace (F.Point × F.Point) :=
    TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
      (projectiveSquare K F.ambientDimension).zariskiTopology
  obtain ⟨U, hUsub, hUopen, hxy⟩ := mem_nhds_iff.mp hrep
  refine ⟨U ∩ {xy : F.Point × F.Point | ParameterChart.Valid F c H xy.2},
    hUopen.inter (ParameterChart.valid_pair_isOpen F c H), ⟨hxy, hHy⟩,
    c, H, (fun xy hxy => hxy.2), Q, hQ, ?_⟩
  intro xy hxy
  have heq : (fun t => MvPolynomial.eval₂ (ParameterChart.specialize F c H xy.2 hxy.2)
      xy.1.val.rep (Q t)) = (fun t => ParameterStalk.formValue F c y hy (P t) xy.1 xy.2) :=
    funext (heval xy.2 hxy.2 xy.1)
  obtain ⟨hne, he⟩ := hUsub hxy.1
  have hnQ : (fun t => MvPolynomial.eval₂ (ParameterChart.specialize F c H xy.2 hxy.2)
      xy.1.val.rep (Q t)) ≠ 0 := by
    rw [heq]
    exact hne
  refine ⟨hnQ, ?_⟩
  simpa only [heq] using he

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
                  (xy.1+xy.2).val := by
  exact localized_families_of_stalk_germs K
    (exists_quadratic_parameter_stalk_germs K)
