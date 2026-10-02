-- Prove2me | solution 1 for PhilipponMultiplicity.addendum_converse
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T12:20:06.284952+00:00
-- url     : https://prove2.me/submissions/d013783a-c7cc-4ac8-927b-d5c31873b660
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_addendum_contact_hilbert_gap
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Analytic
set_option autoImplicit false
open scoped BigOperators


section

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


end PhilipponMultiplicity
end
end

section
set_option autoImplicit false
noncomputable section
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
end
end

section

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


end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

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


end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section

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


end PhilipponMultiplicity.OperatorSupport
end
end

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

namespace MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- A strict drop of quotient Hilbert functions supplies a homogeneous
equation in the second ideal which is not in the first. Neither ideal is
assumed homogeneous: only its intersection with the degree piece matters. -/
theorem exists_homogeneous_mem_not_mem_of_hilbertFunction_lt
    (I J : Ideal M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hgap : Hilbert.hilbertFunction K M.factorCount M.ambientDimension J D <
      Hilbert.hilbertFunction K M.factorCount M.ambientDimension I D) :
    ∃ P : M.CoordinateRing, M.IsHomogeneous P D ∧ P ∈ J ∧ P ∉ I := by
  classical
  let W := Hilbert.degreePiece K M.factorCount M.ambientDimension D
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict W
  let g := (Ideal.Quotient.mkₐ K J).toLinearMap.domRestrict W
  have hf : Module.finrank K (LinearMap.range f) =
      Hilbert.hilbertFunction K M.factorCount M.ambientDimension I D := by
    rw [LinearMap.range_domRestrict]
    rfl
  have hg : Module.finrank K (LinearMap.range g) =
      Hilbert.hilbertFunction K M.factorCount M.ambientDimension J D := by
    rw [LinearMap.range_domRestrict]
    rfl
  by_contra! h
  have hker : LinearMap.ker g ≤ LinearMap.ker f := by
    intro P hP
    change Ideal.Quotient.mk I P.val = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply h P.val ((M.degreePiece_iff _ _).mp P.property)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hP
  have hdim := Submodule.finrank_mono hker
  have hfdim := f.finrank_range_add_finrank_ker
  have hgdim := g.finrank_range_add_finrank_ker
  rw [hf] at hfdim
  rw [hg] at hgdim
  omega

end MultiProjectiveSpace

open OperatorSupport
variable {K : Type*} [NontriviallyNormedField K]
  {G : EmbeddedGroupProduct K}

/-- The ideal of all jets, through order T, along all points of the sampled
subgroup cosets. This uses the actual analytic lifts, with no chosen finite
set of test points or artificial finite-rank certificate. -/
def sampledContactIdeal [CompleteSpace K] (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (H : AlgebraicSubgroup G) (T : ℕ) :
    Ideal G.CoordinateRing :=
  ⨅ g : sample, ⨅ h : H.carrier, jetIdeal A (g.val + h.val) T

theorem mem_sampledContactIdeal_iff [CompleteSpace K] (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (H : AlgebraicSubgroup G) (T : ℕ)
    (P : G.CoordinateRing) :
    P ∈ sampledContactIdeal A sample H T ↔
      ∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h) := by
  simp only [sampledContactIdeal, Ideal.mem_iInf, mem_jetIdeal_iff]
  constructor
  · intro h g hg x hx
    exact ENat.natCast_add_one_le_iff.mpr (h ⟨g,hg⟩ ⟨x,hx⟩)
  · intro h g x
    exact ENat.natCast_add_one_le_iff.mp (h g.val g.property x.val x.property)

/-- The finite-dimensional interpolation step, separated from the numerical
Hilbert estimate. In particular the resulting polynomial is nonzero as a
section on the group, not just nonzero in the coordinate polynomial ring. -/
theorem converse_polynomial_of_contact_hilbert_gap
    (A : AnalyticSubgroup G) (sample : Finset G.Point) (H : AlgebraicSubgroup G)
    (T : ℕ) (D : G.FactorIndex → ℕ) (J : Ideal G.CoordinateRing)
    (hJ : ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
      (P ∈ J ↔ ∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h)))
    (hgap : Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension J D <
      Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) D) :
    ∃ P : G.CoordinateRing,
      P ≠ 0 ∧ IsMultihomogeneousOfDegree G P D ∧
      (∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h)) ∧
      (∃ x : G.Point, x ∉ zeroLocusOnGroup G P) := by
  obtain ⟨P,hP,hPJ,hPI⟩ := G.ambient.exists_homogeneous_mem_not_mem_of_hilbertFunction_lt
    (G.vanishingIdeal Set.univ) J D hgap
  refine ⟨P,fun hzero => hPI (hzero ▸ (G.vanishingIdeal Set.univ).zero_mem),
    hP,(hJ P hP).mp hPJ,?_⟩
  by_contra! hall
  apply hPI
  apply Ideal.subset_span
  refine ⟨⟨D,hP⟩,?_⟩
  rintro _ ⟨x,_,rfl⟩
  exact hall x

/-- All construction in the converse is proved here conditional on the
precise numerical comparison of the two actual quotient Hilbert functions. -/
theorem addendum_converse_of_contact_hilbert_gap
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgap : ∀ (G : EmbeddedGroupProduct K), 0 < G.dimension →
      ∀ (A : AnalyticSubgroup G) (sample : Finset G.Point), 0 ∈ sample →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ),
      (∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ)) →
      ∀ H : AlgebraicSubgroup G,
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ D →
      ∀ J : Ideal G.CoordinateRing,
      (∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
        (P ∈ J ↔ ∀ g ∈ sample, ∀ h ∈ H.carrier,
          ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h))) →
      Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension J D <
        Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
          (G.vanishingIdeal Set.univ) D)
    (G : EmbeddedGroupProduct K) (hn : 0 < G.dimension) (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (hsample : 0 ∈ sample) (T : ℕ) (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ))
    (H : AlgebraicSubgroup G)
    (hbound :
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ D) :
    ∃ P : G.CoordinateRing,
      P ≠ 0 ∧ IsMultihomogeneousOfDegree G P D ∧
      (∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h)) ∧
      (∃ x : G.Point, x ∉ zeroLocusOnGroup G P) := by
  let : CompleteSpace K := hK.completeSpace
  let J := sampledContactIdeal A sample H T
  have hJ : ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
      (P ∈ J ↔ ∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h)) :=
    fun P _ => mem_sampledContactIdeal_iff A sample H T P
  exact converse_polynomial_of_contact_hilbert_gap A sample H T D J hJ
    (hgap G hn A sample hsample T D hD H hbound J hJ)

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hn : 0 < G.dimension) (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (hsample : 0 ∈ sample) (T : ℕ) (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ))
    (H : AlgebraicSubgroup G)
    (hbound :
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ D) :
    ∃ P : G.CoordinateRing,
      P ≠ 0 ∧ IsMultihomogeneousOfDegree G P D ∧
      (∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h)) ∧
      (∃ x : G.Point, x ∉ zeroLocusOnGroup G P) := by
  exact addendum_converse_of_contact_hilbert_gap K hK
    (addendum_contact_hilbert_gap K hK) G hn A sample hsample T D hD H hbound
