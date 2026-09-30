-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.exists_bounded_homogeneous_avoiding
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T02:41:43.729054+00:00
-- url     : https://prove2.me/submissions/51970686-bd16-4b70-86e7-f6b63c4d7191

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

-- Reused from Solutions/PhilipponPointHilbert.lean

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
noncomputable section
namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem relevant_variables (Q : Ideal M.CoordinateRing)
    (hQ : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ v : ∀ i, Fin (M.ambientDimension i + 1), ∀ i, X ⟨i, v i⟩ ∉ Q := by
  classical
  have hx (i : M.FactorIndex) : ∃ j : Fin (M.ambientDimension i + 1), X ⟨i, j⟩ ∉ Q := by
    by_contra! h
    apply hQ
    apply (iInf_le (blockIdeal K M.factorCount M.ambientDimension) i).trans
    rw [blockIdeal, Ideal.span_le]
    rintro x ⟨j, rfl⟩
    exact h j
  exact Classical.axiomOfChoice hx

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

theorem variable_product_notMem (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (v : ∀ i, Fin (M.ambientDimension i + 1)) (hv : ∀ i, X ⟨i, v i⟩ ∉ Q)
    (d : M.FactorIndex → ℕ) : (∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i) ∉ Q := by
  classical
  letI := hQ
  intro h
  obtain ⟨i, hi, hip⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hv i (hQ.mem_of_pow_mem _ hip)


end PhilipponMultiplicity.Hilbert
end

-- Reused from Solutions/PhilipponBoundedAvoidance.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree
variable {K : Type*} [Field K] [Infinite K] (M : MultiProjectiveSpace K)

/-- The equation-selection step on p. 367: bounded generators yield one
equation of the exact requested multidegree avoiding every selected relevant prime. -/
theorem exists_bounded_homogeneous_avoiding {ι : Type*} [Finite ι]
    (I₀ : Ideal M.CoordinateRing) (m : ℕ) (P : Fin m → M.CoordinateRing)
    (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (q : ι → Ideal M.CoordinateRing) (hq : ∀ i, (q i).IsPrime)
    (hrel : ∀ i, Hilbert.IsRelevant K M.factorCount M.ambientDimension (q i))
    (hI₀ : ∀ i, I₀ ≤ q i)
    (havoid : ∀ i, ¬ I₀ ⊔ Ideal.span (Set.range P) ≤ q i) :
    ∃ f : M.CoordinateRing, f ∈ Ideal.span (Set.range P) ∧
      M.IsHomogeneous f D ∧ ∀ i, f ∉ q i := by
  classical
  let W : Submodule K M.CoordinateRing :=
    Hilbert.degreePiece K M.factorCount M.ambientDimension D ⊓
      (Ideal.span (Set.range P)).restrictScalars K
  let V : ι → Submodule K W := fun i => ((q i).restrictScalars K).comap W.subtype
  have hproper : ∀ i, V i ≠ ⊤ := by
    intro i htop
    have hj : ∃ j, P j ∉ q i := by
      by_contra! hh
      apply havoid i
      refine sup_le (hI₀ i) (Ideal.span_le.mpr ?_)
      rintro f ⟨j, rfl⟩
      exact hh j
    obtain ⟨j, hj⟩ := hj
    obtain ⟨E, heD, hE⟩ := hP j
    obtain ⟨v, hv⟩ := Hilbert.relevant_variables M (q i) (hrel i)
    let B : M.CoordinateRing := ∏ k, (X ⟨k, v k⟩ : M.CoordinateRing) ^ (D k - E k)
    have hB := Hilbert.variable_product_homogeneous M v (fun k => D k - E k)
    have hBout := Hilbert.variable_product_notMem M (q i) (hq i) v hv
      (fun k => D k - E k)
    have hdeg : E + (fun k => D k - E k) = D := by
      funext k
      have := heD k
      simp only [Pi.add_apply]
      omega
    have hfhom : M.IsHomogeneous (P j * B) D := by
      rw [← hdeg]
      exact (M.degreePiece_iff _ _).mp
        (hE.mul ((M.degreePiece_iff _ _).mpr hB))
    have hfspan : P j * B ∈ Ideal.span (Set.range P) :=
      (Ideal.span (Set.range P)).mul_mem_right B (Ideal.subset_span (Set.mem_range_self j))
    let f : W := ⟨P j * B, (M.degreePiece_iff _ _).mpr hfhom, hfspan⟩
    have hfmem : f ∈ V i := htop.symm ▸ Submodule.mem_top
    have hmem : P j * B ∈ q i := hfmem
    exact ((hq i).mem_or_mem hmem).elim hj hBout
  have hnot : (⋃ i, (V i : Set W)) ≠ Set.univ := by
    intro h
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ h
    exact hproper i hi
  obtain ⟨f, hf⟩ := (Set.ne_univ_iff_exists_notMem _).mp hnot
  refine ⟨f.1, f.2.2, (M.degreePiece_iff _ _).mp f.2.1, ?_⟩
  intro i hi
  exact hf (Set.mem_iUnion.mpr ⟨i, hi⟩)

end PhilipponMultiplicity.SectionThreeSupport

end

theorem solution
    {K : Type*} [Field K] [Infinite K] (M : MultiProjectiveSpace K) {ι : Type*} [Finite ι]
    (I₀ : Ideal M.CoordinateRing) (m : ℕ) (P : Fin m → M.CoordinateRing)
    (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D)
    (q : ι → Ideal M.CoordinateRing) (hq : ∀ i, (q i).IsPrime)
    (hrel : ∀ i, Hilbert.IsRelevant K M.factorCount M.ambientDimension (q i))
    (hI₀ : ∀ i, I₀ ≤ q i)
    (havoid : ∀ i, ¬ I₀ ⊔ Ideal.span (Set.range P) ≤ q i) :
    ∃ f : M.CoordinateRing, f ∈ Ideal.span (Set.range P) ∧
      M.IsHomogeneous f D ∧ ∀ i, f ∉ q i := by
  exact PhilipponMultiplicity.SectionThreeSupport.exists_bounded_homogeneous_avoiding M I₀ m P D hP q hq hrel hI₀ havoid
