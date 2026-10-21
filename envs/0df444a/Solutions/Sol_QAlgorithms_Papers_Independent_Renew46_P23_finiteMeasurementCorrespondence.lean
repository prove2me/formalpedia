-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P23.finiteMeasurementCorrespondence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:42:09.243564+00:00
-- url     : https://prove2.me/submissions/3b03715e-0025-4e50-96db-5a2b290f759d

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P23
noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Renew46.P23

open QAlgorithms.Papers.Independent.Next46.P43
  (SufficientSigmaAlgebra MinimalSufficientSigmaAlgebra IsCStarCoarseGraining)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (relativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

local instance : MeasurableSpace Bool := ⊤

lemma g64m_entry00 {N : Type*} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
    (Y : CStarMatrix (Fin 2) (Fin 2) N) (hY : 0 ≤ Y) : 0 ≤ Y 0 0 := by
  rw [StarOrderedRing.nonneg_iff] at hY
  induction hY using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    show 0 ≤ (star b * b) 0 0
    rw [CStarMatrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => by rw [CStarMatrix.star_apply]; exact star_mul_self_nonneg _)
  | zero => exact le_rfl
  | add x y _ _ hx hy => exact add_nonneg hx hy

lemma g64m_csum_apply' {A ι : Type*} [AddCommMonoid A] (s : Finset ι)
    (f : ι → CStarMatrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (∑ p ∈ s, f p) i j = ∑ p ∈ s, f p i j :=
  Matrix.sum_apply i j s f

lemma g64m_map_nonneg {M N : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N] (σ : M →ₗ[ℂ] N)
    (hgen : ∀ b : CStarMatrix (Fin 2) (Fin 2) M, 0 ≤ (star b * b).map σ)
    (Y : CStarMatrix (Fin 2) (Fin 2) M) (hY : 0 ≤ Y) : 0 ≤ Y.map σ := by
  rw [StarOrderedRing.nonneg_iff] at hY
  induction hY using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact hgen b
  | zero =>
    have : (0 : CStarMatrix (Fin 2) (Fin 2) M).map σ = 0 := CStarMatrix.ext (fun i j => by
      simp [CStarMatrix.map_apply, CStarMatrix.zero_apply])
    rw [this]
  | add x y _ _ hx hy =>
    have : (x + y).map σ = x.map σ + y.map σ :=
      CStarMatrix.ext (fun i j => by simp [CStarMatrix.map_apply])
    rw [this]
    exact add_nonneg hx hy

lemma g64m_pos {X N : Type*} [Fintype X] [DecidableEq X] [CStarAlgebra N] [PartialOrder N]
    [StarOrderedRing N] (σ : (X → ℂ) →ₗ[ℂ] N)
    (hσ : ∀ Y : CStarMatrix (Fin 2) (Fin 2) (X → ℂ), 0 ≤ Y → 0 ≤ Y.map σ) (x : X) :
    0 ≤ σ (fun y => if y = x then 1 else 0) := by
  set d : X → ℂ := fun y => if y = x then 1 else 0 with hd
  set C : CStarMatrix (Fin 2) (Fin 2) (X → ℂ) :=
    (fun i j => if i = 0 ∧ j = 0 then d else 0) with hC
  have h1 : 0 ≤ star C * C := star_mul_self_nonneg C
  have h2 := g64m_entry00 _ (hσ _ h1)
  have h3 : (star C * C) 0 0 = d := by
    rw [CStarMatrix.mul_apply, Fin.sum_univ_two]
    rw [CStarMatrix.star_apply, CStarMatrix.star_apply]
    simp only [hC]
    funext y
    by_cases hy : y = x <;> simp [hd, hy]
  rw [CStarMatrix.map_apply, h3] at h2
  exact h2

lemma g64m_decomp {X : Type*} [Fintype X] [DecidableEq X] (f : X → ℂ) :
    f = ∑ x, f x • (fun y => if y = x then (1 : ℂ) else 0) := by
  funext y
  simp [Finset.sum_apply]

theorem solution
    {X N : Type*} [Fintype X] [Nonempty X] [CStarAlgebra N]
    [PartialOrder N] [StarOrderedRing N] (E : X → N) :
    (((∀ x, 0 ≤ E x) ∧ (∑ x, E x) = 1) ↔
      IsCStarCoarseGraining (measurementMap E)) ∧
    (∀ sigma : (X → ℂ) →ₗ[ℂ] N, IsCStarCoarseGraining sigma →
      (∀ x, 0 ≤ sigma (fun y => if y = x then 1 else 0)) ∧
      (∑ x, sigma (fun y => if y = x then 1 else 0)) = 1 ∧
      sigma = measurementMap (fun x => sigma (fun y => if y = x then 1 else 0))) := by
  have hrep : ∀ sigma : (X → ℂ) →ₗ[ℂ] N,
      sigma = measurementMap (fun x => sigma (fun y => if y = x then 1 else 0)) := by
    intro sigma
    refine LinearMap.ext (fun f => ?_)
    conv_lhs => rw [g64m_decomp f]
    rw [map_sum]
    simp only [map_smul]
    rfl
  have hsum : ∀ sigma : (X → ℂ) →ₗ[ℂ] N, sigma 1 = 1 →
      (∑ x, sigma (fun y => if y = x then 1 else 0)) = 1 := by
    intro sigma h1
    rw [← map_sum]
    convert h1
    funext y
    simp [Finset.sum_apply]
  have back : ∀ sigma : (X → ℂ) →ₗ[ℂ] N, IsCStarCoarseGraining sigma →
      (∀ x, 0 ≤ sigma (fun y => if y = x then 1 else 0)) ∧
      (∑ x, sigma (fun y => if y = x then 1 else 0)) = 1 ∧
      sigma = measurementMap (fun x => sigma (fun y => if y = x then 1 else 0)) :=
    fun sigma h => ⟨g64m_pos sigma h.2, hsum sigma h.1, hrep sigma⟩
  refine ⟨⟨?_, ?_⟩, back⟩
  · rintro ⟨hE, hE1⟩
    refine ⟨?_, ?_⟩
    · show ∑ x, (1 : X → ℂ) x • E x = 1
      simpa using hE1
    · apply g64m_map_nonneg
      intro b
      have he : ∀ x, ∃ e : N, E x = star e * e :=
        fun x => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hE x)
      choose e he using he
      set R : X → CStarMatrix (Fin 2) (Fin 2) N := fun y =>
        (fun l j => b l j y • e y) with hR
      have key : (star b * b).map (measurementMap E) = ∑ y, star (R y) * R y := by
        refine CStarMatrix.ext (fun i j => ?_)
        rw [CStarMatrix.map_apply, g64m_csum_apply', CStarMatrix.mul_apply]
        show ∑ y, (∑ l, star b i l * b l j) y • E y = _
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [CStarMatrix.mul_apply, Finset.sum_apply, Finset.sum_smul]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [CStarMatrix.star_apply, CStarMatrix.star_apply, he y]
        simp only [hR, Pi.mul_apply, Pi.star_apply, star_smul, smul_mul_smul_comm, mul_smul]
      rw [key]
      exact Finset.sum_nonneg (fun y _ => star_mul_self_nonneg _)
  · intro h
    have h' := back _ h
    refine ⟨fun x => ?_, ?_⟩
    · have := h'.1 x
      simpa [measurementMap] using this
    · have := h'.2.1
      simpa [measurementMap] using this
