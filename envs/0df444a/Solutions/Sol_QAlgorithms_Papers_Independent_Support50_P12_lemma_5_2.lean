-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:30:27.965992+00:00
-- url     : https://prove2.me/submissions/249261cc-fd74-4b3d-b5c3-9802460cd6d4

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50 QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

open Polynomial in
theorem X7M3_cauchy_ker {L : Type} [Fintype L] (x t : L → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hxi : Function.Injective x)
    (ht : ∀ i, 0 < t i) (hti : Function.Injective t) (c : L → ℂ)
    (hc : ∀ i, ∑ j, c j / ((x i + t j : ℝ) : ℂ) = 0) : c = 0 := by
  classical
  have hne : ∀ i j, ((x i + t j : ℝ) : ℂ) ≠ 0 := by
    intro i j
    have : 0 < x i + t j := by linarith [hx i, ht j]
    exact_mod_cast this.ne'
  funext j
  set P : ℂ[X] := ∑ l, C (c l) * ∏ k ∈ Finset.univ.erase l, (X + C ((t k : ℝ) : ℂ)) with hP
  have hdeg : P.natDegree < Fintype.card L := by
    have hpos : 0 < Fintype.card L := Fintype.card_pos_iff.mpr ⟨j⟩
    have : P.natDegree ≤ Fintype.card L - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro l _
      refine (natDegree_C_mul_le _ _).trans ?_
      refine (natDegree_prod_le _ _).trans ?_
      simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  have heval : ∀ i, P.eval ((x i : ℝ) : ℂ) = 0 := by
    intro i
    have hprod : ∀ l, (∏ k ∈ Finset.univ.erase l, (((x i : ℝ) : ℂ) + ((t k : ℝ) : ℂ))) =
        (∏ k, (((x i + t k : ℝ)) : ℂ)) / ((x i + t l : ℝ) : ℂ) := by
      intro l
      rw [eq_div_iff (hne i l), ← Finset.prod_erase_mul _ _ (Finset.mem_univ l)]
      push_cast; ring
    simp only [hP, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X]
    simp_rw [hprod]
    have := hc i
    calc ∑ l, c l * ((∏ k, (((x i + t k : ℝ)) : ℂ)) / ((x i + t l : ℝ) : ℂ))
        = (∏ k, (((x i + t k : ℝ)) : ℂ)) * ∑ l, c l / ((x i + t l : ℝ) : ℂ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have hinj : Function.Injective (fun i => ((x i : ℝ) : ℂ)) := by
    intro a b h; exact hxi (Complex.ofReal_injective h)
  have hP0 : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hinj heval hdeg
  have h1 : P.eval (-((t j : ℝ) : ℂ)) =
      c j * ∏ k ∈ Finset.univ.erase j, (-((t j : ℝ) : ℂ) + ((t k : ℝ) : ℂ)) := by
    simp only [hP, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X]
    rw [Finset.sum_eq_single j]
    · intro l _ hl
      rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨Ne.symm hl, Finset.mem_univ _⟩)
        (by ring), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hP0, eval_zero] at h1
  have h2 : ∏ k ∈ Finset.univ.erase j, (-((t j : ℝ) : ℂ) + ((t k : ℝ) : ℂ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk h
    have hk' : k ≠ j := (Finset.mem_erase.mp hk).1
    apply hk'; apply hti
    have : ((t k : ℝ) : ℂ) = ((t j : ℝ) : ℂ) := by linear_combination h
    exact_mod_cast this
  simpa [h2] using h1.symm

/-- Lemma 5.2, PDF p.25: injective interpolation points, distinct positive poles;
the empty index set yields the empty identity. -/
theorem solution {L : Type} [Fintype L] (x t : L → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hxi : Function.Injective x)
    (ht : ∀ i, 0 < t i) (hti : Function.Injective t) (f : ℝ → ℂ) :
    ∃ c : L → ℂ, ∀ i, f (x i) = ∑ j, c j / ((x i + t j : ℝ) : ℂ) := by
  classical
  set M : Matrix L L ℂ := Matrix.of fun i j => (((x i + t j : ℝ) : ℂ))⁻¹ with hM
  have hinj : Function.Injective M.mulVec := by
    intro a b hab
    have := X7M3_cauchy_ker x t hx hxi ht hti (a - b) (by
      intro i
      have h := congrFun hab i
      simp only [hM, Matrix.mulVec, dotProduct, Matrix.of_apply] at h
      have h2 : ∑ j, (a - b) j / ((x i + t j : ℝ) : ℂ) =
          ∑ j, (((x i + t j : ℝ) : ℂ))⁻¹ * a j - ∑ j, (((x i + t j : ℝ) : ℂ))⁻¹ * b j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply]; ring
      rw [h2, h, sub_self])
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨c, hc⟩ := hsurj (fun i => f (x i))
  refine ⟨c, fun i => ?_⟩
  have h := congrFun hc i
  simp only [hM, Matrix.mulVec, dotProduct, Matrix.of_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => by rw [div_eq_mul_inv, mul_comm]


end

