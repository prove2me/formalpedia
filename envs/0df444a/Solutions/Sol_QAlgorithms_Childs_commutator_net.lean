-- Prove2me | solution 1 for QAlgorithms.Childs.commutator_net
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T19:59:20.537143+00:00
-- url     : https://prove2.me/submissions/5c2f304a-f634-4898-a30e-2364294b286e

import Theorems.Thm_QAlgorithms_Childs_su2_small_commutator_factorization

open QAlgorithms
open scoped Matrix.Norms.L2Operator

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
private abbrev SU := Matrix.specialUnitaryGroup (Fin 2) ℂ

private def cmat (A B : Mat) : Mat := A * B * star A * star B

private lemma conjugation_sub_bound (A C X : Mat)
    (hA : A ∈ unitary Mat) (hC : C ∈ unitary Mat) :
    ‖A * X * star A - C * X * star C‖ ≤ 2 * ‖A - C‖ * ‖X‖ := by
  calc
    _ = ‖(A - C) * X * star A + C * X * star (A - C)‖ := by
      congr 1
      simp only [star_sub]
      noncomm_ring
    _ ≤ ‖(A - C) * X * star A‖ + ‖C * X * star (A - C)‖ := norm_add_le _ _
    _ = ‖(A - C) * X‖ + ‖X * star (A - C)‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hA), mul_assoc,
        CStarRing.norm_mem_unitary_mul _ hC]
    _ ≤ ‖A - C‖ * ‖X‖ + ‖X‖ * ‖star (A - C)‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖A - C‖ * ‖X‖ := by rw [norm_star]; ring

private lemma comm_first_bound (A B C : Mat)
    (hA : A ∈ unitary Mat) (hB : B ∈ unitary Mat) (hC : C ∈ unitary Mat) :
    ‖cmat A B - cmat C B‖ ≤ 2 * ‖A - C‖ * ‖B - 1‖ := by
  have hc : A * B * star A - C * B * star C =
      A * (B - 1) * star A - C * (B - 1) * star C := by
    simp only [mul_sub, sub_mul, mul_one, hA.2, hC.2]
    abel
  calc
    _ = ‖(A * B * star A - C * B * star C) * star B‖ := by rw [sub_mul]; rfl
    _ = ‖A * B * star A - C * B * star C‖ :=
      CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hB)
    _ = ‖A * (B - 1) * star A - C * (B - 1) * star C‖ := congrArg norm hc
    _ ≤ _ := conjugation_sub_bound A C (B - 1) hA hC

private lemma comm_star (A B : Mat) : star (cmat A B) = cmat B A := by
  simp only [cmat, star_mul, star_star]
  noncomm_ring

private lemma comm_second_bound (A B D : Mat)
    (hA : A ∈ unitary Mat) (hB : B ∈ unitary Mat) (hD : D ∈ unitary Mat) :
    ‖cmat A B - cmat A D‖ ≤ 2 * ‖B - D‖ * ‖A - 1‖ := by
  calc
    _ = ‖star (cmat A B - cmat A D)‖ := (norm_star _).symm
    _ = ‖cmat B A - cmat D A‖ := by rw [star_sub, comm_star, comm_star]
    _ ≤ _ := comm_first_bound B A D hB hA hD

private lemma comm_bound (A B C D : Mat)
    (hA : A ∈ unitary Mat) (hB : B ∈ unitary Mat)
    (hC : C ∈ unitary Mat) (hD : D ∈ unitary Mat) :
    ‖cmat A B - cmat C D‖ ≤
      2 * ‖A - C‖ * ‖B - 1‖ + 2 * ‖B - D‖ * ‖C - 1‖ := by
  exact (norm_sub_le_norm_sub_add_norm_sub (cmat A B) (cmat C B) (cmat C D)).trans
    (add_le_add (comm_first_bound A B C hA hB hC) (comm_second_bound C B D hC hB hD))

private lemma coe_comm (A B : SU) :
    ((A * B * A⁻¹ * B⁻¹ : SU) : Mat) = cmat (A : Mat) (B : Mat) := rfl

private lemma rounding_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (A B C D : SU) (hA : A ∈ su2Ball ε) (hB : B ∈ su2Ball ε)
    (hAC : specNorm ((A : Mat) - (C : Mat)) ≤ ε ^ 2)
    (hBD : specNorm ((B : Mat) - (D : Mat)) ≤ ε ^ 2) :
    specNorm (((A * B * A⁻¹ * B⁻¹ : SU) : Mat) -
      ((C * D * C⁻¹ * D⁻¹ : SU) : Mat)) ≤ 6 * ε ^ 3 := by
  have ha : ‖(A : Mat) - 1‖ ≤ ε := by
    simpa only [su2Ball, Set.mem_ofPred_eq, specNorm, norm_sub_rev] using hA
  have hb : ‖(B : Mat) - 1‖ ≤ ε := by
    simpa only [su2Ball, Set.mem_ofPred_eq, specNorm, norm_sub_rev] using hB
  have hac : ‖(A : Mat) - (C : Mat)‖ ≤ ε ^ 2 := hAC
  have hbd : ‖(B : Mat) - (D : Mat)‖ ≤ ε ^ 2 := hBD
  have hc : ‖(C : Mat) - 1‖ ≤ ε + ε ^ 2 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (C : Mat) (A : Mat) (1 : Mat)
    rw [norm_sub_rev (C : Mat) (A : Mat)] at ht
    linarith
  change ‖_‖ ≤ _
  rw [coe_comm, coe_comm]
  calc
    _ ≤ 2 * ‖(A : Mat) - (C : Mat)‖ * ‖(B : Mat) - 1‖ +
        2 * ‖(B : Mat) - (D : Mat)‖ * ‖(C : Mat) - 1‖ :=
      comm_bound _ _ _ _ A.property.1 B.property.1 C.property.1 D.property.1
    _ ≤ 2 * ε ^ 2 * ε + 2 * ε ^ 2 * (ε + ε ^ 2) := by
      gcongr
    _ ≤ 6 * ε ^ 3 := by nlinarith [mul_nonneg (sq_nonneg ε) (mul_nonneg hε.le (sub_nonneg.mpr hε1))]

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ Γ : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ),
        IsNet Γ (su2Ball ε) (ε ^ 2) → IsNet (commutatorSet Γ) (su2Ball (ε ^ 2)) (C * ε ^ 3) := by
  obtain ⟨K, hK, ε₀, hε₀, hfactor⟩ := QAlgorithms.Childs.su2_small_commutator_factorization
  refine ⟨K + 6, by linarith, min ε₀ 1, lt_min hε₀ (by norm_num), ?_⟩
  intro ε hε hsmall Γ hnet A hA
  obtain ⟨B, hB, C, hC, hBC⟩ := hfactor ε hε (hsmall.trans (min_le_left _ _)) A hA
  obtain ⟨U, hU, hBU⟩ := hnet B hB
  obtain ⟨V, hV, hCV⟩ := hnet C hC
  refine ⟨U * V * U⁻¹ * V⁻¹, ⟨U, hU, V, hV, rfl⟩, ?_⟩
  have hround := rounding_bound ε hε (hsmall.trans (min_le_right _ _)) B C U V hB hC hBU hCV
  change ‖_‖ ≤ _ at hBC hround ⊢
  calc
    _ ≤ ‖(A : Mat) - ((B * C * B⁻¹ * C⁻¹ : SU) : Mat)‖ +
        ‖((B * C * B⁻¹ * C⁻¹ : SU) : Mat) - ((U * V * U⁻¹ * V⁻¹ : SU) : Mat)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ K * ε ^ 3 + 6 * ε ^ 3 := add_le_add hBC hround
    _ = (K + 6) * ε ^ 3 := by ring
