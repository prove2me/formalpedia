-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsOpen_proof_265a021d820f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:12:52.457675+00:00
-- url     : https://prove2.me/submissions/c2468f49-abc9-4420-b89d-4c16af0410ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_isHomogeneous_leadIdeal_sup_linIdeal_93230be836e2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_monomial_mem_originIdeal_pow_6baf16d737ed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_originIdeal_pow_le_92c638b6f9b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_isZariskiOpen_of_local_8b9b0416d030

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace ConeAvoidsOpen
theorem _root_.solution : ConeAvoidsOpen.Statement := by
  intro n d N J
  classical
  refine isZariskiOpen_of_local fun A₀ hA₀ => ?_
  set V := Finset.finsuppAntidiag (Finset.univ : Finset (Fin n)) N
  have hV : ∀ m : Fin n →₀ ℕ, m ∈ V ↔ m.degree = N := fun m => by
    simp [V, Finsupp.degree_eq_sum]
  have hrep : ∀ m : V, ∃ a ∈ leadIdeal J, ∃ h : Fin d → MvPolynomial (Fin n) ℂ,
      a + ∑ j, h j * linPoly A₀ j = monomial (m : Fin n →₀ ℕ) 1 := by
    intro m
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Submodule.mem_sup.1 (hA₀ (monomial_mem_originIdeal_pow ((hV m).1 m.2)))
    obtain ⟨h, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb
    exact ⟨a, ha, h, hab⟩
  choose a ha h hah using hrep
  let T : Matrix (Fin d) (Fin n) ℂ → V → MvPolynomial (Fin n) ℂ :=
    fun A m => a m + ∑ j, h m j * linPoly A j
  let P : Matrix V V (MvPolynomial (Fin d × Fin n) ℂ) := fun m' m =>
    C (coeff (m' : Fin n →₀ ℕ) (a m)) +
      ∑ j, ∑ k, C (coeff (m' : Fin n →₀ ℕ) (h m j * X k)) * X (j, k)
  have hP : ∀ (A : Matrix (Fin d) (Fin n) ℂ) (m' m : V),
      (eval fun ij : Fin d × Fin n => A ij.1 ij.2).mapMatrix P m' m =
        coeff (m' : Fin n →₀ ℕ) (T A m) := by
    intro A m' m
    show eval _ (P m' m) = _
    simp only [P, T, linPoly, map_add, map_sum, map_mul, eval_C, eval_X, coeff_add, coeff_sum,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, coeff_C_mul, mul_comm]
  refine ⟨P.det, ?_, fun A hA => ?_⟩
  · rw [RingHom.map_det]
    have h1 : (eval fun ij : Fin d × Fin n => A₀ ij.1 ij.2).mapMatrix P = 1 := by
      ext m' m
      rw [hP, Matrix.one_apply]
      simp only [T, hah, coeff_monomial, Subtype.ext_iff, eq_comm]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  · rw [RingHom.map_det] at hA
    set M := (eval fun ij : Fin d × Fin n => A ij.1 ij.2).mapMatrix P
    have hMT : ∀ m' m : V, M m' m = coeff (m' : Fin n →₀ ℕ) (T A m) := hP A
    have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hA)
    have hI : ∀ m, T A m ∈ leadIdeal J ⊔ linIdeal A := fun m =>
      Submodule.add_mem_sup (ha m) (Ideal.mem_span_range_iff_exists_fun.2 ⟨h m, rfl⟩)
    have hhom := isHomogeneous_leadIdeal_sup_linIdeal J A
    refine originIdeal_pow_le fun m hm => ?_
    have key : monomial m (1 : ℂ) =
        ∑ m'' : V, C (M⁻¹ m'' ⟨m, (hV m).2 hm⟩) * homogeneousComponent N (T A m'') := by
      ext s
      simp only [coeff_sum, coeff_C_mul, coeff_homogeneousComponent, coeff_monomial]
      by_cases hs : s.degree = N
      · have e := congr_fun (congr_fun hinv ⟨s, (hV s).2 hs⟩) ⟨m, (hV m).2 hm⟩
        simp only [Matrix.mul_apply, hMT, Matrix.one_apply, Subtype.ext_iff] at e
        simp only [hs, if_true]
        simp_rw [mul_comm (M⁻¹ _ _)]
        rw [e]
        by_cases hsm : s = m
        · simp [hsm]
        · simp [hsm, Ne.symm hsm]
      · simp only [hs, if_false, mul_zero, Finset.sum_const_zero]
        rw [if_neg]
        rintro rfl
        exact hs hm
    rw [key]
    exact Ideal.sum_mem _ fun m'' _ =>
      Ideal.mul_mem_left _ _ (homogeneousComponent_mem_of_mem hhom (hI m'') N)
end ConeAvoidsOpen
end GroundTheory.Heights₂.Heights.ComplexSets
