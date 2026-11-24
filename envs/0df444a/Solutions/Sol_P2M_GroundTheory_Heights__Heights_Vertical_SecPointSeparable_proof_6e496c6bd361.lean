-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecPointSeparable_proof_6e496c6bd361
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:40.399479+00:00
-- url     : https://prove2.me/submissions/d4417172-79e2-4d73-9c93-c981288626ce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecPointSeparable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenericFormsKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsDerivSpanTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFreeParAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecPointSeparable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecPointSeparable_isSeparable_of_derivation_eq_zero_006ace4b1d9d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open SecPointSeparable
namespace GroundTheory.Heights₂.Heights.Vertical
namespace SecPointSeparable
theorem _root_.solution (h₁ : GenericFormsKer.Statement) (h₂ : DerivSpanTrdeg.Statement)
    (h₃ : FreeParAlgIndep.Statement) : SecPointSeparable.Statement := by
  intro k _ _ n e L _ _ _ _ _ x hx hU hT htr
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, x j₀ ≠ 0 := by
    by_contra! h
    simp [h] at hT
  set z : Fin n → L := fun m => x m * (x j₀)⁻¹ with hz
  obtain ⟨r, hre, b, hb⟩ := h₂ k L (Fin n) z e (htr j₀ hj₀)
  have hind := h₃ k n e L x hx hU hT j₀ hj₀ (htr j₀ hj₀)
  apply isSeparable_of_derivation_eq_zero
  intro D
  obtain ⟨c, hc⟩ := hb (D.restrictScalars k)
  have hc' : ∀ j, D (z j) = ∑ m, c m * (b m j : L) := hc
  have hDK : ∀ a : GenParField k e n, D (algebraMap (GenParField k e n) L a) = 0 :=
    fun a => D.map_algebraMap a
  have hlin : ∀ (a : GenParField k e n) (y : L),
      D (algebraMap (GenParField k e n) L a * y) = algebraMap (GenParField k e n) L a * D y := by
    intro a y
    rw [D.leibniz, hDK, smul_zero, add_zero, smul_eq_mul]
  have hDz₀ : D (z j₀) = 0 := by
    simp only [z, mul_inv_cancel₀ hj₀, Derivation.map_one_eq_zero]
  have hUDz : ∀ i : Fin e,
      ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * D (z j) = 0 := by
    intro i
    have h0 : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j = 0 := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hU i, zero_mul]
    have := congrArg D h0
    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => (hlin _ _).symm
  have hDz : ∀ j, D (z j) = 0 := by
    have key := h₁ (IntermediateField.adjoin k (Set.range z)) L {j : Fin n // j ≠ j₀} e r hre
      (fun p => algebraMap (GenParField k e n) L (genPar k e n (.inl (p.1, p.2.1)))) hind
      (fun m j => b m j.1) c (fun i => ?_)
    · intro j
      by_cases hj : j = j₀
      · rw [hj, hDz₀]
      · rw [hc' j]
        exact key ⟨j, hj⟩
    · have := hUDz i
      rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, hDz₀, mul_zero, zero_add] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc' j.1]
      rfl
  have hx₀ : D (x j₀) = 0 := by
    have hs : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j = (x j₀)⁻¹ := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hT, one_mul]
    have h1 := congrArg D hs
    rw [map_sum, Finset.sum_eq_zero fun j _ => by rw [hlin, hDz, mul_zero], Derivation.leibniz_inv,
      eq_comm, smul_eq_mul, neg_mul, neg_eq_zero, mul_eq_zero] at h1
    exact h1.resolve_left (pow_ne_zero _ (inv_ne_zero hj₀))
  have hxj : ∀ j, D (x j) = 0 := by
    intro j
    have hxz : x j = z j * x j₀ := by simp only [z, mul_assoc, inv_mul_cancel₀ hj₀, mul_one]
    rw [hxz, D.leibniz, hx₀, hDz, smul_zero, smul_zero, add_zero]
  exact Derivation.ext_of_adjoin_eq_top (Set.range x) hx (by rintro _ ⟨j, rfl⟩; simpa using hxj j)
end SecPointSeparable
end GroundTheory.Heights₂.Heights.Vertical
