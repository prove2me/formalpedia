-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pderiv_facts_charZero_b7d4ab5b97c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:06.56212+00:00
-- url     : https://prove2.me/submissions/7ca36bfa-fc66-42a5-b753-753185a16c10

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinorA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {F : Type*} [Field F] [CharZero F] {σ : Type*} (p : MvPolynomial σ F) (j : σ) (hj : 0 < degreeOf j p) :
    pderiv j p ≠ 0 ∧ degreeOf j (pderiv j p) < degreeOf j p ∧
      (pderiv j p).vars ⊆ p.vars := by
  classical
  have hsupp : ∀ m ∈ (pderiv j p).support, m + Finsupp.single j 1 ∈ p.support := by
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    rw [mem_support_iff]
    exact left_ne_zero_of_mul hm
  refine ⟨?_, ?_, ?_⟩
  · have : ¬ degreeOf j p < 1 := by omega
    rw [degreeOf_lt_iff one_pos] at this
    push_neg at this
    obtain ⟨m, hm, hmj⟩ := this
    have hle : Finsupp.single j 1 ≤ m := Finsupp.single_le_iff.mpr hmj
    intro h0
    have hc := congr_arg (coeff (m - Finsupp.single j 1)) h0
    rw [coeff_pderiv, tsub_add_cancel_of_le hle, coeff_zero] at hc
    rw [mem_support_iff] at hm
    exact mul_ne_zero hm (Nat.cast_add_one_ne_zero _) hc
  · rw [degreeOf_lt_iff hj]
    intro m hm
    have := monomial_le_degreeOf j (hsupp m hm)
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  · intro i hi
    rw [mem_vars] at hi ⊢
    obtain ⟨m, hm, him⟩ := hi
    refine ⟨m + Finsupp.single j 1, hsupp m hm, ?_⟩
    rw [Finsupp.mem_support_iff] at him ⊢
    simp only [Finsupp.add_apply]
    omega
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
