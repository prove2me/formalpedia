-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.ebt_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:56:50.517983+00:00
-- url     : https://prove2.me/submissions/8f81c00b-0d7f-4a67-a479-c67428912244

import Mathlib
import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P02
/-- Theorem 3, PDF p.3: convexity in the real vector space of complex-linear maps. -/
theorem gk_sep_cone {I J : Type*} [Fintype I] [Fintype J]
    (X Y : Matrix (I × J) (I × J) ℂ) (hX : Entanglement.IsSeparablePositive X)
    (hY : Entanglement.IsSeparablePositive Y) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Entanglement.IsSeparablePositive ((a : ℂ) • X + (b : ℂ) • Y) := by
  obtain ⟨q1, w1, A1, B1, hw1, hAB1, rfl⟩ := hX
  obtain ⟨q2, w2, A2, B2, hw2, hAB2, rfl⟩ := hY
  refine ⟨q1 + q2, Fin.append (fun j => a * w1 j) (fun j => b * w2 j),
    Fin.append A1 A2, Fin.append B1 B2, ?_, ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.append_left]; exact mul_nonneg ha (hw1 j)
    · simp only [Fin.append_right]; exact mul_nonneg hb (hw2 j)
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.append_left]; exact hAB1 j
    · simp only [Fin.append_right]; exact hAB2 j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.smul_sum, smul_smul,
      Complex.ofReal_mul]

theorem solution (d : ℕ) (hd : 0 < d) : Convex ℝ (ebtSet d) := by
  intro P1 h1 P2 h2 a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro n hn X hX
    have e : idTensorSuperop (⇑(a • P1 + b • P2)) X =
        (a : ℂ) • idTensorSuperop (⇑P1) X + (b : ℂ) • idTensorSuperop (⇑P2) X := by
      ext p q
      simp [idTensorSuperop, Complex.real_smul]
    rw [e]
    exact gk_sep_cone _ _ (h1.1 n hn X hX) (h2.1 n hn X hX) a b ha hb
  · intro X
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Matrix.trace_add,
      Matrix.trace_smul, h1.2 X, h2.2 X]
    rw [← add_smul, hab, one_smul]

