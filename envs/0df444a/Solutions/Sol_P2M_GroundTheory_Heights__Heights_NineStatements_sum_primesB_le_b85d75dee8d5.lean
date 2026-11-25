-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_sum_primesB_le_b85d75dee8d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:14.603833+00:00
-- url     : https://prove2.me/submissions/280a97c6-83f0-48f2-b525-1146dae9a320

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {C : ℝ} (h5 : ∀ B : ℕ, 2 ≤ B → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ B →
      ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) ≤ C * Real.log B)
    {B : ℕ} (hB : 2 ≤ B) {bad : Finset ℕ} (hbad : ∀ p ∈ bad, p.Prime) (hcard : bad.card ≤ B) :
    ∑ p ∈ primesB B bad, Real.log p / ((p : ℝ) - 1) ≤ 2 * C * Real.log B := by
  have hnn : ∀ p ∈ (Finset.Icc 1 B).filter Nat.Prime ∩ bad, 0 ≤ Real.log p / ((p : ℝ) - 1) := by
    intro p hp
    have hp' := hbad p (Finset.mem_inter.mp hp).2
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
    exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hA : ∑ p ∈ (Finset.Icc 1 B).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) ≤ C * Real.log B := by
    apply h5 B hB
    · intro p hp; exact (Finset.mem_filter.mp hp).2
    · calc ((Finset.Icc 1 B).filter Nat.Prime).card ≤ (Finset.Icc 1 B).card := Finset.card_filter_le _ _
        _ = B := by simp
  have hU := Finset.sum_union_inter (s₁ := (Finset.Icc 1 B).filter Nat.Prime) (s₂ := bad)
    (f := fun p : ℕ => Real.log p / ((p : ℝ) - 1))
  have hI := Finset.sum_nonneg hnn
  have hb := h5 B hB bad hbad hcard
  rw [primesB]
  linarith
end GroundTheory.Heights₂.Heights.NineStatements
