-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_proof_023ff2a73f0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:28.677488+00:00
-- url     : https://prove2.me/submissions/233b4af8-f14b-4957-b2bb-b6e00dd83f6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_isNumPolyLT_shear_d7c5eb724902
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_unit_steps_49b53de83d48

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SnapperDiffPoly
theorem _root_.solution : SnapperDiffPoly.Statement := by
  intro t D f μ hc hj
  classical
  let L : (Fin t → ℕ) → ℤ := fun n => ∑ i, μ i * (n i : ℤ)
  have hL : ∀ n j, L (Function.update n j (n j + 1)) = L n + μ j := by
    intro n j
    simp only [L]
    have : ∀ i, μ i * ((Function.update n j (n j + 1) i : ℕ) : ℤ) =
        μ i * (n i : ℤ) + if i = j then μ j else 0 := by
      intro i
      by_cases h : i = j
      · subst h; simp; ring
      · simp [h]
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  let g : (Fin t → ℕ) → ℤ → ℚ := fun n c => f n (c + L n)
  have hgc : IsNumPolyLT t D (fun n c => g n (c + 1) - g n c) := by
    obtain ⟨Q, hQ, hE⟩ := SnapperDiffPoly.isNumPolyLT_shear μ hc
    refine ⟨Q, hQ, fun n c => ?_⟩
    rw [← hE n c]
    simp only [g, L]
    rw [add_right_comm]
  have hgj : ∀ j, IsNumPolyLT t D (fun n c => g (Function.update n j (n j + 1)) c - g n c) := by
    intro j
    obtain ⟨Q, hQ, hE⟩ := SnapperDiffPoly.isNumPolyLT_shear μ (hj j)
    refine ⟨Q, hQ, fun n c => ?_⟩
    rw [← hE n c]
    simp only [g]
    rw [hL n j, ← add_assoc]
  obtain ⟨Q, hQ, hE⟩ := SnapperDiffPoly.isNumPolyLT_shear (-μ) (SnapperDiffPoly.unit_steps g hgc hgj)
  refine ⟨Q, hQ, fun n c => ?_⟩
  rw [← hE n c]
  simp only [g, L, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  congr 1
  ring
end SnapperDiffPoly
end GroundTheory.Heights₂.Heights.Kleiman
