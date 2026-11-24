-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_mem_succ_43982fb32ce9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:48:31.822738+00:00
-- url     : https://prove2.me/submissions/ae6a303f-acac-45b6-9e9c-5b831866ac33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
theorem _root_.solution (j : Fin q) {k : ℕ} {x : Ω} (hx : x ∈ gradedSpan w d t k) :
    x * w j ∈ gradedSpan w d t (k + 1) := by
  classical
  have hle : gradedSpan w d t k ≤
      (gradedSpan w d t (k + 1)).comap (AddMonoidHom.mulRight (w j)) := by
    rw [gradedSpan, AddSubgroup.closure_le]
    rintro _ ⟨l, μ, hμ, rfl⟩
    refine AddSubgroup.subset_closure ⟨l, μ + Pi.single j 1, ?_, ?_⟩
    · simp [Finset.sum_add_distrib, ← hμ, add_assoc]
    · have h1 : ∏ i, w i ^ (μ + Pi.single j 1 : Fin q → ℕ) i =
          (∏ i, w i ^ μ i) * ∏ i, w i ^ (Pi.single j 1 : Fin q → ℕ) i := by
        rw [← Finset.prod_mul_distrib]; simp [pow_add]
      have h2 : ∏ i, w i ^ (Pi.single j 1 : Fin q → ℕ) i = w j := by
        rw [Finset.prod_eq_single j (fun b _ hb => by simp [hb]) (by simp)]; simp
      rw [h1, h2]; simp [mul_assoc]
  exact hle hx
end GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
