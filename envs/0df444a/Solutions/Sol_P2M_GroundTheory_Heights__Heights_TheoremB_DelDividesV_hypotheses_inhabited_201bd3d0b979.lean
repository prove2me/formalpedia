-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_DelDividesV_hypotheses_inhabited_201bd3d0b979
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:23.17981+00:00
-- url     : https://prove2.me/submissions/6f52ee50-9f13-4c95-b6ae-a6c84b80358d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace DelDividesV
theorem _root_.solution (d : IndexData) :
    ∀ (τ : Fin d.f) (a b : Fin d.N), a < b →
      (X (τ, a) - X (τ, b) : LamPoly d) ∣ antisymDelta (Fin d.f) d.N := by
  intro τ a b hab
  unfold antisymDelta
  exact ((Finset.dvd_prod_of_mem (fun b => (X (τ, a) - X (τ, b) : LamPoly d))
    (Finset.mem_Ioi.2 hab)).trans (Finset.dvd_prod_of_mem
      (fun a => ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b) : LamPoly d)) (Finset.mem_univ a))).trans
    (Finset.dvd_prod_of_mem
      (fun τ => ∏ a : Fin d.N, ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b) : LamPoly d))
      (Finset.mem_univ τ))
end DelDividesV
end GroundTheory.Heights₂.Heights.TheoremB
