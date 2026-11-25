-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_polarise_1454c871b39d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:40.430828+00:00
-- url     : https://prove2.me/submissions/c9b28bdd-1189-4fbc-a42f-39aac36cd0b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (hM : Mᵀ = M) (p q : Fin g) :
    (((fun k => ((Pi.single p 1 + Pi.single q 1 : Fin g → ℤ) k : ℂ)) ⬝ᵥ
          M *ᵥ fun k => ((Pi.single p 1 + Pi.single q 1 : Fin g → ℤ) k : ℂ)) -
        ((fun k => ((Pi.single p 1 : Fin g → ℤ) k : ℂ)) ⬝ᵥ
          M *ᵥ fun k => ((Pi.single p 1 : Fin g → ℤ) k : ℂ)) -
        ((fun k => ((Pi.single q 1 : Fin g → ℤ) k : ℂ)) ⬝ᵥ
          M *ᵥ fun k => ((Pi.single q 1 : Fin g → ℤ) k : ℂ))) / 2 = M p q := by
  have hc : ∀ r : Fin g, (fun k => ((Pi.single r 1 : Fin g → ℤ) k : ℂ)) = Pi.single r 1 := fun r => by
    funext k
    by_cases hk : k = r
    · subst hk; simp
    · simp [hk]
  have hadd : (fun k => ((Pi.single p 1 + Pi.single q 1 : Fin g → ℤ) k : ℂ)) =
      Pi.single p 1 + Pi.single q 1 := by
    rw [← hc p, ← hc q]
    funext k
    simp
  have hqp : M q p = M p q := by
    have := congrFun (congrFun hM p) q
    simpa [transpose_apply] using this
  rw [hadd, hc p, hc q]
  simp only [mulVec_add, dotProduct_add, add_dotProduct, mulVec_single_one, single_one_dotProduct,
    col_apply, hqp]
  ring
end GroundTheory.Heights₂.Heights.Regular
