-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSec_mapDomain_newEmb_some_d6e9fc69ab69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:00.434362+00:00
-- url     : https://prove2.me/submissions/bcb57c05-cddf-4834-ab8b-932630a3df37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSec
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.YPlusSec
theorem _root_.solution (m : (Σ _ : Unit, Fin (D.size + 1)) →₀ ℕ) (k : ι)
    (i : Fin (D.extSizes (some k) + 1)) :
    Finsupp.mapDomain (newEmb D) m ⟨some k, i⟩ = 0 := by
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨p, hp⟩
  have h1 := congrArg (fun w : Coord D.extSizes ↦ w.1) hp
  simp [newEmb] at h1
end GroundTheory.Heights₂.Heights.YPlusSec
