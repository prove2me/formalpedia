-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_eulerChar_eq_finrank_H0_8f9d9dde05af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:44.301811+00:00
-- url     : https://prove2.me/submissions/a8c61582-c7f3-4160-b42d-f82801df3ce5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSnapperSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleSnapper

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
open MvPolynomial Filter
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (F : SubSystem k x Ω) (hF : ∀ i, 1 ≤ i → Subsingleton (F.H i)) :
    eulerChar k F = Module.finrank k (F.H 0) := by
  unfold eulerChar
  rw [Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp
  · intro i _
    have := hF (i + 1) (by omega)
    simp [Module.finrank_zero_of_subsingleton]
end GroundTheory.Heights₂.Heights.Kleiman
