-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.hd_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:51:36.034578+00:00
-- url     : https://prove2.me/submissions/033716b3-de3c-44c6-888f-facc8cd4f873

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution {V X : Type u} [AddCommGroup V] (n : ℕ) (c : ℤ) (F : (Fin (n + 1) → X) → V) :
    hd n (c • F) = c • hd n F := by
  funext x
  unfold hd
  simp only [Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
end ReciprocityTheory.Coh.CCA
