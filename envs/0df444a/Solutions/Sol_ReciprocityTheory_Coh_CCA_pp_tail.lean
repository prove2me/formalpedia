-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.pp_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:45:59.685243+00:00
-- url     : https://prove2.me/submissions/d8bf19ad-64f2-4e3c-9e1a-c438aba376ba

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
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution {K : Type*} [Group K] {p q : ℕ} (g : Fin (p + q) → K) (j : Fin q) :
    (Fin.partialProd g ⟨p + j, by omega⟩)⁻¹ * Fin.partialProd g ⟨p + j + 1, by omega⟩ =
      g (Fin.natAdd p j) := by
  rw [show (⟨p + j + 1, by omega⟩ : Fin (p + q + 1)) = Fin.succ (⟨p + j, by omega⟩ : Fin (p + q)) from
    Fin.ext rfl, Fin.partialProd_succ]
  exact inv_mul_cancel_left _ _
end ReciprocityTheory.Coh.CCA
