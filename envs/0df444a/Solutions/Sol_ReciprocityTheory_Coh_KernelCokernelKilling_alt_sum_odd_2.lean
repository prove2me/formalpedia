-- Prove2me | solution 2 for ReciprocityTheory.Coh.KernelCokernelKilling.alt_sum_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:55:42.672677+00:00
-- url     : https://prove2.me/submissions/991f885b-dc25-4339-b70f-79735900bf80

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_alt_sum_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
open ReciprocityTheory.Coh.KernelCokernelKilling
variable {R : Type u} [CommRing R] {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Subsingleton H]
namespace ReciprocityTheory.Coh.KernelCokernelKilling
theorem _root_.solution (m : ℕ) : (1 + ∑ j : Fin (2 * m + 1 + 1), (-1 : R) ^ ((j : ℕ) + 1)) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (-1 : R) ^ (j + 1)) (2 * m + 1 + 1)]
  exact (alt_sum_range m).2
end ReciprocityTheory.Coh.KernelCokernelKilling
