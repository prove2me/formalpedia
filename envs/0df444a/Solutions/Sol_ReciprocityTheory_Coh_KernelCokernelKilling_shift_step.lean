-- Prove2me | solution 1 for ReciprocityTheory.Coh.KernelCokernelKilling.shift_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:28:01.582014+00:00
-- url     : https://prove2.me/submissions/ac19f35d-128a-4256-9a3a-a9e798ff7c8a

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_shAdm
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_shC_acyc
import Theorems.Thm_ReciprocityTheory_Coh_admissibility_holds
import Theorems.Thm_ReciprocityTheory_Coh_lES_holds


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
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V]
namespace ReciprocityTheory.Coh.KernelCokernelKilling
theorem _root_.solution (n : ℕ) (hQ : Subsingleton ((shQ M).H n)) : Subsingleton (M.H (n + 1)) := by
  obtain ⟨δ, -, hL⟩ := (lES_holds R _ _ _ _ _ (admissibility_holds R G _ _ _ _ _ (shAdm M))).1
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have hC := shC_acyc M (n + 1) (by omega)
  have h0 : (shIP M).hom.H (n + 1) x = 0 := Subsingleton.elim _ _
  obtain ⟨q, rfl⟩ := (hL.exA n x).1 h0
  rw [Subsingleton.elim q 0, map_zero]
end ReciprocityTheory.Coh.KernelCokernelKilling
