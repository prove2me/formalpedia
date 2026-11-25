-- Prove2me | solution 1 for ReciprocityTheory.Coh.KernelCokernelKilling.triv_H_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:22.602003+00:00
-- url     : https://prove2.me/submissions/0ae244c7-cd70-494e-bef7-a4907c746365

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_triv_odd
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_triv_even

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
theorem _root_.solution (T : TRep R H) (k : ℕ) (hk : 1 ≤ k) : Subsingleton (T.H k) := by
  obtain ⟨m, hm | hm⟩ : ∃ m, k = 2 * m + 1 ∨ k = 2 * m + 1 + 1 := by
    rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t - 1, Or.inr (by omega)⟩
    · exact ⟨t, Or.inl ht⟩
  · subst hm
    exact triv_odd T m
  · subst hm
    exact triv_even T m
end ReciprocityTheory.Coh.KernelCokernelKilling
