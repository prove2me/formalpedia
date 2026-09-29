-- Prove2me | solution 1 for Rep.indBotIota_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1a0807ed-14e5-5857-83b8-d0c78e053756

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_indBotIota_apply

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (a : A) :
    (Rep.indBotι A).hom a = ∑ g : G, A.indBotMk g (A.ρ g a) := by
  classical
  unfold Rep.indBotι
  rw [Rep.resIndAdjunction_unit_app]
  change Rep.coindToInd _ (((Rep.resCoindAdjunction k _).unit.app A).hom a) = _
  rw [Rep.coindToInd_apply]

  have hbij : Function.Bijective (Quotient.mk'' : G → Quotient (QuotientGroup.rightRel (⊥ : Subgroup G))) :=
    ⟨fun x y h => by
      have hxy : QuotientGroup.rightRel (⊥ : Subgroup G) x y := Quotient.exact' h
      rw [QuotientGroup.rightRel_apply, Subgroup.mem_bot] at hxy
      exact (mul_inv_eq_one.1 hxy).symm,
     fun q => Quotient.inductionOn' q fun g => ⟨g, rfl⟩⟩
  refine (Finset.sum_bij (fun g _ => Quotient.mk'' g) (fun _ _ => by convert Finset.mem_univ _) (fun _ _ _ _ h => hbij.1 h)
    (fun q _ => (hbij.2 q).elim fun g hg => ⟨g, Finset.mem_univ _, hg⟩) (fun g _ => ?_)).symm

  rfl

end S_Rep_indBotIota_apply
end P2MW
export P2MW.S_Rep_indBotIota_apply (solution)
