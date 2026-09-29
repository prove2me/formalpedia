-- Prove2me | solution 1 for Rep.IsTateCupProduct.cup_mk_mk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a62c64c4-580d-5a57-a9b1-8a6978d666fd

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Theorems.Thm_Rep_IsTateCupProduct_cup_mk_left_eq_tateMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_IsTateCupProduct_cup_mk_mk

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"
open groupCohomology

namespace P2mS26H0a

noncomputable def tmulLeft {k G : Type u} [CommRing k] [Group G] (A M : Rep.{u} k G) (a : A.ρ.invariants) :
    M ⟶ A ⊗ M :=
  Rep.ofHom ⟨TensorProduct.mk k A M (a : A), fun g => LinearMap.ext fun m => by
    change (a : A) ⊗ₜ[k] (M.ρ g m) = (A.ρ.tprod M.ρ) g ((a : A) ⊗ₜ[k] m)
    rw [Representation.tprod_apply, TensorProduct.map_tmul, a.2 g]⟩

end P2mS26H0a

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (a : A.ρ.invariants) (b : B.ρ.invariants) (c : (A ⊗ B).ρ.invariants)
    (hc : (c : (A ⊗ B : Rep.{u} k G)) = (a : A) ⊗ₜ[k] (b : B)) :
    cup A B 0 0 0 (add_zero 0) (Submodule.Quotient.mk a : A.tateH0) (Submodule.Quotient.mk b : B.tateH0)
      = (Submodule.Quotient.mk c : (A ⊗ B).tateH0) := by
  refine (Rep.IsTateCupProduct.cup_mk_left_eq_tateMap hcup A B a (P2mS26H0a.tmulLeft A B a) (fun _ => rfl) 0
    (Submodule.Quotient.mk b : B.tateH0)).trans ?_
  change (Submodule.Quotient.mk (Rep.invariantsMap (P2mS26H0a.tmulLeft A B a) b) : (A ⊗ B).tateH0)
    = Submodule.Quotient.mk c
  congr 1
  exact Subtype.ext hc.symm

end S_Rep_IsTateCupProduct_cup_mk_mk
end P2MW
export P2MW.S_Rep_IsTateCupProduct_cup_mk_mk (solution)
