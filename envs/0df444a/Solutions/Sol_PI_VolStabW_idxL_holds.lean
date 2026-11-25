-- Prove2me | solution 1 for PI.VolStabW.idxL_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:28.780318+00:00
-- url     : https://prove2.me/submissions/1c538927-b2af-4f3b-9075-80b4144c43ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
import Definitions.Def_ReciprocityTheory_ResidueCardinality_ArtinOntoB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHIL
import Theorems.Thm_PI_VolStabW_IdxLW_index_maxIdeal
import Theorems.Thm_PI_VolStabW_IdxLW_crdL_surj
import Theorems.Thm_PI_VolStabW_IdxLW_addSubgroupOf_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open IdxLW
namespace PI.VolStabW
theorem _root_.solution : IdxL := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT _ d b v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at this
    exact this.symm
  unfold AddSubgroup.relIndex
  rw [addSubgroupOf_eq, AddSubgroup.index_comap_of_surjective _ (crdL_surj v b a M),
    AddSubgroup.index_pi]
  simp only [index_maxIdeal, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]
  subst hd
  ring_nf
end PI.VolStabW
