-- Prove2me | solution 1 for ULHC.card_allStrips
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:51:18.288181+00:00
-- url     : https://prove2.me/submissions/072e161c-1147-461e-9360-c6e931bc9ae4

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
attribute [local simp] ULHC.Edge.hi_mk
attribute [local simp] ULHC.Edge.lo_h
attribute [local simp] ULHC.Edge.lo_v
attribute [local simp] ULHC.Edge.q_h
attribute [local simp] ULHC.Edge.q_v



set_option autoImplicit true
open ULHC
open Finset
variable (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side)
variable {V F c s}
variable (V F)
variable {V F}
namespace ULHC
theorem _root_.solution : (allStrips V F).card ≤ 4 * V.card := by
  unfold allStrips
  refine (Finset.card_biUnion_le).trans ?_
  have h1 : ∀ c ∈ V.filter (IsCell V), (sidesF.biUnion fun s =>
      ((stripLen V F c s).map (fun n => StripSpec.mk c s n)).toFinset).card ≤ 4 := by
    intro c _
    refine (Finset.card_biUnion_le).trans ?_
    have : ∀ s ∈ sidesF, (((stripLen V F c s).map (fun n => StripSpec.mk c s n)).toFinset).card
        ≤ 1 := fun s _ => by
      cases (stripLen V F c s).map (fun n => StripSpec.mk c s n) <;> simp
    refine (Finset.sum_le_sum this).trans ?_
    simp [sidesF]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  have := Finset.card_filter_le V (IsCell V)
  omega
end ULHC
