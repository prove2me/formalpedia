-- Prove2me | solution 1 for ULHC.mem_allStrips
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:02:19.671955+00:00
-- url     : https://prove2.me/submissions/1fe432b9-89f9-4332-89df-fe786a58b762

import Definitions.Def_ULHC_CrPath
import Definitions.Def_ULHC_Comp
import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_Enum
import Theorems.Thm_ULHC_stripLen_eq_some
import Theorems.Thm_ULHC_mem_sidesF
import Theorems.Thm_ULHC_Edge_hi_mk
import Theorems.Thm_ULHC_Edge_lo_h
import Theorems.Thm_ULHC_Edge_lo_v
import Theorems.Thm_ULHC_Edge_q_h
import Theorems.Thm_ULHC_Edge_q_v
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_ULHC_cellJ_zero
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
theorem _root_.solution {σ : StripSpec} :
    σ ∈ allStrips V F ↔
      1 ≤ σ.n ∧ StripPat F σ.c σ.s σ.n ∧ ∀ j < σ.n, IsCell V (cellJ σ.c σ.s j) := by
  obtain ⟨c, s, n⟩ := σ
  simp only [allStrips, Finset.mem_biUnion, Finset.mem_filter, Option.mem_toFinset,
    Option.mem_def, Option.map_eq_some_iff]
  constructor
  · rintro ⟨c', _, s', _, n', hn', he⟩
    cases he
    exact stripLen_eq_some.1 hn'
  · intro h
    have hc0 : IsCell V c := by have := h.2.2 0 (by omega); rwa [cellJ_zero] at this
    exact ⟨c, ⟨hc0.1, hc0⟩, s, mem_sidesF s, n, stripLen_eq_some.2 h, rfl⟩
end ULHC
