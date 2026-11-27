-- Prove2me | solution 1 for PalomarZF207.internal_provC1_implies_linkedHalts
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-27T03:21:14.668473+00:00
-- url     : https://prove2.me/submissions/0d2c6333-7b7b-4f9e-9939-c7eaa107df3d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_internal_prov
import Definitions.Def_palomar_zf207_internal_tm
import Theorems.Thm_PalomarZF207_internal_startup_and_linkedHalts
import Theorems.Thm_PalomarZF207_internal_tm_loop_step
import Theorems.Thm_PalomarZF207_internal_provC1_implies_reg_halts

open PalomarZF207

theorem solution :
    ∀ (V : Type) (E : V → V → Prop), Nonempty V → Model E →
      PalomarZF207Internal.InternalProvC1 E → PalomarZF207History.InternalLinkedHalts E := by
  intro V E hNe hMod hProvC1
  obtain ⟨hLinked, hTrans, c0, m, t, z, two, c1, hc0, hz, h2, hm, ht, hfr, hreach01⟩ :=
    PalomarZF207.internal_startup_and_linkedHalts V E hNe hMod
  have hLoop := PalomarZF207.internal_tm_loop_step V E hNe hMod
  obtain ⟨c', term, hreach1', hcode', hval', hterm'⟩ :=
    PalomarZF207.internal_provC1_implies_reg_halts V E hNe hMod hLoop hProvC1 m t z two c1 hz h2 hm ht hfr
  exact hLinked c0 hc0 ⟨c', term, hTrans c0 c1 c' hreach01 hreach1', hcode', hval', hterm'⟩
