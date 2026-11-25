-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Cg.of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:04.075274+00:00
-- url     : https://prove2.me/submissions/5de9350a-8211-4cad-9095-1b9308bb09ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_ksC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_map_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_p_mem_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
namespace Cg
theorem _root_.solution {p : ℕ} (hp : p.Prime) {F G W : PowerSeries ℤ} (h : F = G + PowerSeries.C (p : ℤ) * W) :
    Cg p (F.map (Int.castRingHom ℂ)) (G.map (Int.castRingHom ℂ)) := by
  obtain ⟨r, hr, hpr⟩ := p_mem_span hp
  refine ⟨CoeffIn.map_int _ G, PowerSeries.C r * W.map (Int.castRingHom ℂ),
    (CoeffIn.ksC hr).mul (CoeffIn.map_int _ W), ?_⟩
  rw [h, map_add, map_mul, PowerSeries.map_C]
  have hc : (Int.castRingHom ℂ) (p : ℤ) = (1 - zetaC p) * r := by
    rw [eq_intCast, Int.cast_natCast, hpr]
  rw [hc, map_mul]
  ring
end Cg
end ReciprocityTheory.ChartRestriction.L1
