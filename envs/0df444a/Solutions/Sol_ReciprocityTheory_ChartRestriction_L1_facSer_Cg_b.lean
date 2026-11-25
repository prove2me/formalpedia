-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.facSer_Cg_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:43:03.896327+00:00
-- url     : https://prove2.me/submissions/b5ed2240-920c-41cd-a2c5-5db2d44e172e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_refl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ks_coeffIn_aC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ks_coeffIn_dC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ks_xp_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_rescale_map_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_mul


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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (b : ℕ) :
    Cg p (facSer p (1, b, p)) (xp p aC * dC - aC * xp p dC) := by
  have hsub : ∀ f : PowerSeries ℂ,
      sub1 (zetaC ((1, b, p) : ℕ × ℕ × ℕ).2.2 ^ ((1, b, p) : ℕ × ℕ × ℕ).2.1)
        (((1, b, p) : ℕ × ℕ × ℕ).1 ^ 2) f = PowerSeries.rescale (zetaC p ^ b) f := by
    intro f
    simp only [sub1, one_pow]
    exact ks_xp_one _
  rw [facSer, hsub, hsub]
  have hd : Cg p (PowerSeries.rescale (zetaC p ^ b) dC) dC := Cg.rescale_map_int hp.pos b dZ
  have ha : Cg p (PowerSeries.rescale (zetaC p ^ b) aC) aC := Cg.rescale_map_int hp.pos b aZ
  exact ((Cg.refl ((ks_coeffIn_aC _).xp p)).mul hd).sub (ha.mul (Cg.refl ((ks_coeffIn_dC _).xp p)))
end ReciprocityTheory.ChartRestriction.L1
