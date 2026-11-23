-- Prove2me | solution 1 for PI.IsoDetW.Loc.lidx_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:34.408964+00:00
-- url     : https://prove2.me/submissions/75c0b28f-4c4b-4d08-87c6-12d6d1d2f65b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Theorems.Thm_PI_IsoDetW_Loc_lidx_eq_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs
variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
variable (p : Ideal R) [p.IsPrime]
namespace PI.IsoDetW.Loc
theorem _root_.solution {A B C D : Submodule R W} (hDA : D ≤ A) (hDB : D ≤ B) (hDC : D ≤ C)
    (hA : relative₂ (localization₂ p D) (localization₂ p A) ≠ ⊤) (hB : relative₂ (localization₂ p D) (localization₂ p B) ≠ ⊤)
    (hC : relative₂ (localization₂ p D) (localization₂ p C) ≠ ⊤) :
    lidx p A C = lidx p A B + lidx p B C := by
  rw [lidx_eq_of_le p (le_inf hDA hDC) hA hC, lidx_eq_of_le p (le_inf hDA hDB) hA hB,
    lidx_eq_of_le p (le_inf hDB hDC) hB hC]
  ring
end PI.IsoDetW.Loc
