-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.gram_eq_Hpk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:05:55.65179+00:00
-- url     : https://prove2.me/submissions/dc495b19-7ca3-4393-90f9-7e9f2fa4f3f4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_hJ_swap
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_gram_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula PI.NUnimodLoc.UnitaryGroupMassFormula.FC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW Formalism.REAL
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}
variable (hF : IsFrameJ ε e f wf z0)
include hF
namespace PI.NUnimodLoc.UnitaryGroupMassFormula.FC
theorem _root_.solution : (Pm k r e f wf z0)ᴴ * Jm ε * Pm k r e f wf z0 = Hpk k r := by
  have fe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0 := fun a b => by
    rw [hJ_swap, hF.ef]; split_ifs with h1 h2 h2 <;> simp_all
  have ze : ∀ a, hJ ε z0 (e a) = 0 := fun a => by rw [hJ_swap, hF.ez, star_zero]
  have zf : ∀ a, hJ ε z0 (f a) = 0 := fun a => by rw [hJ_swap, hF.fz, star_zero]
  have we : ∀ c a, hJ ε (wf a) (e c) = 0 := fun c a => by rw [hJ_swap, hF.ew, star_zero]
  have wf' : ∀ c a, hJ ε (wf a) (f c) = 0 := fun c a => by rw [hJ_swap, hF.fw, star_zero]
  have wz : ∀ a, hJ ε (wf a) z0 = 0 := fun a => by rw [hJ_swap, hF.zw, star_zero]
  ext i j
  rw [gram_apply]
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff, fcol]
  split_ifs <;>
    simp only [hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw, fe, ze, zf, we, wf',
      wz, Fin.mk.injEq] <;>
    (try split_ifs) <;> first | rfl | (exfalso; omega)
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
