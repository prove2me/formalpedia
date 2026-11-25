-- Prove2me | solution 1 for PIW.ClassFinD.Icf.val_eq_of_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:49:01.770058+00:00
-- url     : https://prove2.me/submissions/9248c27c-2fa8-4047-9d89-cc7ff76ad3f4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_LatticeIdealNonzero
import Theorems.Thm_PIW_ClassFinD_Icf_val_le_of_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.ClassFinD PIW.ClassFinD.Icf
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PIW.ClassFinD.Icf
theorem _root_.solution (b b0 : (FiniteAdeleRing (𝓞 F) F)ˣ) (hb : IsIntU b) (hb0 : IsIntU b0)
    (h : cls b = cls b0) : ∃ x y : 𝓞 F, x ≠ 0 ∧ y ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
      v.intValuation x * Valued.v ((b : FiniteAdeleRing (𝓞 F) F) v) =
        v.intValuation y * Valued.v ((b0 : FiniteAdeleRing (𝓞 F) F) v) := by
  unfold cls at h
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  refine ⟨x, y, hx, hy, fun v => le_antisymm ?_ ?_⟩
  · exact val_le_of_le b b0 hb (le_of_eq hxy) v
  · exact val_le_of_le b0 b hb0 (le_of_eq hxy.symm) v
end PIW.ClassFinD.Icf
