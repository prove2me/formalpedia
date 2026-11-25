-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.isClosed_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:13.108928+00:00
-- url     : https://prove2.me/submissions/23400efa-2491-4437-ba3b-7acdbb241301

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_isClosed_N
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mem_S_iff

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
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution (hK : IsCompact (UWset k r z)) : IsClosed (Sset k r z) := by
  haveI : CompactSpace (UWset k r z) := isCompact_iff_compactSpace.mp hK
  set C : Set (UWset k r z × Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    {p | Hpk k r * (p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * p.2 ∈ Nset k r}
  have hC : IsClosed C := by
    have hc : Continuous fun p : UWset k r z × Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
        Hpk k r * (p.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * p.2 :=
      ((continuous_const.matrix_mul
        ((continuous_subtype_val.comp continuous_fst).matrix_conjTranspose)).matrix_mul continuous_const).matrix_mul
        continuous_snd
    exact isClosed_N.preimage hc
  have e : Sset k r z = Prod.snd '' C := by
    ext g
    rw [mem_S_iff]
    constructor
    · rintro ⟨h, hh, hn⟩; exact ⟨(⟨h, hh⟩, g), hn, rfl⟩
    · rintro ⟨⟨h, g'⟩, hn, rfl⟩; exact ⟨h.1, h.2, hn⟩
  rw [e]
  exact isClosedMap_snd_of_compactSpace C hC
end PI.QuotSetU.UnitaryGroupMassFormula.SW
