-- Prove2me | solution 1 for PI.DatumBlockEigen.Main.phiU_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:10.853587+00:00
-- url     : https://prove2.me/submissions/798f836d-d74c-4b25-a093-be9d1e57190a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumBlockEigen
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_PhiUZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Main
open PI.DatumBlockEigen.Unit Formalism.DoubleCosetMeasures
variable {F : Type} [Field F] {a t : ℕ}
variable (O : Subring F) (ϖ : F) (J' : Subgroup (GL (Fin a) F))
namespace PI.DatumBlockEigen.Main
theorem _root_.solution (ρ : J' →* ℂˣ) (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (k : J')
    (hk : ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x)
    (hx : toRows₂ x ∈ IIset O ϖ) : phiU O ϖ J' ρ x = ((ρ k : ℂˣ) : ℂ) := by
  have h : (∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x) ∧
      toRows₂ x ∈ IIset O ϖ := ⟨⟨k, hk⟩, hx⟩
  unfold phiU
  rw [dif_pos h]
  have hc := Classical.choose_spec h.1
  have hck : Classical.choose h.1 = k := Subtype.ext (Units.ext (hc.trans hk.symm))
  rw [hck]
end PI.DatumBlockEigen.Main
