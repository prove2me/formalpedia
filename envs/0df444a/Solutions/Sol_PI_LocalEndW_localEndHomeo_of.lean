-- Prove2me | solution 1 for PI.LocalEndW.localEndHomeo_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:14.24049+00:00
-- url     : https://prove2.me/submissions/e80ecd05-8f5b-4bad-9326-ff6088a46186

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_ValSurjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_LocalEndHomeoOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open PI PI.LocalEndW
namespace PI.LocalEndW
theorem _root_.solution (hA : HenselRoot) (hB1 : IntOfHensel) (hB2 : ValOfInt)
    (hC1 : ValContinuous) (hC2 : ValSurjective) : PI.LocalEndHomeo := by
  have hV : ValPreserved := hB2 (hB1 hA)
  intro F _ _ v τ
  have hτv : ∀ x, Valued.v (τ x) = Valued.v x := hV F v τ
  have hsurj := hC2 F v τ hτv
  let e := RingEquiv.ofBijective τ ⟨τ.injective, hsurj⟩
  refine ⟨hC1 F v τ hτv, e.symm.toRingHom, ?_, fun a => e.apply_symm_apply a⟩
  apply hC1 F v
  intro x
  have := hτv (e.symm x)
  rw [show τ (e.symm x) = x from e.apply_symm_apply x] at this
  exact this.symm
end PI.LocalEndW
