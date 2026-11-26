-- Prove2me | solution 1 for TDLC.Syntax.interpret_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:27.898308+00:00
-- url     : https://prove2.me/submissions/e1e69100-8487-4bd7-8c3c-b18076f2b019

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax
import Theorems.Thm_TDLC_Syntax_parity_cast

set_option autoImplicit true
open TDLC TDLC.Syntax
namespace TDLC.Syntax
theorem _root_.solution {t s : Tm Γ a} (c : Conv t s) (ρ : Env U Γ) :
    TDLC.Step.parity (interpret c ρ) = c.parity := by
  induction c with
  | beta t x =>
      exact parity_cast _ _ _
  | eta f =>
      exact parity_cast _ _ _
  | appLeft c x ih => exact ih ρ
  | appRight f c ih => exact ih ρ
  | lam c ih => rfl
  | refl t => rfl
  | sym c ih => exact ih ρ
  | trans c d ihc ihd =>
      change bxor _ _ = bxor _ _
      rw [ihc, ihd]
end TDLC.Syntax
