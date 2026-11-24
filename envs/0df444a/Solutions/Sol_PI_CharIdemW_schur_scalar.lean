-- Prove2me | solution 1 for PI.CharIdemW.schur_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:14:33.739889+00:00
-- url     : https://prove2.me/submissions/336f6bf6-cf36-4f73-9f8f-58a07042e842

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
namespace PI.CharIdemW
theorem _root_.solution (W : FDRep ℂ G) [Simple W] (T : Module.End ℂ W)
    (hT : ∀ g : G, W.ρ g * T = T * W.ρ g) : ∃ c : ℂ, T = c • 1 := by
  let f : W ⟶ W :=
    { hom := FGModuleCat.ofHom T
      comm := fun g => by
        ext x
        exact (LinearMap.congr_fun (hT g) x).symm }
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ f
  refine ⟨c, ?_⟩
  ext x
  have hx := congrArg (fun φ : W ⟶ W => φ.hom.hom.hom x) hc
  exact hx.symm
end PI.CharIdemW
