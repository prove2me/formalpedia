-- Prove2me | solution 1 for PI.LocJacOrd.W.Ar.absV_prod_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:59:18.716881+00:00
-- url     : https://prove2.me/submissions/a1d5c568-7ae9-477f-8f3b-a5abe0ca3e9e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W PI.LocJacOrd.W.Ar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd
open scoped TensorProduct Classical
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocJacOrd.W.Ar
theorem _root_.solution {r : ℕ} (s : Finset (Fin (r + 1))) (f : Fin (r + 1) → Fv F v) :
    absV v (∏ i ∈ s, f i ^ 2) = ∏ i ∈ s, absV v (f i) ^ 2 :=
  (map_prod (absVHom v) (fun i => f i ^ 2) s).trans
    (Finset.prod_congr rfl fun i _ => map_pow (absVHom v) (f i) 2)
end PI.LocJacOrd.W.Ar
