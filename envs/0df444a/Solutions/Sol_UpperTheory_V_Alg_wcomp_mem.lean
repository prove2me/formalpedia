-- Prove2me | solution 1 for UpperTheory.V.Alg.wcomp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:34:06.895156+00:00
-- url     : https://prove2.me/submissions/79eaa5bf-52d0-43a9-b02e-5e0490e46950

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective
import Theorems.Thm_UpperTheory_V_Alg_coeff_wcomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open UpperTheory UpperTheory.V UpperTheory.V.Alg
attribute [instance] IsCO.complete IsCO.isLocalHom
variable (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
namespace UpperTheory.V.Alg
theorem _root_.solution (j : X) (f : MvPowerSeries σ O) : wcomp O wt j f ∈ wtPart O wt j :=
  fun n hn => by rw [coeff_wcomp, if_neg hn]
end UpperTheory.V.Alg
