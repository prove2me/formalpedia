-- Prove2me | solution 1 for P2M_Formalism_L2_DIV_polyAction_one__f4d3cf3e4198
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:18.307423+00:00
-- url     : https://prove2.me/submissions/c53a882e-ca78-4826-89a4-6f5f8bc3c5a7

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
omit [NumberField K]
namespace Formalism.L2.DIV
theorem _root_.solution (lam : ι → DomWeight n) (F : Pol K ι n) : actP lam 1 F = F :=
  congrArg (fun φ : Module.End K (Pol K ι n) => φ F) (rhoP lam).map_one
end Formalism.L2.DIV
