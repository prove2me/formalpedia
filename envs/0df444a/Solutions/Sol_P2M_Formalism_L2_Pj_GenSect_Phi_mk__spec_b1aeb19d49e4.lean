-- Prove2me | solution 1 for P2M_Formalism_L2_Pj_GenSect_Phi_mk__spec_b1aeb19d49e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:41:27.444589+00:00
-- url     : https://prove2.me/submissions/558a946f-9db2-4f1c-95a1-f2cf97cfe896

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m)
    (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) (a : ΩT Ω D m) (y : KTS K Ω D m)
    (v : FractionRing (CT Ω D j₀)) :
    Phi x j₀ hinj (IsLocalization.mk' (RS K Ω D m) a y) = v ↔
      algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ a) =
        algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y) * v :=
  IsLocalization.lift_mk'_spec _ _ _ _
end Formalism.L2.Pj.GenSect
