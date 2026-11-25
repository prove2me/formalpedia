-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_c2x4_ut_inv_super__b4a875ff4b5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:12.871093+00:00
-- url     : https://prove2.me/submissions/fcac8bba-84f6-4495-aede-793f4af1f49b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_inv_super


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (a b : Fin m)
    (hb : b.val = a.val + 1) : u⁻¹ a b = -u a b := by
  obtain ⟨bv, hbv⟩ := b
  simp only at hb
  subst hb
  exact C2x2.ut_inv_super hu a hbv
end Formalism.FourierDecayAlt.P
