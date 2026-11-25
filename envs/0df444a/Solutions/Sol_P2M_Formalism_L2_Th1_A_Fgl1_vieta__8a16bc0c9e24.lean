-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_A_Fgl1_vieta__8a16bc0c9e24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:51:24.274816+00:00
-- url     : https://prove2.me/submissions/bf9c67e1-3981-461b-9b1d-1f8cb629e249

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Fgl1
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
open Formalism.ELL.WeierstrassChordSeries
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution {A : Type*} [CommRing A] {a1 a2 a3 a4 a6 l n z1 z2 z3 : A}
    (hz : ∀ f : A, f * (z1 - z2) = 0 → f = 0)
    (h1 : G a1 a2 a3 a4 a6 z1 (l * z1 + n) = 0) (h2 : G a1 a2 a3 a4 a6 z2 (l * z2 + n) = 0)
    (he1 : c3 a2 a4 a6 l * (z1 + z2 + z3) + c2 a1 a2 a3 a4 a6 l n = 0) :
    G a1 a2 a3 a4 a6 z3 (l * z3 + n) = 0 := by
  have hQ : (c3 a2 a4 a6 l * (z1 ^ 2 + z1 * z2 + z2 ^ 2) + c2 a1 a2 a3 a4 a6 l n * (z1 + z2) +
      (a1 * n + 2 * a3 * l * n + a4 * n ^ 2 + 3 * a6 * l * n ^ 2 - l)) * (z1 - z2) = 0 := by
    unfold G at h1 h2
    unfold c3 c2
    linear_combination h1 - h2
  have hQ0 := hz _ hQ
  unfold G at h1 ⊢
  unfold c3 c2 at hQ0 he1
  linear_combination h1 + (z3 - z1) * hQ0 + (z3 - z1) * (z3 - z2) * he1
end Formalism.L2.Th1.A.Fgl1
