-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceLinearCycleFamily6814.checked_linear_owner_cycle_yukon_a79265a7855b
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-04T01:01:46.825296+00:00
-- url     : https://prove2.me/submissions/914aad62-6503-426a-b0d2-34ac1ac1a0b9

import Definitions.Def_Yukon_42e09cdac02be46bc4db2213



import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_755f5ab5e1dfa660f8e11f09
import Definitions.Def_Yukon_470e6b3ad95913c90c8c44d8
import Definitions.Def_Yukon_4eb9e7e98149c44e25409e85
import Definitions.Def_Yukon_89b17c85954a108661049f02
import Definitions.Def_Yukon_4f316b5d60b209d4b31c20b9
import Definitions.Def_Yukon_1bcd4c4ffdf14561f9186504
import Definitions.Def_Yukon_cfd2e7e9b4a5d9c97487b438
import Definitions.Def_Yukon_1f886e14a1fc29f50d6a3d3c
import Definitions.Def_Yukon_ca06e00072579899a61b0098
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingSourceReducedGamma6814
end MovingSourceReducedGamma6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceReducedCycle6814
end MovingSourceReducedCycle6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceFlowNumerator6814
end MovingSourceFlowNumerator6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN313
end RCN313
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN249
end RCN249
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN245
end RCN245
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN244
end RCN244
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN086
end RCN086
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN074
end RCN074
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN136
end RCN136
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN135
end RCN135
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceGammaProjections6814
end MovingSourceGammaProjections6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourcePrimeFamily6814
end MovingSourcePrimeFamily6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceProjectionFamily6814
end MovingSourceProjectionFamily6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN125
end RCN125
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN117
end RCN117
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN116
end RCN116
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN093
end RCN093
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN042
end RCN042
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN022
end RCN022
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceLinearCycleFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators
open RCN002 RCN022 RCN042 RCN093 RCN095 RCN116 RCN117 RCN125
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814
open MovingSourceGammaProjections6814
open RCN135 RCN136 RCN074 RCN086 RCN244 RCN245 RCN249 RCN313
open MovingSourceFlowNumerator6814 MovingSourceReducedCycle6814 MovingSourceReducedGamma6814
variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
/-- Checked-cell specialization consumes the actual exhaustive owner's
LinearRoute. Its recurrence, first-tail support, projection construction,
and all three weighted resultant inequalities are supplied, not assumed. -/
theorem _root_.solution
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    [Fact (Irreducible S.F)] (hp : p=2130706433)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K))
    (hroute : MovingSourceReducedRoutes6814.LinearRoute S.F J)
    (hH : ¬S.G∣surfaceMap (polynomialEmbedding K) (MovingSourceLinearFlow6814.linearH J))
    {A : Type} [Fintype A] (component : A → FirstTailComponent S)
    (hinj : Function.Injective component)
    (hz : ∀ a, Transcendental (GenericField K) (coordinate (GenericField K) (component a).1 2))
    (hS : RCN095.PolynomialInFlag ⟨3504,45,12⟩ S.G) :
    ∃ D : GammaFrame (fun a => (component a).1) S.G, ∀ axis : Axis,
      (∑ a, localMultiplicity S (canonicalLocalDVRFamily S hfirst) (component a)*frameCost D hz axis a) ≤
        flagMixed ⟨3504,45,12⟩ reducedFirstFlag axis.flag  := by
  have hs : flagMixed ⟨3504,45,12⟩ reducedFirstFlag unitZFlag<p := by
    rw [hp]
    exact checked_gamma_budget.2
  exact exists_reduced_cycle_family S hfirst
    (MovingSourceLinearFlow6814.linearH J) (MovingSourceLinearFlow6814.linearG J)
    (hroute.2.2.2.2 (RCN326.w+1)).1 hH component hinj hz
    ⟨3504,45,12⟩ reducedFirstFlag hS (reducedFirstFlag_of_route S.F J hroute) hs
end
end MovingSourceLinearCycleFamily6814
end SubmissionLower
end ProximityPrize
