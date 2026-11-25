-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_UnitBallLemmas_intMv_inv__c1599895b530
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:25.387424+00:00
-- url     : https://prove2.me/submissions/027e38d8-f3c5-4311-9ee3-32710ec82914

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.UnitBallLemmas.intMv_inv
theorem _root_.solution.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv F →
        (MvPowerSeries.constantCoeff : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F = (1 : ℂ_[p]) →
          ∃ (G : MvPowerSeries σ ℂ_[p]), UpperTheory.Reformulated.B.UnitBallLemmas.IntegralMv G ∧ F * G = (1 : MvPowerSeries σ ℂ_[p]) := by
  intro p _ σ F hF h1
  let F' : MvPowerSeries σ (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p) :=
    fun n => ⟨MvPowerSeries.coeff n F, hF n⟩
  have hmap : MvPowerSeries.map (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p).subtype F' = F := by
    ext n
    rw [MvPowerSeries.coeff_map]
    rfl
  have hc : MvPowerSeries.constantCoeff F' = ((1 : (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p)ˣ) : UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p) := by
    apply Subtype.ext
    exact h1
  refine ⟨MvPowerSeries.map (UpperTheory.Reformulated.B.UnitBallLemmas.unitBall p).subtype (MvPowerSeries.invOfUnit F' 1), ?_, ?_⟩
  · intro n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n (MvPowerSeries.invOfUnit F' 1)).2
  · rw [← hmap, ← map_mul, MvPowerSeries.mul_invOfUnit F' 1 hc, map_one]
end UpperTheory.Reformulated.B.UnitBallLemmas.intMv_inv
