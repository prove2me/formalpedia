-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P50.gauge_cocycle_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:15:10.092379+00:00
-- url     : https://prove2.me/submissions/5b0890aa-06b2-45fe-93b1-3c8f8d837a6e

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P50
noncomputable section

open QAlgorithms.Papers.Independent.Claimed50.P50

open scoped TensorProduct BigOperators

variable {H N : Type*}

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]

theorem solution {G : Type*} [Group G]
    (F : G → NoiseGauge N) (hOne : F 1 = gaugeIdentity)
    (hMul : ∀ gp g, F (gp * g) = gaugeMul (F gp) (F g)) :
    (F 1).Dnoise = LinearIsometryEquiv.refl ℂ N ∧
    (F 1).a = 0 ∧ (F 1).b = 0 ∧
    ∀ gp g,
      (F (gp * g)).Dnoise = (F g).Dnoise.trans (F gp).Dnoise ∧
      (F (gp * g)).a = (F gp).Dnoise (F g).a + (F gp).a ∧
      (F gp).b + (F g).b - (F (gp * g)).b =
        (inner ℂ (F gp).a ((F gp).Dnoise (F g).a)).im := by
  refine ⟨by rw [hOne]; rfl, by rw [hOne]; rfl, by rw [hOne]; rfl, fun gp g => ?_⟩
  rw [hMul]
  refine ⟨rfl, rfl, ?_⟩
  simp only [gaugeMul]
  ring

end
