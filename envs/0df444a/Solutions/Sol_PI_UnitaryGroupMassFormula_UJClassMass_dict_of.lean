-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.dict_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:56.412215+00:00
-- url     : https://prove2.me/submissions/eb2f09e4-be6e-41e3-9b12-2af89a7439f8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UJClassMassAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_coe_gmap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (s1 : LatStep) (si : IsomStep) (s2 : EquivStep) (s3 : InjStep) (s4 : SurjStep)
    (s5 : CardStep) : Dict := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig
  have S1 := s1 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig
  choose Λ hΛ using S1
  refine ⟨Λ, iotaG σ (gramOf h b) b, ⟨fun g => (hΛ g).2, si F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig,
    ?_, ?_, ?_, ?_⟩⟩
  · intro g γ k
    apply SetLike.coe_injective
    rw [coe_gmap, (hΛ g).1, (hΛ _).1]
    exact s2 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g γ k
  · intro g g' u hu hgm
    apply s3 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g g' u hu
    have e := congrArg (fun N : Submodule (𝓞 E) V => (N : Set V)) hgm
    simp only [coe_gmap] at e
    rwa [(hΛ g).1, (hΛ g').1] at e
  · intro N hN
    obtain ⟨g, hg⟩ := s4 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig N hN
    exact ⟨g, SetLike.coe_injective ((hΛ g).1.trans hg)⟩
  · intro g
    rw [s5 F E σ V h M b L0 hσ hθ hτ hs hnd hL hsig g]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
    show _ ∧ _ ↔ _ ∧ _
    rw [← (hΛ g).1, ← coe_gmap]
    exact and_congr Iff.rfl ⟨fun e => SetLike.coe_injective e, fun e => by rw [e]⟩
end PI.UnitaryGroupMassFormula.UJClassMass
