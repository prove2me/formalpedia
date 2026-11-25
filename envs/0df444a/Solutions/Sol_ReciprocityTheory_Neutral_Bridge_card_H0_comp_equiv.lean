-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.card_H0_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:26:07.931195+00:00
-- url     : https://prove2.me/submissions/a856712d-cda6-4ddc-92a6-39946e6d3089

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_Transport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open ReciprocityTheory.Gal
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
namespace ReciprocityTheory.Neutral.Bridge
theorem _root_.solution (e : G ≃ₜ* G') (rho : Representation R G' M) :
    Nat.card (H0 (rho.comp (e : G →* G'))) = Nat.card (H0 rho) := by
  have hinv : Representation.invariants (rho.comp (e : G →* G')) = rho.invariants := by
    ext v
    simp only [Representation.mem_invariants, MonoidHom.comp_apply]
    constructor
    · intro h g'
      simpa using h (e.symm g')
    · intro h g
      exact h _
  unfold H0
  rw [hinv]
end ReciprocityTheory.Neutral.Bridge
