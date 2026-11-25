-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_EichlerDense_continuous_eich_25adfc1992d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:47.967669+00:00
-- url     : https://prove2.me/submissions/c3f342b8-721b-4cc8-a39f-eb47fd97346f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PEichlerDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
variable {X : Type*} [TopologicalSpace X] {S : Type*} [CommRing S] [TopologicalSpace S]
  [IsTopologicalRing S] {N : ℕ} {σ : S →+* S}
namespace GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
theorem _root_.solution (hσ : Continuous σ) (J : Matrix (Fin N) (Fin N) S) (e : Fin N → S)
    {g : X → Fin N → S} {k : X → S} (hg : Continuous g) (hk : Continuous k) :
    Continuous fun t => eich σ J e (g t) (k t) := by
  have hσg : Continuous fun t => σ ∘ g t :=
    continuous_pi fun i => hσ.comp ((continuous_apply i).comp hg)
  unfold eich
  fun_prop
end GroundTheory.Heights₂.Heights.StrongApprox.EichlerDense
