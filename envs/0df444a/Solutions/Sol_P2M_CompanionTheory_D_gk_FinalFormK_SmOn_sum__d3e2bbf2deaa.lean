-- Prove2me | solution 1 for P2M_CompanionTheory_D_gk_FinalFormK_SmOn_sum__d3e2bbf2deaa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:20:10.757967+00:00
-- url     : https://prove2.me/submissions/8dbe80e5-7709-4b29-b49f-e50a62ea26f4

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_SmoothOnAdditive_main__f00fdea2d781
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.FinalFormK
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.Poul
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Mat n → (H →L[ℂ] H)} {τ : Mat n → (H' →L[ℂ] H')}
variable {L : Mat n → Prop}
namespace CompanionTheory.D.gk.FinalFormK
namespace SmOn
theorem _root_.solution {E V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Set E} {f : ι → E → V} (s : Finset ι) (hf : ∀ i ∈ s, SmOn A (f i)) : SmOn A fun a => ∑ i ∈ s, f i a :=
  _root_.P2M_UpperTheory_Reformulated_B_SmoothOnAdditive_main__f00fdea2d781 s hf
end SmOn
end CompanionTheory.D.gk.FinalFormK
