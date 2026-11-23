-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_vge_sum__98181df79b27
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:43.474026+00:00
-- url     : https://prove2.me/submissions/e911c117-d65f-44a2-a755-0ffcccdb01c3

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_UpperTheory_Reformulated_B_Qh31_vge_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {ι : Type} {a : ℝ} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, vge v a (f i)) :
    vge v a (∑ i ∈ s, f i) := by
  first | exact UpperTheory.Reformulated.B.Qh31.vge_sum .. | (apply UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh31.vge_sum <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a s f h | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a s f | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a s | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι a | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v ι | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› v | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K ‹_› | exact @UpperTheory.Reformulated.B.Qh31.vge_sum K
end Formalism.MainNotions.PlaneGram
