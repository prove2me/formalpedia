-- Prove2me | solution 1 for P2M_Formalism_RepresentationBoundsCohomology_LOC_mem_annih__37a7288d66f3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:37.4488+00:00
-- url     : https://prove2.me/submissions/ec868068-77bc-4a30-bf35-7e881cea125a

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_LocDualOrth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution {O A H : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup H] [Module O H]
    (pr : A →ₗ[O] H →ₗ[O] KO O) (M : Submodule O H) (x : A) :
    x ∈ annih pr M ↔ ∀ m ∈ M, pr x m = 0 := by
  simp only [annih, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
end Formalism.RepresentationBoundsCohomology.LOC
