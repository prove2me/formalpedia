-- Prove2me | solution 1 for QnRdSkewW.glev_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:06:19.403574+00:00
-- url     : https://prove2.me/submissions/124494b9-98f2-4bb0-85d8-29d2dd5b7ef7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_SkewReductionGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
namespace QnRdSkewW
theorem _root_.solution (k r : ℕ) (i : Fin (r + 1)) : IsClosed (Glev k r i) := by
  have e : Glev k r i = {g : Mx k r | gᴴ * Hpk k r * g = Hpk k r} ∩
      ⋂ a : Fin r, ⋂ (_ : a.val < i.val),
        ({g : Mx k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {g : Mx k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)}) := by
    ext g
    simp only [Glev, UH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun _ => IsClosed.inter ?_ ?_)
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  · exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
end QnRdSkewW
