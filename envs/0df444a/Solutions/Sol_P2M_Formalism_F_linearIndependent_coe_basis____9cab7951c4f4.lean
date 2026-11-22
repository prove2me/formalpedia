-- Prove2me | solution 1 for P2M_Formalism_F_linearIndependent_coe_basis____9cab7951c4f4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:21:57.352273+00:00
-- url     : https://prove2.me/submissions/87b8a8a0-36d1-484c-8a36-360765940eb6

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) := by
  classical
  have hs : Submodule.span ℤ (Set.range fun i => (b i : E)) = L := by
    have h1 : (Set.range fun i => (b i : E)) = L.subtype '' Set.range b := Set.range_comp L.subtype b
    rw [h1, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hd : DiscreteTopology (Submodule.span ℤ (Set.range fun i => (b i : E))) := by
    rw [hs]; infer_instance
  rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hd]
  unfold Set.finrank
  rw [hs, Module.finrank_eq_card_basis b]
end Formalism.F
