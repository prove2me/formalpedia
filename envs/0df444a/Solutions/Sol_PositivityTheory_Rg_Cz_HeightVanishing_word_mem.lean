-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.word_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:44.89081+00:00
-- url     : https://prove2.me/submissions/5f7edce5-5378-4e6c-a290-6ca901a42c34

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.HeightVanishing
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable (E : Fin n → Fin n → Module.End ℂ M)
namespace PositivityTheory.Rg.Cz.HeightVanishing
theorem _root_.solution {k : ℕ} {h : ℤ} (w : List (Fin n × Fin n)) (hk : w.length ≤ k) (hh : ht w = h) :
    word E w ∈ W E k h := Submodule.subset_span ⟨w, hk, hh, rfl⟩
end PositivityTheory.Rg.Cz.HeightVanishing
