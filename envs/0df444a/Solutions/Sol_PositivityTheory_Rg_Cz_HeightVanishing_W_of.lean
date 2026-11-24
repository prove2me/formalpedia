-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.W_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:09.758816+00:00
-- url     : https://prove2.me/submissions/b9954f7d-7727-4ce9-a3e9-983a1306a05c

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
theorem _root_.solution {k k' : ℕ} {h h' : ℤ} {A : Module.End ℂ M} (hk : k ≤ k') (hh : h = h') (hA : A ∈ W E k h) :
    A ∈ W E k' h' := hh ▸ Submodule.span_mono (fun _ hx => by obtain ⟨w, h1, h2, h3⟩ := hx; exact ⟨w, h1.trans hk, h2, h3⟩) hA
end PositivityTheory.Rg.Cz.HeightVanishing
