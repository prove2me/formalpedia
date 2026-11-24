-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.W_ind
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:25.595643+00:00
-- url     : https://prove2.me/submissions/77af0442-bb70-4856-8a9b-cbca46d578fc

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
theorem _root_.solution {k : ℕ} {h : ℤ} {p : Module.End ℂ M → Prop} (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y))
    (hsm : ∀ (c : ℂ) x, p x → p (c • x)) (hw : ∀ w : List (Fin n × Fin n), w.length ≤ k → ht w = h → p (word E w))
    {A : Module.End ℂ M} (hA : A ∈ W E k h) : p A := by
  induction hA using Submodule.span_induction with
  | mem x hx => obtain ⟨w, h1, h2, rfl⟩ := hx; exact hw w h1 h2
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsm c x hx
end PositivityTheory.Rg.Cz.HeightVanishing
