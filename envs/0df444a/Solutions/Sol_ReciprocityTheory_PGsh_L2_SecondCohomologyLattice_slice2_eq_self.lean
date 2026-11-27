-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.slice2_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:32:00.548548+00:00
-- url     : https://prove2.me/submissions/3e8f83ef-9d11-41d8-bfc0-61d8d08981fb

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
theorem _root_.solution {X : Type} (E : (X → C) →ₗ[C] (X → C)) (W : Submodule C (X → C))
    (hE : ∀ f ∈ W, E f = f) (F : X × X → C) (h1 : ∀ a, (fun b => F (a, b)) ∈ W)
    (h2 : ∀ y, (fun a => F (a, y)) ∈ W) : slice2 E F = F := by
  funext p
  show E (fun a => E (fun b => F (a, b)) p.2) p.1 = F p
  have h3 : (fun a => E (fun b => F (a, b)) p.2) = fun a => F (a, p.2) := by
    funext a
    rw [hE _ (h1 a)]
  rw [h3, hE _ (h2 p.2)]
end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
