-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.PullbackHopfOrder.sqIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:32:34.759137+00:00
-- url     : https://prove2.me/submissions/4c68fc9a-d264-4511-b33e-6e4935a81d71

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_MemAugIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.PullbackHopfOrder
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder
theorem _root_.solution {X Y : Type} (F : (X → C) →ₗ[R] (Y → C))
    (hF : ∀ f g, F (f * g) = F f * F g) {I : Submodule R (X → C)} {J : Submodule R (Y → C)}
    (hIJ : ∀ f ∈ I, F f ∈ J) : sqIdeal I ≤ (sqIdeal J).comap F := by
  refine Submodule.span_le.2 ?_
  rintro h ⟨f, hf, f', hf', rfl⟩
  show F (f * f') ∈ sqIdeal J
  rw [hF]
  exact Submodule.subset_span ⟨_, hIJ f hf, _, hIJ f' hf', rfl⟩
end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
