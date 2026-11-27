-- Prove2me | solution 1 for SizeRamsey.Plan.hasC4_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:23.707831+00:00
-- url     : https://prove2.me/submissions/1ae392eb-bb32-49d4-96fc-239fcd0fb3ba

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ ⦃a b⦄,
      G.Adj a b → H.Adj (f a) (f b)) :
    HasC4 G → HasC4 H := by
  rintro ⟨g, hg, h01, h12, h23, h30⟩
  exact ⟨f ∘ g, hf.comp hg,
    hadj h01, hadj h12, hadj h23, hadj h30⟩
end SizeRamsey.Plan
