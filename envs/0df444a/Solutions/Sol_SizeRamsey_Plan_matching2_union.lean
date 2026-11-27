-- Prove2me | solution 1 for SizeRamsey.Plan.matching2_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:34.588583+00:00
-- url     : https://prove2.me/submissions/a8404336-9db0-4b3a-8b03-340c9dadf5fe

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution {V W : Type*}
    {G H : SimpleGraph V} {F : SimpleGraph W}
    (i j : V → W)
    (hi : Function.Injective i)
    (hj : Function.Injective j)
    (hdis : ∀ a b, i a ≠ j b)
    (hG : ∀ ⦃a b⦄,
      G.Adj a b → F.Adj (i a) (i b))
    (hH : ∀ ⦃a b⦄,
      H.Adj a b → F.Adj (j a) (j b)) :
    HasMatching2 G → HasMatching2 H → HasMatching4 F := by
  rintro ⟨f, hf, hf01, hf23⟩ ⟨g, hg, hg01, hg23⟩
  have hdis' : ∀ a b, j b ≠ i a := fun a b h => hdis a b h.symm
  refine ⟨![i (f 0), i (f 1), i (f 2), i (f 3), j (g 0), j (g 1), j (g 2), j (g 3)],
    ?_, by simpa using hG hf01, by simpa using hG hf23, by simpa using hH hg01,
    by simpa using hH hg23⟩
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp_all [hi.eq_iff, hj.eq_iff, hf.eq_iff, hg.eq_iff]
end SizeRamsey.Plan
