-- Prove2me | solution 1 for ReaderSel.left_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:31.980847+00:00
-- url     : https://prove2.me/submissions/0cb478ae-cea6-4080-ae48-c05177732840

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ReaderMonad

set_option autoImplicit true
@[expose] public section
public section
universe u v w
namespace ReaderSel
theorem _root_.solution {ι : Type u} {α : Type v} {γ : Type w}
    (i₀ : ι) (f : α → γ)
    (g : γ → ReaderSel ι α γ) (a : α) :
    (ReaderSel.pure i₀ f |>.bind g).eval a = (g (f a)).eval a := rfl
end ReaderSel
