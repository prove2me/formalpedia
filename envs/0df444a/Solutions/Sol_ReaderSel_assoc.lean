-- Prove2me | solution 1 for ReaderSel.assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:42.375798+00:00
-- url     : https://prove2.me/submissions/d281f09a-751c-4160-b7ae-765d4ad919ba

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ReaderMonad

set_option autoImplicit true
@[expose] public section
public section
universe u v w
namespace ReaderSel
theorem _root_.solution {ι : Type u} {α : Type v} {γ : Type w}
    (r : ReaderSel ι α γ)
    (f : γ → ReaderSel ι α γ) (g : γ → ReaderSel ι α γ) (a : α) :
    ((r.bind f).bind g).eval a = (r.bind (fun v => (f v).bind g)).eval a := rfl
end ReaderSel
