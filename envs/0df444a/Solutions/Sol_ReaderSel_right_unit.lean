-- Prove2me | solution 1 for ReaderSel.right_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:35.826163+00:00
-- url     : https://prove2.me/submissions/697fdb6e-084b-4534-b148-7aabc9b6834e

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ReaderMonad

set_option autoImplicit true
@[expose] public section
public section
universe u v w
namespace ReaderSel
theorem _root_.solution {ι : Type u} {α : Type v} {γ : Type w}
    (r : ReaderSel ι α γ) (i₀ : ι) (a : α) :
    (r.bind (fun v => ReaderSel.pure i₀ (fun _ => v))).eval a = r.eval a := rfl
end ReaderSel
