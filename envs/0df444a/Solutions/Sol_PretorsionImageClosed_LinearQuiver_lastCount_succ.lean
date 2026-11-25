-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.lastCount_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:04:24.134386+00:00
-- url     : https://prove2.me/submissions/74d5f8fd-59d0-4541-a839-5053af6d1731

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {m : ℕ} (D : IntervalFamily (m + 1)) :
    D.lastCount = (univ.filter (fun a : Fin (m + 1) => (a, Fin.last m) ∈ D.D)).card := by
  unfold IntervalFamily.lastCount
  refine Finset.card_bij' (fun p _ => p.1) (fun a _ => (a, Fin.last m)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : p.2 = Fin.last m := Fin.ext (by rw [Fin.val_last]; omega)
    rw [← this]
    exact hp1
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.2, by simp⟩
  · intro p hp
    obtain ⟨-, hp2⟩ := Finset.mem_filter.1 hp
    have : p.2 = Fin.last m := Fin.ext (by rw [Fin.val_last]; omega)
    exact Prod.ext rfl this.symm
  · intro a _
    rfl
end PretorsionImageClosed.LinearQuiver
