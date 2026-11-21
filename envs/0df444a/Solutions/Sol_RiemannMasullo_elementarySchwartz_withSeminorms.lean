-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartz_withSeminorms
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:18:37.22224+00:00
-- url     : https://prove2.me/submissions/cebf734f-7f9c-41dc-9a35-2ad7176b7622

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L435-L436
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
theorem solution :
    WithSeminorms (E := ElementarySchwartz m n r F) elementarySchwartzSeminorm := by
  exact ⟨rfl⟩
