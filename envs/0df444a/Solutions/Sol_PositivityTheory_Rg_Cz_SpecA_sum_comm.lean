-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.sum_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:40.193366+00:00
-- url     : https://prove2.me/submissions/f8d0b40f-4578-4adf-b21e-99e4f96e3af1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_dvd_prod_shift_sub_prod
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}
namespace PositivityTheory.Rg.Cz.SpecA
theorem _root_.solution {R : Type*} [CommRing R] [Algebra ℂ R] (A B : R) (α β : ℂ) (La Lb : List ℕ)
    (hA : (La.map fun a : ℕ => A - algebraMap ℂ R (α + a)).prod = 0)
    (hB : (Lb.map fun b : ℕ => B - algebraMap ℂ R (β + b)).prod = 0) :
    ((La.flatMap fun a => Lb.map (a + ·)).map fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)).prod = 0 := by
  set x : ℕ → R := fun a => A - algebraMap ℂ R (α + a) with hx
  set y : ℕ → R := fun b => B - algebraMap ℂ R (β + b) with hy
  have hA' : (La.map x).prod = 0 := hA
  have hB' : (Lb.map y).prod = 0 := hB
  have hterm : ∀ a b : ℕ, A + B - algebraMap ℂ R (α + β + ((a + b : ℕ) : ℂ)) = x a + y b := by
    intro a b
    simp only [hx, hy]
    push_cast
    ring
  have key : ∀ L : List ℕ, ∃ u v : R,
      ((L.flatMap fun a => Lb.map (a + ·)).map fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)).prod =
        u * (L.map x).prod + v * (Lb.map y).prod := by
    intro L
    induction L with
    | nil => exact ⟨1, 0, by simp⟩
    | cons a L ih =>
      obtain ⟨u, v, huv⟩ := ih
      obtain ⟨c, hc⟩ := dvd_prod_shift_sub_prod (x a) (Lb.map y)
      have h1 : ((Lb.map (a + ·)).map fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)).prod =
          x a * c + (Lb.map y).prod := by
        rw [← hc, List.map_map, List.map_map]
        have hm : ((fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)) ∘ (a + ·)) =
            ((x a + ·) ∘ y) := by
          funext b
          exact hterm a b
        rw [hm]
        ring
      refine ⟨c * u, (x a * c + (Lb.map y).prod) * v + u * (L.map x).prod, ?_⟩
      rw [List.flatMap_cons, List.map_append, List.prod_append, huv, h1]
      simp only [List.map_cons, List.prod_cons]
      ring
  obtain ⟨u, v, huv⟩ := key La
  rw [huv, hA', hB']
  ring
end PositivityTheory.Rg.Cz.SpecA
