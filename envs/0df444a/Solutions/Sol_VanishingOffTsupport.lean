-- Prove2me | solution 1 for VanishingOffTsupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:09:49.67752+00:00
-- url     : https://prove2.me/submissions/50998cc9-b02a-42f8-9197-8c047976e2a5

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_VanishingOffTsupport

set_option autoImplicit false

theorem _root_.solution :
    (∀ (f : Plane → ℝ) (x : Plane), x ∉ tsupport f → f x = 0)
      ∧ (∀ (f : Plane → ℝ) (x : Plane), x ∉ tsupport f → gradient f x = 0) := by
  refine ⟨fun f x hx => image_eq_zero_of_notMem_tsupport hx, ?_⟩
  intro f x hx
  have hev : f =ᶠ[nhds x] fun _ : Plane => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hx
  rw [hev.gradient_eq, gradient_fun_const]
