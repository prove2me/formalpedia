-- Prove2me | solution 1 for SONATA.Undir.eq_19
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:04:55.500747+00:00
-- url     : https://prove2.me/submissions/8fca706b-ff21-4765-a97e-1824f2910a2a

import Mathlib
import Definitions.Def_SONATA_Undir_Network
import Definitions.Def_SONATA_Undir_Setting

open SONATA.Undir in
theorem solution
    {m d : ℕ} {K O : Set (E d)} {f : Fin m → E d → ℝ} {G : E d → ℝ} {μ L : ℝ}
    {ft : Fin m → E d → E d → ℝ} {μt Lt Dl Du : Fin m → ℝ} {Gr : SimpleGraph (Fin m)}
    {W : Matrix (Fin m) (Fin m) ℝ} {xstar : E d}
    (hS : Standing K O f G μ L ft μt Lt Dl Du Gr W xstar)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {x y xh : ℕ → Stack m d}
    (hrun : IsRun K f G ft W α x y xh) :
    ∀ ν, avg (y ν) = (m : ℝ)⁻¹ • ∑ i, gradient (f i) (x ν i) := by
  have key : ∀ ν, ∑ i, y ν i = ∑ i, gradient (f i) (x ν i) := by
    intro ν
    induction ν with
    | zero => exact Finset.sum_congr rfl (fun i _ => hrun.init_y i)
    | succ k ih =>
      have h1 : ∑ i, y (k + 1) i
          = ∑ j, (y k j + gradient (f j) (x (k + 1) j) - gradient (f j) (x k j)) := by
        simp only [hrun.tracking]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Finset.sum_smul, hS.D.col_sum j, one_smul]
      rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ih]
      abel
  intro ν
  unfold avg
  rw [key ν]
