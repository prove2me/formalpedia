-- Prove2me | solution 1 for RingHom.eq_of_forall_exists_sub_mem_pow_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/76b7b13e-e147-5b37-9032-31dcda32c163

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_eq_of_forall_exists_sub_mem_pow_of_comp_eq

set_option autoImplicit false

theorem solution
    (R Rh S : Type) [CommRing R] [CommRing Rh] [CommRing S]
    (ι : R →+* Rh) (I : Ideal Rh)
    (hdense : ∀ (x : Rh) (n : ℕ), ∃ r : R, x - ι r ∈ I ^ n)
    (J : Ideal S) [IsHausdorff J S]
    (G H : Rh →+* S) (hG : ∀ x ∈ I, G x ∈ J) (hH : ∀ x ∈ I, H x ∈ J)
    (h : G.comp ι = H.comp ι) :
    G = H := by
  have hGn : ∀ (n : ℕ) (x : Rh), x ∈ I ^ n → G x ∈ J ^ n := by
    intro n x hx
    have h1 : Ideal.map G (I ^ n) ≤ J ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun y hy => hG y hy) n
    exact h1 (Ideal.mem_map_of_mem G hx)
  have hHn : ∀ (n : ℕ) (x : Rh), x ∈ I ^ n → H x ∈ J ^ n := by
    intro n x hx
    have h1 : Ideal.map H (I ^ n) ≤ J ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun y hy => hH y hy) n
    exact h1 (Ideal.mem_map_of_mem H hx)
  refine RingHom.ext fun x => ?_
  rw [← sub_eq_zero]
  refine IsHausdorff.haus ‹IsHausdorff J S› (G x - H x) fun n => ?_
  obtain ⟨r, hr⟩ := hdense x n
  have hGH : G (ι r) = H (ι r) := by
    have := congrArg (fun f : R →+* S => f r) h
    simpa using this
  have hrew : G x - H x = G (x - ι r) - H (x - ι r) := by
    simp only [map_sub, hGH]; ring
  rw [hrew, SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.sub_mem _ (hGn n _ hr) (hHn n _ hr)

end S_RingHom_eq_of_forall_exists_sub_mem_pow_of_comp_eq
end P2MW
export P2MW.S_RingHom_eq_of_forall_exists_sub_mem_pow_of_comp_eq (solution)
