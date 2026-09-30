-- Prove2me | solution 1 for WeierstrassEllipticZeta.philippon_model_realization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-24T05:01:38.038509+00:00
-- url     : https://prove2.me/submissions/ccefd470-e8d6-4211-9328-47de8edaab6c

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_group_geometry
import Theorems.Thm_WeierstrassEllipticZeta_projective_extension_group_with_regular_operations
import Theorems.Thm_WeierstrassEllipticZeta_philippon_model_from_regular_extension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    Nonempty (Model S) := by
  obtain ⟨η, hη, _⟩ := elliptic_extension_group_geometry L
  obtain ⟨group, e, he, hadd, hneg⟩ :=
    projective_extension_group_with_regular_operations L D S hS hS_value hS_ne η hη
  letI := group
  exact philippon_model_from_regular_extension L D S hS hS_value hS_ne η hη e he hadd hneg
