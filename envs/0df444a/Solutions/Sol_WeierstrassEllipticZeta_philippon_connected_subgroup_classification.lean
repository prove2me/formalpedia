-- Prove2me | solution 1 for WeierstrassEllipticZeta.philippon_connected_subgroup_classification
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T02:05:47.55134+00:00
-- url     : https://prove2.me/submissions/34e8da1c-ea78-4450-8e64-a8735d59ceec

import Theorems.Thm_WeierstrassEllipticZeta_connected_subgroup_linear_equations
import Theorems.Thm_WeierstrassEllipticZeta_subgroup_paper_type_of_linear_equations
import Definitions.Def_WeierstrassEllipticZeta_SubgroupLinearization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hH : H.IsConnected) (hproper : H.carrier ≠ Set.univ) :
    M.HasPaperSubgroupType L H := by
  exact WeierstrassEllipticZeta.subgroup_paper_type_of_linear_equations L D S hS hS_value hS_ne M H hproper
    (WeierstrassEllipticZeta.connected_subgroup_linear_equations L D S hS hS_value hS_ne M H hH hproper)
