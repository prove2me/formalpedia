-- Prove2me | solution 1 for WeierstrassEllipticZeta.philippon_subgroup_degree_profile
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T01:26:03.513839+00:00
-- url     : https://prove2.me/submissions/a2cef45f-8c6f-4bd1-b602-80ae2a952a21

import Definitions.Def_WeierstrassEllipticZeta_SubgroupCoordinateCases
import Theorems.Thm_WeierstrassEllipticZeta_philippon_connected_subgroup_classification
import Theorems.Thm_WeierstrassEllipticZeta_subgroup_degree_profile_of_paper_type
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
    ((M.pullbackSubmodule H = ⊥) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        1 ≤ hilbertDegreeForm M.group H.carrier ![m, n]) ∨
    ((M.pullbackSubmodule H ≤ L.lattice) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
        (m : ℝ) ≤ hilbertDegreeForm M.group H.carrier ![m, n]) := by
  exact WeierstrassEllipticZeta.subgroup_degree_profile_of_paper_type
    L D S hS hS_value hS_ne M H
    (WeierstrassEllipticZeta.philippon_connected_subgroup_classification
      L D S hS hS_value hS_ne M H hH hproper)
