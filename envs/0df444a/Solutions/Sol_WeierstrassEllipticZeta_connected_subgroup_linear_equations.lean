-- Prove2me | solution 1 for WeierstrassEllipticZeta.connected_subgroup_linear_equations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T03:26:55.271423+00:00
-- url     : https://prove2.me/submissions/e0c7d874-8836-4aaa-ab67-1504cd546d84

import Theorems.Thm_WeierstrassEllipticZeta_analytic_additive_identity_component
import Theorems.Thm_WeierstrassEllipticZeta_exponentialPreimage_finite_entire_equations
import Theorems.Thm_WeierstrassEllipticZeta_subgroup_exponential_preimage_additive
import Theorems.Thm_WeierstrassEllipticZeta_connected_subgroup_exponential_component_equations
import Definitions.Def_WeierstrassEllipticZeta_ExponentialPreimage
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity

noncomputable section
namespace WeierstrassEllipticZeta
open PhilipponApplication
theorem linear_equations_of_exponential_preimage_geometry
    (S : Fin 5 → ℂ → ℂ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hadditive : ∃ K : AddSubgroup (Fin 3 → ℂ),
      (K : Set (Fin 3 → ℂ)) = M.exponentialPreimage H)
    (hcomponent : M.HasParametricEquations H
      (fun v : connectedComponentIn (M.exponentialPreimage H) 0 =>
        exponentialCoordinates S v.val)) :
    M.HasLinearSubgroupEquations H := by
  obtain ⟨K, hK⟩ := hadditive
  obtain ⟨F, hF, hzero⟩ := exponentialPreimage_finite_entire_equations S hS M H
  have hzeroK (v) : v ∈ K ↔ ∀ f ∈ F, f v = 0 := by
    change v ∈ (K : Set (Fin 3 → ℂ)) ↔ _
    rw [hK]
    exact hzero v
  obtain ⟨V, hV⟩ := analytic_additive_identity_component K F hF hzeroK
  rw [hK] at hV
  refine ⟨V, fun Q m n hQ => ?_⟩
  rw [hcomponent Q m n hQ]
  constructor
  · intro h v
    exact h ⟨v.val, by rw [← hV]; exact v.property⟩
  · intro h v
    exact h ⟨v.val, by
      change v.val ∈ (V : Set (Fin 3 → ℂ))
      rw [hV]
      exact v.property⟩

end WeierstrassEllipticZeta
end
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
    M.HasLinearSubgroupEquations H := by
  exact WeierstrassEllipticZeta.linear_equations_of_exponential_preimage_geometry S hS M H
    (WeierstrassEllipticZeta.subgroup_exponential_preimage_additive L D S hS hS_value hS_ne M H)
    (WeierstrassEllipticZeta.connected_subgroup_exponential_component_equations
      L D S hS hS_value hS_ne M H hH hproper)
