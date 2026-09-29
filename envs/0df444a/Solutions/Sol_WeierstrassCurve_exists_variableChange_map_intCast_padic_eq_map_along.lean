-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_map_intCast_padic_eq_map_along
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/52289588-8897-543d-a1b9-e41c768e4a63

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_map_intCast_padic_eq_map_along

set_option maxHeartbeats 3200000

open scoped WeierstrassCurve.Affine in
theorem solution
    (R : Type) [CommRing R] [IsDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (E : WeierstrassCurve ℚ) (W₀ : WeierstrassCurve R) (heq : W₀⁄ℚ = E)
    {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] (f : R →+* ℤ_[p])
    (hfc : ∀ r : R, ((f r : ℤ_[p]) : ℚ_[p]) = (algebraMap ℚ ℚ_[p]) (algebraMap R ℚ r)) :
    ∃ C : WeierstrassCurve.VariableChange ℚ_[p],
      C • ((W₀.map f)⁄ℚ_[p]) = W.map (Int.castRingHom ℚ_[p]) := by
  obtain ⟨C₀, hC₀⟩ := hW
  refine ⟨C₀.map (algebraMap ℚ ℚ_[p]), ?_⟩
  have hcomp : (algebraMap ℤ_[p] ℚ_[p]).comp f = (algebraMap ℚ ℚ_[p]).comp (algebraMap R ℚ) := by
    ext r; simpa using hfc r
  have h1 : (W₀.map f)⁄ℚ_[p] = E.map (algebraMap ℚ ℚ_[p]) := by
    show (W₀.map f).map (algebraMap ℤ_[p] ℚ_[p]) = E.map (algebraMap ℚ ℚ_[p])
    rw [WeierstrassCurve.map_map, hcomp, ← WeierstrassCurve.map_map, ← heq]
    rfl
  have h2 : W.map (Int.castRingHom ℚ_[p]) =
      (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[p]) := by
    rw [WeierstrassCurve.map_map]; rfl
  rw [h1, h2, ← hC₀]
  exact WeierstrassCurve.map_variableChange (C := C₀) (W := E) (φ := algebraMap ℚ ℚ_[p])

end S_WeierstrassCurve_exists_variableChange_map_intCast_padic_eq_map_along
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_map_intCast_padic_eq_map_along (solution)
