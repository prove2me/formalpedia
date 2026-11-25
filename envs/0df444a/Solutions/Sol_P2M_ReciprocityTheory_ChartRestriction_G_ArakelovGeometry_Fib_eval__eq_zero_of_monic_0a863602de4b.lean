-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__eq_zero_of_monic_0a863602de4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:46.135124+00:00
-- url     : https://prove2.me/submissions/b74e1be3-4d59-4a66-8b30-9d54f2216443

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : R →+* T) (hker : ∀ m, φ m = 0 → ψ m = 0) {P : Polynomial R}
    (hP : P.Monic) {θ : S} {ρ : T}
    (hmin : ∀ H : Polynomial R, H.natDegree < P.natDegree → H.eval₂ φ θ = 0 →
      ∀ j, φ (H.coeff j) = 0)
    (hθ : P.eval₂ φ θ = 0) (hρ : P.eval₂ ψ ρ = 0) (hP1 : P ≠ 1) {H : Polynomial R}
    (hH : H.eval₂ φ θ = 0) : H.eval₂ ψ ρ = 0 := by
  have hdec := Polynomial.modByMonic_add_div H P
  have h1 : (H %ₘ P).eval₂ φ θ = 0 := by
    have := congrArg (Polynomial.eval₂ φ θ) hdec
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, hθ, zero_mul, add_zero, hH] at this
    exact this
  have h2 := hmin _ (Polynomial.natDegree_modByMonic_lt H hP hP1) h1
  have h3 : (H %ₘ P).eval₂ ψ ρ = 0 := by
    rw [← Polynomial.eval_map]
    have : (H %ₘ P).map ψ = 0 := by
      ext j; rw [Polynomial.coeff_map, hker _ (h2 j), Polynomial.coeff_zero]
    rw [this, Polynomial.eval_zero]
  rw [← hdec, Polynomial.eval₂_add, Polynomial.eval₂_mul, hρ, zero_mul, add_zero, h3]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
