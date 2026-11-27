-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:25:20.238805+00:00
-- url     : https://prove2.me/submissions/987f0544-d8e6-460e-9fb6-5d862f1f5d83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__eq_zero_of_monic_0a863602de4b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_HG_eval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_dehomogenized_generator_eval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_P_ne_one

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
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ}
variable {x : ι → Ω} {e : Fin (D + 1) → ι}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
namespace Gen
theorem _root_.solution [DecidableEq ι] (G : Gen x e) (w : Fin (D + 1) → ℂ)
    (hker : ∀ m, deh (x ∘ e) 0 m = 0 → deh w 0 m = 0) (hdw : deh w 0 G.dd ≠ 0)
    {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0) {F : MvPolynomial ι ℤ}
    {H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)}
    (h : deh x (e 0) F = H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) (G.evQ (deh w 0) ρ) F = H.eval₂ (deh w 0) ρ := by
  have key := eval₂_eq_zero_of_monic (deh (x ∘ e) 0) (deh w 0) hker G.monic G.min G.root hρ
    G.P_ne_one (H := G.HG F - Polynomial.C (G.dd ^ F.totalDegree) * H) (by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, G.HG_eval _ _ G.dd_ne,
        G.dehomogenized_generator_eval, ← deh_apply, h, map_pow, sub_self])
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, G.HG_eval _ _ hdw, map_pow,
    ← mul_sub, mul_eq_zero] at key
  exact sub_eq_zero.mp (key.resolve_left (pow_ne_zero _ hdw))
end Gen
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
