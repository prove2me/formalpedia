-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.zOf_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:07.460309+00:00
-- url     : https://prove2.me/submissions/eb861ac4-1ee1-43de-be20-5042f8a127bc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}
variable [DecidableEq ι] (G : Gen x e) {w : Fin (D + 1) → ℂ}
private theorem eval₂_deh_eq_zero_of_good_of_root (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0)
    (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ))
    (hH : H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0) : H.eval₂ (deh w 0) ρ = 0 := by
  have hP1 : G.P ≠ 1 := by
    intro h
    have h' := G.root
    rw [h, Polynomial.eval₂_one] at h'
    exact one_ne_zero h'
  have hsplit : H %ₘ G.P + G.P * (H /ₘ G.P) = H := by
    first
    | exact Polynomial.modByMonic_add_div H G.P
    | exact Polynomial.modByMonic_add_div H G.monic
  have hdeg : (H %ₘ G.P).natDegree < G.P.natDegree := by
    first
    | exact Polynomial.natDegree_modByMonic_lt H G.monic hP1
    | exact Polynomial.natDegree_modByMonic_lt H G.monic hP1
  have hrx : (H %ₘ G.P).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
    have h2 := congrArg (fun p => p.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) hsplit
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, G.root, zero_mul, add_zero, hH] at h2
    exact h2
  have hc := G.min _ hdeg hrx
  have hrw : (H %ₘ G.P).map (deh w 0) = 0 := by
    ext j
    rw [Polynomial.coeff_map, hw.ker _ (hc j), Polynomial.coeff_zero]
  have hr : (H %ₘ G.P).eval₂ (deh w 0) ρ = 0 := by
    rw [← Polynomial.eval_map, hrw, Polynomial.eval_zero]
  have h3 := congrArg (fun p => p.eval₂ (deh w 0) ρ) hsplit
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, hr, hρ, zero_mul, add_zero] at h3
  exact h3.symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω}
  {e : Fin (D + 1) → ι} (G : Gen x e)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}
variable [DecidableEq ι] (G : Gen x e) {w : Fin (D + 1) → ℂ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
namespace Gen
theorem _root_.solution (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0) (k : Fin (D + 1)) :
    G.zOf w ρ (e k) = w k := by
  have hH := eval₂_deh_eq_zero_of_good_of_root G hw hρ (G.Q (e k) - Polynomial.C (G.dd * X k)) (by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, ← G.hQ (e k), map_mul, sub_eq_zero, deh_X, deh_X]
    rfl)
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, map_mul, deh_X, sub_eq_zero] at hH
  have h0 := hw.w0
  have h1 := hw.dd
  simp only [Gen.zOf, Gen.evQ]
  rw [hH]
  first
  | (field_simp; done)
  | (field_simp; ring)
end Gen
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
