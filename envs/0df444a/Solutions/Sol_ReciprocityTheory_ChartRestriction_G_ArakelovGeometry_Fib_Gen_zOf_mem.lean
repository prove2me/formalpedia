-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.zOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:52.983262+00:00
-- url     : https://prove2.me/submissions/747f0ad7-cbf4-4f11-bc14-cffa6991de70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_zOf_e
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
private theorem map_eval₂_X_mul_C_eq {K : Type*} [Field K] (φ : MvPolynomial (Fin (D + 1)) ℤ →+* K) (t : K)
    (f : MvPolynomial ι ℤ) :
    (MvPolynomial.eval₂ (Int.castRingHom (Polynomial (Polynomial (MvPolynomial (Fin (D + 1)) ℤ))))
        (fun i => Polynomial.X * Polynomial.C (G.Q i)) f).map (Polynomial.eval₂RingHom φ t) =
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial K))
        (fun i => Polynomial.X * Polynomial.C ((G.Q i).eval₂ φ t)) f := by
  have hk := MvPolynomial.eval₂_comp_left (Polynomial.mapRingHom (Polynomial.eval₂RingHom φ t))
    (Int.castRingHom _) (fun i => Polynomial.X * Polynomial.C (G.Q i)) f
  first
  | rw [Polynomial.coe_mapRingHom] at hk
  | skip
  rw [hk]
  congr 1
  · exact RingHom.ext_int _ _
  · funext i
    simp [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, Polynomial.coe_eval₂RingHom]
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
theorem _root_.solution (hx0 : x (e 0) ≠ 0) (hw : G.Good w) {ρ : ℂ}
    (hρ : G.P.eval₂ (deh w 0) ρ = 0) : G.zOf w ρ ∈ pts (coordIdeal ℤ x) := by
  show G.zOf w ρ ≠ 0 ∧ ∀ f ∈ coordIdeal ℤ x,
    MvPolynomial.eval (G.zOf w ρ) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0
  refine ⟨fun h => hw.w0 ?_, fun f hf => ?_⟩
  · rw [← G.zOf_e hw hρ 0, h, Pi.zero_apply]
  have hcone := RingHom.mem_ker.mp (show f ∈ RingHom.ker (coneMap ℤ x) from hf)
  have hrel : MvPolynomial.eval₂ (Int.castRingHom (Polynomial Ω))
      (fun i => Polynomial.X * Polynomial.C ((G.Q i).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ))) f =
      ((coneMap ℤ x) f).comp (Polynomial.C (deh (x ∘ e) 0 G.dd * (x (e 0))⁻¹) * Polynomial.X) := by
    have hk := MvPolynomial.eval₂_comp_left
      (Polynomial.compRingHom (Polynomial.C (deh (x ∘ e) 0 G.dd * (x (e 0))⁻¹) * Polynomial.X))
      (algebraMap ℤ (Polynomial Ω)) (fun i => Polynomial.C (x i) * Polynomial.X) f
    rw [coneMap, MvPolynomial.aeval_def, ← Polynomial.coe_compRingHom_apply, hk]
    congr 1
    · exact RingHom.ext_int _ _
    · funext i
      simp only [Function.comp_apply, Polynomial.coe_compRingHom_apply, Polynomial.mul_comp,
        Polynomial.C_comp, Polynomial.X_comp, ← G.hQ i, deh_X, div_eq_mul_inv, map_mul]
      ring
  have h2 := map_eval₂_X_mul_C_eq G (deh (x ∘ e) 0) (deh x (e 0) G.Θ) f
  rw [hrel, hcone, Polynomial.zero_comp] at h2
  have h3 : (MvPolynomial.eval₂ (Int.castRingHom (Polynomial (Polynomial (MvPolynomial (Fin (D + 1)) ℤ))))
        (fun i => Polynomial.X * Polynomial.C (G.Q i)) f).map (Polynomial.eval₂RingHom (deh w 0) ρ) = 0 := by
    ext d
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coe_eval₂RingHom]
    apply eval₂_deh_eq_zero_of_good_of_root G hw hρ
    have h4 := Polynomial.ext_iff.mp h2 d
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coe_eval₂RingHom] at h4
    exact h4
  rw [map_eval₂_X_mul_C_eq G (deh w 0) ρ f] at h3
  rw [MvPolynomial.eval_map]
  have h4 := congrArg (Polynomial.eval (w 0 / deh w 0 G.dd)) h3
  rw [Polynomial.eval_zero, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left] at h4
  have e1 : (Polynomial.evalRingHom (w 0 / deh w 0 G.dd)).comp (Int.castRingHom (Polynomial ℂ)) =
      Int.castRingHom ℂ := RingHom.ext_int _ _
  have e2 : (⇑(Polynomial.evalRingHom (w 0 / deh w 0 G.dd)) ∘
      fun i => Polynomial.X * Polynomial.C ((G.Q i).eval₂ (deh w 0) ρ)) = G.zOf w ρ := by
    funext i
    simp only [Function.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Gen.zOf, Gen.evQ]
    ring
  rw [e1, e2] at h4
  exact h4
end Gen
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
