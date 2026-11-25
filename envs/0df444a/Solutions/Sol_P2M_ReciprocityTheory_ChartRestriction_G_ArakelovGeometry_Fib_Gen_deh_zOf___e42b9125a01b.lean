-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_deh_zOf___e42b9125a01b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:44:58.396917+00:00
-- url     : https://prove2.me/submissions/1af3919b-90e3-472c-9093-60e595f43c5d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_deh_zOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_apply

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
private theorem sum_coeff_homogenize_eq_pow_mul_eval₂ {S : Type*} [Field S] (F : MvPolynomial ι ℤ) (v a : ι → S) (d : S)
    (hv : ∀ i, v i = a i / d) (hd : d ≠ 0) (N : ℕ) (hN : F.totalDegree ≤ N) :
    ∑ m ∈ F.support, ((MvPolynomial.coeff m F : ℤ) : S) * d ^ (N - ∑ i ∈ m.support, m i) *
      ∏ i ∈ m.support, a i ^ m i = d ^ N * MvPolynomial.eval₂ (Int.castRingHom S) v F := by
  rw [MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hs : ∑ i ∈ m.support, m i ≤ N := (MvPolynomial.le_totalDegree hm).trans hN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  simp only [hv, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, eq_intCast,
    Nat.add_sub_cancel_left, pow_add]
  first
  | (field_simp; done)
  | (field_simp; ring)
  | ring
private theorem map_homogenized_sub_dd_pow_X_eq {S : Type*} [Field S] (φ : MvPolynomial (Fin (D + 1)) ℤ →+* S) (t : S)
    (hd : φ G.dd ≠ 0) :
    Polynomial.eval₂ φ t ((∑ m ∈ G.Θ.support, Polynomial.C (MvPolynomial.C (MvPolynomial.coeff m G.Θ) *
        G.dd ^ (G.Θ.totalDegree - ∑ i ∈ m.support, m i)) * ∏ i ∈ m.support, G.Q i ^ m i) -
      Polynomial.C (G.dd ^ G.Θ.totalDegree) * Polynomial.X) =
      φ G.dd ^ G.Θ.totalDegree * (MvPolynomial.eval₂ (Int.castRingHom S) (G.evQ φ t) G.Θ - t) := by
  have hC : ∀ c : ℤ, φ (MvPolynomial.C c) = (c : S) := fun c => eq_intCast (φ.comp MvPolynomial.C) c
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_finset_sum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_finset_prod, Polynomial.eval₂_pow, map_mul, map_pow, hC]
  rw [mul_sub, ← sum_coeff_homogenize_eq_pow_mul_eval₂ G.Θ (G.evQ φ t) (fun i => (G.Q i).eval₂ φ t) (φ G.dd) (fun i => rfl) hd
    G.Θ.totalDegree le_rfl]
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
theorem _root_.solution (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0) :
    deh (G.zOf w ρ) (e 0) G.Θ = ρ := by
  have hx := map_homogenized_sub_dd_pow_X_eq G (deh (x ∘ e) 0) (deh x (e 0) G.Θ) G.dd_ne
  have hQx : MvPolynomial.eval₂ (Int.castRingHom Ω) (G.evQ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) G.Θ =
      deh x (e 0) G.Θ := by
    conv_rhs => rw [deh_apply]
    congr 1
    funext i
    simp only [Gen.evQ]
    rw [← G.hQ i, deh_X]
    first
    | exact mul_div_cancel_left₀ _ G.dd_ne
    | field_simp [G.dd_ne]
  rw [hQx, sub_self, mul_zero] at hx
  have hw' := eval₂_deh_eq_zero_of_good_of_root G hw hρ _ hx
  rw [map_homogenized_sub_dd_pow_X_eq G (deh w 0) ρ hw.dd] at hw'
  have h2 := (mul_eq_zero.mp hw').resolve_left (pow_ne_zero _ hw.dd)
  rw [G.deh_zOf hw hρ]
  exact sub_eq_zero.mp h2
end Gen
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
