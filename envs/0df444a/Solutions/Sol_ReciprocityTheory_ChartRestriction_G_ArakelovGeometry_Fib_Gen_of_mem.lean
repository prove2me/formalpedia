-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:12.008018+00:00
-- url     : https://prove2.me/submissions/569a3bb6-8d49-4314-b904-78347e65785e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_eval__rename_376a9ee8007e
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
private theorem deh_eq_zero_of_mem_pts_of_deh_eq_zero (hx0 : x (e 0) ≠ 0) (F : MvPolynomial ι ℤ) (hF : deh x (e 0) F = 0)
    {z : ι → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) (hz0 : z (e 0) ≠ 0) : deh z (e 0) F = 0 := by
  have hz' : z ≠ 0 ∧ ∀ f ∈ coordIdeal ℤ x,
      MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := hz
  have hmem : (∑ m ∈ F.support, MvPolynomial.C (MvPolynomial.coeff m F) *
      X (e 0) ^ (F.totalDegree - ∑ i ∈ m.support, m i) * ∏ i ∈ m.support, X i ^ m i) ∈ coordIdeal ℤ x := by
    show _ ∈ RingHom.ker (coneMap ℤ x)
    rw [RingHom.mem_ker, coneMap, map_sum]
    have h1 : ∀ m ∈ F.support, (aeval fun i => Polynomial.C (x i) * Polynomial.X)
        (MvPolynomial.C (MvPolynomial.coeff m F) * X (e 0) ^ (F.totalDegree - ∑ i ∈ m.support, m i) *
          ∏ i ∈ m.support, X i ^ m i) =
        Polynomial.C (((MvPolynomial.coeff m F : ℤ) : Ω) * x (e 0) ^ (F.totalDegree - ∑ i ∈ m.support, m i) *
          ∏ i ∈ m.support, x i ^ m i) * Polynomial.X ^ F.totalDegree := by
      intro m hm
      have hs : ∑ i ∈ m.support, m i ≤ F.totalDegree := MvPolynomial.le_totalDegree hm
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
      rw [hk, Nat.add_sub_cancel_left]
      simp only [map_mul, map_pow, map_prod, MvPolynomial.aeval_C, MvPolynomial.aeval_X, mul_pow,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, algebraMap_int_eq, eq_intCast, map_intCast]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← map_sum Polynomial.C,
      sum_coeff_homogenize_eq_pow_mul_eval₂ F (fun i => x i / x (e 0)) x (x (e 0)) (fun i => rfl) hx0 _ le_rfl, ← deh_apply, hF,
      mul_zero, map_zero, zero_mul]
  have h2 := hz'.2 _ hmem
  rw [MvPolynomial.eval_map] at h2
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_prod, Int.coe_castRingHom] at h2
  rw [sum_coeff_homogenize_eq_pow_mul_eval₂ F (fun i => z i / z (e 0)) z (z (e 0)) (fun i => rfl) hz0 _ le_rfl, ← deh_apply] at h2
  exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hz0)
private theorem deh_rename' {S : Type*} [Field S] (v : ι → S) (F : MvPolynomial (Fin (D + 1)) ℤ) :
    deh v (e 0) (rename e F) = deh (v ∘ e) 0 F := by
  rw [deh_apply, deh_apply, MvPolynomial.eval₂_rename]
  rfl
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
theorem _root_.solution (hx0 : x (e 0) ≠ 0) (hw : G.Good w) {z : ι → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) (hze : ∀ k, z (e k) = w k) :
    G.P.eval₂ (deh w 0) (deh z (e 0) G.Θ) = 0 ∧ G.zOf w (deh z (e 0) G.Θ) = z := by
  have hz0 : z (e 0) ≠ 0 := by
    rw [hze 0]
    exact hw.w0
  have hze' : z ∘ e = w := funext hze
  constructor
  · have h := deh_eq_zero_of_mem_pts_of_deh_eq_zero hx0
      (G.P.eval₂ (rename e : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι ℤ).toRingHom G.Θ)
      (by rw [deh_eval₂_rename]; exact G.root) hz hz0
    rw [deh_eval₂_rename, hze'] at h
    exact h
  · funext i
    have h := deh_eq_zero_of_mem_pts_of_deh_eq_zero hx0
      ((G.Q i).eval₂ (rename e : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι ℤ).toRingHom G.Θ -
        rename e G.dd * X i)
      (by rw [map_sub, deh_eval₂_rename, map_mul, deh_rename', ← G.hQ i, sub_self]) hz hz0
    rw [map_sub, deh_eval₂_rename, map_mul, deh_rename', hze', deh_X, sub_eq_zero] at h
    have h0 := hw.w0
    have h1 := hw.dd
    simp only [Gen.zOf, Gen.evQ]
    rw [h, hze 0]
    first
    | (field_simp; done)
    | (field_simp; ring)
end Gen
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
