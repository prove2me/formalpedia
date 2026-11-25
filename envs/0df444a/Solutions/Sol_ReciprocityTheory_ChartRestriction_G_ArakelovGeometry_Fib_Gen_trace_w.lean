-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.Gen.trace_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:32:55.831124+00:00
-- url     : https://prove2.me/submissions/f2029104-c4a4-4f74-8d26-4488da3effd8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_deh_S
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_mem_roots

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
variable [DecidableEq ι] (G : Gen x e)
private theorem eval₂_deh_eq_zero_of_mem_roots {w : Fin (D + 1) → ℂ} (hw : G.Good w)
    (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ))
    (hH : H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0) {ρ : ℂ}
    (hρ : ρ ∈ (G.P.map (deh w 0)).roots) : H.eval₂ (deh w 0) ρ = 0 := by
  have hP1 : G.P ≠ 1 := by
    intro h1
    have h2 := G.root
    rw [h1, Polynomial.eval₂_one] at h2
    exact one_ne_zero h2
  have hdecomp : H %ₘ G.P + G.P * (H /ₘ G.P) = H := by
    first
    | exact Polynomial.modByMonic_add_div H G.monic
    | exact Polynomial.modByMonic_add_div H G.P
    | exact Polynomial.modByMonic_add_div H G.P G.monic
  have hr : (H %ₘ G.P).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
    have h1 := congrArg (Polynomial.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) hdecomp
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, G.root, zero_mul, add_zero, hH] at h1
    exact h1
  have hcoef := G.min (H %ₘ G.P) (Polynomial.natDegree_modByMonic_lt H G.monic hP1) hr
  have hrw : (H %ₘ G.P).map (deh w 0) = 0 := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact hw.ker _ (hcoef j)
  have hPρ : G.P.eval₂ (deh w 0) ρ = 0 := by
    have h3 := (Polynomial.mem_roots (G.monic.map _).ne_zero).mp hρ
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at h3
  have h2 := congrArg (Polynomial.eval₂ (deh w 0) ρ) hdecomp
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, hPρ, zero_mul, add_zero] at h2
  rw [← h2, ← Polynomial.eval_map, hrw, Polynomial.eval_zero]
private theorem deh_dd_mul_deh_zOf_X_eq_eval₂_Q {w : Fin (D + 1) → ℂ} (hw : G.Good w) (i : ι) {ρ : ℂ}
    (hρ : ρ ∈ (G.P.map (deh w 0)).roots) :
    deh w 0 G.dd * deh (G.zOf w ρ) (e 0) (X i) = (G.Q i).eval₂ (deh w 0) ρ := by
  have hx : ∀ j, deh x (e 0) (X j) = x j / x (e 0) := fun j => by simp [deh]
  have hz : ∀ j, deh (G.zOf w ρ) (e 0) (X j) = G.zOf w ρ j / G.zOf w ρ (e 0) :=
    fun j => by simp [deh]
  have hzj : ∀ j, G.zOf w ρ j = w 0 * ((G.Q j).eval₂ (deh w 0) ρ / deh w 0 G.dd) := fun j => rfl
  have hd := hw.dd
  have h0 := hw.w0
  rw [hz, hzj, hzj]
  by_cases hxe : x (e 0) = 0
  · have hq : ∀ j, (G.Q j).eval₂ (deh w 0) ρ = 0 := by
      intro j
      refine eval₂_deh_eq_zero_of_mem_roots G hw (G.Q j) ?_ hρ
      rw [← G.hQ j, hx, hxe, div_zero, mul_zero]
    simp [hq]
  · have hxs : (G.Q (e 0) - Polynomial.C G.dd).eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = 0 := by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, ← G.hQ (e 0), hx, div_self hxe, mul_one,
        sub_self]
    have h1 := eval₂_deh_eq_zero_of_mem_roots G hw _ hxs hρ
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, sub_eq_zero] at h1
    rw [h1]
    field_simp
    first | done | ring
private theorem exists_pow_mul_eq_eval₂_theta {w : Fin (D + 1) → ℂ} (hw : G.Good w) (f : MvPolynomial ι ℤ) :
    ∃ (N : ℕ) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)),
      deh (x ∘ e) 0 G.dd ^ N * deh x (e 0) f = H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) ∧
      ∀ ρ ∈ (G.P.map (deh w 0)).roots,
        deh w 0 G.dd ^ N * deh (G.zOf w ρ) (e 0) f = H.eval₂ (deh w 0) ρ := by
  induction f using MvPolynomial.induction_on
  next a =>
    refine ⟨0, Polynomial.C (MvPolynomial.C a), ?_, fun ρ _ => ?_⟩ <;>
      (rw [pow_zero, one_mul, Polynomial.eval₂_C]; simp [deh])
  next f1 f2 h1 h2 =>
    obtain ⟨N1, H1, hx1, hw1⟩ := h1
    obtain ⟨N2, H2, hx2, hw2⟩ := h2
    refine ⟨N1 + N2, Polynomial.C (G.dd ^ N2) * H1 + Polynomial.C (G.dd ^ N1) * H2, ?_,
      fun ρ hρ => ?_⟩
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hx1, ← hx2, map_add, map_pow, map_pow]
      ring
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hw1 ρ hρ, ← hw2 ρ hρ, map_add, map_pow, map_pow]
      ring
  next f1 i h1 =>
    obtain ⟨N, H, hx1, hw1⟩ := h1
    refine ⟨N + 1, H * G.Q i, ?_, fun ρ hρ => ?_⟩
    · rw [Polynomial.eval₂_mul, ← hx1, ← G.hQ i, map_mul]
      ring
    · rw [Polynomial.eval₂_mul, ← hw1 ρ hρ, ← deh_dd_mul_deh_zOf_X_eq_eval₂_Q G hw i hρ, map_mul]
      ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open Polynomial IntermediateField
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
end
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}
variable [DecidableEq ι] (G : Gen x e)
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
namespace Gen
theorem _root_.solution {w : Fin (D + 1) → ℂ} (hw : G.Good w) (Tr : Ω → Ω)
    (hTr : ∀ H, Tr (H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) = deh (x ∘ e) 0 (G.TrP H))
    (hsc : ∀ (m : MvPolynomial (Fin (D + 1)) ℤ) (F : MvPolynomial ι ℤ),
      Tr (deh (x ∘ e) 0 m * deh x (e 0) F) = deh (x ∘ e) 0 m * Tr (deh x (e 0) F))
    {f : MvPolynomial ι ℤ} {g : MvPolynomial (Fin (D + 1)) ℤ}
    (h : deh (x ∘ e) 0 g = Tr (deh x (e 0) f)) :
    deh w 0 g = ((G.P.map (deh w 0)).roots.map fun ρ => deh (G.zOf w ρ) (e 0) f).sum := by
  obtain ⟨N, H, hx, hwr⟩ := exists_pow_mul_eq_eval₂_theta G hw f
  have hker : deh (x ∘ e) 0 (G.dd ^ N * g - G.TrP H) = 0 := by
    rw [map_sub, map_mul, h, ← hTr H, ← hx, ← hsc, map_pow, sub_self]
  have hwk := hw.ker _ hker
  rw [map_sub, map_mul, map_pow, sub_eq_zero] at hwk
  have hTrw : deh w 0 (G.TrP H) =
      ((G.P.map (deh w 0)).roots.map fun ρ => H.eval₂ (deh w 0) ρ).sum := by
    rw [Gen.TrP, map_sum]
    simp only [map_mul, G.deh_S, Polynomial.eval₂_eq_sum_range]
    generalize (G.P.map (deh w 0)).roots = s
    refine Multiset.induction_on s ?_ ?_
    · simp
    · intro a s ih
      simp [Multiset.map_cons, Multiset.sum_cons, mul_add, Finset.sum_add_distrib, ih]
  have hdN : deh w 0 G.dd ^ N ≠ 0 := pow_ne_zero _ hw.dd
  apply mul_left_cancel₀ hdN
  rw [hwk, hTrw, ← Multiset.sum_map_mul_left]
  congr 1
  exact Multiset.map_congr rfl fun ρ hρ => (hwr ρ hρ).symm
end Gen
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
