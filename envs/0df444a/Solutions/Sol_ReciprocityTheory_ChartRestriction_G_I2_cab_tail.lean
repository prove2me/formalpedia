-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:25:57.537788+00:00
-- url     : https://prove2.me/submissions/0dc0bec9-7ca3-4495-a965-d1f6ea2a874a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) {κ : Type}
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (g' : ℕ) (hN : Module.finrank ℝ W = 2 * g') (U : κ → W) (δ k : ℝ) (hδ : 0 < δ) (hk : 0 < k)
    (hsep : ∀ a b, a ≠ b → δ ≤ ‖U a - U b‖) (hlow : ∀ a, δ ≤ ‖U a‖)
    (hbig : 2 * (g' : ℝ) + 1 ≤ k * δ ^ 2) :
    Summable (fun a => Real.exp (-(k * ‖U a‖ ^ 2))) ∧
      ∑' a, Real.exp (-(k * ‖U a‖ ^ 2)) ≤ 2 * 9 ^ g' * Real.exp (-(k * δ ^ 2)) := by
  classical
  set sk := Real.sqrt k with hsk
  have hsk0 : 0 < sk := Real.sqrt_pos.mpr hk
  have hsk2 : sk ^ 2 = k := Real.sq_sqrt hk.le
  set R0 := 4 * sk * δ with hR0
  have hR00 : 0 < R0 := by positivity
  let h : κ → ℝ := fun a => 4 * sk * ‖U a‖
  have hsq : ∀ t : ℝ, Real.exp (-(4 * sk * t) ^ 2 / 16) = Real.exp (-(k * t ^ 2)) := by
    intro t; congr 1; rw [mul_pow, mul_pow, hsk2]; ring
  let e := stdOrthonormalBasis ℝ W
  have hcount : ∀ R : ℝ, R0 ≤ R → ∀ S : Finset κ, (∀ i ∈ S, h i ≤ R) →
      (S.card : ℝ) ≤ (3 * R / R0) ^ (2 * g') := by
    intro R hR S hS
    set R' := R / (4 * sk) with hR'
    have h4 : 0 < 4 * sk := by positivity
    have hδR : δ ≤ R' := by
      rw [hR', le_div_iff₀ h4]; rw [hR0] at hR; linarith
    let P : Finset (EuclideanSpace ℝ (Fin (Module.finrank ℝ W))) := S.image (fun a => e.repr (U a))
    have hinj : Set.InjOn (fun a => e.repr (U a)) S := by
      intro a _ b _ hab
      by_contra hne
      have h1 := hsep a b hne
      simp only at hab
      have h2 : U a = U b := e.repr.injective hab
      rw [h2, sub_self, norm_zero] at h1
      linarith
    have hcard : P.card = S.card := Finset.card_image_of_injOn hinj
    have hPn : ∀ x ∈ P, ‖x‖ ≤ R' := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      rw [LinearIsometryEquiv.norm_map, hR', le_div_iff₀ h4]
      have := hS a ha
      simp only [h] at this; linarith
    have hPs : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y := by
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      have hab : a ≠ b := fun hab => hxy (by rw [hab])
      rw [dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map]
      exact hsep a b hab
    have := hP _ P δ R' hδ hδR hPn hPs
    rw [hcard, hN] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    rw [hR', hR0]; field_simp
  have hlowh : ∀ a, R0 ≤ h a := fun a => by
    simp only [h, hR0]; exact mul_le_mul_of_nonneg_left (hlow a) (by positivity)
  have hbig' : 16 * (2 * (g' : ℝ) + 1) ≤ R0 ^ 2 := by
    rw [hR0, mul_pow, mul_pow, hsk2]; nlinarith
  obtain ⟨hs, hle⟩ := hA κ h g' R0 hR00 hbig' hlowh hcount
  have hfun : (fun a => Real.exp (-(h a) ^ 2 / 16)) = fun a => Real.exp (-(k * ‖U a‖ ^ 2)) := by
    funext a; exact hsq _
  rw [hfun] at hs hle
  refine ⟨hs, hle.trans (le_of_eq ?_)⟩
  rw [hR0, hsq]
end ReciprocityTheory.ChartRestriction.G.I2
