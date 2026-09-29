-- Prove2me | solution 1 for WeierstrassCurve.discr_dvd_pow_of_jOfUnit_mem_range_short
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/90e0a443-0855-5c98-ab73-f3eb20cd7ec8

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_discr_dvd_pow_of_jOfUnit_mem_range_short

set_option autoImplicit false

universe u

theorem solution
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (h2 : IsUnit ((2 : ℕ) : R₀)) (h3 : IsUnit ((3 : ℕ) : R₀)) (a b : R₀)
    (hΔ : IsUnit ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K)).Δ)
    (hj : ((⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K)).jOfUnit hΔ ∈ Set.range (algebraMap R₀ K)) :
    (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).Δ ∣ a ^ 3 ∧ (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).Δ ∣ b ^ 2 := by
  classical
  set W₀ : WeierstrassCurve R₀ := ⟨0, 0, 0, a, b⟩ with hW₀
  have hinj : Function.Injective (algebraMap R₀ K) := IsFractionRing.injective R₀ K

  have hu2 : IsUnit (2 : R₀) := by simpa using h2
  have hu3 : IsUnit (3 : R₀) := by simpa using h3

  obtain ⟨r, hr⟩ := hj
  haveI hE : (W₀.map (algebraMap R₀ K)).IsElliptic := ⟨hΔ⟩
  have hjdef : (W₀.map (algebraMap R₀ K)).jOfUnit hΔ = (W₀.map (algebraMap R₀ K)).j := rfl
  have hjΔ : algebraMap R₀ K r * (W₀.map (algebraMap R₀ K)).Δ = (W₀.map (algebraMap R₀ K)).c₄ ^ 3 := by
    rw [hr, hjdef, WeierstrassCurve.j, mul_comm, ← mul_assoc, ← WeierstrassCurve.coe_Δ', Units.mul_inv, one_mul]
  rw [WeierstrassCurve.map_Δ, WeierstrassCurve.map_c₄, ← map_pow, ← map_mul] at hjΔ
  have hRΔ : r * W₀.Δ = W₀.c₄ ^ 3 := hinj hjΔ

  have hc₄ : W₀.c₄ = -48 * a := by
    simp only [hW₀, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring
  have hΔv : W₀.Δ = -64 * a ^ 3 - 432 * b ^ 2 := by
    simp only [hW₀, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]; ring

  have h110592 : IsUnit ((-110592 : R₀)) := by
    have : (-110592 : R₀) = -(2 ^ 12 * 3 ^ 3) := by norm_num
    rw [this]
    exact ((hu2.pow 12).mul (hu3.pow 3)).neg
  have hda : W₀.Δ ∣ a ^ 3 := by
    have : W₀.Δ ∣ (-110592) * a ^ 3 := ⟨r, by rw [mul_comm W₀.Δ r, hRΔ, hc₄]; ring⟩
    exact (h110592.dvd_mul_left).mp this
  have h432 : IsUnit ((432 : R₀)) := by
    have : (432 : R₀) = 2 ^ 4 * 3 ^ 3 := by norm_num
    rw [this]
    exact (hu2.pow 4).mul (hu3.pow 3)
  have hdb : W₀.Δ ∣ b ^ 2 := by
    have h1 : W₀.Δ ∣ 432 * b ^ 2 := by
      have e : 432 * b ^ 2 = -W₀.Δ - 64 * a ^ 3 := by rw [hΔv]; ring
      rw [e]
      exact (dvd_neg.mpr dvd_rfl).sub (Dvd.dvd.mul_left hda _)
    exact (h432.dvd_mul_left).mp h1
  exact ⟨hda, hdb⟩

end S_WeierstrassCurve_discr_dvd_pow_of_jOfUnit_mem_range_short
end P2MW
export P2MW.S_WeierstrassCurve_discr_dvd_pow_of_jOfUnit_mem_range_short (solution)
