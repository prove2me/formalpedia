-- Prove2me | solution 1 for ZMod.kloosterman_sum_crt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T02:12:04.238428+00:00
-- url     : https://prove2.me/submissions/572ec40e-b623-48e5-9fe6-2d26989db1ea

import Mathlib
import Definitions.Def_RPLib_S3_KloostermanB

set_option autoImplicit false

theorem solution {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂] {α β : ℤ}
    (hab : α * c₂ + β * c₁ = 1) (m r : ℤ) :
    ∑ x : (ZMod (c₁ * c₂))ˣ, ZMod.stdAddChar ((m : ZMod (c₁ * c₂)) * (x : ZMod (c₁ * c₂)) +
        (r : ZMod (c₁ * c₂)) * (x : ZMod (c₁ * c₂))⁻¹) =
      (∑ x : (ZMod c₁)ˣ, ZMod.stdAddChar (((α * m : ℤ) : ZMod c₁) * (x : ZMod c₁) +
        ((α * r : ℤ) : ZMod c₁) * (x : ZMod c₁)⁻¹)) *
      (∑ x : (ZMod c₂)ˣ, ZMod.stdAddChar (((β * m : ℤ) : ZMod c₂) * (x : ZMod c₂) +
        ((β * r : ℤ) : ZMod c₂) * (x : ZMod c₂)⁻¹)) := by
  have hc : c₁.Coprime c₂ := by
    rw [← Nat.isCoprime_iff_coprime]
    exact ⟨β, α, by linarith⟩
  have h := RamanujanPetersson.KL.kl_crt hc hab (m : ZMod (c₁ * c₂)) (r : ZMod (c₁ * c₂))
  unfold RamanujanPetersson.KL.kl at h
  simpa only [map_intCast, Int.cast_mul] using h
