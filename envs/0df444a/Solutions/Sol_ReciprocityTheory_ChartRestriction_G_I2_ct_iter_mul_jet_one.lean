-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ct_iter_mul_jet_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:10:38.917749+00:00
-- url     : https://prove2.me/submissions/67ae3136-3a52-493a-8271-ddd428dc9821

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f g : V → ℂ) (hf : ContDiff ℂ (⊤ : ℕ∞) f) (hg : ContDiff ℂ (⊤ : ℕ∞) g) (c : ℕ)
    (h0 : g 0 = 1) (hjet : ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j g 0 = 0) :
    iteratedFDeriv ℂ c (fun v => f v * g v) 0 = iteratedFDeriv ℂ c f 0 := by
  have hle : ∀ k : ℕ, ((k : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    intro k
    first
      | exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.2 le_top
  have hhC : ContDiff ℂ (⊤ : ℕ∞) (fun v => g v - 1) := hg.sub contDiff_const
  have hz : ∀ k ≤ c, iteratedFDeriv ℂ k (fun v => g v - 1) 0 = 0 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · ext x
      simp [iteratedFDeriv_zero_apply, h0]
    · have e : (fun v => g v - 1) = g - fun _ => (1 : ℂ) := rfl
      rw [e]
      first
        | rw [iteratedFDeriv_sub_apply (hg.of_le (hle k)).contDiffAt contDiff_const.contDiffAt]
        | rw [iteratedFDeriv_sub_apply (hg.of_le (hle k)) contDiff_const]
      rw [hjet k hk0 hk, iteratedFDeriv_const_of_ne (by omega)]
      simp
  have hsplit : (fun v => f v * g v) = (fun v => f v) + (fun v => f v * (g v - 1)) := by
    funext v
    simp only [Pi.add_apply]
    ring
  have hfh : ContDiff ℂ (⊤ : ℕ∞) (fun v => f v * (g v - 1)) := hf.mul hhC
  rw [hsplit]
  first
    | rw [iteratedFDeriv_add_apply (hf.of_le (hle c)).contDiffAt (hfh.of_le (hle c)).contDiffAt]
    | rw [iteratedFDeriv_add_apply (hf.of_le (hle c)) (hfh.of_le (hle c))]
  have hb := norm_iteratedFDeriv_mul_le hf hhC (0 : V) (n := c) (hle c)
  have h0' : iteratedFDeriv ℂ c (fun v => f v * (g v - 1)) 0 = 0 := by
    rw [← norm_le_zero_iff]
    refine hb.trans (le_of_eq (Finset.sum_eq_zero fun i hi => ?_))
    rw [hz (c - i) (Nat.sub_le _ _), norm_zero, mul_zero]
  rw [h0', add_zero]
end ReciprocityTheory.ChartRestriction.G.I2
