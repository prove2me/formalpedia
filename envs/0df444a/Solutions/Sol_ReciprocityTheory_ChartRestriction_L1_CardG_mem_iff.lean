-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.CardG.mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:55:37.506461+00:00
-- url     : https://prove2.me/submissions/39319297-c6a9-4bfc-9915-81ff89bff188

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedCardG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CardG_coord_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open ReciprocityTheory.ChartRestriction.L1.CardG
namespace ReciprocityTheory.ChartRestriction.L1.CardG
theorem _root_.solution (L : PeriodPair) (p : ℕ) (hp : p ≠ 0) {z : ℂ} {m n : ℤ}
    (h : (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z) :
    z ∈ L.lattice ↔ (m : ZMod p) = 0 ∧ (n : ZMod p) = 0 := by
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro hz
    obtain ⟨m', n', e⟩ := PeriodPair.mem_lattice.mp hz
    have := coord_unique L (m := m) (n := n) (m' := p * m') (n' := p * n') (by
      rw [h, ← e]; push_cast; ring)
    exact ⟨⟨m', this.1⟩, ⟨n', this.2⟩⟩
  · rintro ⟨⟨m', rfl⟩, ⟨n', rfl⟩⟩
    refine PeriodPair.mem_lattice.mpr ⟨m', n', ?_⟩
    apply mul_left_cancel₀ hpc
    rw [← h]; push_cast; ring
end ReciprocityTheory.ChartRestriction.L1.CardG
