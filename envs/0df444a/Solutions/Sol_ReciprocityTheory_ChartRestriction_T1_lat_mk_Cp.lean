-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.T1.lat_mk_Cp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:40.524301+00:00
-- url     : https://prove2.me/submissions/82493ae6-aaea-4794-98f9-a5e023562984

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlaceB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_T1_lat_mk_le_of_denseRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Cardinal Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.T1
namespace ReciprocityTheory.ChartRestriction.T1
theorem _root_.solution (p : ℕ) [Fact p.Prime] : #ℂ_[p] = 𝔠 := by
  apply le_antisymm
  · have h1 : Cardinal.mk ℚ_[p] ≤ 𝔠 := by
      calc Cardinal.mk ℚ_[p] ≤ Cardinal.mk ℚ ^ ℵ₀ :=
            lat_mk_le_of_denseRange ((↑) : ℚ → ℚ_[p]) (Padic.denseRange_ratCast p)
        _ = 𝔠 := by rw [Cardinal.mkRat, Cardinal.aleph0_power_aleph0]
    have h2 : Cardinal.mk (PadicAlgCl p) ≤ 𝔠 :=
      (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans
        (max_le h1 Cardinal.aleph0_le_continuum)
    calc Cardinal.mk ℂ_[p] ≤ Cardinal.mk (PadicAlgCl p) ^ ℵ₀ :=
          lat_mk_le_of_denseRange ((↑) : PadicAlgCl p → ℂ_[p]) UniformSpace.Completion.denseRange_coe
      _ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right h2
      _ = 𝔠 := Cardinal.continuum_power_aleph0
  ·
    obtain ⟨g, -, -, hg⟩ := Perfect.exists_nat_bool_injection (C := (Set.univ : Set ℂ_[p]))
      ⟨isClosed_univ, PerfectSpace.univ_preperfect⟩ ⟨0, trivial⟩
    calc 𝔠 = Cardinal.mk (ℕ → Bool) := by
          rw [← Cardinal.two_power_aleph0, ← Cardinal.mk_nat, ← Cardinal.mk_bool, Cardinal.power_def]
      _ ≤ Cardinal.mk ℂ_[p] := Cardinal.mk_le_of_injective hg
end ReciprocityTheory.ChartRestriction.T1
