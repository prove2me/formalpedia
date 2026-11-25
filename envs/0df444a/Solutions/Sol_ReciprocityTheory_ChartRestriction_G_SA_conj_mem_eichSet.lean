-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.conj_mem_eichSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:17:59.826931+00:00
-- url     : https://prove2.me/submissions/8531ef39-2a94-4b45-8559-063fab7681f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ConjMemEichSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_conj_mem_along
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ
variable {e f : ι → K} (he : hf σ J e e = 0) (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {l m : K} (hml : m * σ l = 1) {M : Matrix ι ι K}
    (hM : M ∈ eichSet σ J e f) :
    ∃ M' ∈ eichSet σ J e f, tor σ J e f l m * M = M' * tor σ J e f l m := by
  rcases hM with hM | hM
  · obtain ⟨M', h1, h2⟩ := conj_mem_along hσ hJ he hff hef hml hM
    exact ⟨M', Or.inl h1, h2⟩
  · have hfe := hf_fe hσ hJ he hff hef
    have hlm : l * σ m = 1 := by rw [← hσ l, ← map_mul, mul_comm, hml, map_one]
    obtain ⟨M', h1, h2⟩ := conj_mem_along hσ hJ hff he hfe hlm hM
    rw [← tor_swap] at h2
    exact ⟨M', Or.inr h1, h2⟩
end ReciprocityTheory.ChartRestriction.G.SA
