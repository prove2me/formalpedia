-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefA_decompM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:30.206796+00:00
-- url     : https://prove2.me/submissions/0de941ea-7976-419c-9976-cb340fc78dc4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefA_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {M' : Submodule ℂ X} (hloc : CoefLocFin T M') {y : X} (hy : y ∈ M') :
    ∃ m : ℕ, ∃ b : Fin m → X, ∃ θ : Fin m → ℝ, y = ∑ i, b i ∧
      ∀ i, b i ∈ M' ∧ T (b i) = (θ i : ℂ) • b i := by
  obtain ⟨F, hFd, hFM, hF, hyF⟩ := hloc y hy
  obtain ⟨m, b, θ, hsum, hb⟩ := coefA_decomp hT hFd hF hyF
  exact ⟨m, b, θ, hsum, fun i => ⟨hFM (hb i).1, (hb i).2⟩⟩
end ReciprocityTheory.ChartRestriction.DS
