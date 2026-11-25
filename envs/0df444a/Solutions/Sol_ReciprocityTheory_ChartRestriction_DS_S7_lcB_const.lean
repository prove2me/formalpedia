-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lcB_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:41:29.916886+00:00
-- url     : https://prove2.me/submissions/af88f74f-02a0-4806-9123-9bcfa13fd740

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LocalB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lcB_hasDerivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Set
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (psM T μ) U) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z))
    (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (A : Matrix (Fin n) (Fin n) ℂ) (hpath : ∀ t ∈ Icc (0 : ℝ) 1, A * NormedSpace.exp ((t : ℂ) • Y) ∈ U) :
    T.op (γ 1) * psM T μ (A * NormedSpace.exp Y) = psM T μ A := by
  have h0 : γ 0 = 1 := by simpa using hmul 0 0
  let g : ℝ → T.V →L[ℂ] T.V := fun t => T.op (γ t) * psM T μ (A * NormedSpace.exp ((t : ℂ) • Y))
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g 0 t := fun t ht =>
    lcB_hasDerivAt T μ hUo hdiff hid hY γ hγ hmul A (hpath t ht)
  have hcont : ContinuousOn g (Icc 0 1) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hc := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  simpa [g, h0, KType.op] using hc
end ReciprocityTheory.ChartRestriction.DS.S7
