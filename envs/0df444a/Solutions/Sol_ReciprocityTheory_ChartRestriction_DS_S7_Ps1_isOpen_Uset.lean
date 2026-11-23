-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.isOpen_Uset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:52:49.146608+00:00
-- url     : https://prove2.me/submissions/3d3ecd7e-b852-4985-888b-a907a052e664

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_omega__9ea460878a6b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.Ps1
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.Ps1
theorem _root_.solution [CompactSpace (KG ε)] : IsOpen (Uset ε) := by
  have hC : IsClosed ((fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => toMK p.2⁻¹ * p.1 * toMK p.2) ⁻¹'
      (OmegaSet n)ᶜ) :=
    isOpen_omega'.isClosed_compl.preimage continuous_conj
  have e : (Uset ε)ᶜ = Prod.fst ''
      ((fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => toMK p.2⁻¹ * p.1 * toMK p.2) ⁻¹' (OmegaSet n)ᶜ) := by
    ext z
    constructor
    · intro hz
      simp only [Uset, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hz
      obtain ⟨k, hk⟩ := hz
      exact ⟨(z, k), hk, rfl⟩
    · rintro ⟨p, hp, rfl⟩ hz
      exact hp (hz p.2)
  rw [← isClosed_compl_iff, e]
  exact isClosedMap_fst_of_compactSpace _ hC
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
