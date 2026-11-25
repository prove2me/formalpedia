-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.xiExists_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:30.107145+00:00
-- url     : https://prove2.me/submissions/09c1d41e-b4fc-42f8-988e-60ce2880bb13

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XiExists2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution (hA : ∀ k r : ℕ, 1 ≤ k → AAt k r) (hB : ∀ k r : ℕ, 1 ≤ k → BAt k r (1 / 2))
    (hC : CoefStep) (hX : XiIntStep) : XiExists := by
  intro k r Wp Wq _ _ _ _ _ _ D A hA'
  obtain ⟨eS, heS, hBs⟩ := hB k r D.k_pos
  have he0 : 0 < min eS (1 / 10 : ℝ) := lt_min heS (by norm_num)
  have adm : SAdm k r (fun l => s0 k r l - min eS (1 / 10)) := fun l => by
    simp only [sub_sub_cancel]; exact ⟨he0, min_le_right _ _⟩
  have adm' : ∀ l, 0 < s0 k r l - (s0 k r l - min eS (1 / 10)) ∧ s0 k r l - (s0 k r l - min eS (1 / 10)) ≤ eS :=
    fun l => by simp only [sub_sub_cancel]; exact ⟨he0, min_le_left _ _⟩
  exact ⟨xiN k r _, hC k r Wp Wq D A _ adm hA' (hA k r D.k_pos _ adm D.μG D.haarG A hA'),
    hX k r Wp Wq D _ adm (hBs _ adm' D.z D.z_mem D.T_pos D.μN D.haarN)
      (hBs _ adm' D.z' D.z'_mem D.T'_pos D.μN D.haarN)⟩
end ReciprocityTheory.ChartRestriction.DS.Xi
