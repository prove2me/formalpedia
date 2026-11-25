-- Prove2me | solution 1 for PI.FHS.harmSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:20:06.046997+00:00
-- url     : https://prove2.me/submissions/981106d9-da91-47f2-8b18-dd9ad8ff2e30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_MinusPartOfMem
import Theorems.Thm_PI_FHS_plusPart_of_mem
import Theorems.Thm_PI_FHS_kill
import Theorems.Thm_PI_FHS_exists_orth
import Theorems.Thm_PI_FHS_fockAct1_adj
import Theorems.Thm_PI_FHS_fockAct2_adj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {p q r s : ℕ}
namespace PI.FHS
theorem _root_.solution : PI.FockDegreeTwoParts.HarmSplit := by
  intro p q r s u1 u2 _ d
  have hRle : Submodule.span ℂ (raised p q r s u1 u2 d) ≤ homog (Ix p q × Ix r s) (d + 2) := by
    rw [Submodule.span_le]
    rintro R ⟨Q, hQ, h | h⟩
    · obtain ⟨_, Z, _, rfl⟩ := h
      rw [SetLike.mem_coe, plusPart_of_mem hQ]
      exact homogeneousComponent_mem _ _
    · obtain ⟨_, Z, _, rfl⟩ := h
      rw [SetLike.mem_coe, plusPart_of_mem hQ]
      exact homogeneousComponent_mem _ _
  apply le_antisymm
  · intro f hf
    obtain ⟨y, hy, horth⟩ := exists_orth (Submodule.span ℂ (raised p q r s u1 u2 d)) (d + 2) hRle f
    have hfy : f - y ∈ homog (Ix p q × Ix r s) (d + 2) := Submodule.sub_mem _ hf (hRle hy)
    have hlow : f - y ∈ lowKer p q r s u1 u2 := by
      refine ⟨fun hu Z hZ => ?_, fun hu Z hZ => ?_⟩
      · refine kill (fockAct1 p q r s) (fun Z hZ P Q => fockAct1_adj hZ P Q) hfy (fun Z' hZ' g hg => ?_) Z hZ
        exact horth _ (Submodule.subset_span ⟨g, hg, Or.inl ⟨hu, Z', hZ', rfl⟩⟩)
      · refine kill (fockAct2 p q r s) (fun Z hZ P Q => fockAct2_adj hZ P Q) hfy (fun Z' hZ' g hg => ?_) Z hZ
        exact horth _ (Submodule.subset_span ⟨g, hg, Or.inr ⟨hu, Z', hZ', rfl⟩⟩)
    have hsplit : f = (f - y) + y := by abel
    rw [hsplit]
    exact Submodule.add_mem_sup ⟨hfy, Submodule.subset_span hlow⟩ hy
  · exact sup_le inf_le_left hRle
end PI.FHS
