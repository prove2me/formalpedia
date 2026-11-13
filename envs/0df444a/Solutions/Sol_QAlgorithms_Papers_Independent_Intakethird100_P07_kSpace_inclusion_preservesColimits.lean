-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.kSpace_inclusion_preservesColimits
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T22:58:53.457304+00:00
-- url     : https://prove2.me/submissions/b82c3d7f-e26d-46b0-b046-15737cd35e29

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kification_coreflection
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Mathlib.CategoryTheory.Adjunction.Limits
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P07
noncomputable section

universe u v



open CategoryTheory Topology TopologicalSpace

/-- Corollary B.6, PDF p. 36: the inclusion preserves categorical colimits. -/
theorem solution :
    Limits.PreservesColimits
      (CompactlyGenerated.compactlyGeneratedToTop.{u, u}) := by
  exact (Classical.choice kification_coreflection).leftAdjoint_preservesColimits
