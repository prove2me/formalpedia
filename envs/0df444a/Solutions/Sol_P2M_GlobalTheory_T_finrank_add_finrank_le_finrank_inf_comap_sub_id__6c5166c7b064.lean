-- Prove2me | solution 1 for P2M_GlobalTheory_T_finrank_add_finrank_le_finrank_inf_comap_sub_id__6c5166c7b064
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:34.406512+00:00
-- url     : https://prove2.me/submissions/87519c4a-b162-49f2-8888-3121ea1f847c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAddFinrankLeFinrankInfComapSubId
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAddFinrankLeFinrankInfComapSubIdStatement
import Theorems.Thm_GlobalTheory_finrank_add_finrank_le_finrank_inf_comap_sub_id


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (M W : Type) [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W] (D R : Submodule k M) [FiniteDimensional k ↥D] (F : M →ₗ[k] M) (B : M →ₗ[k] W →ₗ[k] k), R ≤ D → (∀ x ∈ D, F x ∈ D) → (∀ x ∈ R, ∀ w, B x w = 0) → (∀ x ∈ D, ∀ w, B (F x) w = B x w) → (∀ w, (∀ x ∈ D, B x w = 0) → w = 0) → finrank k W + finrank k ↥R ≤ finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
  first | exact @GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id | exact GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id | (intros; apply GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id <;> assumption)
end _root_.GlobalTheory.T
