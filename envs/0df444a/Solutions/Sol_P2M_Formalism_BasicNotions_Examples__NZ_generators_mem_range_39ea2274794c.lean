-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_generators_mem_range_39ea2274794c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:36:29.162013+00:00
-- url     : https://prove2.me/submissions/ec51d418-69e1-4da1-bb3d-928b32d8c04d

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_jB_single_5e18f8ca6be9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution : ∀ v ∈ genB b, v ∈ Set.range (jB σ b) := fun v hv => by
  classical
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  exact ⟨_, jB_single σ b i⟩
end Formalism.BasicNotions.Examples₂.NZ
