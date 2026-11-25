-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_satSub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:05:49.89377+00:00
-- url     : https://prove2.me/submissions/130bbca7-26b4-4625-ab7a-b013104e2ed5

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_proj_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type} [Field K] [NumberField K] {r e : ℕ}
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {k₀ : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b₀ : Fin k₀ → Fin r → K)
    (hb₀ : IsKBasisIn (B ⊓ cutSub K r e) b₀) : satSub B b₀ = B ⊓ cutSub K r e := by
  have hle : Submodule.span K (Set.range b₀) ≤ LinearMap.ker (cutProjK K r e) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (sdd_proj_eq_zero_iff _).mpr (hb₀.1 i).2
  ext x
  simp only [satSub, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨hx, hs⟩
    exact ⟨hx, (sdd_proj_eq_zero_iff x).mp (hle hs)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨hx, hb₀.2.2 x ⟨hx, hc⟩⟩
end ReciprocityTheory.MultiplicativeHeights
