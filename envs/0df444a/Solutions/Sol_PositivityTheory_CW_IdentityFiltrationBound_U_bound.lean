-- Prove2me | solution 1 for PositivityTheory.CW.IdentityFiltrationBound.U_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:25:32.885319+00:00
-- url     : https://prove2.me/submissions/6dfe4d4e-4694-41ae-b11b-fa744aee8a9b

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EnvelopingAlgebraGrowthBound
import Theorems.Thm_PositivityTheory_CW_IdentityFiltrationBound_le_N

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.IdentityFiltrationBound
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace PositivityTheory.CW.IdentityFiltrationBound
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (u : Module.End ℂ V) (hu : u ∈ U E k) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v, ‖u v‖ ≤ c * N E k v := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact ⟨1, zero_le_one, fun v => by simpa [wd] using le_N E hl v⟩
  | zero => exact ⟨0, le_rfl, fun v => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, h⟩ := hx
    obtain ⟨d, hd, h'⟩ := hy
    refine ⟨c + d, add_nonneg hc hd, fun v => ?_⟩
    calc ‖(x + y) v‖ ≤ ‖x v‖ + ‖y v‖ := by simpa using norm_add_le (x v) (y v)
      _ ≤ c * N E k v + d * N E k v := add_le_add (h v) (h' v)
      _ = (c + d) * N E k v := by ring
  | smul a x _ hx =>
    obtain ⟨c, hc, h⟩ := hx
    refine ⟨‖a‖ * c, mul_nonneg (norm_nonneg _) hc, fun v => ?_⟩
    calc ‖(a • x) v‖ = ‖a‖ * ‖x v‖ := by simp [norm_smul]
      _ ≤ ‖a‖ * (c * N E k v) := mul_le_mul_of_nonneg_left (h v) (norm_nonneg _)
      _ = ‖a‖ * c * N E k v := by ring
end PositivityTheory.CW.IdentityFiltrationBound
