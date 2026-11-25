-- Prove2me | solution 1 for ReciprocityTheory.Cheb.exists_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:37:19.463174+00:00
-- url     : https://prove2.me/submissions/5ae8e901-34aa-487e-bdce-8641881b9d00

import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe
import Definitions.Def_ReciprocityTheory_Chebotarev_RpowNegFinrankSubOne
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
import Definitions.Def_ReciprocityTheory_Chebotarev_MeanZero
import Definitions.Def_ReciprocityTheory_Chebotarev_LatSum
import Definitions.Def_ReciprocityTheory_Chebotarev_KHoldA
import Theorems.Thm_ReciprocityTheory_Cheb_continuous_gs
import Theorems.Thm_ReciprocityTheory_Cheb_exists_continuousOn_latticeSum
import Theorems.Thm_ReciprocityTheory_Cheb_exists_reps_meanZero
import Theorems.Thm_ReciprocityTheory_Cheb_finrank_latOf
import Theorems.Thm_ReciprocityTheory_Cheb_gs_diff_bound
import Theorems.Thm_ReciprocityTheory_Cheb_norm_gs_embZ_le
import Theorems.Thm_ReciprocityTheory_Cheb_summable_gs
import Theorems.Thm_ReciprocityTheory_Cheb_tsum_latOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units Set
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2,
      F s = ∑' α : b.1, cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E)) := by
  obtain ⟨hle, reps, hmem, hcover, huniq, hper, hmean⟩ := exists_reps_meanZero χ b c hcop
  obtain ⟨R₀, C, hRC⟩ := gs_diff_bound (E := E) χ (∑ β ∈ reps, ‖β‖)
  have hr : -(Module.finrank ℚ E : ℝ) - 1 < -(Module.finrank ℤ (latOf b.1) : ℝ) := by
    rw [finrank_latOf b.2]; linarith
  have hd : ∀ s ∈ Icc (1 : ℝ) 2, ∀ β ∈ reps, ∀ x ∈ latOf (mbc l b.1 c.1), R₀ ≤ ‖x‖ →
      ‖Gs χ s (x + β) - Gs χ s x‖ ≤ C * ‖x‖ ^ (-(Module.finrank ℚ E : ℝ) - 1) := by
    intro s hs β hβ x _ hR
    exact hRC s hs x β (Finset.single_le_sum (f := fun β => ‖β‖) (fun _ _ => norm_nonneg _) hβ) hR
  have hbd : ∀ s ∈ Icc (1 : ℝ) 2, ∀ x ∈ latOf b.1, ‖Gs χ s x‖ ≤ 1 := by
    intro s hs x hx
    obtain ⟨α, -, rfl⟩ := mem_latOf.mp hx
    exact norm_gs_embZ_le χ hs.1 α
  have hsm : ∀ s ∈ Ioc (1 : ℝ) 2, Summable fun α : latOf b.1 => Gs χ s (α : mixedSpace E) := fun s hs =>
    summable_gs χ (latOf b.1) (finrank_latOf b.2) hs.1
  have hct : ∀ x ∈ latOf b.1, ContinuousOn (fun s => Gs χ s x) (Icc 1 2) := fun x _ =>
    (continuous_gs χ x).continuousOn
  obtain ⟨F, hF, hFeq⟩ := exists_continuousOn_latticeSum (latOf b.1) (latOf (mbc l b.1 c.1)) hle reps
    hmem hcover huniq (cfun χ b.1 c.1) hper hmean (fun s => Gs χ s) _ hr ⟨R₀, C, hd⟩ 1 hbd hsm hct
  refine ⟨F, hF, fun s hs => ?_⟩
  rw [hFeq s hs]
  exact tsum_latOf b.1 (fun x => cfun χ b.1 c.1 x * Gs χ s x)
end ReciprocityTheory.Cheb
