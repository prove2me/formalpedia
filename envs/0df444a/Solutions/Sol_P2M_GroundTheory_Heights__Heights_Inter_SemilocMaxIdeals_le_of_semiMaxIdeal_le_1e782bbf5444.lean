-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_le_of_semiMaxIdeal_le_1e782bbf5444
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:23:25.166272+00:00
-- url     : https://prove2.me/submissions/1e9cdd04-f944-41bf-a0fe-650accbb4736

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocMaxIdeals
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_fracHom_ne_zero_e8d84d906420
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_frac_mem_c6800c83aff2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_mem_semiMaxIdeal_iff_9811936ba746
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_scale_b69a487db7c3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
open regularityLocalFlat_holds
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (P : Ideal (MRing ι)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι)))
variable {P 𝒲}
namespace GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
theorem _root_.solution (hfin : 𝒲.Finite) (h𝒲 : ∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W)
    {W₁ W₂ : Ideal (MRing ι)} (h₁ : W₁ ∈ 𝒲) (h₂ : W₂ ∈ 𝒲) [IsLocalRing (locRing P W₁)]
    [IsLocalRing (locRing P W₂)] (hle : semiMaxIdeal P 𝒲 W₁ h₁ ≤ semiMaxIdeal P 𝒲 W₂ h₂) : W₁ ≤ W₂ := by
  obtain ⟨⟨hp1, ⟨S, hS, hW1⟩, -⟩, hP1⟩ := h𝒲 W₁ h₁
  obtain ⟨⟨hp2, -, hr2⟩, hP2⟩ := h𝒲 W₂ h₂
  have hmem : ∀ f ∈ S, f ∈ W₁ := fun f hf => hW1 ▸ Ideal.subset_span hf
  rw [hW1, Ideal.span_le]
  intro f hfS
  obtain ⟨a, hfa⟩ := hS f hfS
  obtain ⟨t, h, d, ht, hh, htW, hhW⟩ := exists_scale 𝒲 hfin (fun W hW => (h𝒲 W hW).1) a hr2 hp2
  have hhP : h ∉ P := fun hP => hhW W₁ h₁ (hP1 hP)
  let b : semiLocRing P 𝒲 := ⟨_, frac_mem P 𝒲 (homog_mul hfa ht) hh hhP hhW⟩
  have hb : (b : FractionRing (MRing ι ⧸ P)) * fracHom P h = fracHom P (f * t) :=
    div_mul_cancel₀ _ (fracHom_ne_zero P hhP)
  have h1 : b ∈ semiMaxIdeal P 𝒲 W₁ h₁ :=
    (mem_semiMaxIdeal_iff P 𝒲 h₁ hP1 b (homog_mul hfa ht) hh (hhW W₁ h₁) hb).mpr
      (W₁.mul_mem_right t (hmem f hfS))
  have h2 := (mem_semiMaxIdeal_iff P 𝒲 h₂ hP2 b (homog_mul hfa ht) hh (hhW W₂ h₂) hb).mp (hle h1)
  exact (hp2.mem_or_mem h2).resolve_right htW
end GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
