-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DataX.freq_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:26:34.588544+00:00
-- url     : https://prove2.me/submissions/93afc65a-1cd7-4a69-9ae7-4133a7481121

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_mem_LZ_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_pairR_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_exists_emb_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.DataX
theorem _root_.solution (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hf : X.IsFreqZ X.g χ) (z : X.Ψ → ℂ)
    (w : 𝓞 E → Fin 2 → Fin 2 → E) (hwi : ∀ γ i k, IsIntegral ℤ (w γ i k))
    (hwh : ∀ γ i k, cc (w γ i k) = w γ k i)
    (hterm : ∀ γ : 𝓞 E, (∑ τ : X.Ψ, ∑ i, ∑ k, χ τ i k * τ.1 (w γ i k)).re =
      2 * (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re) :
    ∃ ω : E, (∀ τ : X.Ψ, z τ = τ.1 ω) ∧
      IsIntegral ℤ (((X.g * (NumberField.discr E).natAbs ^ 2 : ℕ) : E) * ω) := by
  refine X.exists_emb_int z X.g X.g_pos fun γ => ?_
  obtain ⟨k, hk⟩ := hf _ (X.mem_LZ_of (w γ) (hwi γ) (hwh γ))
  rw [X.pairR_of, hterm γ] at hk
  refine ⟨k, ?_⟩
  rw [← hk]
  unfold dEnat
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.G.FD.DataX
