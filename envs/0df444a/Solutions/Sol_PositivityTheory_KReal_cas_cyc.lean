-- Prove2me | solution 1 for PositivityTheory.KReal.cas_cyc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:04:31.363225+00:00
-- url     : https://prove2.me/submissions/8230f312-ec43-40fe-abd2-4a0bba861e53

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Theorems.Thm_PositivityTheory_KReal_cas_comm
import Theorems.Thm_PositivityTheory_KReal_cas_hw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Ix r s → Ix r s → Module.End ℂ M}
    (hρ : GlK ρ) {μ : Ix r s → ℚ} {f : M} (hf : HwK ρ μ f) :
    ∀ x ∈ cycK ρ f, casK ρ x = ((casW μ : ℚ) : ℂ) • x := by
  intro x hx
  have hle : cycK ρ f ≤ LinearMap.ker (casK ρ - ((casW μ : ℚ) : ℂ) • 1) := by
    refine sInf_le ⟨?_, ?_⟩
    · simp [LinearMap.mem_ker, cas_hw hρ hf]
    · intro a b hab y hy
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_eq_zero] at hy ⊢
      rw [← Module.End.mul_apply, cas_comm hρ hab, Module.End.mul_apply, hy, map_smul]
  have h := hle hx
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] using h
end PositivityTheory.KReal
