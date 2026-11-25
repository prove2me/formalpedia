-- Prove2me | solution 1 for PositivityTheory.CW.eigenspaces_orthogonal_of_calculus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:39.940906+00:00
-- url     : https://prove2.me/submissions/7ffd1b5c-889e-4782-bbb1-d1cd69c78b71

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigenspacesOrthogonalOfCalculus
import Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_Lsym
import Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_beta_smul_left
import Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_beta_smul_right

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
namespace PositivityTheory.CW
theorem _root_.solution : A0 → FunctionalCalculusLaws → EigenspacesOrthogonalAlt := by
  intro hA0 hA11b n ε V _ _ E h ι b μ hB φ ν ν' v w hne hv hw
  obtain ⟨-, -, hZ, -⟩ := hA0 n ε V E h
  obtain ⟨hfc, -⟩ := hA11b n ε V E h ι b μ hB
  have hcomm : ∀ c d, ε c = ε d → ∀ z, fc b μ φ (E c d z) = E c d (fc b μ φ z) := by
    intro c d hcd z
    have heig : ∀ i, Eig ε E (μ i) (E c d (b i)) := by
      intro i
      have hz := congrArg (fun T : Module.End ℂ V => T (b i)) (hZ c d hcd)
      simp only [Z, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at hz
      show casimirK ε E (E c d (b i)) = ((μ i : ℝ) : ℂ) • E c d (b i)
      rw [sub_eq_zero.mp hz, show casimirK ε E (b i) = ((μ i : ℝ) : ℂ) • b i from hB.eig i, map_smul]
    have hT : (fc b μ φ).comp (E c d) = (E c d).comp (fc b μ φ) := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply]
      rw [hfc φ (μ i) _ (heig i), hfc φ (μ i) _ (hB.eig i), map_smul]
    exact LinearMap.congr_fun hT z
  have hL := EigenspaceOrthogonality.Lsym (A := fc b μ φ) h.gl h.uni hcomm v w
  rw [show casimirK ε E v = ((ν : ℝ) : ℂ) • v from hv,
    show casimirK ε E w = ((ν' : ℝ) : ℂ) • w from hw,
    EigenspaceOrthogonality.beta_smul_left, EigenspaceOrthogonality.beta_smul_right] at hL
  have hm : (((ν : ℝ) : ℂ) - ((ν' : ℝ) : ℂ)) * beta ε E (fc b μ φ) v w = 0 := by
    rw [sub_mul, hL, sub_self]
  rcases mul_eq_zero.mp hm with h0 | h0
  · exact absurd (Complex.ofReal_injective (sub_eq_zero.mp h0)) hne
  · exact h0
end PositivityTheory.CW
