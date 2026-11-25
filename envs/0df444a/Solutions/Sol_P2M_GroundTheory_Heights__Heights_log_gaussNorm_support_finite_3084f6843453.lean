-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_log_gaussNorm_support_finite_3084f6843453
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:57:08.605421+00:00
-- url     : https://prove2.me/submissions/15e489a1-9683-419c-8c28-b823bcf08281

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_gaussNormOf_eq_b0903c48cd28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_eq_gaussNormOf_d4ed71b31023
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_adicAbv_mulSupport_finite_ae38e0238065

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type*} {f : MvPolynomial ι K} (hf : f ≠ 0) :
    (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (gaussNorm v f)).Finite := by
  classical
  refine (Set.Finite.biUnion (s := (f.support : Set (ι →₀ ℕ))) f.support.finite_toSet
    fun m hm => adicAbv_mulSupport_finite (K := K) (mem_support_iff.mp hm)).subset ?_
  intro v hv
  rw [Function.mem_support] at hv
  by_contra hc
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hc
  apply hv
  have h1 : gaussNorm v f = 1 := by
    apply le_antisymm
    · refine gaussNormOf_le _ zero_le_one fun m => ?_
      by_cases hm : m ∈ f.support
      · exact (hc m hm).le
      · rw [notMem_support_iff.mp hm, map_zero]
        exact zero_le_one
    · obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq (NumberField.HeightOneSpectrum.adicAbv K v) hf
      rw [gaussNorm_eq_gaussNormOf, h, hc m hm]
  rw [h1, Real.log_one]
end GroundTheory.Heights₂.Heights
