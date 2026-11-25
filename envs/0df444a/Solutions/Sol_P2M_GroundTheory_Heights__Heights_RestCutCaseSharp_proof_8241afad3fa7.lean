-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutCaseSharp_proof_8241afad3fa7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:20:44.252562+00:00
-- url     : https://prove2.me/submissions/3568130a-6027-40b4-bcb7-da54a4195ae7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutCaseSharp
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_smallPowerSum_isHomogeneous_cdf6a1058f11

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace RestCutCaseSharp
theorem _root_.solution (h₁ : RestTerms.RestBound.Statement) (h₂ : RestCutCaseCompare.Statement)
    (h₃ : RestCutCaseDecomp.Statement) (h₄ : RestCutTermEq.Statement)
    (h₅ : RestCutPrimeEq.Statement) : RestCutCaseSharp.Statement := by
  intro f j k r a cs e hf hj hk hr ha hN hra hF hJ hlie I hI vol hvol P hP B₀ hB φ
  have hB' : 4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ := by rw [hN]; exact hB
  obtain ⟨hex0, hall0⟩ := h₁ f r a cs B₀ hf hr ha hB'
  obtain ⟨c, hcomp, hdeg⟩ := h₂ f j k r a cs e hf hr ha hN hJ I hI
  obtain ⟨⟨Q₀, hQ₀, hQ₀h⟩, hexQ⟩ := h₃ f j k r a cs e hf hN (by omega) hF hex0
  refine ⟨hexQ, fun Q hQ => ?_⟩
  have hQ' : IsPowerSumDecomposition f j k
      (restTransport f j k (r + a) e (RestTerms.restPolynomial f r a cs)) Q := by
    rw [hF]; exact hQ
  have hterm : ∀ m : ℕ, 2 ≤ m → m ≤ r + a → ∀ τ τ' : Fin f,
      I (restTransport f j k (r + a) e (RestTerms.smallPowerSum f r a cs (m - 1) τ') * Q τ m) =
        c * RestTerms.flagIntegral f (r + a)
          (RestTerms.smallPowerSum f r a cs (m - 1) τ' * Q₀ m τ) := fun m hm2 hmN τ τ' =>
    h₄ f j k (r + a) e I c hcomp _ Q₀ hQ₀ hQ₀h Q hQ' m (by omega) hmN τ _
      (KRest.smallPowerSum_isHomogeneous f r a cs (m - 1) τ')
  obtain ⟨s, ε, hε, heq⟩ := h₅ f j k r a cs e hf hj hk hN hlie I hI c Q₀ Q hQ hterm φ
  obtain ⟨hsum, hbound⟩ := hall0 Q₀ hQ₀ s ε hε P
  have hfun : (fun p : primesAbove P B₀ => restAt f j k I vol φ Q p.1) =
      fun p : primesAbove P B₀ => (vol * c) * RestTerms.restPrimeModel f r a cs Q₀ s ε p.1 :=
    funext fun p => heq vol p.1
  rw [hfun]
  refine ⟨(hsum.of_abs).mul_left _, ?_⟩
  rw [tsum_mul_left, abs_mul, abs_mul, abs_of_pos hvol, hdeg, abs_mul]
  have hn : (((f * (r * a) + 1 : ℕ)) : ℝ) = ((f * j * k : ℕ) : ℝ) + 1 := by
    rw [hra]; push_cast; ring
  rw [hn] at hbound
  have hc : 0 ≤ vol * |c| := by positivity
  calc vol * |c| * |∑' p : primesAbove P B₀, RestTerms.restPrimeModel f r a cs Q₀ s ε p.1|
      ≤ vol * |c| * (1.6 * (((f * j * k : ℕ) : ℝ) + 1) * |(RestTerms.fibreDegree f r a cs : ℝ)|) :=
        mul_le_mul_of_nonneg_left hbound hc
    _ = 1.6 * (((f * j * k : ℕ) : ℝ) + 1) * vol * (|c| * |(RestTerms.fibreDegree f r a cs : ℝ)|) := by
        ring
end RestCutCaseSharp
end GroundTheory.Heights₂.Heights
