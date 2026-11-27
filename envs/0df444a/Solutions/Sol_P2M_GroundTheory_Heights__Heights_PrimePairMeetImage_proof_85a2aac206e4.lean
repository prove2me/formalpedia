-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimePairMeetImage_proof_85a2aac206e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:17.185889+00:00
-- url     : https://prove2.me/submissions/6fb6f7b0-dfe8-4e7b-adac-2a695dd5dfee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimePairMeetImage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PImageDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBadSetSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HeightCoheightQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPrimePairMeetImage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimePairMeetImage_projHom_not_injective_7535f594d16c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_eval_pullback_94d345000549


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace PrimePairMeetImage
theorem _root_.solution (hF : FiniteFibresDimLe.Statement) : PrimePairMeetImage.Statement := by
  classical
  intro n d Q Q' A hQ hQ' hne hfin hfin'
  have hker : ∀ P ∈ (Q ⊔ Q').minimalPrimes,
      ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧ ComplexSets.pullback A e ∈ P := by
    intro P hPm
    have hni := PrimePairMeetImage.projHom_not_injective hF A hQ hQ' hne hfin hfin' hPm.1.1 hPm.1.2
    rw [injective_iff_map_eq_zero] at hni
    obtain ⟨e, he0, hne0⟩ : ∃ e, ComplexSets.projHom P A e = 0 ∧ e ≠ 0 := by
      by_contra hc
      exact hni fun e he => by_contra fun h => hc ⟨e, he, h⟩
    exact ⟨e, hne0, Ideal.Quotient.eq_zero_iff_mem.1 he0⟩
  choose! f hf0 hfP using hker
  have hfs := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) (Q ⊔ Q')
  refine ⟨∏ P ∈ hfs.toFinset, f P,
    Finset.prod_ne_zero_iff.2 fun P hP => hf0 P (hfs.mem_toFinset.1 hP), ?_⟩
  rintro x ⟨hx, hx'⟩
  have hmx : Q ⊔ Q' ≤ RingHom.ker (eval x) :=
    sup_le (fun q hq => RingHom.mem_ker.2 (hx q hq)) (fun q hq => RingHom.mem_ker.2 (hx' q hq))
  have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hmx
  have hPs : P ∈ hfs.toFinset := hfs.mem_toFinset.2 hP
  have hmem : ComplexSets.pullback A (∏ P ∈ hfs.toFinset, f P) ∈ P := by
    rw [← Finset.prod_erase_mul _ _ hPs, map_mul]
    exact P.mul_mem_left _ (hfP P hP)
  rw [← ComplexSets.eval_pullback]
  exact RingHom.mem_ker.1 (hPle hmem)
end PrimePairMeetImage
end GroundTheory.Heights₂.Heights
