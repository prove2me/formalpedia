-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_restrict_twist_eq_zero_e84501a9b4aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:48.662515+00:00
-- url     : https://prove2.me/submissions/6b68ecb5-e956-4ebc-a141-6808ea838549

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GlobalFunctionsIntegralSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestriction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutOneGenerator
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_mem_chartRing_of_mem_idealMod_b0a56f85ec39
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_restrict_zero_2ed7d83dda69
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_exists_restrict_mul_4a5c4ef82f99
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
variable {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {Q : SubSystem k x Ω} {Q' : SubSystem k y K'} {ρ : Ω → K'}
namespace GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator
theorem _root_.solution (hR : RestrictData Q hxy Q' ρ) {pp : Ideal (Poly k N)}
    (hpp : primeOf (S := k) y = pp) (J : Chart y) {z : Ω}
    (hz : z ∈ (Q.twist (idealSys x pp)).sub (liftChart hxy J)) :
    z ∈ Q.sub (liftChart hxy J) ∧ ρ z = 0 := by
  have hgen : ∀ w ∈ Q.sub (liftChart hxy J), ∀ q ∈ idealMod (x := x) pp (liftChart hxy J),
      q * w ∈ Q.sub (liftChart hxy J) ∧ ρ (q * w) = 0 := by
    intro w hw q hq
    have hmw : ∀ a ∈ idealMod (x := x) pp (liftChart hxy J), a * w ∈ Q.sub (liftChart hxy J) :=
      fun a ha => (Q.sub _).smul_mem
        ⟨a, mem_chartRing_of_mem_idealMod (pp := pp) (I := liftChart hxy J) ha⟩ hw
    refine ⟨hmw q hq, ?_⟩
    induction hq using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨f, t, e, hfp, ht, hf, hte, rfl⟩ := ha
      rw [hR.smul J w hw f t e ht hf hte,
        (mem_primeOf_of_isHomogeneous y hf).mp (hpp ▸ hfp), zero_div, zero_mul]
    | zero => rw [zero_mul]; exact restrict_zero hR J
    | add a b ha hb iha ihb =>
      rw [add_mul, hR.add J _ (hmw a ha) _ (hmw b hb), iha, ihb, add_zero]
    | smul c a ha iha =>
      obtain ⟨b, -, hb⟩ := exists_restrict_mul hR J c.2 (hmw a ha)
      rw [chartRing_smul_def, mul_assoc, hb, iha, mul_zero]
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨q, hq, w, hw, rfl⟩ := hz; exact hgen w hw q hq
  | zero => exact ⟨zero_mem _, restrict_zero hR J⟩
  | add a b _ _ ha hb => exact ⟨add_mem ha.1 hb.1, by rw [hR.add J a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
  | smul c a _ ha =>
    refine ⟨(Q.sub _).smul_mem c ha.1, ?_⟩
    obtain ⟨b, -, hb⟩ := exists_restrict_mul hR J c.2 ha.1
    rw [chartRing_smul_def]
    erw [hb]
    rw [ha.2, mul_zero]
end GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator
