-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_exists_eq_mul_of_le_2bf3338d8737
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:42:11.305513+00:00
-- url     : https://prove2.me/submissions/713fe2c8-5c89-4d28-9605-1efc5ed60930

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GlobalFunctionsIntegralSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestriction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutOneGenerator
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_exists_restrict_mul_4a5c4ef82f99
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CutOneGenerator_restrict_twist_eq_zero_e84501a9b4aa

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
    (hpp : primeOf (S := k) y = pp) (J : Chart y) {s : Ω} (hs : s ∈ Q.sub (liftChart hxy J))
    (hle : Q.sub (liftChart hxy J) ≤ (Q.twist (idealSys x pp)).sub (liftChart hxy J) ⊔
      Submodule.span (chartRing k x (liftChart hxy J)) {s}) {t : K'} (ht : t ∈ Q'.sub J) :
    ∃ b ∈ chartRing k y J, t = b * ρ s := by
  rw [← hR.span J] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨q, hq, rfl⟩ := ht
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp (hle hq)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨hu', hu0⟩ := restrict_twist_eq_zero hR hpp J hu
    obtain ⟨b, hb, he⟩ := exists_restrict_mul hR J a.2 hs
    refine ⟨b, hb, ?_⟩
    rw [hR.add J u hu' _ ((Q.sub _).smul_mem a hs), hu0, zero_add, chartRing_smul_def, he]
  | zero => exact ⟨0, zero_mem _, (zero_mul _).symm⟩
  | add t t' _ _ ht ht' =>
    obtain ⟨b, hb, rfl⟩ := ht
    obtain ⟨b', hb', rfl⟩ := ht'
    exact ⟨b + b', add_mem hb hb', (add_mul _ _ _).symm⟩
  | smul c t _ ht =>
    obtain ⟨b, hb, rfl⟩ := ht
    exact ⟨c * b, mul_mem c.2 hb, by rw [chartRing_smul_def, mul_assoc]⟩
end GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator
