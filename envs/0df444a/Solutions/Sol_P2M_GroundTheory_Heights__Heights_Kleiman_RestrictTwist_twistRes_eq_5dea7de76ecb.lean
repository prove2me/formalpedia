-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_eq_5dea7de76ecb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:32:02.959477+00:00
-- url     : https://prove2.me/submissions/5a67bc61-e5dc-4773-bf9c-c26eed29dadd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_div_eq_of_isFrac_5a8880453f6c

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
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) {c : ℤ} (I : Chart y) {z : Ω}
    {t : Poly S N × Poly S N × ℕ × ℕ} (h : IsFrac x c I.1 z t) :
    twistRes S x y c z = aeval y t.1 / aeval y t.2.1 := by
  classical
  have hex : ∃ (I : Chart y) (t : Poly S N × Poly S N × ℕ × ℕ), IsFrac x c I.1 z t := ⟨I, t, h⟩
  rw [twistRes, dif_pos hex]
  have h₀ := Classical.choose_spec (Classical.choose_spec hex)
  exact div_eq_of_isFrac hle h₀ h
    (eval_ne_zero_of_mem_monos (liftChart hxy (Classical.choose hex)) h₀.1)
    (eval_ne_zero_of_mem_monos (liftChart hxy I) h.1)
    (eval_ne_zero_of_mem_monos (Classical.choose hex) h₀.1) (eval_ne_zero_of_mem_monos I h.1)
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
