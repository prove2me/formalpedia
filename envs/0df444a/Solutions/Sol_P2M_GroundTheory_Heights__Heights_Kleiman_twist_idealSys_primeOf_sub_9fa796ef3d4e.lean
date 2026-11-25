-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twist_idealSys_primeOf_sub_9fa796ef3d4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:25.128677+00:00
-- url     : https://prove2.me/submissions/5e17f088-6795-47f9-9168-0276ff38127d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
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
universe u v w u₁ v₁ w₁
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
omit [Module k E] [IsScalarTower k Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (F : SubSystem k x E) (I : Chart x) :
    (F.twist (idealSys x (primeOf (S := k) x))).sub I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨q, hq, y, -, rfl⟩
  have hq0 : q = 0 := by
    have h0 : idealMod (primeOf (S := k) x) I = ⊥ := by
      refine Submodule.span_eq_bot.mpr ?_
      rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
      rw [(mem_primeOf_of_isHomogeneous x hfe).mp hf, zero_div]
    have hq' : q ∈ (⊥ : Submodule (chartRing k x I) Ω) := h0 ▸ hq
    exact (Submodule.mem_bot _).mp hq'
  rw [hq0, zero_smul]
end GroundTheory.Heights₂.Heights.Kleiman
