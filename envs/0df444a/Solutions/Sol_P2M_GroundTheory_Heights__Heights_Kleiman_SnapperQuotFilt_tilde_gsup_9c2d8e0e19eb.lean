-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_tilde_gsup_9c2d8e0e19eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:03:19.625378+00:00
-- url     : https://prove2.me/submissions/aeeeb528-c821-459e-9e0d-7ef544192250

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_HomogeneousComponentMulForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_tilde_mono_f91653fcd91e

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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
theorem _root_.solution (M M' : FinGradedSub (S := S) (x := x) E) (c : ℤ) (I : Chart x) :
    (gsup M M').tilde c I = M.tilde c I ⊔ M'.tilde c I := by
  refine le_antisymm (Submodule.span_le.mpr ?_)
    (sup_le (tilde_mono (fun _ => le_sup_left) c I) (tilde_mono (fun _ => le_sup_right) c I))
  rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hm
  rw [smul_add]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨p, s, a, e, hs, hse, hp, hae, rfl⟩)
    (Submodule.subset_span ⟨q, s, a, e, hs, hse, hq, hae, rfl⟩)
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
