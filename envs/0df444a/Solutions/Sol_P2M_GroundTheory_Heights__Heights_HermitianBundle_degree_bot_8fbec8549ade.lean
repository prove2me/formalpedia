-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_bot_8fbec8549ade
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:56.62723+00:00
-- url     : https://prove2.me/submissions/18d2bfaa-3d0c-4423-9876-cc9aadeac494

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight

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
namespace GroundTheory.Heights₂.Heights
namespace HermitianBundle
theorem _root_.solution {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K) :
    E.degree ⊥ = 0 := by
  unfold HermitianBundle.degree HermitianBundle.degreeWith
  have hc : Nat.card ((⊥ : Submodule (𝓞 K) E.carrier) ⧸ Submodule.span (𝓞 K) (Set.range
      (HermitianBundle.exists_linearIndependent_rank E ⊥).choose)) = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    exact ⟨inferInstance, inferInstance⟩
  rw [hc]
  have hz : E.rank ⊥ = 0 := by simp [HermitianBundle.rank]
  have hg : ∀ (m : ℕ) (hm : m = 0) (σ : K →+* ℂ) (f : Fin m → E.carrier),
      ‖HermitianBundle.gramDet E σ f‖ = 1 := by
    intro m hm σ f
    subst hm
    simp [HermitianBundle.gramDet]
  simp [hg _ hz]
end HermitianBundle
end GroundTheory.Heights₂.Heights
