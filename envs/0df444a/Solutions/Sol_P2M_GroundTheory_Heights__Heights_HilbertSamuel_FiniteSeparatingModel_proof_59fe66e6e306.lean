-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_proof_59fe66e6e306
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:56:16.964595+00:00
-- url     : https://prove2.me/submissions/90727d1c-2d3c-47e9-b24e-79d37332ee4d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiniteSeparatingModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsNoetherProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsLiftToZeros
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiniteSeparatingModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_aeval_eval__9cd9ca05b2cb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_monic_coeff_zero_ne_315458a1ed4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_minpoly_426ccccab7a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiniteSeparatingModel_exists_separating_b05fbc61f580

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace FiniteSeparatingModel
theorem _root_.solution (hN : NoetherProjection.Statement)
    (hL : RootsLiftToZeros.Statement) : FiniteSeparatingModel.Statement := by
  classical
  intro σ _ P f x hP hf _
  obtain ⟨e, ℓ, hinj, hint⟩ := hN σ P hP.ne_top
  choose p hpm hp using hint
  let yx : Fin e → ℂ := fun j => aeval x (ℓ j)
  let S : Finset (σ → ℂ) := Fintype.piFinset fun i =>
    ((p (X i)).map (aeval yx).toRingHom).roots.toFinset
  have hS : ∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) → (fun j => aeval z (ℓ j)) = yx → z ∈ S := by
    intro z hz hzl
    rw [Fintype.mem_piFinset]
    intro i
    rw [Multiset.mem_toFinset, Polynomial.mem_roots ((hpm _).map _).ne_zero, Polynomial.IsRoot,
      Polynomial.eval_map, ← hzl]
    have := hz _ (hp (X i))
    rwa [FiniteSeparatingModel.aeval_eval₂, aeval_X] at this
  obtain ⟨u, hu⟩ := FiniteSeparatingModel.exists_separating S x
  obtain ⟨G, hGm, hGu, hGdvd⟩ :=
    FiniteSeparatingModel.exists_minpoly hP ℓ hinj (fun g => ⟨p g, hpm g, hp g⟩) u
  obtain ⟨q, -, hqf, hq0⟩ :=
    FiniteSeparatingModel.exists_monic_coeff_zero_ne hP ℓ hf (hpm f) (hp f)
  refine ⟨e, ℓ, u, G, q.coeff 0, 1, hGm, hq0, one_ne_zero,
    fun i => ⟨p (X i), hpm _, fun z hz => ?_⟩, fun z hz => ?_, fun z hz hc hfz => ?_,
    fun y t _ ht => hL σ P e ℓ u G (fun g => ⟨p g, hpm g, hp g⟩) hGdvd y t ht,
    fun z hz hzl hzu => hu z (hS z hz hzl) hzu⟩
  · have := hz _ (hp (X i))
    rwa [FiniteSeparatingModel.aeval_eval₂, aeval_X] at this
  · have := hz _ hGu
    rwa [FiniteSeparatingModel.aeval_eval₂] at this
  · apply hc
    have := hz _ hqf
    rw [FiniteSeparatingModel.aeval_eval₂, hfz, Polynomial.eval₂_at_zero] at this
    exact this
end FiniteSeparatingModel
end GroundTheory.Heights₂.Heights.HilbertSamuel
