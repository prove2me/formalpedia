-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_lift_frac_3934fd766e28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:35:06.277795+00:00
-- url     : https://prove2.me/submissions/708be78e-c595-4828-aa2c-3f622d48365c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_map_eq_C_mul_8251d5a003dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_monos_map_70b2a16a9725
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_isHomogeneous_bb0f48dbdc12


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial Kleiman
noncomputable section
variable {S : Type*} [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] {O : Type*} [CommRing O] [Algebra S O]
  [IsLocalization.AtPrime O 𝔪] {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
  {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution {I : Chart x} {f s : Poly O N} {e : ℕ} (hf : f.IsHomogeneous e)
    (hs : s ∈ monos I.1) (hse : s.IsHomogeneous e) :
    ∃ t : S, t ∉ 𝔪 ∧ ∃ g s₀ : Poly S N, g.IsHomogeneous e ∧ s₀ ∈ monos I.1 ∧ s₀.IsHomogeneous e ∧
      map (algebraMap S O) g = C (algebraMap S O t) * f ∧
      algebraMap S Ω t * (aeval x f / aeval x s) = aeval x g / aeval x s₀ := by
  obtain ⟨t, ht, g, hg, hgc⟩ := exists_map_eq_C_mul 𝔪 f
  obtain ⟨s₀, hs₀, rfl⟩ := exists_monos_map (S := S) hs
  obtain ⟨e₀, he₀⟩ := monos_isHomogeneous hs₀
  have hs0 : map (algebraMap S O) s₀ ≠ 0 := fun h =>
    eval_ne_zero_of_mem_monos I hs (by rw [h, map_zero])
  have hee : e₀ = e := (he₀.map (algebraMap S O)).inj_right hse hs0
  subst hee
  refine ⟨t, ht, g, s₀, ?_, hs₀, he₀, hg, ?_⟩
  · intro d hd
    exact hf (hgc d hd)
  · rw [← aeval_map_algebraMap (A := O) x g, hg, ← aeval_map_algebraMap (A := O) x s₀, map_mul, aeval_C,
      IsScalarTower.algebraMap_apply S O Ω, mul_div_assoc]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
