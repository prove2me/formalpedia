-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_idealSys_localize_58e57dfdf4ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:13.092928+00:00
-- url     : https://prove2.me/submissions/0c41a257-4899-4f4c-92df-09ac27f81745

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulMemSecsTwistIdealSys
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_lift_frac_3934fd766e28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_exists_inv_algebraMap_079c35648306
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_map_mem_monos_baseChange_b5bafc269c9f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_span_baseChange_span_614cec3597f7


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
include 𝔪
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution (pp' : Ideal (Poly O N)) :
    idealSys x pp' =
      (idealSys x (pp'.comap (map (algebraMap S O) : Poly S N →+* Poly O N))).baseChange O := by
  refine SubSystem.ext_sub fun I => ?_
  change idealMod pp' I = Submodule.span (chartRing O x I)
    (idealMod (pp'.comap (map (algebraMap S O) : Poly S N →+* Poly O N)) I : Set Ω)
  simp only [idealMod]
  rw [span_baseChange_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    obtain ⟨t, ht, g, s₀, hg, hs₀, hs₀e, hmap, hval⟩ := exists_lift_frac 𝔪 hfe hs hse
    obtain ⟨u, hu⟩ := exists_inv_algebraMap 𝔪 (O := O) (Ω := Ω) ht
    have hg' : g ∈ pp'.comap (map (algebraMap S O) : Poly S N →+* Poly O N) := by
      rw [Ideal.mem_comap]
      change map (algebraMap S O) g ∈ pp'
      rw [hmap]
      exact Ideal.mul_mem_left _ _ hf
    have e' : aeval x f / aeval x s = (⟨algebraMap O Ω u, Subalgebra.algebraMap_mem _ u⟩ : chartRing O x I) •
        (aeval x g / aeval x s₀) := by
      rw [chartRing_smul_def, ← hval, ← mul_assoc, hu, one_mul]
    rw [SetLike.mem_coe, e']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, s₀, e, hg', hs₀, hg, hs₀e, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨g, s, e, hg, hs, hge, hse, rfl⟩
    exact Submodule.subset_span ⟨map (algebraMap S O) g, map (algebraMap S O) s, e, hg,
      map_mem_monos_baseChange hs, hge.map _, hse.map _, by
        rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
