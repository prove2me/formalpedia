-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_map_compAt_mem_SU_3b573f666034
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:47.494685+00:00
-- url     : https://prove2.me/submissions/4e126716-2740-49ef-9fab-c2ef25056fd2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PTruncation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_inclA_fa3b000bd639
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_sigA_4ec6939ea22f
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open Classical
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox
theorem _root_.solution (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) {x : Matrix (Fin N) (Fin N) (AE F E)}
    (hx : x ∈ SU (sigA c) (J.map (inclA F E))) :
    x.map (compAt E v) ∈ SU (sigV c v).toRingHom (J.map (inclV E v)) := by
  obtain ⟨hdet, hu⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · have h := congrArg (compAt E v).mapMatrix hu
    simp only [map_mul, RingHom.mapMatrix_apply] at h
    have hJ : (J.map (inclA F E)).map (compAt E v) = J.map (inclV E v) := by
      ext i j; simp [compAt_inclA]
    have hs : (x.map (sigA c)).map (compAt E v) = (x.map (compAt E v)).map (sigV c v).toRingHom := by
      ext i j; simp [compAt_sigA]
    rw [hJ, hs, Matrix.transpose_map] at h
    exact h
end GroundTheory.Heights₂.Heights.StrongApprox
