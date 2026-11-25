-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FramePlaneGraph_zeroSetEuc_sup_span_494301978f7d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:50.228881+00:00
-- url     : https://prove2.me/submissions/e313f14b-5b1b-4ae2-ad21-54da078c5e84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFramePlaneGraph

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
noncomputable section
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace FramePlaneGraph
theorem _root_.solution {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (q : MvPolynomial (Fin n) ℂ) :
    zeroSetEuc (J ⊔ Ideal.span {q}) = zeroSetEuc J ∩ {z | eval (fun i => z i) q = 0} := by
  ext z
  simp only [zeroSetEuc, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun p hp => h p (Ideal.mem_sup_left hp),
      h q (Ideal.mem_sup_right (Ideal.mem_span_singleton_self q))⟩
  · rintro ⟨h1, h2⟩ p hp
    have hle : J ⊔ Ideal.span {q} ≤ RingHom.ker (eval fun i => z i) :=
      sup_le (fun p hp => RingHom.mem_ker.mpr (h1 p hp))
        ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr h2))
    exact RingHom.mem_ker.mp (hle hp)
end FramePlaneGraph
end GroundTheory.Heights₂.Heights
