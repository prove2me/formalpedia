-- Prove2me | solution 1 for PI.VolSemiDirect.W.stabilizer_fixes_frame_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:01.248799+00:00
-- url     : https://prove2.me/submissions/3613119d-8b08-486f-8253-30ac9511c9ef

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SemiDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_StabilizerFixesFrameVector
import Theorems.Thm_PI_VolSemiDirect_W_stabilizer_fixes_frame_vector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolSemiDirect.W
theorem _root_.solution {r : ℕ} (P : Frame E M r) {g : HA R σ J} (hg : g ∈ S0 R σ J P)
    (x : Fin M → R ⊗[F] E) (hx : x ∈ spanR (F := F) R P.e Set.univ) : lin R σ J g x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, _, rfl⟩ := hy
    exact stabilizer_fixes_frame_vector R σ J P hg a
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]
end PI.VolSemiDirect.W
