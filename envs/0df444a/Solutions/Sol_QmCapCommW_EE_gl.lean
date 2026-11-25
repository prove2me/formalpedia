-- Prove2me | solution 1 for QmCapCommW.EE_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:09.347634+00:00
-- url     : https://prove2.me/submissions/906a807e-d630-4557-86eb-07612130915c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open QmCapCommW
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace QmCapCommW
theorem _root_.solution (hC : CapCongr) (hP : EabPres) (hG : EabGlLev) (hD : IsOpen D) :
    GlRel (EE (E := E) (i := i) hP hD) := by
  unfold GlRel
  unfold EabGlLev at hG
  have loc : ∀ (a b c d : Fin (mdim k r i)) (x : SS k r i D E) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D),
      (EE hP hD a b (EE hP hD c d x)).1 ⟨g, hg⟩ =
        EH k r (posL k r i a) (posL k r i b) (EH k r (posL k r i c) (posL k r i d) (ext0 x.1)) g := by
    intro a b c d x g hg
    show EH k r (posL k r i a) (posL k r i b) (ext0 (TT c d x.1)) g = _
    exact (hC E k r i D a b (EH k r (posL k r i c) (posL k r i d) (ext0 x.1)) (ext0 (TT c d x.1)) hD
      (fun g' hg' => by rw [extension_by_zero_apply hg']; rfl) g hg).symm
  intro a b c d
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext q
  obtain ⟨g, hg⟩ := q
  have key := hG E k r i D a b c d (ext0 x.1) hD x.2 g hg
  change (EE hP hD a b (EE hP hD c d x)).1 ⟨g, hg⟩ - (EE hP hD c d (EE hP hD a b x)).1 ⟨g, hg⟩ = _
  rw [loc a b c d x g hg, loc c d a b x g hg, key]
  split_ifs <;> rfl
end QmCapCommW
