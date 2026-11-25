-- Prove2me | solution 1 for P2M_PI_MirrorSection__uw_inWb_121488a2cc3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:34:11.839881+00:00
-- url     : https://prove2.me/submissions/4f460884-e243-44ad-a199-1e7c29320194

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Theorems.Thm_P2M_PI_MirrorSection__herm_inv_f146d41e237b
import Theorems.Thm_P2M_PI_MirrorSection__herm_esI_b4e3cf5e2800
import Theorems.Thm_P2M_PI_MirrorSection__herm_eI_18f96727ec1f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : inWb k r (h *ᵥ v) := by
  intro l hl
  rcases hl with hl | hl
  · have hle : eI k r ⟨l.val, hl⟩ = l := Fin.ext rfl
    have key : (h *ᵥ v) (eI k r ⟨l.val, hl⟩) = 0 := by
      rw [← herm_esI (h *ᵥ v) ⟨l.val, hl⟩, ← (hh.2.1 ⟨l.val, hl⟩).2, herm_inv hh.1, herm_esI]
      exact hv _ (Or.inl hl)
    rwa [hle] at key
  · have hb : 2 * r + k - l.val < r := by omega
    have hle : esI k r ⟨2 * r + k - l.val, hb⟩ = l := by
      apply Fin.ext
      simp only [esI]
      omega
    have key : (h *ᵥ v) (esI k r ⟨2 * r + k - l.val, hb⟩) = 0 := by
      rw [← herm_eI (h *ᵥ v) ⟨2 * r + k - l.val, hb⟩, ← (hh.2.1 ⟨2 * r + k - l.val, hb⟩).1, herm_inv hh.1,
        herm_eI]
      rw [hle]
      exact hv l (Or.inr hl)
    rwa [hle] at key
end PI.MirrorSection₂
