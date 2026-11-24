-- Prove2me | solution 1 for P2M_PI_MirrorSection__maps_low_ff5c1839ec93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:42:25.1298+00:00
-- url     : https://prove2.me/submissions/7c194a03-a02f-4882-b099-eae2f6138b7c

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI

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
theorem _root_.solution {n : B.Mat k r} (hn : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      n i (eI k r a) = if i = eI k r a then 1 else 0) {a : ℕ} (har : a ≤ r) :
    ∀ y ∈ lowS k r a, n *ᵥ y ∈ lowS k r a := by
  intro y hy i hi
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : a ≤ l.val
  · rw [hy l hl, mul_zero]
  · have hlr : l.val < r := by omega
    have hle : (eI k r ⟨l.val, hlr⟩) = l := Fin.ext rfl
    have := hn ⟨l.val, hlr⟩ i (by simp; omega)
    rw [hle] at this
    rw [this, if_neg (by intro h; rw [h] at hi; omega), zero_mul]
end PI.MirrorSection₂
