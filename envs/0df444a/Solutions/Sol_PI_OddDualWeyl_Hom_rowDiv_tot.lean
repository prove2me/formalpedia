-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.rowDiv_tot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:26.912615+00:00
-- url     : https://prove2.me/submissions/4a09bc32-c39c-4fb4-b109-de5ed1dabdcc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_good_rowGen
import Theorems.Thm_PI_OddDualWeyl_Hom_toZ
import Theorems.Thm_PI_OddDualWeyl_Hom_ofZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Hom
variable {R : Type} [CommRing R] {k : ℕ}
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}
namespace PI.OddDualWeyl.Hom
theorem _root_.solution (a b : Fin k) (j : ℕ) {f : MvPolynomial (Fin k × Fin k) R} {n : ℕ}
    (hf : IsHomogeneous f n) : IsHomogeneous (rowDiv R a b j f) n := by
  have h := good_rowGen (wt := fun v => (((1 : Fin k × Fin k → ℕ) v : ℕ) : ℤ)) (δ := 0) a b
    (fun s => by simp) (toZ (w := 1) hf) j
  have h2 := ofZ (w := 1) h
  have h3 : ((n : ℤ) + (j : ℤ) * 0).toNat = n := by simp
  rw [h3] at h2
  exact h2
end PI.OddDualWeyl.Hom
