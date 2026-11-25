-- Prove2me | solution 1 for PI.OddDualWeyl.oddFact_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:17:04.351392+00:00
-- url     : https://prove2.me/submissions/9c056e47-7ca0-45c2-9bdd-1747fce7c8e8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose
import Theorems.Thm_PI_OddDualWeyl_lamStar_lamStar
import Theorems.Thm_PI_OddDualWeyl_isUnit_invT
import Theorems.Thm_PI_OddDualWeyl_invT_invT
import Theorems.Thm_PI_OddDualWeyl_isUnit_revInv
import Theorems.Thm_PI_OddDualWeyl_revInv_revInv
import Theorems.Thm_PI_OddDualWeyl_dir1

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
variable {K : Type} [Field K]
namespace PI.OddDualWeyl
theorem _root_.solution (hC1 : ∀ (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
      ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam) f f')
    (hH : HomW) (hB : Bk) (hE : EV) (hU : Uniq) (hDB : DualB) (hS : SgnPM) (hG : GStep)
    (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) : OddFact (K := K) O m lam := by
  intro g hg
  refine ⟨dir1 hC1 hH hB hE hU hDB hS hG O m lam g hg, ?_⟩
  intro F' hF'
  have hfw := dir1 hC1 hH hB hE hU hDB hS hG O m (lamStar lam) ((g⁻¹)ᵀ)
    (isUnit_invT hg)
  rw [lamStar_lamStar, invT_invT hg] at hfw
  obtain ⟨F, hF, hid⟩ := hfw F' hF'
  refine ⟨F, hF, fun z hz => ?_⟩
  have := hid (revCol (z⁻¹)ᵀ) (isUnit_revInv hz)
  rw [revInv_revInv hz] at this
  exact this.symm
end PI.OddDualWeyl
