-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_X_pow_smul_mem_c63731a7437b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:35.008009+00:00
-- url     : https://prove2.me/submissions/b1d447ca-abd5-4f52-bd6d-7833341b88c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_degZ_zero_c867a29a5255

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
theorem _root_.solution (hM : IsMultigrading ι M piece) (v : Σ k, ι k) (n : ℕ) :
    ∀ (m : K → ℤ) (x : M), x ∈ piece m →
      ((X v : MRing ι F) ^ n) • x ∈ piece (m + degZ (n • blockWeight ι v)) := by
  induction n with
  | zero => intro m x hx; simpa [degZ_zero] using hx
  | succ n ih =>
    intro m x hx
    rw [pow_succ, mul_smul]
    have h := ih _ _ (hM.smul_mem v m x hx)
    convert h using 2
    funext k
    simp only [degZ, unitDeg, blockWeight, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> push_cast <;> ring
end GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
