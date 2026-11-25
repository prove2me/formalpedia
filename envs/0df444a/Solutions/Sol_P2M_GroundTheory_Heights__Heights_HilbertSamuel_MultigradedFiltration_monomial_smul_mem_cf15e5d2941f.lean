-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_monomial_smul_mem_cf15e5d2941f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:04:21.267073+00:00
-- url     : https://prove2.me/submissions/bfde6894-6b50-4876-94c4-f97b15ffcbf3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_degZ_add_18174cc39b3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_degZ_zero_c867a29a5255
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_X_pow_smul_mem_c63731a7437b

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
theorem _root_.solution (hM : IsMultigrading ι M piece) (d : (Σ k, ι k) →₀ ℕ) :
    ∀ (m : K → ℤ) (x : M), x ∈ piece m →
      (monomial d (1 : F) : MRing ι F) • x ∈ piece (m + degZ (Finsupp.weight (blockWeight ι) d)) := by
  induction d using Finsupp.induction with
  | zero => intro m x hx; simpa [degZ_zero] using hx
  | single_add v n d _ _ ih =>
    intro m x hx
    have e : (monomial (Finsupp.single v n + d) (1 : F) : MRing ι F) =
        (X v : MRing ι F) ^ n * monomial d (1 : F) := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [e, mul_smul]
    have h := X_pow_smul_mem hM v n _ _ (ih m x hx)
    convert h using 2
    rw [map_add, Finsupp.weight_single, degZ_add, add_assoc, add_comm (degZ _)]
end GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
