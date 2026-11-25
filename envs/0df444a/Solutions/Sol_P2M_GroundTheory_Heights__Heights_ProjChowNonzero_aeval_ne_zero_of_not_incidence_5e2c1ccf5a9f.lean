-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjChowNonzero_aeval_ne_zero_of_not_incidence_5e2c1ccf5a9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:52.718452+00:00
-- url     : https://prove2.me/submissions/fdb92763-e286-44bc-9820-1d17be7c00d8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_proof_d2bcebd65e98


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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjChowNonzero
namespace GroundTheory.Heights₂.Heights.ProjChowNonzero
theorem _root_.solution {n k : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin k × Fin n) ℂ} (hW : IsHomogIdeal W) (hf : IsChowForm W k f)
    (v : Fin k × Fin n → AlgebraicClosure ℂ)
    (hv : ∀ y : Fin n → AlgebraicClosure ℂ, (∀ q ∈ W, aeval y q = 0) →
      (∀ i, ∑ j, v (i, j) * y j = 0) → y = 0) :
    aeval v f ≠ 0 := by
  intro h0
  have hinc : ∀ g ∈ incIdeal W k, aeval v g = 0 := by
    intro g hg
    have hmem : ∀ u ∈ incidence W k, aeval u g = 0 := by
      simpa only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] using hg
    obtain ⟨h, rfl⟩ := (hf.2 g).mp hmem
    rw [map_mul, h0, zero_mul]
  obtain ⟨y, hy0, hyW, hyv⟩ := IncidenceZeroLocus.proof ℂ n k W hW (AlgebraicClosure ℂ) v hinc
  exact hy0 (hv y hyW hyv)
end GroundTheory.Heights₂.Heights.ProjChowNonzero
