-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_mkF_aeval_forms_d6606fc0914c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:46.983603+00:00
-- url     : https://prove2.me/submissions/56542248-7545-4d67-963f-9edec4019832

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_aeval_mul_of_isHomogeneous_c85aa64315b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_mkF_aeval_b52b2ae4cc89

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
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SmallSections
theorem _root_.solution {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) {τ : ℕ} {F : MvPolynomial (Fin (D.size + 1)) ℤ}
    (hF : F.IsHomogeneous τ) :
    P.mkF (aeval (g c) F) = P.mkF (chartMonomial c d) ^ τ * aeval D.elt F := by
  rw [mkF_aeval, show (fun j ↦ P.mkF (g c j)) = fun j ↦ P.mkF (chartMonomial c d) * D.elt j from
    funext (hg.value c hc), aeval_mul_of_isHomogeneous hF]
end GroundTheory.Heights₂.Heights.SmallSections
