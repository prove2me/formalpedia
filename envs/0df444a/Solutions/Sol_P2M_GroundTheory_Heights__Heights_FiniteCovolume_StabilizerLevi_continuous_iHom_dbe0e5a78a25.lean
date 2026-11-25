-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_continuous_iHom_dbe0e5a78a25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:56:54.963169+00:00
-- url     : https://prove2.me/submissions/1d4d635c-72c3-44a3-8dae-08c249107630

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_continuous_mat_a5253d6a3533

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W} {n : ℕ}
  (hp : IsHyperbolicPair h x₀ w₀) {h' : HermitianForm F E (hypComplement h x₀ w₀)}
  (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y) {v' : Basis (Fin n) E (hypComplement h x₀ w₀)}
include hp hh'
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
theorem _root_.solution : Continuous (iHom hp hh' (v := v) (v' := v')) := by
  refine continuous_induced_rng.2 (continuous_induced_rng.2
    (continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩))
  · change Continuous fun m : archUnitary h' v' =>
      1 - bMat v v' w * leftInv (gramAt h v w) (bMat v v' w) +
        bMat v v' w * mat m w * leftInv (gramAt h v w) (bMat v v' w)
    exact continuous_const.add ((continuous_const.matrix_mul (continuous_mat w)).matrix_mul
      continuous_const)
  · change Continuous fun m : archUnitary h' v' =>
      1 - bMat v v' w * leftInv (gramAt h v w) (bMat v v' w) +
        bMat v v' w * mat m⁻¹ w * leftInv (gramAt h v w) (bMat v v' w)
    exact continuous_const.add ((continuous_const.matrix_mul
      ((continuous_mat w).comp continuous_inv)).matrix_mul continuous_const)
end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
