-- Prove2me | solution 1 for P2M_GlobalTheory_HermFrame_curv_blockDiagonal__429244f97e4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:50:57.760593+00:00
-- url     : https://prove2.me/submissions/6702afe4-523d-41ee-bff1-25922c77a87c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal
import Theorems.Thm_P2M_GlobalTheory_HermFrame_mdbar_blockDiagonal__573a2ef87000
import Theorems.Thm_P2M_GlobalTheory_HermFrame_conn_blockDiagonal__e0b95dccad40
import Theorems.Thm_GlobalTheory_HermFrame_OneFormBound_mono
import Theorems.Thm_GlobalTheory_HermFrame_TwoFormBound_mono
import Theorems.Thm_GlobalTheory_IsPshC2On_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {o : Type*} [DecidableEq o] {m m' : o → Type*}
variable [Fintype o] [∀ i, Fintype (m i)] [∀ i, Fintype (m' i)]
variable [∀ i, DecidableEq (m i)] {H : ∀ i, E → Matrix (m i) (m i) ℂ} {z : E}
namespace GlobalTheory.HermFrame
theorem _root_.solution {k : WithTop ℕ∞} (d : ∀ i, MContDiffAt k (H i) z)
    (h : ∀ i, IsUnit (H i z).det) (ξ η : E) :
    curv (fun x => blockDiagonal' fun i => H i x) z ξ η =
      blockDiagonal' fun i => curv (H i) z ξ η := by
  have he : (fun x => conn (fun x => blockDiagonal' fun i => H i x) x ξ) =ᶠ[𝓝 z]
      fun x => blockDiagonal' fun i => conn (H i) x ξ :=
    (eventually_all.2 fun i => (d i).eventually_isUnit (h i)).mono
      fun x hx => conn_blockDiagonal' hx ξ
  rw [curv, mdbar_congr he, mdbar_blockDiagonal' fun i x => conn (H i) x ξ, ← blockDiagonal'_neg]
  rfl
end GlobalTheory.HermFrame
