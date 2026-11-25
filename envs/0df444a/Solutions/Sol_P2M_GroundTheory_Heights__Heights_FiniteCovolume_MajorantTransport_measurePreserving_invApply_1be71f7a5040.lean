-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_measurePreserving_invApply_1be71f7a5040
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:24.866474+00:00
-- url     : https://prove2.me/submissions/926321b0-70f4-46df-9230-fc18adc4fce9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StMajorantTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMajorantTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_measurePreserving_mulVec_8a450dd7dca1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_normSq_det_dae0eb0a6bfc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped MatrixOrder ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.FiniteCovolume.MajorantTransport
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.MajorantTransport
theorem _root_.solution {h : HermitianForm F E W} {v : Basis ι E W}
    (g : archUnitary h v) : MeasurePreserving (invApply g) volume volume :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume)
    (fun w => measurePreserving_mulVec (normSq_det h v g⁻¹ w))
end GroundTheory.Heights₂.Heights.FiniteCovolume.MajorantTransport
