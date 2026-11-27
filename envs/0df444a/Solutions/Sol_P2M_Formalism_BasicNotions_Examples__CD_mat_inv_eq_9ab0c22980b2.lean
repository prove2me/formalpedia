-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_mat_inv_eq_9ab0c22980b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:30.613372+00:00
-- url     : https://prove2.me/submissions/d6f1554f-13c8-4561-b793-2f3d017ac575

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormLeSum
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_mat_left_inv_4e578481c43f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Metric NormedSpace Set Matrix Formalism.UG.P
open scoped ENNReal NNReal Matrix.Norms.Operator
variable (P Q : ℕ)
local notation "J" => Formalism.UG.Jpq P Q
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution (g : Formalism.UG.Upq P Q) :
    (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q) =
      J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J := by
  have h1 := mat_left_inv P Q g
  have h2 : UpqT.mat (P := P) (Q := Q) g *
      (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q) = 1 :=
    Units.mul_inv (g : GL (Fin P ⊕ Fin Q) ℂ)
  calc (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q)
      = (J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J * UpqT.mat (P := P) (Q := Q) g) *
          (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q) := by
        rw [h1, Matrix.one_mul]
    _ = J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J := by
        rw [Matrix.mul_assoc (J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J), h2, Matrix.mul_one]
end Formalism.BasicNotions.Examples₂.CD
