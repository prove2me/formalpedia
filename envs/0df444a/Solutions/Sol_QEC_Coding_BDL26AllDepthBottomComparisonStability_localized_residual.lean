-- Prove2me | solution 1 for QEC.Coding.BDL26AllDepthBottomComparisonStability.localized_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:13:01.706466+00:00
-- url     : https://prove2.me/submissions/583eac05-db4c-421e-a663-b5b4d98c1289

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_actual_history
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self

section
noncomputable section
namespace QEC.Coding.BDL26AllDepthBottomComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
private theorem swap_two_bases {I J K : Type}
    (L : Word F I →ₗ[F] Word F J) (d : Word F K →ₗ[F] Word F J)
    (e A B : Word F J) (h b c u v : Word F I) (P : Word F K)
    (equation : e+A+B=L (h+b+c)+d P) :
    e+(A+L (b+u))+(B+L (c+v))=L (h+u+v)+d P := by
  have cancel : L (h+b+c)+L (b+u)+L (c+v)=L (h+u+v) := by
    rw [← map_add,← map_add]
    apply congrArg L
    calc
      _ = (h+u+v)+(b+b)+(c+c) := by abel
      _ = _ := by rw [word_add_self,word_add_self,add_zero,add_zero]
  calc
    _ = (e+A+B)+L (b+u)+L (c+v) := by abel
    _ = (L (h+b+c)+d P)+L (b+u)+L (c+v) := by rw [equation]
    _ = (L (h+b+c)+L (b+u)+L (c+v))+d P := by abel
    _ = _ := by rw [cancel]
end QEC.Coding.BDL26AllDepthBottomComparisonStability
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26AllDepthBottomComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26AllDepthBottomComparisonStability
theorem _root_.solution (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    residual S n sigma e =
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        ((BDL26LocalizedHistoryErrorDescent.actualDescent S n sigma e x support 0).word+
          baseComparison S n sigma+baseComparison S n (perturbTop S n sigma e))+
      (Data S n).family.coboundary0 (TopIndex n)
        (BDL26LocalizedHistoryErrorDescent.actualPotential S n sigma e x support 0 (TopIndex n)) := by
  exact swap_two_bases
    (intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _))
    ((Data S n).family.coboundary0 (TopIndex n)) _ _ _ _ _ _ _ _ _
    (BDL26LocalizedHistoryErrorDescent.actual_history S n sigma e x support)
end QEC.Coding.BDL26AllDepthBottomComparisonStability
