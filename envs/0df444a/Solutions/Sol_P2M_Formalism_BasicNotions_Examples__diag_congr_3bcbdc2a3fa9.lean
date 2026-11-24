-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__diag_congr_3bcbdc2a3fa9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:30:31.908598+00:00
-- url     : https://prove2.me/submissions/1c6513c5-3e3f-4380-9280-155668521ab2

import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement
import Definitions.Def_Formalism_FockGram_SymGramPosSemidef
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open NumberField
open scoped TensorProduct
open IsDedekindDomain
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution {n A : Type} [Fintype n] [DecidableEq n] [CommRing A] (σ : A →+* A)
    (d s t : n → A) (h : ∀ i, σ (d i) * s i * d i = t i) :
    Formalism.UG.cT σ (Matrix.diagonal d) * Matrix.diagonal s * Matrix.diagonal d = Matrix.diagonal t := by
  rw [cT_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact h i
end Formalism.BasicNotions.Examples₂
