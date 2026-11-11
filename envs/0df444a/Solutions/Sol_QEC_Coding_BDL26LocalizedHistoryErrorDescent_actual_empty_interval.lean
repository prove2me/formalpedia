-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.actual_empty_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:21:53.824213+00:00
-- url     : https://prove2.me/submissions/e4f50689-5dc7-48d1-ab9b-59bd3ee4246c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_intervalPotential_self
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap1_self


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))
variable (e : (Data S n).family.Cochain1 (TopIndex n))
variable (x : (state S (n+2)).presentation.X) (he : hammingSupport e ⊆ star S n (TopIndex n) x)
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent
theorem _root_.solution (a : LevelIndex n) :
    actualPotential S n sigma e x he a a=0 ∧
      intervalMap1 (Data S n) a a (Nat.le_refl _)=LinearMap.id :=
  ⟨intervalPotential_self S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a,
    intervalMap1_self (Data S n) a⟩
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
