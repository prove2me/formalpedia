-- Prove2me | solution 2 for QEC.Coding.BDL26RandomPerturbation.countedScan_map_pair
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-10T23:26:56.900799+00:00
-- url     : https://prove2.me/submissions/e4aa6724-31a5-453b-aaec-1f221874cdc0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListMeasurable
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListSingleton
theorem solution {A B W : Type*} (encode : A → B)
    (q : A → W → Bool × ℕ) (q' : B → W → Bool × ℕ)
    (hq : ∀ a w, q' (encode a) w = q a w) (L : List A) (w : W) :
    scanQuery q' (L.map encode) w = ((scanQuery q L w).1.map encode, (scanQuery q L w).2) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, scanQuery, hq]
    split <;> simp_all
