-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.keyEvent_addresses_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:05:33.677695+00:00
-- url     : https://prove2.me/submissions/762bd91f-c781-444e-bd5a-4ca11456702d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_addresses_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26KeyedGeometric
theorem _root_.solution (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) :
    Function.Injective (fun s : (a : e.val) × Fin 3 => triangleVertex P s.1.val s.2) :=
  key_addresses_injective P key hk (fun a : e.val => a.val) Subtype.val_injective
    (fun a b => e.property.2.1 a.val a.property b.val b.property)
end QEC.Coding.BDL26KeyedGeometric
