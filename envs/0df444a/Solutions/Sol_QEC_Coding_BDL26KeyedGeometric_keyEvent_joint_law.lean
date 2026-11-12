-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.keyEvent_joint_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:38:21.216632+00:00
-- url     : https://prove2.me/submissions/f7bd353e-5e34-4e69-ae2e-1a31071b86de

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_triangle_family_law

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
    (e : KeyEvent P key hk J radius) (ν : Vertex P → Measure Space)
    [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.pi ν).map (fun w (a : e.val) i => w (triangleVertex P a.val i)) =
      Measure.pi (fun a : e.val => Measure.pi (fun i => ν (triangleVertex P a.val i))) :=
  key_triangle_family_law P key hk (fun a : e.val => a.val) Subtype.val_injective
    (fun a b => e.property.2.1 a.val a.property b.val b.property) ν
end QEC.Coding.BDL26KeyedGeometric
