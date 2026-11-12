-- Prove2me | solution 1 for QEC.Coding.BDL26NativeHamiltonianLocality.checkBall_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:41:40.193033+00:00
-- url     : https://prove2.me/submissions/ca56b886-15e6-4d13-8168-8880158606c9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeHamiltonianLocality

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeHamiltonianLocality
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open PauliSymplectic Semantics
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace QEC.Coding.BDL26NativeHamiltonianLocality
theorem _root_.solution (S : OddScale) (n : ℕ)
    (J : Vertex (state S n).presentation → E) {t : ℝ}
    (hJ : PhysicalGeometry S n J t) (j : Sum (ZLabel S n) (XLabel S n)) :
    (((ballSubsystem S n J (checkCenter S n J j) 1).selected.card : ℕ) : ℝ) ≤ 2*t :=
  hJ.1 (checkCenter S n J j)
end QEC.Coding.BDL26NativeHamiltonianLocality
