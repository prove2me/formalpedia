-- Prove2me | solution 1 for P2M_GlobalTheory_cohOn___naturality_642b907f030d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:32:35.310975+00:00
-- url     : https://prove2.me/submissions/832d6ad0-c858-48a3-9d4c-bcdb9cf80bb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_SheafLES___naturality_d0a1c18f99f7


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.cohOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
variable (U : X.Opens) (n : ℕ)
namespace GlobalTheory.cohOn
theorem _root_.solution {S' : ShortComplex X.Modules} (hS' : S'.ShortExact) (φ : S ⟶ S')
    (x : cohOn S.X₃ U n) :
    map R φ.τ₁ U (n + 1) (δ R hS U n x) = δ R hS' U n (map R φ.τ₃ U n x) :=
  SheafLES.δ_naturality.{u} (shortExact_toAbSheaf hS) (shortExact_toAbSheaf hS')
    ((toAbSheaf X).mapShortComplex.map φ) n U x
end GlobalTheory.cohOn
