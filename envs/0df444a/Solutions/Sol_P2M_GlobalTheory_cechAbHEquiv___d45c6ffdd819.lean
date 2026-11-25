-- Prove2me | solution 1 for P2M_GlobalTheory_cechAbHEquiv___d45c6ffdd819
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:24:54.690018+00:00
-- url     : https://prove2.me/submissions/fd2d9022-bc00-466b-9672-e82897b55ccd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic
import Theorems.Thm_P2M_GlobalTheory_Cube_SemiHom_homology___79af601acfd5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}} {ι : Type}
variable {V : X.Opens} {U : ι → X.Opens} {F G : X.Modules}
variable [LinearOrder ι] (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable {S S' : ShortComplex X.Modules} (hS : S.ShortExact) (h₁ : CechAcyclicMod V U S.X₁)
namespace GlobalTheory
theorem _root_.solution (n : ℕ) (x : cechAbH S.X₃.presheaf V U n) :
    cechAbHEquiv R S.X₁ V U (n + 1) (cechAbδ (T := X.toPresheafedSpace.carrier)
        (shortExact_toAbSheaf hS) (cechAcyclicMod_iff.1 h₁) n x) =
      cechδ R hS h₁ n (cechAbHEquiv R S.X₃ V U n x) :=
  Cube.SemiHom.homology_δ
    (S := (S.map (toAbSheaf X)).map (sheafToPresheaf _ _ ⋙ cechAbCubeFunctor V U))
    (S' := S.map (cechCubeFunctor R V U))
    (cechAbSheafFunctor_shortExact (T := X.toPresheafedSpace.carrier)
      (shortExact_toAbSheaf hS) (cechAcyclicMod_iff.1 h₁))
    (cechModulesFunctor_shortExact_of_acyclic R hS h₁)
    (cechAbCubeToCube R S.X₁ V U) (cechAbCubeToCube R S.X₂ V U) (cechAbCubeToCube R S.X₃ V U)
    (fun _ _ => rfl) (fun _ _ => rfl) n x
end GlobalTheory
