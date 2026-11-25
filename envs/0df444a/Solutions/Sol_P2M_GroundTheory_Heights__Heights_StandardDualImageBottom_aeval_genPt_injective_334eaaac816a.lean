-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualImageBottom_aeval_genPt_injective_334eaaac816a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:18:50.701418+00:00
-- url     : https://prove2.me/submissions/636bc638-a9e1-4a7b-ab52-4a552443cd6f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemDualLatticeStandard
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_algebraicIndependent_gen_854857cd4c30


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualImageBottom
open DualArithmeticVariety
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]
namespace GroundTheory.Heights₂.Heights.StandardDualImageBottom
theorem _root_.solution : Function.Injective (aeval (R := ℤ) (genPt K i)) := by
  have hK : AlgebraicIndependent ℤ fun j : Fin i =>
      algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j) :=
    (algebraicIndependent_gen i).restrictScalars (algebraMap ℤ K).injective_int
  have h := hK.comp (fun q : Σ _ : Unit, Fin i => q.2) (by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, c⟩ h
    cases h
    rfl)
  exact algebraicIndependent_iff_injective_aeval.mp h
end GroundTheory.Heights₂.Heights.StandardDualImageBottom
