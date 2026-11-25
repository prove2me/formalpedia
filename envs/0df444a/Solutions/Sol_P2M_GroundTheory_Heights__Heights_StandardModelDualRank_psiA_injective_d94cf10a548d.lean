-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_psiA_injective_d94cf10a548d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:33.467792+00:00
-- url     : https://prove2.me/submissions/dcbb6d7f-37fd-4427-9aba-ab6f86446083

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
open GroundTheory.Heights₂.Heights.StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.StandardModelDualRank
theorem _root_.solution : Function.Injective (psiA K i) := by
  let ev : MvPolynomial Unit (MvPolynomial Unit (ProjField K i)) →+* ProjField K i :=
    eval₂Hom (MvPolynomial.eval fun _ => (1 : ProjField K i)) fun _ => 1
  have h : ev.comp (psiA K i) = algebraMap (MvPolynomial (Fin i) K) (ProjField K i) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp only [ev, psiA, RingHom.comp_apply, eval₂Hom_C, eval_C]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    · intro j
      simp [ev, psiA]
  intro p q hpq
  apply IsFractionRing.injective (MvPolynomial (Fin i) K) (ProjField K i)
  rw [← h, RingHom.comp_apply, RingHom.comp_apply, hpq]
end GroundTheory.Heights₂.Heights.StandardModelDualRank
