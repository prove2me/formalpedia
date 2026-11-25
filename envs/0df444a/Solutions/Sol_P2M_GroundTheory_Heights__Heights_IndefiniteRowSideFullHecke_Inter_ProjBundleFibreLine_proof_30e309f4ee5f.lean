-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ProjBundleFibreLine_proof_30e309f4ee5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:24:06.349928+00:00
-- url     : https://prove2.me/submissions/a32e2eba-7196-4b0d-bee7-af369194b6bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_linSubst_3544d063a3f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_linForm_79f34270cd45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreIdeal_projBundleGenFibre_74df3f8a7734

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace ProjBundleFibreLine
theorem _root_.solution : ProjBundleFibreLine.Statement := by
  intro K _ ι _ N1 t P d c m B hP _ hB
  have : P.IsPrime := hP.2.1.1
  classical
  set e := fibreCoordEquiv ι N1
  set ℓ : (Σ k : FibreBlock (Sum.inl : K → K ⊕ Unit), fibreIdx (PBlk ι N1) Sum.inl k) → Fin 2 → FnField P :=
    fun q a => B a (e q) with hℓ
  obtain ⟨g, hg⟩ := (Fintype.linearCombination (FnField P) B).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hB.1.fintypeLinearCombination_injective)
  have hν : ∀ a b, ∑ q, g (Pi.single (e q) 1) a * ℓ q b = if a = b then 1 else 0 := by
    intro a b
    have h1 : ∑ q, g (Pi.single (e q) 1) a * ℓ q b = g (B b) a := by
      rw [Fintype.sum_equiv e (fun q => g (Pi.single (e q) 1) a * ℓ q b)
        (fun j => g (Pi.single j 1) a * B b j) (fun q => rfl)]
      have hB' : B b = ∑ j, B b j • Pi.single j (1 : FnField P) := by
        ext i
        simp [Finset.sum_apply, Pi.single_apply]
      conv_rhs => rw [hB']
      rw [map_sum, Finset.sum_apply]
      simp [mul_comm]
    have h2 : B b = Fintype.linearCombination (FnField P) B (Pi.single b 1) := by
      exact ((Fintype.linearCombination_apply_single (FnField P) B b (1 : FnField P)).trans (one_smul _ _)).symm
    rw [h1, h2, ← LinearMap.comp_apply, hg, LinearMap.id_apply, Pi.single_apply]
  refine ⟨projBundleGenFibre P B, linKerForms ℓ, ?_, ?_⟩
  · rintro f ⟨μ, -, rfl⟩
    exact isMultiHomog_linForm μ
  · rw [fibreIdeal_projBundleGenFibre, ker_linSubst ℓ (fun a q => g (Pi.single (e q) 1) a) hν]
    exact rfl
end ProjBundleFibreLine
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
