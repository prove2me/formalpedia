-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_Truncation_proof_5b8f6403e517
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:47:50.337193+00:00
-- url     : https://prove2.me/submissions/a6da1186-42d0-45a1-a28c-24a51eda0491

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PTruncation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_mul_of_ne_4e9cbe6c464d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_compAt_restrictTo_3d6cb5d193c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_map_compAt_mem_SU_3b573f666034
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_list_prod_one_add_67ee7372c84e
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_mul_mem_SU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_one_mem_SU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
namespace GroundTheory.Heights₂.Heights.StrongApprox
namespace Truncation
theorem _root_.solution (hLoc : LocalInClosure.Statement) : Truncation.Statement := by
  classical
  intro F E _ _ _ _ _ c hE hc N J hJ hdet hiso _ _ S x
  have part3 : ∀ l : List (HeightOneSpectrum (𝓞 F)), l.Nodup → (∀ v, v ∈ l ↔ v ∈ S) →
      trunc E S x = (l.map fun v => embed E v (x.map (compAt E v))).prod := by
    intro l hl hlS
    have hB : ∀ v w : HeightOneSpectrum (𝓞 F), v ≠ w →
        (x.map (compAt E v) - 1).map (singleV E v) * (x.map (compAt E w) - 1).map (singleV E w) = 0 := by
      intro v w h
      ext i j
      rw [Matrix.mul_apply]
      exact Finset.sum_eq_zero fun k _ => singleV_mul_of_ne h _ _
    rw [show (fun v => embed E v (x.map (compAt E v))) =
      fun v => 1 + (x.map (compAt E v) - 1).map (singleV E v) from rfl, list_prod_one_add _ hB l hl]
    have hS : l.toFinset = S := by ext v; rw [List.mem_toFinset, hlS]
    rw [← List.sum_toFinset _ hl, hS, trunc]
    congr 1
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.map_apply, restrictTo, Matrix.sub_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_sub, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨?_, ?_, part3, ?_⟩
  · intro v hv
    ext i j
    simp only [trunc, Matrix.map_apply, Matrix.add_apply, map_add, compAt_restrictTo, if_pos hv,
      Matrix.sub_apply, map_sub]
    abel
  · intro v hv
    ext i j
    simp only [trunc, Matrix.map_apply, Matrix.add_apply, map_add, compAt_restrictTo, if_neg hv,
      add_zero]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro hx
    have : Module.Finite F E := Module.finite_of_finrank_eq_succ hE
    have : IsTopologicalRing (AE F E) :=
      IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) (AE F E)
    rw [part3 S.toList (Finset.nodup_toList S) (fun v => Finset.mem_toList)]
    have hmem : ∀ l : List (HeightOneSpectrum (𝓞 F)),
        (l.map fun v => embed E v (x.map (compAt E v))).prod ∈ Cl c J := by
      intro l
      induction l with
      | nil =>
        exact subset_closure ⟨1, one_mem_SU, Matrix.map_one _ (map_zero _) (map_one _)⟩
      | cons v l ih =>
        rw [List.map_cons, List.prod_cons]
        refine map_mem_closure₂ continuous_mul
          (hLoc F E c hE hc N J hJ hdet hiso v _ (map_compAt_mem_SU c v J hx)) ih ?_
        rintro _ ⟨γ, hγ, rfl⟩ _ ⟨γ', hγ', rfl⟩
        exact ⟨γ * γ', mul_mem_SU hγ hγ', Matrix.map_mul⟩
    exact hmem _
end Truncation
end GroundTheory.Heights₂.Heights.StrongApprox
