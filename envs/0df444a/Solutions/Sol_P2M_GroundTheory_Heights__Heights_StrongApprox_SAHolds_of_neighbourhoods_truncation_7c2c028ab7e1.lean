-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_SAHolds_of_neighbourhoods_truncation_7c2c028ab7e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:20:35.286127+00:00
-- url     : https://prove2.me/submissions/a4c22405-2997-4101-92c3-72e616b7c85d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PSAHolds
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
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
namespace SAHolds
theorem _root_.solution (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement := by
  classical
  intro F E _ _ _ _ _ c hrk hc N J hJ hdet hiso _ _ x hx
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  obtain ⟨hN1, hN2⟩ := hNb F E c hrk hc
  change x ∈ Cl c J
  rw [Cl, ← closure_closure, mem_closure_iff_nhds]
  intro U hU
  have hU' : (fun M => x + M) ⁻¹' U ∈ 𝓝 (0 : Matrix (Fin N) (Fin N) (AE F E)) := by
    have hcont : Continuous (fun M : Matrix (Fin N) (Fin N) (AE F E) => x + M) :=
      continuous_const.add continuous_id
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hU
  obtain ⟨S₀, hS₀⟩ := hN1 N _ hU'
  choose T hT using fun p : Fin N × Fin N => hN2 (x p.1 p.2)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ Finset.univ.biUnion T with hSdef
  obtain ⟨t1, t2, -, t4⟩ := hTr F E c hrk hc N J hJ hdet hiso S x
  refine ⟨trunc E S x, ?_, t4 hx⟩
  have hmem : x + (trunc E S x - x) ∈ U := by
    apply hS₀
    intro i j
    have hS : ∀ v ∈ S, compAt E v ((trunc E S x - x) i j) = 0 := by
      intro v hv
      have h := congrFun (congrFun (t1 v hv) i) j
      simp only [Matrix.map_apply] at h
      rw [Matrix.sub_apply, map_sub, h, sub_self]
    refine ⟨fun v hv => hS v (Finset.mem_union_left _ hv), fun v hv => ?_⟩
    by_cases hvS : v ∈ S
    · rw [hS v hvS]; exact zero_mem _
    · have h := congrFun (congrFun (t2 v hvS) i) j
      simp only [Matrix.map_apply] at h
      have hvT : v ∉ T (i, j) := fun h' =>
        hvS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, h'⟩))
      have hx' : compAt E v (x i j) ∈ intAt E v := hT (i, j) v hvT
      rw [Matrix.sub_apply, map_sub, h]
      refine sub_mem ?_ hx'
      rw [Matrix.one_apply]
      split_ifs
      · exact AddSubgroup.subset_closure
          ⟨1, one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩
      · exact zero_mem _
  simpa using hmem
end SAHolds
end GroundTheory.Heights₂.Heights.StrongApprox
