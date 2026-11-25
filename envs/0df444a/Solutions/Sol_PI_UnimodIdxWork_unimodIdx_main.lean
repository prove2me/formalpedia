-- Prove2me | solution 1 for PI.UnimodIdxWork.unimodIdx_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:39:27.598365+00:00
-- url     : https://prove2.me/submissions/0fe81689-9b16-4cfa-afce-555a4b417e46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnimodIdx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
import Theorems.Thm_PI_UnimodIdxWork_subgroup_eq_iUnion
import Theorems.Thm_PI_UnimodIdxWork_pairwise_disjoint_cosets
import Theorems.Thm_PI_UnimodIdxWork_mem_conj_map
import Theorems.Thm_PI_UnimodIdxWork_measure_subgroup_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Measure Topology Pointwise Set Function
noncomputable section
namespace PI.UnimodIdxWork
section Cosets
variable {G : Type} [Group G]
end Cosets
section Measure
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]
end Measure
private theorem measure_eq_of_eq_on_partition {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ ν : Measure α) (T : ι → Set α) (hT : ⋃ i, T i = Set.univ) (hd : Pairwise (Disjoint on T))
    (hm : ∀ i, MeasurableSet (T i)) (h : ∀ i s, MeasurableSet s → s ⊆ T i → ν s = μ s) :
    ν = μ := by
  ext s hs
  have hs' : s = ⋃ i, s ∩ T i := by rw [← Set.inter_iUnion, hT, Set.inter_univ]
  have hd' : Pairwise (Disjoint on fun i => s ∩ T i) := fun i j hij =>
    (hd hij).mono Set.inter_subset_right Set.inter_subset_right
  have hm' : ∀ i, MeasurableSet (s ∩ T i) := fun i => hs.inter (hm i)
  rw [hs', measure_iUnion hd' hm', measure_iUnion hd' hm']
  exact tsum_congr fun i => h i _ (hm' i) Set.inter_subset_right
private theorem relIndex_map_conj_eq_relIndex_map_conj_inv {G : Type} [Group G] (K : Subgroup G) (g : G) :
    K.relIndex (K.map (MulAut.conj g).toMonoidHom)
      = (K.map (MulAut.conj g⁻¹).toMonoidHom).relIndex K := by
  have hK : (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
    ext y
    simp [mul_assoc]
  calc K.relIndex (K.map (MulAut.conj g).toMonoidHom)
      = ((K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom).relIndex
          (K.map (MulAut.conj g).toMonoidHom) := by rw [hK]
    _ = (K.map (MulAut.conj g⁻¹).toMonoidHom).relIndex K :=
        Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
end PI.UnimodIdxWork
end
end

set_option autoImplicit false
open MeasureTheory Measure Topology Pointwise Set Function
noncomputable section
open PI PI.UnimodIdxWork
namespace PI.UnimodIdxWork
theorem _root_.solution : PI.UnimodIdx := by
  unfold PI.UnimodIdx
  intro G _ _ _ _ _ μ _ hμ U hU hUb K hKo hKc hidx
  have : LocallyCompactSpace G :=
    hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds K.one_mem)
  refine ⟨fun g => ?_⟩
  have hKcl : IsClosed (K : Set G) := Subgroup.isClosed_of_isOpen K hKo
  have hKpos : 0 < μ K := hKo.measure_pos μ ⟨1, K.one_mem⟩
  have hKfin : μ K < ⊤ := hKc.measure_lt_top
  have hinv : IsMulLeftInvariant (map (· * g) μ) := by
    constructor
    intro h
    calc map (h * ·) (map (· * g) μ) = map ((h * ·) ∘ (· * g)) μ :=
          map_map (measurable_const_mul h) (measurable_mul_const g)
      _ = map ((· * g) ∘ (h * ·)) μ := by
          congr 1; funext x; simp [mul_assoc]
      _ = map (· * g) (map (h * ·) μ) :=
          (map_map (measurable_mul_const g) (measurable_const_mul h)).symm
      _ = map (· * g) μ := by rw [map_mul_left_eq_self]
  have he : MeasurableEmbedding (fun x : G => x * g) := (MeasurableEquiv.mulRight g).measurableEmbedding
  have hfin : IsFiniteMeasureOnCompacts (map (· * g) μ) := by
    constructor
    intro C hC
    rw [he.map_apply]
    have : IsCompact ((fun x : G => x * g) ⁻¹' C) := (Homeomorph.mulRight g).isCompact_preimage.mpr hC
    exact this.measure_lt_top
  have hK'set : ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
      = (fun y => g⁻¹ * y * g) ⁻¹' (K : Set G) := by
    ext y
    simp only [SetLike.mem_coe, Set.mem_preimage, mem_conj_map]
  have hK'o : IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [hK'set]; exact hKo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hcont : Continuous (MulAut.conj g).toMonoidHom := by
    have : ⇑(MulAut.conj g).toMonoidHom = fun x => g * x * g⁻¹ := by
      funext x; simp [MulAut.conj_apply]
    rw [this]; exact (continuous_const.mul continuous_id).mul continuous_const
  have hK'c : IsCompact ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]; exact hKc.image hcont
  have hconj : μ ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) = μ K := by
    have h1 := measure_subgroup_eq μ K (K.map (MulAut.conj g).toMonoidHom) hKo hK'c hK'o
    have h2 := measure_subgroup_eq μ (K.map (MulAut.conj g).toMonoidHom) K hK'o hKc hKo
    rw [h1, h2, inf_comm, relIndex_map_conj_eq_relIndex_map_conj_inv, hidx g]
  have hνK : map (· * g) μ K = μ K := by
    rw [he.map_apply]
    have hset : (fun x : G => x * g) ⁻¹' (K : Set G)
        = g⁻¹ • ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
      ext x
      simp only [Set.mem_preimage, SetLike.mem_coe, Set.mem_smul_set_iff_inv_smul_mem, inv_inv,
        smul_eq_mul, mem_conj_map]
      simp
    rw [hset, measure_smul]
    exact hconj
  have hc : haarScalarFactor (map (· * g) μ) μ = 1 := by
    have h := measure_isMulInvariant_eq_smul_of_isCompact_closure (map (· * g) μ) μ
      (s := (K : Set G)) (by rw [hKcl.closure_eq]; exact hKc)
    rw [hνK] at h
    have h' : ((haarScalarFactor (map (· * g) μ) μ : NNReal) : ENNReal) * μ K = 1 * μ K := by
      rw [one_mul]
      exact h.symm
    have key : ((haarScalarFactor (map (· * g) μ) μ : NNReal) : ENNReal) = 1 := by
      exact (ENNReal.mul_left_inj hKpos.ne' hKfin.ne).mp h'
    exact_mod_cast key
  have hKTo : IsOpen ((K ⊓ ⊤ : Subgroup G) : Set G) := by rw [inf_top_eq]; exact hKo
  have hKTc : IsCompact ((K ⊓ ⊤ : Subgroup G) : Set G) := by rw [inf_top_eq]; exact hKc
  have hKTcl : IsClosed ((K ⊓ ⊤ : Subgroup G) : Set G) := by rw [inf_top_eq]; exact hKcl
  have hcov : (⋃ q : (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤,
      ((q.out : (⊤ : Subgroup G)) : G) • ((K ⊓ ⊤ : Subgroup G) : Set G)) = Set.univ := by
    rw [← subgroup_eq_iUnion K ⊤, Subgroup.coe_top]
  have hTpos : ∀ q : (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤,
      0 < μ (((q.out : (⊤ : Subgroup G)) : G) • ((K ⊓ ⊤ : Subgroup G) : Set G)) := by
    intro q
    rw [measure_smul]
    exact hKTo.measure_pos μ ⟨1, (K ⊓ ⊤).one_mem⟩
  have hcount : Countable ((⊤ : Subgroup G) ⧸ K.subgroupOf ⊤) := by
    have := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
      (fun q : (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤ => (hKTo.smul ((q.out : (⊤ : Subgroup G)) : G)).measurableSet)
      (pairwise_disjoint_cosets K ⊤)
    exact Set.countable_univ_iff.mp (Set.Countable.mono (fun q _ => hTpos q) this)
  refine measure_eq_of_eq_on_partition μ (map (· * g) μ)
    (fun q : (⊤ : Subgroup G) ⧸ K.subgroupOf ⊤ =>
      ((q.out : (⊤ : Subgroup G)) : G) • ((K ⊓ ⊤ : Subgroup G) : Set G))
    hcov (pairwise_disjoint_cosets K ⊤) (fun q => (hKTo.smul _).measurableSet) ?_
  intro q s hs hsub
  have hcl : IsCompact (closure s) :=
    (hKTc.smul ((q.out : (⊤ : Subgroup G)) : G)).of_isClosed_subset isClosed_closure
      (closure_minimal hsub (hKTcl.smul ((q.out : (⊤ : Subgroup G)) : G)))
  rw [measure_isMulInvariant_eq_smul_of_isCompact_closure (map (· * g) μ) μ hcl, hc, one_smul]
end PI.UnimodIdxWork
