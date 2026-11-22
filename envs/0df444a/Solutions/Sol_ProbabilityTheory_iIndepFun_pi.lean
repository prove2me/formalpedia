-- Prove2me | solution 1 for ProbabilityTheory.iIndepFun.pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:25:31.779795+00:00
-- url     : https://prove2.me/submissions/22f822d7-4ad9-4d52-bf6e-e5727f7605cb

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Theorems.Thm_ProbabilityTheory_iIndepFun_inv
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_Finset_prod_univ_prod
public import Theorems.Thm_P2M_Finset_prod_univ_prod__3be403f26078
attribute [local simp] ProbabilityTheory.indepFun_zero_measure

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal
open ProbabilityTheory
variable {ι Ω : Type*} {κ : ι → Type*} {α : ∀ i,
  κ i → Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [m : ∀ i j, MeasurableSpace (α i j)] {f : ∀ i j, Ω → α i j}
variable [Fintype ι] [∀ i, Fintype (κ i)]
variable {ι : Type*} {κ : ι → Type*} [∀ i, Finite (κ i)]
  {α : ∀ i, κ i → Type*} {f : ∀ i j, Ω → α i j} [m : ∀ i j, MeasurableSpace (α i j)]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.iIndepFun
theorem _root_.solution
    (f_meas : ∀ i j, Measurable (f i j))
    (hf : iIndepFun (fun ij : Σ i, κ i ↦ f ij.1 ij.2) μ) :
    iIndepFun (fun i ω j ↦ f i j ω) μ := by
  have (i : ι) : Fintype (κ i) := .ofFinite _
  let F i ω j := f i j ω
  let M (i : ι):= MeasurableSpace.pi (m := m i)
  let πβ (i : ι) := Set.pi Set.univ '' Set.pi Set.univ fun j => { s | MeasurableSet[m i j] s }
  apply iIndepSets.iIndep
  · exact fun i ↦ measurable_iff_comap_le.mp (measurable_pi_iff.mpr (f_meas i))
  · exact fun i ↦ IsPiSystem.comap isPiSystem_pi (F i)
  · intro k
    change MeasurableSpace.comap _ (M k) = _
    have : M k = MeasurableSpace.generateFrom (πβ k) := generateFrom_pi.symm
    rewrite [this, MeasurableSpace.comap_generateFrom]; rfl
  rw [iIndepSets_iff]
  intro s E hE
  simp only [mem_image, mem_pi, mem_univ, true_implies, exists_exists_and_eq_and] at hE
  have hE' (k : s) := hE k (Finset.coe_mem k)
  classical
  obtain ⟨sets, h_sets⟩ := Classical.axiomOfChoice hE'
  let sets' (i : ι) (j : κ i) : Set (α i j) := if h : i ∈ s then sets ⟨i,
    h⟩ j else Set.univ
  have box (i : ι) (hi : i ∈ s) : E i = ⋂ j : κ i, (f i j)⁻¹' (sets' i j) := by
    rw [← (h_sets ⟨i, hi⟩).right]
    simp_rw [sets', hi]
    ext : 1
    rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    exact ⟨fun hj j ↦ mem_preimage.mpr (hj j), fun hj j ↦ mem_preimage.mp (hj j)⟩
  let set (i : ι) (j : κ i) := f i j ⁻¹' sets' i j
  set set_σ := fun (ij : (i : ι) × κ i) ↦ set ij.fst ij.snd with set_σ_def
  let meas i j := μ (set i j)
  let meas_σ ij := μ (set_σ ij)
  suffices μ (⋂ i ∈ s, ⋂ j, set i j) = ∏ i ∈ s, μ (⋂ j, set i j) by
    convert this with k hk k hk; all_goals { exact box k hk }
  let κ_σ (i : ι) := Finset.sigma {i} fun i ↦ Finset.univ (α := κ i)
  have reindex_prod (i : ι) : ∏ j, meas i j = ∏ ij : κ_σ i, meas_σ ij := by
    rw [Finset.prod_coe_sort, Finset.prod_sigma, Finset.prod_singleton]
  have reindex_inter (i : ι) : ⋂ j, set i j = ⋂ ij ∈ κ_σ i, set_σ ij := by
    rw [set_σ_def, Set.biInter_finsetSigma, Finset.set_biInter_singleton]
    simp
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf
  rw [Set.biInter_finsetSigma_univ', hf, Finset.prod_sigma]
  · apply Finset.prod_congr rfl
    intro i hi
    symm
    rw [reindex_prod, reindex_inter, Finset.prod_coe_sort]
    apply hf (κ_σ i) (sets := fun ij ↦ sets' ij.fst ij.snd)
    intro ij hij
    rw [← Finset.mem_singleton.mp (Finset.mem_sigma.mp hij).left] at hi
    convert (h_sets ⟨ij.fst, hi⟩).left ij.snd
    simp [sets', hi]
  intros ij hij
  obtain ⟨hi, _⟩ := Finset.mem_sigma.mp hij
  simp_rw [sets', hi]
  exact (h_sets ⟨ij.fst, hi⟩).1 ij.snd
end _root_.ProbabilityTheory.iIndepFun
end ProbabilityTheory
