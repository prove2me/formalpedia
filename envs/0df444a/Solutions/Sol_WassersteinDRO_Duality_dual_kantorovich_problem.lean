-- Prove2me | solution 1 for WassersteinDRO.Duality.dual_kantorovich_problem
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:35:47.615317+00:00
-- url     : https://prove2.me/submissions/c65e133c-e1bc-4164-abae-4d1dab1b03a8

import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus
import Definitions.Def_WassersteinDRO_Duality_nominalRisk_v2
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk_v2
import Mathlib
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.MetricSpace.Completion

-- Complete local proof: Solutions.Duality_KantorovichCells
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace DualityCodex

noncomputable def probabilityCell {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (s : Set E) (x0 : E) : Measure E := by
  classical
  exact if Q s = 0 then Measure.dirac x0 else ProbabilityTheory.cond Q s

lemma probabilityCell_isProbability {E : Type*} [MeasurableSpace E]
    (Q : Measure E) [IsFiniteMeasure Q] (s : Set E) (x0 : E) :
    IsProbabilityMeasure (probabilityCell Q s x0) := by
  classical
  unfold probabilityCell
  split_ifs with h
  · infer_instance
  · exact cond_isProbabilityMeasure h

lemma cell_mass_smul_probabilityCell {E : Type*} [MeasurableSpace E]
    (Q : Measure E) [IsFiniteMeasure Q] (s : Set E) (x0 : E) :
    Q s • probabilityCell Q s x0 = Q.restrict s := by
  classical
  by_cases h : Q s = 0
  · rw [h,zero_smul,Measure.restrict_eq_zero.mpr h]
  · rw [probabilityCell,if_neg h,ProbabilityTheory.cond,smul_smul,
      ENNReal.mul_inv_cancel h (measure_ne_top Q s),one_smul]

lemma probabilityCell_ae_mem {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (s : Set E) (hs : MeasurableSet s) (h : Q s ≠ 0) (x0 : E) :
    ∀ᵐ x ∂probabilityCell Q s x0, x ∈ s := by
  classical
  apply ae_iff.mpr
  change probabilityCell Q s x0 sᶜ = 0
  rw [probabilityCell,if_neg h,ProbabilityTheory.cond]
  simp [Measure.smul_apply,Measure.restrict_apply hs.compl,Set.compl_inter_self]

#print axioms probabilityCell_isProbability
#print axioms cell_mass_smul_probabilityCell
#print axioms probabilityCell_ae_mem
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichLift
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
namespace DualityCodex

noncomputable def finiteProductLift {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype I] [Fintype J] (w : I × J → ENNReal)
    (ρ : I → Measure E) (σ : J → Measure F) : Measure (E × F) :=
  ∑ ij, w ij • (ρ ij.1).prod (σ ij.2)

lemma finiteProductLift_fst {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype I] [Fintype J] (w : I × J → ENNReal)
    (ρ : I → Measure E) (σ : J → Measure F) (hσ : ∀ j, IsProbabilityMeasure (σ j)) :
    (finiteProductLift w ρ σ).map Prod.fst = ∑ i, (∑ j, w (i,j)) • ρ i := by
  letI : ∀ j, IsProbabilityMeasure (σ j) := hσ
  unfold finiteProductLift
  rw [Measure.map_finset_sum' measurable_fst.aemeasurable]
  simp_rw [Measure.map_smul,Measure.map_fst_prod,measure_univ,one_smul]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_smul]

lemma finiteProductLift_snd {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype I] [Fintype J] (w : I × J → ENNReal)
    (ρ : I → Measure E) (σ : J → Measure F) (hρ : ∀ i, IsProbabilityMeasure (ρ i))
    (hσ : ∀ j, IsProbabilityMeasure (σ j)) :
    (finiteProductLift w ρ σ).map Prod.snd = ∑ j, (∑ i, w (i,j)) • σ j := by
  letI : ∀ i, IsProbabilityMeasure (ρ i) := hρ
  letI : ∀ j, IsProbabilityMeasure (σ j) := hσ
  unfold finiteProductLift
  rw [Measure.map_finset_sum' measurable_snd.aemeasurable]
  simp_rw [Measure.map_smul,Measure.map_snd_prod,measure_univ,one_smul]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [← Finset.sum_smul]

lemma finite_partition_restrict_sum {E I : Type*} [MeasurableSpace E] [Fintype I]
    (Q : Measure E) (S : I → Set E) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hcover : (⋃ i, S i) = Set.univ) :
    (∑ i, Q.restrict (S i)) = Q := by
  have h := Measure.restrict_iUnion (μ := Q) hd hS
  rw [hcover,Measure.restrict_univ] at h
  calc
    (∑ i, Q.restrict (S i)) = Measure.sum (fun i => Q.restrict (S i)) := by
      ext s hs
      rw [Measure.finsetSum_apply,Measure.sum_apply _ hs]
      exact (tsum_fintype _).symm
    _ = Q := h.symm

lemma finite_ofReal_sum_eq_mass {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (m : ENNReal) (hm : m ≠ ⊤)
    (h : ∑ i, w i = m.toReal) : (∑ i, ENNReal.ofReal (w i)) = m := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),h,ENNReal.ofReal_toReal hm]

#print axioms finiteProductLift_fst
#print axioms finiteProductLift_snd
#print axioms finite_partition_restrict_sum
#print axioms finite_ofReal_sum_eq_mass
noncomputable def finiteCellLift {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype I] [Fintype J] (Q : Measure E) (Q' : Measure F) (S : I → Set E) (T : J → Set F)
    (w : I × J → ENNReal) (x0 : E) (y0 : F) : Measure (E × F) :=
  finiteProductLift w (fun i => probabilityCell Q (S i) x0) (fun j => probabilityCell Q' (T j) y0)

lemma finiteCellLift_marginals {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype I] [Fintype J] (Q : Measure E) (Q' : Measure F)
    [IsFiniteMeasure Q] [IsFiniteMeasure Q'] (S : I → Set E) (T : J → Set F)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hdT : Pairwise (fun i j => Disjoint (T i) (T j)))
    (hcoverS : (⋃ i, S i) = Set.univ) (hcoverT : (⋃ j, T j) = Set.univ)
    (w : I × J → ENNReal) (hrow : ∀ i, ∑ j, w (i,j) = Q (S i))
    (hcol : ∀ j, ∑ i, w (i,j) = Q' (T j)) (x0 : E) (y0 : F) :
    (finiteCellLift Q Q' S T w x0 y0).map Prod.fst = Q ∧
      (finiteCellLift Q Q' S T w x0 y0).map Prod.snd = Q' := by
  constructor
  · unfold finiteCellLift
    rw [finiteProductLift_fst w _ _ (fun j => probabilityCell_isProbability Q' (T j) y0)]
    simp_rw [hrow,cell_mass_smul_probabilityCell]
    exact finite_partition_restrict_sum Q S hS hdS hcoverS
  · unfold finiteCellLift
    rw [finiteProductLift_snd w _ _ (fun i => probabilityCell_isProbability Q (S i) x0)
      (fun j => probabilityCell_isProbability Q' (T j) y0)]
    simp_rw [hcol,cell_mass_smul_probabilityCell]
    exact finite_partition_restrict_sum Q' T hT hdT hcoverT

lemma finiteCellLift_isProbability {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype I] [Fintype J] (Q : Measure E) (Q' : Measure F)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] (S : I → Set E) (T : J → Set F)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hdT : Pairwise (fun i j => Disjoint (T i) (T j)))
    (hcoverS : (⋃ i, S i) = Set.univ) (hcoverT : (⋃ j, T j) = Set.univ)
    (w : I × J → ENNReal) (hrow : ∀ i, ∑ j, w (i,j) = Q (S i))
    (hcol : ∀ j, ∑ i, w (i,j) = Q' (T j)) (x0 : E) (y0 : F) :
    IsProbabilityMeasure (finiteCellLift Q Q' S T w x0 y0) := by
  have h := (finiteCellLift_marginals Q Q' S T hS hT hdS hdT hcoverS hcoverT
    w hrow hcol x0 y0).1
  have hm := congrArg (fun μ : Measure E => μ Set.univ) h
  constructor
  simpa [Measure.map_apply measurable_fst MeasurableSet.univ] using hm

lemma real_matrix_cell_lift_marginals {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype I] [Fintype J] (Q : Measure E) (Q' : Measure F)
    [IsFiniteMeasure Q] [IsFiniteMeasure Q'] (S : I → Set E) (T : J → Set F)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hdT : Pairwise (fun i j => Disjoint (T i) (T j)))
    (hcoverS : (⋃ i, S i) = Set.univ) (hcoverT : (⋃ j, T j) = Set.univ)
    (w : I × J → ℝ) (hw : ∀ ij, 0 ≤ w ij)
    (hrow : ∀ i, ∑ j, w (i,j) = (Q (S i)).toReal)
    (hcol : ∀ j, ∑ i, w (i,j) = (Q' (T j)).toReal) (x0 : E) (y0 : F) :
    (finiteCellLift Q Q' S T (fun ij => ENNReal.ofReal (w ij)) x0 y0).map Prod.fst = Q ∧
      (finiteCellLift Q Q' S T (fun ij => ENNReal.ofReal (w ij)) x0 y0).map Prod.snd = Q' := by
  apply finiteCellLift_marginals Q Q' S T hS hT hdS hdT hcoverS hcoverT
  · intro i
    exact finite_ofReal_sum_eq_mass (fun j => w (i,j)) (fun j => hw (i,j))
      (Q (S i)) (measure_ne_top Q (S i)) (hrow i)
  · intro j
    exact finite_ofReal_sum_eq_mass (fun i => w (i,j)) (fun i => hw (i,j))
      (Q' (T j)) (measure_ne_top Q' (T j)) (hcol j)

lemma finiteProductLift_lintegral {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype I] [Fintype J] (w : I × J → ENNReal)
    (ρ : I → Measure E) (σ : J → Measure F) (f : E × F → ENNReal) :
    (∫⁻ z, f z ∂finiteProductLift w ρ σ) = ∑ ij, w ij * (∫⁻ z, f z ∂(ρ ij.1).prod (σ ij.2)) := by
  simp only [finiteProductLift,lintegral_finsetSum_measure,lintegral_smul_measure,smul_eq_mul]

lemma finiteProductLift_lintegral_le {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype I] [Fintype J] (w : I × J → ENNReal)
    (ρ : I → Measure E) (σ : J → Measure F) (f : E × F → ENNReal) (C : I × J → ENNReal)
    (hc : ∀ ij, (∫⁻ z, f z ∂(ρ ij.1).prod (σ ij.2)) ≤ C ij) :
    (∫⁻ z, f z ∂finiteProductLift w ρ σ) ≤ ∑ ij, w ij * C ij := by
  rw [finiteProductLift_lintegral]
  apply Finset.sum_le_sum
  intro ij _
  gcongr
  exact hc ij

#print axioms finiteCellLift_marginals
#print axioms finiteCellLift_isProbability
#print axioms real_matrix_cell_lift_marginals
#print axioms finiteProductLift_lintegral
#print axioms finiteProductLift_lintegral_le
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichLiftCost
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma nonzero_entry_row_mass {I J : Type*} [Fintype J] (w : I × J → ENNReal)
    (m : I → ENNReal) (hrow : ∀ i, ∑ j, w (i,j) = m i) (i : I) (j : J) (hw : w (i,j) ≠ 0) :
    m i ≠ 0 := by
  have hle : w (i,j) ≤ ∑ k, w (i,k) := Finset.single_le_sum (f := fun k => w (i,k)) (fun _ _ => zero_le) (Finset.mem_univ j)
  rw [hrow i] at hle
  intro hm
  rw [hm] at hle
  exact hw (nonpos_iff_eq_zero.mp hle)

lemma probability_cell_product_ae_cells {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (Q : Measure E) (Q' : Measure F) [IsFiniteMeasure Q] [IsFiniteMeasure Q']
    (S : Set E) (T : Set F) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hQS : Q S ≠ 0) (hQT : Q' T ≠ 0) (x0 : E) (y0 : F) :
    ∀ᵐ z ∂(probabilityCell Q S x0).prod (probabilityCell Q' T y0), z.1 ∈ S ∧ z.2 ∈ T := by
  let ρ := probabilityCell Q S x0
  let σ := probabilityCell Q' T y0
  letI : IsProbabilityMeasure ρ := probabilityCell_isProbability Q S x0
  letI : IsProbabilityMeasure σ := probabilityCell_isProbability Q' T y0
  have hX : ∀ᵐ z ∂ρ.prod σ, z.1 ∈ S := by
    apply (ae_map_iff (f := Prod.fst) measurable_fst.aemeasurable hS).mp
    rw [Measure.map_fst_prod,measure_univ,one_smul]
    change ∀ᵐ x ∂probabilityCell Q S x0, x ∈ S
    exact probabilityCell_ae_mem Q S hS hQS x0
  have hY : ∀ᵐ z ∂ρ.prod σ, z.2 ∈ T := by
    apply (ae_map_iff (f := Prod.snd) measurable_snd.aemeasurable hT).mp
    rw [Measure.map_snd_prod,measure_univ,one_smul]
    change ∀ᵐ y ∂probabilityCell Q' T y0, y ∈ T
    exact probabilityCell_ae_mem Q' T hT hQT y0
  exact hX.and hY

lemma finiteCellLift_cost_le_of_cellwise_bound {E F I J : Type*}
    [MeasurableSpace E] [MeasurableSpace F] [Fintype I] [Fintype J]
    (Q : Measure E) (Q' : Measure F) [IsFiniteMeasure Q] [IsFiniteMeasure Q']
    (S : I → Set E) (T : J → Set F) (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (w : I × J → ENNReal) (hrow : ∀ i, ∑ j, w (i,j) = Q (S i))
    (hcol : ∀ j, ∑ i, w (i,j) = Q' (T j)) (x0 : E) (y0 : F)
    (f : E × F → ENNReal) (C : I × J → ENNReal)
    (hc : ∀ i j x y, x ∈ S i → y ∈ T j → f (x,y) ≤ C (i,j)) :
    (∫⁻ z, f z ∂finiteCellLift Q Q' S T w x0 y0) ≤ ∑ ij, w ij * C ij := by
  unfold finiteCellLift
  rw [finiteProductLift_lintegral]
  apply Finset.sum_le_sum
  intro ij _
  obtain ⟨i,j⟩ := ij
  by_cases hw : w (i,j) = 0
  · simp [hw]
  · have hQS := nonzero_entry_row_mass w (fun i => Q (S i)) hrow i j hw
    have hQT := nonzero_entry_row_mass (fun ji : J × I => w (ji.2,ji.1))
      (fun j => Q' (T j)) hcol j i hw
    letI : IsProbabilityMeasure (probabilityCell Q (S i) x0) := probabilityCell_isProbability Q (S i) x0
    letI : IsProbabilityMeasure (probabilityCell Q' (T j) y0) := probabilityCell_isProbability Q' (T j) y0
    have hcost : (∫⁻ z, f z ∂(probabilityCell Q (S i) x0).prod (probabilityCell Q' (T j) y0)) ≤ C (i,j) := by
      have hae := probability_cell_product_ae_cells Q Q' (S i) (T j) (hS i) (hT j) hQS hQT x0 y0
      have hle := lintegral_mono_ae (hae.mono fun z hz => hc i j z.1 z.2 hz.1 hz.2)
      simpa only [lintegral_const,measure_univ,mul_one] using hle
    gcongr

#print axioms nonzero_entry_row_mass
#print axioms probability_cell_product_ae_cells
#print axioms finiteCellLift_cost_le_of_cellwise_bound
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichPartitions
set_option autoImplicit false
open MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace DualityCodex

def finitePartitionHead {E : Type*} (A : ℕ → Set E) (N : ℕ) : Set E :=
  ⋃ i : Fin N, A i.val

def truncatedPartitionCells {E : Type*} (A : ℕ → Set E) (N : ℕ) (i : Fin (N+1)) : Set E :=
  if i.val < N then A i.val else (finitePartitionHead A N)ᶜ

lemma finitePartitionHead_measurable {E : Type*} [MeasurableSpace E]
    (A : ℕ → Set E) (hA : ∀ n, MeasurableSet (A n)) (N : ℕ) :
    MeasurableSet (finitePartitionHead A N) := MeasurableSet.iUnion fun i => hA i.val

lemma cell_subset_finitePartitionHead {E : Type*} (A : ℕ → Set E)
    (N n : ℕ) (hn : n < N) : A n ⊆ finitePartitionHead A N := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨⟨n,hn⟩,hx⟩

lemma truncatedPartitionCells_measurable {E : Type*} [MeasurableSpace E]
    (A : ℕ → Set E) (hA : ∀ n, MeasurableSet (A n)) (N : ℕ) :
    ∀ i, MeasurableSet (truncatedPartitionCells A N i) := by
  intro i
  unfold truncatedPartitionCells
  split_ifs
  · exact hA i.val
  · exact (finitePartitionHead_measurable A hA N).compl

lemma truncatedPartitionCells_tail {E : Type*} (A : ℕ → Set E) (N : ℕ) :
    truncatedPartitionCells A N (Fin.last N) = (finitePartitionHead A N)ᶜ := by
  simp [truncatedPartitionCells]

lemma truncatedPartitionCells_disjoint {E : Type*} (A : ℕ → Set E)
    (hd : Pairwise (fun n m => Disjoint (A n) (A m))) (N : ℕ) :
    Pairwise (fun i j => Disjoint (truncatedPartitionCells A N i) (truncatedPartitionCells A N j)) := by
  intro i j hij
  by_cases hi : i.val < N
  · by_cases hj : j.val < N
    · simp only [truncatedPartitionCells,if_pos hi,if_pos hj]
      exact hd (fun h => hij (Fin.ext h))
    · simp only [truncatedPartitionCells,if_pos hi,if_neg hj]
      apply Set.disjoint_left.mpr
      intro x hx hx'
      exact hx' (cell_subset_finitePartitionHead A N i.val hi hx)
  · by_cases hj : j.val < N
    · simp only [truncatedPartitionCells,if_neg hi,if_pos hj]
      apply Set.disjoint_left.mpr
      intro x hx hx'
      exact hx (cell_subset_finitePartitionHead A N j.val hj hx')
    · have heq : i = j := by
        apply Fin.ext
        have := i.isLt
        have := j.isLt
        omega
      exact False.elim (hij heq)

lemma truncatedPartitionCells_cover {E : Type*} (A : ℕ → Set E) (N : ℕ) :
    (⋃ i, truncatedPartitionCells A N i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ finitePartitionHead A N
  · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨⟨i.val,by have := i.isLt; omega⟩,?_⟩
    simpa [truncatedPartitionCells,i.isLt] using hi
  · refine Set.mem_iUnion.mpr ⟨Fin.last N,?_⟩
    rw [truncatedPartitionCells_tail]
    exact hx

noncomputable def partitionCellCenter {E : Type*} (A : ℕ → Set E) (x0 : E) (n : ℕ) : E := by
  classical
  exact if h : (A n).Nonempty then h.choose else x0

lemma partitionCellCenter_mem {E : Type*} (A : ℕ → Set E) (x0 : E) (n : ℕ)
    (h : (A n).Nonempty) : partitionCellCenter A x0 n ∈ A n := by
  classical
  simp only [partitionCellCenter,dif_pos h]
  exact h.choose_spec

lemma partitionCellCenter_dist_le {E : Type*} [PseudoMetricSpace E]
    (A : ℕ → Set E) (x0 : E) (n : ℕ) (δ : ℝ)
    (hb : Bornology.IsBounded (A n)) (hd : Metric.diam (A n) ≤ δ) (x : E) (hx : x ∈ A n) :
    dist x (partitionCellCenter A x0 n) ≤ δ :=
  (Metric.dist_le_diam_of_mem hb hx (partitionCellCenter_mem A x0 n ⟨x,hx⟩)).trans hd

lemma exists_countable_measurable_partition_centers {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [SeparableSpace E]
    (x0 : E) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (A : ℕ → Set E) (a : ℕ → E), (∀ n, MeasurableSet (A n)) ∧
      (∀ n, Bornology.IsBounded (A n)) ∧ (∀ n, Metric.diam (A n) ≤ δ) ∧
      (⋃ n, A n) = Set.univ ∧ Pairwise (fun n m => Disjoint (A n) (A m)) ∧
      ∀ n x, x ∈ A n → dist x (a n) ≤ δ := by
  obtain ⟨A,hm,hb,hd,hcover,hdisj⟩ := SeparableSpace.exists_measurable_partition_diam_le E hδ
  exact ⟨A,partitionCellCenter A x0,hm,hb,hd,hcover,hdisj,
    fun n x hx => partitionCellCenter_dist_le A x0 n δ (hb n) (hd n) x hx⟩

#print axioms finitePartitionHead_measurable
#print axioms cell_subset_finitePartitionHead
#print axioms truncatedPartitionCells_measurable
#print axioms truncatedPartitionCells_tail
#print axioms truncatedPartitionCells_disjoint
#print axioms truncatedPartitionCells_cover
#print axioms partitionCellCenter_mem
#print axioms partitionCellCenter_dist_le
#print axioms exists_countable_measurable_partition_centers
lemma finitePartitionHead_mono {E : Type*} (A : ℕ → Set E) : Monotone (finitePartitionHead A) := by
  intro N M hNM x hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨⟨i.val,lt_of_lt_of_le i.isLt hNM⟩,hi⟩

lemma iUnion_finitePartitionHead {E : Type*} (A : ℕ → Set E) :
    (⋃ N, finitePartitionHead A N) = ⋃ n, A n := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨N,hN⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hN
    exact Set.mem_iUnion.mpr ⟨i.val,hi⟩
  · intro x hx
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n+1,Set.mem_iUnion.mpr ⟨Fin.last n,hn⟩⟩

lemma partition_tail_tendsto_zero {E : Type*} [MeasurableSpace E]
    (Q : Measure E) [IsFiniteMeasure Q] (A : ℕ → Set E)
    (hA : ∀ n, MeasurableSet (A n)) (hcover : (⋃ n, A n) = Set.univ) :
    Tendsto (fun N => Q (finitePartitionHead A N)ᶜ) atTop (𝓝 0) := by
  have hm : Antitone (fun N => (finitePartitionHead A N)ᶜ) := by
    intro N M hNM
    exact Set.compl_subset_compl.mpr (finitePartitionHead_mono A hNM)
  have hi : (⋂ N, (finitePartitionHead A N)ᶜ) = ∅ := by
    rw [← Set.compl_iUnion,iUnion_finitePartitionHead,hcover,Set.compl_univ]
  have h := tendsto_measure_iInter_atTop (μ := Q)
    (fun N => (finitePartitionHead_measurable A hA N).compl.nullMeasurableSet) hm
    ⟨0,measure_ne_top Q _⟩
  change Tendsto (fun N => Q ((finitePartitionHead A N)ᶜ)) atTop
    (𝓝 (Q (⋂ N, (finitePartitionHead A N)ᶜ))) at h
  rw [hi,measure_empty] at h
  exact h

lemma exists_common_small_partition_tail {E : Type*} [MeasurableSpace E]
    (Q Q' : Measure E) [IsFiniteMeasure Q] [IsFiniteMeasure Q'] (A : ℕ → Set E)
    (hA : ∀ n, MeasurableSet (A n)) (hcover : (⋃ n, A n) = Set.univ)
    (τ : ENNReal) (hτ : 0 < τ) :
    ∃ N, Q (finitePartitionHead A N)ᶜ + Q' (finitePartitionHead A N)ᶜ < τ := by
  have hlim : Tendsto (fun N => Q (finitePartitionHead A N)ᶜ + Q' (finitePartitionHead A N)ᶜ)
      atTop (𝓝 (0 : ENNReal)) := by
    simpa only [zero_add] using (partition_tail_tendsto_zero Q A hA hcover).add
      (partition_tail_tendsto_zero Q' A hA hcover)
  exact (hlim.eventually (eventually_lt_nhds hτ)).exists

lemma finite_partition_mass_sum_one {E I : Type*} [MeasurableSpace E] [Fintype I]
    (Q : Measure E) [IsProbabilityMeasure Q] (S : I → Set E) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hcover : (⋃ i, S i) = Set.univ) :
    (∑ i, Q (S i)) = 1 := by
  have h := congrArg (fun μ : Measure E => μ Set.univ) (finite_partition_restrict_sum Q S hS hd hcover)
  simpa [Measure.finsetSum_apply,Measure.restrict_apply_univ] using h

lemma finite_partition_real_mass_sum_one {E I : Type*} [MeasurableSpace E] [Fintype I]
    (Q : Measure E) [IsProbabilityMeasure Q] (S : I → Set E) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hcover : (⋃ i, S i) = Set.univ) :
    (∑ i, (Q (S i)).toReal) = 1 := by
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top Q (S i)),
    finite_partition_mass_sum_one Q S hS hd hcover,ENNReal.toReal_one]

lemma finite_partition_masses_simplex {E I : Type*} [MeasurableSpace E] [Fintype I]
    (Q : Measure E) [IsProbabilityMeasure Q] (S : I → Set E) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hcover : (⋃ i, S i) = Set.univ) :
    (fun i => (Q (S i)).toReal) ∈ stdSimplex ℝ I :=
  ⟨fun _ => ENNReal.toReal_nonneg,finite_partition_real_mass_sum_one Q S hS hd hcover⟩

#print axioms finitePartitionHead_mono
#print axioms iUnion_finitePartitionHead
#print axioms partition_tail_tendsto_zero
#print axioms exists_common_small_partition_tail
#print axioms finite_partition_mass_sum_one
#print axioms finite_partition_real_mass_sum_one
#print axioms finite_partition_masses_simplex
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichRounding
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma coupling_probability_from_fst {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (π : Measure (E × F)) (Q : Measure E) [IsProbabilityMeasure Q]
    (hπ : π.map Prod.fst = Q) : IsProbabilityMeasure π := by
  have hm := congrArg (fun μ : Measure E => μ Set.univ) hπ
  constructor
  simpa [Measure.map_apply measurable_fst MeasurableSet.univ] using hm

lemma coupling_partition_row_mass {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype J] (π : Measure (E × F)) (Q : Measure E) (hπ : π.map Prod.fst = Q)
    (S : I → Set E) (T : J → Set F) (hS : ∀ i, MeasurableSet (S i))
    (hT : ∀ j, MeasurableSet (T j)) (hdT : Pairwise (fun j k => Disjoint (T j) (T k)))
    (hcoverT : (⋃ j, T j) = Set.univ) (i : I) :
    (∑ j, π (S i ×ˢ T j)) = Q (S i) := by
  have hd : Pairwise (fun j k => Disjoint (S i ×ˢ T j) (S i ×ˢ T k)) :=
    fun j k hjk => Set.disjoint_prod.mpr (Or.inr (hdT hjk))
  have hsum := measure_iUnion (μ := π) hd (fun j => (hS i).prod (hT j))
  rw [tsum_fintype] at hsum
  have hu : (⋃ j, S i ×ˢ T j) = S i ×ˢ Set.univ := by
    ext z
    constructor
    · intro h
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
      exact ⟨hj.1,Set.mem_univ _⟩
    · intro h
      have hy : z.2 ∈ ⋃ j, T j := by rw [hcoverT]; exact Set.mem_univ _
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨j,⟨h.1,hj⟩⟩
  rw [← hsum,hu,Set.prod_univ]
  have hm := congrArg (fun μ : Measure E => μ (S i)) hπ
  rw [Measure.map_apply measurable_fst (hS i)] at hm
  exact hm

lemma coupling_partition_col_mass {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype I] (π : Measure (E × F)) (Q' : Measure F) (hπ : π.map Prod.snd = Q')
    (S : I → Set E) (T : J → Set F) (hS : ∀ i, MeasurableSet (S i))
    (hT : ∀ j, MeasurableSet (T j)) (hdS : Pairwise (fun i k => Disjoint (S i) (S k)))
    (hcoverS : (⋃ i, S i) = Set.univ) (j : J) :
    (∑ i, π (S i ×ˢ T j)) = Q' (T j) := by
  have hd : Pairwise (fun i k => Disjoint (S i ×ˢ T j) (S k ×ˢ T j)) :=
    fun i k hik => Set.disjoint_prod.mpr (Or.inl (hdS hik))
  have hsum := measure_iUnion (μ := π) hd (fun i => (hS i).prod (hT j))
  rw [tsum_fintype] at hsum
  have hu : (⋃ i, S i ×ˢ T j) = Set.univ ×ˢ T j := by
    ext z
    constructor
    · intro h
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
      exact ⟨Set.mem_univ _,hi.2⟩
    · intro h
      have hx : z.1 ∈ ⋃ i, S i := by rw [hcoverS]; exact Set.mem_univ _
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i,⟨hi,h.2⟩⟩
  rw [← hsum,hu,Set.univ_prod]
  have hm := congrArg (fun μ : Measure F => μ (T j)) hπ
  rw [Measure.map_apply measurable_snd (hT j)] at hm
  exact hm

noncomputable def partitionCouplingMatrix {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (π : Measure (E × F)) (S : I → Set E) (T : J → Set F) (ij : I × J) : ℝ :=
  (π (S ij.1 ×ˢ T ij.2)).toReal

lemma partitionCouplingMatrix_marginals {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype I] [Fintype J] (π : Measure (E × F)) (Q : Measure E) (Q' : Measure F)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (hπ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q')
    (S : I → Set E) (T : J → Set F) (hS : ∀ i, MeasurableSet (S i))
    (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (fun i k => Disjoint (S i) (S k)))
    (hdT : Pairwise (fun j k => Disjoint (T j) (T k)))
    (hcoverS : (⋃ i, S i) = Set.univ) (hcoverT : (⋃ j, T j) = Set.univ) :
    (∀ i, ∑ j, partitionCouplingMatrix π S T (i,j) = (Q (S i)).toReal) ∧
      (∀ j, ∑ i, partitionCouplingMatrix π S T (i,j) = (Q' (T j)).toReal) := by
  letI : IsProbabilityMeasure π := coupling_probability_from_fst π Q hπ.1
  constructor
  · intro i
    have h := congrArg ENNReal.toReal (coupling_partition_row_mass π Q hπ.1 S T hS hT hdT hcoverT i)
    rw [ENNReal.toReal_sum (fun j _ => measure_ne_top π (S i ×ˢ T j))] at h
    exact h
  · intro j
    have h := congrArg ENNReal.toReal (coupling_partition_col_mass π Q' hπ.2 S T hS hT hdS hcoverS j)
    rw [ENNReal.toReal_sum (fun i _ => measure_ne_top π (S i ×ˢ T j))] at h
    exact h

lemma partitionCouplingMatrix_simplex {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Fintype I] [Fintype J] (π : Measure (E × F)) (Q : Measure E) (Q' : Measure F)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (hπ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q')
    (S : I → Set E) (T : J → Set F) (hS : ∀ i, MeasurableSet (S i))
    (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (fun i k => Disjoint (S i) (S k)))
    (hdT : Pairwise (fun j k => Disjoint (T j) (T k)))
    (hcoverS : (⋃ i, S i) = Set.univ) (hcoverT : (⋃ j, T j) = Set.univ) :
    partitionCouplingMatrix π S T ∈ stdSimplex ℝ (I × J) := by
  have hrow := (partitionCouplingMatrix_marginals π Q Q' hπ S T hS hT hdS hdT hcoverS hcoverT).1
  constructor
  · intro ij
    exact ENNReal.toReal_nonneg
  · rw [Fintype.sum_prod_type]
    simp_rw [hrow]
    exact finite_partition_real_mass_sum_one Q S hS hdS hcoverS

#print axioms coupling_probability_from_fst
#print axioms coupling_partition_row_mass
#print axioms coupling_partition_col_mass
#print axioms partitionCouplingMatrix_marginals
#print axioms partitionCouplingMatrix_simplex
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichCountableLift
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

noncomputable def countableProductLift {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Countable I] [Countable J] (w : I × J → ENNReal)
    (ρ : I → Measure E) (σ : J → Measure F) : Measure (E × F) :=
  Measure.sum (fun ij => w ij • (ρ ij.1).prod (σ ij.2))

lemma countableProductLift_fst {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Countable I] [Countable J] (w : I × J → ENNReal)
    (ρ : I → Measure E) (σ : J → Measure F) (hσ : ∀ j, IsProbabilityMeasure (σ j)) :
    (countableProductLift w ρ σ).map Prod.fst = Measure.sum (fun i => (∑' j, w (i,j)) • ρ i) := by
  letI : ∀ j, IsProbabilityMeasure (σ j) := hσ
  unfold countableProductLift
  rw [Measure.map_sum measurable_fst.aemeasurable]
  simp_rw [Measure.map_smul,Measure.map_fst_prod,measure_univ,one_smul]
  ext s hs
  simp only [Measure.sum_apply _ hs,Measure.smul_apply,smul_eq_mul]
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_mul_right]

lemma countableProductLift_snd {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Countable I] [Countable J] (w : I × J → ENNReal)
    (ρ : I → Measure E) (σ : J → Measure F) (hρ : ∀ i, IsProbabilityMeasure (ρ i))
    (hσ : ∀ j, IsProbabilityMeasure (σ j)) :
    (countableProductLift w ρ σ).map Prod.snd = Measure.sum (fun j => (∑' i, w (i,j)) • σ j) := by
  letI : ∀ i, IsProbabilityMeasure (ρ i) := hρ
  letI : ∀ j, IsProbabilityMeasure (σ j) := hσ
  unfold countableProductLift
  rw [Measure.map_sum measurable_snd.aemeasurable]
  simp_rw [Measure.map_smul,Measure.map_snd_prod,measure_univ,one_smul]
  ext s hs
  simp only [Measure.sum_apply _ hs,Measure.smul_apply,smul_eq_mul]
  rw [ENNReal.tsum_prod',ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_right]

lemma countable_partition_restrict_sum {E I : Type*} [MeasurableSpace E] [Countable I]
    (Q : Measure E) (S : I → Set E) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hcover : (⋃ i, S i) = Set.univ) :
    Measure.sum (fun i => Q.restrict (S i)) = Q := by
  have h := Measure.restrict_iUnion (μ := Q) hd hS
  rw [hcover,Measure.restrict_univ] at h
  exact h.symm

noncomputable def countableCellLift {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Countable I] [Countable J] (Q : Measure E) (Q' : Measure F) (S : I → Set E) (T : J → Set F)
    (w : I × J → ENNReal) (x0 : E) (y0 : F) : Measure (E × F) :=
  countableProductLift w (fun i => probabilityCell Q (S i) x0) (fun j => probabilityCell Q' (T j) y0)

lemma countableCellLift_marginals {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Countable I] [Countable J] (Q : Measure E) (Q' : Measure F)
    [IsFiniteMeasure Q] [IsFiniteMeasure Q'] (S : I → Set E) (T : J → Set F)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hdT : Pairwise (fun i j => Disjoint (T i) (T j)))
    (hcoverS : (⋃ i, S i) = Set.univ) (hcoverT : (⋃ j, T j) = Set.univ)
    (w : I × J → ENNReal) (hrow : ∀ i, ∑' j, w (i,j) = Q (S i))
    (hcol : ∀ j, ∑' i, w (i,j) = Q' (T j)) (x0 : E) (y0 : F) :
    (countableCellLift Q Q' S T w x0 y0).map Prod.fst = Q ∧
      (countableCellLift Q Q' S T w x0 y0).map Prod.snd = Q' := by
  constructor
  · unfold countableCellLift
    rw [countableProductLift_fst w _ _ (fun j => probabilityCell_isProbability Q' (T j) y0)]
    simp_rw [hrow,cell_mass_smul_probabilityCell]
    exact countable_partition_restrict_sum Q S hS hdS hcoverS
  · unfold countableCellLift
    rw [countableProductLift_snd w _ _ (fun i => probabilityCell_isProbability Q (S i) x0)
      (fun j => probabilityCell_isProbability Q' (T j) y0)]
    simp_rw [hcol,cell_mass_smul_probabilityCell]
    exact countable_partition_restrict_sum Q' T hT hdT hcoverT

lemma countableProductLift_lintegral {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Countable I] [Countable J] (w : I × J → ENNReal)
    (ρ : I → Measure E) (σ : J → Measure F) (f : E × F → ENNReal) :
    (∫⁻ z, f z ∂countableProductLift w ρ σ) = ∑' ij, w ij * (∫⁻ z, f z ∂(ρ ij.1).prod (σ ij.2)) := by
  simp only [countableProductLift,lintegral_sum_measure,lintegral_smul_measure,smul_eq_mul]

#print axioms countableProductLift_fst
#print axioms countableProductLift_snd
#print axioms countable_partition_restrict_sum
#print axioms countableCellLift_marginals
#print axioms countableProductLift_lintegral
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichCountableLiftCost
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma nonzero_entry_tsum_row_mass {I J : Type*} (w : I × J → ENNReal) (m : I → ENNReal)
    (hrow : ∀ i, ∑' j, w (i,j) = m i) (i : I) (j : J) (hw : w (i,j) ≠ 0) : m i ≠ 0 := by
  intro hm
  have hle : w (i,j) ≤ m i := by
    rw [← hrow i]
    exact ENNReal.le_tsum j
  rw [hm] at hle
  exact hw (le_zero_iff.mp hle)

lemma countableCellLift_isProbability {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Countable I] [Countable J] (Q : Measure E) (Q' : Measure F)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] (S : I → Set E) (T : J → Set F)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hdT : Pairwise (fun i j => Disjoint (T i) (T j)))
    (hcoverS : (⋃ i, S i) = Set.univ) (hcoverT : (⋃ j, T j) = Set.univ)
    (w : I × J → ENNReal) (hrow : ∀ i, ∑' j, w (i,j) = Q (S i))
    (hcol : ∀ j, ∑' i, w (i,j) = Q' (T j)) (x0 : E) (y0 : F) :
    IsProbabilityMeasure (countableCellLift Q Q' S T w x0 y0) :=
  coupling_probability_from_fst _ Q (countableCellLift_marginals Q Q' S T hS hT hdS hdT
    hcoverS hcoverT w hrow hcol x0 y0).1

lemma countableCellLift_cost_le_of_cellwise_bound {E F I J : Type*}
    [MeasurableSpace E] [MeasurableSpace F] [Countable I] [Countable J]
    (Q : Measure E) (Q' : Measure F) [IsFiniteMeasure Q] [IsFiniteMeasure Q']
    (S : I → Set E) (T : J → Set F) (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (w : I × J → ENNReal) (hrow : ∀ i, ∑' j, w (i,j) = Q (S i))
    (hcol : ∀ j, ∑' i, w (i,j) = Q' (T j)) (x0 : E) (y0 : F)
    (f : E × F → ENNReal) (C : I × J → ENNReal)
    (hc : ∀ i j x y, x ∈ S i → y ∈ T j → f (x,y) ≤ C (i,j)) :
    (∫⁻ z, f z ∂countableCellLift Q Q' S T w x0 y0) ≤ ∑' ij, w ij * C ij := by
  unfold countableCellLift
  rw [countableProductLift_lintegral]
  apply ENNReal.tsum_le_tsum
  intro ij
  obtain ⟨i,j⟩ := ij
  by_cases hw : w (i,j) = 0
  · simp [hw]
  · have hQS := nonzero_entry_tsum_row_mass w (fun i => Q (S i)) hrow i j hw
    have hQT := nonzero_entry_tsum_row_mass (fun ji : J × I => w (ji.2,ji.1))
      (fun j => Q' (T j)) hcol j i hw
    letI : IsProbabilityMeasure (probabilityCell Q (S i) x0) := probabilityCell_isProbability Q (S i) x0
    letI : IsProbabilityMeasure (probabilityCell Q' (T j) y0) := probabilityCell_isProbability Q' (T j) y0
    have hcost : (∫⁻ z, f z ∂(probabilityCell Q (S i) x0).prod (probabilityCell Q' (T j) y0)) ≤ C (i,j) := by
      have hae := probability_cell_product_ae_cells Q Q' (S i) (T j) (hS i) (hT j) hQS hQT x0 y0
      have hle := lintegral_mono_ae (hae.mono fun z hz => hc i j z.1 z.2 hz.1 hz.2)
      simpa only [lintegral_const,measure_univ,mul_one] using hle
    gcongr

#print axioms nonzero_entry_tsum_row_mass
#print axioms countableCellLift_isProbability
#print axioms countableCellLift_cost_le_of_cellwise_bound
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichCountableRounding
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma countable_coupling_partition_row_mass {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Countable J] (π : Measure (E × F)) (Q : Measure E) (hπ : π.map Prod.fst = Q)
    (S : I → Set E) (T : J → Set F) (hS : ∀ i, MeasurableSet (S i))
    (hT : ∀ j, MeasurableSet (T j)) (hdT : Pairwise (fun j k => Disjoint (T j) (T k)))
    (hcoverT : (⋃ j, T j) = Set.univ) (i : I) :
    (∑' j, π (S i ×ˢ T j)) = Q (S i) := by
  have hd : Pairwise (fun j k => Disjoint (S i ×ˢ T j) (S i ×ˢ T k)) :=
    fun j k hjk => Set.disjoint_prod.mpr (Or.inr (hdT hjk))
  have hsum := measure_iUnion (μ := π) hd (fun j => (hS i).prod (hT j))
  have hu : (⋃ j, S i ×ˢ T j) = S i ×ˢ Set.univ := by
    ext z
    constructor
    · intro h
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
      exact ⟨hj.1,Set.mem_univ _⟩
    · intro h
      have hy : z.2 ∈ ⋃ j, T j := by rw [hcoverT]; exact Set.mem_univ _
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨j,⟨h.1,hj⟩⟩
  rw [← hsum,hu,Set.prod_univ]
  have hm := congrArg (fun μ : Measure E => μ (S i)) hπ
  rw [Measure.map_apply measurable_fst (hS i)] at hm
  exact hm

lemma countable_coupling_partition_col_mass {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Countable I] (π : Measure (E × F)) (Q' : Measure F) (hπ : π.map Prod.snd = Q')
    (S : I → Set E) (T : J → Set F) (hS : ∀ i, MeasurableSet (S i))
    (hT : ∀ j, MeasurableSet (T j)) (hdS : Pairwise (fun i k => Disjoint (S i) (S k)))
    (hcoverS : (⋃ i, S i) = Set.univ) (j : J) :
    (∑' i, π (S i ×ˢ T j)) = Q' (T j) := by
  have hd : Pairwise (fun i k => Disjoint (S i ×ˢ T j) (S k ×ˢ T j)) :=
    fun i k hik => Set.disjoint_prod.mpr (Or.inl (hdS hik))
  have hsum := measure_iUnion (μ := π) hd (fun i => (hS i).prod (hT j))
  have hu : (⋃ i, S i ×ˢ T j) = Set.univ ×ˢ T j := by
    ext z
    constructor
    · intro h
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
      exact ⟨Set.mem_univ _,hi.2⟩
    · intro h
      have hx : z.1 ∈ ⋃ i, S i := by rw [hcoverS]; exact Set.mem_univ _
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i,⟨hi,h.2⟩⟩
  rw [← hsum,hu,Set.univ_prod]
  have hm := congrArg (fun μ : Measure F => μ (T j)) hπ
  rw [Measure.map_apply measurable_snd (hT j)] at hm
  exact hm


#print axioms countable_coupling_partition_row_mass
#print axioms countable_coupling_partition_col_mass
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichCountableRect
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma rectangle_partition_disjoint {E F I J : Type*} (S : I → Set E) (T : J → Set F)
    (hdS : Pairwise (fun i k => Disjoint (S i) (S k)))
    (hdT : Pairwise (fun j k => Disjoint (T j) (T k))) :
    Pairwise (fun ij kl : I × J => Disjoint (S ij.1 ×ˢ T ij.2) (S kl.1 ×ˢ T kl.2)) := by
  intro ij kl hne
  by_cases hi : ij.1 = kl.1
  · apply Set.disjoint_prod.mpr
    right
    apply hdT
    intro hj
    exact hne (Prod.ext hi hj)
  · exact Set.disjoint_prod.mpr (Or.inl (hdS hi))

lemma rectangle_partition_cover {E F I J : Type*} (S : I → Set E) (T : J → Set F)
    (hS : (⋃ i, S i) = Set.univ) (hT : (⋃ j, T j) = Set.univ) :
    (⋃ ij : I × J, S ij.1 ×ˢ T ij.2) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  have hx : z.1 ∈ ⋃ i, S i := by rw [hS]; exact Set.mem_univ _
  have hy : z.2 ∈ ⋃ j, T j := by rw [hT]; exact Set.mem_univ _
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hy
  exact Set.mem_iUnion.mpr ⟨(i,j),hi,hj⟩

lemma countable_rectangle_cost_sum_le {E F I J : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [Countable I] [Countable J] (π : Measure (E × F)) (S : I → Set E) (T : J → Set F)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (fun i k => Disjoint (S i) (S k)))
    (hdT : Pairwise (fun j k => Disjoint (T j) (T k)))
    (hcoverS : (⋃ i, S i) = Set.univ) (hcoverT : (⋃ j, T j) = Set.univ)
    (f : E × F → ENNReal) (C : I × J → ENNReal)
    (hc : ∀ i j x y, x ∈ S i → y ∈ T j → C (i,j) ≤ f (x,y)) :
    (∑' ij : I × J, π (S ij.1 ×ˢ T ij.2) * C ij) ≤ ∫⁻ z, f z ∂π := by
  have hμ := countable_partition_restrict_sum π (fun ij : I × J => S ij.1 ×ˢ T ij.2)
    (fun ij => (hS ij.1).prod (hT ij.2)) (rectangle_partition_disjoint S T hdS hdT)
    (rectangle_partition_cover S T hcoverS hcoverT)
  calc
    (∑' ij : I × J, π (S ij.1 ×ˢ T ij.2) * C ij) =
        ∑' ij : I × J, ∫⁻ _ : E × F, C ij ∂π.restrict (S ij.1 ×ˢ T ij.2) := by
      simp only [lintegral_const,Measure.restrict_apply_univ,mul_comm]
    _ ≤ ∑' ij : I × J, ∫⁻ z, f z ∂π.restrict (S ij.1 ×ˢ T ij.2) := by
      apply ENNReal.tsum_le_tsum
      intro ij
      exact lintegral_mono_ae ((ae_restrict_mem ((hS ij.1).prod (hT ij.2))).mono
        (fun z hz => hc ij.1 ij.2 z.1 z.2 hz.1 hz.2))
    _ = ∫⁻ z, f z ∂π := by
      rw [← lintegral_sum_measure,hμ]

#print axioms rectangle_partition_disjoint
#print axioms rectangle_partition_cover
#print axioms countable_rectangle_cost_sum_le
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichDenseCells
set_option autoImplicit false
open MeasureTheory TopologicalSpace
namespace DualityCodex

lemma exists_dense_range_partition_centers {E Z : Type*} [PseudoMetricSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z] [SeparableSpace Z]
    (f : E → Z) (hfd : DenseRange f) (x0 : E) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (A : ℕ → Set Z) (a : ℕ → E), (∀ n, MeasurableSet (A n)) ∧
      (⋃ n, A n) = Set.univ ∧ Pairwise (fun n m => Disjoint (A n) (A m)) ∧
      ∀ n z, z ∈ A n → dist z (f (a n)) ≤ δ := by
  obtain ⟨A,c,hm,hb,hd,hcover,hdisj,hcenter⟩ :=
    exists_countable_measurable_partition_centers (f x0) (δ/2) (by positivity)
  have hx : ∀ n, ∃ x, dist (c n) (f x) < δ/2 := fun n => hfd.exists_dist_lt (c n) (by positivity)
  choose a ha using hx
  refine ⟨A,a,hm,hcover,hdisj,?_⟩
  intro n z hz
  have h := dist_triangle z (c n) (f (a n))
  have h1 := hcenter n z hz
  have h2 := ha n
  linarith

lemma preimage_partition_disjoint {E Z I : Type*} (f : E → Z) (A : I → Set Z)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    Pairwise (fun i j => Disjoint (f ⁻¹' A i) (f ⁻¹' A j)) := by
  intro i j hij
  exact (hd hij).preimage f

lemma preimage_partition_cover {E Z I : Type*} (f : E → Z) (A : I → Set Z)
    (hcover : (⋃ i, A i) = Set.univ) : (⋃ i, f ⁻¹' A i) = Set.univ := by
  rw [← Set.preimage_iUnion,hcover,Set.preimage_univ]

lemma isometry_cell_pair_distance {E Z : Type*} [PseudoMetricSpace E] [PseudoMetricSpace Z]
    (f : E → Z) (hf : Isometry f) (x y a b : E) (δ : ℝ)
    (hx : dist (f x) (f a) ≤ δ) (hy : dist (f y) (f b) ≤ δ) :
    dist x y ≤ dist a b + 2 * δ := by
  have h := dist_triangle4 (f x) (f a) (f b) (f y)
  rw [hf.dist_eq,hf.dist_eq,hf.dist_eq,hf.dist_eq] at h
  rw [hf.dist_eq] at hx hy
  have hrev : dist b y ≤ δ := by simpa only [dist_comm] using hy
  linarith

lemma centered_cell_pair_distance {Z : Type*} [PseudoMetricSpace Z] (x y a b : Z) (δ : ℝ)
    (hx : dist x a ≤ δ) (hy : dist y b ≤ δ) :
    dist a b + 2 * δ ≤ dist x y + 4 * δ := by
  have h := dist_triangle4 a x y b
  have hrev : dist a x ≤ δ := by simpa only [dist_comm] using hx
  linarith

#print axioms exists_dense_range_partition_centers
#print axioms preimage_partition_disjoint
#print axioms preimage_partition_cover
#print axioms isometry_cell_pair_distance
#print axioms centered_cell_pair_distance
end DualityCodex

-- Complete local proof: Solutions.DualityReplay_FiniteModulus
set_option autoImplicit false
namespace DualityReplayCodex
open WassersteinDRO.Duality

lemma abs_sub_le_modulus_mul_dist {E : Type*} [NormedAddCommGroup E]
    (l : E → ℝ) (hfinite : lipschitzModulus l ≠ ⊤) (x y : E) :
    |l x - l y| ≤ (lipschitzModulus l).toReal * ‖x - y‖ := by
  by_cases hxy : x = y
  · subst y
    simp
  have hm : ENNReal.ofReal (|l x - l y| / ‖x - y‖) ≤ lipschitzModulus l :=
    le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le hxy le_rfl))
  have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [← ENNReal.ofReal_toReal hfinite] at hm
  have hr : |l x - l y| / ‖x - y‖ ≤ (lipschitzModulus l).toReal :=
    (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hm
  exact (div_le_iff₀ hn).mp hr

lemma modulus_zero_constant {E : Type*} [NormedAddCommGroup E]
    (l : E → ℝ) (hzero : lipschitzModulus l = 0) (x y : E) : l x = l y := by
  have hf : lipschitzModulus l ≠ ⊤ := by simp [hzero]
  have h := abs_sub_le_modulus_mul_dist l hf x y
  simp only [hzero, ENNReal.toReal_zero, zero_mul, abs_nonpos_iff] at h
  exact sub_eq_zero.mp h

#print axioms abs_sub_le_modulus_mul_dist
#print axioms modulus_zero_constant
end DualityReplayCodex

-- Complete local proof: Solutions.DualityReplay_SignedExpectation
set_option autoImplicit false
open MeasureTheory
namespace DualityReplayCodex
open WassersteinDRO.Duality

lemma erealExpectation_eq_integral {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (l : E → ℝ) (hl : Integrable l Q) :
    erealExpectation Q (fun x => (l x : EReal)) = (∫ x, l x ∂Q : ℝ) := by
  have hp : (∫⁻ x, ENNReal.ofReal (l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm l).trans_lt hl.2).ne
  have hn : (∫⁻ x, ENNReal.ofReal (-l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm (fun x => -l x)).trans_lt hl.neg.2).ne
  unfold erealExpectation
  rw [if_neg (show (∫⁻ x, ((l x : EReal)).toENNReal ∂Q) ≠ ⊤ from hp)]
  simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
  rw [ ← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hl]

lemma nominalRisk_eq_integral {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (l : E → ℝ) (hl : Integrable l Q) :
    nominalRisk Q l = (∫ x, l x ∂Q : ℝ) :=
  erealExpectation_eq_integral Q l hl

#print axioms erealExpectation_eq_integral
#print axioms nominalRisk_eq_integral
end DualityReplayCodex

-- Complete local proof: Solutions.DualityReplay_Empirical
set_option autoImplicit false
namespace DualityReplayCodex
open MeasureTheory
open scoped BigOperators
open WassersteinDRO.Duality

lemma empirical_probability {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (hn : 0 < n) (X : Fin n → Z) : IsProbabilityMeasure (empiricalDistribution X) := by
  constructor
  simp [empiricalDistribution, Measure.smul_apply, Measure.finsetSum_apply]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

lemma empirical_map {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W] {n : ℕ}
    (X : Fin n → Z) (f : Z → W) (hf : Measurable f) :
    (empiricalDistribution X).map f = empiricalDistribution (fun i => f (X i)) := by
  unfold empiricalDistribution
  rw [Measure.map_smul, Measure.map_finset_sum' hf.aemeasurable]
  simp only [Measure.map_dirac' hf]

lemma empirical_lintegral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (X : Fin n → Z) (f : Z → ENNReal) :
    (∫⁻ z, f z ∂empiricalDistribution X) = (n : ENNReal)⁻¹ * ∑ i, f (X i) := by
  unfold empiricalDistribution
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac]
  rfl

lemma empirical_coupling {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (Y : Fin n → W) :
    IsProbabilityMeasure (empiricalDistribution (fun i => (X i, Y i))) ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.fst = empiricalDistribution X ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.snd = empiricalDistribution Y := by
  refine ⟨empirical_probability hn _, ?_, ?_⟩
  · exact empirical_map _ Prod.fst measurable_fst
  · exact empirical_map _ Prod.snd measurable_snd

lemma empirical_integrable {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (l : Z → ℝ) :
    Integrable l (empiricalDistribution X) := by
  unfold empiricalDistribution
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro i hi
    exact integrable_dirac (by simp)
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hn.ne')

lemma empirical_integral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (X : Fin n → Z) (l : Z → ℝ) :
    (∫ z, l z ∂empiricalDistribution X) = (n : ℝ)⁻¹ * ∑ i, l (X i) := by
  unfold empiricalDistribution
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  · intro i hi
    exact integrable_dirac (by simp)

lemma empirical_nominalRisk {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (l : Z → ℝ) :
    nominalRisk (empiricalDistribution X) l = ((n : ℝ)⁻¹ * ∑ i, l (X i) : ℝ) := by
  rw [nominalRisk_eq_integral _ _ (empirical_integrable hn X l), empirical_integral]

#print axioms empirical_probability
#print axioms empirical_map
#print axioms empirical_lintegral
#print axioms empirical_coupling
#print axioms empirical_integrable
#print axioms empirical_integral
#print axioms empirical_nominalRisk
end DualityReplayCodex

-- Complete local proof: Solutions.DualityReplay_Diagonal
set_option autoImplicit false
open MeasureTheory
namespace DualityReplayCodex
open WassersteinDRO.Duality

lemma wasserstein_one_eq {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (Q P : Measure E) :
    wassersteinDistance 1 Q P =
      ⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = P),
        ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π := by
  simp [wassersteinDistance]

lemma wasserstein_one_le_coupling {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (Q P : Measure E) (π : Measure (E × E))
    (hπ : π.map Prod.fst = Q ∧ π.map Prod.snd = P) :
    wassersteinDistance 1 Q P ≤ ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π := by
  rw [wasserstein_one_eq]
  exact iInf_le_of_le π (iInf_le_of_le hπ le_rfl)

lemma empirical_wasserstein_self {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [NormedAddCommGroup E] {N : ℕ} (hN : 0 < N) (X : Fin N → E) :
    wassersteinDistance 1 (empiricalDistribution X) (empiricalDistribution X) = 0 := by
  apply le_antisymm _ bot_le
  have hc := empirical_coupling hN X X
  apply (wasserstein_one_le_coupling _ _ _ ⟨hc.2.1, hc.2.2⟩).trans
  rw [empirical_lintegral]
  simp

lemma empirical_in_ambiguity {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [NormedAddCommGroup E] {N : ℕ} (hN : 0 < N) (X : Fin N → E) (ε : ℝ) :
    empiricalDistribution X ∈ ambiguitySet ε 1 Set.univ (empiricalDistribution X) := by
  have := empirical_probability hN X
  exact ⟨measure_univ, by simp, by rw [empirical_wasserstein_self hN X]; exact bot_le⟩

lemma nominalRisk_le_worstCaseRisk {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup E] {N : ℕ}
    (hN : 0 < N) (X : Fin N → E) (ε : ℝ) (l : E → ℝ) :
    nominalRisk (empiricalDistribution X) l ≤
      worstCaseRisk ε 1 Set.univ (empiricalDistribution X) l := by
  exact le_iSup_of_le (empiricalDistribution X)
    (le_iSup_of_le (empirical_in_ambiguity hN X ε) le_rfl)

#print axioms wasserstein_one_eq
#print axioms wasserstein_one_le_coupling
#print axioms empirical_wasserstein_self
#print axioms empirical_in_ambiguity
#print axioms nominalRisk_le_worstCaseRisk
end DualityReplayCodex

-- Complete local proof: Solutions.DualityReplay_SignedCoupling
set_option autoImplicit false
open MeasureTheory
namespace DualityReplayCodex
open WassersteinDRO.Duality

lemma finite_modulus_lipschitz {E : Type*} [NormedAddCommGroup E]
    (l : E → ℝ) (hfinite : lipschitzModulus l ≠ ⊤) :
    LipschitzWith ⟨(lipschitzModulus l).toReal, ENNReal.toReal_nonneg⟩ l := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, Real.norm_eq_abs]
  change |l x - l y| ≤ (lipschitzModulus l).toReal * ‖x - y‖
  exact abs_sub_le_modulus_mul_dist l hfinite x y

lemma signed_coupling_upper {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q P : Measure E) (π : Measure (E × E)) (l : E → ℝ) (L : ℝ)
    (hl : Measurable l) (_hL : 0 ≤ L)
    (hbound : ∀ x y, |l x - l y| ≤ L * ‖x - y‖)
    (hP : Integrable l P) (hπ : π.map Prod.fst = Q ∧ π.map Prod.snd = P)
    (hcost : (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π) ≠ ⊤) :
    Integrable l Q ∧ (∫ x, l x ∂Q) ≤
      (∫ x, l x ∂P) + L * (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π).toReal := by
  have hm : Measurable (fun z : E × E => ‖z.1 - z.2‖) :=
    (measurable_fst.sub measurable_snd).norm
  have hi : Integrable (fun z : E × E => ‖z.1 - z.2‖) π :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => norm_nonneg (z.1 - z.2))).mp hcost
  have hPs : Integrable l (π.map Prod.snd) := by rwa [hπ.2]
  have hs : Integrable (fun z : E × E => l z.2) π := hPs.comp_measurable measurable_snd
  have hb : Integrable (fun z : E × E => ‖l z.2‖ + L * ‖z.1 - z.2‖) π :=
    hs.norm.add (hi.const_mul L)
  have hf : Integrable (fun z : E × E => l z.1) π := by
    apply hb.mono' (hl.comp measurable_fst).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    have h := hbound z.1 z.2
    have ha := abs_add_le (l z.1 - l z.2) (l z.2)
    simp only [sub_add_cancel] at ha
    simp only [Real.norm_eq_abs, Function.comp_apply]
    linarith
  have hQ : Integrable l Q := by
    rw [← hπ.1]
    exact (integrable_map_measure hl.aestronglyMeasurable measurable_fst.aemeasurable).mpr hf
  refine ⟨hQ, ?_⟩
  have hfst : (∫ x, l x ∂Q) = ∫ z, l z.1 ∂π := by
    rw [← hπ.1]
    exact integral_map_of_stronglyMeasurable measurable_fst hl.stronglyMeasurable
  have hsnd : (∫ x, l x ∂P) = ∫ z, l z.2 ∂π := by
    rw [← hπ.2]
    exact integral_map_of_stronglyMeasurable measurable_snd hl.stronglyMeasurable
  rw [hfst, hsnd]
  calc
    (∫ z, l z.1 ∂π) ≤ ∫ z, l z.2 + L * ‖z.1 - z.2‖ ∂π := by
      apply integral_mono hf (hs.add (hi.const_mul L))
      intro z
      simp only [Pi.add_apply]
      have h := (le_abs_self (l z.1 - l z.2)).trans (hbound z.1 z.2)
      linarith
    _ = (∫ z, l z.2 ∂π) + L * (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π).toReal := by
      rw [integral_add hs (hi.const_mul L), integral_const_mul,
        integral_eq_lintegral_of_nonneg_ae (f := fun z : E × E => ‖z.1 - z.2‖)
          (Filter.Eventually.of_forall fun z => norm_nonneg (z.1 - z.2)) hm.aestronglyMeasurable]

#print axioms finite_modulus_lipschitz
#print axioms signed_coupling_upper
end DualityReplayCodex

-- Complete local proof: Solutions.Duality_ExpectationMonotone
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma erealExpectation_mono {Z : Type*} [MeasurableSpace Z] (Q : Measure Z)
    (f g : Z → EReal) (hfg : f ≤ᵐ[Q] g) :
    erealExpectation Q f ≤ erealExpectation Q g := by
  have hpos : (∫⁻ z, (f z).toENNReal ∂Q) ≤ ∫⁻ z, (g z).toENNReal ∂Q :=
    lintegral_mono_ae (hfg.mono fun z hz => EReal.toENNReal_le_toENNReal hz)
  have hneg : (∫⁻ z, (-g z).toENNReal ∂Q) ≤ ∫⁻ z, (-f z).toENNReal ∂Q :=
    lintegral_mono_ae (hfg.mono fun z hz => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hz))
  unfold erealExpectation
  by_cases hgtop : (∫⁻ z, (g z).toENNReal ∂Q) = ⊤
  · rw [if_pos hgtop]
    exact le_top
  · have hftop : (∫⁻ z, (f z).toENNReal ∂Q) ≠ ⊤ :=
      (lt_of_le_of_lt hpos (lt_top_iff_ne_top.mpr hgtop)).ne
    rw [if_neg hgtop, if_neg hftop]
    exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hpos)
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hneg)

#print axioms erealExpectation_mono
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichWeak
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex
open WassersteinDRO.Duality

lemma erealExpectation_ennreal {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (f : Z → ENNReal) :
    erealExpectation μ (fun z => (f z : EReal)) = ((∫⁻ z, f z ∂μ) : EReal) := by
  have hneg : ∀ z, (-(f z : EReal)).toENNReal = 0 := by
    intro z
    apply EReal.toENNReal_eq_zero_iff.mpr
    exact EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _)
  unfold erealExpectation
  simp only [EReal.toENNReal_coe, hneg, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]
  split_ifs with h
  · simp [h]
  · rfl

lemma integral_le_extended_cost {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (f : Z → ℝ) (c : Z → ENNReal) (hf : Integrable f μ)
    (hbound : ∀ᵐ z ∂μ, (f z : EReal) ≤ (c z : EReal)) :
    ((∫ z, f z ∂μ : ℝ) : EReal) ≤ ((∫⁻ z, c z ∂μ) : EReal) := by
  have h := erealExpectation_mono μ (fun z => (f z : EReal)) (fun z => (c z : EReal)) hbound
  rw [DualityReplayCodex.erealExpectation_eq_integral μ f hf, erealExpectation_ennreal] at h
  exact h

lemma real_le_transport_inf {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (Q Q' : Measure E) (p a : ℝ)
    (h : ∀ (π : Measure (E × E)), π.map Prod.fst = Q ∧ π.map Prod.snd = Q' →
      (a : EReal) ≤ ((∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) : EReal)) :
    (a : EReal) ≤ ((⨅ (π : Measure (E × E))
      (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q'),
      ∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π : ENNReal) : EReal) := by
  by_cases ha : a ≤ 0
  · exact (EReal.coe_le_coe_iff.mpr ha).trans (EReal.coe_ennreal_nonneg _)
  · have ha0 : 0 ≤ a := (lt_of_not_ge ha).le
    have he : (ENNReal.ofReal a : EReal) = (a : EReal) := by
      rw [EReal.coe_ennreal_ofReal,max_eq_left ha0]
    rw [← he]
    apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    refine le_iInf fun π => le_iInf fun hπ => ?_
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mp (by rw [he]; exact h π hπ)

lemma wasserstein_power_eq_cost_inf {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (p : ℝ) (hp : 0 < p) (Q Q' : Measure E) :
    wassersteinDistance p Q Q' ^ p =
      ⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q'),
        ∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π := by
  unfold wassersteinDistance
  rw [← ENNReal.rpow_mul,one_div_mul_cancel hp.ne',ENNReal.rpow_one]

#print axioms erealExpectation_ennreal
#print axioms integral_le_extended_cost
#print axioms real_le_transport_inf
#print axioms wasserstein_power_eq_cost_inf
lemma kantorovich_coupling_lower_bound {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E]
    (Q Q' : Measure E) (p : ℝ) (φ ψ : E → ℝ)
    (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφ : Integrable φ Q) (hψ : Integrable ψ Q')
    (hc : ∀ x y : E, ψ x - φ y ≤ ‖x-y‖ ^ p)
    (π : Measure (E × E)) (hπ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q') :
    ((∫ x, ψ x ∂Q' - ∫ x, φ x ∂Q : ℝ) : EReal) ≤
      ((∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) : EReal) := by
  have hφπ : Integrable (fun z : E × E => φ z.1) π :=
    (show Integrable φ (π.map Prod.fst) by rw [hπ.1]; exact hφ).comp_measurable measurable_fst
  have hψπ : Integrable (fun z : E × E => ψ z.2) π :=
    (show Integrable ψ (π.map Prod.snd) by rw [hπ.2]; exact hψ).comp_measurable measurable_snd
  have hfst : (∫ z : E × E, φ z.1 ∂π) = ∫ x, φ x ∂Q := by
    rw [← hπ.1]
    exact (integral_map_of_stronglyMeasurable measurable_fst hφm.stronglyMeasurable).symm
  have hsnd : (∫ z : E × E, ψ z.2 ∂π) = ∫ x, ψ x ∂Q' := by
    rw [← hπ.2]
    exact (integral_map_of_stronglyMeasurable measurable_snd hψm.stronglyMeasurable).symm
  have h := integral_le_extended_cost π (fun z : E × E => ψ z.2 - φ z.1)
    (fun z => ENNReal.ofReal (‖z.1-z.2‖ ^ p)) (hψπ.sub hφπ) (Filter.Eventually.of_forall (by
      intro z
      rw [EReal.coe_ennreal_ofReal,max_eq_left (Real.rpow_nonneg (norm_nonneg _) p)]
      apply EReal.coe_le_coe_iff.mpr
      simpa only [norm_sub_rev] using hc z.2 z.1))
  rw [integral_sub hψπ hφπ,hsnd,hfst] at h
  exact h

lemma kantorovich_weak_duality {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E]
    (Q Q' : Measure E) (p : ℝ) (hp : 0 < p) (φ ψ : E → ℝ)
    (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφ : Integrable φ Q) (hψ : Integrable ψ Q')
    (hc : ∀ x y : E, ψ x - φ y ≤ ‖x-y‖ ^ p) :
    ((∫ x, ψ x ∂Q' - ∫ x, φ x ∂Q : ℝ) : EReal) ≤
      ((wassersteinDistance p Q Q' ^ p : ENNReal) : EReal) := by
  rw [wasserstein_power_eq_cost_inf p hp Q Q']
  apply real_le_transport_inf
  intro π hπ
  exact kantorovich_coupling_lower_bound Q Q' p φ ψ hφm hψm hφ hψ hc π hπ

lemma bounded_kantorovich_dual_le_primal {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E]
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (p : ℝ) (hp : 1 ≤ p) :
    (⨆ (φ : BoundedContinuousFunction E ℝ) (ψ : BoundedContinuousFunction E ℝ)
        (_ : ∀ x y : E, ψ x - φ y ≤ ‖x-y‖ ^ p),
      ((∫ x, ψ x ∂Q' - ∫ x, φ x ∂Q : ℝ) : EReal)) ≤
        ((wassersteinDistance p Q Q' ^ p : ENNReal) : EReal) := by
  refine iSup_le fun φ => iSup_le fun ψ => iSup_le fun hc => ?_
  exact kantorovich_weak_duality Q Q' p (lt_of_lt_of_le zero_lt_one hp) φ ψ
    φ.continuous.measurable ψ.continuous.measurable (φ.integrable (μ := Q)) (ψ.integrable (μ := Q')) hc

#print axioms kantorovich_coupling_lower_bound
#print axioms kantorovich_weak_duality
#print axioms bounded_kantorovich_dual_le_primal
lemma modulus_le_one_abs_bound {E : Type*} [NormedAddCommGroup E]
    (φ : E → ℝ) (hφ : lipschitzModulus φ ≤ 1) :
    ∀ x y, |φ x - φ y| ≤ ‖x-y‖ := by
  have hf : lipschitzModulus φ ≠ ⊤ := (lt_of_le_of_lt hφ (by norm_num : (1 : ENNReal) < ⊤)).ne
  have hL : (lipschitzModulus φ).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) hφ
  intro x y
  exact (DualityReplayCodex.abs_sub_le_modulus_mul_dist φ hf x y).trans
    (by nlinarith [norm_nonneg (x-y)])

lemma rubinstein_weak_duality {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E] [SecondCountableTopology E]
    (Q Q' : Measure E) (φ : E → ℝ) (hφ : lipschitzModulus φ ≤ 1)
    (hQ : Integrable φ Q) (hQ' : Integrable φ Q') :
    ((∫ x, φ x ∂Q - ∫ x, φ x ∂Q' : ℝ) : EReal) ≤
      ((wassersteinDistance 1 Q Q' : ENNReal) : EReal) := by
  have hf : lipschitzModulus φ ≠ ⊤ := (lt_of_le_of_lt hφ (by norm_num : (1 : ENNReal) < ⊤)).ne
  have hm : Measurable φ := (DualityReplayCodex.finite_modulus_lipschitz φ hf).continuous.measurable
  have hc : ∀ x y : E, -φ x - (-φ y) ≤ ‖x-y‖ ^ (1 : ℝ) := by
    intro x y
    have hb := modulus_le_one_abs_bound φ hφ x y
    rw [Real.rpow_one]
    have := neg_le_abs (φ x-φ y)
    linarith
  have h := kantorovich_weak_duality Q Q' 1 zero_lt_one (fun x => -φ x) (fun x => -φ x)
    hm.neg hm.neg hQ.neg hQ'.neg hc
  simpa only [integral_neg,neg_sub_neg,ENNReal.rpow_one] using h

lemma rubinstein_dual_le_primal {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E] [SecondCountableTopology E] (Q Q' : Measure E) :
    (⨆ (φ : E → ℝ) (_ : lipschitzModulus φ ≤ 1)
      (_ : Integrable φ Q) (_ : Integrable φ Q'),
      ((∫ x, φ x ∂Q - ∫ x, φ x ∂Q' : ℝ) : EReal)) ≤
        ((wassersteinDistance 1 Q Q' : ENNReal) : EReal) := by
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun hQ => iSup_le fun hQ' => ?_
  exact rubinstein_weak_duality Q Q' φ hφ hQ hQ'

#print axioms modulus_le_one_abs_bound
#print axioms rubinstein_weak_duality
#print axioms rubinstein_dual_le_primal
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichShiftRoot
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma shifted_power_cost_root_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (p : ℝ) (hp : 1 ≤ p) (a : ℝ) (ha : 0 ≤ a) :
    (∫⁻ x, ENNReal.ofReal ((f x+a)^p) ∂μ) ^ (1/p) ≤
      (∫⁻ x, ENNReal.ofReal ((f x)^p) ∂μ) ^ (1/p) + ENNReal.ofReal a := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h := ENNReal.lintegral_Lp_add_le (μ := μ) (ENNReal.continuous_ofReal.measurable.comp hf).aemeasurable
    (f := fun x => ENNReal.ofReal (f x)) (g := fun _ => ENNReal.ofReal a) aemeasurable_const hp
  have hshift : (fun x => (ENNReal.ofReal (f x)+ENNReal.ofReal a)^p) =
      (fun x => ENNReal.ofReal ((f x+a)^p)) := by
    funext x
    rw [← ENNReal.ofReal_add (hf0 x) ha,ENNReal.ofReal_rpow_of_nonneg (add_nonneg (hf0 x) ha) hp0.le]
  have hbase : (fun x => (ENNReal.ofReal (f x))^p) =
      (fun x => ENNReal.ofReal ((f x)^p)) := by
    funext x
    exact ENNReal.ofReal_rpow_of_nonneg (hf0 x) hp0.le
  have hconst : (∫⁻ _ : X, (ENNReal.ofReal a)^p ∂μ) ^ (1/p) = ENNReal.ofReal a := by
    rw [lintegral_const,measure_univ,mul_one,← ENNReal.rpow_mul,mul_one_div_cancel hp0.ne',ENNReal.rpow_one]
  change (∫⁻ x, (ENNReal.ofReal (f x)+ENNReal.ofReal a)^p ∂μ) ^ (1/p) ≤
    (∫⁻ x, (ENNReal.ofReal (f x))^p ∂μ) ^ (1/p) +
      (∫⁻ _ : X, (ENNReal.ofReal a)^p ∂μ) ^ (1/p) at h
  rw [hshift,hbase,hconst] at h
  exact h

#print axioms shifted_power_cost_root_le
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichDenseLift
set_option autoImplicit false
open MeasureTheory TopologicalSpace
namespace DualityCodex

lemma dense_isometry_coupling_lift_root {E Z : Type*} [PseudoMetricSpace E] [PseudoMetricSpace Z]
    [MeasurableSpace E] [MeasurableSpace Z] [BorelSpace E] [BorelSpace Z]
    [SecondCountableTopology E] [SecondCountableTopology Z]
    (f : E → Z) (hf : Isometry f) (hfm : Measurable f) (hfd : DenseRange f)
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (π : Measure (Z × Z)) (hπ : π.map Prod.fst = Q.map f ∧ π.map Prod.snd = Q'.map f)
    (p : ℝ) (hp : 1 ≤ p) (δ : ℝ) (hδ : 0 < δ) (x0 : E) :
    ∃ μ : Measure (E × E), (μ.map Prod.fst = Q ∧ μ.map Prod.snd = Q') ∧
      (∫⁻ z, ENNReal.ofReal ((dist z.1 z.2)^p) ∂μ) ^ (1/p) ≤
        (∫⁻ z, ENNReal.ofReal ((dist z.1 z.2)^p) ∂π) ^ (1/p) + ENNReal.ofReal (4*δ) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨A,a,hm,hcover,hdisj,hcenter⟩ := exists_dense_range_partition_centers f hfd x0 δ hδ
  let S : ℕ → Set E := fun i => f ⁻¹' A i
  let w : ℕ × ℕ → ENNReal := fun ij => π (A ij.1 ×ˢ A ij.2)
  have hS : ∀ i, MeasurableSet (S i) := fun i => (hm i).preimage hfm
  have hdS := preimage_partition_disjoint f A hdisj
  have hcoverS := preimage_partition_cover f A hcover
  have hrow : ∀ i, ∑' j, w (i,j) = Q (S i) := by
    intro i
    have h := countable_coupling_partition_row_mass π (Q.map f) hπ.1 A A hm hm hdisj hcover i
    rw [Measure.map_apply hfm (hm i)] at h
    exact h
  have hcol : ∀ j, ∑' i, w (i,j) = Q' (S j) := by
    intro j
    have h := countable_coupling_partition_col_mass π (Q'.map f) hπ.2 A A hm hm hdisj hcover j
    rw [Measure.map_apply hfm (hm j)] at h
    exact h
  let μ := countableCellLift Q Q' S S w x0 x0
  have hμ := countableCellLift_marginals Q Q' S S hS hS hdS hdS hcoverS hcoverS w hrow hcol x0 x0
  let C : ℕ × ℕ → ENNReal := fun ij => ENNReal.ofReal ((dist (a ij.1) (a ij.2)+2*δ)^p)
  have hcost : (∫⁻ z, ENNReal.ofReal ((dist z.1 z.2)^p) ∂μ) ≤ ∑' ij, w ij * C ij := by
    apply countableCellLift_cost_le_of_cellwise_bound Q Q' S S hS hS w hrow hcol x0 x0 _ C
    intro i j x y hx hy
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow dist_nonneg _ hp0.le
    exact isometry_cell_pair_distance f hf x y (a i) (a j) δ
      (hcenter i (f x) hx) (hcenter j (f y) hy)
  have hback : (∑' ij, w ij * C ij) ≤ ∫⁻ z, ENNReal.ofReal ((dist z.1 z.2+4*δ)^p) ∂π := by
    apply countable_rectangle_cost_sum_le π A A hm hm hdisj hdisj hcover hcover _ C
    intro i j x y hx hy
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (add_nonneg dist_nonneg (by positivity)) _ hp0.le
    have h := centered_cell_pair_distance x y (f (a i)) (f (a j)) δ
      (hcenter i x hx) (hcenter j y hy)
    rw [hf.dist_eq] at h
    exact h
  letI : IsProbabilityMeasure (Q.map f) := Q.isProbabilityMeasure_map hfm.aemeasurable
  letI : IsProbabilityMeasure π := coupling_probability_from_fst π (Q.map f) hπ.1
  have hshift := shifted_power_cost_root_le π (fun z : Z × Z => dist z.1 z.2)
    continuous_dist.measurable (fun _ => dist_nonneg) p hp (4*δ) (by positivity)
  refine ⟨μ,hμ,?_⟩
  exact (ENNReal.rpow_le_rpow (hcost.trans hback) (by positivity)).trans hshift

#print axioms dense_isometry_coupling_lift_root
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichIntegralApprox
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma restricted_integral_constant_error {E : Type*} [MeasurableSpace E]
    (Q : Measure E) [IsFiniteMeasure Q] (S : Set E) (hS : MeasurableSet S)
    (f : E → ℝ) (hf : Integrable f Q) (a : E) (C : ℝ)
    (h : ∀ x, x ∈ S → |f x-f a| ≤ C) :
    |(∫ x, f x ∂Q.restrict S) - f a * (Q S).toReal| ≤ C * (Q S).toReal := by
  have hae : ∀ᵐ x ∂Q.restrict S, ‖f x-f a‖ ≤ C := by
    apply (ae_restrict_mem hS).mono
    intro x hx
    simpa only [Real.norm_eq_abs] using h x hx
  have hb := norm_integral_le_of_norm_le_const hae
  rw [integral_sub hf.restrict (integrable_const (f a)),integral_const] at hb
  simpa only [Real.norm_eq_abs,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hb

lemma finite_partition_integral_error {E I : Type*} [MeasurableSpace E] [Fintype I]
    (Q : Measure E) [IsFiniteMeasure Q] (S : I → Set E) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hcover : (⋃ i, S i) = Set.univ)
    (f : E → ℝ) (hf : Integrable f Q) (a : I → E) (C : I → ℝ)
    (hc : ∀ i x, x ∈ S i → |f x-f (a i)| ≤ C i) :
    |(∫ x, f x ∂Q) - ∑ i, f (a i) * (Q (S i)).toReal| ≤ ∑ i, C i * (Q (S i)).toReal := by
  have hdecomp : (∫ x, f x ∂Q) = ∑ i, ∫ x, f x ∂Q.restrict (S i) := by
    calc
      (∫ x, f x ∂Q) = ∫ x, f x ∂(∑ i, Q.restrict (S i)) := by
        rw [finite_partition_restrict_sum Q S hS hd hcover]
      _ = _ := integral_finsetSum_measure (fun i _ => hf.restrict)
  rw [hdecomp,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum fun i _ => restricted_integral_constant_error Q (S i) (hS i) f hf
    (a i) (C i) (hc i)

lemma finite_indicator_error_sum {I : Type*} [Fintype I] [DecidableEq I]
    (B : Finset I) (α : I → ℝ) (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1)
    (η M : ℝ) (hη : 0 ≤ η) :
    (∑ i, (if i ∈ B then M else η) * α i) ≤ η + M * ∑ i ∈ B, α i := by
  classical
  calc
    (∑ i, (if i ∈ B then M else η) * α i) ≤
        ∑ i, (η * α i + M * (if i ∈ B then α i else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ B
      · simp only [if_pos hi]
        have := mul_nonneg hη (hα i)
        linarith
      · simp [hi]
    _ = η + M * ∑ i ∈ B, α i := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,hαsum,mul_one,Finset.sum_ite_mem_eq]

lemma finite_partition_integral_tail_error {E I : Type*} [MeasurableSpace E] [Fintype I]
    (Q : Measure E) [IsProbabilityMeasure Q] (S : I → Set E) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hcover : (⋃ i, S i) = Set.univ)
    (f : E → ℝ) (hf : Integrable f Q) (a : I → E) (B : Finset I) (η M : ℝ) (hη : 0 ≤ η)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hg : ∀ i, i ∉ B → ∀ x, x ∈ S i → |f x-f (a i)| ≤ η) :
    |(∫ x, f x ∂Q) - ∑ i, f (a i) * (Q (S i)).toReal| ≤
      η + M * ∑ i ∈ B, (Q (S i)).toReal := by
  classical
  have hc : ∀ i x, x ∈ S i → |f x-f (a i)| ≤ if i ∈ B then M else η := by
    intro i x hx
    by_cases hi : i ∈ B
    · rw [if_pos hi]
      apply abs_le.mpr
      have hfx := hb x
      have hfa := hb (a i)
      constructor <;> linarith
    · rw [if_neg hi]
      exact hg i hi x hx
  exact (finite_partition_integral_error Q S hS hd hcover f hf a _ hc).trans
    (finite_indicator_error_sum B (fun i => (Q (S i)).toReal) (fun _ => ENNReal.toReal_nonneg)
      (finite_partition_real_mass_sum_one Q S hS hd hcover) η M hη)

#print axioms restricted_integral_constant_error
#print axioms finite_partition_integral_error
#print axioms finite_indicator_error_sum
#print axioms finite_partition_integral_tail_error
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichPairErrors
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

def badPairIndices {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J) : Finset (I × J) := Finset.univ.filter (fun ij => ij.1 = i0 ∨ ij.2 = j0)

lemma finite_bad_pair_mass_le {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (w : I × J → ℝ) (hw : ∀ ij, 0 ≤ w ij) (i0 : I) (j0 : J) :
    (∑ ij ∈ badPairIndices i0 j0, w ij) ≤ (∑ j, w (i0,j)) + ∑ i, w (i,j0) := by
  classical
  unfold badPairIndices
  rw [Finset.sum_filter]
  calc
    (∑ ij, if ij.1 = i0 ∨ ij.2 = j0 then w ij else 0) ≤
        ∑ ij, ((if ij.1 = i0 then w ij else 0) + (if ij.2 = j0 then w ij else 0)) := by
      apply Finset.sum_le_sum
      intro ij _
      by_cases hi : ij.1 = i0 <;> by_cases hj : ij.2 = j0
      · simp only [hi,hj,or_self,if_true]
        have := hw ij
        linarith
      · simp [hi,hj]
      · simp [hi,hj]
      · simp [hi,hj]
    _ = (∑ j, w (i0,j)) + ∑ i, w (i,j0) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Fintype.sum_prod_type,Finset.sum_comm]
        simp
      · rw [Fintype.sum_prod_type]
        simp

lemma finite_pair_error_sum_le {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (w : I × J → ℝ) (hw : ∀ ij, 0 ≤ w ij) (hsum : ∑ ij, w ij = 1)
    (i0 : I) (j0 : J) (η M : ℝ) (hη : 0 ≤ η) (hM : 0 ≤ M) :
    (∑ ij, (if ij ∈ badPairIndices i0 j0 then M else η) * w ij) ≤
      η + M * ((∑ j, w (i0,j)) + ∑ i, w (i,j0)) := by
  exact (finite_indicator_error_sum (badPairIndices i0 j0) w hw hsum η M hη).trans
    (add_le_add (le_refl η) (mul_le_mul_of_nonneg_left (finite_bad_pair_mass_le w hw i0 j0) hM))

#print axioms finite_bad_pair_mass_le
#print axioms finite_pair_error_sum_le
lemma bounded_pair_integral_objective_error {E I J : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] [Fintype I] [Fintype J]
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (S : I → Set E) (T : J → Set E) (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (fun i k => Disjoint (S i) (S k)))
    (hdT : Pairwise (fun j k => Disjoint (T j) (T k)))
    (hcoverS : (⋃ i, S i) = Set.univ) (hcoverT : (⋃ j, T j) = Set.univ)
    (a : I → E) (b : J → E) (i0 : I) (j0 : J)
    (Φ Ψ : BoundedContinuousFunction E ℝ) (η M : ℝ) (hη : 0 ≤ η)
    (hΦ : ∀ x, 0 ≤ Φ x ∧ Φ x ≤ M) (hΨ : ∀ x, 0 ≤ Ψ x ∧ Ψ x ≤ M)
    (hgΦ : ∀ i, i ≠ i0 → ∀ x, x ∈ S i → |Φ x-Φ (a i)| ≤ η)
    (hgΨ : ∀ j, j ≠ j0 → ∀ x, x ∈ T j → |Ψ x-Ψ (b j)| ≤ η) :
    |((∫ x, Ψ x ∂Q') - ∫ x, Φ x ∂Q) -
      ((∑ j, Ψ (b j) * (Q' (T j)).toReal) - ∑ i, Φ (a i) * (Q (S i)).toReal)| ≤
        2 * η + M * ((Q (S i0)).toReal + (Q' (T j0)).toReal) := by
  classical
  have heΦ := finite_partition_integral_tail_error Q S hS hdS hcoverS Φ
    (Φ.integrable (μ := Q)) a {i0} η M hη hΦ (by
      intro i hi x hx
      exact hgΦ i (by simpa using hi) x hx)
  have heΨ := finite_partition_integral_tail_error Q' T hT hdT hcoverT Ψ
    (Ψ.integrable (μ := Q')) b {j0} η M hη hΨ (by
      intro j hj x hx
      exact hgΨ j (by simpa using hj) x hx)
  simp only [Finset.sum_singleton] at heΦ heΨ
  have ha := abs_le.mp heΦ
  have hb := abs_le.mp heΨ
  apply abs_le.mpr
  constructor <;> nlinarith

#print axioms bounded_pair_integral_objective_error
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichLiftApprox
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma finiteCellLift_cost_le_matrix_plus_tail {E F I J : Type*}
    [MeasurableSpace E] [MeasurableSpace F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (Q : Measure E) (Q' : Measure F) [IsFiniteMeasure Q] [IsFiniteMeasure Q']
    (S : I → Set E) (T : J → Set F) (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (w : I × J → ℝ) (hw : ∀ ij, 0 ≤ w ij) (hsum : ∑ ij, w ij = 1)
    (hrow : ∀ i, ∑ j, w (i,j) = (Q (S i)).toReal)
    (hcol : ∀ j, ∑ i, w (i,j) = (Q' (T j)).toReal)
    (x0 : E) (y0 : F) (i0 : I) (j0 : J) (c : I × J → ℝ) (hc0 : ∀ ij, 0 ≤ c ij)
    (η M : ℝ) (hη : 0 ≤ η) (hM : 0 ≤ M) (f : E × F → ENNReal)
    (hcell : ∀ i j x y, x ∈ S i → y ∈ T j →
      f (x,y) ≤ ENNReal.ofReal (c (i,j) + if (i,j) ∈ badPairIndices i0 j0 then M else η)) :
    (∫⁻ z, f z ∂finiteCellLift Q Q' S T (fun ij => ENNReal.ofReal (w ij)) x0 y0) ≤
      ENNReal.ofReal ((∑ ij, c ij * w ij) + η + M * ((Q (S i0)).toReal + (Q' (T j0)).toReal)) := by
  classical
  let C : I × J → ℝ := fun ij => c ij + if ij ∈ badPairIndices i0 j0 then M else η
  have hC : ∀ ij, 0 ≤ C ij := by
    intro ij
    apply add_nonneg (hc0 ij)
    split_ifs
    · exact hM
    · exact hη
  have hrowNN : ∀ i, ∑ j, ENNReal.ofReal (w (i,j)) = Q (S i) := by
    intro i
    exact finite_ofReal_sum_eq_mass (fun j => w (i,j)) (fun j => hw (i,j))
      (Q (S i)) (measure_ne_top Q (S i)) (hrow i)
  have hcolNN : ∀ j, ∑ i, ENNReal.ofReal (w (i,j)) = Q' (T j) := by
    intro j
    exact finite_ofReal_sum_eq_mass (fun i => w (i,j)) (fun i => hw (i,j))
      (Q' (T j)) (measure_ne_top Q' (T j)) (hcol j)
  have hbound := finiteCellLift_cost_le_of_cellwise_bound Q Q' S T hS hT
    (fun ij => ENNReal.ofReal (w ij)) hrowNN hcolNN x0 y0 f (fun ij => ENNReal.ofReal (C ij)) hcell
  have hNN : (∑ ij, ENNReal.ofReal (w ij) * ENNReal.ofReal (C ij)) =
      ENNReal.ofReal (∑ ij, w ij * C ij) := by
    rw [ENNReal.ofReal_sum_of_nonneg (f := fun ij => w ij * C ij)
      (fun ij _ => mul_nonneg (hw ij) (hC ij))]
    apply Finset.sum_congr rfl
    intro ij _
    exact (ENNReal.ofReal_mul (hw ij)).symm
  have he := finite_pair_error_sum_le w hw hsum i0 j0 η M hη hM
  rw [hrow i0,hcol j0] at he
  have hR : (∑ ij, w ij * C ij) ≤ (∑ ij, c ij * w ij) + η +
      M * ((Q (S i0)).toReal + (Q' (T j0)).toReal) := by
    calc
      (∑ ij, w ij * C ij) = (∑ ij, c ij * w ij) +
          ∑ ij, (if ij ∈ badPairIndices i0 j0 then M else η) * w ij := by
        simp only [C,mul_add,mul_comm,Finset.sum_add_distrib]
      _ ≤ (∑ ij, c ij * w ij) +
          (η + M * ((Q (S i0)).toReal + (Q' (T j0)).toReal)) := add_le_add le_rfl he
      _ = _ := by ring
  rw [hNN] at hbound
  exact hbound.trans (ENNReal.ofReal_le_ofReal hR)

#print axioms finiteCellLift_cost_le_matrix_plus_tail
noncomputable def couplingCostInf {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (Q : Measure E) (Q' : Measure F) (f : E × F → ENNReal) : ENNReal :=
  ⨅ (π : Measure (E × F)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q'), ∫⁻ z, f z ∂π

lemma couplingCostInf_le_matrix_plus_tail {E F I J : Type*}
    [MeasurableSpace E] [MeasurableSpace F] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (Q : Measure E) (Q' : Measure F) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (S : I → Set E) (T : J → Set F) (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (fun i k => Disjoint (S i) (S k)))
    (hdT : Pairwise (fun j k => Disjoint (T j) (T k)))
    (hcoverS : (⋃ i, S i) = Set.univ) (hcoverT : (⋃ j, T j) = Set.univ)
    (w : I × J → ℝ) (hw : ∀ ij, 0 ≤ w ij) (hsum : ∑ ij, w ij = 1)
    (hrow : ∀ i, ∑ j, w (i,j) = (Q (S i)).toReal)
    (hcol : ∀ j, ∑ i, w (i,j) = (Q' (T j)).toReal)
    (x0 : E) (y0 : F) (i0 : I) (j0 : J) (c : I × J → ℝ) (hc0 : ∀ ij, 0 ≤ c ij)
    (η M : ℝ) (hη : 0 ≤ η) (hM : 0 ≤ M) (f : E × F → ENNReal)
    (hcell : ∀ i j x y, x ∈ S i → y ∈ T j →
      f (x,y) ≤ ENNReal.ofReal (c (i,j) + if (i,j) ∈ badPairIndices i0 j0 then M else η)) :
    couplingCostInf Q Q' f ≤
      ENNReal.ofReal ((∑ ij, c ij * w ij) + η + M * ((Q (S i0)).toReal + (Q' (T j0)).toReal)) := by
  have hm := real_matrix_cell_lift_marginals Q Q' S T hS hT hdS hdT hcoverS hcoverT w hw hrow hcol x0 y0
  have hl := finiteCellLift_cost_le_matrix_plus_tail Q Q' S T hS hT w hw hsum hrow hcol
    x0 y0 i0 j0 c hc0 η M hη hM f hcell
  unfold couplingCostInf
  exact (iInf_le_of_le (finiteCellLift Q Q' S T (fun ij => ENNReal.ofReal (w ij)) x0 y0)
    (iInf_le_of_le hm le_rfl)).trans hl

#print axioms couplingCostInf_le_matrix_plus_tail
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichDenseInf
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma dense_isometry_cost_inf_le {E Z : Type*} [PseudoMetricSpace E] [PseudoMetricSpace Z]
    [MeasurableSpace E] [MeasurableSpace Z] [BorelSpace E] [BorelSpace Z]
    [SecondCountableTopology E] [SecondCountableTopology Z]
    (f : E → Z) (hf : Isometry f) (hfm : Measurable f) (hfd : DenseRange f)
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (p : ℝ) (hp : 1 ≤ p) (x0 : E) :
    couplingCostInf Q Q' (fun z => ENNReal.ofReal ((dist z.1 z.2)^p)) ≤
      couplingCostInf (Q.map f) (Q'.map f) (fun z => ENNReal.ofReal ((dist z.1 z.2)^p)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  refine le_iInf fun π => le_iInf fun hπ => ?_
  have hroot : (couplingCostInf Q Q' (fun z => ENNReal.ofReal ((dist z.1 z.2)^p))) ^ (1/p) ≤
      (∫⁻ z, ENNReal.ofReal ((dist z.1 z.2)^p) ∂π) ^ (1/p) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨μ,hμ,hr⟩ := dense_isometry_coupling_lift_root f hf hfm hfd Q Q' π hπ p hp
      ((ε : ℝ)/4) (by positivity) x0
    have hi : couplingCostInf Q Q' (fun z => ENNReal.ofReal ((dist z.1 z.2)^p)) ≤
        ∫⁻ z, ENNReal.ofReal ((dist z.1 z.2)^p) ∂μ :=
      iInf_le_of_le μ (iInf_le_of_le hμ le_rfl)
    have h := (ENNReal.rpow_le_rpow hi (by positivity)).trans hr
    have he : ENNReal.ofReal (4*((ε : ℝ)/4)) = (ε : ENNReal) := by
      rw [show 4*((ε : ℝ)/4) = (ε : ℝ) by ring,ENNReal.ofReal_coe_nnreal]
    rwa [he] at h
  have h := ENNReal.rpow_le_rpow hroot hp0.le
  simpa only [← ENNReal.rpow_mul,one_div_mul_cancel hp0.ne',ENNReal.rpow_one] using h

#print axioms dense_isometry_cost_inf_le
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichFiniteSeparation
set_option autoImplicit false
open scoped Pointwise
namespace DualityCodex

lemma functional_product_decomposition {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : (V × ℝ) →L[ℝ] ℝ) (x : V) (t : ℝ) :
    f (x,t) = (f.comp (ContinuousLinearMap.inl ℝ V ℝ)) x + f (0,1) * t := by
  have he : (x,t) = (x,0) + t • (0,1) := by ext <;> simp
  rw [he,map_add,map_smul]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,smul_eq_mul]
  ring

lemma compact_cost_gap_separation {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : Set (V × ℝ)) (hK : Convex ℝ K) (hcompact : IsCompact K)
    (u : V) (r c : ℝ) (hbase : (u,c) ∈ K)
    (hgap : ∀ z ∈ K, z.1 = u → r < z.2) :
    ∃ (a : V →L[ℝ] ℝ) (γ κ : ℝ), 0 < γ ∧ a u + γ * r < κ ∧
      ∀ z ∈ K, κ ≤ a z.1 + γ * z.2 := by
  have hnot : (u,r) ∉ K := by
    intro h
    have := hgap (u,r) h rfl
    exact (lt_irrefl r) this
  obtain ⟨f,κ,htarget,hsep⟩ := geometric_hahn_banach_point_closed hK hcompact.isClosed hnot
  let a : V →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ V ℝ)
  let γ : ℝ := f (0,1)
  have hdecomp (x : V) (t : ℝ) : f (x,t) = a x + γ * t :=
    functional_product_decomposition f x t
  have hc : r < c := hgap (u,c) hbase rfl
  have hb := hsep (u,c) hbase
  rw [hdecomp] at htarget hb
  have hγ : 0 < γ := by
    by_contra h
    have hn : γ ≤ 0 := le_of_not_gt h
    have hp : γ * (c-r) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn (sub_nonneg.mpr hc.le)
    nlinarith
  refine ⟨a,γ,κ,hγ,htarget,?_⟩
  intro z hz
  have hb := hsep z hz
  rw [show z = (z.1,z.2) from Prod.eta z, hdecomp] at hb
  exact hb.le

#print axioms functional_product_decomposition
#print axioms compact_cost_gap_separation
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichFiniteTransport
set_option autoImplicit false
open scoped BigOperators
namespace DualityCodex

noncomputable def finiteTransportMap {I J : Type*} [Fintype I] [Fintype J]
    (c : I × J → ℝ) : (I × J → ℝ) →ₗ[ℝ] ((I → ℝ) × (J → ℝ)) × ℝ where
  toFun w := ((fun i => ∑ j, w (i,j), fun j => ∑ i, w (i,j)), ∑ k, w k * c k)
  map_add' := by
    intro w v
    ext <;> simp [Finset.sum_add_distrib,add_mul]
  map_smul' := by
    intro a w
    ext <;> simp [Finset.mul_sum,mul_assoc]

lemma product_weights_simplex {I J : Type*} [Fintype I] [Fintype J]
    (α : I → ℝ) (β : J → ℝ) (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    (hαsum : ∑ i, α i = 1) (hβsum : ∑ j, β j = 1) :
    (fun k : I × J => α k.1 * β k.2) ∈ stdSimplex ℝ (I × J) := by
  constructor
  · intro k
    exact mul_nonneg (hα k.1) (hβ k.2)
  · simp only [Fintype.sum_prod_type, ← Finset.mul_sum,hβsum,mul_one,hαsum]

lemma product_weights_marginals {I J : Type*} [Fintype I] [Fintype J]
    (c : I × J → ℝ) (α : I → ℝ) (β : J → ℝ)
    (hαsum : ∑ i, α i = 1) (hβsum : ∑ j, β j = 1) :
    (finiteTransportMap c (fun k => α k.1 * β k.2)).1 = (α,β) := by
  ext <;> simp [finiteTransportMap,← Finset.mul_sum,← Finset.sum_mul,hαsum,hβsum]

lemma finite_transport_image_compact {I J : Type*} [Fintype I] [Fintype J]
    (c : I × J → ℝ) :
    IsCompact (finiteTransportMap c '' stdSimplex ℝ (I × J)) :=
  (isCompact_stdSimplex ℝ (I × J)).image (finiteTransportMap c).continuous_of_finiteDimensional

lemma finite_transport_image_convex {I J : Type*} [Fintype I] [Fintype J]
    (c : I × J → ℝ) :
    Convex ℝ (finiteTransportMap c '' stdSimplex ℝ (I × J)) :=
  (convex_stdSimplex ℝ (I × J)).linear_image (finiteTransportMap c)

#print axioms product_weights_simplex
#print axioms product_weights_marginals
#print axioms finite_transport_image_compact
#print axioms finite_transport_image_convex
lemma finite_transport_map_single {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (c : I × J → ℝ) (i : I) (j : J) :
    finiteTransportMap c (Pi.single (i,j) 1) = ((Pi.single i 1,Pi.single j 1),c (i,j)) := by
  classical
  ext <;> simp [finiteTransportMap,Pi.single_apply,Fintype.sum_prod_type,Prod.mk.injEq,ite_and]

lemma finite_transport_gap_separation {I J : Type*} [Fintype I] [Fintype J]
    (c : I × J → ℝ) (α : I → ℝ) (β : J → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    (hαsum : ∑ i, α i = 1) (hβsum : ∑ j, β j = 1) (r : ℝ)
    (hgap : ∀ w ∈ stdSimplex ℝ (I × J), (finiteTransportMap c w).1 = (α,β) →
      r < (finiteTransportMap c w).2) :
    ∃ (a : ((I → ℝ) × (J → ℝ)) →L[ℝ] ℝ) (γ κ : ℝ), 0 < γ ∧
      a (α,β) + γ * r < κ ∧ ∀ w ∈ stdSimplex ℝ (I × J),
        κ ≤ a (finiteTransportMap c w).1 + γ * (finiteTransportMap c w).2 := by
  let w0 : I × J → ℝ := fun k => α k.1 * β k.2
  have hw0 : w0 ∈ stdSimplex ℝ (I × J) := product_weights_simplex α β hα hβ hαsum hβsum
  have hm : (finiteTransportMap c w0).1 = (α,β) := product_weights_marginals c α β hαsum hβsum
  have hbase : ((α,β),(finiteTransportMap c w0).2) ∈
      finiteTransportMap c '' stdSimplex ℝ (I × J) := by
    refine ⟨w0,hw0,?_⟩
    exact Prod.ext hm rfl
  obtain ⟨a,γ,κ,hγ,ht,hK⟩ := compact_cost_gap_separation
    (finiteTransportMap c '' stdSimplex ℝ (I × J))
    (finite_transport_image_convex c) (finite_transport_image_compact c)
    (α,β) r (finiteTransportMap c w0).2 hbase (by
      rintro z ⟨w,hw,rfl⟩ heq
      exact hgap w hw heq)
  exact ⟨a,γ,κ,hγ,ht,fun w hw => hK _ ⟨w,hw,rfl⟩⟩

#print axioms finite_transport_map_single
#print axioms finite_transport_gap_separation
lemma finite_marginal_functional_expansion {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (a : ((I → ℝ) × (J → ℝ)) →L[ℝ] ℝ) (α : I → ℝ) (β : J → ℝ) :
    a (α,β) = (∑ i, α i * a (Pi.single i 1,0)) +
      ∑ j, β j * a (0,Pi.single j 1) := by
  have he : (α,β) = (∑ i, α i • (Pi.single i 1, (0 : J → ℝ))) +
      ∑ j, β j • ((0 : I → ℝ),Pi.single j 1) := by
    ext <;> simp [Prod.fst_sum,Prod.snd_sum,Finset.sum_apply,Pi.single_apply]
  rw [he,map_add,map_sum,map_sum]
  simp only [map_smul,smul_eq_mul]

lemma finite_transport_dual_gap {I J : Type*} [Fintype I] [Fintype J]
    (c : I × J → ℝ) (α : I → ℝ) (β : J → ℝ)
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    (hαsum : ∑ i, α i = 1) (hβsum : ∑ j, β j = 1) (r : ℝ)
    (hgap : ∀ w ∈ stdSimplex ℝ (I × J), (finiteTransportMap c w).1 = (α,β) →
      r < (finiteTransportMap c w).2) :
    ∃ (φ : I → ℝ) (ψ : J → ℝ), (∀ i j, ψ j - φ i ≤ c (i,j)) ∧
      r < (∑ j, ψ j * β j) - ∑ i, φ i * α i := by
  classical
  obtain ⟨a,γ,κ,hγ,ht,hK⟩ := finite_transport_gap_separation c α β hα hβ hαsum hβsum r hgap
  let u : I → ℝ := fun i => a (Pi.single i 1,0)
  let v : J → ℝ := fun j => a (0,Pi.single j 1)
  let φ : I → ℝ := fun i => (u i - κ) / γ
  let ψ : J → ℝ := fun j => -v j / γ
  have ha : a (α,β) = (∑ i, u i * α i) + ∑ j, v j * β j := by
    simpa only [u,v,mul_comm] using finite_marginal_functional_expansion a α β
  refine ⟨φ,ψ,?_,?_⟩
  · intro i j
    have hb := hK (Pi.single (i,j) 1) (single_mem_stdSimplex ℝ (i,j))
    rw [finite_transport_map_single] at hb
    have he : a (Pi.single i 1,Pi.single j 1) = u i + v j := by
      rw [show (Pi.single i 1,Pi.single j 1) =
        (Pi.single i 1,(0 : J → ℝ)) + ((0 : I → ℝ),Pi.single j 1) by ext <;> simp,map_add]
    rw [he] at hb
    dsimp only [φ,ψ]
    rw [← sub_div]
    apply (div_le_iff₀ hγ).mpr
    nlinarith
  · have ho : (∑ j, ψ j * β j) - ∑ i, φ i * α i = (κ-a (α,β)) / γ := by
      simp only [φ,ψ,div_mul_eq_mul_div,← Finset.sum_div,sub_mul,
        Finset.sum_sub_distrib,← Finset.mul_sum,hαsum,mul_one,neg_mul,Finset.sum_neg_distrib]
      rw [ha]
      ring
    rw [ho]
    apply (lt_div_iff₀ hγ).mpr
    linarith

#print axioms finite_marginal_functional_expansion
#print axioms finite_transport_dual_gap
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichNormalize
set_option autoImplicit false
open scoped BigOperators
namespace DualityCodex

lemma finite_c_transform_bounds {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (c : I × J → ℝ) (M : ℝ) (hc0 : ∀ i j, 0 ≤ c (i,j)) (hcM : ∀ i j, c (i,j) ≤ M)
    (φ : I → ℝ) (ψ : J → ℝ) (hc : ∀ i j, ψ j - φ i ≤ c (i,j)) :
    ∃ (A : I → ℝ) (B : J → ℝ) (L : ℝ),
      (∀ i, A i ≤ φ i) ∧ (∀ j, ψ j ≤ B j) ∧
      (∀ i j, B j - A i ≤ c (i,j)) ∧ (∀ i, L - M ≤ A i ∧ A i ≤ L) := by
  let B : J → ℝ := fun j => ⨅ i, φ i + c (i,j)
  let A : I → ℝ := fun i => ⨆ j, B j - c (i,j)
  let L : ℝ := ⨆ j, B j
  have hB (i : I) (j : J) : B j ≤ φ i + c (i,j) :=
    ciInf_le (Set.finite_range (fun i => φ i + c (i,j))).bddBelow i
  have hA (i : I) (j : J) : B j - c (i,j) ≤ A i :=
    le_ciSup (Set.finite_range (fun j => B j - c (i,j))).bddAbove j
  have hBL (j : J) : B j ≤ L := le_ciSup (Set.finite_range B).bddAbove j
  refine ⟨A,B,L,?_,?_,?_,?_⟩
  · intro i
    apply ciSup_le
    intro j
    have := hB i j
    linarith
  · intro j
    apply le_ciInf
    intro i
    have := hc i j
    linarith
  · intro i j
    have := hA i j
    linarith
  · intro i
    have hupper : A i ≤ L := by
      apply ciSup_le
      intro j
      have := hBL j
      have := hc0 i j
      linarith
    have hlower : L ≤ A i + M := by
      apply ciSup_le
      intro j
      have := hA i j
      have := hcM i j
      linarith
    exact ⟨by linarith,hupper⟩

lemma finite_potential_objective_mono {I J : Type*} [Fintype I] [Fintype J]
    (α : I → ℝ) (β : J → ℝ) (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    (φ A : I → ℝ) (ψ B : J → ℝ) (hA : ∀ i, A i ≤ φ i) (hB : ∀ j, ψ j ≤ B j) :
    (∑ j, ψ j * β j) - ∑ i, φ i * α i ≤ (∑ j, B j * β j) - ∑ i, A i * α i := by
  apply sub_le_sub
  · exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hB j) (hβ j)
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hA i) (hα i)

lemma bounded_finite_potential_normalization {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J]
    (c : I × J → ℝ) (M : ℝ) (hc0 : ∀ i j, 0 ≤ c (i,j)) (hcM : ∀ i j, c (i,j) ≤ M)
    (α : I → ℝ) (β : J → ℝ) (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    (hαsum : ∑ i, α i = 1) (hβsum : ∑ j, β j = 1)
    (φ : I → ℝ) (ψ : J → ℝ) (hc : ∀ i j, ψ j - φ i ≤ c (i,j)) :
    ∃ (φ' : I → ℝ) (ψ' : J → ℝ), (∀ i, 0 ≤ φ' i ∧ φ' i ≤ M) ∧
      (∀ j, 0 ≤ ψ' j ∧ ψ' j ≤ M) ∧ (∃ i, φ' i = 0) ∧
      (∀ i j, ψ' j - φ' i ≤ c (i,j)) ∧
      (∑ j, ψ j * β j) - ∑ i, φ i * α i ≤
        (∑ j, ψ' j * β j) - ∑ i, φ' i * α i := by
  classical
  obtain ⟨A,B,L,hA,hB,hcAB,hAL⟩ := finite_c_transform_bounds c M hc0 hcM φ ψ hc
  obtain ⟨i0,_,hmin⟩ := Finset.exists_min_image Finset.univ A Finset.univ_nonempty
  let s : ℝ := A i0
  let φ' : I → ℝ := fun i => A i - s
  let ψ' : J → ℝ := fun j => ⨅ i, φ' i + c (i,j)
  have hφ' (i : I) : 0 ≤ φ' i ∧ φ' i ≤ M := by
    have hm := hmin i (Finset.mem_univ i)
    have hi := hAL i
    have hs := hAL i0
    dsimp [φ',s]
    constructor <;> linarith
  have hi0 : φ' i0 = 0 := by simp [φ',s]
  have hψupper (i : I) (j : J) : ψ' j ≤ φ' i + c (i,j) :=
    ciInf_le (Set.finite_range (fun i => φ' i + c (i,j))).bddBelow i
  have hψ' (j : J) : 0 ≤ ψ' j ∧ ψ' j ≤ M := by
    constructor
    · apply le_ciInf
      intro i
      exact add_nonneg (hφ' i).1 (hc0 i j)
    · have := hψupper i0 j
      rw [hi0,zero_add] at this
      exact this.trans (hcM i0 j)
  have hBshift (j : J) : B j - s ≤ ψ' j := by
    apply le_ciInf
    intro i
    have := hcAB i j
    dsimp only [φ']
    linarith
  have himprove := finite_potential_objective_mono α β hα hβ φ A ψ B hA hB
  have hshift : (∑ j, (B j-s) * β j) - ∑ i, φ' i * α i =
      (∑ j, B j * β j) - ∑ i, A i * α i := by
    simp only [φ',sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum,hαsum,hβsum,mul_one]
    ring
  have hfinal : (∑ j, (B j-s) * β j) - ∑ i, φ' i * α i ≤
      (∑ j, ψ' j * β j) - ∑ i, φ' i * α i := by
    apply sub_le_sub_right
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hBshift j) (hβ j)
  refine ⟨φ',ψ',hφ',hψ',⟨i0,hi0⟩,?_,?_⟩
  · intro i j
    have := hψupper i j
    linarith
  · rw [hshift] at hfinal
    exact himprove.trans hfinal

#print axioms finite_c_transform_bounds
#print axioms finite_potential_objective_mono
#print axioms bounded_finite_potential_normalization
lemma bounded_finite_transport_dual_gap {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J]
    (c : I × J → ℝ) (M : ℝ) (hc0 : ∀ i j, 0 ≤ c (i,j)) (hcM : ∀ i j, c (i,j) ≤ M)
    (α : I → ℝ) (β : J → ℝ) (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    (hαsum : ∑ i, α i = 1) (hβsum : ∑ j, β j = 1) (r : ℝ)
    (hgap : ∀ w ∈ stdSimplex ℝ (I × J), (finiteTransportMap c w).1 = (α,β) →
      r < (finiteTransportMap c w).2) :
    ∃ (φ : I → ℝ) (ψ : J → ℝ), (∀ i, 0 ≤ φ i ∧ φ i ≤ M) ∧
      (∀ j, 0 ≤ ψ j ∧ ψ j ≤ M) ∧ (∃ i, φ i = 0) ∧
      (∀ i j, ψ j - φ i ≤ c (i,j)) ∧
      r < (∑ j, ψ j * β j) - ∑ i, φ i * α i := by
  obtain ⟨φ,ψ,hc,hr⟩ := finite_transport_dual_gap c α β hα hβ hαsum hβsum r hgap
  obtain ⟨φ',ψ',hφ',hψ',hzero,hc',hobj⟩ :=
    bounded_finite_potential_normalization c M hc0 hcM α β hα hβ hαsum hβsum φ ψ hc
  exact ⟨φ',ψ',hφ',hψ',hzero,hc',hr.trans_le hobj⟩

#print axioms bounded_finite_transport_dual_gap
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichExtend
set_option autoImplicit false
open scoped BigOperators
namespace DualityCodex

lemma finite_ciInf_attained {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) :
    ∃ i, (⨅ j, f j) = f i := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨i,le_antisymm (ciInf_le (Set.finite_range f).bddBelow i) ?_⟩
  exact le_ciInf fun j => hi j (Finset.mem_univ j)

lemma finite_ciInf_abs_sub_le {I : Type*} [Fintype I] [Nonempty I]
    (f g : I → ℝ) (η : ℝ) (h : ∀ i, |f i-g i| ≤ η) :
    |(⨅ i, f i) - (⨅ i, g i)| ≤ η := by
  obtain ⟨i,hi⟩ := finite_ciInf_attained f
  obtain ⟨j,hj⟩ := finite_ciInf_attained g
  have hf := ciInf_le (Set.finite_range f).bddBelow j
  have hg := ciInf_le (Set.finite_range g).bddBelow i
  rw [hi] at hf
  rw [hj] at hg
  have hbi := abs_le.mp (h i)
  have hbj := abs_le.mp (h j)
  rw [hi,hj]
  apply abs_le.mpr
  constructor <;> linarith

lemma bounded_ciSup_abs_sub_le {X : Type*} [Nonempty X]
    (f g : X → ℝ) (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g))
    (η : ℝ) (h : ∀ x, |f x-g x| ≤ η) :
    |(⨆ x, f x) - (⨆ x, g x)| ≤ η := by
  have hfg : (⨆ x, f x) ≤ (⨆ x, g x) + η := by
    apply ciSup_le
    intro x
    have := le_ciSup hg x
    have := (abs_le.mp (h x)).2
    linarith
  have hgf : (⨆ x, g x) ≤ (⨆ x, f x) + η := by
    apply ciSup_le
    intro x
    have := le_ciSup hf x
    have := (abs_le.mp (h x)).1
    linarith
  apply abs_le.mpr
  constructor <;> linarith

noncomputable def finiteCostSelling {E I : Type*} [Fintype I]
    (k : E × E → ℝ) (a : I → E) (φ : I → ℝ) (x : E) : ℝ :=
  ⨅ i, φ i + k (x,a i)

noncomputable def finiteCostBuying {E I : Type*} [Fintype I]
    (k : E × E → ℝ) (a : I → E) (φ : I → ℝ) (y : E) : ℝ :=
  ⨆ x, finiteCostSelling k a φ x - k (x,y)

lemma finite_selling_bounds {E I : Type*} [Fintype I] [Nonempty I]
    (k : E × E → ℝ) (a : I → E) (φ : I → ℝ) (M : ℝ)
    (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M)
    (hφ0 : ∀ i, 0 ≤ φ i) (hzero : ∃ i, φ i = 0) (x : E) :
    0 ≤ finiteCostSelling k a φ x ∧ finiteCostSelling k a φ x ≤ M := by
  constructor
  · exact le_ciInf fun i => add_nonneg (hφ0 i) (hk0 x (a i))
  · obtain ⟨i,hi⟩ := hzero
    have h := ciInf_le (Set.finite_range (fun i => φ i + k (x,a i))).bddBelow i
    rw [hi,zero_add] at h
    exact h.trans (hkM x (a i))

lemma finite_buying_scores_bddAbove {E I : Type*} [Fintype I] [Nonempty I]
    (k : E × E → ℝ) (a : I → E) (φ : I → ℝ) (M : ℝ)
    (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M)
    (hφ0 : ∀ i, 0 ≤ φ i) (hzero : ∃ i, φ i = 0) (y : E) :
    BddAbove (Set.range (fun x => finiteCostSelling k a φ x - k (x,y))) := by
  refine ⟨M,?_⟩
  rintro _ ⟨x,rfl⟩
  have := (finite_selling_bounds k a φ M hk0 hkM hφ0 hzero x).2
  have := hk0 x y
  linarith

lemma finite_buying_bounds {E I : Type*} [Nonempty E] [Fintype I] [Nonempty I]
    (k : E × E → ℝ) (a : I → E) (φ : I → ℝ) (M : ℝ)
    (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M)
    (hdiag : ∀ x, k (x,x) = 0)
    (hφ0 : ∀ i, 0 ≤ φ i) (hzero : ∃ i, φ i = 0) (y : E) :
    0 ≤ finiteCostBuying k a φ y ∧ finiteCostBuying k a φ y ≤ M := by
  constructor
  · have h := le_ciSup (finite_buying_scores_bddAbove k a φ M hk0 hkM hφ0 hzero y) y
    rw [hdiag y,sub_zero] at h
    exact (finite_selling_bounds k a φ M hk0 hkM hφ0 hzero y).1.trans h
  · apply ciSup_le
    intro x
    have := (finite_selling_bounds k a φ M hk0 hkM hφ0 hzero x).2
    have := hk0 x y
    linarith

lemma finite_extended_pair_feasible {E I : Type*} [Fintype I] [Nonempty I]
    (k : E × E → ℝ) (a : I → E) (φ : I → ℝ) (M : ℝ)
    (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M)
    (hφ0 : ∀ i, 0 ≤ φ i) (hzero : ∃ i, φ i = 0) (x y : E) :
    finiteCostSelling k a φ x - finiteCostBuying k a φ y ≤ k (x,y) := by
  have h := le_ciSup (finite_buying_scores_bddAbove k a φ M hk0 hkM hφ0 hzero y) x
  change finiteCostSelling k a φ x - k (x,y) ≤ finiteCostBuying k a φ y at h
  linarith

lemma finite_buying_at_center_le {E I : Type*} [Nonempty E] [Fintype I] [Nonempty I]
    (k : E × E → ℝ) (a : I → E) (φ : I → ℝ) (i : I) :
    finiteCostBuying k a φ (a i) ≤ φ i := by
  apply ciSup_le
  intro x
  have h := ciInf_le (Set.finite_range (fun j => φ j + k (x,a j))).bddBelow i
  change finiteCostSelling k a φ x ≤ φ i + k (x,a i) at h
  linarith

lemma finite_selling_at_destination_ge {E I J : Type*} [Fintype I] [Nonempty I]
    (k : E × E → ℝ) (a : I → E) (b : J → E) (φ : I → ℝ) (ψ : J → ℝ)
    (hc : ∀ i j, ψ j - φ i ≤ k (b j,a i)) (j : J) :
    ψ j ≤ finiteCostSelling k a φ (b j) := by
  apply le_ciInf
  intro i
  have := hc i j
  linarith

#print axioms finite_ciInf_attained
#print axioms finite_ciInf_abs_sub_le
#print axioms bounded_ciSup_abs_sub_le
#print axioms finite_selling_bounds
#print axioms finite_buying_scores_bddAbove
#print axioms finite_buying_bounds
#print axioms finite_extended_pair_feasible
#print axioms finite_buying_at_center_le
#print axioms finite_selling_at_destination_ge
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichExtendUniform
set_option autoImplicit false
namespace DualityCodex

lemma finite_selling_cost_oscillation {E I : Type*} [Fintype I] [Nonempty I]
    (k : E × E → ℝ) (a : I → E) (φ : I → ℝ) (x z : E) (η : ℝ)
    (h : ∀ y, |k (x,y)-k (z,y)| ≤ η) :
    |finiteCostSelling k a φ x - finiteCostSelling k a φ z| ≤ η := by
  apply finite_ciInf_abs_sub_le
  intro i
  have he : φ i + k (x,a i) - (φ i + k (z,a i)) = k (x,a i)-k (z,a i) := by ring
  rw [he]
  exact h (a i)

lemma finite_buying_cost_oscillation {E I : Type*} [Nonempty E] [Fintype I] [Nonempty I]
    (k : E × E → ℝ) (a : I → E) (φ : I → ℝ) (M : ℝ)
    (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M)
    (hφ0 : ∀ i, 0 ≤ φ i) (hzero : ∃ i, φ i = 0) (y z : E) (η : ℝ)
    (h : ∀ x, |k (x,y)-k (x,z)| ≤ η) :
    |finiteCostBuying k a φ y - finiteCostBuying k a φ z| ≤ η := by
  apply bounded_ciSup_abs_sub_le
    (fun x => finiteCostSelling k a φ x - k (x,y))
    (fun x => finiteCostSelling k a φ x - k (x,z))
    (finite_buying_scores_bddAbove k a φ M hk0 hkM hφ0 hzero y)
    (finite_buying_scores_bddAbove k a φ M hk0 hkM hφ0 hzero z)
  intro x
  have he : (finiteCostSelling k a φ x - k (x,y)) -
      (finiteCostSelling k a φ x - k (x,z)) = k (x,z)-k (x,y) := by ring
  rw [he,abs_sub_comm]
  exact h x

lemma finite_selling_uniformContinuous {E I : Type*} [PseudoMetricSpace E]
    [Fintype I] [Nonempty I] (k : E × E → ℝ) (hk : UniformContinuous k)
    (a : I → E) (φ : I → ℝ) : UniformContinuous (finiteCostSelling k a φ) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hk (ε/2) (half_pos hε)
  refine ⟨δ,hδ,?_⟩
  intro x z hxz
  have hb := finite_ciInf_abs_sub_le (fun i => φ i + k (x,a i))
    (fun i => φ i + k (z,a i)) (ε/2) (by
      intro i
      have hp : dist (x,a i) (z,a i) < δ := by simpa [Prod.dist_eq] using hxz
      have hv := (hd hp).le
      rw [Real.dist_eq] at hv
      have he : φ i + k (x,a i) - (φ i + k (z,a i)) = k (x,a i)-k (z,a i) := by ring
      rw [he]
      exact hv)
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hb (by linarith)

lemma finite_buying_uniformContinuous {E I : Type*} [PseudoMetricSpace E] [Nonempty E]
    [Fintype I] [Nonempty I] (k : E × E → ℝ) (hk : UniformContinuous k)
    (a : I → E) (φ : I → ℝ) (M : ℝ)
    (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M)
    (hφ0 : ∀ i, 0 ≤ φ i) (hzero : ∃ i, φ i = 0) :
    UniformContinuous (finiteCostBuying k a φ) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hk (ε/2) (half_pos hε)
  refine ⟨δ,hδ,?_⟩
  intro y z hyz
  have hb := bounded_ciSup_abs_sub_le
    (fun x => finiteCostSelling k a φ x - k (x,y))
    (fun x => finiteCostSelling k a φ x - k (x,z))
    (finite_buying_scores_bddAbove k a φ M hk0 hkM hφ0 hzero y)
    (finite_buying_scores_bddAbove k a φ M hk0 hkM hφ0 hzero z) (ε/2) (by
      intro x
      have hp : dist (x,y) (x,z) < δ := by simpa [Prod.dist_eq] using hyz
      have hv := (hd hp).le
      rw [Real.dist_eq] at hv
      have he : (finiteCostSelling k a φ x - k (x,y)) -
          (finiteCostSelling k a φ x - k (x,z)) = k (x,z)-k (x,y) := by ring
      rw [he,abs_sub_comm]
      exact hv)
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hb (by linarith)

lemma exists_boundedContinuous_of_range {E : Type*} [TopologicalSpace E]
    (f : E → ℝ) (hf : Continuous f) (M : ℝ) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    ∃ F : BoundedContinuousFunction E ℝ, ∀ x, F x = f x := by
  let F := BoundedContinuousFunction.mkOfBound ⟨f,hf⟩ M (by
    intro x y
    rw [Real.dist_eq]
    change |f x-f y| ≤ M
    apply abs_le.mpr
    have hx := hb x
    have hy := hb y
    constructor <;> linarith)
  exact ⟨F,fun _ => rfl⟩

lemma bounded_continuous_finite_potential_extension {E I J : Type*}
    [PseudoMetricSpace E] [Nonempty E] [Fintype I] [Nonempty I]
    (k : E × E → ℝ) (hk : UniformContinuous k) (M : ℝ)
    (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M)
    (hdiag : ∀ x, k (x,x) = 0) (a : I → E) (b : J → E)
    (φ : I → ℝ) (ψ : J → ℝ) (hφ0 : ∀ i, 0 ≤ φ i) (hzero : ∃ i, φ i = 0)
    (hc : ∀ i j, ψ j - φ i ≤ k (b j,a i)) :
    ∃ (Φ Ψ : BoundedContinuousFunction E ℝ), (∀ x, 0 ≤ Φ x ∧ Φ x ≤ M) ∧
      (∀ x, 0 ≤ Ψ x ∧ Ψ x ≤ M) ∧ (∀ x y, Ψ x - Φ y ≤ k (x,y)) ∧
      (∀ i, Φ (a i) ≤ φ i) ∧ (∀ j, ψ j ≤ Ψ (b j)) ∧
      (∀ x z η, (∀ y, |k (x,y)-k (z,y)| ≤ η) → |Ψ x-Ψ z| ≤ η) ∧
      (∀ y z η, (∀ x, |k (x,y)-k (x,z)| ≤ η) → |Φ y-Φ z| ≤ η) := by
  obtain ⟨Ψ,hΨ⟩ := exists_boundedContinuous_of_range (finiteCostSelling k a φ)
    (finite_selling_uniformContinuous k hk a φ).continuous M
    (finite_selling_bounds k a φ M hk0 hkM hφ0 hzero)
  obtain ⟨Φ,hΦ⟩ := exists_boundedContinuous_of_range (finiteCostBuying k a φ)
    (finite_buying_uniformContinuous k hk a φ M hk0 hkM hφ0 hzero).continuous M
    (finite_buying_bounds k a φ M hk0 hkM hdiag hφ0 hzero)
  refine ⟨Φ,Ψ,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x
    rw [hΦ]
    exact finite_buying_bounds k a φ M hk0 hkM hdiag hφ0 hzero x
  · intro x
    rw [hΨ]
    exact finite_selling_bounds k a φ M hk0 hkM hφ0 hzero x
  · intro x y
    rw [hΨ,hΦ]
    exact finite_extended_pair_feasible k a φ M hk0 hkM hφ0 hzero x y
  · intro i
    rw [hΦ]
    exact finite_buying_at_center_le k a φ i
  · intro j
    rw [hΨ]
    exact finite_selling_at_destination_ge k a b φ ψ hc j
  · intro x z η h
    rw [hΨ,hΨ]
    exact finite_selling_cost_oscillation k a φ x z η h
  · intro y z η h
    rw [hΦ,hΦ]
    exact finite_buying_cost_oscillation k a φ M hk0 hkM hφ0 hzero y z η h

#print axioms finite_selling_cost_oscillation
#print axioms finite_buying_cost_oscillation
#print axioms finite_selling_uniformContinuous
#print axioms finite_buying_uniformContinuous
#print axioms exists_boundedContinuous_of_range
#print axioms bounded_continuous_finite_potential_extension
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichBoundedDiscrete
set_option autoImplicit false
open scoped BigOperators
namespace DualityCodex

lemma bounded_continuous_discrete_dual_gap {E I J : Type*} [PseudoMetricSpace E] [Nonempty E]
    [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (k : E × E → ℝ) (hk : UniformContinuous k) (M : ℝ)
    (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M)
    (hdiag : ∀ x, k (x,x) = 0) (a : I → E) (b : J → E)
    (α : I → ℝ) (β : J → ℝ) (hα : ∀ i, 0 ≤ α i) (hβ : ∀ j, 0 ≤ β j)
    (hαsum : ∑ i, α i = 1) (hβsum : ∑ j, β j = 1) (r : ℝ)
    (hgap : ∀ w ∈ stdSimplex ℝ (I × J),
      (finiteTransportMap (fun ij => k (b ij.2,a ij.1)) w).1 = (α,β) →
        r < (finiteTransportMap (fun ij => k (b ij.2,a ij.1)) w).2) :
    ∃ (Φ Ψ : BoundedContinuousFunction E ℝ), (∀ x, 0 ≤ Φ x ∧ Φ x ≤ M) ∧
      (∀ x, 0 ≤ Ψ x ∧ Ψ x ≤ M) ∧ (∀ x y, Ψ x - Φ y ≤ k (x,y)) ∧
      r < (∑ j, Ψ (b j) * β j) - ∑ i, Φ (a i) * α i ∧
      (∀ x z η, (∀ y, |k (x,y)-k (z,y)| ≤ η) → |Ψ x-Ψ z| ≤ η) ∧
      (∀ y z η, (∀ x, |k (x,y)-k (x,z)| ≤ η) → |Φ y-Φ z| ≤ η) := by
  obtain ⟨φ,ψ,hφ,hψ,hzero,hc,hr⟩ := bounded_finite_transport_dual_gap
    (fun ij => k (b ij.2,a ij.1)) M (fun i j => hk0 (b j) (a i))
    (fun i j => hkM (b j) (a i)) α β hα hβ hαsum hβsum r hgap
  obtain ⟨Φ,Ψ,hΦ,hΨ,hfeasible,hΦa,hΨb,hΨosc,hΦosc⟩ := bounded_continuous_finite_potential_extension
    k hk M hk0 hkM hdiag a b φ ψ (fun i => (hφ i).1) hzero hc
  have hobj := finite_potential_objective_mono α β hα hβ φ (fun i => Φ (a i))
    ψ (fun j => Ψ (b j)) hΦa hΨb
  exact ⟨Φ,Ψ,hΦ,hΨ,hfeasible,hr.trans_le hobj,hΨosc,hΦosc⟩

#print axioms bounded_continuous_discrete_dual_gap
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichPartitionGap
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma partition_bounded_continuous_dual_gap {E I J : Type*}
    [PseudoMetricSpace E] [Nonempty E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J]
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (k : E × E → ℝ) (hk : UniformContinuous k) (M : ℝ) (hM : 0 ≤ M)
    (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M)
    (hdiag : ∀ x, k (x,x) = 0)
    (S : I → Set E) (T : J → Set E) (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (fun i l => Disjoint (S i) (S l)))
    (hdT : Pairwise (fun j l => Disjoint (T j) (T l)))
    (hcoverS : (⋃ i, S i) = Set.univ) (hcoverT : (⋃ j, T j) = Set.univ)
    (a : I → E) (b : J → E) (x0 : E) (i0 : I) (j0 : J) (η r : ℝ) (hη : 0 ≤ η)
    (hcell : ∀ i j x y, x ∈ S i → y ∈ T j →
      k (y,x) ≤ k (b j,a i) + if (i,j) ∈ badPairIndices i0 j0 then M else η)
    (hgS : ∀ i, i ≠ i0 → ∀ y, y ∈ S i → ∀ x, |k (x,y)-k (x,a i)| ≤ η)
    (hgT : ∀ j, j ≠ j0 → ∀ x, x ∈ T j → ∀ y, |k (x,y)-k (b j,y)| ≤ η)
    (hgap : ENNReal.ofReal (r + 3 * η + 2 * M *
      ((Q (S i0)).toReal + (Q' (T j0)).toReal)) <
      couplingCostInf Q Q' (fun z => ENNReal.ofReal (k (z.2,z.1)))) :
    ∃ (Φ Ψ : BoundedContinuousFunction E ℝ), (∀ x, 0 ≤ Φ x ∧ Φ x ≤ M) ∧
      (∀ x, 0 ≤ Ψ x ∧ Ψ x ≤ M) ∧ (∀ x y, Ψ x - Φ y ≤ k (x,y)) ∧
      r < (∫ x, Ψ x ∂Q') - ∫ x, Φ x ∂Q := by
  classical
  let α : I → ℝ := fun i => (Q (S i)).toReal
  let β : J → ℝ := fun j => (Q' (T j)).toReal
  let t : ℝ := α i0 + β j0
  let c : I × J → ℝ := fun ij => k (b ij.2,a ij.1)
  have hfinite : ∀ w ∈ stdSimplex ℝ (I × J), (finiteTransportMap c w).1 = (α,β) →
      r + 2 * η + M * t < (finiteTransportMap c w).2 := by
    intro w hw hm
    have hrow : ∀ i, ∑ j, w (i,j) = α i := by
      intro i
      exact congrArg (fun z : (I → ℝ) × (J → ℝ) => z.1 i) hm
    have hcol : ∀ j, ∑ i, w (i,j) = β j := by
      intro j
      exact congrArg (fun z : (I → ℝ) × (J → ℝ) => z.2 j) hm
    have hl := couplingCostInf_le_matrix_plus_tail Q Q' S T hS hT hdS hdT hcoverS hcoverT
      w hw.1 hw.2 hrow hcol x0 x0 i0 j0 c (fun ij => hk0 (b ij.2) (a ij.1)) η M hη hM
      (fun z => ENNReal.ofReal (k (z.2,z.1)))
      (fun i j x y hx hy => ENNReal.ofReal_le_ofReal (hcell i j x y hx hy))
    by_contra hn
    push_neg at hn
    have hr : (∑ ij, c ij * w ij) + η + M * t ≤ r + 3 * η + 2 * M * t := by
      change (∑ ij, w ij * c ij) ≤ r + 2 * η + M * t at hn
      have he : (∑ ij, c ij * w ij) = ∑ ij, w ij * c ij := by
        apply Finset.sum_congr rfl
        intro ij _
        ring
      rw [he]
      linarith
    exact (not_lt_of_ge (hl.trans (ENNReal.ofReal_le_ofReal hr))) hgap
  obtain ⟨Φ,Ψ,hΦ,hΨ,hfeas,hobj,hΨosc,hΦosc⟩ := bounded_continuous_discrete_dual_gap
    k hk M hk0 hkM hdiag a b α β (fun _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg)
    (finite_partition_real_mass_sum_one Q S hS hdS hcoverS)
    (finite_partition_real_mass_sum_one Q' T hT hdT hcoverT)
    (r + 2 * η + M * t) hfinite
  have he := bounded_pair_integral_objective_error Q Q' S T hS hT hdS hdT hcoverS hcoverT
    a b i0 j0 Φ Ψ η M hη hΦ hΨ
    (fun i hi y hy => hΦosc y (a i) η (hgS i hi y hy))
    (fun j hj x hx => hΨosc x (b j) η (hgT j hj x hx))
  refine ⟨Φ,Ψ,hΦ,hΨ,hfeas,?_⟩
  have he' := (abs_le.mp he).1
  dsimp only [α,β,t] at hobj
  linarith

#print axioms partition_bounded_continuous_dual_gap
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichCellGeometry
set_option autoImplicit false
open MeasureTheory TopologicalSpace
namespace DualityCodex

lemma uniform_cost_common_modulus {E : Type*} [PseudoMetricSpace E]
    (k : E × E → ℝ) (hk : UniformContinuous k) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, (∀ x z y, dist x z ≤ δ → |k (x,y)-k (z,y)| ≤ η) ∧
      (∀ y z x, dist y z ≤ δ → |k (x,y)-k (x,z)| ≤ η) ∧
      (∀ x y z t, dist x z ≤ δ → dist y t ≤ δ → |k (x,y)-k (z,t)| ≤ η) := by
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff_le.mp hk η hη
  refine ⟨δ,hδ,?_,?_,?_⟩
  · intro x z y hx
    simpa only [Real.dist_eq] using hd (a := (x,y)) (b := (z,y)) (by simpa using hx)
  · intro y z x hy
    simpa only [Real.dist_eq] using hd (a := (x,y)) (b := (x,z)) (by simpa using hy)
  · intro x y z t hx hy
    simpa only [Real.dist_eq] using hd (a := (x,y)) (b := (z,t)) (by
      simpa only [Prod.dist_eq,max_le_iff] using And.intro hx hy)

noncomputable def truncatedPartitionCenter {E : Type*} (a : ℕ → E) (x0 : E) (N : ℕ)
    (i : Fin (N+1)) : E := if i.val < N then a i.val else x0

lemma truncatedPartitionCenter_dist {E : Type*} [PseudoMetricSpace E]
    (A : ℕ → Set E) (a : ℕ → E) (x0 : E) (N : ℕ) (δ : ℝ)
    (hcenter : ∀ n x, x ∈ A n → dist x (a n) ≤ δ)
    (i : Fin (N+1)) (hi : i ≠ Fin.last N) (x : E) (hx : x ∈ truncatedPartitionCells A N i) :
    dist x (truncatedPartitionCenter a x0 N i) ≤ δ := by
  have hiN : i.val < N := by
    have := i.isLt
    have hn : i.val ≠ N := by
      intro h
      exact hi (Fin.ext h)
    omega
  simp only [truncatedPartitionCenter,if_pos hiN]
  apply hcenter i.val x
  simpa only [truncatedPartitionCells,if_pos hiN] using hx

lemma truncated_partition_cost_bound {E : Type*} [PseudoMetricSpace E]
    (k : E × E → ℝ) (M η δ : ℝ) (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M)
    (hmod : ∀ x y z t, dist x z ≤ δ → dist y t ≤ δ → |k (x,y)-k (z,t)| ≤ η)
    (A : ℕ → Set E) (a : ℕ → E) (x0 : E) (N : ℕ)
    (hcenter : ∀ n x, x ∈ A n → dist x (a n) ≤ δ) :
    ∀ i j x y, x ∈ truncatedPartitionCells A N i → y ∈ truncatedPartitionCells A N j →
      k (y,x) ≤ k (truncatedPartitionCenter a x0 N j,truncatedPartitionCenter a x0 N i) +
        if (i,j) ∈ badPairIndices (Fin.last N) (Fin.last N) then M else η := by
  classical
  intro i j x y hx hy
  by_cases hb : (i,j) ∈ badPairIndices (Fin.last N) (Fin.last N)
  · rw [if_pos hb]
    have h0 := hk0 (truncatedPartitionCenter a x0 N j) (truncatedPartitionCenter a x0 N i)
    have hm := hkM y x
    linarith
  · rw [if_neg hb]
    have hi : i ≠ Fin.last N := by
      intro hi
      exact hb (by simp [badPairIndices,hi])
    have hj : j ≠ Fin.last N := by
      intro hj
      exact hb (by simp [badPairIndices,hj])
    have hm := hmod y x (truncatedPartitionCenter a x0 N j) (truncatedPartitionCenter a x0 N i)
      (truncatedPartitionCenter_dist A a x0 N δ hcenter j hj y hy)
      (truncatedPartitionCenter_dist A a x0 N δ hcenter i hi x hx)
    have := (abs_le.mp hm).2
    linarith

#print axioms uniform_cost_common_modulus
#print axioms truncatedPartitionCenter_dist
#print axioms truncated_partition_cost_bound
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichTailReal
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma exists_small_real_partition_tail {E : Type*} [MeasurableSpace E]
    (Q Q' : Measure E) [IsFiniteMeasure Q] [IsFiniteMeasure Q'] (A : ℕ → Set E)
    (hA : ∀ n, MeasurableSet (A n)) (hcover : (⋃ n, A n) = Set.univ)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ N, (Q (finitePartitionHead A N)ᶜ).toReal + (Q' (finitePartitionHead A N)ᶜ).toReal < τ := by
  obtain ⟨N,hN⟩ := exists_common_small_partition_tail Q Q' A hA hcover
    (ENNReal.ofReal τ) (ENNReal.ofReal_pos.mpr hτ)
  have hfin : Q (finitePartitionHead A N)ᶜ + Q' (finitePartitionHead A N)ᶜ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top Q _,measure_ne_top Q' _⟩
  have h := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hN
  rw [ENNReal.toReal_add (measure_ne_top Q _) (measure_ne_top Q' _),ENNReal.toReal_ofReal hτ.le] at h
  exact ⟨N,h⟩

#print axioms exists_small_real_partition_tail
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichBoundedGap
set_option autoImplicit false
open MeasureTheory TopologicalSpace
namespace DualityCodex

lemma bounded_uniform_cost_dual_gap_with_margin {E : Type*} [PseudoMetricSpace E]
    [Nonempty E] [MeasurableSpace E] [OpensMeasurableSpace E] [SeparableSpace E]
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (k : E × E → ℝ) (hk : UniformContinuous k) (M : ℝ) (hM : 0 ≤ M)
    (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M)
    (hdiag : ∀ x, k (x,x) = 0)
    (r η τ : ℝ) (hη : 0 < η) (hτ : 0 < τ)
    (hgap : ENNReal.ofReal (r + 3 * η + 2 * M * τ) <
      couplingCostInf Q Q' (fun z => ENNReal.ofReal (k (z.2,z.1)))) :
    ∃ (Φ Ψ : BoundedContinuousFunction E ℝ), (∀ x, 0 ≤ Φ x ∧ Φ x ≤ M) ∧
      (∀ x, 0 ≤ Ψ x ∧ Ψ x ≤ M) ∧ (∀ x y, Ψ x - Φ y ≤ k (x,y)) ∧
      r < (∫ x, Ψ x ∂Q') - ∫ x, Φ x ∂Q := by
  classical
  let x0 : E := Classical.choice inferInstance
  obtain ⟨δ,hδ,hfirst,hsecond,hboth⟩ := uniform_cost_common_modulus k hk η hη
  obtain ⟨A,a,hm,hb,hd,hcover,hdisj,hcenter⟩ :=
    exists_countable_measurable_partition_centers x0 δ hδ
  obtain ⟨N,hN⟩ := exists_small_real_partition_tail Q Q' A hm hcover τ hτ
  let S := truncatedPartitionCells A N
  let c := truncatedPartitionCenter a x0 N
  have htail : (Q (S (Fin.last N))).toReal + (Q' (S (Fin.last N))).toReal < τ := by
    simpa only [S,truncatedPartitionCells_tail] using hN
  have hg : ENNReal.ofReal (r + 3 * η + 2 * M *
      ((Q (S (Fin.last N))).toReal + (Q' (S (Fin.last N))).toReal)) <
      couplingCostInf Q Q' (fun z => ENNReal.ofReal (k (z.2,z.1))) := by
    apply lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hgap
    have ht := mul_le_mul_of_nonneg_left htail.le (show 0 ≤ 2 * M by positivity)
    linarith
  exact partition_bounded_continuous_dual_gap Q Q' k hk M hM hk0 hkM hdiag S S
    (truncatedPartitionCells_measurable A hm N) (truncatedPartitionCells_measurable A hm N)
    (truncatedPartitionCells_disjoint A hdisj N) (truncatedPartitionCells_disjoint A hdisj N)
    (truncatedPartitionCells_cover A N) (truncatedPartitionCells_cover A N)
    c c x0 (Fin.last N) (Fin.last N) η r hη.le
    (truncated_partition_cost_bound k M η δ hk0 hkM hboth A a x0 N hcenter)
    (fun i hi y hy x => hsecond y (c i) x
      (truncatedPartitionCenter_dist A a x0 N δ hcenter i hi y hy))
    (fun j hj x hx y => hfirst x (c j) y
      (truncatedPartitionCenter_dist A a x0 N δ hcenter j hj x hx)) hg

#print axioms bounded_uniform_cost_dual_gap_with_margin
lemma exists_positive_dual_gap_margin (P : ENNReal) (M r : ℝ) (hM : 0 ≤ M)
    (hr : ENNReal.ofReal r < P) :
    ∃ ε > 0, ENNReal.ofReal (r + 3 * ε + 2 * M * ε) < P := by
  by_cases hP : P = ⊤
  · refine ⟨1,by norm_num,?_⟩
    rw [hP]
    exact ENNReal.ofReal_lt_top
  · have hm : max r 0 < P.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (le_max_right r 0) hP).mp (by simpa using hr)
    have hR : 0 < P.toReal := (le_max_right r 0).trans_lt hm
    have hrr : r < P.toReal := (le_max_left r 0).trans_lt hm
    let C : ℝ := 3 + 2 * M
    have hC : 0 < C := by dsimp [C]; linarith
    let ε : ℝ := (P.toReal-r) / (2 * C)
    have hε : 0 < ε := div_pos (sub_pos.mpr hrr) (by positivity)
    have he : 2 * C * ε = P.toReal-r := by
      dsimp only [ε]
      field_simp
    refine ⟨ε,hε,?_⟩
    calc
      ENNReal.ofReal (r + 3 * ε + 2 * M * ε) < ENNReal.ofReal P.toReal := by
        apply (ENNReal.ofReal_lt_ofReal_iff hR).mpr
        dsimp only [C] at he
        nlinarith
      _ = P := ENNReal.ofReal_toReal hP

lemma bounded_uniform_cost_dual_gap {E : Type*} [PseudoMetricSpace E]
    [Nonempty E] [MeasurableSpace E] [OpensMeasurableSpace E] [SeparableSpace E]
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (k : E × E → ℝ) (hk : UniformContinuous k) (M : ℝ) (hM : 0 ≤ M)
    (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M)
    (hdiag : ∀ x, k (x,x) = 0) (r : ℝ)
    (hr : ENNReal.ofReal r < couplingCostInf Q Q' (fun z => ENNReal.ofReal (k (z.2,z.1)))) :
    ∃ (Φ Ψ : BoundedContinuousFunction E ℝ), (∀ x, 0 ≤ Φ x ∧ Φ x ≤ M) ∧
      (∀ x, 0 ≤ Ψ x ∧ Ψ x ≤ M) ∧ (∀ x y, Ψ x - Φ y ≤ k (x,y)) ∧
      r < (∫ x, Ψ x ∂Q') - ∫ x, Φ x ∂Q := by
  obtain ⟨ε,hε,hmargin⟩ := exists_positive_dual_gap_margin _ M r hM hr
  exact bounded_uniform_cost_dual_gap_with_margin Q Q' k hk M hM hk0 hkM hdiag
    r ε ε hε hε hmargin

#print axioms exists_positive_dual_gap_margin
#print axioms bounded_uniform_cost_dual_gap
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichBoundedStrong
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

noncomputable def boundedCostDualSup {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (Q Q' : Measure E) (k : E × E → ℝ) : EReal :=
  ⨆ (Φ : BoundedContinuousFunction E ℝ) (Ψ : BoundedContinuousFunction E ℝ) (_ : ∀ x y, Ψ x - Φ y ≤ k (x,y)),
    ((∫ x, Ψ x ∂Q' - ∫ x, Φ x ∂Q : ℝ) : EReal)

lemma real_le_couplingCostInf {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (Q : Measure E) (Q' : Measure F) (f : E × F → ENNReal) (r : ℝ)
    (hr : ∀ π : Measure (E × F), π.map Prod.fst = Q ∧ π.map Prod.snd = Q' →
      (r : EReal) ≤ ((∫⁻ z, f z ∂π) : EReal)) :
    (r : EReal) ≤ (couplingCostInf Q Q' f : EReal) := by
  by_cases h : r ≤ 0
  · exact (EReal.coe_le_coe_iff.mpr h).trans (EReal.coe_ennreal_nonneg _)
  · have h0 : 0 ≤ r := (lt_of_not_ge h).le
    have he : (ENNReal.ofReal r : EReal) = (r : EReal) := by
      rw [EReal.coe_ennreal_ofReal,max_eq_left h0]
    rw [← he]
    apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    refine le_iInf fun π => le_iInf fun hπ => ?_
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mp (by rw [he]; exact hr π hπ)

lemma bounded_cost_coupling_lower_bound {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (k : E × E → ℝ) (hk0 : ∀ x y, 0 ≤ k (x,y)) (Φ Ψ : BoundedContinuousFunction E ℝ)
    (hc : ∀ x y, Ψ x - Φ y ≤ k (x,y))
    (π : Measure (E × E)) (hπ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q') :
    ((∫ x, Ψ x ∂Q' - ∫ x, Φ x ∂Q : ℝ) : EReal) ≤
      ((∫⁻ z, ENNReal.ofReal (k (z.2,z.1)) ∂π) : EReal) := by
  have hΦπ : Integrable (fun z : E × E => Φ z.1) π :=
    (show Integrable Φ (π.map Prod.fst) by rw [hπ.1]; exact Φ.integrable (μ := Q)).comp_measurable measurable_fst
  have hΨπ : Integrable (fun z : E × E => Ψ z.2) π :=
    (show Integrable Ψ (π.map Prod.snd) by rw [hπ.2]; exact Ψ.integrable (μ := Q')).comp_measurable measurable_snd
  have hf : (∫ z : E × E, Φ z.1 ∂π) = ∫ x, Φ x ∂Q := by
    rw [← hπ.1]
    exact (integral_map_of_stronglyMeasurable measurable_fst Φ.continuous.measurable.stronglyMeasurable).symm
  have hs : (∫ z : E × E, Ψ z.2 ∂π) = ∫ x, Ψ x ∂Q' := by
    rw [← hπ.2]
    exact (integral_map_of_stronglyMeasurable measurable_snd Ψ.continuous.measurable.stronglyMeasurable).symm
  have h := integral_le_extended_cost π (fun z : E × E => Ψ z.2 - Φ z.1)
    (fun z => ENNReal.ofReal (k (z.2,z.1))) (hΨπ.sub hΦπ) (Filter.Eventually.of_forall (by
      intro z
      rw [EReal.coe_ennreal_ofReal,max_eq_left (hk0 z.2 z.1)]
      exact EReal.coe_le_coe_iff.mpr (hc z.2 z.1)))
  rw [integral_sub hΨπ hΦπ,hs,hf] at h
  exact h

lemma bounded_cost_dual_weak {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (k : E × E → ℝ) (hk0 : ∀ x y, 0 ≤ k (x,y)) :
    boundedCostDualSup Q Q' k ≤ (couplingCostInf Q Q' (fun z => ENNReal.ofReal (k (z.2,z.1))) : EReal) := by
  refine iSup_le fun Φ => iSup_le fun Ψ => iSup_le fun hc => ?_
  exact real_le_couplingCostInf Q Q' _ _ (fun π hπ => bounded_cost_coupling_lower_bound Q Q' k hk0 Φ Ψ hc π hπ)

lemma bounded_cost_dual_nonnegative {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (Q Q' : Measure E) (k : E × E → ℝ) (hk0 : ∀ x y, 0 ≤ k (x,y)) :
    0 ≤ boundedCostDualSup Q Q' k := by
  have hc : ∀ x y, (0 : BoundedContinuousFunction E ℝ) x - (0 : BoundedContinuousFunction E ℝ) y ≤ k (x,y) := by
    simpa using hk0
  have h : ((∫ x, (0 : BoundedContinuousFunction E ℝ) x ∂Q' -
      ∫ x, (0 : BoundedContinuousFunction E ℝ) x ∂Q : ℝ) : EReal) ≤ boundedCostDualSup Q Q' k :=
    le_iSup_of_le (0 : BoundedContinuousFunction E ℝ)
    (le_iSup_of_le (0 : BoundedContinuousFunction E ℝ) (le_iSup_of_le hc le_rfl))
  simpa only [BoundedContinuousFunction.coe_zero,Pi.zero_apply,integral_zero,sub_zero,EReal.coe_zero] using
    (show ((∫ x, (0 : BoundedContinuousFunction E ℝ) x ∂Q' -
      ∫ x, (0 : BoundedContinuousFunction E ℝ) x ∂Q : ℝ) : EReal) ≤ boundedCostDualSup Q Q' k from h)

lemma bounded_uniform_cost_strong_duality {E : Type*} [PseudoMetricSpace E]
    [Nonempty E] [MeasurableSpace E] [OpensMeasurableSpace E] [TopologicalSpace.SeparableSpace E]
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    (k : E × E → ℝ) (hk : UniformContinuous k) (M : ℝ) (hM : 0 ≤ M)
    (hk0 : ∀ x y, 0 ≤ k (x,y)) (hkM : ∀ x y, k (x,y) ≤ M) (hdiag : ∀ x, k (x,x) = 0) :
    (couplingCostInf Q Q' (fun z => ENNReal.ofReal (k (z.2,z.1))) : EReal) =
      boundedCostDualSup Q Q' k := by
  apply le_antisymm
  · by_contra hn
    have hlt := lt_of_not_ge hn
    obtain ⟨r,hrS,hrP⟩ := EReal.exists_between_coe_real hlt
    have hr0 : 0 ≤ r := (EReal.coe_le_coe_iff.mp
      ((bounded_cost_dual_nonnegative Q Q' k hk0).trans hrS.le))
    have hrNN : ENNReal.ofReal r < couplingCostInf Q Q' (fun z => ENNReal.ofReal (k (z.2,z.1))) := by
      apply EReal.coe_ennreal_lt_coe_ennreal_iff.mp
      simpa only [EReal.coe_ennreal_ofReal,max_eq_left hr0] using hrP
    obtain ⟨Φ,Ψ,hΦ,hΨ,hfeas,hobj⟩ := bounded_uniform_cost_dual_gap Q Q' k hk M hM hk0 hkM hdiag r hrNN
    have ho : ((∫ x, Ψ x ∂Q' - ∫ x, Φ x ∂Q : ℝ) : EReal) ≤ boundedCostDualSup Q Q' k :=
      le_iSup_of_le Φ (le_iSup_of_le Ψ (le_iSup_of_le hfeas le_rfl))
    exact (not_lt_of_ge (ho.trans hrS.le)) (EReal.coe_lt_coe_iff.mpr hobj)
  · exact bounded_cost_dual_weak Q Q' k hk0

#print axioms real_le_couplingCostInf
#print axioms bounded_cost_coupling_lower_bound
#print axioms bounded_cost_dual_weak
#print axioms bounded_cost_dual_nonnegative
#print axioms bounded_uniform_cost_strong_duality
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichCompact
set_option autoImplicit false
open MeasureTheory TopologicalSpace
namespace DualityCodex

noncomputable def probabilityCouplings {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (Q Q' : ProbabilityMeasure E) :
    Set (ProbabilityMeasure (E × E)) :=
  {π | π.map continuous_fst.measurable.aemeasurable = Q ∧
    π.map continuous_snd.measurable.aemeasurable = Q'}

lemma probabilityCouplings_closed {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (Q Q' : ProbabilityMeasure E) :
    IsClosed (probabilityCouplings Q Q') := by
  exact (isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const).inter
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const)

lemma probabilityCouplings_tight {E : Type*} [MetricSpace E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (Q Q' : ProbabilityMeasure E) :
    IsTightMeasureSet {((π : ProbabilityMeasure (E × E)) : Measure (E × E)) | π ∈ probabilityCouplings Q Q'} := by
  apply IsTightMeasureSet.prodMk
  · apply (isTightMeasureSet_singleton (μ := (Q : Measure E))).subset
    rintro _ ⟨μ,⟨π,hπ,rfl⟩,rfl⟩
    have h := congrArg ProbabilityMeasure.toMeasure hπ.1
    simpa only [Set.mem_singleton_iff,Measure.fst,ProbabilityMeasure.toMeasure_map] using h
  · apply (isTightMeasureSet_singleton (μ := (Q' : Measure E))).subset
    rintro _ ⟨μ,⟨π,hπ,rfl⟩,rfl⟩
    have h := congrArg ProbabilityMeasure.toMeasure hπ.2
    simpa only [Set.mem_singleton_iff,Measure.snd,ProbabilityMeasure.toMeasure_map] using h

lemma probabilityCouplings_compact {E : Type*} [MetricSpace E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (Q Q' : ProbabilityMeasure E) :
    IsCompact (probabilityCouplings Q Q') := by
  have h := isCompact_closure_of_isTightMeasureSet (probabilityCouplings_tight Q Q')
  rwa [(probabilityCouplings_closed Q Q').closure_eq] at h

#print axioms probabilityCouplings_closed
#print axioms probabilityCouplings_tight
#print axioms probabilityCouplings_compact
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichCompactLimit
set_option autoImplicit false
namespace DualityCodex

lemma compact_monotone_iInf_iSup {X : Type*} [TopologicalSpace X] [T2Space X]
    (K : Set X) (hK : IsCompact K) (f : ℕ → X → ENNReal)
    (hf : ∀ n, Continuous (f n)) (hm : ∀ x, Monotone (fun n => f n x)) :
    (⨅ x, ⨅ (_ : x ∈ K), ⨆ n, f n x) = ⨆ n, ⨅ x, ⨅ (_ : x ∈ K), f n x := by
  classical
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro d hd
    let T : ℕ → Set X := fun n => K ∩ {x | f n x ≤ d}
    have hclosed : ∀ n, IsClosed (T n) := fun n =>
      hK.isClosed.inter (isClosed_le (hf n) continuous_const)
    have hnonempty : ∀ n, (T n).Nonempty := by
      intro n
      have hn : (⨅ x, ⨅ (_ : x ∈ K), f n x) < d :=
        (le_iSup (fun n => ⨅ x, ⨅ (_ : x ∈ K), f n x) n).trans_lt hd
      obtain ⟨x,hx⟩ := iInf_lt_iff.mp hn
      obtain ⟨hmem,hval⟩ := iInf_lt_iff.mp hx
      exact ⟨x,hmem,hval.le⟩
    have hstep : ∀ n, T (n+1) ⊆ T n := by
      intro n x hx
      exact ⟨hx.1,((hm x) (Nat.le_succ n)).trans hx.2⟩
    have hcompact : IsCompact (T 0) := hK.inter_right (isClosed_le (hf 0) continuous_const)
    obtain ⟨x,hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      T hstep hnonempty hcompact hclosed
    have hn : ∀ n, x ∈ T n := Set.mem_iInter.mp hx
    exact iInf_le_of_le x (iInf_le_of_le (hn 0).1 (iSup_le fun n => (hn n).2))
  · refine le_iInf fun x => le_iInf fun hx => iSup_le fun n => ?_
    exact (iInf_le_of_le x (iInf_le_of_le hx le_rfl)).trans (le_iSup (fun n => f n x) n)

#print axioms compact_monotone_iInf_iSup
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichTruncatedCost
set_option autoImplicit false
open MeasureTheory TopologicalSpace
namespace DualityCodex

noncomputable def truncatedPowerCost {E : Type*} [PseudoMetricSpace E] (p : ℝ) (n : ℕ)
    (z : E × E) : ℝ := (min (dist z.1 z.2) ((n : ℝ)+1)) ^ p

lemma truncatedPowerCost_nonnegative {E : Type*} [PseudoMetricSpace E] (p : ℝ) (n : ℕ) (z : E × E) :
    0 ≤ truncatedPowerCost p n z :=
  Real.rpow_nonneg (le_min (dist_nonneg) (by positivity)) p

lemma truncatedPowerCost_bound {E : Type*} [PseudoMetricSpace E] (p : ℝ) (hp : 0 ≤ p) (n : ℕ) (z : E × E) :
    truncatedPowerCost p n z ≤ ((n : ℝ)+1) ^ p :=
  Real.rpow_le_rpow (le_min dist_nonneg (by positivity)) (min_le_right _ _) hp

lemma truncatedPowerCost_le_full {E : Type*} [PseudoMetricSpace E] (p : ℝ) (hp : 0 ≤ p) (n : ℕ) (z : E × E) :
    truncatedPowerCost p n z ≤ (dist z.1 z.2) ^ p :=
  Real.rpow_le_rpow (le_min dist_nonneg (by positivity)) (min_le_left _ _) hp

lemma truncatedPowerCost_monotone {E : Type*} [PseudoMetricSpace E] (p : ℝ) (hp : 0 ≤ p) (z : E × E) :
    Monotone (fun n => truncatedPowerCost p n z) := by
  intro n m hnm
  apply Real.rpow_le_rpow (le_min dist_nonneg (by positivity))
    (min_le_min_left _ (by exact_mod_cast Nat.add_le_add_right hnm 1)) hp

lemma truncatedPowerCost_diag {E : Type*} [PseudoMetricSpace E] (p : ℝ) (hp : 0 < p) (n : ℕ) (x : E) :
    truncatedPowerCost p n (x,x) = 0 := by
  simp [truncatedPowerCost,min_eq_left (show (0 : ℝ) ≤ (n : ℝ)+1 by positivity),Real.zero_rpow hp.ne']

lemma truncatedPowerCost_uniform {E : Type*} [PseudoMetricSpace E] (p : ℝ) (hp : 0 ≤ p) (n : ℕ) :
    UniformContinuous (truncatedPowerCost (E := E) p n) := by
  let g : E × E → ℝ := fun z => min (dist z.1 z.2) ((n : ℝ)+1)
  have hg : UniformContinuous g := lipschitzWith_min.uniformContinuous.comp
    (uniformContinuous_dist.prodMk uniformContinuous_const)
  have hpw : UniformContinuousOn (fun x : ℝ => x ^ p) (Set.Icc 0 ((n : ℝ)+1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (Real.continuous_rpow_const hp).continuousOn
  have hcomp := hpw.comp hg.uniformContinuousOn (s := Set.univ) (by
    intro z _
    exact ⟨le_min dist_nonneg (by positivity),min_le_right _ _⟩)
  change UniformContinuous (fun z : E × E => (min (dist z.1 z.2) ((n : ℝ)+1)) ^ p)
  exact uniformContinuousOn_univ.mp hcomp

#print axioms truncatedPowerCost_nonnegative
#print axioms truncatedPowerCost_bound
#print axioms truncatedPowerCost_le_full
#print axioms truncatedPowerCost_monotone
#print axioms truncatedPowerCost_diag
#print axioms truncatedPowerCost_uniform
lemma truncatedPowerCost_swap {E : Type*} [PseudoMetricSpace E] (p : ℝ) (n : ℕ) (x y : E) :
    truncatedPowerCost p n (y,x) = truncatedPowerCost p n (x,y) := by
  simp only [truncatedPowerCost,dist_comm]

lemma truncatedPowerCost_iSup {E : Type*} [PseudoMetricSpace E] (p : ℝ) (hp : 0 ≤ p) (z : E × E) :
    (⨆ n, ENNReal.ofReal (truncatedPowerCost p n z)) = ENNReal.ofReal ((dist z.1 z.2)^p) := by
  apply le_antisymm
  · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (truncatedPowerCost_le_full p hp n z)
  · obtain ⟨n,hn⟩ := exists_nat_gt (dist z.1 z.2)
    have hd : dist z.1 z.2 ≤ (n : ℝ)+1 := by linarith
    apply le_iSup_of_le n
    simp only [truncatedPowerCost,min_eq_left hd,le_refl]

#print axioms truncatedPowerCost_swap
#print axioms truncatedPowerCost_iSup
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichTruncatedIntegral
set_option autoImplicit false
open MeasureTheory TopologicalSpace
namespace DualityCodex

noncomputable def truncatedPowerCostNN {E : Type*} [PseudoMetricSpace E] (p : ℝ) (n : ℕ)
    (z : E × E) : NNReal := ⟨truncatedPowerCost p n z,truncatedPowerCost_nonnegative p n z⟩

lemma truncatedPowerCostNN_continuous {E : Type*} [PseudoMetricSpace E] (p : ℝ) (hp : 0 ≤ p) (n : ℕ) :
    Continuous (truncatedPowerCostNN (E := E) p n) :=
  (truncatedPowerCost_uniform p hp n).continuous.subtype_mk _

noncomputable def truncatedPowerCostBCF {E : Type*} [PseudoMetricSpace E] (p : ℝ) (hp : 0 ≤ p) (n : ℕ) :
    BoundedContinuousFunction (E × E) NNReal :=
  BoundedContinuousFunction.mkOfBound ⟨truncatedPowerCostNN p n,truncatedPowerCostNN_continuous p hp n⟩
    (((n : ℝ)+1)^p) (by
      intro x y
      change |truncatedPowerCost p n x - truncatedPowerCost p n y| ≤ ((n : ℝ)+1)^p
      have hx0 := truncatedPowerCost_nonnegative p n x
      have hy0 := truncatedPowerCost_nonnegative p n y
      have hx := truncatedPowerCost_bound p hp n x
      have hy := truncatedPowerCost_bound p hp n y
      apply abs_le.mpr
      constructor <;> linarith)

lemma truncatedPowerCost_integral_continuous {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (p : ℝ) (hp : 0 ≤ p) (n : ℕ) :
    Continuous (fun π : ProbabilityMeasure (E × E) => ∫⁻ z : E × E, ENNReal.ofReal (truncatedPowerCost p n z) ∂(π : Measure (E × E))) := by
  have h := ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction (truncatedPowerCostBCF (E := E) p hp n)
  have he : (fun π : ProbabilityMeasure (E × E) => ∫⁻ z : E × E,
      ENNReal.ofReal (truncatedPowerCost p n z) ∂(π : Measure (E × E))) =
      (fun π : ProbabilityMeasure (E × E) => ∫⁻ z : E × E,
        (truncatedPowerCostBCF p hp n z : ENNReal) ∂(π : Measure (E × E))) := by
    funext π
    apply lintegral_congr
    intro z
    exact ENNReal.ofReal_eq_coe_nnreal (truncatedPowerCost_nonnegative p n z)
  rw [he]
  exact h

lemma truncatedPowerCost_integral_monotone {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (π : Measure (E × E)) (p : ℝ) (hp : 0 ≤ p) :
    Monotone (fun n => ∫⁻ z, ENNReal.ofReal (truncatedPowerCost p n z) ∂π) := by
  intro n m hnm
  apply lintegral_mono
  intro z
  exact ENNReal.ofReal_le_ofReal (truncatedPowerCost_monotone p hp z hnm)

#print axioms truncatedPowerCostNN_continuous
#print axioms truncatedPowerCost_integral_continuous
#print axioms truncatedPowerCost_integral_monotone
lemma truncatedPowerCost_integral_iSup {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (π : Measure (E × E)) (p : ℝ) (hp : 0 ≤ p) :
    (⨆ n, ∫⁻ z, ENNReal.ofReal (truncatedPowerCost p n z) ∂π) =
      ∫⁻ z, ENNReal.ofReal ((dist z.1 z.2)^p) ∂π := by
  rw [← lintegral_iSup (μ := π) (f := fun n z => ENNReal.ofReal (truncatedPowerCost p n z)) (fun n => ENNReal.continuous_ofReal.measurable.comp
    (truncatedPowerCost_uniform p hp n).continuous.measurable)
    (show Monotone (fun (n : ℕ) (z : E × E) => ENNReal.ofReal (truncatedPowerCost p n z)) from
      fun n m hnm z => ENNReal.ofReal_le_ofReal (truncatedPowerCost_monotone p hp z hnm))]
  apply lintegral_congr
  intro z
  exact truncatedPowerCost_iSup p hp z

#print axioms truncatedPowerCost_integral_iSup
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichProbabilityInf
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma probabilityCouplings_iff_maps {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (Q Q' : ProbabilityMeasure E) (π : ProbabilityMeasure (E × E)) :
    π ∈ probabilityCouplings Q Q' ↔
      (π : Measure (E × E)).map Prod.fst = (Q : Measure E) ∧
      (π : Measure (E × E)).map Prod.snd = (Q' : Measure E) := by
  constructor
  · intro h
    exact ⟨congrArg ProbabilityMeasure.toMeasure h.1,congrArg ProbabilityMeasure.toMeasure h.2⟩
  · intro h
    exact ⟨Subtype.ext h.1,Subtype.ext h.2⟩

lemma couplingCostInf_eq_probabilityInf {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (Q Q' : ProbabilityMeasure E) (f : E × E → ENNReal) :
    couplingCostInf (Q : Measure E) (Q' : Measure E) f =
      ⨅ (π : ProbabilityMeasure (E × E)) (_ : π ∈ probabilityCouplings Q Q'), ∫⁻ z, f z ∂π := by
  apply le_antisymm
  · refine le_iInf fun π => le_iInf fun hπ => ?_
    exact iInf_le_of_le (π : Measure (E × E))
      (iInf_le_of_le ((probabilityCouplings_iff_maps Q Q' π).mp hπ) le_rfl)
  · refine le_iInf fun μ => le_iInf fun hμ => ?_
    letI : IsProbabilityMeasure μ := coupling_probability_from_fst μ (Q : Measure E) hμ.1
    let π : ProbabilityMeasure (E × E) := ⟨μ,inferInstance⟩
    have hπ : π ∈ probabilityCouplings Q Q' :=
      (probabilityCouplings_iff_maps Q Q' π).mpr hμ
    exact iInf_le_of_le π (iInf_le_of_le hπ le_rfl)

#print axioms probabilityCouplings_iff_maps
#print axioms couplingCostInf_eq_probabilityInf
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichCompleteStrong
set_option autoImplicit false
open MeasureTheory TopologicalSpace
namespace DualityCodex

lemma complete_power_cost_inf_truncations {E : Type*} [MetricSpace E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q Q' : ProbabilityMeasure E) (p : ℝ) (hp : 0 ≤ p) :
    couplingCostInf (Q : Measure E) (Q' : Measure E) (fun z => ENNReal.ofReal ((dist z.1 z.2)^p)) =
      ⨆ n, couplingCostInf (Q : Measure E) (Q' : Measure E)
        (fun z => ENNReal.ofReal (truncatedPowerCost p n z)) := by
  rw [couplingCostInf_eq_probabilityInf]
  simp_rw [← truncatedPowerCost_integral_iSup _ p hp]
  rw [compact_monotone_iInf_iSup (probabilityCouplings Q Q') (probabilityCouplings_compact Q Q')
    (fun n (π : ProbabilityMeasure (E × E)) => ∫⁻ z : E × E, ENNReal.ofReal (truncatedPowerCost p n z) ∂(π : Measure (E × E)))
    (fun n => truncatedPowerCost_integral_continuous p hp n)
    (fun π => truncatedPowerCost_integral_monotone (π : Measure (E × E)) p hp)]
  simp_rw [← couplingCostInf_eq_probabilityInf]

lemma boundedCostDualSup_mono {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (Q Q' : Measure E) (k l : E × E → ℝ) (hkl : ∀ z, k z ≤ l z) :
    boundedCostDualSup Q Q' k ≤ boundedCostDualSup Q Q' l := by
  refine iSup_le fun Φ => iSup_le fun Ψ => iSup_le fun hc => ?_
  exact le_iSup_of_le Φ (le_iSup_of_le Ψ (le_iSup_of_le
    (show ∀ x y, Ψ x-Φ y ≤ l (x,y) from fun x y => (hc x y).trans (hkl (x,y))) le_rfl))

#print axioms complete_power_cost_inf_truncations
#print axioms boundedCostDualSup_mono
lemma complete_power_cost_strong_duality {E : Type*} [MetricSpace E] [CompleteSpace E] [Nonempty E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] (p : ℝ) (hp : 0 < p) :
    (couplingCostInf Q Q' (fun z => ENNReal.ofReal ((dist z.1 z.2)^p)) : EReal) =
      boundedCostDualSup Q Q' (fun z => (dist z.1 z.2)^p) := by
  have hnonnegative : ∀ x y : E, 0 ≤ (dist x y)^p := fun x y => Real.rpow_nonneg dist_nonneg p
  have htrunc : ∀ n, (couplingCostInf Q Q' (fun z => ENNReal.ofReal (truncatedPowerCost p n z)) : EReal) ≤
      boundedCostDualSup Q Q' (fun z => (dist z.1 z.2)^p) := by
    intro n
    have hs := bounded_uniform_cost_strong_duality Q Q' (truncatedPowerCost p n)
      (truncatedPowerCost_uniform p hp.le n) (((n : ℝ)+1)^p)
      (Real.rpow_nonneg (by positivity) p)
      (fun x y => truncatedPowerCost_nonnegative p n (x,y))
      (fun x y => truncatedPowerCost_bound p hp.le n (x,y))
      (truncatedPowerCost_diag p hp n)
    have he : (fun z : E × E => ENNReal.ofReal (truncatedPowerCost p n (z.2,z.1))) =
        (fun z => ENNReal.ofReal (truncatedPowerCost p n z)) := by
      funext z
      rw [truncatedPowerCost_swap]
    rw [he] at hs
    exact hs.trans_le (boundedCostDualSup_mono Q Q' _ _ (truncatedPowerCost_le_full p hp.le n))
  let Qp : ProbabilityMeasure E := ⟨Q,inferInstance⟩
  let Qp' : ProbabilityMeasure E := ⟨Q',inferInstance⟩
  have hlim := complete_power_cost_inf_truncations Qp Qp' p hp.le
  change couplingCostInf Q Q' (fun z => ENNReal.ofReal ((dist z.1 z.2)^p)) =
    ⨆ n, couplingCostInf Q Q' (fun z => ENNReal.ofReal (truncatedPowerCost p n z)) at hlim
  apply le_antisymm
  · by_contra hn
    obtain ⟨r,hrS,hrP⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
    have hr0 : 0 ≤ r := EReal.coe_le_coe_iff.mp
      ((bounded_cost_dual_nonnegative Q Q' _ hnonnegative).trans hrS.le)
    have hrNN : ENNReal.ofReal r < couplingCostInf Q Q' (fun z => ENNReal.ofReal ((dist z.1 z.2)^p)) := by
      apply EReal.coe_ennreal_lt_coe_ennreal_iff.mp
      simpa only [EReal.coe_ennreal_ofReal,max_eq_left hr0] using hrP
    rw [hlim] at hrNN
    obtain ⟨n,hn⟩ := lt_iSup_iff.mp hrNN
    have hnE := EReal.coe_ennreal_lt_coe_ennreal_iff.mpr hn
    rw [EReal.coe_ennreal_ofReal,max_eq_left hr0] at hnE
    exact (not_lt_of_ge hrS.le) (hnE.trans_le (htrunc n))
  · have hw := bounded_cost_dual_weak Q Q' (fun z : E × E => (dist z.1 z.2)^p) hnonnegative
    change boundedCostDualSup Q Q' (fun z => (dist z.1 z.2)^p) ≤
      (couplingCostInf Q Q' (fun z => ENNReal.ofReal ((dist z.2 z.1)^p)) : EReal) at hw
    have he : (fun z : E × E => ENNReal.ofReal ((dist z.2 z.1)^p)) =
        (fun z => ENNReal.ofReal ((dist z.1 z.2)^p)) := by
      funext z
      rw [dist_comm]
    rw [he] at hw
    exact hw

#print axioms complete_power_cost_strong_duality
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichDualRestrict
set_option autoImplicit false
open MeasureTheory
namespace DualityCodex

lemma bounded_power_dual_restrict_isometry {E Z : Type*} [PseudoMetricSpace E] [PseudoMetricSpace Z]
    [MeasurableSpace E] [MeasurableSpace Z] [BorelSpace E] [BorelSpace Z]
    (f : E → Z) (hf : Isometry f) (hfm : Measurable f) (Q Q' : Measure E) (p : ℝ) :
    boundedCostDualSup (Q.map f) (Q'.map f) (fun z => (dist z.1 z.2)^p) ≤
      boundedCostDualSup Q Q' (fun z => (dist z.1 z.2)^p) := by
  refine iSup_le fun Φ => iSup_le fun Ψ => iSup_le fun hc => ?_
  let ΦE := Φ.compContinuous ⟨f,hf.continuous⟩
  let ΨE := Ψ.compContinuous ⟨f,hf.continuous⟩
  have hfeas : ∀ x y, ΨE x - ΦE y ≤ (dist x y)^p := by
    intro x y
    have h := hc (f x) (f y)
    change Ψ (f x) - Φ (f y) ≤ (dist (f x) (f y))^p at h
    rw [hf.dist_eq] at h
    exact h
  have hΦ : (∫ x, Φ (f x) ∂Q) = ∫ z, Φ z ∂Q.map f :=
    (integral_map_of_stronglyMeasurable hfm Φ.continuous.measurable.stronglyMeasurable).symm
  have hΨ : (∫ x, Ψ (f x) ∂Q') = ∫ z, Ψ z ∂Q'.map f :=
    (integral_map_of_stronglyMeasurable hfm Ψ.continuous.measurable.stronglyMeasurable).symm
  have hl : ((∫ x, ΨE x ∂Q' - ∫ x, ΦE x ∂Q : ℝ) : EReal) ≤
      boundedCostDualSup Q Q' (fun z => (dist z.1 z.2)^p) :=
    le_iSup_of_le ΦE (le_iSup_of_le ΨE (le_iSup_of_le hfeas le_rfl))
  change ((∫ x, Ψ (f x) ∂Q' - ∫ x, Φ (f x) ∂Q : ℝ) : EReal) ≤ _ at hl
  rw [hΦ,hΨ] at hl
  exact hl

#print axioms bounded_power_dual_restrict_isometry
end DualityCodex

-- Complete local proof: Solutions.Duality_KantorovichFullStrong
set_option autoImplicit false
open MeasureTheory TopologicalSpace
namespace DualityCodex

lemma power_cost_strong_duality {E : Type*} [MetricSpace E] [Nonempty E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] (p : ℝ) (hp : 1 ≤ p) :
    (couplingCostInf Q Q' (fun z => ENNReal.ofReal ((dist z.1 z.2)^p)) : EReal) =
      boundedCostDualSup Q Q' (fun z => (dist z.1 z.2)^p) := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let Z := UniformSpace.Completion E
  letI : MeasurableSpace Z := borel Z
  letI : BorelSpace Z := ⟨rfl⟩
  let x0 : E := Classical.choice inferInstance
  let f : E → Z := fun x => (x : UniformSpace.Completion E)
  letI : Nonempty Z := ⟨f x0⟩
  have hf : Isometry f := UniformSpace.Completion.coe_isometry
  have hfd : DenseRange f := UniformSpace.Completion.denseRange_coe
  have hfm : Measurable f := hf.continuous.measurable
  letI : IsProbabilityMeasure (Q.map f) := Q.isProbabilityMeasure_map hfm.aemeasurable
  letI : IsProbabilityMeasure (Q'.map f) := Q'.isProbabilityMeasure_map hfm.aemeasurable
  have hi := dense_isometry_cost_inf_le f hf hfm hfd Q Q' p hp x0
  have hc := complete_power_cost_strong_duality (Q.map f) (Q'.map f) p hp0
  have hs := bounded_power_dual_restrict_isometry f hf hfm Q Q' p
  apply le_antisymm
  · exact (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hi).trans (hc.trans_le hs)
  · have hn : ∀ x y : E, 0 ≤ (dist x y)^p := fun x y => Real.rpow_nonneg dist_nonneg p
    have hw := bounded_cost_dual_weak Q Q' (fun z : E × E => (dist z.1 z.2)^p) hn
    change boundedCostDualSup Q Q' (fun z => (dist z.1 z.2)^p) ≤
      (couplingCostInf Q Q' (fun z => ENNReal.ofReal ((dist z.2 z.1)^p)) : EReal) at hw
    have he : (fun z : E × E => ENNReal.ofReal ((dist z.2 z.1)^p)) =
        (fun z => ENNReal.ofReal ((dist z.1 z.2)^p)) := by
      funext z
      rw [dist_comm]
    rw [he] at hw
    exact hw

#print axioms power_cost_strong_duality
lemma kantorovich_power_norm_duality {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E] [SecondCountableTopology E] (p : ℝ) (hp : 1 ≤ p)
    (Q Q' : Measure E) [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] :
    ((WassersteinDRO.Duality.wassersteinDistance p Q Q' ^ p : ENNReal) : EReal) =
      ⨆ (φ : BoundedContinuousFunction E ℝ) (ψ : BoundedContinuousFunction E ℝ)
        (_ : ∀ x y : E, ψ x - φ y ≤ ‖x-y‖^p),
        ((∫ x, ψ x ∂Q' - ∫ x, φ x ∂Q : ℝ) : EReal) := by
  rw [wasserstein_power_eq_cost_inf p (lt_of_lt_of_le zero_lt_one hp) Q Q']
  simpa only [couplingCostInf,boundedCostDualSup,dist_eq_norm] using power_cost_strong_duality Q Q' p hp

#print axioms kantorovich_power_norm_duality
end DualityCodex

-- Complete local proof: Solutions.Sol_WassersteinDRO_Duality_dual_kantorovich_problem
set_option autoImplicit false
open MeasureTheory WassersteinDRO.Duality

theorem solution {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
    (p : ℝ) (hp : 1 ≤ p) (Q Q' : Measure E)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] :
    ((wassersteinDistance p Q Q' ^ p : ENNReal) : EReal) =
      ⨆ (φ : BoundedContinuousFunction E ℝ) (ψ : BoundedContinuousFunction E ℝ)
          (_ : ∀ x y : E, ψ x - φ y ≤ ‖x - y‖ ^ p),
        ((∫ x, ψ x ∂Q' - ∫ x, φ x ∂Q : ℝ) : EReal) := by
  exact DualityCodex.kantorovich_power_norm_duality p hp Q Q'

#print axioms solution
