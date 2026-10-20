-- Prove2me | solution 1 for PermLimits.Cauchy.convergent_iff_cauchy_rectangular
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T04:44:09.258912+00:00
-- url     : https://prove2.me/submissions/0085f817-5ddb-4cc6-9f42-4770d3f76a02

/-
SPDX-License-Identifier: Apache-2.0

Corrected Theorem 1.8: permutation convergence iff rectangular Cauchy convergence.
Mathematical source: C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth,
R. M. Sampaio, "Limits of permutation sequences", arXiv:1103.5844v2.

This formalization reuses the author's previously checked Apache-2.0
permutation-limit empirical-law and pattern-continuity infrastructure.
New contributions include full pattern-law identification via mixed moments,
the literal native step-function/empirical-CDF estimate, and the exact
rectangular Cauchy equivalence. Mathlib retains its own Apache-2.0 attribution.
-/

import Definitions.Def_PermLimits_Cauchy_RectCauchy
import Definitions.Def_PermLimits_Shared_ConvergesTo
import Definitions.Def_PermLimits_Shared_LimitMeasure
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_PermDensity
import Mathlib


/- Source module: Canonical -/
section

end

/- Source module: Shared -/
section

noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared

def UniformMarginals (μ : ProbabilityMeasure (I × I)) : Prop :=
  (μ : Measure (I × I)).map Prod.fst = volume ∧
  (μ : Measure (I × I)).map Prod.snd = volume

def patternProbability {k : ℕ} (μ : ProbabilityMeasure (I × I))
    (τ : Equiv.Perm (Fin k)) : ℝ :=
  (Measure.pi fun _ : Fin k => (μ : Measure (I × I))).real (patternEvent τ)

def gridPoint {n : ℕ} (i : Fin n) : I :=
  ⟨((i.val : ℝ) + 1) / n, by
    have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
    constructor
    · positivity
    · apply (div_le_one hn).2
      exact_mod_cast i.isLt⟩

def empiricalLaw {n : ℕ} (π : Equiv.Perm (Fin n)) : ProbabilityMeasure (I × I) := by
  classical
  by_cases hn : 0 < n
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let ν : ProbabilityMeasure (Fin n) := ⟨(PMF.uniformOfFintype (Fin n)).toMeasure,
      inferInstance⟩
    exact ν.map (measurable_of_finite (fun i => (gridPoint i, gridPoint (π i)))).aemeasurable
  · exact ⟨Measure.dirac (0, 0), inferInstance⟩

end PermutationLimitProof
end
end

/- Source module: PatternCounting -/
section

noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared Set

abbrev Occurrence {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :=
  {x : Fin k → Fin n // StrictMono x ∧ ∀ i j, (π (x i) < π (x j) ↔ τ i < τ j)}

abbrev PatternTuple {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :=
  {x : Fin k → Fin n // ∃ ρ : Equiv.Perm (Fin k),
    StrictMono (x ∘ ρ) ∧ ∀ i j, (π (x (ρ i)) < π (x (ρ j)) ↔ τ i < τ j)}

def occurrenceTuple {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    (p : Occurrence τ π × Equiv.Perm (Fin k)) : PatternTuple τ π :=
  ⟨p.1.val ∘ p.2.symm, p.2, by simpa only [Function.comp_def, Equiv.symm_apply_apply] using p.1.property⟩

lemma occurrenceTuple_bijective {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    Function.Bijective (occurrenceTuple τ π) := by
  constructor
  · rintro ⟨x,ρ⟩ ⟨y,η⟩ h
    have he : x.val ∘ ρ.symm = y.val ∘ η.symm := congrArg Subtype.val h
    have hr : Set.range x.val = Set.range y.val := by
      have hh := congrArg Set.range he
      simpa only [ρ.symm.surjective.range_comp, η.symm.surjective.range_comp] using hh
    have hxy : x = y := Subtype.ext ((x.property.1.range_inj y.property.1).mp hr)
    subst y
    have hrs : ρ.symm = η.symm := by
      apply Equiv.ext
      intro i
      exact x.property.1.injective (congrFun he i)
    have hρη : ρ = η := by simpa using congrArg Equiv.symm hrs
    subst η
    rfl
  · rintro ⟨x,ρ,hx,hy⟩
    refine ⟨(⟨x ∘ ρ, hx, hy⟩,ρ), ?_⟩
    apply Subtype.ext
    funext i
    exact congrArg x (ρ.apply_symm_apply i)

lemma patternTuple_card {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    Fintype.card (PatternTuple τ π) = occurrences τ π * Nat.factorial k := by
  classical
  have h := Fintype.card_congr (Equiv.ofBijective (occurrenceTuple τ π)
    (occurrenceTuple_bijective τ π))
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin] at h
  have ho : Fintype.card (Occurrence τ π) = occurrences τ π := by
    change Fintype.card {x : Fin k → Fin n // _} = _
    rw [Fintype.card_subtype]
    unfold occurrences
    congr 1
  rw [ho] at h
  exact h.symm

lemma gridPoint_strictMono {n : ℕ} : StrictMono (@gridPoint n) := by
  intro i j hij
  change ((i.val : ℝ)+1)/n < ((j.val : ℝ)+1)/n
  exact (div_lt_div_iff_of_pos_right (by exact_mod_cast i.pos)).mpr
    (by exact_mod_cast Nat.add_lt_add_right hij 1)

lemma empirical_pattern_iff {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    (x : Fin k → Fin n) :
    (fun i => (gridPoint (x i), gridPoint (π (x i)))) ∈ patternEvent τ ↔
    ∃ ρ : Equiv.Perm (Fin k), StrictMono (x ∘ ρ) ∧
      ∀ i j, (π (x (ρ i)) < π (x (ρ j)) ↔ τ i < τ j) := by
  simp only [patternEvent, mem_ofPred_eq, gridPoint_strictMono.lt_iff_lt, StrictMono,
    Function.comp_def]

end PermutationLimitProof
end
end

/- Source module: PatternTopology -/
section

namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared Set

lemma frontier_finite_union {α ι : Type*} [TopologicalSpace α] (s : Finset ι)
    (A : ι → Set α) : frontier (⋃ i ∈ s, A i) ⊆ ⋃ i ∈ s, frontier (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
    intro x hx
    rcases frontier_union_subset (A i) (⋃ j ∈ s, A j) hx with hx | hx
    · exact Or.inl hx.1
    · exact Or.inr (ih hx.2)

lemma frontier_finite_iUnion {α ι : Type*} [TopologicalSpace α] [Fintype ι]
    (A : ι → Set α) : frontier (⋃ i, A i) ⊆ ⋃ i, frontier (A i) := by
  simpa using frontier_finite_union (Finset.univ : Finset ι) A

lemma frontier_finite_iInter {α ι : Type*} [TopologicalSpace α] [Fintype ι]
    (A : ι → Set α) : frontier (⋂ i, A i) ⊆ ⋃ i, frontier (A i) := by
  simpa only [← compl_iInter, frontier_compl] using
    frontier_finite_iUnion (fun i => (A i)ᶜ)

lemma patternEvent_chain {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    patternEvent τ = {p | ∃ ρ : Equiv.Perm (Fin k),
      StrictMono (fun i => (p (ρ i)).1) ∧
      StrictMono (fun i => (p (ρ (τ.symm i))).2)} := by
  ext p
  constructor
  · rintro ⟨ρ, hx, hy⟩
    refine ⟨ρ, hx, ?_⟩
    intro i j hij
    exact (hy (τ.symm i) (τ.symm j)).mpr (by simpa using hij)
  · rintro ⟨ρ, hx, hy⟩
    refine ⟨ρ, hx, ?_⟩
    intro i j
    simpa using (hy.lt_iff_lt (a := τ i) (b := τ j))

abbrev OrderedPair (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

def horizontalChain {k : ℕ} (ρ : Equiv.Perm (Fin k)) : Set (Fin k → I × I) :=
  ⋂ q : OrderedPair k, {p | (p (ρ q.val.1)).1 < (p (ρ q.val.2)).1}

def verticalChain {k : ℕ} (ρ : Equiv.Perm (Fin k)) : Set (Fin k → I × I) :=
  ⋂ q : OrderedPair k, {p | (p (ρ q.val.1)).2 < (p (ρ q.val.2)).2}

lemma patternEvent_union {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    patternEvent τ = ⋃ ρ : Equiv.Perm (Fin k),
      horizontalChain ρ ∩ verticalChain (τ.symm.trans ρ) := by
  rw [patternEvent_chain]
  ext p
  simp only [mem_ofPred_eq, mem_iUnion, horizontalChain, verticalChain, mem_inter_iff,
    mem_iInter, Equiv.trans_apply]
  constructor
  · rintro ⟨ρ, hx, hy⟩
    exact ⟨ρ, fun q => hx q.property, fun q => hy q.property⟩
  · rintro ⟨ρ, hx, hy⟩
    exact ⟨ρ, fun i j hij => hx ⟨(i,j),hij⟩, fun i j hij => hy ⟨(i,j),hij⟩⟩

lemma patternEvent_isOpen {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    IsOpen (patternEvent τ) := by
  rw [patternEvent_union]
  apply isOpen_iUnion
  intro ρ
  apply IsOpen.inter
  · exact isOpen_iInter_of_finite fun q =>
      isOpen_lt (continuous_apply _ |>.fst) (continuous_apply _ |>.fst)
  · exact isOpen_iInter_of_finite fun q =>
      isOpen_lt (continuous_apply _ |>.snd) (continuous_apply _ |>.snd)

lemma patternEvent_frontier_subset {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    frontier (patternEvent τ) ⊆ {p | ∃ i j : Fin k, i ≠ j ∧
      ((p i).1 = (p j).1 ∨ (p i).2 = (p j).2)} := by
  rw [patternEvent_union]
  intro p hp
  obtain ⟨ρ, hρ⟩ := mem_iUnion.mp (frontier_finite_iUnion _ hp)
  rcases frontier_inter_subset _ _ hρ with hx | hy
  · obtain ⟨q, hq⟩ := mem_iUnion.mp (frontier_finite_iInter _ hx.1)
    exact ⟨ρ q.val.1, ρ q.val.2, fun h => (ne_of_lt q.property) (ρ.injective h),
      Or.inl (frontier_lt_subset_eq (continuous_apply _ |>.fst)
        (continuous_apply _ |>.fst) hq)⟩
  · obtain ⟨q, hq⟩ := mem_iUnion.mp (frontier_finite_iInter _ hy.2)
    exact ⟨ρ (τ.symm q.val.1), ρ (τ.symm q.val.2),
      fun h => (ne_of_lt q.property) (τ.symm.injective (ρ.injective h)),
      Or.inr (frontier_lt_subset_eq (continuous_apply _ |>.snd)
        (continuous_apply _ |>.snd) hq)⟩

end PermutationLimitProof
end

/- Source module: EmpiricalIntegrals -/
section

noncomputable section
namespace PermutationLimitProof
open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

lemma empiricalLaw_eq {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) :
    (empiricalLaw π : Measure (I × I)) =
      (by letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
          exact (PMF.uniformOfFintype (Fin n)).toMeasure.map
            (fun i => (gridPoint i, gridPoint (π i)))) := by
  simp only [empiricalLaw, hn, ↓reduceDIte]
  rfl

lemma empirical_integral {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n))
    (f : I × I → ℝ) (hf : Measurable f) :
    ∫ z, f z ∂(empiricalLaw π : Measure (I × I)) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, f (gridPoint i, gridPoint (π i)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [empiricalLaw_eq hn, integral_map (measurable_of_finite _).aemeasurable
    hf.aestronglyMeasurable, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, Finset.mul_sum]

lemma empirical_first_integral {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n))
    (f : I → ℝ) (hf : Measurable f) :
    ∫ z, f z.1 ∂(empiricalLaw π : Measure (I × I)) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, f (gridPoint i) :=
  empirical_integral hn π _ (hf.comp measurable_fst)

lemma empirical_second_integral {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n))
    (f : I → ℝ) (hf : Measurable f) :
    ∫ z, f z.2 ∂(empiricalLaw π : Measure (I × I)) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, f (gridPoint i) := by
  have h := empirical_integral hn π (fun z => f z.2) (hf.comp measurable_snd)
  rw [h]
  congr 1
  exact Equiv.sum_comp π (fun i => f (gridPoint i))

end PermutationLimitProof
end
end

/- Source module: EmpiricalPatterns -/
section

noncomputable section
namespace PermutationLimitProof
open MeasureTheory ProbabilityTheory unitInterval PermLimits.Shared Set
open scoped ENNReal

lemma pi_uniform_fin (k n : ℕ) [NeZero n] :
    (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin n)).toMeasure) =
      (PMF.uniformOfFintype (Fin k → Fin n)).toMeasure := by
  apply Measure.ext_of_singleton
  intro x
  simp only [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_fin, Fintype.card_fun, Finset.prod_const,
    Finset.card_univ, Nat.cast_pow, ENNReal.inv_pow]

lemma empirical_pattern_probability {k n : ℕ} (hn : 0<n)
    (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    patternProbability (empiricalLaw π) τ =
      (occurrences τ π : ℝ) * Nat.factorial k / (n : ℝ)^k := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let g : Fin n → I × I := fun i => (gridPoint i, gridPoint (π i))
  have hg : Measurable g := measurable_of_finite _
  have hm : Measure.pi (fun _ : Fin k => (empiricalLaw π : Measure (I × I))) =
      (PMF.uniformOfFintype (Fin k → Fin n)).toMeasure.map (fun x i => g (x i)) := by
    simp_rw [empiricalLaw_eq hn]
    rw [← Measure.pi_map_pi (fun _ : Fin k => hg.aemeasurable), pi_uniform_fin]
  have hc : Fintype.card {x : Fin k → Fin n | (fun i => g (x i)) ∈ patternEvent τ} =
      occurrences τ π * Nat.factorial k := by
    calc
      _ = Fintype.card (PatternTuple τ π) :=
        Fintype.card_congr (Equiv.subtypeEquivRight (empirical_pattern_iff τ π))
      _ = _ := patternTuple_card τ π
  have hs : MeasurableSet ((fun x : Fin k → Fin n => fun i => g (x i)) ⁻¹' patternEvent τ) :=
    (patternEvent_isOpen τ).measurableSet.preimage (measurable_of_finite _)
  rw [patternProbability, measureReal_def, hm,
    Measure.map_apply (measurable_of_finite _) (patternEvent_isOpen τ).measurableSet,
    PMF.toMeasure_uniformOfFintype_apply _ hs]
  change (↑(Fintype.card {x : Fin k → Fin n | (fun i => g (x i)) ∈ patternEvent τ}) /
    ↑(Fintype.card (Fin k → Fin n)) : ℝ≥0∞).toReal = _
  rw [hc]
  simp only [Fintype.card_fun, Fintype.card_fin, ENNReal.toReal_div,
    Nat.cast_mul, Nat.cast_pow, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]

end PermutationLimitProof
end
end

/- Source module: PatternContinuity -/
section

namespace PermutationLimitProof
open MeasureTheory ProbabilityTheory unitInterval PermLimits.Shared Set Filter Topology

lemma unit_diagonal_null :
    (volume.prod volume : Measure (I × I)) {p | p.1 = p.2} = 0 := by
  apply Measure.measure_prod_null_of_ae_null measurableSet_diagonal
  exact Filter.Eventually.of_forall fun x => by
    have he : Prod.mk x ⁻¹' {p : I × I | p.1=p.2} = {x} := by ext y; simp [eq_comm]
    change volume (Prod.mk x ⁻¹' {p : I × I | p.1=p.2}) = 0
    rw [he]
    simp

lemma coordinate_collision_null {k : ℕ} (μ : ProbabilityMeasure (I × I))
    (c : I × I → I) (hc : Measurable c) (hm : (μ : Measure (I × I)).map c = volume)
    {i j : Fin k} (hij : i ≠ j) :
    (Measure.pi fun _ : Fin k => (μ : Measure (I × I)))
      {p | c (p i) = c (p j)} = 0 := by
  let ν := Measure.pi fun _ : Fin k => (μ : Measure (I × I))
  have hf (a : Fin k) : Measurable (fun p : Fin k → I × I => c (p a)) :=
    hc.comp (measurable_pi_apply a)
  have hind := (iIndepFun_pi (μ := fun _ : Fin k => (μ : Measure (I × I)))
    (X := fun _ => c) (fun _ => hc.aemeasurable)).indepFun hij
  have hmap (a : Fin k) : ν.map (fun p => c (p a)) = volume := by
    rw [show (fun p : Fin k → I × I => c (p a)) = c ∘ Function.eval a from rfl,
      ← Measure.map_map hc (measurable_pi_apply a),
      (measurePreserving_eval (fun _ : Fin k => (μ : Measure (I × I))) a).map_eq, hm]
  have hpair := hind.map_prod_eq_prod_map_map (hf i).aemeasurable (hf j).aemeasurable
  change ν.map (fun p => (c (p i), c (p j))) = _ at hpair
  rw [hmap i, hmap j] at hpair
  have hv := congrArg (fun η : Measure (I × I) => η {p | p.1=p.2}) hpair
  rw [Measure.map_apply ((hf i).prodMk (hf j))
    (show MeasurableSet {p : I × I | p.1=p.2} from measurableSet_diagonal),
    unit_diagonal_null] at hv
  exact hv

lemma patternEvent_frontier_null {k : ℕ} (μ : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (τ : Equiv.Perm (Fin k)) :
    (Measure.pi fun _ : Fin k => (μ : Measure (I × I))) (frontier (patternEvent τ)) = 0 := by
  let ν := Measure.pi fun _ : Fin k => (μ : Measure (I × I))
  have hz : ν {p | ∃ i j : Fin k, i ≠ j ∧
      ((p i).1 = (p j).1 ∨ (p i).2 = (p j).2)} = 0 := by
    have he : {p : Fin k → I × I | ∃ i j : Fin k, i ≠ j ∧
        ((p i).1 = (p j).1 ∨ (p i).2 = (p j).2)} =
        ⋃ i : Fin k, ⋃ j : Fin k, ⋃ (_ : i ≠ j),
          ({p | (p i).1 = (p j).1} ∪ {p | (p i).2 = (p j).2}) := by ext p; simp
    rw [he]
    apply measure_iUnion_null
    intro i
    apply measure_iUnion_null
    intro j
    apply measure_iUnion_null
    intro hij
    exact measure_union_null
      (coordinate_collision_null μ Prod.fst measurable_fst hμ.1 hij)
      (coordinate_collision_null μ Prod.snd measurable_snd hμ.2 hij)
  exact measure_mono_null (patternEvent_frontier_subset τ) hz

lemma patternProbability_tendsto {ι : Type*} {l : Filter ι} {μs : ι → ProbabilityMeasure (I × I)}
    {μ : ProbabilityMeasure (I × I)} (h : Tendsto μs l (𝓝 μ)) (hμ : UniformMarginals μ)
    {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    Tendsto (fun a => patternProbability (μs a) τ) l (𝓝 (patternProbability μ τ)) := by
  have hp : Tendsto (fun a => ProbabilityMeasure.pi (fun _ : Fin k => μs a)) l
      (𝓝 (ProbabilityMeasure.pi (fun _ : Fin k => μ))) :=
    ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr fun _ => h)
  have he := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hp
    (patternEvent_frontier_null μ hμ τ)
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp he

end PermutationLimitProof
end

/- Source module: EmpiricalTransfer -/
section

noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval PermLimits.Shared Set Filter Topology

def collisionFactor (k n : ℕ) : ℝ := ∏ i ∈ Finset.range k, (1 - (i : ℝ) / n)

lemma collisionFactor_formula {k n : ℕ} (hn : 0<n) (hk : k≤n) :
    collisionFactor k n = ((Nat.factorial k : ℝ) * Nat.choose n k) / (n : ℝ)^k := by
  have hn' : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  calc
    collisionFactor k n = ∏ i ∈ Finset.range k, ((n-i : ℕ) : ℝ)/(n : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hin : i≤n := (Finset.mem_range.mp hi).le.trans hk
      rw [Nat.cast_sub hin]
      field_simp
    _ = (n.descFactorial k : ℝ) / (n : ℝ)^k := by
      rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range]
      simp
    _ = _ := by rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]

lemma collisionFactor_pos {k n : ℕ} (hn : 0<n) (hk : k≤n) : 0<collisionFactor k n := by
  rw [collisionFactor_formula hn hk]
  have hc : 0<Nat.choose n k := Nat.choose_pos hk
  have hf : 0<Nat.factorial k := Nat.factorial_pos k
  positivity

lemma empirical_pattern_factor {k n : ℕ} (hn : 0<n) (hk : k≤n)
    (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    patternProbability (empiricalLaw π) τ = collisionFactor k n * permDensity τ π := by
  rw [empirical_pattern_probability hn, collisionFactor_formula hn hk, permDensity, if_pos hk]
  have hc : (Nat.choose n k : ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  field_simp

lemma collisionFactor_tendsto (k : ℕ) :
    Tendsto (collisionFactor k) atTop (𝓝 (1 : ℝ)) := by
  have h (i : ℕ) : Tendsto (fun n : ℕ => 1 - (i : ℝ)/n) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ))
  change Tendsto (fun n : ℕ => ∏ i ∈ Finset.range k, (1 - (i : ℝ)/n)) atTop (𝓝 (1 : ℝ))
  simpa only [Finset.prod_const_one] using
    tendsto_finsetProd (Finset.range k) (fun i _ => h i)

lemma empirical_pattern_tendsto_iff (s : ℕ → Σ n, Equiv.Perm (Fin n))
    (hs : Tendsto (fun m => (s m).1) atTop atTop) {k : ℕ}
    (τ : Equiv.Perm (Fin k)) (a : ℝ) :
    Tendsto (fun m => permDensity τ (s m).2) atTop (𝓝 a) ↔
    Tendsto (fun m => patternProbability (empiricalLaw (s m).2) τ) atTop (𝓝 a) := by
  have hf := (collisionFactor_tendsto k).comp hs
  have hn : ∀ᶠ m in atTop, max 1 k ≤ (s m).1 := hs.eventually (eventually_ge_atTop _)
  have he : (fun m => patternProbability (empiricalLaw (s m).2) τ) =ᶠ[atTop]
      (fun m => collisionFactor k (s m).1 * permDensity τ (s m).2) := by
    filter_upwards [hn] with m hm
    exact empirical_pattern_factor (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm))
      ((le_max_right _ _).trans hm) τ (s m).2
  constructor
  · intro hd
    simpa only [one_mul] using (hf.mul hd).congr' he.symm
  · intro hp
    have he' : (fun m => permDensity τ (s m).2) =ᶠ[atTop]
        (fun m => patternProbability (empiricalLaw (s m).2) τ / collisionFactor k (s m).1) := by
      filter_upwards [hn, he] with m hm hem
      have hpos := collisionFactor_pos
        (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hm))
        ((le_max_right _ _).trans hm)
      rw [hem]
      field_simp
    simpa only [div_one] using (hp.div hf one_ne_zero).congr' he'.symm

lemma empirical_weak_implies_densities (s : ℕ → Σ n, Equiv.Perm (Fin n))
    (hs : Tendsto (fun m => (s m).1) atTop atTop)
    {μ : ProbabilityMeasure (I × I)}
    (hweak : Tendsto (fun m => empiricalLaw (s m).2) atTop (𝓝 μ)) (hμ : UniformMarginals μ)
    {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    Tendsto (fun m => permDensity τ (s m).2) atTop (𝓝 (patternProbability μ τ)) :=
  (empirical_pattern_tendsto_iff s hs τ _).mpr (patternProbability_tendsto hweak hμ τ)

end PermutationLimitProof
end
end

/- Source module: GridCells -/
section

noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval Set
open scoped ENNReal

def gridLeft {n : ℕ} (i : Fin n) : I :=
  ⟨(i.val : ℝ) / n, by
    have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
    exact ⟨by positivity, (div_le_one hn).2 (by exact_mod_cast i.isLt.le)⟩⟩

def gridCell {n : ℕ} (i : Fin n) : Set I := Ioc (gridLeft i) (gridPoint i)

lemma gridCell_measurable {n : ℕ} (i : Fin n) : MeasurableSet (gridCell i) := measurableSet_Ioc

lemma mem_gridCell {n : ℕ} (i : Fin n) (x : I) :
    x ∈ gridCell i ↔ (i.val : ℝ) / n < x ∧ (x : ℝ) ≤ ((i.val : ℝ) + 1) / n := Iff.rfl

lemma gridCell_volume {n : ℕ} (i : Fin n) : volume (gridCell i) = (n : ℝ≥0∞)⁻¹ := by
  rw [gridCell, unitInterval.volume_Ioc]
  change ENNReal.ofReal (((i.val : ℝ) + 1) / n - (i.val : ℝ) / n) = _
  have he : ((i.val : ℝ) + 1) / n - (i.val : ℝ) / n = (n : ℝ)⁻¹ := by ring
  rw [he, ENNReal.ofReal_inv_of_pos (by exact_mod_cast i.pos)]
  simp

lemma gridCell_disjoint {n : ℕ} : Pairwise (fun i j : Fin n => Disjoint (gridCell i) (gridCell j)) := by
  intro i j hij
  wlog h : i < j generalizing i j
  · exact (@this j i hij.symm (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hij))).symm
  apply Set.disjoint_left.2
  intro x hxi hxj
  rw [mem_gridCell] at hxi hxj
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  have hij' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
  have hd := div_le_div_of_nonneg_right hij' hn.le
  exact (not_lt_of_ge (hxi.2.trans hd)) hxj.1

lemma gridCell_cover {n : ℕ} (hn : 0 < n) :
    (⋃ i : Fin n, gridCell i) = Ioi (0 : I) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 hx
    have h := (mem_gridCell i x).1 hxi
    have hz : (0 : ℝ) ≤ (i.val : ℝ) / n := by positivity
    exact hz.trans_lt h.1
  · intro hx
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hx' : (x : ℝ) ∈ Ioc ((0 : ℝ) / n) ((n : ℝ) / n) := by
      simpa [hn'.ne'] using (show (0 : ℝ) < x ∧ (x : ℝ) ≤ 1 from ⟨hx, x.2.2⟩)
    have h := Ioc_subset_biUnion_Ioc n (fun j : ℕ => (j : ℝ) / n) (by simpa only [Nat.cast_zero] using hx')
    simp only [mem_iUnion, Finset.mem_range] at h
    obtain ⟨j, hj, hxj⟩ := h
    refine mem_iUnion.2 ⟨⟨j, hj⟩, ?_⟩
    simpa only [mem_gridCell, Set.mem_Ioc, Nat.cast_add, Nat.cast_one] using hxj

lemma gridCell_diameter {n : ℕ} (i : Fin n) {x y : I}
    (hx : x ∈ gridCell i) (hy : y ∈ gridCell i) : dist x y ≤ (n : ℝ)⁻¹ := by
  rw [mem_gridCell] at hx hy
  change |(x : ℝ) - y| ≤ _
  rw [abs_le]
  have he : ((i.val : ℝ) + 1) / n - (i.val : ℝ) / n = (n : ℝ)⁻¹ := by ring
  constructor <;> linarith

end PermutationLimitProof
end
end

/- Source module: UniformGeometry -/
section

noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval Set Filter

lemma volume_ae_pos : ∀ᵐ x : I, 0 < x := by
  rw [ae_iff]
  have hs : {a : I | ¬0 < a} = Iic (0 : I) := by ext a; simp
  rw [hs, unitInterval.volume_Iic]
  norm_num

lemma uniform_ae_pos (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ) :
    ∀ᵐ p ∂(μ : Measure (I × I)), 0 < p.1 ∧ 0 < p.2 := by
  have hx : ∀ᵐ p ∂(μ : Measure (I × I)), 0 < p.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hμ.1]
    exact volume_ae_pos
  have hy : ∀ᵐ p ∂(μ : Measure (I × I)), 0 < p.2 := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hμ.2]
    exact volume_ae_pos
  exact hx.and hy

lemma grid_square_cover (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) :
    ∀ᵐ p ∂(μ : Measure (I × I)), ∃ j : Fin n × Fin n,
      p ∈ gridCell j.1 ×ˢ gridCell j.2 := by
  filter_upwards [uniform_ae_pos μ hμ] with p hp
  have hx : p.1 ∈ ⋃ i : Fin n, gridCell i := by rw [gridCell_cover hn]; exact hp.1
  have hy : p.2 ∈ ⋃ i : Fin n, gridCell i := by rw [gridCell_cover hn]; exact hp.2
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  obtain ⟨j, hj⟩ := mem_iUnion.1 hy
  exact ⟨(i,j), hi, hj⟩

lemma grid_square_disjoint {n : ℕ} : Pairwise (fun i j : Fin n × Fin n =>
    Disjoint (gridCell i.1 ×ˢ gridCell i.2) (gridCell j.1 ×ˢ gridCell j.2)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro p hpi hpj
  by_cases h : i.1 = j.1
  · have h' : i.2 ≠ j.2 := fun he => hij (Prod.ext h he)
    exact Set.disjoint_left.1 (gridCell_disjoint h') hpi.2 hpj.2
  · exact Set.disjoint_left.1 (gridCell_disjoint h) hpi.1 hpj.1

lemma uniform_row_sum (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ∑ j : Fin n, (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j) = (n : ℝ)⁻¹ := by
  have hd : Pairwise (fun j k : Fin n =>
      Disjoint (gridCell i ×ˢ gridCell j) (gridCell i ×ˢ gridCell k)) := by
    intro j k hjk
    exact Set.disjoint_left.2 (fun _ hp hq =>
      Set.disjoint_left.1 (gridCell_disjoint hjk) hp.2 hq.2)
  rw [← measureReal_iUnion_fintype hd (fun j => (gridCell_measurable i).prod (gridCell_measurable j))]
  have he : (⋃ j : Fin n, gridCell i ×ˢ gridCell j) = gridCell i ×ˢ Ioi (0 : I) := by
    rw [← prod_iUnion, gridCell_cover hn]
  rw [he]
  have hae : gridCell i ×ˢ Ioi (0 : I) =ᵐ[(μ : Measure (I × I))] Prod.fst ⁻¹' gridCell i := by
    filter_upwards [uniform_ae_pos μ hμ] with p hp
    change (p.1 ∈ gridCell i ∧ 0 < p.2) = (p.1 ∈ gridCell i)
    simp only [hp.2, and_true]
  rw [measureReal_congr hae]
  have hm := congrArg (fun ξ : Measure I => ξ.real (gridCell i)) hμ.1
  rw [map_measureReal_apply measurable_fst (gridCell_measurable i)] at hm
  rw [hm, measureReal_def, gridCell_volume]
  simp

lemma uniform_column_sum (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ∑ j : Fin n, (μ : Measure (I × I)).real (gridCell j ×ˢ gridCell i) = (n : ℝ)⁻¹ := by
  have hd : Pairwise (fun j k : Fin n =>
      Disjoint (gridCell j ×ˢ gridCell i) (gridCell k ×ˢ gridCell i)) := by
    intro j k hjk
    exact Set.disjoint_left.2 (fun _ hp hq =>
      Set.disjoint_left.1 (gridCell_disjoint hjk) hp.1 hq.1)
  rw [← measureReal_iUnion_fintype hd (fun j => (gridCell_measurable j).prod (gridCell_measurable i))]
  have he : (⋃ j : Fin n, gridCell j ×ˢ gridCell i) = Ioi (0 : I) ×ˢ gridCell i := by
    rw [← iUnion_prod_const, gridCell_cover hn]
  rw [he]
  have hae : Ioi (0 : I) ×ˢ gridCell i =ᵐ[(μ : Measure (I × I))] Prod.snd ⁻¹' gridCell i := by
    filter_upwards [uniform_ae_pos μ hμ] with p hp
    change (0 < p.1 ∧ p.2 ∈ gridCell i) = (p.2 ∈ gridCell i)
    simp only [hp.1, true_and]
  rw [measureReal_congr hae]
  have hm := congrArg (fun ξ : Measure I => ξ.real (gridCell i)) hμ.2
  rw [map_measureReal_apply measurable_snd (gridCell_measurable i)] at hm
  rw [hm, measureReal_def, gridCell_volume]
  simp

end PermutationLimitProof
end
end

/- Source module: GridMatrix -/
section

noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval Set Matrix

def gridMatrix (μ : ProbabilityMeasure (I × I)) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => n * (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j)

lemma gridMatrix_stochastic (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) : gridMatrix μ n ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨fun i j => mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg, ?_, ?_⟩
  · intro i
    simp only [gridMatrix, ← Finset.mul_sum, uniform_row_sum μ hμ hn i, mul_inv_cancel₀ hn']
  · intro j
    simp only [gridMatrix, ← Finset.mul_sum, uniform_column_sum μ hμ hn j, mul_inv_cancel₀ hn']

lemma grid_birkhoff (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) :
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ a, 0 ≤ w a) ∧ (∑ a, w a = 1) ∧
      ∀ i j, (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j) =
        (n : ℝ)⁻¹ * ∑ a, w a * (if a i = j then 1 else 0) := by
  obtain ⟨w, hw, hs, he⟩ := exists_eq_sum_perm_of_mem_doublyStochastic
    (gridMatrix_stochastic μ hμ hn)
  refine ⟨w, hw, hs, ?_⟩
  intro i j
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) he
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, gridMatrix] at h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [h, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]

lemma birkhoff_quadrature {n : ℕ} (μ : ProbabilityMeasure (I × I))
    (w : Equiv.Perm (Fin n) → ℝ)
    (he : ∀ i j, (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j) =
      (n : ℝ)⁻¹ * ∑ a, w a * (if a i = j then 1 else 0))
    (v : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j) * v i j =
      ∑ a, w a * ((n : ℝ)⁻¹ * ∑ i, v i (a i)) := by
  simp_rw [he]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp [mul_assoc, mul_left_comm]

end PermutationLimitProof
end
end

/- Source module: PartitionIntegral -/
section

noncomputable section
namespace PermutationLimitProof
open MeasureTheory Set Filter

lemma finite_partition_integral_bound {α J : Type*} [MeasurableSpace α] [Fintype J]
    [DecidableEq J] (μ : Measure α) [IsProbabilityMeasure μ]
    (S : J → Set α) (hS : ∀ j, MeasurableSet (S j))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hc : ∀ᵐ x ∂μ, ∃ j, x ∈ S j) (v : J → ℝ) (f : α → ℝ)
    (hf : Integrable f μ) (δ : ℝ)
    (ho : ∀ j x, x ∈ S j → |f x - v j| ≤ δ) :
    |(∫ x, f x ∂μ) - ∑ j, μ.real (S j) * v j| ≤ δ := by
  let g : α → ℝ := fun x => ∑ j, (S j).indicator (fun _ => v j) x
  have hg : Integrable g μ := by
    apply integrable_finsetSum
    intro j _
    exact (integrable_const _).indicator (hS j)
  have hgj {j : J} {x : α} (hx : x ∈ S j) : g x = v j := by
    dsimp [g]
    rw [Finset.sum_eq_single j]
    · exact Set.indicator_of_mem hx _
    · intro k _ hkj
      apply Set.indicator_of_notMem
      exact fun hxk => Set.disjoint_left.1 (hd hkj) hxk hx
    · simp
  have hgi : ∫ x, g x ∂μ = ∑ j, μ.real (S j) * v j := by
    rw [integral_finsetSum _ (fun j _ => (integrable_const _).indicator (hS j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_indicator (hS j)]
    simp
  have hb : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ δ := by
    filter_upwards [hc] with x hx
    obtain ⟨j, hj⟩ := hx
    rw [hgj hj, Real.norm_eq_abs]
    exact ho j x hj
  have h := norm_integral_le_of_norm_le_const hb
  rw [integral_sub hf hg, hgi, Real.norm_eq_abs] at h
  simpa using h

end PermutationLimitProof
end
end

/- Source module: GridQuadrature -/
section

noncomputable section
namespace PermutationLimitProof
open scoped BoundedContinuousFunction
open MeasureTheory unitInterval Set Filter Topology

def gridAverage {n : ℕ} (a : Equiv.Perm (Fin n)) (f : I × I → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, f (gridPoint i, gridPoint (a i))

lemma gridPoint_mem {n : ℕ} (i : Fin n) : gridPoint i ∈ gridCell i := by
  rw [mem_gridCell]
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  exact ⟨(div_lt_div_iff_of_pos_right hn).2 (by linarith), le_rfl⟩

lemma grid_pair_dist {n : ℕ} (i j : Fin n) {p : I × I}
    (hp : p ∈ gridCell i ×ˢ gridCell j) :
    dist p (gridPoint i, gridPoint j) ≤ (n : ℝ)⁻¹ := by
  rw [Prod.dist_eq]
  exact max_le (gridCell_diameter i hp.1 (gridPoint_mem i))
    (gridCell_diameter j hp.2 (gridPoint_mem j))

lemma gridAverage_bound {n : ℕ} (hn : 0 < n) (a : Equiv.Perm (Fin n))
    (f : I × I →ᵇ ℝ) : |gridAverage a f| ≤ ‖f‖ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold gridAverage
  rw [abs_mul, abs_of_pos (inv_pos.mpr hn')]
  have hs : |∑ i : Fin n, f (gridPoint i, gridPoint (a i))| ≤ (n : ℝ) * ‖f‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      ∑ i : Fin n, |f (gridPoint i, gridPoint (a i))| ≤ ∑ _i : Fin n, ‖f‖ :=
        Finset.sum_le_sum (fun i _ => f.norm_coe_le_norm _)
      _ = _ := by simp
  calc
    _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ‖f‖) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn'.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]

lemma grid_integral_bound (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) (f : I × I →ᵇ ℝ) (δ : ℝ)
    (ho : ∀ p q : I × I, dist p q ≤ (n : ℝ)⁻¹ → |f p - f q| ≤ δ) :
    |(∫ p, f p ∂(μ : Measure (I × I))) -
      ∑ i : Fin n, ∑ j : Fin n,
        (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j) * f (gridPoint i, gridPoint j)| ≤ δ := by
  have h := finite_partition_integral_bound (μ : Measure (I × I))
    (fun j : Fin n × Fin n => gridCell j.1 ×ˢ gridCell j.2)
    (fun j => (gridCell_measurable j.1).prod (gridCell_measurable j.2))
    grid_square_disjoint (grid_square_cover μ hμ hn)
    (fun j => f (gridPoint j.1, gridPoint j.2)) f (f.integrable _) δ
    (fun j p hp => ho p _ (grid_pair_dist j.1 j.2 hp))
  simpa only [Fintype.sum_prod_type] using h

lemma grid_birkhoff_integral_bound (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {n : ℕ} (hn : 0 < n) (w : Equiv.Perm (Fin n) → ℝ)
    (he : ∀ i j, (μ : Measure (I × I)).real (gridCell i ×ˢ gridCell j) =
      (n : ℝ)⁻¹ * ∑ a, w a * (if a i = j then 1 else 0))
    (f : I × I →ᵇ ℝ) (δ : ℝ)
    (ho : ∀ p q : I × I, dist p q ≤ (n : ℝ)⁻¹ → |f p - f q| ≤ δ) :
    |(∫ p, f p ∂(μ : Measure (I × I))) - ∑ a, w a * gridAverage a f| ≤ δ := by
  have h := grid_integral_bound μ hμ hn f δ ho
  rw [birkhoff_quadrature μ w he] at h
  exact h

end PermutationLimitProof
end
end

/- Source module: MarginalQuadrature -/
section

noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval Set Filter Topology
open scoped BoundedContinuousFunction ENNReal

lemma grid_line_integral_bound {n : ℕ} (hn : 0 < n) (f : I →ᵇ ℝ) (δ : ℝ)
    (ho : ∀ p r : I, dist p r ≤ (n : ℝ)⁻¹ → |f p - f r| ≤ δ) :
    |(∫ p : I, f p) - (n : ℝ)⁻¹ * ∑ i : Fin n, f (gridPoint i)| ≤ δ := by
  have hc : ∀ᵐ x : I, ∃ i : Fin n, x ∈ gridCell i := by
    filter_upwards [volume_ae_pos] with x hx
    exact mem_iUnion.1 ((gridCell_cover hn).symm ▸ hx)
  have h := finite_partition_integral_bound (volume : Measure I) gridCell gridCell_measurable
    gridCell_disjoint hc (fun i => f (gridPoint i)) f (f.integrable _) δ
    (fun i x hx => ho x _ (gridCell_diameter i hx (gridPoint_mem i)))
  simpa only [measureReal_def, gridCell_volume, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← Finset.mul_sum] using h

lemma grid_line_integral_tendsto {m : ℕ → ℕ} (hm : Tendsto m atTop atTop)
    (f : I →ᵇ ℝ) :
    Tendsto (fun j => (m j : ℝ)⁻¹ * ∑ i : Fin (m j), f (gridPoint i))
      atTop (𝓝 (∫ p : I, f p)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨d, hd, ho⟩ := Metric.uniformContinuous_iff_le.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / 2) (by positivity)
  have hi : Tendsto (fun j => (m j : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hm
  have hd' := hi.eventually (gt_mem_nhds hd)
  have hp : ∀ᶠ j in atTop, 0 < m j := hm.eventually (eventually_gt_atTop 0)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hd'.and hp)
  refine ⟨N, fun j hj => ?_⟩
  obtain ⟨hdj, hpj⟩ := hN j hj
  have h := grid_line_integral_bound hpj f (ε / 2) (fun p r hpr => by
    simpa only [Real.dist_eq] using ho (hpr.trans hdj.le))
  rw [Real.dist_eq, abs_sub_comm]
  exact h.trans_lt (by linarith)

end PermutationLimitProof
end
end

/- Source module: MarginalLimits -/
section

noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval Filter Topology
open scoped BoundedContinuousFunction

def uniformLaw : ProbabilityMeasure I := ⟨volume, inferInstance⟩

lemma empirical_marginal_tendsto (s : ℕ → Σ n, Equiv.Perm (Fin n))
    (hs : Tendsto (fun j => (s j).1) atTop atTop)
    (g : I × I → I) (hg : Continuous g)
    (he : ∀ j, 0 < (s j).1 → ∀ f : I →ᵇ ℝ,
      (∫ p, f (g p) ∂(empiricalLaw (s j).2 : Measure (I × I))) =
        ((s j).1 : ℝ)⁻¹ * ∑ i : Fin (s j).1, f (gridPoint i)) :
    Tendsto (fun j => (empiricalLaw (s j).2).map hg.measurable.aemeasurable)
      atTop (𝓝 uniformLaw) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have h := grid_line_integral_tendsto hs f
  apply h.congr'
  filter_upwards [hs.eventually (eventually_gt_atTop 0)] with j hj
  change _ = ∫ p, f p ∂((empiricalLaw (s j).2 : Measure (I × I)).map g)
  have hf : AEStronglyMeasurable (fun p : I => f p)
      ((empiricalLaw (s j).2 : Measure (I × I)).map g) := f.continuous.aestronglyMeasurable
  rw [integral_map hg.measurable.aemeasurable hf, he j hj f]

lemma empirical_limit_uniform (s : ℕ → Σ n, Equiv.Perm (Fin n))
    (hs : Tendsto (fun j => (s j).1) atTop atTop)
    {μ : ProbabilityMeasure (I × I)}
    (h : Tendsto (fun j => empiricalLaw (s j).2) atTop (𝓝 μ)) : UniformMarginals μ := by
  have hx := empirical_marginal_tendsto s hs Prod.fst continuous_fst
    (fun j hj f => empirical_first_integral hj (s j).2 f f.measurable)
  have hy := empirical_marginal_tendsto s hs Prod.snd continuous_snd
    (fun j hj f => empirical_second_integral hj (s j).2 f f.measurable)
  have hx' := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h continuous_fst
  have hy' := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h continuous_snd
  have ex := tendsto_nhds_unique hx' hx
  have ey := tendsto_nhds_unique hy' hy
  exact ⟨congrArg (fun ν : ProbabilityMeasure I => (ν : Measure I)) ex,
    congrArg (fun ν : ProbabilityMeasure I => (ν : Measure I)) ey⟩

end PermutationLimitProof
end
end

/- Source module: RectangleExt -/
section

noncomputable section
namespace PermutationLimitProof
open MeasureTheory unitInterval Set

def rectangleSection (μ : Measure (I × I)) (B : Set I) : Measure I :=
  (μ.restrict (B ×ˢ univ)).map Prod.snd

lemma rectangleSection_apply (μ : Measure (I × I)) (B C : Set I)
    (hC : MeasurableSet C) : rectangleSection μ B C = μ (B ×ˢ C) := by
  rw [rectangleSection, Measure.map_apply measurable_snd hC,
    Measure.restrict_apply (hC.preimage measurable_snd)]
  congr 1
  ext p
  simp [and_comm]

lemma measure_eq_of_lower_rectangles (μ ν : Measure (I × I)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ (B : Set I), MeasurableSet B → ∀ y : I, μ.real (B ×ˢ Iic y) = ν.real (B ×ˢ Iic y)) :
    μ = ν := by
  apply Measure.ext_prod
  intro B C hB hC
  have : IsFiniteMeasure (rectangleSection μ B) := by unfold rectangleSection; infer_instance
  have he : rectangleSection μ B = rectangleSection ν B := by
    apply Measure.ext_of_Iic
    intro y
    rw [rectangleSection_apply _ _ _ measurableSet_Iic,
      rectangleSection_apply _ _ _ measurableSet_Iic]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 (h B hB y)
  have he' := congrArg (fun ξ : Measure I => ξ C) he
  simpa only [rectangleSection_apply _ _ _ hC] using he'

end PermutationLimitProof
end
end

/- Source module: CauchyFoundation -/
section

end

/- Source module: IdentificationOrders -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory ProbabilityTheory PermutationLimitProof PermLimits.Shared unitInterval
open Set Function

lemma exists_sorting_perm {k : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin k → α) (hf : Injective f) :
    ∃ ρ : Equiv.Perm (Fin k), StrictMono (fun i => f (ρ i)) := by
  classical
  let S := Finset.univ.image f
  have hc : S.card = k := by simp [S, Finset.card_image_of_injective _ hf]
  let g : Fin k → S := fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hg : Bijective g := by
    constructor
    · intro i j h
      exact hf (congrArg Subtype.val h)
    · intro y
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp y.property
      exact ⟨i, Subtype.ext hi⟩
  let e := Equiv.ofBijective g hg
  let o := S.orderIsoOfFin hc
  refine ⟨o.toEquiv.trans e.symm, ?_⟩
  intro i j hij
  have he (i : Fin k) : f (e.symm (o i)) = (o i).val := by
    have h := e.apply_symm_apply (o i)
    exact congrArg Subtype.val h
  change f (e.symm (o i)) < f (e.symm (o j))
  rw [he, he]
  exact o.strictMono hij

lemma strictMono_order_unique {k : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin k → α) (ρ η : Equiv.Perm (Fin k))
    (hρ : StrictMono (fun i => f (ρ i))) (hη : StrictMono (fun i => f (η i))) : ρ = η := by
  have he : (fun i => f (ρ i)) = (fun i => f (η i)) := by
    apply (hρ.range_inj hη).mp
    simp only [← Function.comp_def, Equiv.surjective, Surjective.range_comp]
  have hf : Injective f := by
    intro i j h
    have hh := hρ.injective (show f (ρ (ρ.symm i)) = f (ρ (ρ.symm j)) by simpa using h)
    exact ρ.symm.injective hh
  exact Equiv.ext fun i => hf (congrFun he i)

def fullOrderCell {k : ℕ} (ρ η : Equiv.Perm (Fin k)) : Set (Fin k → I × I) :=
  {p | StrictMono (fun i => (p (ρ i)).1) ∧ StrictMono (fun i => (p (η i)).2)}

lemma fullOrderCell_eq {k : ℕ} (ρ η : Equiv.Perm (Fin k)) :
    fullOrderCell ρ η = horizontalChain ρ ∩ verticalChain η := by
  ext p
  simp only [fullOrderCell, horizontalChain, verticalChain, mem_ofPred_eq,
    mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hx,hy⟩
    exact ⟨fun q => hx q.property, fun q => hy q.property⟩
  · rintro ⟨hx,hy⟩
    exact ⟨fun i j hij => hx ⟨(i,j),hij⟩, fun i j hij => hy ⟨(i,j),hij⟩⟩

lemma fullOrderCell_isOpen {k : ℕ} (ρ η : Equiv.Perm (Fin k)) :
    IsOpen (fullOrderCell ρ η) := by
  rw [fullOrderCell_eq]
  apply IsOpen.inter
  · exact isOpen_iInter_of_finite fun q =>
      isOpen_lt (continuous_apply _ |>.fst) (continuous_apply _ |>.fst)
  · exact isOpen_iInter_of_finite fun q =>
      isOpen_lt (continuous_apply _ |>.snd) (continuous_apply _ |>.snd)

lemma fullOrderCell_disjoint {k : ℕ} : Pairwise (fun a b :
    Equiv.Perm (Fin k) × Equiv.Perm (Fin k) =>
    Disjoint (fullOrderCell a.1 a.2) (fullOrderCell b.1 b.2)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact hab (Prod.ext (strictMono_order_unique (fun i => (p i).1) _ _ hp.1 hq.1)
    (strictMono_order_unique (fun i => (p i).2) _ _ hp.2 hq.2))

end PermutationCauchyProof
end
end

/- Source module: IdentificationCells -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory ProbabilityTheory PermutationLimitProof PermLimits.Shared unitInterval
open Set Function

lemma fullOrderCell_relabel {k : ℕ} (ρ η δ : Equiv.Perm (Fin k)) :
    (fun p : Fin k → I × I => fun i => p (δ i)) ⁻¹' fullOrderCell ρ η =
      fullOrderCell (ρ.trans δ) (η.trans δ) := by
  rfl

lemma fullOrderCell_measure_relabel {k : ℕ} (μ : ProbabilityMeasure (I × I))
    (ρ η δ : Equiv.Perm (Fin k)) :
    (Measure.pi fun _ : Fin k => (μ : Measure (I × I))).real
      (fullOrderCell (ρ.trans δ) (η.trans δ)) =
    (Measure.pi fun _ : Fin k => (μ : Measure (I × I))).real (fullOrderCell ρ η) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin k => I × I) δ.symm
  have he : (fun p : Fin k → I × I => fun i => p (δ i)) = e := by
    funext p i
    simp [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  have hm := measurePreserving_piCongrLeft (fun _ : Fin k => (μ : Measure (I × I))) δ.symm
  have hh := congrArg (fun ν : Measure (Fin k → I × I) => ν.real (fullOrderCell ρ η)) hm.map_eq
  rw [map_measureReal_apply hm.measurable (fullOrderCell_isOpen ρ η).measurableSet] at hh
  rw [← he, fullOrderCell_relabel] at hh
  exact hh

lemma patternProbability_cell_sum {k : ℕ} (μ : ProbabilityMeasure (I × I))
    (τ : Equiv.Perm (Fin k)) :
    patternProbability μ τ = ∑ ρ : Equiv.Perm (Fin k),
      (Measure.pi fun _ : Fin k => (μ : Measure (I × I))).real
        (fullOrderCell ρ (τ.symm.trans ρ)) := by
  rw [patternProbability, patternEvent_union]
  simp_rw [← fullOrderCell_eq]
  apply measureReal_iUnion_fintype
  · intro ρ η h
    exact fullOrderCell_disjoint (show (ρ,τ.symm.trans ρ) ≠ (η,τ.symm.trans η) from
      fun he => h (congrArg Prod.fst he))
  · intro ρ
    exact (fullOrderCell_isOpen _ _).measurableSet
  · intro ρ
    exact measure_ne_top _ _

lemma patternProbability_cell {k : ℕ} (μ : ProbabilityMeasure (I × I))
    (τ : Equiv.Perm (Fin k)) :
    patternProbability μ τ = (Nat.factorial k : ℝ) *
      (Measure.pi fun _ : Fin k => (μ : Measure (I × I))).real
        (fullOrderCell (Equiv.refl _) τ.symm) := by
  rw [patternProbability_cell_sum]
  have hh (ρ : Equiv.Perm (Fin k)) := fullOrderCell_measure_relabel μ (Equiv.refl _) τ.symm ρ
  simp only [Equiv.refl_trans] at hh
  simp_rw [hh]
  simp [Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end PermutationCauchyProof
end
end

/- Source module: IdentificationEvents -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory ProbabilityTheory PermutationLimitProof PermLimits.Shared unitInterval
open Set Function

lemma fullOrderCell_measure_eq {k : ℕ} (μ ν : ProbabilityMeasure (I × I))
    (h : ∀ (τ : Equiv.Perm (Fin k)), patternProbability μ τ = patternProbability ν τ)
    (ρ η : Equiv.Perm (Fin k)) :
    (Measure.pi fun _ : Fin k => (μ : Measure (I × I))).real (fullOrderCell ρ η) =
    (Measure.pi fun _ : Fin k => (ν : Measure (I × I))).real (fullOrderCell ρ η) := by
  have hh := h (ρ.trans η.symm)
  rw [patternProbability_cell, patternProbability_cell] at hh
  have hf : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero k)
  have he := (mul_left_cancel₀ hf) hh
  have hm := fullOrderCell_measure_relabel μ (Equiv.refl _) (ρ.trans η.symm).symm ρ
  have hn := fullOrderCell_measure_relabel ν (Equiv.refl _) (ρ.trans η.symm).symm ρ
  have hc : (ρ.trans η.symm).symm.trans ρ = η := by
    ext i
    simp
  simpa only [Equiv.refl_trans, hc] using hm.trans (he.trans hn.symm)

lemma ae_coordinates_injective {k : ℕ} (μ : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) :
    ∀ᵐ p ∂(Measure.pi fun _ : Fin k => (μ : Measure (I × I))),
      Injective (fun i => (p i).1) ∧ Injective (fun i => (p i).2) := by
  have hx : ∀ᵐ p ∂(Measure.pi fun _ : Fin k => (μ : Measure (I × I))),
      ∀ i j : Fin k, i ≠ j → (p i).1 ≠ (p j).1 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · subst j; simp
    · have hz := coordinate_collision_null μ Prod.fst measurable_fst hμ.1 hij
      have ha : ∀ᵐ p ∂(Measure.pi fun _ : Fin k => (μ : Measure (I × I))),
          (p i).1 ≠ (p j).1 := by simpa only [ae_iff, not_not] using hz
      filter_upwards [ha] with p hp using fun _ => hp
  have hy : ∀ᵐ p ∂(Measure.pi fun _ : Fin k => (μ : Measure (I × I))),
      ∀ i j : Fin k, i ≠ j → (p i).2 ≠ (p j).2 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · subst j; simp
    · have hz := coordinate_collision_null μ Prod.snd measurable_snd hμ.2 hij
      have ha : ∀ᵐ p ∂(Measure.pi fun _ : Fin k => (μ : Measure (I × I))),
          (p i).2 ≠ (p j).2 := by simpa only [ae_iff, not_not] using hz
      filter_upwards [ha] with p hp using fun _ => hp
  filter_upwards [hx,hy] with p hx hy
  constructor
  · intro i j he; by_contra hn; exact hx i j hn he
  · intro i j he; by_contra hn; exact hy i j hn he

def comparisonEvent {k : ℕ} (S T : Finset (Fin k)) (d : Fin k) : Set (Fin k → I × I) :=
  {p | (∀ i ∈ S, (p i).1 < (p d).1) ∧ (∀ j ∈ T, (p j).2 < (p d).2)}

def selectedCell {k : ℕ} (S T : Finset (Fin k)) (d : Fin k)
    (ρ η : Equiv.Perm (Fin k)) : Prop :=
  (∀ i ∈ S, ρ.symm i < ρ.symm d) ∧ (∀ j ∈ T, η.symm j < η.symm d)

lemma comparisonEvent_cell {k : ℕ} (S T : Finset (Fin k)) (d : Fin k)
    (ρ η : Equiv.Perm (Fin k)) {p : Fin k → I × I} (hp : p ∈ fullOrderCell ρ η) :
    p ∈ comparisonEvent S T d ↔ selectedCell S T d ρ η := by
  have hx (i j : Fin k) : (p i).1 < (p j).1 ↔ ρ.symm i < ρ.symm j := by
    simpa using hp.1.lt_iff_lt (a := ρ.symm i) (b := ρ.symm j)
  have hy (i j : Fin k) : (p i).2 < (p j).2 ↔ η.symm i < η.symm j := by
    simpa using hp.2.lt_iff_lt (a := η.symm i) (b := η.symm j)
  simp only [comparisonEvent, selectedCell, mem_ofPred_eq, hx, hy]

end PermutationCauchyProof
end
end

/- Source module: IdentificationEventMeasure -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory ProbabilityTheory PermutationLimitProof PermLimits.Shared unitInterval
open Set Function
open scoped Classical

lemma comparisonEvent_ae_union {k : ℕ} (μ : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (S T : Finset (Fin k)) (d : Fin k) :
    comparisonEvent S T d =ᵐ[Measure.pi fun _ : Fin k => (μ : Measure (I × I))]
      ⋃ q : Equiv.Perm (Fin k) × Equiv.Perm (Fin k),
        if selectedCell S T d q.1 q.2 then fullOrderCell q.1 q.2 else ∅ := by
  classical
  filter_upwards [ae_coordinates_injective μ hμ] with p hp
  apply propext
  constructor
  · intro hE
    obtain ⟨ρ,hρ⟩ := exists_sorting_perm (fun i => (p i).1) hp.1
    obtain ⟨η,hη⟩ := exists_sorting_perm (fun i => (p i).2) hp.2
    have hcell : p ∈ fullOrderCell ρ η := ⟨hρ,hη⟩
    have hs := (comparisonEvent_cell S T d ρ η hcell).mp hE
    exact mem_iUnion.mpr ⟨(ρ,η), by simpa only [if_pos hs] using hcell⟩
  · intro hE
    obtain ⟨q,hq⟩ := mem_iUnion.mp hE
    by_cases hs : selectedCell S T d q.1 q.2
    · have hc : p ∈ fullOrderCell q.1 q.2 := by simpa only [if_pos hs] using hq
      exact (comparisonEvent_cell S T d q.1 q.2 hc).mpr hs
    · simp only [if_neg hs, mem_empty_iff_false] at hq

lemma comparisonEvent_measure_sum {k : ℕ} (μ : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (S T : Finset (Fin k)) (d : Fin k) :
    (Measure.pi fun _ : Fin k => (μ : Measure (I × I))).real (comparisonEvent S T d) =
      ∑ q : Equiv.Perm (Fin k) × Equiv.Perm (Fin k),
        if selectedCell S T d q.1 q.2 then
          (Measure.pi fun _ : Fin k => (μ : Measure (I × I))).real (fullOrderCell q.1 q.2)
        else 0 := by
  classical
  rw [measureReal_congr (comparisonEvent_ae_union μ hμ S T d)]
  rw [measureReal_iUnion_fintype]
  · apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp
  · intro q r hqr
    dsimp only [Function.onFun]
    split_ifs <;> simp only [disjoint_empty, empty_disjoint, fullOrderCell_disjoint hqr]
  · intro q
    split_ifs
    · exact (fullOrderCell_isOpen _ _).measurableSet
    · exact MeasurableSet.empty

lemma comparisonEvent_measure_eq {k : ℕ} (μ ν : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (hν : UniformMarginals ν)
    (h : ∀ (τ : Equiv.Perm (Fin k)), patternProbability μ τ = patternProbability ν τ)
    (S T : Finset (Fin k)) (d : Fin k) :
    (Measure.pi fun _ : Fin k => (μ : Measure (I × I))).real (comparisonEvent S T d) =
    (Measure.pi fun _ : Fin k => (ν : Measure (I × I))).real (comparisonEvent S T d) := by
  classical
  rw [comparisonEvent_measure_sum μ hμ, comparisonEvent_measure_sum ν hν]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs
  · exact fullOrderCell_measure_eq μ ν h q.1 q.2
  · rfl

end PermutationCauchyProof
end
end

/- Source module: IdentificationMoments -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory ProbabilityTheory PermutationLimitProof PermLimits.Shared unitInterval
open Set Function
open scoped Classical

lemma marginal_lower (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    (c : Bool) (z : I × I) :
    (μ : Measure (I × I)) {p | (if c then p.1 else p.2) < (if c then z.1 else z.2)} =
      ENNReal.ofReal (if c then (z.1 : ℝ) else (z.2 : ℝ)) := by
  cases c
  · have h := congrArg (fun m : Measure I => m (Iio z.2)) hμ.2
    rw [Measure.map_apply measurable_snd measurableSet_Iio, unitInterval.volume_Iio] at h
    exact h
  · have h := congrArg (fun m : Measure I => m (Iio z.1)) hμ.1
    rw [Measure.map_apply measurable_fst measurableSet_Iio, unitInterval.volume_Iio] at h
    exact h

def cohortSection {n : ℕ} (c : Fin n → Bool) (z : I × I) : Set (Fin n → I × I) :=
  Set.pi Set.univ (fun i => {p | (if c i then p.1 else p.2) < (if c i then z.1 else z.2)})

lemma cohortSection_measure {n : ℕ} (μ : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (c : Fin n → Bool) (z : I × I) :
    (Measure.pi fun _ : Fin n => (μ : Measure (I × I))) (cohortSection c z) =
      ∏ i, ENNReal.ofReal (if c i then (z.1 : ℝ) else (z.2 : ℝ)) := by
  rw [cohortSection, Measure.pi_pi]
  congr 1
  funext i
  exact marginal_lower μ hμ (c i) z

def cohortEvent {n : ℕ} (c : Fin n → Bool) : Set ((I × I) × (Fin n → I × I)) :=
  {q | q.2 ∈ cohortSection c q.1}

lemma cohortEvent_measurable {n : ℕ} (c : Fin n → Bool) : MeasurableSet (cohortEvent c) := by
  have he : cohortEvent c = ⋂ i, {q | (if c i then (q.2 i).1 else (q.2 i).2) <
      (if c i then q.1.1 else q.1.2)} := by ext q; simp [cohortEvent, cohortSection]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  cases c i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> exact measurableSet_lt (by fun_prop) (by fun_prop)

lemma cohortEvent_measure {n : ℕ} (μ : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (c : Fin n → Bool) :
    ((μ : Measure (I × I)).prod (Measure.pi fun _ : Fin n => (μ : Measure (I × I))))
      (cohortEvent c) = ∫⁻ z, ∏ i, ENNReal.ofReal
        (if c i then (z.1 : ℝ) else (z.2 : ℝ)) ∂(μ : Measure (I × I)) := by
  rw [Measure.prod_apply (cohortEvent_measurable c)]
  apply lintegral_congr
  intro z
  exact cohortSection_measure μ hμ c z

lemma cohortEvent_preimage {n : ℕ} (c : Fin n → Bool) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => I × I) 0) ⁻¹' cohortEvent c =
    comparisonEvent ((Finset.univ.filter fun i => c i = true).image Fin.succ)
      ((Finset.univ.filter fun i => c i = false).image Fin.succ) 0 := by
  ext p
  simp only [mem_preimage, cohortEvent, cohortSection, mem_ofPred_eq, mem_pi,
    mem_univ, forall_const, comparisonEvent, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change (∀ i, (if c i then (p i.succ).1 else (p i.succ).2) <
    (if c i then (p 0).1 else (p 0).2)) ↔ _
  constructor
  · intro h
    constructor
    · rintro j ⟨i, hi, rfl⟩
      simpa only [hi, Bool.true_eq_false, ↓reduceIte] using h i
    · rintro j ⟨i, hi, rfl⟩
      simpa only [hi, Bool.false_eq_true, ↓reduceIte] using h i
  · rintro ⟨hx,hy⟩ i
    cases hi : c i
    · simpa only [hi, Bool.false_eq_true, ↓reduceIte] using hy i.succ ⟨i,hi,rfl⟩
    · simpa only [hi, Bool.true_eq_false, ↓reduceIte] using hx i.succ ⟨i,hi,rfl⟩

lemma cohort_integral_eq {n : ℕ} (μ ν : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (hν : UniformMarginals ν)
    (h : ∀ (τ : Equiv.Perm (Fin (n+1))), patternProbability μ τ = patternProbability ν τ)
    (c : Fin n → Bool) :
    (∫⁻ z, ∏ i, ENNReal.ofReal (if c i then (z.1 : ℝ) else (z.2 : ℝ)) ∂(μ : Measure (I × I))) =
    ∫⁻ z, ∏ i, ENNReal.ofReal (if c i then (z.1 : ℝ) else (z.2 : ℝ)) ∂(ν : Measure (I × I)) := by
  rw [← cohortEvent_measure μ hμ c, ← cohortEvent_measure ν hν c]
  have map_eq (ξ : ProbabilityMeasure (I × I)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (ξ : Measure (I × I))) 0).map_eq
  rw [← map_eq μ, ← map_eq ν,
    Measure.map_apply (MeasurableEquiv.piFinSuccAbove _ 0).measurable (cohortEvent_measurable c),
    Measure.map_apply (MeasurableEquiv.piFinSuccAbove _ 0).measurable (cohortEvent_measurable c),
    cohortEvent_preimage]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact comparisonEvent_measure_eq μ ν hμ hν h _ _ _

lemma mixed_lintegral_eq (μ ν : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (hν : UniformMarginals ν)
    (h : ∀ {k : ℕ} (τ : Equiv.Perm (Fin k)), patternProbability μ τ = patternProbability ν τ)
    (a b : ℕ) :
    (∫⁻ z, ENNReal.ofReal (z.1 : ℝ) ^ a * ENNReal.ofReal (z.2 : ℝ) ^ b ∂(μ : Measure (I × I))) =
    ∫⁻ z, ENNReal.ofReal (z.1 : ℝ) ^ a * ENNReal.ofReal (z.2 : ℝ) ^ b ∂(ν : Measure (I × I)) := by
  have he := cohort_integral_eq μ ν hμ hν h (Fin.append (fun _ : Fin a => true) (fun _ : Fin b => false))
  simpa only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, ↓reduceIte,
    Bool.false_eq_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using he

lemma mixed_integral_eq (μ ν : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (hν : UniformMarginals ν)
    (h : ∀ {k : ℕ} (τ : Equiv.Perm (Fin k)), patternProbability μ τ = patternProbability ν τ)
    (a b : ℕ) :
    (∫ z, (z.1 : ℝ) ^ a * (z.2 : ℝ) ^ b ∂(μ : Measure (I × I))) =
    ∫ z, (z.1 : ℝ) ^ a * (z.2 : ℝ) ^ b ∂(ν : Measure (I × I)) := by
  have hn : ∀ z : I × I, 0 ≤ (z.1 : ℝ) ^ a * (z.2 : ℝ) ^ b := by
    intro z
    exact mul_nonneg (pow_nonneg z.1.property.1 _) (pow_nonneg z.2.property.1 _)
  have hc : Continuous (fun z : I × I => (z.1 : ℝ) ^ a * (z.2 : ℝ) ^ b) := by fun_prop
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn) hc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn) hc.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_mul (pow_nonneg (unitInterval.nonneg _) _),
    ENNReal.ofReal_pow (unitInterval.nonneg _)]
  rw [mixed_lintegral_eq μ ν hμ hν h]

end PermutationCauchyProof
end
end

/- Source module: IdentificationPolynomial -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory ProbabilityTheory PermutationLimitProof PermLimits.Shared unitInterval
open Set Function
open BoundedContinuousFunction
open scoped Classical

def coordinateFunction (c : Bool) : (I × I) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun z => if c then (z.1 : ℝ) else (z.2 : ℝ),
    by cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop⟩

def polynomialMap : MvPolynomial Bool ℝ →ₐ[ℝ] ((I × I) →ᵇ ℝ) :=
  MvPolynomial.aeval coordinateFunction

lemma polynomialMap_monomial (u : Bool →₀ ℕ) (r : ℝ) (z : I × I) :
    polynomialMap (MvPolynomial.monomial u r) z = r * (z.1 : ℝ) ^ (u true) * (z.2 : ℝ) ^ (u false) := by
  rw [polynomialMap, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fintype.prod_bool, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.pow_apply]
  change r * ((z.1 : ℝ) ^ u true * (z.2 : ℝ) ^ u false) = _
  ring


lemma polynomial_integral_eq (μ ν : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (hν : UniformMarginals ν)
    (h : ∀ {k : ℕ} (τ : Equiv.Perm (Fin k)), patternProbability μ τ = patternProbability ν τ)
    (p : MvPolynomial Bool ℝ) :
    (∫ z, polynomialMap p z ∂(μ : Measure (I × I))) =
    ∫ z, polynomialMap p z ∂(ν : Measure (I × I)) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u r =>
    simp_rw [polynomialMap_monomial, mul_assoc]
    rw [integral_const_mul, integral_const_mul, mixed_integral_eq μ ν hμ hν h]
  | add p q hp hq =>
    simp only [map_add, BoundedContinuousFunction.add_apply]
    rw [integral_add ((polynomialMap p).integrable (μ := (μ : Measure (I × I)))) ((polynomialMap q).integrable (μ := (μ : Measure (I × I)))),
      integral_add ((polynomialMap p).integrable (μ := (ν : Measure (I × I)))) ((polynomialMap q).integrable (μ := (ν : Measure (I × I)))), hp, hq]

end PermutationCauchyProof
end
end

/- Source module: Identification -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory ProbabilityTheory PermutationLimitProof PermLimits.Shared unitInterval
open Set Function BoundedContinuousFunction
open scoped Classical

def polynomialAlgebra : StarSubalgebra ℝ ((I × I) →ᵇ ℝ) where
  toSubalgebra := polynomialMap.range
  star_mem' := by
    intro f hf
    have he : star f = f := by ext x; exact star_trivial _
    rwa [he]

lemma coordinateFunction_mem (c : Bool) : coordinateFunction c ∈ polynomialAlgebra := by
  change ∃ p, polynomialMap p = coordinateFunction c
  exact ⟨MvPolynomial.X c, MvPolynomial.aeval_X _ _⟩

lemma polynomialAlgebra_separates :
    (polynomialAlgebra.map (toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  have hc : ∃ c : Bool, coordinateFunction c x ≠ coordinateFunction c y := by
    by_contra! h
    apply hxy
    apply Prod.ext
    · apply Subtype.ext
      exact h true
    · apply Subtype.ext
      exact h false
  obtain ⟨c,hc⟩ := hc
  refine ⟨coordinateFunction c, ?_, hc⟩
  refine ⟨(coordinateFunction c).toContinuousMap, ?_, rfl⟩
  exact ⟨coordinateFunction c, coordinateFunction_mem c, rfl⟩

end PermutationCauchyProof

namespace PermutationLimitProof
open MeasureTheory unitInterval PermutationCauchyProof

theorem patternProbability_injective (μ ν : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (hν : UniformMarginals ν)
    (h : ∀ {k : ℕ} (τ : Equiv.Perm (Fin k)), patternProbability μ τ = patternProbability ν τ) :
    μ = ν := by
  apply Subtype.ext
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish
    (P := (μ : Measure (I × I))) (P' := (ν : Measure (I × I))) polynomialAlgebra_separates
  intro g hg
  obtain ⟨p,rfl⟩ := hg
  exact polynomial_integral_eq μ ν hμ hν h p

end PermutationLimitProof
end
end

/- Source module: DensityWeak -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory ProbabilityTheory PermutationLimitProof PermLimits.Shared unitInterval
open Filter Topology Function

lemma convergent_empirical_weak (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Tendsto (fun m => (s m).1) atTop atTop) (hc : IsConvergent s) :
    ∃ μ : ProbabilityMeasure (I × I), UniformMarginals μ ∧
      Tendsto (fun m => empiricalLaw (s m).2) atTop (𝓝 μ) := by
  obtain ⟨μ,φ,hφ,hμ⟩ := CompactSpace.tendsto_subseq (fun m => empiricalLaw (s m).2)
  have hsizeφ : Tendsto (fun m => (s (φ m)).1) atTop atTop := hs.comp hφ.tendsto_atTop
  have huμ := empirical_limit_uniform (s ∘ φ) hsizeφ hμ
  refine ⟨μ,huμ,tendsto_nhds_of_unique_mapClusterPt ?_⟩
  intro ν hν
  obtain ⟨ψ,hψ,hlimν⟩ := hν.tendsto_subseq
  have hsizeψ : Tendsto (fun m => (s (ψ m)).1) atTop atTop := hs.comp hψ.tendsto_atTop
  have huν := empirical_limit_uniform (s ∘ ψ) hsizeψ hlimν
  apply patternProbability_injective ν μ huν huμ
  intro k τ
  obtain ⟨a,ha⟩ := hc k τ
  have hpμ := empirical_weak_implies_densities (s ∘ φ) hsizeφ hμ huμ τ
  have hpν := empirical_weak_implies_densities (s ∘ ψ) hsizeψ hlimν huν τ
  exact (tendsto_nhds_unique hpν (ha.comp hψ.tendsto_atTop)).trans
    (tendsto_nhds_unique hpμ (ha.comp hφ.tendsto_atTop)).symm

end PermutationCauchyProof
end
end

/- Source module: StepCells -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory unitInterval PermLimits.Shared PermutationLimitProof Set

lemma stepLimit_bounds {n : ℕ} (π : Equiv.Perm (Fin n)) (x y : I) :
    0 ≤ stepLimit π x y ∧ stepLimit π x y ≤ 1 := by
  unfold stepLimit
  split
  · exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
  · exact y.2

lemma stepLimit_zero {n : ℕ} (π : Equiv.Perm (Fin n)) (x : I) :
    stepLimit π x 0 = 0 := by
  unfold stepLimit
  split
  · change min 1 (max 0 ((n : ℝ) * 0 - _)) = 0
    simp only [mul_zero, zero_sub]
    rw [max_eq_left (neg_nonpos.mpr (Nat.cast_nonneg _)), min_eq_right (by norm_num)]
  · rfl

lemma cell_index {n : ℕ} (i : Fin n) {x : I} (hx : x ∈ gridCell i) :
    min (⌈(n : ℝ) * (x : ℝ)⌉₊ - 1) (n - 1) = i.val := by
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  have hi : (i.val : ℝ) < (n : ℝ) * x := by
    have h := (mem_gridCell i x).mp hx
    nlinarith [(div_lt_iff₀ hn).mp h.1]
  have hi' : (n : ℝ) * x ≤ (i.val : ℝ) + 1 := by
    have h := (mem_gridCell i x).mp hx
    nlinarith [(le_div_iff₀ hn).mp h.2]
  have hl : i.val < ⌈(n : ℝ) * (x : ℝ)⌉₊ := Nat.lt_ceil.mpr hi
  have hu : ⌈(n : ℝ) * (x : ℝ)⌉₊ ≤ i.val + 1 := by
    rw [Nat.ceil_le]
    simpa only [Nat.cast_add, Nat.cast_one] using hi'
  have he : ⌈(n : ℝ) * (x : ℝ)⌉₊ - 1 = i.val := by omega
  rw [he, min_eq_left (by omega)]

lemma stepLimit_on_cell {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n)
    {x : I} (hx : x ∈ gridCell i) (y : I) :
    stepLimit π x y = min 1 (max 0 ((n : ℝ) * (y : ℝ) - (π i).val)) := by
  have hn := i.pos
  rw [stepLimit, dif_pos hn]
  have he : (⟨min (⌈(n : ℝ) * (x : ℝ)⌉₊ - 1) (n - 1), by omega⟩ : Fin n) = i :=
    Fin.ext (cell_index i hx)
  simp only [he]

lemma stepLimit_measurable {n : ℕ} (π : Equiv.Perm (Fin n)) (y : I) :
    Measurable (fun x : I => stepLimit π x y) := by
  unfold stepLimit
  split
  · rename_i hn
    exact (measurable_of_countable (fun k : ℕ =>
      min 1 (max 0 ((n : ℝ) * (y : ℝ) -
        ((π ⟨min (k - 1) (n - 1), by omega⟩).val : ℝ))))).comp
      ((measurable_const.mul measurable_subtype_coe).nat_ceil)
  · exact measurable_const

lemma stepLimit_integrable {n : ℕ} (π : Equiv.Perm (Fin n)) (y : I) :
    Integrable (fun x : I => stepLimit π x y) := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (stepLimit_measurable π y).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (stepLimit_bounds π x y).1]
  exact (stepLimit_bounds π x y).2

end PermutationCauchyProof
end
end

/- Source module: CdfMetric -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory unitInterval PermLimits.Shared PermutationLimitProof Set

def integratedCDF (Z : I → I → ℝ) (x y : I) : ℝ := ∫ t in Iic x, Z t y

lemma integral_Icc_prefix {f : I → ℝ} (hf : Integrable f) {a b : I} (hab : a ≤ b) :
    (∫ t in Icc a b, f t) = (∫ t in Iic b, f t) - ∫ t in Iic a, f t := by
  rw [integral_Icc_eq_integral_Ioc]
  have he : Ioc a b = Iic b \ Iic a := by ext t; simp only [mem_Ioc, mem_sdiff, mem_Iic, not_le]; tauto
  rw [he, setIntegral_sdiff measurableSet_Iic hf.integrableOn (Iic_subset_Iic.mpr hab)]

lemma rectangle_four_corners (Z : I → I → ℝ) (hZ : ∀ y, Integrable (fun x => Z x y))
    {a b : I} (hab : a ≤ b) (c d : I) :
    (∫ t in Icc a b, (Z t d - Z t c)) =
      integratedCDF Z b d - integratedCDF Z a d -
        integratedCDF Z b c + integratedCDF Z a c := by
  rw [integral_sub (hZ d).integrableOn (hZ c).integrableOn,
    integral_Icc_prefix (hZ d) hab, integral_Icc_prefix (hZ c) hab]
  unfold integratedCDF
  ring

lemma rect_values_nonempty (Z W : I → I → ℝ) :
    {r : ℝ | ∃ a b c d : I, a < b ∧ c < d ∧
      r = |(∫ t in Icc a b, (Z t d - Z t c)) -
        (∫ t in Icc a b, (W t d - W t c))|}.Nonempty := by
  exact ⟨_, 0, 1, 0, 1, by norm_num, by norm_num, rfl⟩

lemma rectDist_le_of_cdf (Z W : I → I → ℝ)
    (hZ : ∀ y, Integrable (fun x => Z x y)) (hW : ∀ y, Integrable (fun x => W x y))
    {e : ℝ} (he : ∀ x y, |integratedCDF Z x y - integratedCDF W x y| ≤ e) :
    rectDist Z W ≤ 4 * e := by
  apply csSup_le (rect_values_nonempty Z W)
  rintro r ⟨a,b,c,d,hab,hcd,rfl⟩
  rw [rectangle_four_corners Z hZ hab.le, rectangle_four_corners W hW hab.le]
  have h1 := abs_le.mp (he b d)
  have h2 := abs_le.mp (he a d)
  have h3 := abs_le.mp (he b c)
  have h4 := abs_le.mp (he a c)
  rw [abs_le]
  constructor <;> linarith

lemma stepCDF_abs_le_one {n : ℕ} (π : Equiv.Perm (Fin n)) (x y : I) :
    |integratedCDF (stepLimit π) x y| ≤ 1 := by
  have h := norm_setIntegral_le_of_norm_le_const (measure_lt_top volume (Iic x))
    (fun t (_ht : t ∈ Iic x) => show ‖stepLimit π t y‖ ≤ (1 : ℝ) by
      rw [Real.norm_eq_abs, abs_of_nonneg (stepLimit_bounds π t y).1]
      exact (stepLimit_bounds π t y).2)
  change |integratedCDF (stepLimit π) x y| ≤ _ at h
  have hm : volume.real (Iic x) ≤ 1 := by
    rw [Measure.real, unitInterval.volume_Iic, ENNReal.toReal_ofReal x.2.1]
    exact x.2.2
  simpa only [one_mul] using h.trans (by simpa only [one_mul] using hm)

lemma stepCDF_difference_bound {n m : ℕ} (π : Equiv.Perm (Fin n))
    (ρ : Equiv.Perm (Fin m)) (x y : I) :
    |integratedCDF (stepLimit π) x y - integratedCDF (stepLimit ρ) x y| ≤ 2 := by
  calc
    _ ≤ |integratedCDF (stepLimit π) x y| + |integratedCDF (stepLimit ρ) x y| := abs_sub _ _
    _ ≤ 2 := by linarith [stepCDF_abs_le_one π x y, stepCDF_abs_le_one ρ x y]

lemma step_rect_values_bdd {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) :
    BddAbove {r : ℝ | ∃ a b c d : I, a < b ∧ c < d ∧
      r = |(∫ t in Icc a b, (stepLimit π t d - stepLimit π t c)) -
        (∫ t in Icc a b, (stepLimit ρ t d - stepLimit ρ t c))|} := by
  refine ⟨8, ?_⟩
  rintro r ⟨a,b,c,d,hab,hcd,rfl⟩
  rw [rectangle_four_corners _ (stepLimit_integrable π) hab.le,
    rectangle_four_corners _ (stepLimit_integrable ρ) hab.le]
  have h1 := abs_le.mp (stepCDF_difference_bound π ρ b d)
  have h2 := abs_le.mp (stepCDF_difference_bound π ρ a d)
  have h3 := abs_le.mp (stepCDF_difference_bound π ρ b c)
  have h4 := abs_le.mp (stepCDF_difference_bound π ρ a c)
  rw [abs_le]
  constructor <;> linarith

lemma stepCDF_zero_x {n : ℕ} (π : Equiv.Perm (Fin n)) (y : I) :
    integratedCDF (stepLimit π) 0 y = 0 := by
  simp [integratedCDF, show Iic (0 : I) = {0} from Iic_bot]

lemma stepCDF_zero_y {n : ℕ} (π : Equiv.Perm (Fin n)) (x : I) :
    integratedCDF (stepLimit π) x 0 = 0 := by
  simp [integratedCDF, stepLimit_zero]

lemma step_rectDist_nonneg {n m : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) :
    0 ≤ rectDist (stepLimit π) (stepLimit ρ) := by
  obtain ⟨r, a,b,c,d,hab,hcd,hr⟩ := rect_values_nonempty (stepLimit π) (stepLimit ρ)
  exact (hr ▸ abs_nonneg _).trans (le_csSup (step_rect_values_bdd π ρ) ⟨a,b,c,d,hab,hcd,hr⟩)

lemma stepCDF_difference_le_rectDist {n m : ℕ} (π : Equiv.Perm (Fin n))
    (ρ : Equiv.Perm (Fin m)) (x y : I) :
    |integratedCDF (stepLimit π) x y - integratedCDF (stepLimit ρ) x y| ≤
      rectDist (stepLimit π) (stepLimit ρ) := by
  by_cases hx : x = 0
  · simpa [hx, stepCDF_zero_x] using step_rectDist_nonneg π ρ
  by_cases hy : y = 0
  · simpa [hy, stepCDF_zero_y] using step_rectDist_nonneg π ρ
  have hx' : (0 : I) < x := lt_of_le_of_ne bot_le (Ne.symm hx)
  have hy' : (0 : I) < y := lt_of_le_of_ne bot_le (Ne.symm hy)
  apply le_csSup (step_rect_values_bdd π ρ)
  refine ⟨0,x,0,y,hx',hy',?_⟩
  rw [rectangle_four_corners _ (stepLimit_integrable π) hx'.le,
    rectangle_four_corners _ (stepLimit_integrable ρ) hx'.le]
  simp [stepCDF_zero_x, stepCDF_zero_y]

end PermutationCauchyProof
end
end

/- Source module: StepCDF -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory unitInterval PermLimits.Shared PermutationLimitProof Set

/-- The one-dimensional CDF within a single occupied permutation cell. -/
def rowCDF {n : ℕ} (i : Fin n) (y : I) : ℝ :=
  min 1 (max 0 ((n : ℝ) * (y : ℝ) - i.val))

lemma stepLimit_sum_cells {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) (y : I) :
    (fun x : I => stepLimit π x y) =ᵐ[volume]
      fun x => ∑ i : Fin n, (gridCell i).indicator (fun _ => rowCDF (π i) y) x := by
  filter_upwards [volume_ae_pos] with x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp ((gridCell_cover hn).symm ▸ (show x ∈ Ioi (0 : I) from hx))
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hi, stepLimit_on_cell π i hi]
    rfl
  · intro j _ hji
    apply Set.indicator_of_notMem
    exact fun hj => Set.disjoint_left.mp (gridCell_disjoint hji) hj hi
  · simp

lemma stepCDF_sum {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) (x y : I) :
    integratedCDF (stepLimit π) x y =
      ∑ i : Fin n, volume.real (gridCell i ∩ Iic x) * rowCDF (π i) y := by
  unfold integratedCDF
  rw [integral_congr_ae (ae_restrict_of_ae (stepLimit_sum_cells hn π y))]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (gridCell_measurable i)]
    rw [Measure.restrict_restrict (gridCell_measurable i)]
    simp
  · intro i _
    exact ((integrable_const _).indicator (gridCell_measurable i)).integrableOn

lemma rowCDF_eq_zero {n : ℕ} (i : Fin n) {y : I} (hy : (y : ℝ) ≤ (i.val : ℝ) / n) :
    rowCDF i y = 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  have h := (le_div_iff₀ hn).mp hy
  unfold rowCDF
  rw [max_eq_left (by nlinarith), min_eq_right (by norm_num)]

lemma rowCDF_eq_one {n : ℕ} (i : Fin n) {y : I} (hy : gridPoint i ≤ y) :
    rowCDF i y = 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  have h : ((i.val : ℝ) + 1) / n ≤ (y : ℝ) := hy
  have hh := (div_le_iff₀ hn).mp h
  unfold rowCDF
  rw [min_eq_left]
  exact le_max_of_le_right (by nlinarith)

lemma rowCDF_bounds {n : ℕ} (i : Fin n) (y : I) : 0 ≤ rowCDF i y ∧ rowCDF i y ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

lemma gridCell_prefix_volume {n : ℕ} (i : Fin n) (y : I) :
    volume.real (gridCell i ∩ Iic y) = (n : ℝ)⁻¹ * rowCDF i y := by
  have hn : (0 : ℝ) < n := by exact_mod_cast i.pos
  by_cases hyl : y ≤ gridLeft i
  · have he : gridCell i ∩ Iic y = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact (not_lt_of_ge (ht.2.trans hyl)) ht.1.1
    rw [he, measureReal_empty, rowCDF_eq_zero i hyl, mul_zero]
  by_cases hry : gridPoint i ≤ y
  · have he : gridCell i ∩ Iic y = gridCell i := by
      apply inter_eq_left.mpr
      exact fun t ht => ht.2.trans hry
    rw [he, rowCDF_eq_one i hry, mul_one, measureReal_def, gridCell_volume,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hly : gridLeft i < y := lt_of_not_ge hyl
  have hyr : y < gridPoint i := lt_of_not_ge hry
  have he : gridCell i ∩ Iic y = Ioc (gridLeft i) y := by
    ext t
    change ((gridLeft i < t ∧ t ≤ gridPoint i) ∧ t ≤ y) ↔ (gridLeft i < t ∧ t ≤ y)
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2.trans hyr.le⟩,h.2⟩
  rw [he, measureReal_def, unitInterval.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hly.le)]
  change (y : ℝ) - (i.val : ℝ) / n = (n : ℝ)⁻¹ * rowCDF i y
  have hl : (i.val : ℝ) / n < (y : ℝ) := hly
  have hr : (y : ℝ) < ((i.val : ℝ) + 1) / n := hyr
  have hl' := (div_lt_iff₀ hn).mp hl
  have hr' := (lt_div_iff₀ hn).mp hr
  unfold rowCDF
  rw [max_eq_right (by nlinarith), min_eq_right (by nlinarith)]
  field_simp

end PermutationCauchyProof
end
end

/- Source module: RowError -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory unitInterval PermLimits.Shared PermutationLimitProof Set

/-- The atom at the upper endpoint of a grid cell. -/
def endpointCDF {n : ℕ} (i : Fin n) (y : I) : ℝ := if gridPoint i ≤ y then 1 else 0

lemma endpointCDF_bounds {n : ℕ} (i : Fin n) (y : I) :
    0 ≤ endpointCDF i y ∧ endpointCDF i y ≤ rowCDF i y := by
  unfold endpointCDF
  split_ifs with h
  · rw [rowCDF_eq_one i h]; norm_num
  · exact ⟨le_rfl, (rowCDF_bounds i y).1⟩

lemma row_error_bounds {n : ℕ} (i : Fin n) (y : I) :
    0 ≤ rowCDF i y - endpointCDF i y ∧ rowCDF i y - endpointCDF i y ≤ 1 := by
  have h := endpointCDF_bounds i y
  have hh := rowCDF_bounds i y
  constructor <;> linarith

lemma row_error_zero_off_cell {n : ℕ} (i : Fin n) {y : I} (hy : y ∉ gridCell i) :
    rowCDF i y - endpointCDF i y = 0 := by
  by_cases h : gridPoint i ≤ y
  · simp [endpointCDF, h, rowCDF_eq_one i h]
  have hl : y ≤ gridLeft i := by
    by_contra hh
    exact hy ⟨lt_of_not_ge hh, (lt_of_not_ge h).le⟩
  rw [rowCDF_eq_zero i hl]
  simp [endpointCDF, h]

lemma sum_row_error_le_one {n : ℕ} (hn : 0 < n) (y : I) :
    (∑ i : Fin n, (rowCDF i y - endpointCDF i y)) ≤ 1 := by
  by_cases hy : y = 0
  · subst y
    have he : ∀ i : Fin n, rowCDF i 0 - endpointCDF i 0 = 0 := by
      intro i
      apply row_error_zero_off_cell
      intro hi
      exact (not_lt_of_ge (show (0 : I) ≤ gridLeft i from bot_le)) hi.1
    simp [he]
  have hy' : y ∈ Ioi (0 : I) := lt_of_le_of_ne bot_le (Ne.symm hy)
  obtain ⟨j,hj⟩ := mem_iUnion.mp ((gridCell_cover hn).symm ▸ hy')
  rw [Finset.sum_eq_single j]
  · exact (row_error_bounds j y).2
  · intro i _ hij
    apply row_error_zero_off_cell
    exact fun hi => Set.disjoint_left.mp (gridCell_disjoint hij) hi hj
  · simp

lemma row_product_error {n : ℕ} (i j : Fin n) (x y : I) :
    0 ≤ rowCDF i x * rowCDF j y - endpointCDF i x * endpointCDF j y ∧
    rowCDF i x * rowCDF j y - endpointCDF i x * endpointCDF j y ≤
      (rowCDF i x - endpointCDF i x) + (rowCDF j y - endpointCDF j y) := by
  have hi := endpointCDF_bounds i x
  have hj := endpointCDF_bounds j y
  have hi' := rowCDF_bounds i x
  have hj' := rowCDF_bounds j y
  constructor
  · exact sub_nonneg.mpr (mul_le_mul hi.2 hj.2 hj.1 hi'.1)
  · have h1 := mul_nonneg (sub_nonneg.mpr hi.2) (sub_nonneg.mpr hj'.2)
    have h2 := mul_nonneg (sub_nonneg.mpr (hi.2.trans hi'.2)) (sub_nonneg.mpr hj.2)
    nlinarith

end PermutationCauchyProof
end
end

/- Source module: EmpiricalCDF -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory unitInterval PermLimits.Shared PermutationLimitProof Set

def probabilityCDF (μ : ProbabilityMeasure (I × I)) (x y : I) : ℝ :=
  (μ : Measure (I × I)).real (Iic x ×ˢ Iic y)

lemma empiricalCDF_sum {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) (x y : I) :
    probabilityCDF (empiricalLaw π) x y = (n : ℝ)⁻¹ *
      ∑ i : Fin n, endpointCDF i x * endpointCDF (π i) y := by
  have hm : MeasurableSet (Iic x ×ˢ Iic y) := measurableSet_Iic.prod measurableSet_Iic
  rw [probabilityCDF, ← integral_indicator_one hm]
  have hh : Measurable ((Iic x ×ˢ Iic y).indicator (1 : I × I → ℝ)) :=
    measurable_const.indicator hm
  rw [empirical_integral hn π _ hh]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Set.indicator, mem_prod, mem_Iic, endpointCDF]
  split_ifs <;> simp_all

lemma stepCDF_product_sum {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) (x y : I) :
    integratedCDF (stepLimit π) x y = (n : ℝ)⁻¹ *
      ∑ i : Fin n, rowCDF i x * rowCDF (π i) y := by
  rw [stepCDF_sum hn π, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [gridCell_prefix_volume]
  ring

lemma stepCDF_empirical_error {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) (x y : I) :
    |integratedCDF (stepLimit π) x y - probabilityCDF (empiricalLaw π) x y| ≤
      2 * (n : ℝ)⁻¹ := by
  rw [stepCDF_product_sum hn, empiricalCDF_sum hn, ← mul_sub, ← Finset.sum_sub_distrib]
  have hnon : 0 ≤ ∑ i : Fin n, (rowCDF i x * rowCDF (π i) y -
      endpointCDF i x * endpointCDF (π i) y) :=
    Finset.sum_nonneg (fun i _ => (row_product_error i (π i) x y).1)
  rw [abs_of_nonneg (mul_nonneg (by positivity) hnon)]
  have hsum : (∑ i : Fin n, (rowCDF i x * rowCDF (π i) y -
      endpointCDF i x * endpointCDF (π i) y)) ≤ 2 := by
    calc
      _ ≤ ∑ i : Fin n, ((rowCDF i x - endpointCDF i x) +
          (rowCDF (π i) y - endpointCDF (π i) y)) :=
        Finset.sum_le_sum (fun i _ => (row_product_error i (π i) x y).2)
      _ = (∑ i : Fin n, (rowCDF i x - endpointCDF i x)) +
          ∑ i : Fin n, (rowCDF i y - endpointCDF i y) := by
        rw [Finset.sum_add_distrib, Equiv.sum_comp π (fun i => rowCDF i y - endpointCDF i y)]
      _ ≤ 2 := by linarith [sum_row_error_le_one hn x, sum_row_error_le_one hn y]
  nlinarith [mul_le_mul_of_nonneg_left hsum (show 0 ≤ (n : ℝ)⁻¹ by positivity)]

end PermutationCauchyProof
end
end

/- Source module: CDFGeometry -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory unitInterval PermLimits.Shared PermutationLimitProof Set Filter Topology

lemma uniform_coordinate_null (μ : ProbabilityMeasure (I × I)) (c : I × I → I)
    (hc : Measurable c) (hm : (μ : Measure (I × I)).map c = volume) (a : I) :
    (μ : Measure (I × I)) (c ⁻¹' {a}) = 0 := by
  have h := congrArg (fun ν : Measure I => ν {a}) hm
  rw [Measure.map_apply hc (measurableSet_singleton a), measure_singleton] at h
  exact h

lemma lower_rectangle_frontier_null (μ : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (x y : I) :
    (μ : Measure (I × I)) (frontier (Iic x ×ˢ Iic y)) = 0 := by
  apply measure_mono_null (t := (Prod.fst ⁻¹' {x}) ∪ (Prod.snd ⁻¹' {y}))
  · rw [frontier_prod_eq]
    intro p hp
    rcases hp with hp | hp
    · exact Or.inr (frontier_Iic_subset y hp.2)
    · exact Or.inl (frontier_Iic_subset x hp.1)
  · exact measure_union_null
      (uniform_coordinate_null μ _ measurable_fst hμ.1 x)
      (uniform_coordinate_null μ _ measurable_snd hμ.2 y)

lemma probabilityCDF_tendsto {ι : Type*} {l : Filter ι} {μs : ι → ProbabilityMeasure (I × I)}
    {μ : ProbabilityMeasure (I × I)} (h : Tendsto μs l (𝓝 μ))
    (hμ : UniformMarginals μ) (x y : I) :
    Tendsto (fun j => probabilityCDF (μs j) x y) l (𝓝 (probabilityCDF μ x y)) := by
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h
      (lower_rectangle_frontier_null μ hμ x y))

lemma probabilityCDF_mono (μ : ProbabilityMeasure (I × I)) {a b c d : I}
    (hab : a ≤ b) (hcd : c ≤ d) : probabilityCDF μ a c ≤ probabilityCDF μ b d := by
  exact measureReal_mono (prod_mono (Iic_subset_Iic.mpr hab) (Iic_subset_Iic.mpr hcd))

lemma probabilityCDF_increment_x (μ : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) {a b : I} (hab : a ≤ b) (y : I) :
    probabilityCDF μ b y - probabilityCDF μ a y ≤ (b : ℝ) - a := by
  have hs : Iic a ×ˢ Iic y ⊆ Iic b ×ˢ Iic y := prod_mono (Iic_subset_Iic.mpr hab) Subset.rfl
  rw [probabilityCDF, probabilityCDF, ← measureReal_sdiff hs (measurableSet_Iic.prod measurableSet_Iic)]
  have hin : (Iic b ×ˢ Iic y) \ (Iic a ×ˢ Iic y) ⊆ Prod.fst ⁻¹' Ioc a b := by
    intro p hp
    refine ⟨?_,hp.1.1⟩
    by_contra hh
    exact hp.2 ⟨le_of_not_gt hh,hp.1.2⟩
  have hmap := congrArg (fun ν : Measure I => ν.real (Ioc a b)) hμ.1
  rw [map_measureReal_apply measurable_fst measurableSet_Ioc] at hmap
  have hm : (volume : Measure I).real (Ioc a b) = (b : ℝ) - a := by
    rw [measureReal_def, unitInterval.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  exact (measureReal_mono hin).trans_eq (hmap.trans hm)

lemma probabilityCDF_increment_y (μ : ProbabilityMeasure (I × I))
    (hμ : UniformMarginals μ) (x : I) {a b : I} (hab : a ≤ b) :
    probabilityCDF μ x b - probabilityCDF μ x a ≤ (b : ℝ) - a := by
  have hs : Iic x ×ˢ Iic a ⊆ Iic x ×ˢ Iic b := prod_mono Subset.rfl (Iic_subset_Iic.mpr hab)
  rw [probabilityCDF, probabilityCDF, ← measureReal_sdiff hs (measurableSet_Iic.prod measurableSet_Iic)]
  have hin : (Iic x ×ˢ Iic b) \ (Iic x ×ˢ Iic a) ⊆ Prod.snd ⁻¹' Ioc a b := by
    intro p hp
    refine ⟨?_,hp.1.2⟩
    by_contra hh
    exact hp.2 ⟨hp.1.1,le_of_not_gt hh⟩
  have hmap := congrArg (fun ν : Measure I => ν.real (Ioc a b)) hμ.2
  rw [map_measureReal_apply measurable_snd measurableSet_Ioc] at hmap
  have hm : (volume : Measure I).real (Ioc a b) = (b : ℝ) - a := by
    rw [measureReal_def, unitInterval.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  exact (measureReal_mono hin).trans_eq (hmap.trans hm)

end PermutationCauchyProof
end
end

/- Source module: CDFUniform -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory unitInterval PermLimits.Shared PermutationLimitProof Set Filter Topology

lemma grid_bracket {n : ℕ} (hn : 0 < n) (x : I) :
    ∃ i : Fin n, gridLeft i ≤ x ∧ x ≤ gridPoint i := by
  by_cases hx : x = 0
  · refine ⟨⟨0,hn⟩,?_,?_⟩
    · simp [hx,gridLeft]
    · exact hx ▸ bot_le
  have hx' : x ∈ Ioi (0 : I) := lt_of_le_of_ne bot_le (Ne.symm hx)
  obtain ⟨i,hi⟩ := mem_iUnion.mp ((gridCell_cover hn).symm ▸ hx')
  exact ⟨i,hi.1.le,hi.2⟩

lemma grid_width {n : ℕ} (i : Fin n) :
    (gridPoint i : ℝ) - gridLeft i = (n : ℝ)⁻¹ := by
  change ((i.val : ℝ) + 1) / n - i.val / n = _
  ring

lemma probabilityCDF_increment (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    {a b c d : I} (hab : a ≤ b) (hcd : c ≤ d) :
    probabilityCDF μ b d - probabilityCDF μ a c ≤ ((b : ℝ)-a) + ((d : ℝ)-c) := by
  linarith [probabilityCDF_increment_x μ hμ hab d, probabilityCDF_increment_y μ hμ a hcd]

lemma probabilityCDF_uniform_tendsto {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure (I × I)} {μ : ProbabilityMeasure (I × I)}
    (h : Tendsto μs l (𝓝 μ)) (hμ : UniformMarginals μ) :
    ∀ ε > 0, ∀ᶠ j in l, ∀ x y : I,
      |probabilityCDF (μs j) x y - probabilityCDF μ x y| < ε := by
  intro ε hε
  obtain ⟨n,hn,hmesh⟩ := Real.exists_nat_pos_inv_lt (show (0 : ℝ) < ε / 8 by positivity)
  have hleft : ∀ i k : Fin n, ∀ᶠ j in l,
      |probabilityCDF (μs j) (gridLeft i) (gridLeft k) -
        probabilityCDF μ (gridLeft i) (gridLeft k)| < ε / 2 := by
    intro i k
    have hh := probabilityCDF_tendsto h hμ (gridLeft i) (gridLeft k)
    have ha := (hh.sub_const (probabilityCDF μ (gridLeft i) (gridLeft k))).abs
    simpa using (tendsto_order.1 ha).2 (ε/2) (by simp; positivity)
  have hright : ∀ i k : Fin n, ∀ᶠ j in l,
      |probabilityCDF (μs j) (gridPoint i) (gridPoint k) -
        probabilityCDF μ (gridPoint i) (gridPoint k)| < ε / 2 := by
    intro i k
    have hh := probabilityCDF_tendsto h hμ (gridPoint i) (gridPoint k)
    have ha := hh.sub_const (probabilityCDF μ (gridPoint i) (gridPoint k))
    have hb := ha.abs
    simpa using (tendsto_order.1 hb).2 (ε/2) (by simp; positivity)
  have hleft' : ∀ᶠ j in l, ∀ i k : Fin n,
      |probabilityCDF (μs j) (gridLeft i) (gridLeft k) -
        probabilityCDF μ (gridLeft i) (gridLeft k)| < ε / 2 :=
    (eventually_all.mpr fun i => eventually_all.mpr (hleft i))
  have hright' : ∀ᶠ j in l, ∀ i k : Fin n,
      |probabilityCDF (μs j) (gridPoint i) (gridPoint k) -
        probabilityCDF μ (gridPoint i) (gridPoint k)| < ε / 2 :=
    (eventually_all.mpr fun i => eventually_all.mpr (hright i))
  filter_upwards [hleft',hright'] with j hjl hjr
  intro x y
  obtain ⟨i,hil,hir⟩ := grid_bracket hn x
  obtain ⟨k,hkl,hkr⟩ := grid_bracket hn y
  have hl := abs_lt.mp (hjl i k)
  have hr := abs_lt.mp (hjr i k)
  have hml := probabilityCDF_mono (μs j) hil hkl
  have hmr := probabilityCDF_mono (μs j) hir hkr
  have hul := probabilityCDF_increment μ hμ hil hkl
  have hur := probabilityCDF_increment μ hμ hir hkr
  have hw1 := grid_width i
  have hw2 := grid_width k
  have hil' : (gridLeft i : ℝ) ≤ x := hil
  have hir' : (x : ℝ) ≤ gridPoint i := hir
  have hkl' : (gridLeft k : ℝ) ≤ y := hkl
  have hkr' : (y : ℝ) ≤ gridPoint k := hkr
  rw [abs_lt]
  constructor <;> linarith

end PermutationCauchyProof
end
end

/- Source module: CDFIdentification -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory unitInterval PermutationLimitProof Set

def horizontalSection (μ : Measure (I × I)) (y : I) : Measure I :=
  (μ.restrict (univ ×ˢ Iic y)).map Prod.fst

lemma horizontalSection_apply (μ : Measure (I × I)) (y : I) (B : Set I)
    (hB : MeasurableSet B) : horizontalSection μ y B = μ (B ×ˢ Iic y) := by
  rw [horizontalSection, Measure.map_apply measurable_fst hB,
    Measure.restrict_apply (hB.preimage measurable_fst)]
  congr 1
  ext p
  simp

lemma probabilityCDF_injective (μ ν : ProbabilityMeasure (I × I))
    (h : ∀ x y, probabilityCDF μ x y = probabilityCDF ν x y) : μ = ν := by
  apply Subtype.ext
  apply measure_eq_of_lower_rectangles (μ : Measure (I × I)) (ν : Measure (I × I))
  intro B hB y
  have hμ : IsFiniteMeasure (horizontalSection (μ : Measure (I × I)) y) := by
    unfold horizontalSection; infer_instance
  have hν : IsFiniteMeasure (horizontalSection (ν : Measure (I × I)) y) := by
    unfold horizontalSection; infer_instance
  have he : horizontalSection (μ : Measure (I × I)) y =
      horizontalSection (ν : Measure (I × I)) y := by
    apply Measure.ext_of_Iic
    intro x
    rw [horizontalSection_apply _ _ _ measurableSet_Iic,
      horizontalSection_apply _ _ _ measurableSet_Iic]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (h x y)
  have hh := congrArg (fun ξ : Measure I => ξ B) he
  rw [horizontalSection_apply _ _ _ hB, horizontalSection_apply _ _ _ hB] at hh
  exact congrArg ENNReal.toReal hh

end PermutationCauchyProof
end
end

/- Source module: RectCauchyWeak -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory unitInterval PermLimits.Shared PermLimits.Cauchy PermutationLimitProof Set Filter Topology

lemma size_error_tendsto (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Tendsto (fun j => (s j).1) atTop atTop) :
    Tendsto (fun j => 2 * ((s j).1 : ℝ)⁻¹) atTop (𝓝 0) := by
  have hi : Tendsto (fun j => ((s j).1 : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hs
  simpa using hi.const_mul 2

lemma empiricalCDF_difference_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (π : Equiv.Perm (Fin n)) (ρ : Equiv.Perm (Fin m)) (x y : I) :
    |probabilityCDF (empiricalLaw π) x y - probabilityCDF (empiricalLaw ρ) x y| ≤
      2 * (n : ℝ)⁻¹ + rectDist (stepLimit π) (stepLimit ρ) + 2 * (m : ℝ)⁻¹ := by
  have h1 := abs_le.mp (stepCDF_empirical_error hn π x y)
  have h2 := abs_le.mp (stepCDF_empirical_error hm ρ x y)
  have h3 := abs_le.mp (stepCDF_difference_le_rectDist π ρ x y)
  rw [abs_le]
  constructor <;> linarith

lemma empiricalCDF_cauchy (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Tendsto (fun j => (s j).1) atTop atTop) (hc : IsRectCauchy s) (x y : I) :
    CauchySeq (fun j => probabilityCDF (empiricalLaw (s j).2) x y) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := hc (ε/3) (by positivity)
  have he := (size_error_tendsto s hs).eventually (gt_mem_nhds (show (0 : ℝ) < ε/3 by positivity))
  have hp := hs.eventually (eventually_gt_atTop 0)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (he.and hp)
  refine ⟨max N M, ?_⟩
  intro j hj k hk
  have hjN := (le_max_left N M).trans hj
  have hkN := (le_max_left N M).trans hk
  have hjM := hM j ((le_max_right N M).trans hj)
  have hkM := hM k ((le_max_right N M).trans hk)
  rw [Real.dist_eq]
  have hb := empiricalCDF_difference_le hjM.2 hkM.2 (s j).2 (s k).2 x y
  have hd := hN j k hjN hkN
  unfold permRectDist at hd
  linarith

lemma rectCauchy_has_weak_limit (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Tendsto (fun j => (s j).1) atTop atTop) (hc : IsRectCauchy s) :
    ∃ μ : ProbabilityMeasure (I × I), UniformMarginals μ ∧
      Tendsto (fun j => empiricalLaw (s j).2) atTop (𝓝 μ) := by
  obtain ⟨μ,φ,hφ,hweak⟩ := CompactSpace.tendsto_subseq (fun j => empiricalLaw (s j).2)
  have hsφ := hs.comp hφ.tendsto_atTop
  have hμ := empirical_limit_uniform (fun j => s (φ j)) hsφ hweak
  refine ⟨μ,hμ,tendsto_nhds_of_unique_mapClusterPt ?_⟩
  intro ν hνcluster
  obtain ⟨ψ,hψ,hνweak⟩ := hνcluster.tendsto_subseq
  have hsψ := hs.comp hψ.tendsto_atTop
  have hν := empirical_limit_uniform (fun j => s (ψ j)) hsψ hνweak
  apply probabilityCDF_injective
  intro x y
  have hfull := tendsto_nhds_of_cauchySeq_of_subseq (empiricalCDF_cauchy s hs hc x y)
    hφ.tendsto_atTop (probabilityCDF_tendsto hweak hμ x y)
  exact tendsto_nhds_unique (probabilityCDF_tendsto hνweak hν x y)
    (hfull.comp hψ.tendsto_atTop)

end PermutationCauchyProof
end
end

/- Source module: WeakRectCauchy -/
section

noncomputable section
namespace PermutationCauchyProof
open MeasureTheory unitInterval PermLimits.Shared PermLimits.Cauchy PermutationLimitProof Set Filter Topology

lemma weak_limit_rectCauchy (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Tendsto (fun j => (s j).1) atTop atTop)
    (μ : ProbabilityMeasure (I × I)) (hμ : UniformMarginals μ)
    (hw : Tendsto (fun j => empiricalLaw (s j).2) atTop (𝓝 μ)) : IsRectCauchy s := by
  intro ε hε
  have hu := probabilityCDF_uniform_tendsto hw hμ (ε/32) (by positivity)
  have he := (size_error_tendsto s hs).eventually (gt_mem_nhds (show (0 : ℝ) < ε/32 by positivity))
  have hp := hs.eventually (eventually_gt_atTop 0)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hu.and (he.and hp))
  refine ⟨N,?_⟩
  intro j k hj hk
  obtain ⟨hju,hje,hjp⟩ := hN j hj
  obtain ⟨hku,hke,hkp⟩ := hN k hk
  have hc : ∀ x y, |integratedCDF (stepLimit (s j).2) x y -
      integratedCDF (stepLimit (s k).2) x y| ≤ ε/8 := by
    intro x y
    have hj1 := abs_le.mp (stepCDF_empirical_error hjp (s j).2 x y)
    have hk1 := abs_le.mp (stepCDF_empirical_error hkp (s k).2 x y)
    have hj2 := abs_lt.mp (hju x y)
    have hk2 := abs_lt.mp (hku x y)
    rw [abs_le]
    constructor <;> linarith
  have hr := rectDist_le_of_cdf _ _ (stepLimit_integrable (s j).2)
    (stepLimit_integrable (s k).2) hc
  unfold permRectDist
  linarith

end PermutationCauchyProof
end
end


open PermLimits.Shared

namespace PermLimits.Cauchy

open Filter

/-- **Theorem 1.8, corrected** (Hoppen et al., *Limits of permutation sequences*,
arXiv:1103.5844v2, p. 5; proof p. 18). A permutation sequence `(σ_n)` with `|σ_n| → ∞` converges
(Definition 1.2) if and only if it is a Cauchy sequence with respect to the metric `d□`.

**Formalization Note (correction).** The paper states Theorem 1.8 for every permutation sequence.
Without `|σ_n| → ∞` the "if" direction is false: for `σ = id ∈ S₂` and permutations `τ_k` with
`|τ_k| → ∞` and `d□(Z_{τ_k}, Z_σ) → 0` (which exist by Lemma 4.2), the sequence
`σ, τ₁, σ, τ₂, …` is `d□`-Cauchy, while `t(σ, σ) = 1` and `t(σ, τ_k) → t(σ, Z_σ) = 3/4`, so it
is not convergent. The paper's reduction "By Claim 2.4 we may assume that `|σ_n| → ∞`" (p. 18) is
valid only for the "only if" direction, which is stated without the length hypothesis as the
separate theorem `cauchy_of_convergent`. "Converges" is Definition 1.2 (`IsConvergent`: every
density sequence converges); it does not assert a limit permutation. `d□` on permutations of
different lengths is `d□(Z_σ, Z_π)` (`permRectDist`, Sect. 4.1, pp. 12–13). The sequence is named
`s`. -/
theorem convergent_iff_cauchy_rectangular (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Tendsto (fun n => (s n).1) atTop atTop) :
    IsConvergent s ↔ IsRectCauchy s := by
  constructor
  · intro hc
    obtain ⟨μ,hμ,hw⟩ := PermutationCauchyProof.convergent_empirical_weak s hs hc
    exact PermutationCauchyProof.weak_limit_rectCauchy s hs μ hμ hw
  · intro hc
    obtain ⟨μ,hμ,hw⟩ := PermutationCauchyProof.rectCauchy_has_weak_limit s hs hc
    intro k τ
    exact ⟨PermutationLimitProof.patternProbability μ τ,
      PermutationLimitProof.empirical_weak_implies_densities s hs hw hμ τ⟩

end PermLimits.Cauchy


-- Exact public entrypoint expected by the proof submission checker.
theorem solution (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Filter.Tendsto (fun n => (s n).1) Filter.atTop Filter.atTop) :
    PermLimits.Shared.IsConvergent s ↔ PermLimits.Cauchy.IsRectCauchy s :=
  PermLimits.Cauchy.convergent_iff_cauchy_rectangular s hs
