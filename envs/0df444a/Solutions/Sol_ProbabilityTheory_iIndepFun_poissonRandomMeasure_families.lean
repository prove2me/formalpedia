-- Prove2me | solution 1 for ProbabilityTheory.iIndepFun_poissonRandomMeasure_families
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:41:36.522992+00:00
-- url     : https://prove2.me/submissions/004a1483-fc75-4ae8-a140-e9c63d505917

import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_LeanLevy_Probability_IndependenceGrouping
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_charFunDual_pi_thinnedCount
import Theorems.Thm_ProbabilityTheory_iIndepFun_setRestrict_of_pairwiseDisjoint
import Theorems.Thm_ProbabilityTheory_iIndepFun_poissonRandomMeasure_apply
import Mathlib.MeasureTheory.PiSystem
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E}
section Atomization
variable {ι : Type} {B : ι → Set E}
private def evalAtom (B : ι → Set E) (J : Finset ι) : Set E := if J.Nonempty then (⋂ i ∈ J, B i) ∩ ⋂ i ∉ J, (B i)ᶜ else ∅
omit [MeasurableSpace E] in
private lemma evalAtom_of_nonempty {J : Finset ι} (hJ : J.Nonempty) :
    evalAtom B J = (⋂ i ∈ J, B i) ∩ ⋂ i ∉ J, (B i)ᶜ :=
  if_pos hJ
omit [MeasurableSpace E] in
private lemma evalAtom_empty : evalAtom B ∅ = ∅ :=
  if_neg (by simp)
omit [MeasurableSpace E] in
private lemma evalAtom_subset {J : Finset ι} {i : ι} (hiJ : i ∈ J) :
    evalAtom B J ⊆ B i := by
  rw [evalAtom_of_nonempty ⟨i, hiJ⟩]
  exact Set.inter_subset_left.trans (Set.iInter₂_subset i hiJ)
omit [MeasurableSpace E] in
private lemma evalAtom_subset_compl {J : Finset ι} {i : ι} (hJ : J.Nonempty)
    (hiJ : i ∉ J) : evalAtom B J ⊆ (B i)ᶜ := by
  rw [evalAtom_of_nonempty hJ]
  exact Set.inter_subset_right.trans (Set.iInter₂_subset i hiJ)
omit [MeasurableSpace E] in
private lemma evalAtom_subset_iUnion {J : Finset ι} :
    evalAtom B J ⊆ ⋃ i, B i := by
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · rw [evalAtom_empty]; exact Set.empty_subset _
  · obtain ⟨i, hi⟩ := hJ
    exact (evalAtom_subset hi).trans (Set.subset_iUnion _ i)
private lemma measurableSet_evalAtom [Fintype ι] (hBm : ∀ i, MeasurableSet (B i))
    (J : Finset ι) : MeasurableSet (evalAtom B J) := by
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · rw [evalAtom_empty]; exact MeasurableSet.empty
  · rw [evalAtom_of_nonempty hJ]
    exact (Finset.measurableSet_biInter J fun i _ => hBm i).inter
      (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => (hBm i).compl)
private lemma measure_evalAtom_lt_top (hBfin : ∀ i, m (B i) < ⊤) (J : Finset ι) :
    m (evalAtom B J) < ⊤ := by
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · rw [evalAtom_empty, measure_empty]; exact ENNReal.zero_lt_top
  · obtain ⟨i, hi⟩ := hJ
    exact lt_of_le_of_lt (measure_mono (evalAtom_subset hi)) (hBfin i)
omit [MeasurableSpace E] in
private lemma disjoint_evalAtom_of_mem_notMem {J J' : Finset ι} {i : ι}
    (hiJ : i ∈ J) (hiJ' : i ∉ J') : Disjoint (evalAtom B J) (evalAtom B J') := by
  rcases J'.eq_empty_or_nonempty with rfl | hJ'
  · rw [evalAtom_empty]; exact disjoint_bot_right
  · exact Disjoint.mono (evalAtom_subset hiJ) (evalAtom_subset_compl hJ' hiJ') disjoint_compl_right
omit [MeasurableSpace E] in
private lemma pairwise_disjoint_evalAtom :
    Pairwise (Function.onFun Disjoint (evalAtom B)) := by
  intro J J' hJJ'
  show Disjoint (evalAtom B J) (evalAtom B J')
  have hne : ¬ ∀ i, i ∈ J ↔ i ∈ J' := fun h => hJJ' (Finset.ext h)
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  rcases hi with ⟨hiJ, hiJ'⟩ | ⟨hiJ, hiJ'⟩
  · exact disjoint_evalAtom_of_mem_notMem hiJ hiJ'
  · exact (disjoint_evalAtom_of_mem_notMem hiJ' hiJ).symm
omit [MeasurableSpace E] in
private lemma biUnion_evalAtom [Fintype ι] [DecidableEq ι] (i : ι) :
    B i = ⋃ J ∈ Finset.univ.filter (fun J => i ∈ J), evalAtom B J := by
  classical
  ext x
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
  constructor
  · intro hx
    refine ⟨Finset.univ.filter (fun j => x ∈ B j), Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩, ?_⟩
    have hne : (Finset.univ.filter (fun j => x ∈ B j)).Nonempty :=
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩⟩
    rw [evalAtom_of_nonempty hne]
    refine ⟨Set.mem_iInter₂.mpr fun j hj => (Finset.mem_filter.mp hj).2, ?_⟩
    exact Set.mem_iInter₂.mpr fun j hj hxBj =>
      hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hxBj⟩)
  · rintro ⟨J, hiJ, hxJ⟩
    exact evalAtom_subset hiJ hxJ
omit [MeasurableSpace Ω] in
private lemma poissonRandomMeasure_apply_biUnion_evalAtom [Fintype ι] [DecidableEq ι]
    (hBm : ∀ i, MeasurableSet (B i)) (ω : Ω) (i : ι) :
    poissonRandomMeasure K X ω (B i)
      = ∑ J ∈ Finset.univ.filter (fun J => i ∈ J),
          poissonRandomMeasure K X ω (evalAtom B J) := by
  conv_lhs => rw [biUnion_evalAtom (B := B) i]
  rw [measure_biUnion_finset (pairwise_disjoint_evalAtom.set_pairwise _)
    (fun J _ => measurableSet_evalAtom hBm J)]
end Atomization
section Independence
variable {μ : Measure Ω} [SigmaFinite m] [Nonempty E]
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {ι : Type} [Fintype ι] {ιB : ι → Type}
    [∀ i, Fintype (ιB i)] {B : ∀ i, ιB i → Set E}
    (hBm : ∀ i b, MeasurableSet (B i b)) (hBfin : ∀ i b, m (B i b) < ⊤)
    (hBdisj : ∀ i j, i ≠ j → ∀ b b', Disjoint (B i b) (B j b')) :
    iIndepFun (fun i ω (b : ιB i) => poissonRandomMeasure K X ω (B i b)) μ := by
  classical
  set A : (Σ i, Finset (ιB i)) → Set E := fun σ => evalAtom (B σ.1) σ.2 with hA
  have hAm : ∀ σ, MeasurableSet (A σ) := fun σ => measurableSet_evalAtom (hBm σ.1) σ.2
  have hAfin : ∀ σ, m (A σ) < ⊤ := fun σ => measure_evalAtom_lt_top (hBfin σ.1) σ.2
  have hAdisj : Pairwise (Function.onFun Disjoint A) := by
    rintro ⟨i, J⟩ ⟨i', J'⟩ hne
    show Disjoint (evalAtom (B i) J) (evalAtom (B i') J')
    by_cases hii : i = i'
    · subst hii
      exact pairwise_disjoint_evalAtom (fun hJ => hne (by rw [hJ]))
    · have hU : Disjoint (⋃ b, B i b) (⋃ b', B i' b') :=
        Set.disjoint_iUnion_left.mpr fun b =>
          Set.disjoint_iUnion_right.mpr fun b' => hBdisj i i' hii b b'
      exact hU.mono evalAtom_subset_iUnion evalAtom_subset_iUnion
  have hiIndep := iIndepFun_poissonRandomMeasure_apply hd hAm hAfin hAdisj
  have hmeas : ∀ σ, Measurable (fun ω => poissonRandomMeasure K X ω (A σ)) :=
    fun σ => measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point (hAm σ)
  have hSdisj : Pairwise (Function.onFun Disjoint
      (fun i => {σ : Σ i, Finset (ιB i) | σ.1 = i})) := by
    intro i i' hii
    show Disjoint {σ : Σ i, Finset (ιB i) | σ.1 = i} {σ | σ.1 = i'}
    rw [Set.disjoint_left]
    rintro σ hσ hσ'
    simp only [Set.mem_setOf_eq] at hσ hσ'
    exact hii (hσ.symm.trans hσ')
  have hblocks := hiIndep.setRestrict_of_pairwiseDisjoint hmeas hSdisj
  set G : ∀ i, (↥{σ : Σ i, Finset (ιB i) | σ.1 = i} → ℝ≥0∞) → (ιB i → ℝ≥0∞) :=
    fun i g b => ∑ J ∈ Finset.univ.filter (fun J => b ∈ J), g ⟨⟨i, J⟩, rfl⟩ with hG
  have hGmeas : ∀ i, Measurable (G i) := fun i => by
    rw [hG]
    exact measurable_pi_lambda _ fun b =>
      Finset.measurable_sum _ fun J _ => measurable_pi_apply _
  have hcomp := hblocks.comp G hGmeas
  have heq : (fun i ω (b : ιB i) => poissonRandomMeasure K X ω (B i b))
      = fun i => G i ∘ (fun ω => ({σ : Σ i, Finset (ιB i) | σ.1 = i}).restrict
          fun σ => poissonRandomMeasure K X ω (A σ)) := by
    funext i ω b
    rw [poissonRandomMeasure_apply_biUnion_evalAtom (hBm i) ω b]
    simp only [Function.comp_apply, hG, Set.restrict_apply, hA]
    rfl
  rw [heq]
  exact hcomp
end Independence
