-- Prove2me | solution 1 for Plasticity.Polish.exists_isClosed_continuousOn_bijOn
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-11-18T20:10:12.425+00:00
-- url     : https://prove2.me/submissions/113d2c5e-0df0-4311-b5e0-44cbdeee8305

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.CantorScheme

namespace Sol_Plasticity_Polish_exists_isClosed_continuousOn_bijOn

open Set Filter Topology CantorScheme PiNat TopologicalSpace

section Split
variable {X : Type*} [MetricSpace X]

def FSigma (F : Set X) : Prop := ∃ D : ℕ → Set X, (∀ n, IsClosed (D n)) ∧ F = ⋃ n, D n

lemma FSigma.inter_open {E U : Set X} (hE : IsClosed E) (hU : IsOpen U) : FSigma (E ∩ U) := by
  obtain ⟨F, hF, -, rfl, -⟩ := hU.exists_iUnion_isClosed
  exact ⟨fun n => E ∩ F n, fun n => hE.inter (hF n), by rw [inter_iUnion]⟩

lemma split [SeparableSpace X] [Nonempty X] {F : Set X} (hF : FSigma F) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : ℕ → Set X, (∀ n, FSigma (S n)) ∧ (⋃ n, S n) = F ∧ Pairwise (Function.onFun Disjoint S) ∧
      (∀ n, closure (S n) ⊆ F) ∧ ∀ n, Metric.ediam (S n) ≤ ENNReal.ofReal ε := by
  obtain ⟨D, hD, rfl⟩ := hF
  let c := TopologicalSpace.denseSeq X
  let E : ℕ → Set X := fun j => D (Nat.unpair j).1 ∩ Metric.closedBall (c (Nat.unpair j).2) (ε / 2)
  have hEc : ∀ j, IsClosed (E j) := fun j => (hD _).inter Metric.isClosed_closedBall
  have hEU : (⋃ j, E j) = ⋃ n, D n := by
    ext x
    simp only [mem_iUnion, E, mem_inter_iff, Metric.mem_closedBall]
    constructor
    · rintro ⟨j, h, -⟩; exact ⟨_, h⟩
    · rintro ⟨n, hn⟩
      obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq X) x (ε / 2) (by linarith)
      exact ⟨Nat.pair n k, by simpa [c] using ⟨hn, hk.le⟩⟩
  have hEsub : ∀ j, E j ⊆ ⋃ n, D n := fun j => hEU ▸ subset_iUnion E j
  refine ⟨disjointed E, ?_, ?_, disjoint_disjointed E, ?_, ?_⟩
  · intro j
    rw [disjointed_eq_inter_compl]
    apply FSigma.inter_open (hEc j)
    apply (Set.finite_Iio j).isOpen_biInter
    intro i _
    exact (hEc i).isOpen_compl
  · rw [iUnion_disjointed, hEU]
  · intro j
    exact (closure_mono (disjointed_subset E j)).trans ((closure_minimal le_rfl (hEc j) |> fun h => h) |>.trans (hEsub j))
  · intro j
    refine (Metric.ediam_mono (disjointed_subset E j)).trans ?_
    refine EMetric.diam_le fun x hx y hy => ?_
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have h1 := Metric.mem_closedBall.1 hx.2
    have h2 := Metric.mem_closedBall.1 hy.2
    calc dist x y ≤ dist x _ + dist y _ := dist_triangle_right _ _ _
      _ ≤ ε := by linarith
end Split

section Scheme
variable {X : Type*} [MetricSpace X]

def SplitProps (S : Set X → ℝ → ℕ → Set X) : Prop :=
  ∀ F ε, FSigma F → 0 < ε →
    (∀ n, FSigma (S F ε n)) ∧ (⋃ n, S F ε n) = F ∧ Pairwise (Function.onFun Disjoint (S F ε)) ∧
      (∀ n, closure (S F ε n) ⊆ F) ∧ ∀ n, Metric.ediam (S F ε n) ≤ ENNReal.ofReal ε

lemma exists_splitProps [SeparableSpace X] [Nonempty X] : ∃ S : Set X → ℝ → ℕ → Set X, SplitProps S := by
  have : ∀ (p : Set X × ℝ), ∃ T : ℕ → Set X, FSigma p.1 → 0 < p.2 →
      (∀ n, FSigma (T n)) ∧ (⋃ n, T n) = p.1 ∧ Pairwise (Function.onFun Disjoint T) ∧
      (∀ n, closure (T n) ⊆ p.1) ∧ ∀ n, Metric.ediam (T n) ≤ ENNReal.ofReal p.2 := by
    intro p
    by_cases h : FSigma p.1 ∧ 0 < p.2
    · obtain ⟨T, hT⟩ := split h.1 h.2
      exact ⟨T, fun _ _ => hT⟩
    · exact ⟨fun _ => ∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose T hT using this
  exact ⟨fun F ε => T (F, ε), fun F ε => hT (F, ε)⟩

variable (S : Set X → ℝ → ℕ → Set X)

noncomputable def sch : List ℕ → Set X
  | [] => univ
  | n :: l => S (sch l) ((1 / 2) ^ l.length) n

variable {S}

lemma hpos (l : List ℕ) : (0:ℝ) < (1 / 2) ^ l.length := by positivity

lemma sch_fsigma (hS : SplitProps S) : ∀ l, FSigma (sch S l)
  | [] => ⟨fun _ => univ, fun _ => isClosed_univ, by simp [sch, iUnion_const]⟩
  | n :: l => (hS _ _ (sch_fsigma hS l) (hpos l)).1 n

lemma sch_closure (hS : SplitProps S) : ClosureAntitone (sch S) := by
  intro l a
  exact (hS _ _ (sch_fsigma hS l) (hpos l)).2.2.2.1 a

lemma sch_disjoint (hS : SplitProps S) : CantorScheme.Disjoint (sch S) := by
  intro l a b hab
  exact (hS _ _ (sch_fsigma hS l) (hpos l)).2.2.1 hab

lemma sch_cover (hS : SplitProps S) (l : List ℕ) {y : X} (hy : y ∈ sch S l) :
    ∃ n, y ∈ sch S (n :: l) := by
  have := (hS _ _ (sch_fsigma hS l) (hpos l)).2.1
  rw [← this] at hy
  simp only [mem_iUnion] at hy
  exact hy

lemma sch_vanish (hS : SplitProps S) : VanishingDiam (sch S) := by
  intro x
  have h : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num))
    simpa using ENNReal.tendsto_ofReal this
  rw [← tendsto_add_atTop_iff_nat 1]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) ?_
  intro n
  show Metric.ediam (sch S (res x (n+1))) ≤ _
  have := (hS _ _ (sch_fsigma hS (res x n)) (hpos (res x n))).2.2.2.2 (x n)
  simpa [res_succ, sch, res_length] using this
end Scheme

section Core
variable {X : Type*} [MetricSpace X]

lemma domain_eq {S : Set X → ℝ → ℕ → Set X} [CompleteSpace X] (hS : SplitProps S) :
    (inducedMap (sch S)).1 = {x | ∀ n, (sch S (res x n)).Nonempty} := by
  ext x
  constructor
  · intro hx n
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, mem_iInter.1 hy n⟩
  · intro hx
    choose u hu using hx
    have umem : ∀ n m : ℕ, n ≤ m → u m ∈ sch S (res x n) := by
      have : Antitone fun n : ℕ => sch S (res x n) := by
        refine antitone_nat_of_succ_le ?_
        intro n
        exact (sch_closure hS).antitone _ _
      intro n m hnm
      exact this hnm (hu _)
    have : CauchySeq u := by
      rw [Metric.cauchySeq_iff]
      intro ε ε_pos
      obtain ⟨n, hn⟩ := (sch_vanish hS).dist_lt _ ε_pos x
      use n
      intro m₀ hm₀ m₁ hm₁
      apply hn <;> apply umem <;> assumption
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete this
    refine ⟨y, mem_iInter.2 fun n => ?_⟩
    apply sch_closure hS _ (x n)
    apply mem_closure_of_tendsto hy
    rw [eventually_atTop]
    exact ⟨n.succ, umem _⟩

lemma domain_closed (A : List ℕ → Set X) : IsClosed {x : ℕ → ℕ | ∀ n, (A (res x n)).Nonempty} := by
  have hc : ∀ n, IsClopen {x : ℕ → ℕ | (A (res x n)).Nonempty} := by
    intro n
    have key : ∀ x y : ℕ → ℕ, y ∈ cylinder x n → res y n = res x n := fun x y hy =>
      res_eq_res.2 fun m hm => (mem_cylinder_iff.1 hy m hm)
    have hloc : ∀ P : Set (ℕ → ℕ), (∀ x y, y ∈ cylinder x n → (x ∈ P ↔ y ∈ P)) → IsClopen P := by
      intro P hP
      constructor
      · rw [← isOpen_compl_iff]
        refine isOpen_iff_forall_mem_open.2 fun x hx => ⟨cylinder x n, ?_, isOpen_cylinder (E := fun _ => ℕ) x n, mem_cylinder_iff.2 fun _ _ => rfl⟩
        intro y hy hyP
        exact hx ((hP x y hy).2 hyP)
      · refine isOpen_iff_forall_mem_open.2 fun x hx => ⟨cylinder x n, ?_, isOpen_cylinder (E := fun _ => ℕ) x n, mem_cylinder_iff.2 fun _ _ => rfl⟩
        intro y hy
        exact (hP x y hy).1 hx
    apply hloc
    intro x y hy
    simp only [mem_ofPred_eq, key x y hy]
  have : {x : ℕ → ℕ | ∀ n, (A (res x n)).Nonempty} = ⋂ n, {x : ℕ → ℕ | (A (res x n)).Nonempty} := by
    ext; simp
  rw [this]
  exact isClosed_iInter fun n => (hc n).isClosed

lemma core_metric [CompleteSpace X] [SeparableSpace X] [Nonempty X] :
    ∃ C : Set (ℕ → ℕ), IsClosed C ∧ ∃ φ : (ℕ → ℕ) → X, ContinuousOn φ C ∧ BijOn φ C univ := by
  obtain ⟨S, hS⟩ := exists_splitProps (X := X)
  have hD := domain_eq hS
  refine ⟨(inducedMap (sch S)).1, hD ▸ domain_closed _, ?_⟩
  classical
  let φ : (ℕ → ℕ) → X := fun b =>
    if h : b ∈ (inducedMap (sch S)).1 then (inducedMap (sch S)).2 ⟨b, h⟩ else Classical.arbitrary X
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (inducedMap (sch S)).1.domRestrict φ = (inducedMap (sch S)).2 := by
      funext x; simp [φ, Set.domRestrict, x.2]
    rw [this]
    exact (sch_vanish hS).map_continuous
  · intro _ _; trivial
  · intro a ha b hb hab
    have := (sch_disjoint hS).map_injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩)
      (by simpa [φ, ha, hb] using hab)
    simpa using congrArg Subtype.val this
  · intro y _
    let seq : ℕ → {l : List ℕ // y ∈ sch S l} := fun k =>
      Nat.rec ⟨[], mem_univ y⟩ (fun _ p => ⟨Classical.choose (sch_cover hS p.1 p.2) :: p.1,
        Classical.choose_spec (sch_cover hS p.1 p.2)⟩) k
    let b : ℕ → ℕ := fun k => Classical.choose (sch_cover hS (seq k).1 (seq k).2)
    have hres : ∀ k, res b k = (seq k).1 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [res_succ, ih]
    have hb : b ∈ (inducedMap (sch S)).1 := by
      refine ⟨y, mem_iInter.2 fun k => ?_⟩
      rw [hres]; exact (seq k).2
    refine ⟨b, hb, ?_⟩
    have hmem := (inducedMap (sch S)).2 ⟨b, hb⟩
    have := (sch_disjoint hS)
    -- uniqueness of the point on the branch
    have hy : y ∈ ⋂ k, sch S (res b k) := mem_iInter.2 fun k => by rw [hres]; exact (seq k).2
    have hp : (inducedMap (sch S)).2 ⟨b, hb⟩ ∈ ⋂ k, sch S (res b k) :=
      mem_iInter.2 fun k => map_mem ⟨b, hb⟩ k
    have hsub : ∀ z ∈ ⋂ k, sch S (res b k), z = y := by
      intro z hz
      by_contra hne
      have hd : 0 < dist z y := dist_pos.2 hne
      obtain ⟨n, hn⟩ := (sch_vanish hS).dist_lt _ hd b
      exact absurd (hn z (mem_iInter.1 hz n) y (mem_iInter.1 hy n)) (lt_irrefl _)
    simp only [φ, dif_pos hb]
    exact hsub _ hp
end Core

lemma core_polish (Z : Type*) [TopologicalSpace Z] [PolishSpace Z] [Nonempty Z] :
    ∃ C : Set (ℕ → ℕ), IsClosed C ∧ ∃ φ : (ℕ → ℕ) → Z, ContinuousOn φ C ∧ BijOn φ C univ := by
  letI := upgradeIsCompletelyMetrizable Z
  exact core_metric

lemma main {Y : Type*} (t : TopologicalSpace Y) (t' : TopologicalSpace Y) (ht' : t' ≤ t)
    (hP : @PolishSpace Y t') [Nonempty Y] (M : Set Y) (hcl : IsClosed[t'] M) (hMe : M ≠ ∅) :
    ∃ C : Set (ℕ → ℕ), IsClosed C ∧ ∃ φ : (ℕ → ℕ) → Y,
      @ContinuousOn _ _ _ t φ C ∧ Set.BijOn φ C M := by
  have : Nonempty M := (Set.nonempty_iff_ne_empty.2 hMe).to_subtype
  obtain ⟨C, hC, φ, hφ, hbij⟩ := @core_polish M
    (@instTopologicalSpaceSubtype Y _ t') (@IsClosed.polishSpace Y t' hP M hcl) _
  have h1 : @Continuous M Y (@instTopologicalSpaceSubtype Y _ t') t' Subtype.val :=
    @continuous_subtype_val Y t' _
  have hcont : @Continuous M Y (@instTopologicalSpaceSubtype Y _ t') t Subtype.val :=
    @Continuous.comp M Y Y (@instTopologicalSpaceSubtype Y _ t') t' t Subtype.val id
      (@continuous_id_of_le Y t' t ht') h1
  refine ⟨C, hC, fun b => (φ b : Y), @Continuous.comp_continuousOn (ℕ → ℕ) M Y _ (@instTopologicalSpaceSubtype Y _ t') t Subtype.val φ C hcont hφ, ?_, ?_, ?_⟩
  · intro b _; exact (φ b).2
  · intro a ha b hb hab
    exact hbij.injOn ha hb (Subtype.ext hab)
  · intro y hy
    obtain ⟨b, hb, hb2⟩ := hbij.surjOn (Set.mem_univ (⟨y, hy⟩ : M))
    exact ⟨b, hb, by simp [hb2]⟩

end Sol_Plasticity_Polish_exists_isClosed_continuousOn_bijOn

theorem solution {Y : Type*} [TopologicalSpace Y] [PolishSpace Y] [Nonempty Y]
    [MeasurableSpace Y] [BorelSpace Y] (M : Set Y) (hM : MeasurableSet M) :
    ∃ C : Set (ℕ → ℕ), IsClosed C ∧ ∃ φ : (ℕ → ℕ) → Y, ContinuousOn φ C ∧ Set.BijOn φ C M := by
  by_cases hMe : M = ∅
  · subst hMe
    exact ⟨∅, isClosed_empty, fun _ => Classical.arbitrary Y, continuousOn_empty _, by simp⟩
  obtain ⟨t', ht', hP, hcl, -⟩ := hM.isClopenable
  exact Sol_Plasticity_Polish_exists_isClosed_continuousOn_bijOn.main _ t' ht' hP M hcl hMe
