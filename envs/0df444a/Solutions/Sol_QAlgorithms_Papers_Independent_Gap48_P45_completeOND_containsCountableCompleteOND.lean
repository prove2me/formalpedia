-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P45.completeOND_containsCountableCompleteOND
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:36:34.483503+00:00
-- url     : https://prove2.me/submissions/3badcad0-9e03-4642-a248-c6f7c721a66e

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45
noncomputable section

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace X4P45L7

/-- relation restricted to a set -/
def rel {α : Type} (F : Set α) (r : α → α → Prop) (x y : α) : Prop := x ∈ F ∧ y ∈ F ∧ r x y

lemma rel_mono {α : Type} {F G : Set α} {r : α → α → Prop} (h : F ⊆ G) {x y : α}
    (hxy : Relation.ReflTransGen (rel F r) x y) : Relation.ReflTransGen (rel G r) x y :=
by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hh ih => exact ih.tail ⟨h hh.1, h hh.2.1, hh.2.2⟩

lemma reach {α : Type} {S : Set α} {r : α → α → Prop} {a b : α} (ha : a ∈ S)
    (h : Relation.ReflTransGen (rel S r) a b) :
    ∃ F : Set α, F.Finite ∧ F ⊆ S ∧ a ∈ F ∧ b ∈ F ∧
      ∀ x ∈ F, Relation.ReflTransGen (rel F r) a x ∧ Relation.ReflTransGen (rel F r) x b := by
  induction h with
  | refl =>
    refine ⟨{a}, Set.finite_singleton a, by simpa using ha, rfl, rfl, ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx; exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨F, hF, hFS, haF, hbF, hall⟩ := ih
    have hsub : F ⊆ insert c F := Set.subset_insert c F
    have hbc' : rel (insert c F) r b c := ⟨hsub hbF, Set.mem_insert c F, hbc.2.2⟩
    refine ⟨insert c F, hF.insert c, Set.insert_subset hbc.2.1 hFS, hsub haF,
      Set.mem_insert c F, ?_⟩
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨(rel_mono hsub (hall b hbF).1).tail hbc', Relation.ReflTransGen.refl⟩
    · exact ⟨rel_mono hsub (hall x hx).1, (rel_mono hsub (hall x hx).2).tail hbc'⟩

lemma cross {α : Type} {T A : Set α} {r : α → α → Prop} {a b : α} (ha : a ∈ A)
    (h : Relation.ReflTransGen (rel T r) a b) (hb : b ∉ A) :
    ∃ u ∈ A, ∃ w ∈ T, w ∉ A ∧ r u w := by
  induction h with
  | refl => exact absurd ha hb
  | @tail c d _ hcd ih =>
    by_cases hc : c ∈ A
    · exact ⟨c, hc, d, hcd.2.1, hb, hcd.2.2⟩
    · exact ih hc


open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator)
open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)
open QAlgorithms.Papers.Independent.Gap48.P45

/-- the support vectors of a family -/
def V {I : Type} (S : Set (State I)) : Set (Hilbert I) :=
  {v | ∃ rho ∈ S, ∃ w, boundedOperator rho.coefficients w = v}

lemma gen_eq {I : Type} (S : Set (State I)) :
    generatedSpace S = (Submodule.span ℂ (V S)).topologicalClosure := rfl

lemma V_mono {I : Type} {S T : Set (State I)} (h : S ⊆ T) : V S ⊆ V T := by
  rintro v ⟨rho, hr, w, rfl⟩; exact ⟨rho, h hr, w, rfl⟩

lemma gen_mono {I : Type} {S T : Set (State I)} (h : S ⊆ T) :
    generatedSpace S ≤ generatedSpace T := by
  rw [gen_eq, gen_eq]
  exact Submodule.topologicalClosure_mono (Submodule.span_mono (V_mono h))

lemma top_of_single {I : Type} (K : Submodule ℂ (Hilbert I)) (hK : IsClosed (K : Set (Hilbert I)))
    (h : ∀ i, lp.single (E := fun _ : I => ℂ) 2 i 1 ∈ K) : K = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have hs := lp.hasSum_single (p := 2) (by norm_num) f
  refine hK.mem_of_tendsto hs (Eventually.of_forall fun s => ?_)
  refine K.sum_mem fun i _ => ?_
  have : lp.single 2 i (f i) = (f i) • lp.single (E := fun _ : I => ℂ) 2 i 1 := by
    rw [← lp.single_smul]; simp
  rw [this]; exact K.smul_mem _ (h i)

lemma exists_countable {I : Type} [Countable I] (S : Set (State I)) (h : CompleteFamily S) :
    ∃ D ⊆ S, D.Countable ∧ CompleteFamily D := by
  have key : ∀ (i : I) (k : ℕ), ∃ D : Set (State I), D.Finite ∧ D ⊆ S ∧
      ∃ y ∈ Submodule.span ℂ (V D), dist (lp.single (E := fun _ : I => ℂ) 2 i 1) y < 1 / ((k : ℝ) + 1) := by
    intro i k
    have hmem : lp.single (E := fun _ : I => ℂ) 2 i 1 ∈ generatedSpace S := by
      rw [show generatedSpace S = ⊤ from h]; trivial
    rw [gen_eq, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
    obtain ⟨y, hy, hd⟩ := hmem (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨T, hTV, hyT⟩ := Submodule.mem_span_finite_of_mem_span hy
    have hT : ∀ v ∈ T, ∃ rho ∈ S, ∃ w, boundedOperator rho.coefficients w = v :=
      fun v hv => hTV hv
    choose g hgS w hw using hT
    refine ⟨Set.range (fun v : {v // v ∈ T} => g v.1 v.2), Set.finite_range _, ?_, y, ?_, hd⟩
    · rintro _ ⟨v, rfl⟩; exact hgS _ _
    · refine Submodule.span_mono ?_ hyT
      intro v hv
      exact ⟨g v hv, ⟨⟨v, hv⟩, rfl⟩, w v hv, hw v hv⟩
  choose Df hfin hsub y hy hdist using key
  refine ⟨⋃ i, ⋃ k, Df i k, Set.iUnion_subset fun i => Set.iUnion_subset fun k => hsub i k,
    Set.countable_iUnion fun i => Set.countable_iUnion fun k => (hfin i k).countable, ?_⟩
  apply top_of_single _ (Submodule.isClosed_topologicalClosure _)
  intro i
  have hcl := Submodule.isClosed_topologicalClosure (Submodule.span ℂ (V (⋃ i, ⋃ k, Df i k)))
  show _ ∈ (Submodule.span ℂ (V (⋃ i, ⋃ k, Df i k))).topologicalClosure
  rw [← SetLike.mem_coe, ← hcl.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  refine ⟨y i k, ?_, (hdist i k).trans hk⟩
  have h1 : Df i k ⊆ ⋃ i, ⋃ k, Df i k := fun x hx =>
    Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨k, hx⟩⟩
  exact Submodule.le_topologicalClosure _ (Submodule.span_mono (V_mono h1) (hy i k))

end X4P45L7

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P07 (pureStates)
open QAlgorithms.Papers.Independent.Gap48.P45
open X4P45L7

theorem solution
    {I : Type} [Countable I] [Nonempty I]
    (S : Set (State I)) (hPure : S ⊆ pureStates I)
    (hComplete : CompleteFamily S) (hOND : OrthogonallyNondecomposable S) :
    ∃ T ⊆ S, T.Countable ∧ CompleteFamily T ∧ OrthogonallyNondecomposable T := by
  rcases Set.eq_empty_or_nonempty S with hS | ⟨d0, hd0⟩
  · exact ⟨S, subset_rfl, by simp [hS], hComplete, hOND⟩
  set r : State I → State I → Prop := fun a b => ¬ StatesOrthogonal a b with hr
  have fwd : ∀ x ∈ S, Relation.ReflTransGen (rel S r) d0 x := by
    by_contra hc
    push_neg at hc
    obtain ⟨x, hx, hnx⟩ := hc
    obtain ⟨rho, hrho, sigma, hsigma, hrs⟩ := hOND {y | y ∈ S ∧ Relation.ReflTransGen (rel S r) d0 y}
      (fun y hy => hy.1) ⟨d0, hd0, Relation.ReflTransGen.refl⟩ ⟨x, hx, fun h => hnx h.2⟩
    exact hsigma.2 ⟨hsigma.1, hrho.2.tail ⟨hrho.1, hsigma.1, hrs⟩⟩
  have bwd : ∀ x ∈ S, Relation.ReflTransGen (rel S r) x d0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨x, hx, hnx⟩ := hc
    obtain ⟨rho, hrho, sigma, hsigma, hrs⟩ :=
      hOND (S \ {y | y ∈ S ∧ Relation.ReflTransGen (rel S r) y d0}) Set.diff_subset
        ⟨x, hx, fun h => hnx h.2⟩
        ⟨d0, hd0, fun h => h.2 ⟨hd0, Relation.ReflTransGen.refl⟩⟩
    have hs : Relation.ReflTransGen (rel S r) sigma d0 := by
      by_contra hn
      exact hsigma.2 ⟨hsigma.1, fun h => hn h.2⟩
    exact hrho.2 ⟨hrho.1, Relation.ReflTransGen.head ⟨hrho.1, hsigma.1, hrs⟩ hs⟩
  have both : ∀ d ∈ S, ∃ G : Set (State I), G.Finite ∧ G ⊆ S ∧ d ∈ G ∧
      ∀ x ∈ G, Relation.ReflTransGen (rel G r) d0 x ∧ Relation.ReflTransGen (rel G r) x d0 := by
    intro d hd
    obtain ⟨F1, h1f, h1S, h1a, h1b, h1⟩ := reach hd0 (fwd d hd)
    obtain ⟨F2, h2f, h2S, h2a, h2b, h2⟩ := reach hd (bwd d hd)
    have s1 : F1 ⊆ F1 ∪ F2 := Set.subset_union_left
    have s2 : F2 ⊆ F1 ∪ F2 := Set.subset_union_right
    refine ⟨F1 ∪ F2, h1f.union h2f, Set.union_subset h1S h2S, Or.inl h1b, ?_⟩
    rintro x (hx | hx)
    · exact ⟨rel_mono s1 (h1 x hx).1, (rel_mono s1 (h1 x hx).2).trans (rel_mono s2 (h2 d h2a).2)⟩
    · exact ⟨(rel_mono s1 (h1 d h1b).1).trans (rel_mono s2 (h2 x hx).1), rel_mono s2 (h2 x hx).2⟩
  choose G hGf hGS hdG hG using both
  obtain ⟨D, hDS, hDc, hDcomp⟩ := exists_countable S hComplete
  have : Countable D := hDc.to_subtype
  refine ⟨⋃ d : D, G d.1 (hDS d.2), Set.iUnion_subset fun d => hGS _ _,
    Set.countable_iUnion fun d => (hGf _ _).countable, ?_, ?_⟩
  · have hDT : D ⊆ ⋃ d : D, G d.1 (hDS d.2) := fun d hd =>
      Set.mem_iUnion.2 ⟨⟨d, hd⟩, hdG _ _⟩
    unfold CompleteFamily at *
    rw [eq_top_iff, ← hDcomp]
    exact gen_mono hDT
  · intro A hA ⟨a, ha⟩ ⟨b, hb⟩
    have hsub : ∀ d : D, G d.1 (hDS d.2) ⊆ ⋃ d : D, G d.1 (hDS d.2) := fun d =>
      Set.subset_iUnion (fun d : D => G d.1 (hDS d.2)) d
    obtain ⟨da, hda⟩ := Set.mem_iUnion.1 (hA ha)
    obtain ⟨db, hdb⟩ := Set.mem_iUnion.1 hb.1
    have path := (rel_mono (hsub da) (hG _ _ a hda).2).trans (rel_mono (hsub db) (hG _ _ b hdb).1)
    obtain ⟨u, hu, w, hwT, hwA, huw⟩ := cross ha path hb.2
    exact ⟨u, hu, w, ⟨hwT, hwA⟩, huw⟩
