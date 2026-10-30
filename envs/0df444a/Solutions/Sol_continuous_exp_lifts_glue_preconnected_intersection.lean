-- Prove2me | solution 1 for continuous_exp_lifts_glue_preconnected_intersection
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T01:58:07.903534+00:00
-- url     : https://prove2.me/submissions/2ffaf7b2-8417-44f5-96a2-9daff4f337d4

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Piecewise

open Set

/-- The fiber of the complex exponential over one is countable. -/
lemma complex_exp_one_fiber_countable : {z : ℂ | Complex.exp z = 1}.Countable := by
  apply (Set.countable_range (fun n : ℤ => (n : ℂ) * (2 * Real.pi * Complex.I))).mono
  intro z hz
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hz
  exact ⟨n, hn.symm⟩

/-- Two continuous lifts with equal exponentials differ by a constant on a preconnected set. -/
lemma exp_lifts_diff_constant_on_preconnected {X : Type} [TopologicalSpace X]
    (W : Set X) (f g : X → ℂ) (hW : IsPreconnected W)
    (hf : ContinuousOn f W) (hg : ContinuousOn g W)
    (heq : EqOn (fun x => Complex.exp (f x)) (fun x => Complex.exp (g x)) W)
    (p : X) (hp : p ∈ W) :
    ∀ x ∈ W, f x - g x = f p - g p := by
  let H : X → ℂ := fun x => f x - g x
  have hH : ContinuousOn H W := hf.sub hg
  have hconnected : IsPreconnected (H '' W) := hW.image H hH
  have hsubset : H '' W ⊆ {z : ℂ | Complex.exp z = 1} := by
    rintro z ⟨x, hx, rfl⟩
    change Complex.exp (f x - g x) = 1
    exact Complex.exp_eq_exp_iff_exp_sub_eq_one.mp (heq hx)
  have hsub : (H '' W).Subsingleton :=
    complex_exp_one_fiber_countable.isTotallyDisconnected _ hsubset hconnected
  intro x hx
  exact hsub ⟨x, hx, rfl⟩ ⟨p, hp, rfl⟩

/-- Exponential lifts on closed sets with connected nonempty overlap glue after a
constant adjustment, retaining the original exponentials on each set. -/
lemma glue_exp_lifts_connected {X : Type} [TopologicalSpace X]
    (S T : Set X) (f g : X → ℂ) (hS : IsClosed S) (hT : IsClosed T)
    (hW : IsConnected (S ∩ T)) (hf : ContinuousOn f S) (hg : ContinuousOn g T)
    (heq : EqOn (fun x => Complex.exp (f x)) (fun x => Complex.exp (g x)) (S ∩ T)) :
    ∃ k : X → ℂ, ContinuousOn k (S ∪ T) ∧
      EqOn (fun x => Complex.exp (k x)) (fun x => Complex.exp (f x)) S ∧
      EqOn (fun x => Complex.exp (k x)) (fun x => Complex.exp (g x)) T := by
  classical
  obtain ⟨p, hp⟩ := hW.nonempty
  have hd := exp_lifts_diff_constant_on_preconnected (S ∩ T) f g hW.isPreconnected
    (hf.mono inter_subset_left) (hg.mono inter_subset_right) heq p hp
  let k := S.piecewise f (fun x => g x + (f p - g p))
  have hks : EqOn k f S := by
    intro x hx
    simp [k, hx]
  have hkt : EqOn k (fun x => g x + (f p - g p)) T := by
    intro x hx
    by_cases hxS : x ∈ S
    · have hdiff := hd x ⟨hxS, hx⟩
      have hmatch : f x = g x + (f p - g p) := by
        calc
          f x = (f x - g x) + g x := by abel
          _ = (f p - g p) + g x := by rw [hdiff]
          _ = g x + (f p - g p) := add_comm _ _
      simpa [k, hxS] using hmatch
    · simp [k, hxS]
  have hkcS : ContinuousOn k S := hf.congr hks
  have hkcT : ContinuousOn k T := (hg.add continuousOn_const).congr hkt
  have hkc : ContinuousOn k (S ∪ T) := hkcS.union_of_isClosed hkcT hS hT
  have heqp : Complex.exp (f p) = Complex.exp (g p) := heq hp
  refine ⟨k, hkc, ?_, ?_⟩
  · intro x hx
    change Complex.exp (k x) = Complex.exp (f x)
    rw [hks hx]
  · intro x hx
    change Complex.exp (k x) = Complex.exp (g x)
    rw [hkt hx, Complex.exp_add, Complex.exp_sub, heqp]
    simp [Complex.exp_ne_zero]


/-- Exponential lifts glue across any preconnected overlap, including the empty case. -/
theorem solution {X : Type} [TopologicalSpace X]
    (S T : Set X) (f g : X → ℂ) (hS : IsClosed S) (hT : IsClosed T)
    (hW : IsPreconnected (S ∩ T)) (hf : ContinuousOn f S) (hg : ContinuousOn g T)
    (heq : EqOn (fun x => Complex.exp (f x)) (fun x => Complex.exp (g x)) (S ∩ T)) :
    ∃ k : X → ℂ, ContinuousOn k (S ∪ T) ∧
      EqOn (fun x => Complex.exp (k x)) (fun x => Complex.exp (f x)) S ∧
      EqOn (fun x => Complex.exp (k x)) (fun x => Complex.exp (g x)) T := by
  classical
  by_cases hne : (S ∩ T).Nonempty
  · exact glue_exp_lifts_connected S T f g hS hT ⟨hne, hW⟩ hf hg heq
  · have hd : Disjoint S T := Set.disjoint_iff_inter_eq_empty.mpr
      (Set.not_nonempty_iff_eq_empty.mp hne)
    let k := S.piecewise f g
    have hks : EqOn k f S := by
      intro x hx
      simp [k, hx]
    have hkt : EqOn k g T := by
      intro x hx
      have hxS : x ∉ S := fun hs => Set.disjoint_left.mp hd hs hx
      simp [k, hxS]
    have hkc : ContinuousOn k (S ∪ T) :=
      (hf.congr hks).union_of_isClosed (hg.congr hkt) hS hT
    exact ⟨k, hkc, fun x hx => congrArg Complex.exp (hks hx),
      fun x hx => congrArg Complex.exp (hkt hx)⟩

#print axioms solution
