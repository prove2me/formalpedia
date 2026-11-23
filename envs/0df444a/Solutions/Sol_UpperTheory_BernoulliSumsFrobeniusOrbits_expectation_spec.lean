-- Prove2me | solution 1 for UpperTheory.BernoulliSumsFrobeniusOrbits.expectation_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:28.885947+00:00
-- url     : https://prove2.me/submissions/cb58f917-5678-4c56-9a7c-480ca8d3aee9

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_expectationSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
section
variable {p : ℕ → ℝ}
private theorem ex_empty (f : Finset ℕ → ℝ) : exP p ∅ f = f ∅ := by simp [exP]
private theorem ex_insert {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (f : Finset ℕ → ℝ) :
    exP p (insert a S) f = (1 - p a) * exP p S f + p a * exP p S (fun T => f (insert a T)) := by
  unfold exP
  rw [Finset.sum_powerset_insert ha, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun T hT => ?_
    have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
    have h2 : a ∉ S \ T := fun h => ha (Finset.mem_sdiff.1 h).1
    rw [Finset.insert_sdiff_of_notMem _ haT, Finset.prod_insert h2]
    ring
  · refine Finset.sum_congr rfl fun T hT => ?_
    have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
    have e : insert a S \ insert a T = S \ T := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · tauto
      · rintro ⟨h1, h2⟩
        refine ⟨Or.inr h1, ?_⟩
        rintro (rfl | h)
        · exact ha h1
        · exact h2 h
    rw [Finset.prod_insert haT, e]
    ring
private theorem ex_congr {S : Finset ℕ} {f g : Finset ℕ → ℝ} (h : ∀ T ⊆ S, f T = g T) :
    exP p S f = exP p S g :=
  Finset.sum_congr rfl fun T hT => by rw [h T (Finset.mem_powerset.1 hT)]
private theorem ex_const (S : Finset ℕ) (c : ℝ) : exP p S (fun _ => c) = c := by
  induction S using Finset.induction_on with
  | empty => exact ex_empty _
  | insert a S ha ih => rw [ex_insert ha, ih]; ring
private theorem ex_add (S : Finset ℕ) (f g : Finset ℕ → ℝ) :
    exP p S (fun T => f T + g T) = exP p S f + exP p S g := by
  unfold exP
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun T _ => by ring
private theorem ex_mul_left (S : Finset ℕ) (c : ℝ) (f : Finset ℕ → ℝ) :
    exP p S (fun T => c * f T) = c * exP p S f := by
  unfold exP
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun T _ => by ring
private theorem ex_sum {ι : Type*} (S : Finset ℕ) (I : Finset ι) (f : ι → Finset ℕ → ℝ) :
    exP p S (fun T => ∑ i ∈ I, f i T) = ∑ i ∈ I, exP p S (f i) := by
  unfold exP
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun T _ => by rw [Finset.mul_sum]
private theorem ex_mono {S : Finset ℕ} (hp : ∀ a ∈ S, 0 ≤ p a ∧ p a ≤ 1) {f g : Finset ℕ → ℝ}
    (h : ∀ T ⊆ S, f T ≤ g T) : exP p S f ≤ exP p S g := by
  refine Finset.sum_le_sum fun T hT => ?_
  have hT' := Finset.mem_powerset.1 hT
  refine mul_le_mul_of_nonneg_left (h T hT') (mul_nonneg ?_ ?_)
  · exact Finset.prod_nonneg fun a ha => (hp a (hT' ha)).1
  · exact Finset.prod_nonneg fun a ha => sub_nonneg.2 (hp a (Finset.mem_sdiff.1 ha).1).2
private theorem ex_union {A B : Finset ℕ} (hAB : Disjoint A B) (f : Finset ℕ → ℝ) :
    exP p (A ∪ B) f = exP p A (fun T => exP p B (fun U => f (T ∪ U))) := by
  induction A using Finset.induction_on generalizing f with
  | empty => rw [ex_empty]; simp
  | insert a A ha ih =>
    rw [Finset.disjoint_insert_left] at hAB
    have : a ∉ A ∪ B := by simp [ha, hAB.1]
    rw [Finset.insert_union, ex_insert this, ex_insert ha, ih hAB.2, ih hAB.2]
    simp only [Finset.insert_union]
private theorem ex_split {A S : Finset ℕ} (hA : A ⊆ S) (f g : Finset ℕ → ℝ) :
    exP p S (fun T => f (T ∩ A) * g (T \ A)) = exP p A f * exP p (S \ A) g := by
  conv_lhs => rw [← Finset.union_sdiff_of_subset hA]
  rw [ex_union Finset.disjoint_sdiff, mul_comm, ← ex_mul_left]
  refine ex_congr fun T hT => ?_
  rw [mul_comm, ← ex_mul_left]
  refine ex_congr fun U hU => ?_
  have e1 : (T ∪ U) ∩ A = T := by
    ext x
    have := @hT x
    have := @hU x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  have e2 : (T ∪ U) \ A = U := by
    ext x
    have := @hT x
    have := @hU x
    simp only [Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  rw [e1, e2]
private theorem ex_restrict {A S : Finset ℕ} (hA : A ⊆ S) (f : Finset ℕ → ℝ) :
    exP p S (fun T => f (T ∩ A)) = exP p A f := by
  have := ex_split (p := p) hA f (fun _ => 1)
  simpa [ex_const] using this
private theorem ex_prod {ι : Type*} (J : Finset ι) (A : ι → Finset ℕ) (g : ι → Finset ℕ → ℝ)
    (hd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (A i) (A j)) (S : Finset ℕ)
    (hS : ∀ j ∈ J, A j ⊆ S) :
    exP p S (fun T => ∏ j ∈ J, g j (T ∩ A j)) = ∏ j ∈ J, exP p (A j) (g j) := by
  classical
  induction J using Finset.induction_on generalizing S with
  | empty => simp [ex_const]
  | insert a J ha ih =>
    have hda : ∀ j ∈ J, Disjoint (A a) (A j) := fun j hj =>
      hd a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (fun h => ha (h ▸ hj))
    rw [Finset.prod_insert ha,
      ← ih (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
        (S \ A a) (fun j hj => Finset.subset_sdiff.2
          ⟨hS j (Finset.mem_insert_of_mem hj), (hda j hj).symm⟩),
      ← ex_split (hS a (Finset.mem_insert_self _ _))]
    refine ex_congr fun T _ => ?_
    rw [Finset.prod_insert ha]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    congr 1
    ext x
    have : x ∈ A a → x ∉ A j := fun h => Finset.disjoint_left.1 (hda j hj) h
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto
end
end

set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
theorem _root_.solution :
    ∀ (p : ℕ → ℝ),
      (∀ (S : Finset ℕ) (c : ℝ), exP p S (fun _ => c) = c) ∧
      (∀ (S : Finset ℕ) (f g : Finset ℕ → ℝ), exP p S (fun T => f T + g T) = exP p S f + exP p S g) ∧
      (∀ (S : Finset ℕ) (I : Finset ℕ) (f : ℕ → Finset ℕ → ℝ), exP p S (fun T => ∑ i ∈ I, f i T) = ∑ i ∈ I, exP p S (f i)) ∧
      (∀ (S : Finset ℕ) (f g : Finset ℕ → ℝ), (∀ a ∈ S, 0 ≤ p a ∧ p a ≤ 1) → (∀ T ⊆ S, f T ≤ g T) → exP p S f ≤ exP p S g) ∧
      (∀ (a : ℕ) (S : Finset ℕ) (f : Finset ℕ → ℝ), a ∉ S →
        exP p (insert a S) f = (1 - p a) * exP p S f + p a * exP p S (fun T => f (insert a T))) ∧
      (∀ (A S : Finset ℕ) (f : Finset ℕ → ℝ), A ⊆ S → exP p S (fun T => f (T ∩ A)) = exP p A f) ∧
      (∀ (J : Finset ℕ) (A : ℕ → Finset ℕ) (g : ℕ → Finset ℕ → ℝ) (S : Finset ℕ),
        (∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (A i) (A j)) → (∀ j ∈ J, A j ⊆ S) →
        exP p S (fun T => ∏ j ∈ J, g j (T ∩ A j)) = ∏ j ∈ J, exP p (A j) (g j)) := by
  intro p
  exact ⟨ex_const, ex_add, fun S I f => ex_sum S I f, fun _ _ _ hp h => ex_mono hp h,
    fun _ _ f ha => ex_insert ha f, fun _ _ f hA => ex_restrict hA f,
    fun J A g S hd hS => ex_prod J A g hd S hS⟩
end UpperTheory.BernoulliSumsFrobeniusOrbits
