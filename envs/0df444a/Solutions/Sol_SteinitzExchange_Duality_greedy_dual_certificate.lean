-- Prove2me | solution 1 for SteinitzExchange.Duality.greedy_dual_certificate
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T19:23:06.876596+00:00
-- url     : https://prove2.me/submissions/68f52950-0069-4e68-9941-f68f7bef3919

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
namespace SteinitzGreedyReal
variable {V : Type*} [DecidableEq V]

/-- Remove a minimum-weight coordinate and optimize the nonnegative residual weights. -/
theorem greedy_on_ground (f : Finset V → ℝ)
    (hf : ∀ X Y, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y) (hf0 : f ∅ = 0) :
    ∀ S : Finset V, ∀ w : V → ℝ, (∀ v ∈ S, 0 ≤ w v) →
    ∃ x : V → ℝ,
      (∀ T : Finset V, T ⊆ S → (∑ v ∈ T, x v) ≤ f T) ∧
      (∑ v ∈ S, x v) = f S ∧
      (∀ y : V → ℝ, (∀ T : Finset V, T ⊆ S → (∑ v ∈ T, y v) ≤ f T) →
        (∑ v ∈ S, w v * y v) ≤ ∑ v ∈ S, w v * x v) := by
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih w hw
  by_cases hS : S = ∅
  · subst S
    refine ⟨fun _ => 0, ?_, by simp [hf0], ?_⟩
    · intro T hT
      have hT' : T = ∅ := Finset.Subset.antisymm hT (Finset.empty_subset _)
      simp [hT', hf0]
    · intro y hy; simp
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  obtain ⟨u, huS, hu⟩ := S.exists_min_image w hSne
  let w' : V → ℝ := fun v => w v - w u
  have hw' : ∀ v ∈ S.erase u, 0 ≤ w' v := by
    intro v hv
    exact sub_nonneg.mpr (hu v (Finset.mem_of_mem_erase hv))
  obtain ⟨z, hz, hzS, hzopt⟩ := ih (S.erase u) (Finset.erase_ssubset huS) w' hw'
  let δ : ℝ := f S - f (S.erase u)
  let x : V → ℝ := Function.update z u δ
  have hsum_mem (T : Finset V) (huT : u ∈ T) :
      (∑ v ∈ T, x v) = δ + ∑ v ∈ T.erase u, z v := by
    simpa only [x, Finset.sdiff_singleton_eq_erase] using
      Finset.sum_update_of_mem huT z δ
  have hsum_not_mem (T : Finset V) (huT : u ∉ T) :
      (∑ v ∈ T, x v) = ∑ v ∈ T, z v :=
    Finset.sum_update_of_notMem huT z δ
  have hxS : (∑ v ∈ S, x v) = f S := by
    rw [hsum_mem S huS, hzS]
    dsimp [δ]
    ring
  refine ⟨x, ?_, hxS, ?_⟩
  · intro T hTS
    by_cases huT : u ∈ T
    · have herase : T.erase u ⊆ S.erase u := by
        intro v hv
        obtain ⟨hvu, hvT⟩ := Finset.mem_erase.mp hv
        exact Finset.mem_erase.mpr ⟨hvu, hTS hvT⟩
      have hunion : S.erase u ∪ T = S := by
        ext v
        simp only [Finset.mem_union, Finset.mem_erase]
        constructor
        · rintro (⟨_, hv⟩ | hv)
          · exact hv
          · exact hTS hv
        · intro hv
          by_cases he : v = u
          · exact Or.inr (he.symm ▸ huT)
          · exact Or.inl ⟨he, hv⟩
      have hinter : S.erase u ∩ T = T.erase u := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨hvu, _⟩, hvT⟩
          exact ⟨hvu, hvT⟩
        · rintro ⟨hvu, hvT⟩
          exact ⟨⟨hvu, hTS hvT⟩, hvT⟩
      have hsub := hf (S.erase u) T
      rw [hunion, hinter] at hsub
      have hrec := hz (T.erase u) herase
      rw [hsum_mem T huT]
      dsimp [δ]
      linarith
    · have hTsub : T ⊆ S.erase u := by
        intro v hvT
        refine Finset.mem_erase.mpr ⟨?_, hTS hvT⟩
        intro he
        exact huT (he ▸ hvT)
      rw [hsum_not_mem T huT]
      exact hz T hTsub
  · intro y hy
    have hy' : ∀ T : Finset V, T ⊆ S.erase u → (∑ v ∈ T, y v) ≤ f T :=
      fun T hT => hy T (hT.trans (Finset.erase_subset _ _))
    have hopt := hzopt y hy'
    have hdecomp (a : V → ℝ) :
        (∑ v ∈ S, w v * a v) =
          (∑ v ∈ S.erase u, w' v * a v) + w u * (∑ v ∈ S, a v) := by
      have hid : (∑ v ∈ S, w v * a v) =
          (∑ v ∈ S, w' v * a v) + w u * (∑ v ∈ S, a v) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v hv
        dsimp [w']
        ring
      rw [hid]
      congr 1
      have he := Finset.sum_erase_add S (fun v => w' v * a v) huS
      simpa only [w', sub_self, zero_mul, add_zero] using he.symm
    have hxres : (∑ v ∈ S.erase u, w' v * x v) =
        ∑ v ∈ S.erase u, w' v * z v := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [show x v = z v from Function.update_of_ne (Finset.ne_of_mem_erase hv) _ _]
    rw [hdecomp y, hdecomp x, hxres, hxS]
    exact add_le_add hopt (mul_le_mul_of_nonneg_left (hy S (Finset.Subset.refl _)) (hw u huS))

theorem greedy_dual_certificate [Fintype V] (f : Finset V → ℝ)
    (hf : ∀ X Y, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y) (hf0 : f ∅ = 0)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ x : V → ℝ,
      (∀ X : Finset V, (∑ v ∈ X, x v) ≤ f X) ∧
      (∀ y : V → ℝ, (∀ X : Finset V, (∑ v ∈ X, y v) ≤ f X) →
        (∑ v, w v * y v) ≤ ∑ v, w v * x v) ∧
      (∀ lam : Finset V → ℝ, (∀ X, 0 ≤ lam X) →
        (∀ v, (∑ X : Finset V, lam X * (if v ∈ X then (1 : ℝ) else 0)) = w v) →
        ∀ y : V → ℝ, (∀ X : Finset V, (∑ v ∈ X, y v) ≤ f X) →
          (∑ v, w v * y v) ≤ ∑ X : Finset V, lam X * f X) := by
  classical
  obtain ⟨x, hx, _, hopt⟩ := greedy_on_ground f hf hf0 Finset.univ w (fun v _ => hw v)
  refine ⟨x, fun X => hx X (Finset.subset_univ X), ?_, ?_⟩
  · intro y hy
    exact hopt y (fun X _ => hy X)
  · intro lam hlam hcover y hy
    calc
      (∑ v, w v * y v) =
          ∑ v, (∑ X : Finset V, lam X * (if v ∈ X then (1 : ℝ) else 0)) * y v := by
        simp_rw [hcover]
      _ = ∑ X : Finset V, lam X * (∑ v ∈ X, y v) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro X hX
        rw [Finset.mul_sum]
        calc
          (∑ v, lam X * (if v ∈ X then (1 : ℝ) else 0) * y v) =
              ∑ v, if v ∈ X then lam X * y v else 0 := by
            apply Finset.sum_congr rfl
            intro v hv
            split_ifs <;> simp_all
          _ = ∑ v ∈ X, lam X * y v := by simp
      _ ≤ ∑ X : Finset V, lam X * f X :=
        Finset.sum_le_sum (fun X _ => mul_le_mul_of_nonneg_left (hy X) (hlam X))

#print axioms greedy_on_ground
#print axioms greedy_dual_certificate
end SteinitzGreedyReal

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (f : Finset V → ℝ)
    (hf : ∀ X Y : Finset V, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y)
    (hf0 : f ∅ = 0) :
    ∀ z : V → ℝ, (∀ v : V, 0 ≤ z v) →
      ∃ x : V → ℝ,
        (∀ X : Finset V, Finset.sum X (fun v => x v) ≤ f X) ∧
        (∀ y : V → ℝ, (∀ X : Finset V, Finset.sum X (fun v => y v) ≤ f X) →
          Finset.sum Finset.univ (fun v => z v * y v) ≤
            Finset.sum Finset.univ (fun v => z v * x v)) ∧
        (∀ lam : Finset V → ℝ, (∀ X : Finset V, 0 ≤ lam X) →
          (∀ v : V, Finset.sum Finset.univ (fun X => lam X * (if v ∈ X then (1 : ℝ) else 0)) = z v) →
          ∀ y : V → ℝ, (∀ X : Finset V, Finset.sum X (fun v => y v) ≤ f X) →
            Finset.sum Finset.univ (fun v => z v * y v) ≤
              Finset.sum Finset.univ (fun X => lam X * f X)) := by
  exact SteinitzGreedyReal.greedy_dual_certificate f hf hf0

#print axioms solution
