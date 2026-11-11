-- Prove2me | solution 1 for TopicalIrreducibility.Relations.irreducibility_relations
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T13:50:21.239061+00:00
-- url     : https://prove2.me/submissions/5d53449b-43b9-433f-abfe-e7cc6cfcfba7

import Definitions.Def_TopicalIrreducibility_Relations_Irreducibility
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
open scoped NNReal
open Filter

namespace TopicalIrreducibility.Relations

lemma ray_monotone {n : ℕ} {f : StdCone n → StdCone n} (hf : IsMTopical f)
    (J : Finset (Fin n)) (i : Fin n) :
    Monotone (fun t : ℝ≥0 => f (1 + t • indicatorVec J) i) := by
  intro a b hab
  apply hf.monotone _ i
  intro k
  change 1 + a * indicatorVec J k ≤ 1 + b * indicatorVec J k
  have hm : a * indicatorVec J k ≤ b * indicatorVec J k :=
    mul_le_mul_of_nonneg_right hab (show 0 ≤ indicatorVec J k from zero_le)
  exact add_le_add (le_refl 1) hm

lemma not_ray_unbounded_iff {n : ℕ} {f : StdCone n → StdCone n}
    (hf : IsMTopical f) (J : Finset (Fin n)) (i : Fin n) :
    ¬ RayUnbounded f J i ↔ ∃ B : ℝ≥0, ∀ t : ℝ≥0,
      f (1 + t • indicatorVec J) i ≤ B := by
  unfold RayUnbounded
  rw [(ray_monotone hf J i).tendsto_atTop_atTop_iff]
  constructor
  · intro h
    push Not at h
    obtain ⟨B, hB⟩ := h
    exact ⟨B, fun t => (hB t).le⟩
  · rintro ⟨B, hB⟩ h
    obtain ⟨t, ht⟩ := h (B + 1)
    have := ht.trans (hB t)
    exact (not_le_of_gt (lt_add_one B)) this

lemma ray_interior {n : ℕ} (J : Finset (Fin n)) (t : ℝ≥0) :
    IsInterior (1 + t • indicatorVec J) := by
  intro k
  change 0 < 1 + t * indicatorVec J k
  positivity

lemma half_power_ray {n : ℕ} (J : Finset (Fin n)) (t : ℝ≥0) (k : Fin n) :
    (1 + (t * (t + 2)) • indicatorVec J) k ^ (1 / (2 : ℝ)) =
      (1 + t • indicatorVec J) k := by
  by_cases hk : k ∈ J
  · simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul,
      indicatorVec, if_pos hk, mul_one]
    rw [show (1 : ℝ≥0) + t * (t + 2) = (1 + t) ^ 2 by ring,
      ← NNReal.sqrt_eq_rpow, NNReal.sqrt_sq]
  · simp [indicatorVec, hk]

lemma ray_insert_geomean {n : ℕ} (J : Finset (Fin n)) (a : Fin n)
    (ha : a ∉ J) (t : ℝ≥0) :
    (fun k => (1 + (t * (t + 2)) • indicatorVec {a}) k ^ (1 / (2 : ℝ)) *
      (1 + (t * (t + 2)) • indicatorVec J) k ^ (1 - 1 / (2 : ℝ))) =
      1 + t • indicatorVec (insert a J) := by
  funext k
  rw [show (1 - 1 / (2 : ℝ)) = 1 / 2 by norm_num,
    half_power_ray, half_power_ray]
  by_cases hka : k = a
  · subst k
    simp [indicatorVec, ha]
  · by_cases hk : k ∈ J <;> simp [indicatorVec, hka, hk]

lemma bounded_ray_of_bounded_singletons {n : ℕ} {f : StdCone n → StdCone n}
    (hc : IsMConvex f) (J : Finset (Fin n)) (i : Fin n)
    (h : ∀ j ∈ J, ∃ B : ℝ≥0, ∀ t : ℝ≥0,
      f (1 + t • indicatorVec {j}) i ≤ B) :
    ∃ B : ℝ≥0, ∀ t : ℝ≥0, f (1 + t • indicatorVec J) i ≤ B := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨f 1 i, ?_⟩
    intro t
    have hz : indicatorVec (∅ : Finset (Fin n)) = 0 := by
      funext k
      simp [indicatorVec]
    rw [hz, smul_zero, add_zero]
  | @insert a J ha ih =>
    obtain ⟨A, hA⟩ := h a (Finset.mem_insert_self a J)
    obtain ⟨B, hB⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨NNReal.sqrt A * NNReal.sqrt B, ?_⟩
    intro t
    have hc' := hc (1 + (t * (t + 2)) • indicatorVec {a})
      (1 + (t * (t + 2)) • indicatorVec J)
      (ray_interior _ _) (ray_interior _ _) (1 / 2) (by norm_num) (by norm_num) i
    rw [ray_insert_geomean J a ha t,
      show (1 - 1 / (2 : ℝ)) = 1 / 2 by norm_num,
      ← NNReal.sqrt_eq_rpow, ← NNReal.sqrt_eq_rpow] at hc'
    exact hc'.trans (mul_le_mul' (NNReal.sqrt_le_sqrt.mpr (hA _))
      (NNReal.sqrt_le_sqrt.mpr (hB _)))

lemma topical_zero {n : ℕ} {f : StdCone n → StdCone n} (hf : IsMTopical f) :
    f 0 = 0 := by
  funext i
  have h := congrFun (hf.homogeneous 2 (by norm_num) 0) i
  simp only [smul_zero, Pi.smul_apply, smul_eq_mul] at h
  change f 0 i = 0
  have h' : 0 + f 0 i = f 0 i + f 0 i := by simpa [two_mul] using h
  exact (add_right_cancel h').symm

lemma topical_smul {n : ℕ} {f : StdCone n → StdCone n} (hf : IsMTopical f)
    (t : ℝ≥0) (x : StdCone n) : f (t • x) = t • f x := by
  by_cases ht : t = 0
  · simp [ht, topical_zero hf]
  · exact hf.homogeneous t (pos_iff_ne_zero.mpr ht) x

lemma indicator_mono {n : ℕ} {I J : Finset (Fin n)} (h : I ⊆ J) :
    indicatorVec I ≤ indicatorVec J := by
  intro k
  by_cases hk : k ∈ I
  · simp [indicatorVec, hk, h hk]
  · simp [indicatorVec, hk]

lemma invariant_face_of_bounded {n : ℕ} {f : StdCone n → StdCone n}
    (hf : IsMTopical f) (J : Finset (Fin n))
    (hb : ∀ i, i ∉ J → ∃ B : ℝ≥0, ∀ t : ℝ≥0,
      f (1 + t • indicatorVec J) i ≤ B) :
    Set.MapsTo f (face J) (face J) := by
  have hz : ∀ i, i ∉ J → f (indicatorVec J) i = 0 := by
    intro i hi
    obtain ⟨B, hB⟩ := hb i hi
    have hc (c : ℝ≥0) : c * f (indicatorVec J) i ≤ B := by
      have h := (hf.monotone (show c • indicatorVec J ≤ 1 + c • indicatorVec J by
        intro k
        change c * indicatorVec J k ≤ 1 + c * indicatorVec J k
        exact le_add_of_nonneg_left (by positivity)) i).trans (hB c)
      simpa [topical_smul hf, Pi.smul_apply, smul_eq_mul] using h
    by_contra hne
    have h := hc ((B + 1) / f (indicatorVec J) i)
    rw [div_mul_cancel₀ _ hne] at h
    exact (not_le_of_gt (lt_add_one B)) h
  intro x hx i hi
  let M : ℝ≥0 := ∑ k : Fin n, x k
  have hbound : x ≤ M • indicatorVec J := by
    intro k
    by_cases hk : k ∈ J
    · simp only [Pi.smul_apply, smul_eq_mul, indicatorVec, if_pos hk, mul_one]
      exact Finset.single_le_sum (fun j _ => show (0 : ℝ≥0) ≤ x j from zero_le) (Finset.mem_univ k)
    · simp [hx k hk, indicatorVec, hk]
  have h := hf.monotone hbound i
  simpa [topical_smul hf, Pi.smul_apply, smul_eq_mul, hz i hi] using h

lemma graphically_indec {n : ℕ} {f : StdCone n → StdCone n}
    (hf : IsMTopical f) (hg : GraphicallyIrreducible f) : Indecomposable f := by
  rintro ⟨J, hJ, hb⟩
  obtain ⟨j, hj⟩ := hJ.1
  classical
  have hex : ∃ i, i ∉ J := by
    by_contra h
    apply hJ.2
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hclosed : ∀ a b, a ∉ J → graphArc f a b → b ∉ J := by
    intro a b ha hab hbj
    obtain ⟨B, hB⟩ := hb a ha
    apply (not_ray_unbounded_iff hf {b} a).mpr ?_ hab
    refine ⟨B, fun t => ?_⟩
    apply le_trans (hf.monotone ?_ a) (hB t)
    intro k
    change 1 + t * indicatorVec {b} k ≤ 1 + t * indicatorVec J k
    have hm : t * indicatorVec {b} k ≤ t * indicatorVec J k :=
      mul_le_mul_of_nonneg_left (indicator_mono
        (Finset.singleton_subset_iff.mpr hbj) k) (show 0 ≤ t from zero_le)
    exact add_le_add (le_refl 1) hm
  have hpath : ∀ {b}, Relation.ReflTransGen (graphArc f) i b → b ∉ J := by
    intro b h
    induction h with
    | refl => exact hi
    | @tail b c hab hbc ih => exact hclosed b c ih hbc
  exact hpath (hg i j) hj

lemma mconvex_graphically {n : ℕ} {f : StdCone n → StdCone n}
    (hf : IsMTopical f) (hc : IsMConvex f) (hind : Indecomposable f) :
    GraphicallyIrreducible f := by
  classical
  intro i j
  by_contra hij
  let J : Finset (Fin n) := Finset.univ.filter
    (fun k => ¬ Relation.ReflTransGen (graphArc f) i k)
  have hi : i ∉ J := by
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    exact Relation.ReflTransGen.refl
  have hj : j ∈ J := by simp [J, hij]
  have hJ : IsNontrivialProper J := by
    refine ⟨⟨j, hj⟩, ?_⟩
    intro he
    exact hi (he ▸ Finset.mem_univ i)
  apply hind
  refine ⟨J, hJ, ?_⟩
  intro k hk
  have hik : Relation.ReflTransGen (graphArc f) i k := by simpa [J] using hk
  apply bounded_ray_of_bounded_singletons hc J k
  intro l hl
  apply (not_ray_unbounded_iff hf {l} k).mp
  intro hkl
  have hil : ¬ Relation.ReflTransGen (graphArc f) i l := by simpa [J] using hl
  exact hil (hik.tail hkl)

lemma subadditive_facially {n : ℕ} {f : StdCone n → StdCone n}
    (hf : IsMTopical f) (hs : IsSubadditive f) (hind : Indecomposable f) :
    FaciallyIrreducible f := by
  intro J hJ hm
  apply hind
  refine ⟨J, hJ, ?_⟩
  intro i hi
  have he : indicatorVec J ∈ face J := by
    intro k hk
    simp [indicatorVec, hk]
  have hz := hm he i hi
  refine ⟨f 1 i, ?_⟩
  intro t
  have h := hs 1 (t • indicatorVec J) i
  simpa [topical_smul hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz] using h

end TopicalIrreducibility.Relations

open TopicalIrreducibility.Relations

theorem solution {n : ℕ} (f : StdCone n → StdCone n) (hf : IsMTopical f) :
    ((FaciallyIrreducible f ∨ GraphicallyIrreducible f) → Indecomposable f) ∧
    (IsMConvex f → Indecomposable f → GraphicallyIrreducible f) ∧
    (IsSubadditive f → Indecomposable f → FaciallyIrreducible f) := by
  refine ⟨?_, mconvex_graphically hf, subadditive_facially hf⟩
  rintro (hfac | hgraph)
  · rintro ⟨J, hJ, hb⟩
    exact hfac J hJ (invariant_face_of_bounded hf J hb)
  · exact graphically_indec hf hgraph

#print axioms solution
