-- Prove2me | solution 1 for SaturatedNet.Uniqueness.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:11:59.862225+00:00
-- url     : https://prove2.me/submissions/5db4ca71-df04-401d-9467-c9ba496f1b0f

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
import Theorems.Thm_SaturatedNet_Uniqueness_proposition_1_i
import Theorems.Thm_SaturatedNet_Uniqueness_proposition_4
import Theorems.Thm_SaturatedNet_Uniqueness_proposition_5


open Matrix
namespace SaturatedNet.Uniqueness.MainProof

lemma extend_fixed_set {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w c : n → ℝ) (hw : 0 ≤ w)
    (F : Set n) (a : n → ℝ)
    (ha : ∀ i ∈ F, a i = sat (w i) (inflow P c a i))
    (hF : ∀ i ∈ F, ∀ j ∉ F, P j i = 0) :
    ∃ y ∈ equilibria P w c, ∀ i ∈ F, y i = a i := by
  classical
  let Q : Matrix n n ℝ := fun j i => if j ∈ F then 0 else P j i
  let d : n → ℝ := fun i => c i + ∑ j, if j ∈ F then a j * P j i else 0
  have hQ : ∀ i j, 0 ≤ Q i j := by
    intro i j
    dsimp [Q]
    split
    · exact le_rfl
    · exact hP i j
  obtain ⟨t, ht⟩ := (proposition_1_i Q hQ w hw d).2.1
  let y : n → ℝ := fun i => if i ∈ F then a i else t i
  have hy : ∀ i ∈ F, y i = a i := fun i hi => if_pos hi
  refine ⟨y, ?_, hy⟩
  intro i
  by_cases hi : i ∈ F
  · rw [hy i hi, ha i hi]
    congr 1
    unfold inflow
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ F
    · rw [hy j hj]
    · rw [hF i hi j hj]
      simp
  · have hflow : inflow P c y i = inflow Q d t i := by
      unfold inflow
      change (∑ j, y j * P j i) + c i =
        (∑ j, t j * Q j i) + (c i + ∑ j, if j ∈ F then a j * P j i else 0)
      rw [← add_assoc, add_right_comm, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ F <;> simp [y, Q, hj]
    rw [hflow]
    simpa only [y, if_neg hi] using ht.1 i

lemma inflow_split {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (c x : n → ℝ) (V : Finset n) (i : V) :
    inflow P c x i = inflow (block P V) (classInflow P c V x) (fun j : V => x j) i := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun j : n => j ∈ V) (f := fun j => x j * P j i)
  have hfilter : Finset.univ.filter (fun j : n => j ∈ V) = V := by ext j; simp
  rw [hfilter] at hsplit
  unfold inflow classInflow
  rw [← hsplit]
  simp only [block, Matrix.submatrix_apply]
  rw [← Finset.sum_subtype V (fun _ => Iff.rfl) (fun j => x j * P j i)]
  simp_rw [mul_comm (P _ _) (x _)]
  ring

lemma outside_inflow_eq {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (c : n → ℝ) (V : Finset n) (x y : n → ℝ)
    (hxy : ∀ j ∈ upstream P V, y j = x j) :
    classInflow P c V y = classInflow P c V x := by
  classical
  funext i
  unfold classInflow
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjV : j ∉ V := (Finset.mem_filter.mp hj).2
  by_cases hp : P j i = 0
  · simp [hp]
  · rw [hxy j ⟨hjV, i, i.property, Relation.ReflTransGen.single hp⟩]

lemma projection_subset {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (w c : n → ℝ) (V : Finset n) (x : n → ℝ) :
    classProj P w c V x ⊆ equilibria (block P V) (fun i : V => w i)
      (classInflow P c V x) := by
  rintro z ⟨y, hy, hup, heq⟩ i
  have hi := hy i
  rw [inflow_split P c y V i, outside_inflow_eq P c V x y hup] at hi
  have hyV : (fun j : V => y j) = z := funext heq
  rw [hyV, heq i] at hi
  exact hi

lemma class_reaches {n : Type*} (P : Matrix n n ℝ) {V : Finset n}
    (hV : IsClass P V) {i j : n} (hi : i ∈ V) (hj : j ∈ V) : Reaches P i j := by
  obtain ⟨a, _, h⟩ := hV
  exact ((h i).mp hi).2.trans ((h j).mp hj).1

lemma class_between {n : Type*} (P : Matrix n n ℝ) {V : Finset n}
    (hV : IsClass P V) {i j k : n} (hi : i ∈ V) (hk : k ∈ V)
    (hij : Reaches P i j) (hjk : Reaches P j k) : j ∈ V := by
  obtain ⟨a, _, h⟩ := hV
  apply (h j).mpr
  exact ⟨((h i).mp hi).1.trans hij, hjk.trans ((h k).mp hk).2⟩

lemma class_to_upstream_zero {n : Type*} (P : Matrix n n ℝ) {V : Finset n}
    (hV : IsClass P V) {i j : n} (hi : i ∈ V) (hj : j ∈ upstream P V) : P i j = 0 := by
  by_contra h
  obtain ⟨hjV, k, hk, hjk⟩ := hj
  exact hjV (class_between P hV hi hk (Relation.ReflTransGen.single h) hjk)

lemma projection_eq {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w c : n → ℝ) (hw : 0 ≤ w)
    (V : Finset n) (hV : IsClass P V) (x : n → ℝ) (hx : x ∈ equilibria P w c) :
    classProj P w c V x = equilibria (block P V) (fun i : V => w i)
      (classInflow P c V x) := by
  classical
  apply Set.Subset.antisymm (projection_subset P w c V x)
  intro z hz
  let F : Set n := (V : Set n) ∪ upstream P V
  let a : n → ℝ := fun i => if hi : i ∈ V then z ⟨i, hi⟩ else x i
  have haV : ∀ i : V, a i = z i := fun i => dif_pos i.property
  have haux : ∀ i ∈ upstream P V, a i = x i := fun i hi => dif_neg hi.1
  have ha : ∀ i ∈ F, a i = sat (w i) (inflow P c a i) := by
    intro i hi
    rcases hi with hi | hi
    · have hh := hz ⟨i, hi⟩
      rw [inflow_split P c a V ⟨i, hi⟩, outside_inflow_eq P c V x a haux]
      have hv : (fun j : V => a j) = z := funext haV
      rw [hv, haV ⟨i, hi⟩]
      exact hh
    · rw [haux i hi, hx i]
      congr 1
      unfold inflow
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ V
      · rw [class_to_upstream_zero P hV hj hi]
        simp
      · simp [a, hj]
  have hF : ∀ i ∈ F, ∀ j ∉ F, P j i = 0 := by
    intro i hi j hj
    by_contra hp
    apply hj
    right
    have hjV : j ∉ V := fun h => hj (Or.inl h)
    refine ⟨hjV, ?_⟩
    rcases hi with hi | hi
    · exact ⟨i, hi, Relation.ReflTransGen.single hp⟩
    · obtain ⟨_, k, hk, hik⟩ := hi
      exact ⟨k, hk, (Relation.ReflTransGen.single hp).trans hik⟩
  obtain ⟨y, hy, hya⟩ := extend_fixed_set P hP w c hw F a ha hF
  refine ⟨y, hy, ?_, ?_⟩
  · intro i hi
    exact (hya i (Or.inr hi)).trans (haux i hi)
  · intro i
    exact (hya i (Or.inl i.property)).trans (haV i)

end SaturatedNet.Uniqueness.MainProof


open Matrix
namespace SaturatedNet.Uniqueness.MainProof

lemma reaches_block {n : Type*} (P : Matrix n n ℝ) {V : Finset n}
    (hV : IsClass P V) {i j : n} (hij : Reaches P i j)
    (hi : i ∈ V) (hj : j ∈ V) : Reaches (block P V) ⟨i,hi⟩ ⟨j,hj⟩ := by
  revert hi hj
  induction hij with
  | refl => intro hi hj; exact Relation.ReflTransGen.refl
  | @tail j k hij hjk ih =>
    intro hi hk
    have hj := class_between P hV hi hk hij (Relation.ReflTransGen.single hjk)
    exact Relation.ReflTransGen.tail (ih hi hj) hjk

lemma eigenvector_pos_on_class {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (V : Finset n) (hV : IsClass P V)
    (v : V → ℝ) (hv : 0 ≤ v) (hne : v ≠ 0) (lam : ℝ)
    (he : block P V *ᵥ v = lam • v) : ∀ i, 0 < v i := by
  classical
  have zero_edge (i j : V) (hi : v i=0) (hij : block P V i j≠0) : v j=0 := by
    have hsum : ∑ k : V, block P V i k * v k = 0 := by
      have hh : (block P V *ᵥ v) i = 0 := by simpa [hi] using congrFun he i
      exact hh
    have hjzero : block P V i j * v j=0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun (k : V) _ => mul_nonneg (hP i k) (hv k))).mp hsum j (Finset.mem_univ j)
    exact (mul_eq_zero.mp hjzero).resolve_left hij
  have zero_reaches (a b : V) (h : Reaches (block P V) a b) (ha : v a=0) : v b=0 := by
    induction h with
    | refl => exact ha
    | @tail j k hjk hejk ih => exact zero_edge j k ih hejk
  intro i
  by_contra hn
  have hi : v i=0 := le_antisymm (le_of_not_gt hn) (hv i)
  apply hne
  funext j
  have hij := reaches_block P hV (class_reaches P hV i.property j.property) i.property j.property
  exact zero_reaches i j hij hi

lemma reaches_positive_power {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) {i j : n}
    (hij : Reaches P i j) : ∃ k : ℕ, 0 < (P ^ k) i j := by
  induction hij with
  | refl => exact ⟨0, by simp⟩
  | @tail j k hij hjk ih =>
    obtain ⟨l, hl⟩ := ih
    refine ⟨l+1, ?_⟩
    have he : 0 < P j k := lt_of_le_of_ne (hP j k) (Ne.symm hjk)
    rw [pow_succ, Matrix.mul_apply]
    apply lt_of_lt_of_le (mul_pos hl he)
    exact Finset.single_le_sum (fun z _ => mul_nonneg (Matrix.pow_apply_nonneg hP l i z)
      (hP z k)) (Finset.mem_univ j)

lemma class_irreducible_of_fixed_vector {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (V : Finset n) (hV : IsClass P V) (p : V → ℝ)
    (hp0 : 0 ≤ p) (hp : p ≠ 0) (hpP : block P V *ᵥ p = p) :
    IsIrreducible (block P V) := by
  have hpos : ∀ i, 0 < p i := eigenvector_pos_on_class P hP V hV p hp0 hp 1 (by simpa using hpP)
  intro i j
  have hsum : 0 < ∑ k : V, block P V i k * p k := by
    change 0 < (block P V *ᵥ p) i
    rw [hpP]
    exact hpos i
  have hex : ∃ k : V, 0 < block P V i k * p k := by
    by_contra hn
    push Not at hn
    exact (not_lt_of_ge (Finset.sum_nonpos (fun k _ => hn k))) hsum
  obtain ⟨k, hk⟩ := hex
  have hik : 0 < block P V i k := (mul_pos_iff_of_pos_right (hpos k)).mp hk
  have hkj := reaches_block P hV (class_reaches P hV k.property j.property) k.property j.property
  obtain ⟨l, hl⟩ := reaches_positive_power (block P V) (fun a b => hP a b) hkj
  refine ⟨l+1, by omega, ?_⟩
  rw [pow_succ', Matrix.mul_apply]
  apply lt_of_lt_of_le (mul_pos hik hl)
  exact Finset.single_le_sum (fun (z : V) _ => mul_nonneg (hP i z)
    (Matrix.pow_apply_nonneg (fun a b : V => hP a b) l z j)) (Finset.mem_univ k)

end SaturatedNet.Uniqueness.MainProof


open Matrix
namespace SaturatedNet.Uniqueness.MainProof

lemma subcritical_projection {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w c : n → ℝ) (hw : 0 ≤ w)
    (V : Finset n) (hV : IsClass P V) (x : n → ℝ) (hx : x ∈ equilibria P w c)
    (hρ : specRad (block P V) < 1) : classProj P w c V x = {fun i : V => x i} := by
  have hmem : (fun i : V => x i) ∈ classProj P w c V x :=
    ⟨x, hx, fun _ _ => rfl, fun _ => rfl⟩
  rw [projection_eq P hP w c hw V hV x hx] at hmem ⊢
  obtain ⟨v, hv, huniq⟩ := proposition_4 (block P V) (fun i j => hP i j)
    (fun i : V => w i) (fun i => hw i) (classInflow P c V x) hρ
  ext z
  constructor
  · intro hz
    exact Set.mem_singleton_iff.mpr ((huniq z hz).trans (huniq _ hmem).symm)
  · rintro rfl
    exact hmem

end SaturatedNet.Uniqueness.MainProof


open Matrix
open SaturatedNet.Uniqueness.MainProof

namespace SaturatedNet.Uniqueness

theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) (hρ : specRad P ≤ 1)
    (V : Finset n) (hV : IsClass P V) (x : n → ℝ) (hx : x ∈ equilibria P w c) :
    (specRad (block P V) < 1 → classProj P w c V x = {fun i : V => x i}) ∧
    (specRad (block P V) = 1 →
      ∀ p π : V → ℝ, 0 ≤ p → p ≠ 0 → block P V *ᵥ p = p →
        0 ≤ π → π ≠ 0 → π ᵥ* block P V = π →
        ((classProj P w c V x).Nontrivial ↔
          (p ⬝ᵥ classInflow P c V x = 0 ∧
            ∃ ν : V → ℝ, ν = ν ᵥ* block P V + classInflow P c V x ∧
              minRatio ν π hV.univ_nonempty +
                minRatio (fun i : V => w i - ν i) π hV.univ_nonempty > 0)) ∧
        ((classProj P w c V x).Nontrivial →
          ∀ ν : V → ℝ, ν = ν ᵥ* block P V + classInflow P c V x →
            classProj P w c V x =
              {z | ∃ α : ℝ, -minRatio ν π hV.univ_nonempty ≤ α ∧
                α ≤ minRatio (fun i : V => w i - ν i) π hV.univ_nonempty ∧
                z = ν + α • π})) := by
  clear hρ
  constructor
  · exact subcritical_projection P hP w c hw V hV x hx
  · intro hcrit p π hp0 hp hpP hπ0 hπ hπP
    let : Nonempty V := ⟨hV.univ_nonempty.choose⟩
    have hirr := class_irreducible_of_fixed_vector P hP V hV p hp0 hp hpP
    rw [projection_eq P hP w c hw V hV x hx]
    exact proposition_5 (block P V) (fun i j => hP i j) (fun i : V => w i)
      (fun i => hw i) (classInflow P c V x) hirr hcrit p π hp0 hp hpP hπ0 hπ hπP


end SaturatedNet.Uniqueness
