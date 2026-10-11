-- Prove2me | solution 1 for SchrijverSFM.Alg.schrijver_algorithm
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-10T22:01:31.266419+00:00
-- url     : https://prove2.me/submissions/17f95cf1-bdab-462e-81c6-4a6ed2d2c1e1

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

-- BEGIN COMPLETE MODULE GreedyBase
section

open scoped BigOperators
open NonmonotoneSubmod.Shared
namespace SchrijverSFM.Alg.Proof

variable {n : ℕ} {f : Finset (Fin n) → ℝ}

lemma marginal_antitone (hf : Submodular f) {A B : Finset (Fin n)}
    {v : Fin n} (hAB : A ⊆ B) (hv : v ∉ B) :
    f (insert v B) - f B ≤ f (insert v A) - f A := by
  have hu : insert v A ∪ B = insert v B := by ext x; simp; grind
  have hi : insert v A ∩ B = A := by ext x; simp; grind
  have h := hf (insert v A) B
  rw [hu, hi] at h
  linarith

lemma before_not_mem (σ : Equiv.Perm (Fin n)) (v : Fin n) : v ∉ before σ v := by
  simp [before]

lemma greedy_sum_le (hf : Submodular f) (hf0 : f ∅ = 0)
    (σ : Equiv.Perm (Fin n)) (U : Finset (Fin n)) : xsum (greedy f σ) U ≤ f U := by
  induction U using Finset.induction_on_max_value σ with
  | empty => simp [xsum, hf0]
  | insert a U ha hmax ih =>
    have hU : U ⊆ before σ a := by
      intro v hv
      simp only [before, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_ne (hmax v hv) (fun h => ha (σ.injective h ▸ hv))
    have h := marginal_antitone hf hU (before_not_mem σ a)
    rw [xsum, Finset.sum_insert ha]
    change greedy f σ a + xsum (greedy f σ) U ≤ _
    unfold greedy at h ih ⊢
    linarith

lemma greedy_sum_ideal (hf0 : f ∅ = 0) (σ : Equiv.Perm (Fin n))
    (U : Finset (Fin n)) (hU : IsLowerIdeal σ U) : xsum (greedy f σ) U = f U := by
  induction U using Finset.induction_on_max_value σ with
  | empty => simp [xsum, hf0]
  | insert a U ha hmax ih =>
    have hb : before σ a = U := by
      ext v
      simp only [before, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hv
        have hm := hU a (Finset.mem_insert_self a U) v hv
        rcases Finset.mem_insert.mp hm with he | he
        · subst v; exact (lt_irrefl _ hv).elim
        · exact he
      · intro hv
        exact lt_of_le_of_ne (hmax v hv) (fun h => ha (σ.injective h ▸ hv))
    have hU' : IsLowerIdeal σ U := by
      intro u hu v hv
      have hm := hU u (Finset.mem_insert_of_mem hu) v hv
      rcases Finset.mem_insert.mp hm with he | he
      · subst v; exact (not_lt_of_ge (hmax u hu) hv).elim
      · exact he
    rw [xsum, Finset.sum_insert ha]
    change greedy f σ a + xsum (greedy f σ) U = _
    rw [ih hU']
    simp [greedy, hb]

lemma greedy_mem_baseB (hf : Submodular f) (hf0 : f ∅ = 0)
    (σ : Equiv.Perm (Fin n)) : greedy f σ ∈ baseB f := by
  constructor
  · exact greedy_sum_le hf hf0 σ
  · exact greedy_sum_ideal hf0 σ _ (by intro u hu v hv; exact Finset.mem_univ v)

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE GreedyBase

-- BEGIN COMPLETE MODULE TerminalMinimizer
section

open scoped BigOperators
open NonmonotoneSubmod.Shared
namespace SchrijverSFM.Alg.Proof

variable {n : ℕ} {f : Finset (Fin n) → ℝ}

lemma xsum_point (S : State n) (U : Finset (Fin n)) :
    xsum (point f S) U = (S.map (fun p => p.2 * xsum (greedy f p.1) U)).sum := by
  induction S with
  | nil => simp [xsum, point]
  | cons p S ih =>
    simp only [point, List.map_cons, List.sum_cons, xsum] at ih ⊢
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih]

lemma point_sum_le (hf : Submodular f) (hf0 : f ∅ = 0)
    (S : State n) (hS : ∀ p ∈ S, 0 ≤ p.2) (U : Finset (Fin n)) :
    xsum (point f S) U ≤ (S.map Prod.snd).sum * f U := by
  rw [xsum_point]
  induction S with
  | nil => simp
  | cons p S ih =>
    simp only [List.map_cons, List.sum_cons, add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (greedy_sum_le hf hf0 p.1 U)
      (hS p (by simp))) (ih (fun q hq => hS q (by simp [hq])))

lemma point_sum_ideal (hf0 : f ∅ = 0) (S : State n) (U : Finset (Fin n))
    (hU : ∀ p ∈ S, IsLowerIdeal p.1 U) :
    xsum (point f S) U = (S.map Prod.snd).sum * f U := by
  rw [xsum_point]
  induction S with
  | nil => simp
  | cons p S ih =>
    simp only [List.map_cons, List.sum_cons, add_mul]
    rw [greedy_sum_ideal hf0 p.1 U (hU p (by simp)),
      ih (fun q hq => hU q (by simp [hq]))]

lemma caseOneSet_lower (S : State n) (p : Equiv.Perm (Fin n) × ℝ) (hp : p ∈ S) :
    IsLowerIdeal p.1 (caseOneSet f S) := by
  classical
  intro u hu v hv
  obtain ⟨w, hw, huw⟩ := (Finset.mem_filter.mp hu).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, w, hw, ?_⟩
  exact (Relation.ReflTransGen.single ⟨p, hp, hv⟩).trans huw

lemma caseOne_minimizes (hf : Submodular f) (hf0 : f ∅ = 0)
    (S : State n) (hS : Valid S) (hcase : caseOne f S)
    (W : Finset (Fin n)) : f (caseOneSet f S) ≤ f W := by
  have hid := point_sum_ideal hf0 S (caseOneSet f S) (caseOneSet_lower S)
  rw [hS.2.2, one_mul] at hid
  have hupper := point_sum_le hf hf0 S (fun p hp => (hS.2.1 p hp).le) W
  rw [hS.2.2, one_mul] at hupper
  apply le_trans _ hupper
  rw [← hid]
  classical
  have hneg : ∀ v, point f S v < 0 → v ∈ caseOneSet f S := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, v,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, Relation.ReflTransGen.refl⟩
  have hnonpos : ∀ v ∈ caseOneSet f S, point f S v ≤ 0 := by
    intro v hv
    by_contra hh
    have hpos : v ∈ posSet f S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, lt_of_not_ge hh⟩
    obtain ⟨w, hw, hvw⟩ := (Finset.mem_filter.mp hv).2
    exact hcase ⟨w, hw, v, hpos, hvw⟩
  change (∑ v ∈ caseOneSet f S, point f S v) ≤ ∑ v ∈ W, point f S v
  have he (T : Finset (Fin n)) :
      (∑ v ∈ T, point f S v) = ∑ v : Fin n, if v ∈ T then point f S v else 0 := by
    simp
  rw [he, he]
  apply Finset.sum_le_sum
  intro v hv
  split_ifs with hc hw hw
  · rfl
  · exact hnonpos v hc
  · exact le_of_not_gt (fun hh => hc (hneg v hh))
  · rfl

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE TerminalMinimizer

-- BEGIN COMPLETE MODULE StateConvex
section

open scoped BigOperators
namespace SchrijverSFM.Alg.Proof

variable {n : ℕ} {f : Finset (Fin n) → ℝ}

lemma state_sum_fin (S : State n) (g : Equiv.Perm (Fin n) × ℝ → ℝ) :
    (∑ i : Fin S.length, g S[i]) = (S.map g).sum := by
  change (∑ i : Fin S.length, g S[i.val]) = _
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map S g]

lemma point_mem_hull (S : State n) (A : Set (Equiv.Perm (Fin n)))
    (hA : A.Nonempty) (hpos : ∀ p ∈ S, 0 ≤ p.2)
    (hsum : (S.map Prod.snd).sum = 1)
    (horders : ∀ p ∈ S, p.2 ≠ 0 → p.1 ∈ A) :
    point f S ∈ convexHull ℝ (greedy f '' A) := by
  classical
  obtain ⟨a, ha⟩ := hA
  let z (i : Fin S.length) := if S[i].2 = 0 then greedy f a else greedy f S[i].1
  apply mem_convexHull_of_exists_fintype (fun i : Fin S.length => S[i].2) z
  · intro i; exact hpos S[i] (List.getElem_mem _)
  · rwa [state_sum_fin]
  · intro i
    simp only [z]
    split_ifs with hi
    · exact Set.mem_image_of_mem _ ha
    · exact Set.mem_image_of_mem _ (horders S[i] (List.getElem_mem _) hi)
  · ext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, point]
    rw [← state_sum_fin]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [z]
    split_ifs with hz
    · simp [hz]
    · rfl

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE StateConvex

-- BEGIN COMPLETE MODULE StateAlgebra
section

namespace SchrijverSFM.Alg.Proof

variable {n : ℕ} {f : Finset (Fin n) → ℝ}

noncomputable def scaleState (a : ℝ) (S : State n) : State n := S.map (fun p => (p.1, a * p.2))

lemma scaleState_weight (a : ℝ) (S : State n) :
    ((scaleState a S).map Prod.snd).sum = a * (S.map Prod.snd).sum := by
  induction S with
  | nil => simp [scaleState]
  | cons p S ih => simp [scaleState, List.map_map, Function.comp_def, mul_add] at ih ⊢; exact ih

lemma point_scale (a : ℝ) (S : State n) : point f (scaleState a S) = a • point f S := by
  ext v
  induction S with
  | nil => simp [scaleState, point]
  | cons p S ih =>
    simp only [scaleState, List.map_cons, point, List.sum_cons, Pi.smul_apply, smul_eq_mul] at ih ⊢
    rw [ih]; ring

lemma point_append (S T : State n) : point f (S ++ T) = point f S + point f T := by
  ext v; simp [point]

lemma erase_sum (S : State n) (i : ℕ) (p : Equiv.Perm (Fin n) × ℝ)
    (hp : S[i]? = some p) (g : Equiv.Perm (Fin n) × ℝ → ℝ) :
    (S.map g).sum = g p + ((S.eraseIdx i).map g).sum := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hp
  have hperm := List.getElem_cons_eraseIdx_perm hi
  rw [he] at hperm
  exact ((hperm.map g).sum_eq).symm

lemma point_erase (S : State n) (i : ℕ) (σ : Equiv.Perm (Fin n)) (lam : ℝ)
    (hp : S[i]? = some (σ, lam)) :
    point f S = lam • greedy f σ + point f (S.eraseIdx i) := by
  ext v
  exact erase_sum S i (σ, lam) hp (fun p => p.2 * greedy f p.1 v)

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE StateAlgebra

-- BEGIN COMPLETE MODULE MovedOrder
section

namespace SchrijverSFM.Alg.Proof

variable {n : ℕ}

def movePosition (a b v : Fin n) : Fin n :=
  if v = b then a else if h : a ≤ v ∧ v < b then ⟨v.val + 1, by omega⟩ else v

lemma movePosition_injective (a b : Fin n) (hab : a ≤ b) :
    Function.Injective (movePosition a b) := by
  intro v w he
  have he' := congrArg Fin.val he
  simp only [movePosition] at he'
  split_ifs at he' <;> simp_all only [Fin.le_def, Fin.lt_def, Fin.ext_iff] <;> omega

noncomputable def movePerm (a b : Fin n) (hab : a ≤ b) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (movePosition a b)
    ((Finite.injective_iff_bijective).mp (movePosition_injective a b hab))

lemma movePosition_lt (a b v w : Fin n) (hab : a ≤ b) :
    movePosition a b v < movePosition a b w ↔
      (v = b ∧ a ≤ w ∧ w < b) ∨ (v < w ∧ ¬ (w = b ∧ a ≤ v ∧ v < b)) := by
  simp only [Fin.lt_def, Fin.le_def, Fin.ext_iff, movePosition]
  split_ifs <;> (try dsimp only) <;> omega

lemma exists_moved (σ : Equiv.Perm (Fin n)) (s u : Fin n) (hsu : σ s ≤ σ u) :
    ∃ τ : Equiv.Perm (Fin n), IsMoved σ s u τ := by
  refine ⟨σ.trans (movePerm (σ s) (σ u) hsu), ?_⟩
  intro v w
  change movePosition (σ s) (σ u) (σ v) < movePosition (σ s) (σ u) (σ w) ↔ _
  rw [movePosition_lt _ _ _ _ hsu]
  simp only [Equiv.apply_eq_iff_eq]

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE MovedOrder

-- BEGIN COMPLETE MODULE MovedGreedy
section

open scoped BigOperators
open NonmonotoneSubmod.Shared
namespace SchrijverSFM.Alg.Proof

variable {n : ℕ} {f : Finset (Fin n) → ℝ}

lemma moved_before_self {σ τ : Equiv.Perm (Fin n)} {s u : Fin n}
    (hsu : σ s ≤ σ u) (hm : IsMoved σ s u τ) : before τ u = before σ s := by
  ext v
  simp only [before, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hm v u]
  constructor
  · rintro (⟨rfl, h, h'⟩ | ⟨h, h'⟩)
    · exact (lt_irrefl _ h').elim
    · by_contra hv
      exact h' ⟨rfl, le_of_not_gt hv, h⟩
  · intro hv
    exact Or.inr ⟨hv.trans_le hsu, by simp only [true_and]; omega⟩

lemma moved_before_other {σ τ : Equiv.Perm (Fin n)} {s u v : Fin n}
    (hm : IsMoved σ s u τ) (hvu : v ≠ u) :
    before τ v = if σ s ≤ σ v ∧ σ v < σ u then insert u (before σ v)
      else before σ v := by
  ext w
  simp only [before, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hm w v]
  split_ifs with hv
  · simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    simp [hvu, hv]
  · simp [hvu, hv]

lemma moved_greedy_self_nonneg (hf : Submodular f)
    {σ τ : Equiv.Perm (Fin n)} {s u : Fin n}
    (hsu : σ s ≤ σ u) (hm : IsMoved σ s u τ) :
    0 ≤ greedy f τ u - greedy f σ u := by
  have hsub : before σ s ⊆ before σ u := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ((Finset.mem_filter.mp hv).2).trans_le hsu⟩
  have h := marginal_antitone hf hsub (before_not_mem σ u)
  simp only [greedy, moved_before_self hsu hm]
  linarith

lemma moved_greedy_other_nonpos (hf : Submodular f)
    {σ τ : Equiv.Perm (Fin n)} {s u v : Fin n}
    (hm : IsMoved σ s u τ) (hvu : v ≠ u) :
    greedy f τ v - greedy f σ v ≤ 0 := by
  rw [greedy, moved_before_other hm hvu]
  split_ifs with hv
  · have hn : v ∉ insert u (before σ v) := by simp [hvu, before_not_mem]
    have h := marginal_antitone hf (Finset.subset_insert u (before σ v)) hn
    simpa only [greedy] using sub_nonpos.mpr h
  · simp [greedy]

lemma moved_greedy_outside {σ τ : Equiv.Perm (Fin n)} {s u v : Fin n}
    (hm : IsMoved σ s u τ) (hvu : v ≠ u)
    (hv : ¬ (σ s ≤ σ v ∧ σ v < σ u)) : greedy f τ v = greedy f σ v := by
  simp only [greedy, moved_before_other hm hvu, if_neg hv]

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE MovedGreedy

-- BEGIN COMPLETE MODULE TriangularIdentity
section

open scoped BigOperators
namespace SchrijverSFM.Alg.Proof

variable {n : ℕ}

lemma sum_smul_chi (r : Fin n → ℝ) : (∑ v, r v • chi v) = r := by
  ext w
  simp [chi, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma sum_smul_direction (r : Fin n → ℝ) (s : Fin n) (hr : ∑ v, r v = 0) :
    (∑ v, r v • (chi v - chi s)) = r := by
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, sum_smul_chi, ← Finset.sum_smul, hr, zero_smul, sub_zero]

lemma triangular_identity (σ : Equiv.Perm (Fin n)) (s t u : Fin n)
    (hu : u ∈ interval σ s t) (r : Fin n → ℝ) (hr : ∑ v, r v = 0)
    (hz : ∀ v, v ≠ u → ¬ (σ s ≤ σ v ∧ σ v < σ u) → r v = 0) :
    r u • (chi u - chi s) = r +
      ∑ v ∈ (interval σ s t).filter (fun v => σ v < σ u),
        (-r v) • (chi v - chi s) := by
  classical
  let J := (interval σ s t).filter (fun v => σ v < σ u)
  have hun : u ∉ J := by simp [J]
  have hsum : (∑ v ∈ insert u J, r v • (chi v - chi s)) = r := by
    rw [Finset.sum_subset (Finset.subset_univ _) ?_]
    · exact sum_smul_direction r s hr
    · intro v hv hvnot
      have hvu : v ≠ u := by intro he; subst v; exact hvnot (Finset.mem_insert_self _ _)
      by_cases hvs : v = s
      · subst v; simp
      · have hvo : ¬ (σ s ≤ σ v ∧ σ v < σ u) := by
          intro hh
          apply hvnot
          apply Finset.mem_insert_of_mem
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, hh.2⟩
          · exact lt_of_le_of_ne hh.1 (fun he => hvs (σ.injective he.symm))
          · exact hh.2.le.trans (Finset.mem_filter.mp hu).2.2
        rw [hz v hvu hvo, zero_smul]
  rw [Finset.sum_insert hun] at hsum
  simp_rw [neg_smul, Finset.sum_neg_distrib]
  change r u • (chi u - chi s) = r - ∑ v ∈ J, r v • (chi v - chi s)
  exact eq_sub_of_add_eq hsum

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE TriangularIdentity

-- BEGIN COMPLETE MODULE TriangularCone
section

open scoped BigOperators
namespace SchrijverSFM.Alg.Proof

variable {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma triangular_cone (C : PointedCone ℝ E) (rank : Fin n → ℕ)
    (J : Finset (Fin n)) (row dir : Fin n → E) (d : Fin n → ℝ)
    (a : Fin n → Fin n → ℝ)
    (hrow : ∀ u ∈ J, row u ∈ C) (hd : ∀ u ∈ J, 0 < d u)
    (ha : ∀ u ∈ J, ∀ v ∈ J, rank v < rank u → 0 ≤ a u v)
    (hid : ∀ u ∈ J, d u • dir u = row u +
      ∑ v ∈ J.filter (fun v => rank v < rank u), a u v • dir v) :
    ∀ u ∈ J, dir u ∈ C := by
  have h : ∀ k, ∀ u ∈ J, rank u = k → dir u ∈ C := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro u hu hku
      apply (PointedCone.smul_mem_iff (C := C) (hd u hu)).mp
      rw [hid u hu]
      apply C.add_mem (hrow u hu)
      apply C.sum_mem
      intro v hv
      obtain ⟨hvJ, hvlt⟩ := Finset.mem_filter.mp hv
      exact PointedCone.smul_mem C (ha u hu v hvJ hvlt)
        (ih (rank v) (by omega) v hvJ rfl)
  exact fun u hu => h (rank u) u hu rfl

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE TriangularCone

-- BEGIN COMPLETE MODULE ConeRay
section

open scoped BigOperators
namespace SchrijverSFM.Alg.Proof

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma cone_difference_ray (A : Set E) (b d : E) (hd : d ≠ 0)
    (hcone : d ∈ PointedCone.hull ℝ ((fun y => y - b) '' A)) :
    ∃ δ : ℝ, 0 < δ ∧ b + δ • d ∈ convexHull ℝ A := by
  classical
  obtain ⟨c, hc, hc0, hcd⟩ := PointedCone.mem_hull_set.mp hcone
  have hsup : c.support.Nonempty := by
    by_contra hh
    have he : c.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    have : c = 0 := Finsupp.support_eq_empty.mp he
    subst c
    simp at hcd
    exact hd hcd.symm
  have hpos : 0 < ∑ r ∈ c.support, c r := by
    apply Finset.sum_pos
    · intro r hr
      exact (hc0 r).lt_of_ne (Finsupp.mem_support_iff.mp hr).symm
    · exact hsup
  have hy : ∀ r : c.support, ∃ y ∈ A, y - b = (r : E) := by
    intro r
    exact hc r.property
  choose y hyA hyb using hy
  let T : ℝ := ∑ r ∈ c.support, c r
  have hT : 0 < T := hpos
  have hw : (∑ r : c.support, c r / T) = 1 := by
    rw [← Finset.sum_div]
    simp only [Finset.univ_eq_attach, Finset.sum_attach]
    exact div_self (ne_of_gt hT)
  have hsum : (∑ r : c.support, c r • (r : E)) = d := by
    change (∑ r ∈ c.support.attach, (fun r : E => c r • r) r.val) = d
    rw [Finset.sum_attach (f := fun r : E => c r • r)]
    exact hcd
  have hy' (r : c.support) : y r = (r : E) + b := eq_add_of_sub_eq (hyb r)
  refine ⟨T⁻¹, inv_pos.mpr hT, mem_convexHull_of_exists_fintype
    (fun r : c.support => c r / T) y
    (fun r => div_nonneg (hc0 r) hT.le) hw hyA ?_⟩
  have hs : (∑ r : c.support, c r) = T := by
    simp only [Finset.univ_eq_attach, Finset.sum_attach, T]
  simp_rw [hy', smul_add, div_eq_inv_mul, mul_smul]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, hsum,
    ← Finset.smul_sum, ← Finset.sum_smul, hs, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hT), one_smul, add_comm]

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE ConeRay

-- BEGIN COMPLETE MODULE SubroutineHull
section

open scoped BigOperators
open NonmonotoneSubmod.Shared
namespace SchrijverSFM.Alg.Proof

variable {n : ℕ} {f : Finset (Fin n) → ℝ}

lemma subroutine_hull (hf : Submodular f) (hf0 : f ∅ = 0)
    (σ : Equiv.Perm (Fin n)) (s t : Fin n) (hst : σ s < σ t) :
    ∃ δ : ℝ, 0 ≤ δ ∧ greedy f σ + δ • (chi t - chi s) ∈
      convexHull ℝ {v | ∃ τ : Equiv.Perm (Fin n),
        (∃ u ∈ interval σ s t, IsMoved σ s u τ) ∧ greedy f τ = v} := by
  classical
  let J := interval σ s t
  have hm : ∀ u ∈ J, ∃ τ : Equiv.Perm (Fin n), IsMoved σ s u τ := by
    intro u hu
    exact exists_moved σ s u (Finset.mem_filter.mp hu).2.1.le
  choose τ hτ using hm
  let row (u : Fin n) : Fin n → ℝ :=
    if hu : u ∈ J then greedy f (τ u hu) - greedy f σ else 0
  let A : Set (Fin n → ℝ) := {v | ∃ π : Equiv.Perm (Fin n),
    (∃ u ∈ J, IsMoved σ s u π) ∧ greedy f π = v}
  have hmem (u : Fin n) (hu : u ∈ J) : greedy f (τ u hu) ∈ A :=
    ⟨τ u hu, ⟨u, hu, hτ u hu⟩, rfl⟩
  have hdiag (u : Fin n) (hu : u ∈ J) : 0 ≤ row u u := by
    simpa only [row, dif_pos hu, Pi.sub_apply] using
      moved_greedy_self_nonneg hf (Finset.mem_filter.mp hu).2.1.le (hτ u hu)
  have hoff (u : Fin n) (hu : u ∈ J) (v : Fin n) (hvu : v ≠ u) : row u v ≤ 0 := by
    simpa only [row, dif_pos hu, Pi.sub_apply] using
      moved_greedy_other_nonpos hf (hτ u hu) hvu
  have hsum (u : Fin n) (hu : u ∈ J) : ∑ v, row u v = 0 := by
    simp only [row, dif_pos hu, Pi.sub_apply, Finset.sum_sub_distrib]
    have h1 := (greedy_mem_baseB hf hf0 (τ u hu)).2
    have h2 := (greedy_mem_baseB hf hf0 σ).2
    change (∑ v, greedy f (τ u hu) v) = _ at h1
    change (∑ v, greedy f σ v) = _ at h2
    rw [h1, h2, sub_self]
  by_cases hzero : ∃ u ∈ J, row u u = 0
  · obtain ⟨u, hu, hz⟩ := hzero
    have hrzero : row u = 0 := by
      have hn (v : Fin n) : row u v ≤ 0 := by
        by_cases hv : v = u
        · simp [hv, hz]
        · exact hoff u hu v hv
      have hall := (Finset.sum_eq_zero_iff_of_nonpos (fun v _ => hn v)).mp (hsum u hu)
      ext v
      exact hall v (Finset.mem_univ _)
    have he : greedy f (τ u hu) = greedy f σ := by
      have : greedy f (τ u hu) - greedy f σ = 0 := by simpa [row, hu] using hrzero
      exact sub_eq_zero.mp this
    refine ⟨0, le_rfl, ?_⟩
    simp only [zero_smul, add_zero]
    exact subset_convexHull ℝ A (he ▸ hmem u hu)
  · have hd (u : Fin n) (hu : u ∈ J) : 0 < row u u :=
      (hdiag u hu).lt_of_ne (fun he => hzero ⟨u, hu, he.symm⟩)
    let C := PointedCone.hull ℝ ((fun y => y - greedy f σ) '' A)
    have hrow (u : Fin n) (hu : u ∈ J) : row u ∈ C := by
      apply PointedCone.subset_hull
      exact ⟨greedy f (τ u hu), hmem u hu, by simp [row, hu]⟩
    have hid (u : Fin n) (hu : u ∈ J) :
        row u u • (chi u - chi s) = row u +
          ∑ v ∈ J.filter (fun v => (σ v).val < (σ u).val),
            (-row u v) • (chi v - chi s) := by
      apply triangular_identity σ s t u hu (row u) (hsum u hu)
      intro v hvu hv
      simp only [row, dif_pos hu, Pi.sub_apply]
      exact sub_eq_zero.mpr (moved_greedy_outside (hτ u hu) hvu hv)
    have hall := triangular_cone C (fun u => (σ u).val) J row
      (fun u => chi u - chi s) (fun u => row u u) (fun u v => -row u v)
      hrow hd (fun u hu v _ hv => neg_nonneg.mpr
        (hoff u hu v (fun he => by subst v; omega))) hid
    have ht : t ∈ J := by simp [J, interval, hst]
    have hne : chi t - chi s ≠ (0 : Fin n → ℝ) := by
      intro he
      have hh := congrFun he t
      have hts : t ≠ s := fun he => by subst t; exact (lt_irrefl _ hst)
      simp [chi, hts] at hh
    obtain ⟨δ, hδ, hp⟩ := cone_difference_ray A (greedy f σ) (chi t - chi s) hne (hall t ht)
    exact ⟨δ, hδ.le, hp⟩

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE SubroutineHull

-- BEGIN COMPLETE MODULE HyperplaneCard
section

open scoped BigOperators
namespace SchrijverSFM.Alg.Proof

variable {n : ℕ}

lemma affine_card_of_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (hn : 0 < n) (z : ι → Fin n → ℝ) (c : ℝ)
    (hz : ∀ i, ∑ v, z i v = c) (ha : AffineIndependent ℝ z) : Fintype.card ι ≤ n := by
  classical
  let K : Submodule ℝ (Fin n → ℝ) :=
    { carrier := {x | ∑ v, x v = 0}
      zero_mem' := by simp
      add_mem' := by intro x y hx hy; simpa [Finset.sum_add_distrib] using congrArg₂ (· + ·) hx hy
      smul_mem' := by intro a x hx; simpa [Finset.mul_sum] using congrArg (a * ·) hx }
  let i₀ : ι := Classical.choice inferInstance
  have hle : vectorSpan ℝ (Set.range z) ≤ K := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_range_self i₀)]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, ⟨i, rfl⟩, rfl⟩
    change ∑ v, (z i v - z i₀ v) = 0
    rw [Finset.sum_sub_distrib, hz, hz, sub_self]
  have hK : K ≠ ⊤ := by
    intro he
    let v : Fin n := ⟨0, hn⟩
    have hm : (fun w : Fin n => if w = v then (1 : ℝ) else 0) ∈ K := by rw [he]; trivial
    change (∑ w : Fin n, if w = v then (1 : ℝ) else 0) = 0 at hm
    simp at hm
  have hdim := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hK)
  have hmon := Submodule.finrank_mono hle
  have hc := ha.finrank_vectorSpan_add_one
  have htop : Module.finrank ℝ (⊤ : Submodule ℝ (Fin n → ℝ)) = n := by simp
  rw [htop] at hdim
  omega

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE HyperplaneCard

-- BEGIN COMPLETE MODULE StateFromHull
section

open scoped BigOperators
namespace SchrijverSFM.Alg.Proof

variable {n : ℕ} {f : Finset (Fin n) → ℝ}

lemma state_of_convexHull (hf0 : f ∅ = 0) (hn : 0 < n)
    (A : Set (Equiv.Perm (Fin n))) (x : Fin n → ℝ)
    (hx : x ∈ convexHull ℝ (greedy f '' A)) :
    ∃ S : State n, Valid S ∧ S.length ≤ n ∧ (S.map Prod.fst).Nodup ∧
      (∀ p ∈ S, p.1 ∈ A) ∧ point f S = x := by
  classical
  obtain ⟨ι, hι, z, w, hz, ha, hw, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  let := hι
  have hnι : Nonempty ι := by
    by_contra hh
    let : IsEmpty ι := not_nonempty_iff.mp hh
    simp at hw1
  let := hnι
  have hchoose : ∀ i, ∃ σ ∈ A, greedy f σ = z i := fun i => hz (Set.mem_range_self i)
  choose σ hσA hσz using hchoose
  have hσinj : Function.Injective σ := by
    intro i j hij
    apply ha.injective
    rw [← hσz i, ← hσz j, hij]
  have hcard : Fintype.card ι ≤ n := by
    apply affine_card_of_sum hn z (f Finset.univ) _ ha
    intro i
    rw [← hσz i]
    exact greedy_sum_ideal hf0 (σ i) _ (by intro a ha b hb; exact Finset.mem_univ _)
  let S : State n := Finset.univ.toList.map (fun i => (σ i, w i))
  have hpoint : point f S = x := by
    ext v
    have hv := congrFun hwz v
    simpa [point, S, List.map_map, Function.comp_def, ← hσz,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hv
  refine ⟨S, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, hpoint⟩
  · simpa [S] using (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty).ne_empty
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact hw i
  · simpa [S, List.map_map, Function.comp_def] using hw1
  · simpa [S] using hcard
  · simpa [S, List.map_map, Function.comp_def] using
      (Finset.nodup_toList (Finset.univ : Finset ι)).map hσinj
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact hσA i

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE StateFromHull

-- BEGIN COMPLETE MODULE SubroutineOutput
section

open scoped BigOperators
open NonmonotoneSubmod.Shared
namespace SchrijverSFM.Alg.Proof

variable {n : ℕ} {f : Finset (Fin n) → ℝ}

lemma subroutine_exists (hf : Submodular f) (hf0 : f ∅ = 0)
    (σ : Equiv.Perm (Fin n)) (s t : Fin n) (hst : σ s < σ t) :
    ∃ δ : ℝ, ∃ Mv : State n, SubroutineOutput f σ s t δ Mv := by
  obtain ⟨δ, hδ, hx⟩ := subroutine_hull hf hf0 σ s t hst
  let A : Set (Equiv.Perm (Fin n)) := {τ | ∃ u ∈ interval σ s t, IsMoved σ s u τ}
  change greedy f σ + δ • (chi t - chi s) ∈ convexHull ℝ (greedy f '' A) at hx
  obtain ⟨Mv, hMv, _, _, horders, hpoint⟩ := state_of_convexHull hf0 (by omega) A _ hx
  refine ⟨δ, Mv, hδ, fun p hp => (hMv.2.1 p hp).le, hMv.2.2, horders, ?_⟩
  intro v
  exact (congrFun hpoint v).symm

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE SubroutineOutput

-- BEGIN COMPLETE MODULE SegmentScalar
section

namespace SchrijverSFM.Alg.Proof

lemma segment_parameter (x a : ℝ) (hx : x < 0) (ha : 0 ≤ a) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ x + θ * a ≤ 0 ∧ (θ = 1 ∨ x + θ * a = 0) := by
  by_cases h : x + a ≤ 0
  · exact ⟨1, zero_le_one, le_rfl, by simpa using h, Or.inl rfl⟩
  · have hap : 0 < a := by linarith
    refine ⟨-x / a, div_nonneg (by linarith) ha, ?_, ?_, Or.inr ?_⟩
    · apply (div_le_one hap).mpr; linarith
    · rw [div_mul_cancel₀ _ (ne_of_gt hap)]; linarith
    · rw [div_mul_cancel₀ _ (ne_of_gt hap)]; ring

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE SegmentScalar

-- BEGIN COMPLETE MODULE SegmentHull
section

namespace SchrijverSFM.Alg.Proof

variable {n : ℕ} {f : Finset (Fin n) → ℝ}

lemma segment_hull (S : State n) (hS : Valid S) (i : ℕ)
    (σ : Equiv.Perm (Fin n)) (lam : ℝ) (hget : S[i]? = some (σ, lam))
    (s t : Fin n) (δ : ℝ) (Mv : State n) (hMv : SubroutineOutput f σ s t δ Mv)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (x : Fin n → ℝ) (hx : x = point f S + (θ * (lam * δ)) • (chi t - chi s))
    (hend : θ = 1 ∨ x t = 0) :
    x ∈ convexHull ℝ (greedy f '' {τ | τ ∈ (S.eraseIdx i).map Prod.fst ∨
      (x t = 0 ∧ τ = σ) ∨ ∃ u ∈ interval σ s t, IsMoved σ s u τ}) := by
  classical
  have hmem : (σ, lam) ∈ S := List.mem_of_getElem? hget
  have hlam : 0 < lam := hS.2.1 _ hmem
  let A : Set (Equiv.Perm (Fin n)) := {τ | τ ∈ (S.eraseIdx i).map Prod.fst ∨
      (x t = 0 ∧ τ = σ) ∨ ∃ u ∈ interval σ s t, IsMoved σ s u τ}
  let T := S.eraseIdx i ++ [(σ, (1 - θ) * lam)] ++ scaleState (θ * lam) Mv
  have hweights := erase_sum S i (σ, lam) hget Prod.snd
  have hw : (T.map Prod.snd).sum = 1 := by
    simp only [T, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, scaleState_weight]
    rw [hMv.2.2.1, mul_one]
    rw [hS.2.2] at hweights
    dsimp at hweights
    linarith
  have hp : ∀ p ∈ T, 0 ≤ p.2 := by
    intro p hp
    simp only [T, List.mem_append, List.mem_singleton] at hp
    rcases hp with (hp | rfl) | hp
    · exact (hS.2.1 _ (List.mem_of_mem_eraseIdx hp)).le
    · exact mul_nonneg (sub_nonneg.mpr hθ1) hlam.le
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact mul_nonneg (mul_nonneg hθ hlam.le) (hMv.2.1 _ hq)
  have ho : ∀ p ∈ T, p.2 ≠ 0 → p.1 ∈ A := by
    intro p hp hpn
    simp only [T, List.mem_append, List.mem_singleton] at hp
    rcases hp with (hp | rfl) | hp
    · exact Or.inl (List.mem_map.mpr ⟨p, hp, rfl⟩)
    · refine Or.inr (Or.inl ⟨?_, rfl⟩)
      rcases hend with he | he
      · simp [he] at hpn
      · exact he
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact Or.inr (Or.inr (hMv.2.2.2.1 q hq))
  have hT : point f T = x := by
    dsimp only [T]
    rw [point_append, point_append, point_scale, hx, point_erase S i σ lam hget]
    ext v
    have hm := hMv.2.2.2.2 v
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, point,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hm ⊢
    rw [← hm]
    ring
  have hA : A.Nonempty := by
    obtain ⟨p, hpT, hpn⟩ : ∃ p ∈ T, p.2 ≠ 0 := by
      by_contra hh
      push Not at hh
      have : (T.map Prod.snd).sum = 0 := List.sum_eq_zero (by
        intro a ha; obtain ⟨p, hpT, rfl⟩ := List.mem_map.mp ha; exact hh p hpT)
      linarith
    exact ⟨p.1, ho p hpT hpn⟩
  have hfinal := point_mem_hull (f := f) T A hA hp hw ho
  rw [hT] at hfinal
  exact hfinal

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE SegmentHull

-- BEGIN COMPLETE MODULE NewOrdersPartition
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ} {f : Finset (Fin n) → ℝ} {S S' : State n}

theorem newOrders_of_nodup {i : ℕ} {sigma : Equiv.Perm (Fin n)} {s t : Fin n}
    (hn : (S'.map Prod.fst).Nodup)
    (hmem : ∀ tau ∈ S'.map Prod.fst,
      tau ∈ (S.eraseIdx i).map Prod.fst ++ (if point f S' t = 0 then [sigma] else []) ∨
      ∃ a ∈ interval sigma s t, IsMoved sigma s a tau) :
    NewOrders f S S' i sigma s t := by
  let L := (S.eraseIdx i).map Prod.fst ++ (if point f S' t = 0 then [sigma] else [])
  let p : Equiv.Perm (Fin n) → Bool := fun tau => decide (tau ∈ L)
  refine ⟨(S'.map Prod.fst).filter p, (S'.map Prod.fst).filter (fun tau => !p tau),
    (List.filter_append_perm p _).symm, ?_, hn.filter _, ?_⟩
  · apply List.subperm_of_subset (hn.filter _)
    intro tau htau
    have hh := (List.mem_filter.mp htau).2
    simpa [p, L] using hh
  · intro tau htau
    obtain ⟨htau, hp⟩ := List.mem_filter.mp htau
    rcases hmem tau htau with hh | hh
    · have : tau ∉ L := by simpa [p] using hp
      exact (this hh).elim
    · exact hh

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE NewOrdersPartition

-- BEGIN COMPLETE MODULE WalkDistance
section

namespace SchrijverSFM.Alg.Proof
open Classical

variable {n : ℕ} {f : Finset (Fin n) → ℝ} {S : State n}

theorem reachable_iff_walk {v : Fin n} : reachable f S v ↔ ∃ k, walkLen f S k v := by
  constructor
  · rintro ⟨p, hp, h⟩
    induction h with
    | refl => exact ⟨0, hp⟩
    | @tail b c h hbc ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, b, hk, hbc⟩
  · rintro ⟨k, hk⟩
    induction k generalizing v with
    | zero => exact ⟨v, hk, .refl⟩
    | succ k ih =>
      obtain ⟨w, hw, hwv⟩ := hk
      obtain ⟨p, hp, h⟩ := ih hw
      exact ⟨p, hp, h.tail hwv⟩

theorem dist_le_walk {k : ℕ} {v : Fin n} (h : walkLen f S k v) :
    dist f S v ≤ (k : ℕ∞) :=
  iInf_le_of_le k (iInf_le_of_le h le_rfl)

theorem dist_eq_find {v : Fin n} (h : ∃ k, walkLen f S k v) :
    dist f S v = (Nat.find h : ℕ∞) := by
  classical
  apply le_antisymm (dist_le_walk (Nat.find_spec h))
  apply le_iInf
  intro k
  apply le_iInf
  intro hk
  exact_mod_cast Nat.find_min' h hk

theorem dist_eq_top_iff {v : Fin n} : dist f S v = ⊤ ↔ ¬ reachable f S v := by
  classical
  rw [reachable_iff_walk]
  constructor
  · intro he h
    rw [dist_eq_find h] at he
    exact ENat.natCast_ne_top _ he
  · intro h
    simp only [dist]
    apply top_unique
    apply le_iInf
    intro k
    apply le_iInf
    intro hk
    exact (h ⟨k, hk⟩).elim

theorem dist_zero_iff {v : Fin n} : dist f S v = 0 ↔ v ∈ posSet f S := by
  classical
  constructor
  · intro hd
    have hr : reachable f S v := by
      by_contra h
      have := dist_eq_top_iff.mpr h
      rw [hd] at this
      exact ENat.zero_ne_top this
    have hw := reachable_iff_walk.mp hr
    have he : Nat.find hw = 0 := by
      have := dist_eq_find hw
      rw [hd] at this
      exact_mod_cast this.symm
    simpa [he, walkLen] using Nat.find_spec hw
  · intro h
    exact le_antisymm (dist_le_walk (k := 0) h) (zero_le)

theorem dist_arc {u v : Fin n} (h : arc S u v) :
    dist f S v ≤ dist f S u + 1 := by
  classical
  by_cases hr : reachable f S u
  · have hw := reachable_iff_walk.mp hr
    rw [dist_eq_find hw]
    simpa only [Nat.cast_add, Nat.cast_one] using
      dist_le_walk (v := v) (k := Nat.find hw + 1) ⟨u, Nat.find_spec hw, h⟩
  · rw [dist_eq_top_iff.mpr hr]
    simp

theorem dist_predecessor {v : Fin n} (hr : reachable f S v)
    (hn : v ∉ posSet f S) :
    ∃ u, arc S u v ∧ dist f S u + 1 = dist f S v := by
  classical
  have hw := reachable_iff_walk.mp hr
  have hk : Nat.find hw ≠ 0 := by
    intro hk
    exact hn (by simpa [hk, walkLen] using Nat.find_spec hw)
  obtain ⟨k, he⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hh : walkLen f S (k + 1) v := by simpa [he] using Nat.find_spec hw
  obtain ⟨u, hu, huv⟩ := hh
  refine ⟨u, huv, le_antisymm ?_ (dist_arc huv)⟩
  rw [dist_eq_find hw, he]
  simpa only [Nat.cast_succ, add_comm] using add_le_add_right (dist_le_walk hu) 1

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE WalkDistance

-- BEGIN COMPLETE MODULE ChosenVertices
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ} {f : Finset (Fin n) → ℝ} {S : State n}

theorem chosen_t_exists (h : ¬ caseOne f S) : ∃ t, IsChosenT f S t := by
  have he : ∃ t ∈ negSet f S, reachable f S t := not_not.mp h
  let T := (negSet f S).filter (reachable f S)
  have hT : T.Nonempty := by
    obtain ⟨t, ht, hr⟩ := he
    exact ⟨t, Finset.mem_filter.mpr ⟨ht, hr⟩⟩
  obtain ⟨t, ht, hmax⟩ := T.exists_max_image (fun t => toLex (dist f S t, t)) hT
  refine ⟨t, (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2, ?_⟩
  intro v hv hr
  exact hmax v (Finset.mem_filter.mpr ⟨hv, hr⟩)

theorem chosen_s_exists {t : Fin n} (ht : IsChosenT f S t) :
    ∃ s, IsChosenS f S t s := by
  have hn : t ∉ posSet f S := by
    intro hp
    have hp' : 0 < point f S t := (Finset.mem_filter.mp hp).2
    have hn' : point f S t < 0 := (Finset.mem_filter.mp ht.1).2
    linarith
  obtain ⟨u, hu, hud⟩ := dist_predecessor ht.2.1 hn
  let U := Finset.univ.filter (fun s => arc S s t ∧ dist f S s + 1 = dist f S t)
  have hU : U.Nonempty := ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, hud⟩⟩
  obtain ⟨s, hs, hmax⟩ := U.exists_max_image id hU
  refine ⟨s, (Finset.mem_filter.mp hs).2.1, (Finset.mem_filter.mp hs).2.2, ?_⟩
  intro v hv hd
  exact hmax v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, hd⟩)

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE ChosenVertices

-- BEGIN COMPLETE MODULE IntervalMaximum
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ}

theorem interval_nonempty_iff (σ : Equiv.Perm (Fin n)) (s t : Fin n) :
    (interval σ s t).Nonempty ↔ σ s < σ t := by
  constructor
  · rintro ⟨v, hv⟩
    have h := (Finset.mem_filter.mp hv).2
    exact h.1.trans_le h.2
  · intro h
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, le_rfl⟩⟩

theorem interval_card_lt (σ : Equiv.Perm (Fin n)) (s t : Fin n) :
    (interval σ s t).card < n := by
  have hs : s ∉ interval σ s t := by simp [interval]
  have hsub : interval σ s t ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro he
    exact hs (he.symm ▸ Finset.mem_univ s)
  have hc := Finset.card_lt_card hsub
  simpa using hc

theorem interval_card_le_alpha {S : State n} {p : Equiv.Perm (Fin n) × ℝ}
    (hp : p ∈ S) (s t : Fin n) : (interval p.1 s t).card ≤ alpha S s t := by
  exact List.le_max_of_le (List.mem_map.mpr ⟨p, hp, rfl⟩) le_rfl

theorem alpha_attained {S : State n} (hS : S ≠ []) (s t : Fin n) :
    ∃ (i : ℕ) (σ : Equiv.Perm (Fin n)) (lam : ℝ), S[i]? = some (σ, lam) ∧ (interval σ s t).card = alpha S s t := by
  have hne : S.toFinset.Nonempty := by
    cases S with
    | nil => exact (hS rfl).elim
    | cons p S => exact ⟨p, by simp⟩
  obtain ⟨p, hp, hm⟩ := S.toFinset.exists_max_image (fun p => (interval p.1 s t).card) hne
  have hpS : p ∈ S := List.mem_toFinset.mp hp
  have he : alpha S s t = (interval p.1 s t).card := by
    apply le_antisymm
    · apply List.max_le_of_forall_le
      intro a ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      exact hm q (List.mem_toFinset.mpr hq)
    · exact interval_card_le_alpha hpS s t
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hpS
  exact ⟨i, p.1, p.2, hi, he.symm⟩

theorem alpha_pos_of_arc {S : State n} {s t : Fin n} (h : arc S s t) :
    0 < alpha S s t := by
  obtain ⟨p, hp, hst⟩ := h
  exact (Finset.card_pos.mpr ((interval_nonempty_iff p.1 s t).mpr hst)).trans_le
    (interval_card_le_alpha hp s t)

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE IntervalMaximum

-- BEGIN COMPLETE MODULE SuccessorConstruction
section

open NonmonotoneSubmod.Shared
namespace SchrijverSFM.Alg.Proof

variable {n : ℕ} {f : Finset (Fin n) → ℝ}

lemma successor_of_choices (hf : Submodular f) (hf0 : f ∅ = 0)
    (S : State n) (hS : Valid S) (hcase : ¬ caseOne f S)
    (t s : Fin n) (ht : IsChosenT f S t) (hs : IsChosenS f S t s)
    (i : ℕ) (σ : Equiv.Perm (Fin n)) (lam : ℝ)
    (hget : S[i]? = some (σ, lam)) (hmax : (interval σ s t).card = alpha S s t) :
    ∃ S' : State n, StepVia f S S' t s i := by
  classical
  have hst : σ s < σ t := (interval_nonempty_iff σ s t).mp
    (Finset.card_pos.mp (hmax ▸ alpha_pos_of_arc hs.1))
  have hts : t ≠ s := fun he => by subst t; exact (lt_irrefl _ hst)
  have hlam : 0 < lam := hS.2.1 _ (List.mem_of_getElem? hget)
  have htneg : point f S t < 0 := (Finset.mem_filter.mp ht.1).2
  obtain ⟨δ, Mv, hMv⟩ := subroutine_exists hf hf0 σ s t hst
  obtain ⟨θ, hθ, hθ1, hxt, hend⟩ := segment_parameter (point f S t) (lam * δ)
    htneg (mul_nonneg hlam.le hMv.1)
  let x := point f S + (θ * (lam * δ)) • (chi t - chi s)
  have hxe : x t = point f S t + θ * (lam * δ) := by simp [x, chi, hts]
  have hend' : θ = 1 ∨ x t = 0 := by simpa only [hxe] using hend
  have hxh := segment_hull S hS i σ lam hget s t δ Mv hMv θ hθ hθ1 x rfl hend'
  obtain ⟨S', hS', hlen, hnodup, horders, hpoint⟩ := state_of_convexHull hf0 (by omega) _ x hxh
  refine ⟨S', hS, hcase, ht, hs, σ, lam, hget, hmax, δ, ⟨Mv, hMv⟩, ?_, hS', hlen, ?_⟩
  · refine ⟨θ, hθ, hθ1, ?_, ?_, ?_⟩
    · intro v; exact congrFun hpoint v
    · rw [hpoint, hxe]; exact hxt
    · rw [hpoint]; exact hend'
  · apply newOrders_of_nodup hnodup
    intro τ hτ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hτ
    rcases horders p hp with hold | hzero | hmove
    · exact Or.inl (List.mem_append.mpr (Or.inl hold))
    · refine Or.inl (List.mem_append.mpr (Or.inr ?_))
      rw [hpoint, if_pos hzero.1]
      simp [hzero.2]
    · exact Or.inr hmove

lemma progress (hf : Submodular f) (hf0 : f ∅ = 0)
    (S : State n) (hS : Valid S) (hcase : ¬ caseOne f S) :
    ∃ S' : State n, Step f S S' := by
  obtain ⟨t, ht⟩ := chosen_t_exists hcase
  obtain ⟨s, hs⟩ := chosen_s_exists ht
  obtain ⟨i, σ, lam, hget, hmax⟩ := alpha_attained hS.1 s t
  obtain ⟨S', hstep⟩ := successor_of_choices hf hf0 S hS hcase t s ht hs i σ lam hget hmax
  exact ⟨S', t, s, i, hstep⟩

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE SuccessorConstruction

-- BEGIN COMPLETE MODULE DistanceComparison
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ} {f : Finset (Fin n) → ℝ} {S S' : State n}

theorem dist_comparison (hp : posSet f S' ⊆ posSet f S)
    (ha : ∀ u v, arc S' u v → dist f S v ≤ dist f S u + 1) (v : Fin n) :
    dist f S v ≤ dist f S' v := by
  apply le_iInf
  intro k
  apply le_iInf
  intro hk
  induction k generalizing v with
  | zero => exact le_of_eq (dist_zero_iff.mpr (hp hk))
  | succ k ih =>
    obtain ⟨u, hu, huv⟩ := hk
    have hb : dist f S u + 1 ≤ (k + 1 : ℕ) := by
      simpa only [Nat.cast_succ, add_comm] using add_le_add_right (ih u hu) 1
    exact (ha u v huv).trans hb

theorem segment_pos_subset {t s : Fin n} {lam delta : ℝ}
    (hlam : 0 ≤ lam) (hdelta : 0 ≤ delta)
    (h : SegmentPoint f S S' t s lam delta) : posSet f S' ⊆ posSet f S := by
  obtain ⟨theta, ht, _, he, hneg, _⟩ := h
  intro v hv
  have hv' : 0 < point f S' v := (Finset.mem_filter.mp hv).2
  have hvt : v ≠ t := by intro hvt; subst v; linarith
  have hh := he v
  have hnon : 0 ≤ theta * (lam * delta) := mul_nonneg ht (mul_nonneg hlam hdelta)
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  by_cases hvs : v = s
  · simp only [chi, if_neg hvt, if_pos hvs, zero_sub, mul_neg, mul_one] at hh
    linarith
  · simp only [chi, if_neg hvt, if_neg hvs, sub_self, mul_zero, add_zero] at hh
    rwa [hh] at hv'

theorem moved_arc_bound {sigma tau : Equiv.Perm (Fin n)} {s t a : Fin n}
    (hsigma : ∃ lam, (sigma, lam) ∈ S) (ha : a ∈ interval sigma s t)
    (hmove : IsMoved sigma s a tau) (hd : dist f S s + 1 = dist f S t)
    {u v : Fin n} (huv : tau u < tau v) : dist f S v ≤ dist f S u + 1 := by
  obtain ⟨lam, hmem⟩ := hsigma
  obtain h | h := (hmove u v).mp huv
  · obtain ⟨hua, hsv, hva⟩ := h
    subst u
    have hat : sigma a ≤ sigma t := (Finset.mem_filter.mp ha).2.2
    have hvs : dist f S v ≤ dist f S s + 1 := by
      rcases hsv.eq_or_lt with he | he
      · have : s = v := sigma.injective he
        subst v
        exact le_add_right le_rfl
      · exact dist_arc ⟨(sigma, lam), hmem, he⟩
    have hta : dist f S t ≤ dist f S a + 1 := by
      rcases hat.eq_or_lt with he | he
      · have : a = t := sigma.injective he
        subst a
        exact le_add_right le_rfl
      · exact dist_arc ⟨(sigma, lam), hmem, he⟩
    exact (hvs.trans (le_of_eq hd)).trans hta
  · exact dist_arc ⟨(sigma, lam), hmem, h.1⟩

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE DistanceComparison

-- BEGIN COMPLETE MODULE MovedIntervals
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ} {sigma tau : Equiv.Perm (Fin n)} {s t a : Fin n}

theorem moved_into_t (ha : a ∈ interval sigma s t) (hm : IsMoved sigma s a tau)
    {v : Fin n} (h : tau v < tau t) : sigma v < sigma t := by
  rcases (hm v t).mp h with h | h
  · have hat := (Finset.mem_filter.mp ha).2.2
    exact (not_lt_of_ge hat h.2.2).elim
  · exact h.1

theorem moved_interval_subset_erase (ha : a ∈ interval sigma s t)
    (hm : IsMoved sigma s a tau) : interval tau s t ⊆ (interval sigma s t).erase a := by
  intro v hv
  have hv' := (Finset.mem_filter.mp hv).2
  have hsa := (Finset.mem_filter.mp ha).2.1
  have hne : s ≠ a := by intro he; subst a; exact (lt_irrefl _ hsa)
  have hsv : sigma s < sigma v ∧ v ≠ a := by
    rcases (hm s v).mp hv'.1 with h | h
    · exact (hne h.1).elim
    · refine ⟨h.1, ?_⟩
      intro he
      exact h.2 ⟨he, le_rfl, hsa⟩
  have hvt : sigma v ≤ sigma t := by
    rcases hv'.2.eq_or_lt with he | he
    · exact le_of_eq (congrArg sigma (tau.injective he))
    · exact (moved_into_t ha hm he).le
  exact Finset.mem_erase.mpr ⟨hsv.2, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hsv.1, hvt⟩⟩

theorem moved_interval_card_lt (ha : a ∈ interval sigma s t)
    (hm : IsMoved sigma s a tau) :
    (interval tau s t).card < (interval sigma s t).card := by
  exact (Finset.card_le_card (moved_interval_subset_erase ha hm)).trans_lt
    (Finset.card_erase_lt_of_mem ha)

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE MovedIntervals

-- BEGIN COMPLETE MODULE StepDistance
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ} {f : Finset (Fin n) → ℝ} {S S' : State n}

theorem new_order_cases {i : ℕ} {sigma : Equiv.Perm (Fin n)} {s t : Fin n}
    (h : NewOrders f S S' i sigma s t) {tau : Equiv.Perm (Fin n)}
    (htau : tau ∈ S'.map Prod.fst) :
    tau ∈ S.map Prod.fst ∨ tau = sigma ∨
      ∃ a ∈ interval sigma s t, IsMoved sigma s a tau := by
  obtain ⟨L1, L2, he, hsub, _, hm⟩ := h
  have ht := he.mem_iff.mp htau
  rcases List.mem_append.mp ht with ht | ht
  · have hh := hsub.subset ht
    rcases List.mem_append.mp hh with hh | hh
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
      exact Or.inl (List.mem_map.mpr ⟨p, List.mem_of_mem_eraseIdx hp, rfl⟩)
    · right; left
      split_ifs at hh with hzero
      · simpa using hh
      · simp at hh
  · exact Or.inr (Or.inr (hm tau ht))

theorem new_arc_bound {i : ℕ} {sigma : Equiv.Perm (Fin n)} {s t : Fin n}
    (h : NewOrders f S S' i sigma s t) (hsigma : ∃ lam, (sigma, lam) ∈ S)
    (hd : dist f S s + 1 = dist f S t) {u v : Fin n} (huv : arc S' u v) :
    dist f S v ≤ dist f S u + 1 := by
  obtain ⟨p, hp, huv⟩ := huv
  rcases new_order_cases h (List.mem_map.mpr ⟨p, hp, rfl⟩) with h | h | h
  · obtain ⟨q, hq, he⟩ := List.mem_map.mp h
    exact dist_arc ⟨q, hq, he ▸ huv⟩
  · obtain ⟨lam, hm⟩ := hsigma
    exact dist_arc ⟨(sigma, lam), hm, h ▸ huv⟩
  · obtain ⟨a, ha, hm⟩ := h
    exact moved_arc_bound hsigma ha hm hd huv

theorem stepVia_dist_mono {t s : Fin n} {i : ℕ} (h : StepVia f S S' t s i)
    (v : Fin n) : dist f S v ≤ dist f S' v := by
  obtain ⟨hvalid, _, _, hs, sigma, lam, hi, _, delta, hsub, hseg, _, _, hord⟩ := h
  have hmem : (sigma, lam) ∈ S := List.mem_iff_getElem?.mpr ⟨i, hi⟩
  obtain ⟨Mv, hdelta, _⟩ := hsub
  apply dist_comparison (segment_pos_subset (le_of_lt (hvalid.2.1 _ hmem)) hdelta hseg)
  intro u w huw
  exact new_arc_bound hord ⟨lam, hmem⟩ hs.2.1 huw

theorem step_dist_mono (h : Step f S S') (v : Fin n) :
    dist f S v ≤ dist f S' v := by
  obtain ⟨t, s, i, h⟩ := h
  exact stepVia_dist_mono h v

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE StepDistance

-- BEGIN COMPLETE MODULE IntervalDecrease
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ}

theorem count_map_eraseIdx {A B : Type*} [DecidableEq B] (g : A → B)
    (L : List A) (i : ℕ) (a : A) (hi : L[i]? = some a) :
    (L.map g).count (g a) = ((L.eraseIdx i).map g).count (g a) + 1 := by
  induction L generalizing i with
  | nil => simp at hi
  | cons b L ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst b
      simp
    | succ i =>
      have hh := ih i (by simpa using hi)
      simpa only [List.map_cons, List.eraseIdx_cons_succ, List.count_cons, Nat.add_right_comm] using
        congrArg (fun k => k + if g b == g a then 1 else 0) hh

theorem new_interval_alpha_le {f : Finset (Fin n) → ℝ} {S S' : State n}
    {i : ℕ} {sigma : Equiv.Perm (Fin n)} {s t : Fin n}
    (h : NewOrders f S S' i sigma s t)
    (hsigma : (interval sigma s t).card = alpha S s t) :
    alpha S' s t ≤ alpha S s t := by
  apply List.max_le_of_forall_le
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  rcases new_order_cases h (List.mem_map.mpr ⟨p, hp, rfl⟩) with hh | hh | hh
  · obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hh
    simpa [← hqeq] using interval_card_le_alpha hq s t
  · simpa [hh] using hsigma.le
  · obtain ⟨a, ha, hm⟩ := hh
    exact (moved_interval_card_lt ha hm).le.trans hsigma.le

theorem new_interval_beta_lt {f : Finset (Fin n) → ℝ} {S S' : State n}
    {i : ℕ} {sigma : Equiv.Perm (Fin n)} {lam : ℝ} {s t : Fin n}
    (h : NewOrders f S S' i sigma s t) (hi : S[i]? = some (sigma, lam))
    (hsigma : (interval sigma s t).card = alpha S s t)
    (hneg : point f S' t ≠ 0) (heq : alpha S' s t = alpha S s t) :
    beta S' s t < beta S s t := by
  obtain ⟨L1, L2, hperm, hsub, _, hm⟩ := h
  simp only [if_neg hneg, List.append_nil] at hsub
  let g : Equiv.Perm (Fin n) → ℕ := fun tau => (interval tau s t).card
  have hc2 : (L2.map g).count (alpha S s t) = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro hh
    obtain ⟨tau, htau, he⟩ := List.mem_map.mp hh
    obtain ⟨a, ha, hmove⟩ := hm tau htau
    have hlt := moved_interval_card_lt ha hmove
    change g tau < (interval sigma s t).card at hlt
    rw [he, hsigma] at hlt
    exact (lt_irrefl _ hlt)
  have hsubmap : (L1.map g).Subperm (((S.eraseIdx i).map Prod.fst).map g) := by
    obtain ⟨L, hp, hs⟩ := hsub
    exact ⟨L.map g, hp.map g, hs.map g⟩
  have hc1 := (List.subperm_iff_count.mp hsubmap) (alpha S s t)
  have hremove := count_map_eraseIdx (fun p : Equiv.Perm (Fin n) × ℝ => g p.1) S i
    (sigma, lam) hi
  have hcounts := (hperm.map g).count_eq (alpha S s t)
  simp only [List.map_append, List.count_append, hc2, add_zero, List.map_map] at hcounts
  change beta S' s t < beta S s t
  unfold beta
  rw [heq]
  change (S'.map (g ∘ Prod.fst)).count (alpha S s t) <
    (S.map (g ∘ Prod.fst)).count (alpha S s t)
  rw [hcounts]
  change g sigma = alpha S s t at hsigma
  simp only [List.map_map] at hc1
  change (S.map (g ∘ Prod.fst)).count (g sigma) =
    ((S.eraseIdx i).map (g ∘ Prod.fst)).count (g sigma) + 1 at hremove
  rw [hsigma] at hremove
  omega

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE IntervalDecrease

-- BEGIN COMPLETE MODULE DistanceBound
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ} {f : Finset (Fin n) → ℝ} {S : State n}

theorem dist_levels {k : ℕ} {v : Fin n} (hv : dist f S v = (k : ℕ∞)) :
    ∀ j ≤ k, ∃ u, dist f S u = (j : ℕ∞) := by
  induction k generalizing v with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    subst j
    exact ⟨v, hv⟩
  | succ k ih =>
    have hr : reachable f S v := by
      by_contra h
      rw [dist_eq_top_iff.mpr h] at hv
      exact ENat.natCast_ne_top _ hv.symm
    have hp : v ∉ posSet f S := by
      intro hp
      have hh := dist_zero_iff.mpr hp
      rw [hv] at hh
      have hz : k + 1 = 0 := by exact_mod_cast hh
      omega
    obtain ⟨u, _, hu⟩ := dist_predecessor hr hp
    have hu' : dist f S u = (k : ℕ∞) := by
      rw [hv, Nat.cast_add, Nat.cast_one] at hu
      exact ENat.add_left_injective_of_ne_top (by simp : (1 : ℕ∞) ≠ ⊤) hu
    intro j hj
    by_cases he : j = k + 1
    · exact ⟨v, by simpa [he] using hv⟩
    · exact ih hu' j (by omega)

theorem dist_nat_lt_card {k : ℕ} {v : Fin n} (hv : dist f S v = (k : ℕ∞)) :
    k < n := by
  choose u hu using fun j : Fin (k + 1) => dist_levels hv j.val (by omega)
  have hinj : Function.Injective u := by
    intro i j hij
    have he := (hu i).symm.trans ((congrArg (dist f S) hij).trans (hu j))
    have : i.val = j.val := by exact_mod_cast he
    exact Fin.ext this
  have hc := Fintype.card_le_of_injective u hinj
  simpa only [Fintype.card_fin, Nat.succ_le_iff] using hc

theorem reachable_dist_bound {v : Fin n} (hr : reachable f S v) :
    ∃ k < n, dist f S v = (k : ℕ∞) := by
  have hw := reachable_iff_walk.mp hr
  exact ⟨Nat.find hw, dist_nat_lt_card (dist_eq_find hw), dist_eq_find hw⟩

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE DistanceBound

-- BEGIN COMPLETE MODULE StepChoices
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ} {f : Finset (Fin n) → ℝ} {S S' : State n}

theorem segment_negative_old_or_source {t s v : Fin n} {lam delta : ℝ}
    (hlam : 0 ≤ lam) (hdelta : 0 ≤ delta)
    (h : SegmentPoint f S S' t s lam delta) (hv : v ∈ negSet f S') :
    v ∈ negSet f S ∨ v = s := by
  by_cases hvs : v = s
  · exact Or.inr hvs
  left
  obtain ⟨theta, ht, _, he, _, _⟩ := h
  have hv' := (Finset.mem_filter.mp hv).2
  have hh := he v
  have hnon : 0 ≤ theta * (lam * delta) := mul_nonneg ht (mul_nonneg hlam hdelta)
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  by_cases hvt : v = t
  · simp only [chi, if_pos hvt, if_neg hvs, sub_zero, mul_one] at hh
    linarith
  · simp only [chi, if_neg hvt, if_neg hvs, sub_self, mul_zero, add_zero] at hh
    rwa [hh] at hv'

theorem chosen_source_dist_lt {t s : Fin n} (ht : IsChosenT f S t)
    (hs : IsChosenS f S t s) : dist f S s < dist f S t := by
  obtain ⟨k, _, hk⟩ := reachable_dist_bound ht.2.1
  have hfinite : dist f S s ≠ ⊤ := by
    intro he
    have hh := hs.2.1
    rw [he, top_add] at hh
    exact ENat.natCast_ne_top _ (hk.symm.trans hh.symm)
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hfinite
  rw [← hs.2.1, ← hj]
  exact_mod_cast Nat.lt_succ_self j

theorem new_arc_into_old_target {i : ℕ} {sigma : Equiv.Perm (Fin n)} {s t : Fin n}
    (h : NewOrders f S S' i sigma s t) (hsigma : ∃ lam, (sigma, lam) ∈ S)
    {v : Fin n} (hv : arc S' v t) : arc S v t := by
  obtain ⟨p, hp, hpt⟩ := hv
  rcases new_order_cases h (List.mem_map.mpr ⟨p, hp, rfl⟩) with hh | hh | hh
  · obtain ⟨q, hq, hqeq⟩ := List.mem_map.mp hh
    exact ⟨q, hq, hqeq ▸ hpt⟩
  · obtain ⟨lam, hmem⟩ := hsigma
    exact ⟨(sigma, lam), hmem, hh ▸ hpt⟩
  · obtain ⟨a, ha, hm⟩ := hh
    obtain ⟨lam, hmem⟩ := hsigma
    exact ⟨(sigma, lam), hmem, moved_into_t ha hm hpt⟩

theorem next_target_le {t s t' : Fin n} {i : ℕ}
    (h : StepVia f S S' t s i) (hd : ∀ v, dist f S' v = dist f S v)
    (ht' : IsChosenT f S' t') :
    toLex (dist f S t', t') ≤ toLex (dist f S t, t) := by
  obtain ⟨hv, _, ht, hs, sigma, lam, hi, _, delta, hsub, hseg, _, _, _⟩ := h
  have hmem : (sigma, lam) ∈ S := List.mem_iff_getElem?.mpr ⟨i, hi⟩
  obtain ⟨Mv, hdelta, _⟩ := hsub
  rcases segment_negative_old_or_source (le_of_lt (hv.2.1 _ hmem)) hdelta hseg ht'.1 with hh | hh
  · apply ht.2.2 t' hh
    by_contra hr
    have he := dist_eq_top_iff.mpr hr
    have he' : dist f S' t' = ⊤ := (hd t').trans he
    exact (dist_eq_top_iff.mp he') ht'.2.1
  · subst t'
    exact le_of_lt (Prod.Lex.toLex_lt_toLex.mpr (Or.inl (chosen_source_dist_lt ht hs)))

theorem next_source_le {t s s' : Fin n} {i : ℕ}
    (h : StepVia f S S' t s i) (hd : ∀ v, dist f S' v = dist f S v)
    (hs' : IsChosenS f S' t s') : s' ≤ s := by
  obtain ⟨_, _, _, hs, sigma, lam, hi, _, delta, _, _, _, _, hord⟩ := h
  apply hs.2.2 s'
  · exact new_arc_into_old_target hord
      ⟨lam, List.mem_iff_getElem?.mpr ⟨i, hi⟩⟩ hs'.1
  · simpa only [hd] using hs'.2.1

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE StepChoices

-- BEGIN COMPLETE MODULE FiniteKeys
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ}

noncomputable def vertexRank (d : Fin n → ℕ∞) (t : Fin n) : ℕ :=
  (Finset.univ.filter (fun v => toLex (d v, v) < toLex (d t, t))).card

theorem vertexRank_lt (d : Fin n → ℕ∞) (t : Fin n) : vertexRank d t < n := by
  apply lt_of_lt_of_eq (Finset.card_lt_card ?_) (Finset.card_fin n)
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro he
  have : t ∈ Finset.univ.filter (fun v => toLex (d v, v) < toLex (d t, t)) := by rw [he]; simp
  simp at this

theorem vertexRank_strict {d : Fin n → ℕ∞} {t u : Fin n}
    (h : toLex (d t, t) < toLex (d u, u)) : vertexRank d t < vertexRank d u := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hv).2).trans h⟩
  · intro he
    have ht : t ∈ Finset.univ.filter (fun v => toLex (d v, v) < toLex (d u, u)) := by simp [h]
    rw [← he] at ht
    simp at ht

theorem vertexRank_mono {d : Fin n → ℕ∞} {t u : Fin n}
    (h : toLex (d t, t) ≤ toLex (d u, u)) : vertexRank d t ≤ vertexRank d u := by
  rcases h.eq_or_lt with he | he
  · have : t = u := congrArg Prod.snd (toLex.injective he)
    simp [this]
  · exact (vertexRank_strict he).le

theorem alpha_lt_card {S : State n} (hS : S ≠ []) (s t : Fin n) : alpha S s t < n := by
  obtain ⟨i, sigma, lam, _, he⟩ := alpha_attained hS s t
  rw [← he]
  exact interval_card_lt sigma s t

theorem beta_pos {S : State n} (hS : S ≠ []) (s t : Fin n) : 0 < beta S s t := by
  obtain ⟨i, sigma, lam, hi, he⟩ := alpha_attained hS s t
  apply List.count_pos_iff.mpr
  exact List.mem_map.mpr ⟨(sigma, lam), List.mem_iff_getElem?.mpr ⟨i, hi⟩, he⟩

theorem beta_le_length (S : State n) (s t : Fin n) : beta S s t ≤ S.length := by
  simpa [beta] using (List.count_le_length (a := alpha S s t) (l := S.map (fun p => (interval p.1 s t).card)))

noncomputable def stateKey (f : Finset (Fin n) → ℝ) (S : State n) (t s : Fin n) : ℕ :=
  ((vertexRank (dist f S) t * n + s.val) * n + (alpha S s t - 1)) * n + (beta S s t - 1)

theorem stateKey_lt {f : Finset (Fin n) → ℝ} {S : State n} (hS : S ≠ [])
    (hlen : S.length ≤ n) (t s : Fin n) : stateKey f S t s < n ^ 4 := by
  have hr := vertexRank_lt (dist f S) t
  have hs := s.isLt
  have ha := alpha_lt_card hS s t
  have hb := beta_le_length S s t
  have hp := beta_pos hS s t
  have hb' : beta S s t - 1 < n := by omega
  have ha' : alpha S s t - 1 < n := by omega
  have h1 : vertexRank (dist f S) t * n + s.val < n * n := by nlinarith
  have h2 : (vertexRank (dist f S) t * n + s.val) * n + (alpha S s t - 1) < n*n*n := by nlinarith
  unfold stateKey
  nlinarith [sq_nonneg (n : ℤ)]

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE FiniteKeys

-- BEGIN COMPLETE MODULE KeyDecrease
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ} {f : Finset (Fin n) → ℝ} {S S' : State n}

theorem append_digit_lt {a b c d N : ℕ} (hab : a < b) (hc : c < N) :
    a*N+c < b*N+d := by nlinarith

theorem step_key_decrease {t s t' s' : Fin n} {i : ℕ}
    (h : StepVia f S S' t s i) (hd : ∀ v, dist f S' v = dist f S v)
    (ht' : IsChosenT f S' t') (hs' : IsChosenS f S' t' s') :
    stateKey f S' t' s' < stateKey f S t s := by
  have hvalid : Valid S' := by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hv, _, _⟩ := h; exact hv
  have hlen : S'.length ≤ n := by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hl, _⟩ := h; exact hl
  have ha : alpha S' s' t' - 1 < n := by have := alpha_lt_card hvalid.1 s' t'; omega
  have hb : beta S' s' t' - 1 < n := by
    have := beta_le_length S' s' t'
    have := beta_pos hvalid.1 s' t'
    omega
  have hfun : dist f S' = dist f S := funext hd
  have ht := next_target_le h hd ht'
  unfold stateKey
  rw [hfun]
  by_cases he : t' = t
  · subst t'
    have hsle := next_source_le h hd hs'
    by_cases hes : s' = s
    · subst s'
      obtain ⟨_, _, _, hs, sigma, lam, hi, hmax, delta, _, _, _, _, hord⟩ := h
      have hale := new_interval_alpha_le hord hmax
      by_cases hae : alpha S' s t = alpha S s t
      · have hneg : point f S' t ≠ 0 := ne_of_lt ((Finset.mem_filter.mp ht'.1).2)
        have hblt := new_interval_beta_lt hord hi hmax hneg hae
        have hbpos := beta_pos hvalid.1 s t
        rw [hae]
        omega
      · have hapos : 0 < alpha S' s t := alpha_pos_of_arc hs'.1
        have hal : alpha S' s t - 1 < alpha S s t - 1 := by omega
        apply append_digit_lt _ hb
        omega
    · have hsl : s'.val < s.val := hsle.lt_of_ne hes
      apply append_digit_lt _ hb
      apply append_digit_lt _ ha
      omega
  · have htl : toLex (dist f S t', t') < toLex (dist f S t, t) := by
      apply ht.lt_of_ne
      intro hh
      exact he (congrArg Prod.snd (toLex.injective hh))
    have hrl := vertexRank_strict htl
    exact append_digit_lt (append_digit_lt (append_digit_lt hrl s'.isLt) ha) hb

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE KeyDecrease

-- BEGIN COMPLETE MODULE DistancePhase
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ} {f : Finset (Fin n) → ℝ} {S S' : State n}

noncomputable def capDistance (f : Finset (Fin n) → ℝ) (S : State n) (v : Fin n) : ℕ :=
  (min (dist f S v) (n : ℕ∞)).toNat

noncomputable def distancePhase (f : Finset (Fin n) → ℝ) (S : State n) : ℕ :=
  ∑ v, capDistance f S v

theorem capDistance_le (v : Fin n) : capDistance f S v ≤ n :=
  ENat.toNat_le_of_le_natCast (min_le_right _ _)

theorem capDistance_mono (h : ∀ v, dist f S v ≤ dist f S' v) (v : Fin n) :
    capDistance f S v ≤ capDistance f S' v := by
  apply ENat.toNat_le_toNat (min_le_min_right _ (h v))
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top n) (min_le_right _ _)

theorem capDistance_eq_of_nat {v : Fin n} {k : ℕ} (h : dist f S v = (k : ℕ∞)) :
    capDistance f S v = k := by
  have hk : k < n := dist_nat_lt_card h
  unfold capDistance
  rw [h, min_eq_left (by exact_mod_cast hk.le)]
  simp

theorem capDistance_eq_top {v : Fin n} (h : dist f S v = ⊤) :
    capDistance f S v = n := by simp [capDistance, h]

theorem dist_eq_of_cap_eq {v : Fin n} (h : capDistance f S v = capDistance f S' v) :
    dist f S v = dist f S' v := by
  by_cases hr : reachable f S v
  · obtain ⟨k, hk, hd⟩ := reachable_dist_bound hr
    by_cases hr' : reachable f S' v
    · obtain ⟨j, _, hd'⟩ := reachable_dist_bound hr'
      rw [capDistance_eq_of_nat hd, capDistance_eq_of_nat hd'] at h
      simp [hd, hd', h]
    · rw [capDistance_eq_of_nat hd, capDistance_eq_top (dist_eq_top_iff.mpr hr')] at h
      omega
  · by_cases hr' : reachable f S' v
    · obtain ⟨j, hj, hd'⟩ := reachable_dist_bound hr'
      rw [capDistance_eq_top (dist_eq_top_iff.mpr hr), capDistance_eq_of_nat hd'] at h
      omega
    · rw [dist_eq_top_iff.mpr hr, dist_eq_top_iff.mpr hr']

theorem distancePhase_mono (h : ∀ v, dist f S v ≤ dist f S' v) :
    distancePhase f S ≤ distancePhase f S' :=
  Finset.sum_le_sum (fun v _ => capDistance_mono h v)

theorem dist_eq_of_phase_eq (h : ∀ v, dist f S v ≤ dist f S' v)
    (he : distancePhase f S = distancePhase f S') (v : Fin n) :
    dist f S v = dist f S' v := by
  apply dist_eq_of_cap_eq
  exact (Finset.sum_eq_sum_iff_of_le (fun v _ => capDistance_mono h v)).mp he v
    (Finset.mem_univ _)

theorem distancePhase_bound (h : ¬ caseOne f S) :
    distancePhase f S ≤ n * (n - 1) := by
  obtain ⟨t, _, p, hp, _⟩ := not_not.mp h
  have hz : capDistance f S p = 0 := capDistance_eq_of_nat (dist_zero_iff.mpr hp)
  have hsum : distancePhase f S = ∑ v ∈ Finset.univ.erase p, capDistance f S v := by
    unfold distancePhase
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ p), hz, add_zero]
  rw [hsum]
  calc
    _ ≤ ∑ _v ∈ Finset.univ.erase p, n := Finset.sum_le_sum (fun v _ => capDistance_le v)
    _ = n * (n - 1) := by simp [Nat.mul_comm]

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE DistancePhase

-- BEGIN COMPLETE MODULE RunBounds
section

namespace SchrijverSFM.Alg.Proof
open Classical
variable {n : ℕ} {f : Finset (Fin n) → ℝ} {S : ℕ → State n} {m : ℕ}

structure RunChoice (h : IsRun f S m) (j : Fin m) where
  target : Fin n
  source : Fin n
  index : ℕ
  step : StepVia f (S j.val) (S (j.val + 1)) target source index

noncomputable def runChoice (h : IsRun f S m) (j : Fin m) : RunChoice h j :=
  Classical.choice (by
    obtain ⟨t, s, i, hs⟩ := h.2 j.val j.isLt
    exact ⟨⟨t, s, i, hs⟩⟩)

theorem run_state_length (h : IsRun f S m) (j : Fin m) : (S j.val).length ≤ n := by
  cases hj : j.val with
  | zero =>
    obtain ⟨sigma, hs⟩ := h.1
    rw [hs]
    have hn := (runChoice h j).target.isLt
    simp only [initial, List.length_singleton]
    omega
  | succ k =>
    obtain ⟨t, s, i, hs⟩ := h.2 k (by omega)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlen, _⟩ := hs
    simpa [hj] using hlen

noncomputable def runCode (h : IsRun f S m) (j : Fin m) : ℕ :=
  distancePhase f (S j.val) * n^4 +
    (n^4 - 1 - stateKey f (S j.val) (runChoice h j).target (runChoice h j).source)

theorem run_code_lt (h : IsRun f S m) (j : Fin m) : runCode h j < n^6 := by
  have hc := (runChoice h j).step
  have hn : 0 < n := Nat.zero_lt_of_lt (runChoice h j).target.isLt
  have hp := distancePhase_bound hc.2.1
  have hphase : distancePhase f (S j.val) < n^2 := by
    have hsub : n - 1 + 1 = n := by omega
    nlinarith
  have hpow : 0 < n^4 := pow_pos hn _
  have htail : n^4 - 1 - stateKey f (S j.val) (runChoice h j).target (runChoice h j).source < n^4 := by omega
  have hh := append_digit_lt (d := 0) hphase htail
  simpa only [runCode, add_zero, ← pow_add] using hh

theorem run_code_succ (h : IsRun f S m) (j : ℕ) (hj : j + 1 < m) :
    runCode h ⟨j, by omega⟩ < runCode h ⟨j+1, hj⟩ := by
  let a : Fin m := ⟨j, by omega⟩
  let b : Fin m := ⟨j+1, hj⟩
  have hc := (runChoice h a).step
  have hc' := (runChoice h b).step
  have hd : ∀ v, dist f (S j) v ≤ dist f (S (j+1)) v := stepVia_dist_mono hc
  have hp := distancePhase_mono hd
  have hn : 0 < n := Nat.zero_lt_of_lt (runChoice h a).target.isLt
  have hpow : 0 < n^4 := pow_pos hn _
  by_cases he : distancePhase f (S j) = distancePhase f (S (j+1))
  · have hdeq : ∀ v, dist f (S (j+1)) v = dist f (S j) v :=
      fun v => (dist_eq_of_phase_eq hd he v).symm
    have hk := step_key_decrease hc hdeq hc'.2.2.1 hc'.2.2.2.1
    have hka := stateKey_lt (f := f) hc.1.1 (run_state_length h a) (runChoice h a).target (runChoice h a).source
    have hkb := stateKey_lt (f := f) hc'.1.1 (run_state_length h b) (runChoice h b).target (runChoice h b).source
    change distancePhase f (S j) * n^4 + (n^4-1-_) <
      distancePhase f (S (j+1)) * n^4 + (n^4-1-_)
    rw [he]
    change stateKey f (S (j+1)) (runChoice h b).target (runChoice h b).source <
      stateKey f (S j) (runChoice h a).target (runChoice h a).source at hk
    change stateKey f (S j) (runChoice h a).target (runChoice h a).source < n^4 at hka
    change stateKey f (S (j+1)) (runChoice h b).target (runChoice h b).source < n^4 at hkb
    dsimp only [a, b] at hk hka hkb ⊢
    omega
  · have hpl : distancePhase f (S j) < distancePhase f (S (j+1)) := by omega
    apply append_digit_lt hpl
    omega

theorem run_iterations_bound (h : IsRun f S m) : m ≤ n^6 := by
  have hindex : ∀ j (hj : j < m), j ≤ runCode h ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero => intro hj; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hh := ih (by omega)
      have ht := run_code_succ h j hj
      omega
  by_cases hm : m = 0
  · omega
  have hj : m-1 < m := by omega
  have hh := hindex (m-1) hj
  have ht := run_code_lt h ⟨m-1,hj⟩
  omega

end SchrijverSFM.Alg.Proof
end
-- END COMPLETE MODULE RunBounds

-- BEGIN COMPLETE MODULE SchrijverRoot
section

namespace SchrijverSFM.Alg

open NonmonotoneSubmod.Shared

theorem schrijver_algorithm {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (hf0 : f ∅ = 0) :
    (∀ S : State n, Valid S → caseOne f S → ∀ W : Finset (Fin n), f (caseOneSet f S) ≤ f W) ∧
    (∀ S : State n, Valid S → ¬ caseOne f S → ∃ S' : State n, Step f S S') ∧
    (∀ (S : ℕ → State n) (m : ℕ), IsRun f S m → m ≤ n ^ 6) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun S hS hc W => Proof.caseOne_minimizes hsub hf0 S hS hc W
  · exact fun S hS hc => Proof.progress hsub hf0 S hS hc
  · exact fun S m h => Proof.run_iterations_bound h
end SchrijverSFM.Alg

open SchrijverSFM.Alg NonmonotoneSubmod.Shared

theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (hf0 : f ∅ = 0) :
    (∀ S : State n, Valid S → caseOne f S → ∀ W : Finset (Fin n), f (caseOneSet f S) ≤ f W) ∧
    (∀ S : State n, Valid S → ¬ caseOne f S → ∃ S' : State n, Step f S S') ∧
    (∀ (S : ℕ → State n) (m : ℕ), IsRun f S m → m ≤ n ^ 6) :=
  SchrijverSFM.Alg.schrijver_algorithm f hsub hf0
end
-- END COMPLETE MODULE SchrijverRoot
