-- Prove2me | solution 1 for PrizeAlloc.Interval.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-23T13:43:12.538082+00:00
-- url     : https://prove2.me/submissions/88e54e8a-a435-4d16-bf55-3ef4e05adcad

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Setting

noncomputable section
open scoped BigOperators
namespace PrizeIntervalProof

noncomputable def pairTop {U : Type*} (φ : List U → ℝ → U → ℝ)
    (u v : U) (E : ℝ) : ℝ := φ [u, v] E u

def equalLevels (p : ℝ → ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ p (2 * t) = t}

def PairRegular (p : ℝ → ℝ) : Prop :=
  ContinuousOn p (Set.Ici 0) ∧
  MonotoneOn p (Set.Ici 0) ∧
  MonotoneOn (fun E => E - p E) (Set.Ici 0) ∧
  (∀ E, 0 ≤ E → 0 ≤ E - p E ∧ E - p E ≤ p E ∧ p E ≤ E) ∧
  (∀ E, 0 ≤ E → p E ∈ equalLevels p ∨ E - p E ∈ equalLevels p)

def PairCompatible {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (p : ℝ → ℝ) : Prop :=
  ∀ l E, PrizeAlloc.Interval.IsRanking l → 0 ≤ E →
    ∀ i ∈ l, ∀ j ∈ l, PrizeAlloc.Interval.pos l i < PrizeAlloc.Interval.pos l j →
      p (φ l E i + φ l E j) = φ l E i ∧
      (φ l E i + φ l E j) - p (φ l E i + φ l E j) = φ l E j

def Staircase {n : ℕ} (a : ℝ) (b : EReal) (v : Fin n → ℝ) : Prop :=
  (∀ i, a ≤ v i ∧ (v i : EReal) ≤ b) ∧
  ∀ i j, i < j → (v i : EReal) = b ∨ v j = a

def IntervalCases (n r : ℕ) (E a : ℝ) (b : EReal) (x : ℝ) : Prop :=
  ((((n * a : ℝ) : EReal) ≤ E ∧
      (E : EReal) ≤ (((n - r + 1 : ℕ) * a : ℝ) : EReal)
        + ((r - 1 : ℕ) : EReal) * b) → x = a) ∧
  (((((n - r + 1 : ℕ) * a : ℝ) : EReal)
        + ((r - 1 : ℕ) : EReal) * b ≤ E ∧
      (E : EReal) ≤ (((n - r : ℕ) * a : ℝ) : EReal)
        + (r : EReal) * b) →
      (x : EReal) = (E : EReal) - (((n - r : ℕ) * a : ℝ) : EReal)
        - ((r - 1 : ℕ) : EReal) * b) ∧
  (((((n - r : ℕ) * a : ℝ) : EReal) + (r : EReal) * b ≤ E ∧
      (E : EReal) ≤ (n : EReal) * b) → (x : EReal) = b)

end PrizeIntervalProof
end

noncomputable section
open scoped BigOperators
open PrizeAlloc.Interval
namespace PrizeIntervalProof
variable {U : Type*} [DecidableEq U]

theorem mem_sub (l : List U) (S : Finset U) (i : U) :
    i ∈ sub l S ↔ i ∈ l ∧ i ∈ S := by simp [sub]

theorem sub_ranking (l : List U) (hl : IsRanking l)
    (S : Finset U) (hS : S ⊆ l.toFinset) (hne : S.Nonempty) :
    IsRanking (sub l S) := by
  refine ⟨hl.1.filter _, ?_⟩
  obtain ⟨i, hi⟩ := hne
  have hm : i ∈ sub l S := (mem_sub l S i).2 ⟨List.mem_toFinset.mp (hS hi), hi⟩
  intro he
  simp [he] at hm

theorem pos_get (l : List U) (hl : l.Nodup) (i : Fin l.length) :
    pos l (l.get i) = i.val + 1 := by
  simp [pos, hl]

theorem pos_bounds (l : List U) (i : U) (hi : i ∈ l) :
    1 ≤ pos l i ∧ pos l i ≤ l.length := by
  have := List.idxOf_lt_length_iff.mpr hi
  dsimp [pos]
  omega

theorem sum_get (l : List U) (hl : l.Nodup) (f : U → ℝ) :
    (∑ i : Fin l.length, f (l.get i)) = ∑ i ∈ l.toFinset, f i := by
  classical
  simpa only [List.sum_ofFn, List.get_eq_getElem, List.sum_toFinset _ hl] using
    (show (List.ofFn (fun i : Fin l.length => f (l.get i))).sum = (l.map f).sum by
      exact congrArg List.sum (by simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map l f))

theorem sub_pos_lt_iff (l : List U) (hl : l.Nodup) (S : Finset U)
    (i j : U) (hi : i ∈ l) (hj : j ∈ l) (hiS : i ∈ S) (hjS : j ∈ S) :
    pos (sub l S) i < pos (sub l S) j ↔ pos l i < pos l j := by
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    by_cases hai : a = i
    · subst i
      by_cases haj : a = j
      · subst j; simp
      · have hjl : j ∈ l := (List.mem_cons.mp hj).resolve_left (Ne.symm haj)
        have hja : j ≠ a := Ne.symm haj
        simp [sub, hiS, pos, haj]
    · by_cases haj : a = j
      · subst j
        have hia : i ≠ a := Ne.symm hai
        simp [sub, hjS, pos, hai]
      · have hil : i ∈ l := (List.mem_cons.mp hi).resolve_left (Ne.symm hai)
        have hjl : j ∈ l := (List.mem_cons.mp hj).resolve_left (Ne.symm haj)
        have h := ih hl hil hjl
        by_cases has : a ∈ S
        · simpa [sub, has, pos, List.idxOf_cons, hai, haj] using h
        · simpa [sub, has, pos, List.idxOf_cons, hai, haj] using h

theorem pair_subranking (l : List U) (hl : l.Nodup) (i j : U)
    (hi : i ∈ l) (hj : j ∈ l) (hij : pos l i < pos l j) :
    sub l {i, j} = [i, j] := by
  have hne : i ≠ j := by intro h; subst j; omega
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    by_cases hai : a = i
    · subst a
      have hjl : j ∈ l := (List.mem_cons.mp hj).resolve_left (Ne.symm hne)
      have hfilter : sub l {i,j} = [j] := by
        have he : sub l {i,j} = sub l {j} := by
          apply List.filter_congr
          intro x hx
          have hxi : x ≠ i := by intro h; subst x; exact ha hx
          simp [hxi]
        rw [he]
        simpa [sub, List.count_eq_one_of_mem (List.nodup_cons.mp hl).2 hjl] using (List.filter_eq (l := l) j)
      simpa only [sub, List.filter_cons, Finset.mem_insert_self, decide_true, Bool.true_eq, if_true] using congrArg (List.cons i) hfilter
    · by_cases haj : a = j
      · subst a
        have hia := Ne.symm hai
        simp [pos, hai] at hij
      · have hil : i ∈ l := (List.mem_cons.mp hi).resolve_left (Ne.symm hai)
        have hjl : j ∈ l := (List.mem_cons.mp hj).resolve_left (Ne.symm haj)
        have hijl : pos l i < pos l j := by
          simpa [pos, List.idxOf_cons, hai, haj] using hij
        simpa [sub, hai, haj] using ih hl hil hjl hijl

omit [DecidableEq U] in
theorem prize_mono (φ : List U → ℝ → U → ℝ) (hm : EndowmentMonotone φ)
    (l : List U) (hl : IsRanking l) (E F : ℝ) (hE : 0 ≤ E) (hEF : E ≤ F)
    (i : U) (hi : i ∈ l) : φ l E i ≤ φ l F i := by
  rcases hEF.eq_or_lt with h | h
  · subst F; rfl
  · exact hm l E F hl hE h i hi

theorem prize_increment (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (hm : EndowmentMonotone φ) (l : List U) (hl : IsRanking l)
    (E F : ℝ) (hE : 0 ≤ E) (hEF : E ≤ F) (i : U) (hi : i ∈ l) :
    0 ≤ φ l F i - φ l E i ∧ φ l F i - φ l E i ≤ F - E := by
  have hnon : ∀ j ∈ l.toFinset, 0 ≤ φ l F j - φ l E j := fun j hj =>
    sub_nonneg.mpr (prize_mono φ hm l hl E F hE hEF j (List.mem_toFinset.mp hj))
  refine ⟨hnon i (List.mem_toFinset.mpr hi), ?_⟩
  have hs := Finset.single_le_sum hnon (List.mem_toFinset.mpr hi)
  rw [Finset.sum_sub_distrib, (hφ l F hl (hE.trans hEF)).2, (hφ l E hl hE).2] at hs
  exact hs

theorem endowment_continuous (φ : List U → ℝ → U → ℝ)
    (hφ : IsPrizeRule φ) (hm : EndowmentMonotone φ) : EndowmentContinuous φ := by
  intro l hl i hi
  apply LipschitzOnWith.continuousOn (K := 1)
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro E hE F hF
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  rcases le_total E F with h | h
  · obtain ⟨hn, hb⟩ := prize_increment φ hφ hm l hl E F hE h i hi
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · obtain ⟨hn, hb⟩ := prize_increment φ hφ hm l hl F E hF h i hi
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact hb

end PrizeIntervalProof
end

noncomputable section
open scoped BigOperators
open PrizeAlloc.Interval
namespace PrizeIntervalProof
variable {U : Type*} [DecidableEq U]

omit [DecidableEq U] in
theorem pair_ranking (u v : U) (h : u ≠ v) : IsRanking [u,v] := by
  simp [IsRanking, h]

theorem pair_budget (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (u v : U) (h : u ≠ v) (E : ℝ) (hE : 0 ≤ E) :
    φ [u,v] E u + φ [u,v] E v = E := by
  simpa [h] using (hφ [u,v] E (pair_ranking u v h) hE).2

theorem prize_zero (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (l : List U) (hl : IsRanking l) (i : U) (hi : i ∈ l) : φ l 0 i = 0 := by
  have hn := (hφ l 0 hl le_rfl).1 i hi
  have hs := Finset.single_le_sum (fun j hj => (hφ l 0 hl le_rfl).1 j
    (List.mem_toFinset.mp hj)) (List.mem_toFinset.mpr hi)
  rw [(hφ l 0 hl le_rfl).2] at hs
  linarith

theorem pair_restriction (φ : List U → ℝ → U → ℝ) (hc : Consistent φ)
    (l : List U) (hl : IsRanking l) (E : ℝ) (hE : 0 ≤ E)
    (u v : U) (hu : u ∈ l) (hv : v ∈ l) (huv : pos l u < pos l v) :
    φ [u,v] (φ l E u + φ l E v) u = φ l E u ∧
    φ [u,v] (φ l E u + φ l E v) v = φ l E v := by
  have hne : u ≠ v := by intro h; subst v; omega
  have hs : ({u,v} : Finset U) ⊆ l.toFinset := by
    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp_all
  have hsub := pair_subranking l hl.1 u v hu hv huv
  constructor
  · simpa [hsub, hne] using (hc l E hl hE {u,v} hs (by simp) u (by simp)).symm
  · simpa [hsub, hne] using (hc l E hl hE {u,v} hs (by simp) v (by simp)).symm

theorem pair_embed (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (ho : OrderPreserving φ) (hm : EndowmentMonotone φ) (hc : Consistent φ)
    (l : List U) (hl : IsRanking l) (u v : U) (hu : u ∈ l) (hv : v ∈ l)
    (hfirst : pos l u = 1) (huv : u ≠ v) (T : ℝ) (hT : 0 ≤ T) :
    ∃ E, 0 ≤ E ∧ φ l E u = φ [u,v] T u ∧ φ l E v = φ [u,v] T v := by
  have hn : 0 < l.length := List.length_pos_iff.mpr hl.2
  have hnR : 0 < (l.length : ℝ) := by exact_mod_cast hn
  have hpos : pos l u < pos l v := by
    have hvb := pos_bounds l v hv
    have hne : pos l u ≠ pos l v := by
      intro he
      have hi : l.idxOf u = l.idxOf v := by simpa [pos] using he
      have heq : u = v := by
        exact (List.idxOf_inj hu).mp hi
      exact huv heq
    omega
  have hbound : T ≤ φ l ((l.length : ℝ) * T) u := by
    have hs : ∑ j ∈ l.toFinset, φ l ((l.length : ℝ) * T) j ≤
        ∑ _j ∈ l.toFinset, φ l ((l.length : ℝ) * T) u := by
      apply Finset.sum_le_sum
      intro j hj
      have hjl := List.mem_toFinset.mp hj
      by_cases he : j = u
      · subst j; rfl
      · have hpo : pos l u < pos l j := by
          have hb := pos_bounds l j hjl
          have hi : l.idxOf j ≠ l.idxOf u := by
            intro hi
            exact he ((List.idxOf_inj hjl).mp hi)
          dsimp [pos] at *
          omega
        exact ho l _ hl (mul_nonneg hnR.le hT) u hu j hjl hpo
    rw [(hφ l _ hl (mul_nonneg hnR.le hT)).2] at hs
    have hs' : (l.length : ℝ) * T ≤ (l.length : ℝ) * φ l ((l.length : ℝ) * T) u := by
      simpa [List.toFinset_card_of_nodup hl.1] using hs
    exact le_of_mul_le_mul_left hs' hnR
  have hcont := (endowment_continuous φ hφ hm l hl u hu).add
    (endowment_continuous φ hφ hm l hl v hv)
  have hright : T ≤ φ l ((l.length : ℝ) * T) u + φ l ((l.length : ℝ) * T) v :=
    hbound.trans (le_add_of_nonneg_right ((hφ l _ hl (mul_nonneg hnR.le hT)).1 v hv))
  obtain ⟨E, hE, he⟩ := intermediate_value_Icc (mul_nonneg hnR.le hT)
    (hcont.mono (fun _ hx => hx.1))
    (show T ∈ Set.Icc (φ l 0 u + φ l 0 v)
      (φ l ((l.length : ℝ) * T) u + φ l ((l.length : ℝ) * T) v) from
      ⟨by simpa [prize_zero φ hφ l hl u hu, prize_zero φ hφ l hl v hv] using hT, hright⟩)
  have hr := pair_restriction φ hc l hl E hE.1 u v hu hv hpos
  change φ l E u + φ l E v = T at he
  rw [he] at hr
  exact ⟨E, hE.1, hr.1.symm, hr.2.symm⟩

omit [DecidableEq U] in
theorem same_pair_noncrossing (φ : List U → ℝ → U → ℝ)
    (hm : EndowmentMonotone φ) (u v : U) (huv : u ≠ v)
    (E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ¬ (φ [u,v] E u < φ [u,v] F u ∧ φ [u,v] F v < φ [u,v] E v) := by
  intro h
  rcases le_total E F with hef | hfe
  · have := prize_mono φ hm [u,v] (pair_ranking u v huv) E F hE hef v (by simp)
    linarith [h.2]
  · have := prize_mono φ hm [u,v] (pair_ranking u v huv) F E hF hfe u (by simp)
    linarith [h.1]

omit [DecidableEq U] in
theorem triple_ranking (a b c : U) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    IsRanking [a,b,c] := by simp [IsRanking, hab, hac, hbc]

theorem shared_winner_noncrossing (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (ho : OrderPreserving φ) (hm : EndowmentMonotone φ) (hc : Consistent φ)
    (a b d : U) (hab : a ≠ b) (had : a ≠ d)
    (E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ¬ (φ [a,b] E a < φ [a,d] F a ∧ φ [a,d] F d < φ [a,b] E b) := by
  by_cases hbd : b = d
  · subst d; exact same_pair_noncrossing φ hm a b hab E F hE hF
  intro h
  have hl := triple_ranking a d b had hab (Ne.symm hbd)
  obtain ⟨G,hG,hGa,hGb⟩ := pair_embed φ hφ ho hm hc [a,d,b] hl a b
    (by simp) (by simp) (by simp [pos]) hab E hE
  have hod := ho [a,d,b] G hl hG d (by simp) b (by simp)
    (by simp [pos, had, hab, Ne.symm hbd])
  have hr := pair_restriction φ hc [a,d,b] hl G hG a d (by simp) (by simp)
    (by simp [pos, had])
  have hn := (hφ [a,d,b] G hl hG).1
  apply same_pair_noncrossing φ hm a d had
    (φ [a,d,b] G a + φ [a,d,b] G d) F
    (add_nonneg (hn a (by simp)) (hn d (by simp))) hF
  rw [hr.1,hr.2]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem shared_loser_noncrossing (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (ho : OrderPreserving φ) (hm : EndowmentMonotone φ) (hc : Consistent φ)
    (a b c : U) (hab : a ≠ b) (hcb : c ≠ b)
    (E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ¬ (φ [a,b] E a < φ [c,b] F c ∧ φ [c,b] F b < φ [a,b] E b) := by
  by_cases hac : a = c
  · subst c; exact same_pair_noncrossing φ hm a b hab E F hE hF
  intro h
  have hl := triple_ranking a c b hac hab hcb
  obtain ⟨G,hG,hGa,hGb⟩ := pair_embed φ hφ ho hm hc [a,c,b] hl a b
    (by simp) (by simp) (by simp [pos]) hab E hE
  have hoc := ho [a,c,b] G hl hG a (by simp) c (by simp)
    (by simp [pos, hac])
  have hr := pair_restriction φ hc [a,c,b] hl G hG c b (by simp) (by simp)
    (by simp [pos, hac, hab, hcb])
  have hn := (hφ [a,c,b] G hl hG).1
  apply same_pair_noncrossing φ hm c b hcb
    (φ [a,c,b] G c + φ [a,c,b] G b) F
    (add_nonneg (hn c (by simp)) (hn b (by simp))) hF
  rw [hr.1,hr.2]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

omit [DecidableEq U] in
theorem third_competitor (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (u v : U) : ∃ e : U, e ≠ u ∧ e ≠ v := by
  obtain ⟨a,b,c,hab,hac,hbc⟩ := hU
  by_cases hau : a = u <;> by_cases hav : a = v
  · subst u; subst v; exact ⟨b, Ne.symm hab, Ne.symm hab⟩
  · subst u
    by_cases hbv : b = v
    · subst v; exact ⟨c, Ne.symm hac, Ne.symm hbc⟩
    · exact ⟨b, Ne.symm hab, hbv⟩
  · subst v
    by_cases hbu : b = u
    · subst u; exact ⟨c, Ne.symm hbc, Ne.symm hac⟩
    · exact ⟨b, hbu, Ne.symm hab⟩
  · exact ⟨a,hau,hav⟩

theorem reverse_noncrossing
    (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (ho : OrderPreserving φ) (hm : EndowmentMonotone φ) (hc : Consistent φ)
    (a b : U) (hab : a ≠ b) (E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ¬ (φ [a,b] E a < φ [b,a] F b ∧ φ [b,a] F a < φ [a,b] E b) := by
  intro h
  obtain ⟨e,hea,heb⟩ := third_competitor hU a b
  have hae := Ne.symm hea
  have hbe := Ne.symm heb
  have hl := triple_ranking a b e hab hae hbe
  have hr := triple_ranking a e b hae hab heb
  obtain ⟨L,hL,hLa,hLb⟩ := pair_embed φ hφ ho hm hc [a,b,e] hl a b
    (by simp) (by simp) (by simp [pos]) hab E hE
  obtain ⟨R,hR,hRa,hRb⟩ := pair_embed φ hφ ho hm hc [a,e,b] hr a b
    (by simp) (by simp) (by simp [pos]) hab E hE
  have hLe := ho [a,b,e] L hl hL b (by simp) e (by simp)
    (by simp [pos, hab, hae, hbe])
  have hRe := ho [a,e,b] R hr hR e (by simp) b (by simp)
    (by simp [pos, hae, hab, heb])
  have hpl := pair_restriction φ hc [a,b,e] hl L hL a e (by simp) (by simp)
    (by simp [pos, hae, hbe])
  have hpr := pair_restriction φ hc [a,e,b] hr R hR a e (by simp) (by simp)
    (by simp [pos, hae])
  have heq := pair_budget φ hφ a b hab E hE
  have hnL := (hφ [a,b,e] L hl hL).1
  have hnR := (hφ [a,e,b] R hr hR).1
  have hlow := prize_mono φ hm [a,e] (pair_ranking a e hae)
    (φ [a,b,e] L a + φ [a,b,e] L e) E
    (add_nonneg (hnL a (by simp)) (hnL e (by simp))) (by linarith) a (by simp)
  have hupp := prize_mono φ hm [a,e] (pair_ranking a e hae)
    E (φ [a,e,b] R a + φ [a,e,b] R e) hE (by linarith) a (by simp)
  rw [hpl.1] at hlow
  rw [hpr.1] at hupp
  have hx : φ [a,e] E a = φ [a,b] E a := by linarith
  have hy : φ [a,e] E e = φ [a,b] E b := by
    linarith [pair_budget φ hφ a e hae E hE]
  obtain ⟨G,hG,hGa,hGe⟩ := pair_embed φ hφ ho hm hc [a,b,e] hl a e
    (by simp) (by simp) (by simp [pos]) hae E hE
  have hob := ho [a,b,e] G hl hG a (by simp) b (by simp)
    (by simp [pos, hab])
  have hp := pair_restriction φ hc [a,b,e] hl G hG b e (by simp) (by simp)
    (by simp [pos, hab, hae, hbe])
  have hn := (hφ [a,b,e] G hl hG).1
  apply shared_winner_noncrossing φ hφ ho hm hc b e a hbe (Ne.symm hab)
    (φ [a,b,e] G b + φ [a,b,e] G e) F
    (add_nonneg (hn b (by simp)) (hn e (by simp))) hF
  rw [hp.1,hp.2]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem pair_noncrossing
    (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (ho : OrderPreserving φ) (hm : EndowmentMonotone φ) (hc : Consistent φ)
    (a b c d : U) (hab : a ≠ b) (hcd : c ≠ d)
    (E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ¬ (φ [a,b] E a < φ [c,d] F c ∧ φ [c,d] F d < φ [a,b] E b) := by
  by_cases hac : a = c
  · subst c; exact shared_winner_noncrossing φ hφ ho hm hc a b d hab hcd E F hE hF
  by_cases hbd : b = d
  · subst d; exact shared_loser_noncrossing φ hφ ho hm hc a b c hab hcd E F hE hF
  by_cases had : a = d
  · subst d
    by_cases hbc : b = c
    · subst c; exact reverse_noncrossing hU φ hφ ho hm hc a b hab E F hE hF
    intro h
    have hl := triple_ranking a c b hac hab (Ne.symm hbc)
    obtain ⟨G,hG,hGa,hGb⟩ := pair_embed φ hφ ho hm hc [a,c,b] hl a b
      (by simp) (by simp) (by simp [pos]) hab E hE
    have hoc := ho [a,c,b] G hl hG a (by simp) c (by simp)
      (by simp [pos, hac])
    have hp := pair_restriction φ hc [a,c,b] hl G hG c b (by simp) (by simp)
      (by simp [pos, hac, hab, Ne.symm hbc])
    have hn := (hφ [a,c,b] G hl hG).1
    apply shared_winner_noncrossing φ hφ ho hm hc c b a (Ne.symm hbc) hcd
      (φ [a,c,b] G c + φ [a,c,b] G b) F
      (add_nonneg (hn c (by simp)) (hn b (by simp))) hF
    rw [hp.1,hp.2]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  by_cases hbc : b = c
  · subst c
    intro h
    have hl := triple_ranking a d b had hab (Ne.symm hbd)
    obtain ⟨G,hG,hGa,hGb⟩ := pair_embed φ hφ ho hm hc [a,d,b] hl a b
      (by simp) (by simp) (by simp [pos]) hab E hE
    have hod := ho [a,d,b] G hl hG d (by simp) b (by simp)
      (by simp [pos, had, hab, Ne.symm hbd])
    have hp := pair_restriction φ hc [a,d,b] hl G hG a d (by simp) (by simp)
      (by simp [pos, had])
    have hn := (hφ [a,d,b] G hl hG).1
    apply shared_loser_noncrossing φ hφ ho hm hc a d b had hcd
      (φ [a,d,b] G a + φ [a,d,b] G d) F
      (add_nonneg (hn a (by simp)) (hn d (by simp))) hF
    rw [hp.1,hp.2]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  intro h
  have hl : IsRanking [a,c,d,b] := by
    simp [IsRanking, hac, had, hab, hcd, Ne.symm hbc, Ne.symm hbd]
  obtain ⟨G,hG,hGa,hGb⟩ := pair_embed φ hφ ho hm hc [a,c,d,b] hl a b
    (by simp) (by simp) (by simp [pos]) hab E hE
  have hoc := ho [a,c,d,b] G hl hG a (by simp) c (by simp)
    (by simp [pos, hac])
  have hod := ho [a,c,d,b] G hl hG d (by simp) b (by simp)
    (by simp [pos, had, hab, hcd, Ne.symm hbc, Ne.symm hbd])
  have hp := pair_restriction φ hc [a,c,d,b] hl G hG c d (by simp) (by simp)
    (by simp [pos, hac, had, hcd])
  have hn := (hφ [a,c,d,b] G hl hG).1
  apply same_pair_noncrossing φ hm c d hcd
    (φ [a,c,d,b] G c + φ [a,c,d,b] G d) F
    (add_nonneg (hn c (by simp)) (hn d (by simp))) hF
  rw [hp.1,hp.2]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem pair_anonymous
    (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (ho : OrderPreserving φ) (hm : EndowmentMonotone φ) (hc : Consistent φ)
    (u v a b : U) (huv : u ≠ v) (hab : a ≠ b) (E : ℝ) (hE : 0 ≤ E) :
    φ [u,v] E u = φ [a,b] E a ∧ φ [u,v] E v = φ [a,b] E b := by
  have h₁ := pair_budget φ hφ u v huv E hE
  have h₂ := pair_budget φ hφ a b hab E hE
  have hn₁ := pair_noncrossing hU φ hφ ho hm hc u v a b huv hab E E hE hE
  have hn₂ := pair_noncrossing hU φ hφ ho hm hc a b u v hab huv E E hE hE
  have he : φ [u,v] E u = φ [a,b] E a := by
    rcases lt_trichotomy (φ [u,v] E u) (φ [a,b] E a) with h | h | h
    · exact False.elim (hn₁ ⟨h,by linarith⟩)
    · exact h
    · exact False.elim (hn₂ ⟨h,by linarith⟩)
  exact ⟨he,by linarith⟩

end PrizeIntervalProof
end

noncomputable section
open scoped BigOperators
open PrizeAlloc.Interval
namespace PrizeIntervalProof

 theorem scalar_endpoint (p A B C : ℝ → ℝ)
    (hp : MonotoneOn p (Set.Ici 0))
    (hq : MonotoneOn (fun E => E - p E) (Set.Ici 0))
    (hA : MonotoneOn A (Set.Ici 0)) (hB : MonotoneOn B (Set.Ici 0))
    (hC : MonotoneOn C (Set.Ici 0))
    (htr : ∀ E, 0 ≤ E → 0 ≤ C E ∧ C E ≤ B E ∧ B E ≤ A E ∧ A E + B E + C E = E)
    (hpair : ∀ E, 0 ≤ E → p (A E + B E) = A E ∧ p (B E + C E) = B E ∧
      p (A E + C E) = A E)
    (T G : ℝ) (hT : 0 ≤ T) (hG : 0 ≤ G)
    (hx : A G = p T) (hy : C G = T - p T) :
    p T ∈ equalLevels p ∨ T - p T ∈ equalLevels p := by
  let x := p T
  let y := T - p T
  let t := B G
  have hg := htr G hG
  have hpg := hpair G hG
  have hxyz : 0 ≤ y ∧ y ≤ t ∧ t ≤ x ∧ x + t + y = G := by
    dsimp [x,y,t]; simpa only [hx,hy] using hg
  have hxy : x + y = T := by dsimp [x,y]; ring
  have hpTy : T - p T = y := rfl
  have hpT : p T = x := rfl
  have hab : p (x+t) = x := by simpa only [hx] using hpg.1
  have hbc : p (t+y) = t := by simpa only [hy] using hpg.2.1
  have hy0 := hxyz.1
  have ht0 : 0 ≤ t := by linarith [hxyz.2.1]
  have hx0 : 0 ≤ x := by linarith [hxyz.2.2.1]
  by_cases hyt : y = t
  · right
    change 0 ≤ y ∧ p (2*y) = y
    exact ⟨hy0,by simpa [hyt, two_mul] using hbc⟩
  by_cases htx : t = x
  · left
    change 0 ≤ x ∧ p (2*x) = x
    exact ⟨hx0,by simpa [htx, two_mul] using hab⟩
  have hyt' : y < t := lt_of_le_of_ne hxyz.2.1 hyt
  have htx' : t < x := lt_of_le_of_ne hxyz.2.2.1 htx
  have hlocal₁ : ∀ s, t+y ≤ s → s ≤ T → p s = s-y := by
    intro s hlow hupp
    have hs0 : 0 ≤ s := by linarith
    have h₁ := hq (show 0 ≤ t+y by positivity) hs0 hlow
    have h₂ := hq hs0 hT hupp
    dsimp only at h₁ h₂
    rw [hbc] at h₁
    rw [hpT] at h₂
    linarith
  have hlocal₂ : ∀ s, T ≤ s → s ≤ x+t → p s = x := by
    intro s hlow hupp
    have hs0 : 0 ≤ s := hT.trans hlow
    have h₁ := hp hT hs0 hlow
    have h₂ := hp hs0 (show 0 ≤ x+t by positivity) hupp
    rw [hpT] at h₁
    rw [hab] at h₂
    exact le_antisymm h₂ h₁
  have hthreshold₁ : ∀ s, 0 ≤ s → x ≤ p s → T ≤ s := by
    intro s hs hxs
    by_contra hnot
    have hsT : s < T := lt_of_not_ge hnot
    by_cases hst : s ≤ t+y
    · have hh := hp hs (show 0 ≤ t+y by positivity) hst
      rw [hbc] at hh
      linarith
    · have hh := hlocal₁ s (le_of_not_ge hst) hsT.le
      linarith
  have hthreshold₂ : ∀ s, 0 ≤ s → s-p s ≤ y → s ≤ T := by
    intro s hs hsy
    by_contra hnot
    have hTs : T < s := lt_of_not_ge hnot
    by_cases hst : x+t ≤ s
    · have hh := hq (show 0 ≤ x+t by positivity) hs hst
      dsimp only at hh
      rw [hab] at hh
      linarith
    · have hh := hlocal₂ s hTs.le (le_of_not_ge hst)
      linarith
  let L := x+2*y
  let H := 2*x+y
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hLG : L ≤ G := by dsimp [L]; linarith [hxyz.2.2.2]
  have hGH : G ≤ H := by dsimp [H]; linarith [hxyz.2.2.2]
  have hAL := hA hL hG hLG
  have hBL := hB hL hG hLG
  have hCL := hC hL hG hLG
  have hAH := hA hG hH hGH
  have hBH := hB hG hH hGH
  have hCH := hC hG hH hGH
  rw [hx] at hAL hAH
  rw [hy] at hCL hCH
  have htL := htr L hL
  have htH := htr H hH
  have hpL := hpair L hL
  have hpH := hpair H hH
  have hALx : A L = x := by
    have hloc := hlocal₂ (A L+B L) (by dsimp [L] at htL; linarith)
      (by change B L ≤ t at hBL; linarith)
    rw [hpL.1] at hloc
    exact hloc
  have hCHy : C H = y := by
    have hloc := hlocal₁ (B H+C H) (by change t ≤ B H at hBH; linarith)
      (by dsimp [H] at htH; linarith)
    rw [hpH.2.1] at hloc
    linarith
  have hLout : T ≤ A L+C L := hthreshold₁ _
    (by linarith [htL.1,htL.2.1,htL.2.2.1]) (by rw [hpL.2.2,hALx])
  have hHout : A H+C H ≤ T := hthreshold₂ _
    (by linarith [htH.1,htH.2.1,htH.2.2.1]) (by rw [hpH.2.2,hCHy]; linarith)
  have hCLy : C L = y := by linarith
  have hBLy : B L = y := by dsimp [L] at htL; linarith [htL.2.2.2]
  right
  change 0 ≤ y ∧ p (2*y) = y
  exact ⟨hy0, by simpa [hBLy,hCLy,two_mul] using hpL.2.1⟩

theorem exists_pair_model {U : Type*} [DecidableEq U]
    (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (ho : OrderPreserving φ) (hm : EndowmentMonotone φ) (hc : Consistent φ) :
    ∃ p : ℝ → ℝ, PairRegular p ∧ PairCompatible φ p := by
  obtain ⟨a,b,c,hab,hac,hbc⟩ := hU
  let p : ℝ → ℝ := fun E => φ [a,c] E a
  have hU' : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c := ⟨a,b,c,hab,hac,hbc⟩
  have hpair := pair_ranking a c hac
  have hq : ∀ E, 0 ≤ E → E-p E = φ [a,c] E c := by
    intro E hE
    have hh := pair_budget φ hφ a c hac E hE
    dsimp [p]
    linarith
  have hpm : MonotoneOn p (Set.Ici 0) := by
    intro E hE F _ hEF
    exact prize_mono φ hm [a,c] hpair E F hE hEF a (by simp)
  have hqm : MonotoneOn (fun E => E-p E) (Set.Ici 0) := by
    intro E hE F hF hEF
    change E-p E ≤ F-p F
    rw [hq E hE,hq F hF]
    exact prize_mono φ hm [a,c] hpair E F hE hEF c (by simp)
  have hcompat : PairCompatible φ p := by
    intro l E hl hE i hi j hj hij
    have hne : i ≠ j := by intro he; subst j; omega
    have hn := (hφ l E hl hE).1
    have hsum : 0 ≤ φ l E i + φ l E j := add_nonneg (hn i hi) (hn j hj)
    have hr := pair_restriction φ hc l hl E hE i j hi hj hij
    have ha := pair_anonymous hU' φ hφ ho hm hc i j a c hne hac _ hsum
    change p (φ l E i+φ l E j) = φ l E i ∧ _
    have he : p (φ l E i+φ l E j) = φ l E i := ha.1.symm.trans hr.1
    exact ⟨he,by rw [he]; ring⟩
  have htr := triple_ranking a b c hab hac hbc
  have hthree : ∀ E, 0 ≤ E →
      0 ≤ φ [a,b,c] E c ∧ φ [a,b,c] E c ≤ φ [a,b,c] E b ∧
      φ [a,b,c] E b ≤ φ [a,b,c] E a ∧
      φ [a,b,c] E a + φ [a,b,c] E b + φ [a,b,c] E c = E := by
    intro E hE
    refine ⟨(hφ _ _ htr hE).1 c (by simp), ?_, ?_, ?_⟩
    · exact ho _ _ htr hE b (by simp) c (by simp) (by simp [pos,hab,hac,hbc])
    · exact ho _ _ htr hE a (by simp) b (by simp) (by simp [pos,hab])
    · simpa [hab,hac,hbc,add_assoc] using (hφ _ _ htr hE).2
  have hthreepair : ∀ E, 0 ≤ E →
      p (φ [a,b,c] E a+φ [a,b,c] E b) = φ [a,b,c] E a ∧
      p (φ [a,b,c] E b+φ [a,b,c] E c) = φ [a,b,c] E b ∧
      p (φ [a,b,c] E a+φ [a,b,c] E c) = φ [a,b,c] E a := by
    intro E hE
    exact ⟨(hcompat _ _ htr hE a (by simp) b (by simp) (by simp [pos,hab])).1,
      (hcompat _ _ htr hE b (by simp) c (by simp) (by simp [pos,hab,hac,hbc])).1,
      (hcompat _ _ htr hE a (by simp) c (by simp) (by simp [pos,hac,hbc])).1⟩
  refine ⟨p, ⟨endowment_continuous φ hφ hm _ hpair a (by simp),hpm,hqm,?_,?_⟩,hcompat⟩
  · intro E hE
    rw [hq E hE]
    have hn := (hφ [a,c] E hpair hE).1
    have hord := ho [a,c] E hpair hE a (by simp) c (by simp) (by simp [pos,hac])
    have hbud := pair_budget φ hφ a c hac E hE
    dsimp [p]
    exact ⟨hn c (by simp),hord,by linarith [hn c (by simp)]⟩
  · intro T hT
    obtain ⟨G,hG,hGa,hGc⟩ := pair_embed φ hφ ho hm hc [a,b,c] htr a c
      (by simp) (by simp) (by simp [pos]) hac T hT
    apply scalar_endpoint p (fun E => φ [a,b,c] E a) (fun E => φ [a,b,c] E b)
      (fun E => φ [a,b,c] E c) hpm hqm
      (fun E hE F _ hEF => prize_mono φ hm _ htr E F hE hEF a (by simp))
      (fun E hE F _ hEF => prize_mono φ hm _ htr E F hE hEF b (by simp))
      (fun E hE F _ hEF => prize_mono φ hm _ htr E F hE hEF c (by simp))
      hthree hthreepair T G hT hG hGa
    rw [hq T hT]
    exact hGc

end PrizeIntervalProof
end

noncomputable section
open Set
namespace PrizeIntervalProof

theorem equalLevels_closed (p : ℝ → ℝ) (hp : PairRegular p) :
    IsClosed (equalLevels p) := by
  have hc : ContinuousOn (fun t : ℝ => p (2 * t) - t) (Ici 0) :=
    (hp.1.comp (continuous_const.mul continuous_id).continuousOn
      (by intro t ht; change 0 ≤ t at ht; change 0 ≤ 2 * t; positivity)).sub continuousOn_id
  have hh := hc.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_singleton (x := 0))
  convert hh using 1
  ext t
  simp only [equalLevels, mem_ofPred_eq, mem_inter_iff, mem_Ici, mem_preimage,
    mem_singleton_iff, sub_eq_zero]

theorem zero_mem_equalLevels (p : ℝ → ℝ) (hp : PairRegular p) :
    0 ∈ equalLevels p := by
  have h := hp.2.2.2.1 0 le_rfl
  simp only [equalLevels, mem_ofPred_eq, mul_zero]
  constructor
  · rfl
  · linarith [h.1, h.2.1, h.2.2]

def IsGap (Z : Set ℝ) (g : ℝ × EReal) : Prop :=
  g.1 ∈ Z ∧ (g.1 : EReal) < g.2 ∧
    (∀ t : ℝ, (t : EReal) = g.2 → t ∈ Z) ∧
    ∀ t : ℝ, g.1 < t → (t : EReal) < g.2 → t ∉ Z

theorem gap_exists (Z : Set ℝ) (hZ : IsClosed Z) (hzero : 0 ∈ Z)
    (r : ℝ) (hr : 0 ≤ r) (hrZ : r ∉ Z) :
    ∃ g : ℝ × EReal, IsGap Z g ∧ g.1 < r ∧ (r : EReal) < g.2 := by
  let L := Z ∩ Iic r
  have hLne : L.Nonempty := ⟨0, hzero, hr⟩
  have hLbdd : BddAbove L := ⟨r, fun _ h => h.2⟩
  have ha : sSup L ∈ L := (hZ.inter isClosed_Iic).csSup_mem hLne hLbdd
  have har : sSup L < r := lt_of_le_of_ne ha.2 (fun h => hrZ (h ▸ ha.1))
  by_cases hR : (Z ∩ Ici r).Nonempty
  · have hRbdd : BddBelow (Z ∩ Ici r) := ⟨r, fun _ h => h.2⟩
    have hb : sInf (Z ∩ Ici r) ∈ Z ∩ Ici r :=
      (hZ.inter isClosed_Ici).csInf_mem hR hRbdd
    have hrb : r < sInf (Z ∩ Ici r) :=
      lt_of_le_of_ne hb.2 (fun h => hrZ (h.symm ▸ hb.1))
    refine ⟨(sSup L, (sInf (Z ∩ Ici r) : ℝ)), ?_, har, ?_⟩
    · refine ⟨ha.1, ?_, ?_, ?_⟩
      · exact EReal.coe_lt_coe (har.trans hrb)
      · intro t ht
        have ht' := EReal.coe_injective ht
        simpa only [ht'] using hb.1
      · intro t hat htb htZ
        have htb' : t < sInf (Z ∩ Ici r) := EReal.coe_lt_coe_iff.mp htb
        by_cases htr : t ≤ r
        · exact (not_lt_of_ge (le_csSup hLbdd (show t ∈ L from ⟨htZ, htr⟩))) hat
        · exact (not_lt_of_ge (csInf_le hRbdd ⟨htZ, le_of_not_ge htr⟩)) htb'
    · exact EReal.coe_lt_coe hrb
  · refine ⟨(sSup L, ⊤), ?_, har, EReal.coe_lt_top _⟩
    refine ⟨ha.1, EReal.coe_lt_top _, ?_, ?_⟩
    · intro t ht
      exact False.elim (EReal.coe_ne_top t ht)
    · intro t hat _ htZ
      by_cases htr : t ≤ r
      · exact (not_lt_of_ge (le_csSup hLbdd (show t ∈ L from ⟨htZ, htr⟩))) hat
      · exact hR ⟨t, htZ, le_of_not_ge htr⟩

theorem gap_upper_unique (Z : Set ℝ) (g h : ℝ × EReal)
    (hg : IsGap Z g) (hh : IsGap Z h) (ha : g.1 = h.1) : g.2 = h.2 := by
  have step : ∀ u v : ℝ × EReal, IsGap Z u → IsGap Z v →
      u.1 = v.1 → ¬ u.2 < v.2 := by
    intro u v hu hv huv huv'
    have hnt : u.2 ≠ ⊤ := by intro he; simp [he] at huv'
    have hnb : u.2 ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe u.1).trans hu.2.1)
    have he := EReal.coe_toReal hnt hnb
    have hrZ := hu.2.2.1 u.2.toReal he
    have hlu : u.1 < u.2.toReal := by
      apply EReal.coe_lt_coe_iff.mp
      simpa only [he] using hu.2.1
    exact hv.2.2.2 _ (huv ▸ hlu) (by simpa only [he] using huv') hrZ
  exact le_antisymm (le_of_not_gt (step h g hh hg ha.symm))
    (le_of_not_gt (step g h hg hh ha))

theorem gap_disjoint (Z : Set ℝ) (g h : ℝ × EReal)
    (hg : IsGap Z g) (hh : IsGap Z h) (hne : g ≠ h) :
    Disjoint (Ioo (g.1 : EReal) g.2) (Ioo (h.1 : EReal) h.2) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have ha : g.1 = h.1 := by
    apply le_antisymm
    · by_contra hn
      have hlt : h.1 < g.1 := lt_of_not_ge hn
      exact hh.2.2.2 _ hlt (hx.1.trans hy.2) hg.1
    · by_contra hn
      have hlt : g.1 < h.1 := lt_of_not_ge hn
      exact hg.2.2.2 _ hlt (hy.1.trans hx.2) hh.1
  exact hne (Prod.ext ha (gap_upper_unique Z g h hg hh ha))

theorem gap_rational (Z : Set ℝ) (g : ℝ × EReal) (hg : IsGap Z g) :
    ∃ q : ℚ, g.1 < (q : ℝ) ∧ ((q : ℝ) : EReal) < g.2 := by
  rcases g with ⟨a, b⟩
  cases b using EReal.rec with
  | bot => exact False.elim (not_lt_bot hg.2.1)
  | coe b =>
    obtain ⟨q, hq, hq'⟩ := exists_rat_btwn (EReal.coe_lt_coe_iff.mp hg.2.1)
    exact ⟨q, hq, EReal.coe_lt_coe hq'⟩
  | top =>
    obtain ⟨q, hq⟩ := exists_rat_gt a
    exact ⟨q, hq, EReal.coe_lt_top _⟩

theorem exists_gap_family (Z : Set ℝ) (hZ : IsClosed Z)
    (hzero : 0 ∈ Z) (hnonneg : Z ⊆ Set.Ici 0) :
    ∃ a : ℕ → ℝ, ∃ b : ℕ → EReal,
      (∀ k, 0 ≤ a k ∧ (a k : EReal) ≤ b k) ∧
      Pairwise (fun k l => Disjoint (Set.Ioo (a k : EReal) (b k))
        (Set.Ioo (a l : EReal) (b l))) ∧
      (∀ k, a k ∈ Z ∧
        (∀ t : ℝ, (t : EReal) = b k → t ∈ Z) ∧
        (∀ t : ℝ, a k < t → (t : EReal) < b k → t ∉ Z)) ∧
      (∀ t : ℝ, 0 ≤ t → t ∉ Z →
        ∃ k, a k < t ∧ (t : EReal) < b k) := by
  classical
  let G := {g : ℝ × EReal // IsGap Z g}
  let q : G → ℚ := fun g => Classical.choose (gap_rational Z g.1 g.2)
  have hq (g : G) : g.1.1 < (q g : ℝ) ∧ ((q g : ℝ) : EReal) < g.1.2 :=
    Classical.choose_spec (gap_rational Z g.1 g.2)
  have hqi : Function.Injective q := by
    intro g h he
    by_contra hne
    have hv : g.1 ≠ h.1 := fun hv => hne (Subtype.ext hv)
    have hd := gap_disjoint Z g.1 h.1 g.2 h.2 hv
    apply (Set.disjoint_left.mp hd) (a := ((q g : ℝ) : EReal))
    · exact ⟨EReal.coe_lt_coe (hq g).1, (hq g).2⟩
    · simpa only [he] using
        (show ((q h : ℝ) : EReal) ∈ Ioo (h.1.1 : EReal) h.1.2 from
          ⟨EReal.coe_lt_coe (hq h).1, (hq h).2⟩)
  let : Encodable G := Encodable.ofInj q hqi
  let a : ℕ → ℝ := fun k => match Encodable.decode₂ G k with
    | none => 0
    | some g => g.1.1
  let b : ℕ → EReal := fun k => match Encodable.decode₂ G k with
    | none => 0
    | some g => g.1.2
  have hab (k : ℕ) : 0 ≤ a k ∧ (a k : EReal) ≤ b k := by
    cases he : Encodable.decode₂ G k with
    | none => simp [a, b, he]
    | some g =>
      simpa only [a, b, he] using ⟨hnonneg g.2.1, g.2.2.1.le⟩
  refine ⟨a, b, hab, ?_, ?_, ?_⟩
  · intro k l hkl
    cases hk : Encodable.decode₂ G k with
    | none => simp [a, b, hk]
    | some g =>
      cases hl : Encodable.decode₂ G l with
      | none => simp [a, b, hl]
      | some h =>
        have hgh : g.1 ≠ h.1 := by
          intro he
          have he' : g = h := Subtype.ext he
          have hk' := Encodable.decode₂_eq_some.mp hk
          have hl' := Encodable.decode₂_eq_some.mp hl
          exact hkl (hk'.symm.trans (he' ▸ hl'))
        simpa only [a, b, hk, hl] using gap_disjoint Z g.1 h.1 g.2 h.2 hgh
  · intro k
    cases hk : Encodable.decode₂ G k with
    | none =>
      simp only [a, b, hk]
      refine ⟨hzero, ?_, ?_⟩
      · intro t ht
        have ht' : t = 0 := EReal.coe_injective (by simpa using ht)
        simpa only [ht'] using hzero
      · intro t ht ht'
        have htn : t < 0 := EReal.coe_lt_coe_iff.mp (by simpa using ht')
        exact False.elim (ht.not_gt htn)
    | some g =>
      simpa only [a, b, hk] using ⟨g.2.1, g.2.2.2.1, g.2.2.2.2⟩
  · intro t ht htZ
    obtain ⟨g, hg, hga, hgb⟩ := gap_exists Z hZ hzero t ht htZ
    let g' : G := ⟨g, hg⟩
    refine ⟨Encodable.encode g', ?_⟩
    simpa only [a, b, Encodable.decode₂_encode] using ⟨hga, hgb⟩

end PrizeIntervalProof
end

noncomputable section
open scoped BigOperators
namespace PrizeIntervalProof

lemma sum_before {n : ℕ} (i : Fin n) (a b : ℝ) :
    (∑ j : Fin n, if j < i then b else a) =
      (i.val : ℝ) * b + ((n - i.val : ℕ) : ℝ) * a := by
  classical
  rw [Finset.sum_ite]
  have h₁ : Finset.univ.filter (fun j : Fin n => j < i) = Finset.Iio i := by
    ext j
    simp
  have h₂ : Finset.univ.filter (fun j : Fin n => ¬j < i) = Finset.Ici i := by
    ext j
    simp
  rw [h₁, h₂]
  simp

lemma staircase_order {n : ℕ} (a : ℝ) (b : EReal) (v : Fin n → ℝ)
    (hv : Staircase a b v) {i j : Fin n} (hij : i < j) : v j ≤ v i := by
  rcases hv.2 i j hij with h | h
  · exact EReal.coe_le_coe_iff.mp (by simpa only [h] using (hv.1 j).2)
  · simpa only [h] using (hv.1 i).1

theorem staircase_finite_formula (n : ℕ) (a b E : ℝ)
    (hab : a ≤ b) (v : Fin n → ℝ)
    (hv : Staircase a (b : EReal) v) (hsum : ∑ i, v i = E)
    (i : Fin n) :
    v i = a + min (b - a)
      (max 0 (E - (n : ℝ) * a - (i.val : ℝ) * (b - a))) := by
  classical
  have hb (j : Fin n) : v j ≤ b := EReal.coe_le_coe_iff.mp (hv.1 j).2
  have hc : ((n - i.val : ℕ) : ℝ) = (n : ℝ) - i.val :=
    Nat.cast_sub i.isLt.le
  by_cases he : a = b
  · have heq (j : Fin n) : v j = a := le_antisymm (by simpa only [he] using hb j) (hv.1 j).1
    simp only [heq i, he, sub_self]
    rw [min_eq_left (le_max_left _ _), add_zero]
  have hab' : a < b := lt_of_le_of_ne hab he
  by_cases hia : v i = a
  · have hj (j : Fin n) : v j ≤ if j < i then b else a := by
      split_ifs with hji
      · exact hb j
      · exact (le_or_gt j i).elim
          (fun hle => by have hEq : j = i := le_antisymm hle (le_of_not_gt hji); simpa only [hEq, hia] using (le_refl a))
          (fun hij => by
            rcases hv.2 i j hij with h | h
            · have hab'' : a = b := by simpa only [hia, EReal.coe_eq_coe_iff] using h
              exact False.elim (he hab'')
            · exact h.le)
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
    rw [hsum, sum_before, hc] at hs
    have hr : E - (n : ℝ) * a - (i.val : ℝ) * (b - a) ≤ 0 := by nlinarith
    rw [hia, max_eq_left hr, min_eq_right (sub_nonneg.mpr hab), add_zero]
  by_cases hib : v i = b
  · have hj (j : Fin n) :
        (if j < i then b else a) + (if j = i then b - a else 0) ≤ v j := by
      by_cases hji : j < i
      · have hne : j ≠ i := ne_of_lt hji
        simp only [hji, if_true, hne, if_false, add_zero]
        rcases hv.2 j i hji with h | h
        · exact (EReal.coe_injective h).ge
        · exact False.elim (he (h.symm.trans hib))
      · by_cases hEq : j = i
        · simp [hEq, hib]
        · simp only [hji, if_false, hEq, add_zero]
          exact (hv.1 j).1
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
    simp only [Finset.sum_add_distrib, sum_before, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hsum, hc] at hs
    have hr : b - a ≤ E - (n : ℝ) * a - (i.val : ℝ) * (b - a) := by nlinarith
    rw [hib, max_eq_right ((sub_nonneg.mpr hab).trans hr), min_eq_left hr]
    ring
  · have hj (j : Fin n) : v j =
        (if j < i then b else a) + (if j = i then v i - a else 0) := by
      by_cases hji : j < i
      · have hne : j ≠ i := ne_of_lt hji
        simp only [hji, if_true, hne, if_false, add_zero]
        rcases hv.2 j i hji with h | h
        · exact EReal.coe_injective h
        · exact False.elim (hia h)
      · by_cases hEq : j = i
        · simp [hEq]
        · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji) (Ne.symm hEq)
          rcases hv.2 i j hij with h | h
          · exact False.elim (hib (EReal.coe_injective h))
          · simp only [hji, if_false, hEq, add_zero, h]
    have hs := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hj j)
    simp only [Finset.sum_add_distrib, sum_before, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hsum, hc] at hs
    have hr : E - (n : ℝ) * a - (i.val : ℝ) * (b - a) = v i - a := by nlinarith
    rw [hr, max_eq_right (sub_nonneg.mpr (hv.1 i).1),
      min_eq_right (sub_le_sub_right (hb i) a)]
    ring

theorem staircase_top_formula (n : ℕ) (a E : ℝ) (v : Fin n → ℝ)
    (hv : Staircase a ⊤ v) (hsum : ∑ i, v i = E) (i : Fin n) :
    v i = if i.val = 0 then E - ((n - 1 : ℕ) : ℝ) * a else a := by
  classical
  have hn : 0 < n := (Nat.zero_le i.val).trans_lt i.isLt
  let z : Fin n := ⟨0, hn⟩
  have hj (j : Fin n) (hj : j.val ≠ 0) : v j = a := by
    have hzj : z < j := Nat.pos_of_ne_zero hj
    rcases hv.2 z j hzj with h | h
    · exact False.elim (EReal.coe_ne_top _ h)
    · exact h
  split_ifs with hi
  · have hvec (j : Fin n) : v j = (if j = i then v i - a else 0) + a := by
      by_cases he : j = i
      · simp [he]
      · have hj0 : j.val ≠ 0 := by intro hz; apply he; exact Fin.ext (hz.trans hi.symm)
        simp [he, hj j hj0]
    have hs := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hvec j)
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Fin.sum_const, nsmul_eq_mul, hsum] at hs
    rw [Nat.cast_sub hn, Nat.cast_one]
    nlinarith
  · exact hj i hi

lemma finite_clamp_staircase (n : ℕ) (a b E : ℝ) (hab : a ≤ b) :
    Staircase a (b : EReal) (fun i : Fin n =>
      a + min (b - a) (max 0 (E - (n : ℝ) * a - (i.val : ℝ) * (b - a)))) := by
  have hw : 0 ≤ b - a := sub_nonneg.mpr hab
  constructor
  · intro i
    constructor
    · exact le_add_of_nonneg_right (le_min hw (le_max_left _ _))
    · apply EReal.coe_le_coe
      linarith [min_le_left (b - a) (max 0 (E - (n : ℝ) * a - (i.val : ℝ) * (b - a)))]
  · intro i j hij
    by_cases hri : b - a ≤ E - (n : ℝ) * a - (i.val : ℝ) * (b - a)
    · left
      have he : a + min (b - a) (max 0 (E - (n : ℝ) * a - (i.val : ℝ) * (b - a))) = b := by
        rw [max_eq_right (hw.trans hri), min_eq_left hri]
        ring
      exact congrArg (fun x : ℝ => (x : EReal)) he
    · right
      have hij' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (show i.val + 1 ≤ j.val from hij)
      have hm := mul_le_mul_of_nonneg_right hij' hw
      have hrj : E - (n : ℝ) * a - (j.val : ℝ) * (b - a) ≤ 0 := by nlinarith
      change a + min (b - a) (max 0 (E - n * a - j.val * (b - a))) = a
      rw [max_eq_left hrj, min_eq_right hw, add_zero]

lemma intervalCases_finite (n : ℕ) (i : Fin n) (E a b x : ℝ) :
    IntervalCases n (i.val + 1) E a (b : EReal) x ↔
    ((n * a ≤ E ∧ E ≤ n * a + i.val * (b - a)) → x = a) ∧
    ((n * a + i.val * (b - a) ≤ E ∧
      E ≤ n * a + i.val * (b - a) + (b - a)) →
      x = a + (E - n * a - i.val * (b - a))) ∧
    ((n * a + i.val * (b - a) + (b - a) ≤ E ∧ E ≤ n * b) → x = b) := by
  have hn : n - (i.val + 1) + 1 = n - i.val := by omega
  have hL : ((n - i.val : ℕ) : ℝ) * a + (i.val : ℝ) * b =
      n * a + i.val * (b - a) := by rw [Nat.cast_sub i.isLt.le]; ring
  have hU : ((n - (i.val + 1) : ℕ) : ℝ) * a + ((i.val + 1 : ℕ) : ℝ) * b =
      n * a + i.val * (b - a) + (b - a) := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt i.isLt)]
    push_cast
    ring
  have hM : E - ((n - (i.val + 1) : ℕ) : ℝ) * a - (i.val : ℝ) * b =
      a + (E - n * a - i.val * (b - a)) := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt i.isLt)]
    push_cast
    ring
  simp only [IntervalCases, hn, Nat.add_sub_cancel, ← EReal.coe_natCast,
    ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub,
    EReal.coe_le_coe_iff, EReal.coe_eq_coe_iff, hL, hU, hM]

lemma intervalCases_finite_iff_clamp (n : ℕ) (i : Fin n) (E a b x : ℝ)
    (hab : a ≤ b) (hE : n * a ≤ E ∧ E ≤ n * b) :
    IntervalCases n (i.val + 1) E a (b : EReal) x ↔
      x = a + min (b - a) (max 0 (E - n * a - i.val * (b - a))) := by
  rw [intervalCases_finite]
  have hw : 0 ≤ b - a := sub_nonneg.mpr hab
  constructor
  · intro h
    by_cases hL : E ≤ n * a + i.val * (b - a)
    · have hr : E - n * a - i.val * (b - a) ≤ 0 := by linarith
      rw [h.1 ⟨hE.1, hL⟩, max_eq_left hr, min_eq_right hw, add_zero]
    · by_cases hU : E ≤ n * a + i.val * (b - a) + (b - a)
      · have hr₀ : 0 ≤ E - n * a - i.val * (b - a) := by linarith
        have hr₁ : E - n * a - i.val * (b - a) ≤ b - a := by linarith
        rw [h.2.1 ⟨le_of_not_ge hL, hU⟩,
          max_eq_right hr₀, min_eq_right hr₁]
      · have hr : b - a ≤ E - n * a - i.val * (b - a) := by linarith
        rw [h.2.2 ⟨le_of_not_ge hU, hE.2⟩,
          max_eq_right (hw.trans hr), min_eq_left hr]
        ring
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hr : E - n * a - i.val * (b - a) ≤ 0 := by linarith [h.2]
      rw [max_eq_left hr, min_eq_right hw, add_zero]
    · intro h
      have hr₀ : 0 ≤ E - n * a - i.val * (b - a) := by linarith [h.1]
      have hr₁ : E - n * a - i.val * (b - a) ≤ b - a := by linarith [h.2]
      rw [max_eq_right hr₀, min_eq_right hr₁]
    · intro h
      have hr : b - a ≤ E - n * a - i.val * (b - a) := by linarith [h.1]
      rw [max_eq_right (hw.trans hr), min_eq_left hr]
      ring

lemma intervalCases_top (n : ℕ) (i : Fin n) (E a x : ℝ)
    (hE : n * a ≤ E) :
    IntervalCases n (i.val + 1) E a ⊤ x ↔
      x = if i.val = 0 then E - ((n - 1 : ℕ) : ℝ) * a else a := by
  have hn : 0 < n := (Nat.zero_le i.val).trans_lt i.isLt
  have hnt : (n : EReal) * ⊤ = ⊤ := EReal.mul_top_of_pos (by exact_mod_cast hn)
  by_cases hi : i.val = 0
  · simp only [IntervalCases, hi, zero_add, Nat.sub_self, Nat.cast_zero,
      Nat.cast_one, zero_mul, add_zero, one_mul, EReal.coe_add_top,
      hnt, le_top, and_true, EReal.coe_le_coe_iff, EReal.coe_eq_coe_iff,
      sub_zero, ← EReal.coe_sub, if_true]
    constructor
    · intro h
      exact h.2.1 (by simpa only [Nat.sub_add_cancel hn] using hE)
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · intro h'
        have he : E = n * a := le_antisymm (by simpa only [Nat.sub_add_cancel hn] using h'.2) h'.1
        rw [h, he, Nat.cast_sub hn, Nat.cast_one]
        ring
      · intro _
        exact h
      · intro h'
        exact False.elim ((EReal.coe_lt_top E).not_ge h')
  · have hit : ((i.val : ℕ) : EReal) * ⊤ = ⊤ :=
      EReal.mul_top_of_pos (by exact_mod_cast (Nat.pos_of_ne_zero hi))
    have hist : ((i.val + 1 : ℕ) : EReal) * ⊤ = ⊤ :=
      EReal.mul_top_of_pos (by exact_mod_cast (Nat.zero_lt_succ i.val))
    simp only [IntervalCases, Nat.add_sub_cancel, hit, hist, EReal.coe_add_top,
      hnt, le_top, and_true, EReal.coe_le_coe_iff, if_neg hi]
    constructor
    · intro h
      exact h.1 hE
    · intro h
      refine ⟨fun _ => h, ?_, ?_⟩
      · intro h'
        exact False.elim ((EReal.coe_lt_top E).not_ge h')
      · intro h'
        exact False.elim ((EReal.coe_lt_top E).not_ge h')

theorem staircase_iff_cases (n : ℕ) (hn : 0 < n) (a E : ℝ) (b : EReal)
    (ha : 0 ≤ a) (hab : (a : EReal) ≤ b)
    (hE : (((n : ℝ) * a : ℝ) : EReal) ≤ E ∧ (E : EReal) ≤ (n : EReal) * b)
    (v : Fin n → ℝ) (hsum : ∑ i, v i = E) :
    Staircase a b v ↔ ∀ i, IntervalCases n (i.val + 1) E a b (v i) := by
  cases b using EReal.rec with
  | bot => exact False.elim ((EReal.bot_lt_coe 0).not_ge ((EReal.coe_le_coe ha).trans hab))
  | coe b =>
    have hab' := EReal.coe_le_coe_iff.mp hab
    have hE' : n * a ≤ E ∧ E ≤ n * b := by
      simpa only [← EReal.coe_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff] using hE
    simp_rw [intervalCases_finite_iff_clamp n _ E a b _ hab' hE']
    constructor
    · intro hv i
      exact staircase_finite_formula n a b E hab' v hv hsum i
    · intro h
      have he : v = fun i : Fin n =>
          a + min (b - a) (max 0 (E - n * a - i.val * (b - a))) := funext h
      rw [he]
      exact finite_clamp_staircase n a b E hab'
  | top =>
    have hE' := EReal.coe_le_coe_iff.mp hE.1
    simp_rw [intervalCases_top n _ E a _ hE']
    constructor
    · intro hv i
      exact staircase_top_formula n a E v hv hsum i
    · intro h
      refine ⟨?_, ?_⟩
      · intro i
        refine ⟨?_, le_top⟩
        rw [h i]
        split_ifs
        · rw [Nat.cast_sub hn, Nat.cast_one]
          nlinarith
        · rfl
      · intro i j hij
        right
        have hj : j.val ≠ 0 := by have := i.isLt; exact Nat.ne_of_gt ((Nat.zero_le i.val).trans_lt hij)
        rw [h j, if_neg hj]

theorem staircase_unique (n : ℕ) (a : ℝ) (b : EReal)
    (hab : (a : EReal) ≤ b) (v w : Fin n → ℝ)
    (hv : Staircase a b v) (hw : Staircase a b w)
    (hsum : ∑ i, v i = ∑ i, w i) : v = w := by
  cases b using EReal.rec with
  | bot => exact False.elim ((EReal.bot_lt_coe a).not_ge hab)
  | coe b =>
    have hab' := EReal.coe_le_coe_iff.mp hab
    funext i
    rw [staircase_finite_formula n a b _ hab' v hv rfl i,
      staircase_finite_formula n a b _ hab' w hw rfl i, hsum]
  | top =>
    funext i
    rw [staircase_top_formula n a _ v hv rfl i,
      staircase_top_formula n a _ w hw rfl i, hsum]

theorem staircase_monotone (n : ℕ) (a : ℝ) (b : EReal)
    (hab : (a : EReal) ≤ b) (v w : Fin n → ℝ)
    (hv : Staircase a b v) (hw : Staircase a b w)
    (hsum : ∑ i, v i ≤ ∑ i, w i) : ∀ i, v i ≤ w i := by
  cases b using EReal.rec with
  | bot => exact False.elim ((EReal.bot_lt_coe a).not_ge hab)
  | coe b =>
    have hab' := EReal.coe_le_coe_iff.mp hab
    intro i
    rw [staircase_finite_formula n a b _ hab' v hv rfl i,
      staircase_finite_formula n a b _ hab' w hw rfl i]
    gcongr
  | top =>
    intro i
    rw [staircase_top_formula n a _ v hv rfl i,
      staircase_top_formula n a _ w hw rfl i]
    split_ifs
    · linarith
    · rfl

theorem staircase_restrict (n m : ℕ) (a : ℝ) (b : EReal)
    (v : Fin n → ℝ) (hv : Staircase a b v)
    (e : Fin m → Fin n) (he : StrictMono e) :
    Staircase a b (fun i => v (e i)) :=
  ⟨fun i => hv.1 (e i), fun i j hij => hv.2 (e i) (e j) (he hij)⟩

end PrizeIntervalProof
end

noncomputable section
open scoped BigOperators
open PrizeAlloc.Interval
namespace PrizeIntervalProof

lemma scaled_mem_iff (n : ℕ) (hn : 0 < n) (a E : ℝ) (b : EReal) :
    ((((n : ℝ) * a : ℝ) : EReal) ≤ E ∧ (E : EReal) ≤ (n : EReal) * b) ↔
      a ≤ E / n ∧ ((E / n : ℝ) : EReal) ≤ b := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnE : 0 < (n : EReal) := by exact_mod_cast hn
  cases b using EReal.rec with
  | bot => simp [EReal.mul_bot_of_pos hnE]
  | coe b =>
    simp only [← EReal.coe_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff,
      le_div_iff₀ hnR, div_le_iff₀ hnR]
    ring_nf
  | top =>
    simp only [EReal.mul_top_of_pos hnE, le_top, and_true,
      EReal.coe_le_coe_iff, le_div_iff₀ hnR]
    rw [mul_comm]

lemma interval_threshold_bounds (n : ℕ) (i : Fin n) (a : ℝ) (b : EReal)
    (hab : (a : EReal) ≤ b) :
    (((n * a : ℝ) : EReal) ≤
      (((n - (i.val + 1) + 1 : ℕ) * a : ℝ) : EReal) + ((i.val + 1 - 1 : ℕ) : EReal) * b) ∧
    ((((n - (i.val + 1) + 1 : ℕ) * a : ℝ) : EReal) + ((i.val + 1 - 1 : ℕ) : EReal) * b ≤
      (((n - (i.val + 1) : ℕ) * a : ℝ) : EReal) + ((i.val + 1 : ℕ) : EReal) * b) ∧
    ((((n - (i.val + 1) : ℕ) * a : ℝ) : EReal) + ((i.val + 1 : ℕ) : EReal) * b ≤ (n : EReal) * b) := by
  have hn : 0 < n := (Nat.zero_le i.val).trans_lt i.isLt
  have hsub : n - (i.val + 1) + 1 = n - i.val := by omega
  cases b using EReal.rec with
  | bot => exact False.elim ((EReal.bot_lt_coe a).not_ge hab)
  | coe b =>
    have hw : 0 ≤ b - a := sub_nonneg.mpr (EReal.coe_le_coe_iff.mp hab)
    have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
    have hi0 : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    simp only [hsub, Nat.add_sub_cancel, ← EReal.coe_natCast, ← EReal.coe_mul,
      ← EReal.coe_add, EReal.coe_le_coe_iff]
    rw [Nat.cast_sub i.isLt.le, Nat.cast_sub (Nat.succ_le_of_lt i.isLt)]
    push_cast
    constructor
    · nlinarith [mul_nonneg hi0 hw]
    constructor
    · nlinarith
    · nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - i.val - 1 by linarith) hw]
  | top =>
    have hnt : (n : EReal) * ⊤ = ⊤ := EReal.mul_top_of_pos (by exact_mod_cast hn)
    have hist : ((i.val + 1 : ℕ) : EReal) * ⊤ = ⊤ :=
      EReal.mul_top_of_pos (by exact_mod_cast (Nat.zero_lt_succ i.val))
    by_cases hi : i.val = 0
    · simp only [hi, zero_add, Nat.sub_self, Nat.cast_zero, Nat.cast_one, zero_mul,
        one_mul, add_zero, Nat.sub_add_cancel hn, EReal.coe_add_top, hnt, le_top, le_refl, and_self]
    · have hit : (i.val : EReal) * ⊤ = ⊤ :=
        EReal.mul_top_of_pos (by exact_mod_cast (Nat.pos_of_ne_zero hi))
      simp only [Nat.add_sub_cancel, hit, hist, EReal.coe_add_top, hnt, le_top, and_self]

lemma intervalCases_globalize (n : ℕ) (i : Fin n) (E a x : ℝ) (b : EReal)
    (hab : (a : EReal) ≤ b)
    (h : ((((n * a : ℝ) : EReal) ≤ E ∧ (E : EReal) ≤ (n : EReal) * b) →
      IntervalCases n (i.val + 1) E a b x)) : IntervalCases n (i.val + 1) E a b x := by
  obtain ⟨hL,hLU,hU⟩ := interval_threshold_bounds n i a b hab
  refine ⟨?_, ?_, ?_⟩
  · intro he
    exact (h ⟨he.1, he.2.trans (hLU.trans hU)⟩).1 he
  · intro he
    exact (h ⟨hL.trans he.1, he.2.trans hU⟩).2.1 he
  · intro he
    exact (h ⟨(hL.trans hLU).trans he.1, he.2⟩).2.2 he

lemma pair_level_noncross (p : ℝ → ℝ) (hp : PairRegular p)
    (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hpair : p (x + y) = x) (hz : z ∈ equalLevels p) : x ≤ z ∨ z ≤ y := by
  rcases le_total (x+y) (2*z) with h | h
  · left
    have hh := hp.2.1 (add_nonneg hx hy) (show 0 ≤ 2*z by linarith [hz.1]) h
    rw [hpair, hz.2] at hh
    exact hh
  · right
    have hh := hp.2.2.1 (show 0 ≤ 2*z by linarith [hz.1]) (add_nonneg hx hy) h
    dsimp only at hh
    rw [hpair, hz.2] at hh
    linarith

lemma vector_level_bounds (p : ℝ → ℝ) (hp : PairRegular p)
    (n : ℕ) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (ho : ∀ i j, i < j → v j ≤ v i)
    (hc : ∀ i j, i < j → p (v i + v j) = v i)
    (z : ℝ) (hz : z ∈ equalLevels p) :
    ((n : ℝ) * z ≤ ∑ i, v i → ∀ i, z ≤ v i) ∧
    ((∑ i, v i) ≤ (n : ℝ) * z → ∀ i, v i ≤ z) := by
  classical
  have hnc : ∀ i j, v i < z → v j ≤ z := by
    intro i j hi
    rcases lt_trichotomy i j with hij | hij | hji
    · exact (ho i j hij).trans hi.le
    · simpa only [← hij] using hi.le
    · rcases pair_level_noncross p hp (v j) (v i) z (hv j) (hv i) (hc j i hji) hz with h | h
      · exact h
      · exact False.elim (hi.not_ge h)
  constructor
  · intro hs i
    by_contra h
    have hi : v i < z := lt_of_not_ge h
    have hlt := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) => hnc i j hi)
      (show ∃ j ∈ (Finset.univ : Finset (Fin n)), v j < z from ⟨i, Finset.mem_univ _, hi⟩)
    have hlt' : (∑ j, v j) < (n : ℝ) * z := by simpa using hlt
    exact hlt'.not_ge hs
  · intro hs i
    by_contra h
    have hi : z < v i := lt_of_not_ge h
    have hb (j : Fin n) : z ≤ v j := by
      by_contra hj
      exact hi.not_ge (hnc j i (lt_of_not_ge hj))
    have hlt := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) => hb j)
      (show ∃ j ∈ (Finset.univ : Finset (Fin n)), z < v j from ⟨i, Finset.mem_univ _, hi⟩)
    have hlt' : (n : ℝ) * z < ∑ j, v j := by simpa using hlt
    exact hlt'.not_ge hs

lemma vector_gap_staircase (p : ℝ → ℝ) (hp : PairRegular p)
    (n : ℕ) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (ho : ∀ i j, i < j → v j ≤ v i)
    (hc : ∀ i j, i < j → p (v i + v j) = v i)
    (a : ℝ) (b : EReal) (ha : a ∈ equalLevels p)
    (hb : ∀ t : ℝ, (t : EReal) = b → t ∈ equalLevels p)
    (hgap : ∀ t : ℝ, a < t → (t : EReal) < b → t ∉ equalLevels p)
    (hE : (((n : ℝ) * a : ℝ) : EReal) ≤ (∑ i, v i : ℝ) ∧
      ((∑ i, v i : ℝ) : EReal) ≤ (n : EReal) * b) : Staircase a b v := by
  have hlow : ∀ i, a ≤ v i :=
    (vector_level_bounds p hp n v hv ho hc a ha).1 (EReal.coe_le_coe_iff.mp hE.1)
  have hupp : ∀ i, (v i : EReal) ≤ b := by
    cases b using EReal.rec with
    | bot =>
      intro i
      have hn : 0 < n := (Nat.zero_le i.val).trans_lt i.isLt
      have hh := hE.2
      rw [EReal.mul_bot_of_pos (by exact_mod_cast hn)] at hh
      exact False.elim ((EReal.bot_lt_coe _).not_ge hh)
    | coe b =>
      have hs : (∑ i, v i) ≤ n*b := by
        simpa only [← EReal.coe_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff] using hE.2
      exact fun i => EReal.coe_le_coe ((vector_level_bounds p hp n v hv ho hc b (hb b rfl)).2 hs i)
    | top => exact fun _ => le_top
  refine ⟨fun i => ⟨hlow i, hupp i⟩, ?_⟩
  intro i j hij
  by_cases hi : (v i : EReal) = b
  · exact Or.inl hi
  right
  by_contra hj
  have haj : a < v j := lt_of_le_of_ne (hlow j) (Ne.symm hj)
  have hbi : (v i : EReal) < b := lt_of_le_of_ne (hupp i) hi
  have hai : a < v i := haj.trans_le (ho i j hij)
  have hbj : (v j : EReal) < b := (EReal.coe_le_coe (ho i j hij)).trans_lt hbi
  have hep := hp.2.2.2.2 (v i+v j) (add_nonneg (hv i) (hv j))
  rw [hc i j hij] at hep
  have he : v i+v j-v i = v j := by ring
  rw [he] at hep
  exact hep.elim (hgap _ hai hbi) (hgap _ haj hbj)

theorem interval_of_pair_model {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (ho : OrderPreserving φ) (p : ℝ → ℝ)
    (hp : PairRegular p) (hcompat : PairCompatible φ p) : IsIntervalRule φ := by
  classical
  obtain ⟨a,b,hab,hdisj,hends,hcover⟩ := exists_gap_family (equalLevels p)
    (equalLevels_closed p hp) (zero_mem_equalLevels p hp) (fun _ h => h.1)
  refine ⟨a,b,hab,hdisj,?_⟩
  intro l E hl hE u hu
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hu
  subst u
  have hn : 0 < l.length := List.length_pos_iff.mpr hl.2
  have hnR : 0 < (l.length : ℝ) := by exact_mod_cast hn
  let v : Fin l.length → ℝ := fun j => φ l E (l.get j)
  have hv : ∀ j, 0 ≤ v j := fun j => (hφ l E hl hE).1 _ (List.get_mem ..)
  have hs : ∑ j, v j = E := (sum_get l hl.1 (φ l E)).trans (hφ l E hl hE).2
  have hov : ∀ j k, j < k → v k ≤ v j := by
    intro j k hjk
    exact ho l E hl hE _ (List.get_mem ..) _ (List.get_mem ..)
      (by simpa only [pos_get l hl.1] using Nat.succ_lt_succ hjk)
  have hcv : ∀ j k, j < k → p (v j+v k) = v j := by
    intro j k hjk
    exact (hcompat l E hl hE _ (List.get_mem ..) _ (List.get_mem ..)
      (by simpa only [pos_get l hl.1] using Nat.succ_lt_succ hjk)).1
  have hst (k : ℕ) (he : (((l.length * a k : ℝ) : EReal) ≤ E ∧
      (E : EReal) ≤ (l.length : EReal) * b k)) : Staircase (a k) (b k) v :=
    vector_gap_staircase p hp _ v hv hov hcv (a k) (b k)
      (hends k).1 (hends k).2.1 (hends k).2.2 (by simpa only [hs] using he)
  have hcases (k : ℕ) : IntervalCases l.length (i.val+1) E (a k) (b k) (v i) := by
    apply intervalCases_globalize _ i E (a k) (v i) (b k) (hab k).2
    intro he
    exact (staircase_iff_cases _ hn (a k) E (b k) (hab k).1 (hab k).2 he v hs).mp (hst k he) i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    simpa only [pos_get l hl.1 i] using (hcases k).1
  · intro k
    simpa only [pos_get l hl.1 i] using (hcases k).2.1
  · intro k
    simpa only [pos_get l hl.1 i] using (hcases k).2.2
  · intro hout
    have hq : 0 ≤ E / l.length := div_nonneg hE hnR.le
    have hqZ : E / l.length ∈ equalLevels p := by
      by_contra hqZ
      obtain ⟨k,hka,hkb⟩ := hcover _ hq hqZ
      exact hout k ((scaled_mem_iff _ hn _ E _).mpr ⟨hka.le,hkb.le⟩)
    have he : (l.length : ℝ) * (E / l.length) = E := by field_simp
    have hb := vector_level_bounds p hp _ v hv hov hcv _ hqZ
    exact le_antisymm (hb.2 (by rw [hs,he]) i) (hb.1 (by rw [hs,he]) i)

end PrizeIntervalProof
end

noncomputable section
open scoped BigOperators
open PrizeAlloc.Interval
namespace PrizeIntervalProof

def FamilyVector {n : ℕ} (a : ℕ → ℝ) (b : ℕ → EReal)
    (v : Fin n → ℝ) : Prop :=
  (∃ k, (a k : EReal) < b k ∧ Staircase (a k) (b k) v) ∨
  ∃ q : ℝ, (∀ i, v i = q) ∧
    ∀ k, ¬ ((a k : EReal) < (q : EReal) ∧ (q : EReal) < b k)

theorem genuine_intervals_ordered (a : ℕ → ℝ) (b : ℕ → EReal)
    (hd : Pairwise (fun k l => Disjoint (Set.Ioo (a k : EReal) (b k))
      (Set.Ioo (a l : EReal) (b l))))
    (k l : ℕ) (hkl : k ≠ l) (hk : (a k : EReal) < b k)
    (hl : (a l : EReal) < b l) :
    b k ≤ (a l : EReal) ∨ b l ≤ (a k : EReal) := by
  have hdis := Set.Ioo_disjoint_Ioo.mp (hd hkl)
  by_cases h : b k ≤ (a l : EReal)
  · exact Or.inl h
  · right
    by_contra h'
    have hh : max (a k : EReal) (a l : EReal) < min (b k) (b l) :=
      max_lt_iff.mpr ⟨lt_min hk (lt_of_not_ge h'), lt_min (lt_of_not_ge h) hl⟩
    exact (not_lt_of_ge hdis) hh

theorem family_vector_monotone (n : ℕ) (hn : 0 < n)
    (a : ℕ → ℝ) (b : ℕ → EReal)
    (hab : ∀ k, 0 ≤ a k ∧ (a k : EReal) ≤ b k)
    (hd : Pairwise (fun k l => Disjoint (Set.Ioo (a k : EReal) (b k))
      (Set.Ioo (a l : EReal) (b l))))
    (v w : Fin n → ℝ) (hv : FamilyVector a b v) (hw : FamilyVector a b w)
    (hsum : ∑ i, v i < ∑ i, w i) : ∀ i, v i ≤ w i := by
  have no_reverse : ¬ (∀ i, w i ≤ v i) := by
    intro h
    exact (not_lt_of_ge (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i))) hsum
  rcases hv with ⟨k,hk,hvk⟩ | ⟨q,hvq,hq⟩
  · rcases hw with ⟨l,hl,hwl⟩ | ⟨q,hwq,hq⟩
    · by_cases hkl : k = l
      · subst l
        exact staircase_monotone n (a k) (b k) (hab k).2 v w hvk hwl hsum.le
      · rcases genuine_intervals_ordered a b hd k l hkl hk hl with h | h
        · intro i
          exact EReal.coe_le_coe_iff.mp
            (((hvk.1 i).2.trans h).trans (EReal.coe_le_coe (hwl.1 i).1))
        · exact False.elim (no_reverse (fun i => EReal.coe_le_coe_iff.mp
            (((hwl.1 i).2.trans h).trans (EReal.coe_le_coe (hvk.1 i).1))))
    · by_cases h : b k ≤ (q : EReal)
      · intro i
        rw [hwq i]
        exact EReal.coe_le_coe_iff.mp ((hvk.1 i).2.trans h)
      · have hqa : q ≤ a k := by
          apply EReal.coe_le_coe_iff.mp
          apply le_of_not_gt
          intro haq
          exact hq k ⟨haq,lt_of_not_ge h⟩
        exact False.elim (no_reverse (fun i => by rw [hwq i]; exact hqa.trans (hvk.1 i).1))
  · rcases hw with ⟨l,hl,hwl⟩ | ⟨r,hwr,hr⟩
    · by_cases h : q ≤ a l
      · intro i
        rw [hvq i]
        exact h.trans (hwl.1 i).1
      · have hbq : b l ≤ (q : EReal) := by
          apply le_of_not_gt
          intro hqb
          exact hq l ⟨EReal.coe_lt_coe (lt_of_not_ge h),hqb⟩
        exact False.elim (no_reverse (fun i => by
          rw [hvq i]
          exact EReal.coe_le_coe_iff.mp ((hwl.1 i).2.trans hbq)))
    · have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hs : (n : ℝ) * q < (n : ℝ) * r := by simpa [hvq,hwr] using hsum
      have hqr : q < r := by nlinarith
      intro i
      rw [hvq i,hwr i]
      exact hqr.le


 def IntervalModel {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (a : ℕ → ℝ) (b : ℕ → EReal) : Prop :=
  ∀ l E, IsRanking l → 0 ≤ E → ∀ i ∈ l,
    (∀ k, IntervalCases l.length (pos l i) E (a k) (b k) (φ l E i)) ∧
    ((∀ k, ¬((((l.length * a k : ℝ) : EReal) ≤ E) ∧
      (E : EReal) ≤ (l.length : EReal) * b k)) → φ l E i = E / l.length)

lemma model_staircase {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (a : ℕ → ℝ) (b : ℕ → EReal) (hab : ∀ k, 0 ≤ a k ∧ (a k : EReal) ≤ b k)
    (hm : IntervalModel φ a b) (l : List U) (E : ℝ) (hl : IsRanking l) (hE : 0 ≤ E)
    (k : ℕ) (hk : (((l.length * a k : ℝ) : EReal) ≤ E) ∧
      (E : EReal) ≤ (l.length : EReal) * b k) :
    Staircase (a k) (b k) (fun i : Fin l.length => φ l E (l.get i)) := by
  have hn : 0 < l.length := List.length_pos_iff.mpr hl.2
  let v : Fin l.length → ℝ := fun i => φ l E (l.get i)
  have hs : ∑ i, v i = E := (sum_get l hl.1 (φ l E)).trans (hφ l E hl hE).2
  have hc : ∀ i : Fin l.length, IntervalCases l.length (i.val+1) E (a k) (b k) (v i) := by
    intro i
    have hh := (hm l E hl hE (l.get i) (List.get_mem l i)).1 k
    rw [pos_get l hl.1 i] at hh
    exact hh
  exact (staircase_iff_cases l.length hn (a k) E (b k) (hab k).1 (hab k).2 hk v hs).mpr hc

lemma staircase_sum_mem (n : ℕ) (hn : 0 < n) (a : ℝ) (b : EReal)
    (v : Fin n → ℝ) (hv : Staircase a b v) :
    (((n * a : ℝ) : EReal) ≤ (∑ i, v i : ℝ)) ∧
      ((∑ i, v i : ℝ) : EReal) ≤ (n : EReal) * b := by
  have hlow : (n : ℝ) * a ≤ ∑ i, v i := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hv.1 i).1)
  refine ⟨EReal.coe_le_coe hlow, ?_⟩
  cases b using EReal.rec with
  | bot => exact False.elim ((EReal.bot_lt_coe _).not_ge (hv.1 ⟨0,hn⟩).2)
  | coe b =>
    have hupp : (∑ i, v i) ≤ (n : ℝ) * b := by
      simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
        EReal.coe_le_coe_iff.mp (hv.1 i).2)
    simpa only [← EReal.coe_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff] using hupp
  | top =>
    rw [EReal.mul_top_of_pos (by exact_mod_cast hn)]
    exact le_top

lemma sub_toFinset {U : Type*} [DecidableEq U] (l : List U) (S : Finset U)
    (hS : S ⊆ l.toFinset) : (sub l S).toFinset = S := by
  ext i
  simp only [List.mem_toFinset, mem_sub]
  exact ⟨And.right, fun hi => ⟨List.mem_toFinset.mp (hS hi),hi⟩⟩

lemma staircase_subranking {U : Type*} [DecidableEq U]
    (l : List U) (hl : l.Nodup) (S : Finset U) (f : U → ℝ)
    (a : ℝ) (b : EReal) (hv : Staircase a b (fun i : Fin l.length => f (l.get i))) :
    Staircase a b (fun i : Fin (sub l S).length => f ((sub l S).get i)) := by
  have hp (i : Fin (sub l S).length) : (sub l S).get i ∈ l :=
    ((mem_sub l S _).mp (List.get_mem ..)).1
  have hS (i : Fin (sub l S).length) : (sub l S).get i ∈ S :=
    ((mem_sub l S _).mp (List.get_mem ..)).2
  constructor
  · intro i
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp (hp i)
    simpa only [← hj] using hv.1 j
  · intro i j hij
    obtain ⟨r,hr⟩ := List.mem_iff_get.mp (hp i)
    obtain ⟨s,hs⟩ := List.mem_iff_get.mp (hp j)
    have hij' : pos (sub l S) ((sub l S).get i) < pos (sub l S) ((sub l S).get j) := by
      simpa only [pos_get (sub l S) (hl.filter _)] using Nat.succ_lt_succ hij
    have hrs := (sub_pos_lt_iff l hl S _ _ (hp i) (hp j) (hS i) (hS j)).mp hij'
    rw [← hr, ← hs, pos_get l hl r, pos_get l hl s] at hrs
    have hlt : r < s := Nat.lt_of_succ_lt_succ hrs
    simpa only [hr,hs] using hv.2 r s hlt

lemma model_family_vector {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (a : ℕ → ℝ) (b : ℕ → EReal) (hab : ∀ k, 0 ≤ a k ∧ (a k : EReal) ≤ b k)
    (hm : IntervalModel φ a b) (l : List U) (E : ℝ) (hl : IsRanking l) (hE : 0 ≤ E) :
    FamilyVector a b (fun i : Fin l.length => φ l E (l.get i)) := by
  classical
  have hn : 0 < l.length := List.length_pos_iff.mpr hl.2
  have hnR : 0 < (l.length : ℝ) := by exact_mod_cast hn
  have hs := (sum_get l hl.1 (φ l E)).trans (hφ l E hl hE).2
  by_cases hg : ∃ k, (a k : EReal) < b k ∧
      (((l.length * a k : ℝ) : EReal) ≤ E) ∧ (E : EReal) ≤ (l.length : EReal) * b k
  · obtain ⟨k,hkg,hk⟩ := hg
    exact Or.inl ⟨k,hkg,model_staircase φ hφ a b hab hm l E hl hE k hk⟩
  right
  refine ⟨E/l.length, ?_, ?_⟩
  · by_cases hk : ∃ k, (((l.length * a k : ℝ) : EReal) ≤ E) ∧
        (E : EReal) ≤ (l.length : EReal) * b k
    · obtain ⟨k,hk⟩ := hk
      have he : (a k : EReal) = b k := le_antisymm (hab k).2
        (le_of_not_gt (fun h => hg ⟨k,h,hk⟩))
      have hv := model_staircase φ hφ a b hab hm l E hl hE k hk
      have hc (i : Fin l.length) : φ l E (l.get i) = a k :=
        le_antisymm (EReal.coe_le_coe_iff.mp (by simpa only [← he] using (hv.1 i).2)) (hv.1 i).1
      have hsum : (l.length : ℝ) * a k = E := by simpa only [hc, Fin.sum_const, nsmul_eq_mul] using hs
      intro i
      change φ l E (l.get i) = E / l.length
      rw [hc i, ← hsum]
      field_simp
    · intro i
      exact (hm l E hl hE _ (List.get_mem ..)).2 (by simpa only [not_exists] using hk)
  · intro k hk
    exact hg ⟨k, hk.1.trans hk.2,
      (scaled_mem_iff _ hn _ E _).mpr ⟨EReal.coe_le_coe_iff.mp hk.1.le,hk.2.le⟩⟩

theorem axioms_of_interval {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ)
    (hinterval : IsIntervalRule φ) :
    OrderPreserving φ ∧ EndowmentMonotone φ ∧ Consistent φ := by
  classical
  obtain ⟨a,b,hab,hdisj,hr⟩ := hinterval
  have hm : IntervalModel φ a b := by
    intro l E hl hE i hi
    have h := hr l E hl hE i hi
    exact ⟨fun k => ⟨h.1 k,h.2.1 k,h.2.2.1 k⟩,h.2.2.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro l E hl hE u hu v hv huv
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hu
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hv
    subst u
    subst v
    have hij : i < j := by
      rw [pos_get l hl.1 i,pos_get l hl.1 j] at huv
      exact Nat.lt_of_succ_lt_succ huv
    by_cases hk : ∃ k, (((l.length * a k : ℝ) : EReal) ≤ E) ∧
        (E : EReal) ≤ (l.length : EReal) * b k
    · obtain ⟨k,hk⟩ := hk
      exact staircase_order _ _ _ (model_staircase φ hφ a b hab hm l E hl hE k hk) hij
    · have hout : ∀ k, ¬((((l.length * a k : ℝ) : EReal) ≤ E) ∧
          (E : EReal) ≤ (l.length : EReal) * b k) := by simpa only [not_exists] using hk
      rw [(hm l E hl hE _ (List.get_mem ..)).2 hout,
        (hm l E hl hE _ (List.get_mem ..)).2 hout]
  · intro l E F hl hE hEF u hu
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hu
    subst u
    have hn : 0 < l.length := List.length_pos_iff.mpr hl.2
    have hv := model_family_vector φ hφ a b hab hm l E hl hE
    have hw := model_family_vector φ hφ a b hab hm l F hl (hE.trans hEF.le)
    have hs : (∑ j : Fin l.length, φ l E (l.get j)) < ∑ j : Fin l.length, φ l F (l.get j) := by
      rw [sum_get l hl.1, sum_get l hl.1, (hφ l E hl hE).2,
        (hφ l F hl (hE.trans hEF.le)).2]
      exact hEF
    exact family_vector_monotone _ hn a b hab hdisj _ _ hv hw hs i
  · intro l E hl hE S hS hSne u hu
    let lS := sub l S
    let F := ∑ j ∈ S, φ l E j
    have hlS : IsRanking lS := sub_ranking l hl S hS hSne
    have hF : 0 ≤ F := Finset.sum_nonneg (fun j hj => (hφ l E hl hE).1 j
      (List.mem_toFinset.mp (hS hj)))
    have hn : 0 < l.length := List.length_pos_iff.mpr hl.2
    have hmN : 0 < lS.length := List.length_pos_iff.mpr hlS.2
    have hmR : 0 < (lS.length : ℝ) := by exact_mod_cast hmN
    have huS : u ∈ lS := (mem_sub l S u).mpr ⟨List.mem_toFinset.mp (hS hu),hu⟩
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp huS
    subst u
    have hs : (∑ j : Fin lS.length, φ l E (lS.get j)) = F := by
      rw [sum_get lS hlS.1, sub_toFinset l S hS]
    by_cases hk : ∃ k, (((l.length * a k : ℝ) : EReal) ≤ E) ∧
        (E : EReal) ≤ (l.length : EReal) * b k
    · obtain ⟨k,hk⟩ := hk
      have hv := model_staircase φ hφ a b hab hm l E hl hE k hk
      have hvs := staircase_subranking l hl.1 S (φ l E) (a k) (b k) hv
      change Staircase (a k) (b k) (fun j : Fin lS.length => φ l E (lS.get j)) at hvs
      have hFs : (((lS.length * a k : ℝ) : EReal) ≤ F) ∧
          (F : EReal) ≤ (lS.length : EReal) * b k := by
        simpa only [hs] using staircase_sum_mem _ hmN (a k) (b k) _ hvs
      have hws := model_staircase φ hφ a b hab hm lS F hlS hF k hFs
      have he := staircase_unique _ (a k) (b k) (hab k).2 _ _ hvs hws
        (hs.trans ((sum_get lS hlS.1 (φ lS F)).trans (hφ lS F hlS hF).2).symm)
      exact congrFun he i
    · have hout : ∀ k, ¬((((l.length * a k : ℝ) : EReal) ≤ E) ∧
          (E : EReal) ≤ (l.length : EReal) * b k) := by simpa only [not_exists] using hk
      have hc (j : Fin lS.length) : φ l E (lS.get j) = E/l.length :=
        (hm l E hl hE _ ((mem_sub l S _).mp (List.get_mem ..)).1).2 hout
      have hsum : (lS.length : ℝ) * (E/l.length) = F := by
        simpa only [hc, Fin.sum_const, nsmul_eq_mul] using hs
      have hq : F/lS.length = E/l.length := by rw [← hsum]; field_simp
      have houtS : ∀ k, ¬((((lS.length * a k : ℝ) : EReal) ≤ F) ∧
          (F : EReal) ≤ (lS.length : EReal) * b k) := by
        intro k hk
        have hh := (scaled_mem_iff _ hmN (a k) F (b k)).mp hk
        rw [hq] at hh
        exact hout k ((scaled_mem_iff _ hn (a k) E (b k)).mpr hh)
      rw [hc i, (hm lS F hlS hF _ (List.get_mem ..)).2 houtS, hq]

end PrizeIntervalProof
end

namespace PrizeAlloc.Interval

theorem theorem_1 {U : Type*} [DecidableEq U] [Countable U]
    (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ) :
    (OrderPreserving φ ∧ EndowmentMonotone φ ∧ Consistent φ) ↔ IsIntervalRule φ := by
  constructor
  · rintro ⟨ho, hm, hc⟩
    obtain ⟨p, hp, hcompat⟩ := PrizeIntervalProof.exists_pair_model hU φ hφ ho hm hc
    exact PrizeIntervalProof.interval_of_pair_model φ hφ ho p hp hcompat
  · exact PrizeIntervalProof.axioms_of_interval φ hφ

end PrizeAlloc.Interval

open PrizeAlloc.Interval


theorem solution {U : Type*} [DecidableEq U] [Countable U]
    (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : IsPrizeRule φ) :
    (OrderPreserving φ ∧ EndowmentMonotone φ ∧ Consistent φ) ↔ IsIntervalRule φ := by
  exact PrizeAlloc.Interval.theorem_1 hU φ hφ
