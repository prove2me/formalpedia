-- Prove2me | solution 1 for PandoraKnapsack.Skipping.alg1Utility_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:24:57.562358+00:00
-- url     : https://prove2.me/submissions/32958ef1-0101-452a-9fab-c5b454d2c18e

import Definitions.Def_PandoraKnapsack_Skipping_RoundingPayoff
import Theorems.Thm_PandoraKnapsack_Skipping_feasible_reach

open scoped Classical
open PandoraKnapsack.Skipping

namespace PandoraKnapsack.Skipping
variable {n m T : ℕ}
private abbrev Single (m T : ℕ) := Option (Fin m × Fin (T+1))
private abbrev Entry (n m : ℕ) := Fin n × Fin m × ℕ
private lemma order_mem (a : Assignment n m T) (k : Fin n) (j : Fin m) (t : ℕ) :
    (k,j,t) ∈ scanOrder a ↔ ∃ u : Fin (T+1), a k = some (j,u) ∧ u.val = t := by
  simp [scanOrder, retained, Option.map_eq_some_iff, Prod.ext_iff]

private lemma order_distinct (a : Assignment n m T) :
    ((scanOrder a).map Prod.fst).Nodup := by
  apply ((List.mergeSort_perm (retained a) _).map Prod.fst).nodup_iff.mpr
  rw [List.Nodup, List.pairwise_map, retained, List.pairwise_filterMap]
  apply (List.nodup_finRange n).imp
  intro i k hik u hu v hv
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hu
  obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hv
  exact hik

private noncomputable def wt (I : Instance n m T) (x : LPArray n m) (k : Fin n)
    (a : Single m T) (s : Fin (T+2)) : ℝ := assignWeight x k a * sizeWeight I k a s

private lemma size_norm (I : Instance n m T) (k : Fin n) (a : Single m T) :
    ∑ s, sizeWeight I k a s = 1 := by
  cases a with
  | none =>
    have h : ∀ s : Fin (T+2), s.val = 0 ↔ s = 0 := by simp
    simp [sizeWeight,h]
  | some a =>
    rcases a with ⟨j,t⟩
    simp only [sizeWeight]
    rw [← ENNReal.toReal_sum (fun s _ => (I.sizeLaw k j).apply_ne_top s)]
    have hs := (I.sizeLaw k j).tsum_coe
    rw [tsum_fintype] at hs
    rw [hs, ENNReal.toReal_one]

private lemma wt_norm (I : Instance n m T) (x : LPArray n m) (k : Fin n) :
    ∑ a, ∑ s, wt I x k a s = 1 := by
  simp only [wt, ← Finset.mul_sum, size_norm, mul_one]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [assignWeight, Fin.sum_univ_eq_sum_range, ← Finset.sum_div]
  ring

private lemma wt_pos (I : Instance n m T) (x : LPArray n m) (hx : PsiFeasible I T x)
    (ω : Outcome n m T) : 0 ≤ outcomeWeight I x ω := by
  apply Finset.prod_nonneg
  intro k _
  cases ha : ω.1 k with
  | none =>
    simp only [assignWeight,sizeWeight]
    split_ifs <;> linarith [hx.2.1 k]
  | some p =>
    rcases p with ⟨j,u⟩
    apply mul_nonneg _ ENNReal.toReal_nonneg
    exact div_nonneg (hx.2.2 k j u (by omega)).1 (by norm_num)

private lemma factor (f : Fin n → Single m T → Fin (T+2) → ℝ) :
    (∑ ω : Outcome n m T, ∏ k, f k (ω.1 k) (ω.2 k)) =
    ∏ k, ∑ a, ∑ s, f k a s := by
  let e := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Single m T) (fun _ => Fin (T+2))
  rw [← e.sum_comp (fun ω => ∏ k, f k (ω.1 k) (ω.2 k))]
  change (∑ z : Fin n → Single m T × Fin (T+2), ∏ k, f k (z k).1 (z k).2) = _
  rw [← Fintype.prod_sum (fun k (p : Single m T × Fin (T+2)) => f k p.1 p.2)]
  simp [Fintype.sum_prod_type]

private noncomputable def gate (I : Instance n m T) (x : LPArray n m) (i : Fin n)
    (o : Single m T) (k : Fin n) (a : Single m T) (s : Fin (T+2)) : ℝ :=
    if k = i ∧ a ≠ o then 0 else wt I x k a s

private lemma gate_prod (I : Instance n m T) (x : LPArray n m) (i : Fin n) (o : Single m T)
    (ω : Outcome n m T) :
    (∏ k, gate I x i o k (ω.1 k) (ω.2 k)) = if ω.1 i = o then outcomeWeight I x ω else 0 := by
  by_cases h : ω.1 i = o
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro k hk
    by_cases hk' : k = i <;> simp [gate, wt, hk', h]
  · rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [gate,h]

private lemma gate_sum (I : Instance n m T) (x : LPArray n m) (i : Fin n) (o : Single m T)
    (k : Fin n) :
    (∑ a, ∑ s, gate I x i o k a s) = if k = i then assignWeight x i o else 1 := by
  by_cases h : k = i
  · subst k
    simp [gate, wt, ← Finset.mul_sum, size_norm,
      Finset.sum_ite_irrel, eq_comm, ite_not]
  · simp only [gate, h, false_and, if_false, wt_norm]

private lemma prob_sum (I : Instance n m T) (x : LPArray n m) (E : Outcome n m T → Prop)
    [DecidablePred E] : alg1Prob I x E = ∑ ω, if E ω then outcomeWeight I x ω else 0 := by
  unfold alg1Prob
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h]

private lemma event_mass (I : Instance n m T) (x : LPArray n m) (i : Fin n) (o : Single m T) :
    alg1Prob I x (fun ω => ω.1 i = o) = assignWeight x i o := by
  rw [prob_sum]
  simp_rw [← gate_prod I x i o]
  rw [factor]
  simp only [gate_sum, Finset.prod_ite_eq', Finset.mem_univ, if_true]

end PandoraKnapsack.Skipping

namespace PandoraKnapsack.Skipping
variable {n m T : ℕ}
private abbrev Sizes (n T : ℕ) := Fin n → Fin (T+2)
private noncomputable def credit (I : Instance n m T) (z : Sizes n T) :
    List (Entry n m) → ℕ → ℝ
  | [], _ => 0
  | (k,j,b) :: l, S =>
    if S ≤ b then effWeight I k j b + credit I z l (S + (z k).val)
    else credit I z l S

private lemma credit_ext (I : Instance n m T) (z z' : Sizes n T) (l : List (Entry n m))
    (h : ∀ e ∈ l, z e.1 = z' e.1) (S : ℕ) : credit I z l S = credit I z' l S := by
  induction l generalizing S with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k,j,b⟩ := e
    have hk : z k = z' k := h _ (.head _)
    have hh := ih (fun e he => h e (.tail _ he))
    simp [credit,hk,hh]

private lemma credit_overflow (I : Instance n m T) (z : Sizes n T) (l : List (Entry n m))
    (h : ∀ e ∈ l, e.2.2 ≤ T) (S : ℕ) (hS : T < S) : credit I z l S = 0 := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k,j,b⟩ := e
    have hb : b ≤ T := h _ (.head _)
    simpa [credit, show ¬ S ≤ b by omega] using ih (fun e he => h e (.tail _ he))

private noncomputable abbrev law (I : Instance n m T) (a : Assignment n m T) (z : Sizes n T) : ℝ :=
  ∏ k, sizeWeight I k (a k) (z k)

private lemma law_norm (I : Instance n m T) (a : Assignment n m T) :
    ∑ z, law I a z = 1 := by
  unfold law
  rw [← Fintype.prod_sum (fun k s => sizeWeight I k (a k) s)]
  simp only [size_norm,Finset.prod_const_one]

private lemma size_pos (I : Instance n m T) (k : Fin n) (a : Single m T) (s : Fin (T+2)) :
    0 ≤ sizeWeight I k a s := by
  rcases a with _ | ⟨j,t⟩
  · simp [sizeWeight]; positivity
  · exact ENNReal.toReal_nonneg

private lemma independent_tail (I : Instance n m T) (a : Assignment n m T) (k : Fin n)
    (F : Fin (T+2) → Sizes n T → ℝ)
    (hF : ∀ u z z', (∀ l, l ≠ k → z l = z' l) → F u z = F u z') :
    (∑ z : Sizes n T, law I a z * F (z k) z) =
    ∑ u, sizeWeight I k (a k) u * ∑ z, law I a z * F u z := by
  let e := Equiv.funSplitAt k (Fin (T+2))
  let Z := {l : Fin n // l ≠ k} → Fin (T+2)
  let rest (r : Z) := ∏ l : {l : Fin n // l ≠ k}, sizeWeight I l (a l) (r l)
  have he0 (u : Fin (T+2)) (r : Z) : e.symm (u,r) k = u := by simp [e]
  have he1 (u : Fin (T+2)) (r : Z) (l : Fin n) (hl : l ≠ k) :
      e.symm (u,r) l = r ⟨l,hl⟩ := by simp [e,hl]
  have hW (u : Fin (T+2)) (r : Z) : law I a (e.symm (u,r)) = sizeWeight I k (a k) u * rest r := by
    unfold law
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ k, he0]
    congr 1
    apply Finset.prod_congr rfl
    intro l _
    rw [he1 _ _ _ l.2]
  have hF' (u v : Fin (T+2)) (r : Z) : F u (e.symm (v,r)) = F u (e.symm (u,r)) :=
    hF _ _ _ (fun l hl => by simp [he1 _ _ l hl])
  have hdis (g : Sizes n T → ℝ) : ∑ z, g z = ∑ u : Fin (T+2), ∑ r : Z, g (e.symm (u,r)) := by
    rw [← e.symm.sum_comp g, Fintype.sum_prod_type]
  rw [hdis]
  apply Finset.sum_congr rfl
  intro u _
  simp only [he0,hW,mul_assoc,← Finset.mul_sum]
  congr 1
  rw [hdis]
  simp only [hW,hF' u,mul_assoc,← Finset.mul_sum,← Finset.sum_mul,size_norm,one_mul]

private lemma earlier_weight (I : Instance n m T) (hI : IsValid I) (i : Fin n) (j : Fin m)
    {u t : ℕ} (h : u ≤ t) : effWeight I i j t ≤ effWeight I i j u := by
  have hc : 0 ≤ cdf I i j ((T : ℝ) - (0 : ℕ)) := by
    unfold cdf
    positivity
  have hv : 0 ≤ I.value i := by
    by_contra! hn
    have hprod := mul_nonpos_of_nonpos_of_nonneg hn.le hc
    have hp := hI.2.2 i j
    unfold effWeight at hp
    linarith [hI.2.1 i j]
  unfold effWeight
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ hv
  unfold cdf
  apply Finset.sum_le_sum
  intro s hs
  have h' : (u : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
  split_ifs <;> first | rfl | positivity | linarith

private lemma immediate (I : Instance n m T) (k : Fin n) (j : Fin m) (S : ℕ) :
    (∑ s : Fin (T+2), (I.sizeLaw k j s).toReal *
        (if S+s.val ≤ T then I.value k - I.cost k j else -I.cost k j)) =
      effWeight I k j S := by
  let p (s : Fin (T+2)) := (I.sizeLaw k j s).toReal
  have hn : ∑ s, p s = 1 := size_norm I k (some (j,0))
  have h (s : Fin (T+2)) :
      p s * (if S+s.val ≤ T then I.value k - I.cost k j else -I.cost k j) =
      I.value k * (if (s.val:ℝ) ≤ (T:ℝ) - S then p s else 0) - p s * I.cost k j := by
    have iff' : (s.val:ℝ) ≤ (T:ℝ) - S ↔ S+s.val ≤ T := by
      rw [le_sub_iff_add_le, add_comm]; exact_mod_cast Iff.rfl
    simp only [iff']; split_ifs <;> ring
  change (∑ s, p s * _) = _
  simp_rw [h]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,hn,one_mul]
  rfl

private lemma expected_credit (I : Instance n m T) (hI : IsValid I) (a : Assignment n m T)
    (l : List (Entry n m)) (hd : (l.map Prod.fst).Nodup) (hm : ∀ e ∈ l, e ∈ scanOrder a)
    (S : ℕ) (hS : S ≤ T) :
    (∑ z : Sizes n T, law I a z * credit I z l S) ≤
    skipValueFrom I (l.map (fun e => (e.1,e.2.1,T-e.2.2))) S := by
  induction l generalizing S with
  | nil => simp [credit,skipValueFrom]
  | cons e l ih =>
    rcases e with ⟨k,j,b⟩
    have hsub : ∀ e ∈ l, e ∈ scanOrder a := fun e he => hm e (.tail _ he)
    have htail : ∀ e ∈ l, e.2.2 ≤ T := by
      rintro ⟨i,c,v⟩ he
      obtain ⟨u,hu,rfl⟩ := (order_mem _ _ _ _).mp (hsub _ he)
      exact Nat.lt_succ_iff.mp u.isLt
    have hd' := (List.nodup_cons.mp hd).2
    have hnot := (List.nodup_cons.mp hd).1
    obtain ⟨t,ha,ht⟩ := (order_mem a k j b).mp (hm _ (.head _))
    have hb : b ≤ T := by omega
    have ih' := ih hd' hsub
    change _ ≤ skipValueFrom I ((k,j,T-b) :: _) S
    by_cases hSb : S ≤ b
    · have hθ : T-b ≤ T-S := by omega
      simp only [credit,hSb,if_true,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,law_norm,
        one_mul,skipValueFrom,hθ]
      have h_indep := independent_tail I a k
        (fun u z => credit I z l (S+u.val)) (by
          intro u z z' he
          apply credit_ext
          intro e he'
          apply he
          exact fun hk => hnot (List.mem_map.mpr ⟨e,he',hk⟩))
      rw [h_indep,ha]
      simp only [sizeWeight]
      calc
        _ ≤ effWeight I k j S + ∑ s : Fin (T+2), (I.sizeLaw k j s).toReal *
              (if S+s.val ≤ T then skipValueFrom I (l.map (fun e => (e.1,e.2.1,T-e.2.2))) (S+s.val) else 0) := by
          apply add_le_add (earlier_weight I hI k j hSb)
          apply Finset.sum_le_sum
          intro s _
          apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          split_ifs with hf
          · exact ih' _ hf
          · simp [credit_overflow I _ l htail _ (by omega : T < S+s.val)]
        _ = _ := by
          rw [← immediate, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro s _
          split_ifs <;> ring
    · have hθ : ¬ T-b ≤ T-S := by omega
      simpa only [credit,hSb,if_false,skipValueFrom,hθ] using ih' S hS

private noncomputable def accrued (I : Instance n m T) (z : Sizes n T) (l : List (Entry n m))
    (S : ℕ) (k : Fin n) (j : Fin m) (t : Fin (T+1)) : ℝ :=
  if (k,j,t.val) ∈ l ∧ loadBefore (fun k => (z k).val) k l S ≤ t.val
  then effWeight I k j t.val else 0

private lemma credit_sum (I : Instance n m T) (a : Assignment n m T) (z : Sizes n T)
    (l : List (Entry n m)) (hd : (l.map Prod.fst).Nodup) (hm : ∀ e ∈ l, e ∈ scanOrder a)
    (S : ℕ) : credit I z l S = ∑ k, ∑ j, ∑ t, accrued I z l S k j t := by
  induction l generalizing S with
  | nil => simp [accrued,credit]
  | cons e l ih =>
    rcases e with ⟨i,c,b⟩
    obtain ⟨v,ha,rfl⟩ := (order_mem a i c b).mp (hm _ (.head _))
    let S' := if S ≤ v.val then S+(z i).val else S
    let headGain := if S ≤ v.val then effWeight I i c v.val else 0
    have hn := (List.nodup_cons.mp hd).1
    have hrec := ih (List.nodup_cons.mp hd).2 (fun e he => hm e (.tail _ he)) S'
    have hstep (k : Fin n) (j : Fin m) (t : Fin (T+1)) :
        accrued I z ((i,c,v.val)::l) S k j t =
        (if k = i ∧ j = c ∧ t = v then headGain else 0) + accrued I z l S' k j t := by
      by_cases hk : k = i
      · subst k
        have hl : (i,j,t.val) ∉ l := fun he => hn (List.mem_map.mpr ⟨_,he,rfl⟩)
        simp [accrued,hl,loadBefore,headGain,Fin.val_inj, ite_and]
        split_ifs <;> simp_all
      · simp [accrued,loadBefore,hk,Ne.symm hk,S']
    simp_rw [hstep,Finset.sum_add_distrib]
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, ← hrec]
    simp [credit,headGain,S']; split_ifs <;> simp

private lemma accrued_scan (I : Instance n m T) (ω : Outcome n m T) (i : Fin n)
    (j : Fin m) (t : Fin (T+1)) :
    accrued I ω.2 (scanOrder ω.1) 0 i j t =
      if ω.1 i = some (j,t) ∧ predecessorLoad ω i ≤ t.val then effWeight I i j t.val else 0 := by
  have hm : (i,j,t.val) ∈ scanOrder ω.1 ↔ ω.1 i = some (j,t) := by
    rw [order_mem]
    constructor
    · rintro ⟨u,hu,ht⟩
      simpa [Fin.ext ht] using hu
    · intro h; exact ⟨t,h,rfl⟩
  unfold accrued predecessorLoad
  by_cases h : ω.1 i = some (j,t) <;> by_cases h' : loadBefore (fun k => (ω.2 k).val) i (scanOrder ω.1) 0 ≤ t.val <;> simp [hm,h,h']

private lemma assign_nonneg (x : LPArray n m) (I : Instance n m T) (hx : PsiFeasible I T x)
    (k : Fin n) (a : Single m T) : 0 ≤ assignWeight x k a := by
  rcases a with _ | ⟨j,t⟩
  · simp only [assignWeight]; linarith [hx.2.1 k]
  · exact div_nonneg (hx.2.2 k j t (by omega)).1 (by norm_num)

private lemma utility_ge (I : Instance n m T) (hI : IsValid I) (x : LPArray n m)
    (hx : PsiFeasible I T x) :
    (∑ i, ∑ j, ∑ t : Fin (T+1), alg1Prob I x
      (fun ω => ω.1 i = some (j,t) ∧ predecessorLoad ω i ≤ t.val) * effWeight I i j t.val) ≤
      alg1Utility I x := by
  let A (a : Assignment n m T) := ∏ k, assignWeight x k (a k)
  have hW (a : Assignment n m T) (z : Sizes n T) : outcomeWeight I x (a,z) = A a * law I a z := by
    simp only [A,law,outcomeWeight,Finset.prod_mul_distrib]
  let U (ω : Outcome n m T) := credit I ω.2 (scanOrder ω.1) 0
  have hu (ω : Outcome n m T) : U ω = ∑ i, ∑ j, ∑ t : Fin (T+1),
      if ω.1 i = some (j,t) ∧ predecessorLoad ω i ≤ t.val then effWeight I i j t.val else 0 := by
    dsimp [U]
    rw [credit_sum I ω.1 ω.2 (scanOrder ω.1) (order_distinct _) (fun e he => he)]
    simp only [accrued_scan]
  have hcredit : (∑ ω : Outcome n m T, outcomeWeight I x ω * U ω) ≤ alg1Utility I x := by
    rw [Fintype.sum_prod_type]
    unfold alg1Utility
    apply Finset.sum_le_sum
    intro a _
    simp only [hW,mul_assoc,← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun i _ => assign_nonneg x I hx i (a i)))
    exact expected_credit I hI a (scanOrder a) (order_distinct _) (fun _ he => he) 0 (by omega)
  apply le_trans (le_of_eq ?_) hcredit
  simp_rw [hu, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [prob_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp_all

end PandoraKnapsack.Skipping

theorem solution {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) (x : LPArray n m)
    (hx : PsiFeasible I T x)
    (hsupp : ∀ i j t, t ≤ T → 0 < x i j t → 0 ≤ effWeight I i j t) :
    psiObjective I T x / 8 ≤ alg1Utility I x := by
  apply le_trans _ (utility_ge I hI x hx)
  unfold psiObjective
  simp_rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [← Fin.sum_univ_eq_sum_range (fun t => effWeight I i j t * x i j t / 8)]
  apply Finset.sum_le_sum
  intro t _
  let E (ω : Outcome n m T) := ω.1 i = some (j,t)
  let G (ω : Outcome n m T) := E ω ∧ predecessorLoad ω i ≤ t.val
  have he : alg1Prob I x E = x i j t.val / 4 := event_mass I x i (some (j,t))
  have hg : (1/2:ℝ) * alg1Prob I x E ≤ alg1Prob I x G := feasible_reach I hI x hx i j t
  change _ ≤ alg1Prob I x G * effWeight I i j t.val
  by_cases h : 0 < x i j t.val
  · have hw := hsupp i j t.val (by omega) h
    rw [he] at hg
    linarith [mul_le_mul_of_nonneg_right hg hw]
  · have hz : x i j t.val = 0 := le_antisymm (le_of_not_gt h) (hx.2.2 i j t.val (by omega)).1
    have hsub : alg1Prob I x G ≤ alg1Prob I x E := by
      unfold alg1Prob
      apply Finset.sum_le_sum
      intro ω _
      by_cases hh : E ω <;> by_cases hu : predecessorLoad ω i ≤ t.val <;>
        simp [G,hh,hu,wt_pos I x hx ω]
    rw [hz] at he
    rw [he] at hg hsub
    have gz : alg1Prob I x G = 0 := by linarith
    simp [gz,hz]
