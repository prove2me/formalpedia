-- Prove2me | solution 1 for PandoraKnapsack.Skipping.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:06:37.431958+00:00
-- url     : https://prove2.me/submissions/8e4333e4-8b45-45d6-8652-308503f068cb

import Definitions.Def_PandoraKnapsack_Skipping_Policies
import Definitions.Def_PandoraKnapsack_Skipping_TimeIndexedLP

open PandoraKnapsack.Skipping
namespace PandoraOccupation

variable {n m T : ℕ}

private abbrev Reward (n m : ℕ) := (Fin n × Fin m × ℕ) → ℝ

private noncomputable def visits (I : Instance n m T) (π : AdaptivePolicy n m) :
    ℕ → History n m → (Reward n m →ₗ[ℝ] ℝ)
  | 0, _ => 0
  | k+1, h =>
    match π h with
    | none => 0
    | some (i,j) =>
      if i ∈ h.map (fun e => e.1) then 0 else
        LinearMap.proj (R := ℝ) (φ := fun _ : Fin n × Fin m × ℕ => ℝ) (i,j,usedCapacity h) +
        ∑ s : Fin (T+2), (I.sizeLaw i j s).toReal •
          (if usedCapacity h + s.val ≤ T then visits I π k (h ++ [(i,j,s.val)]) else 0)

private def atom (i : Fin n) (j : Fin m) (t : ℕ) : Reward n m :=
  fun z => if z.1 = i ∧ z.2.1 = j ∧ z.2.2 = t then 1 else 0

private lemma expand (L : Reward n m →ₗ[ℝ] ℝ) (u : ℕ) (w : Reward n m) :
    ∑ i : Fin n, ∑ j : Fin m, ∑ t ∈ Finset.range (u+1),
      w (i,j,t) * L (atom i j t) =
        L (fun z => if z.2.2 ≤ u then w z else 0) := by
  classical
  have factor (i : Fin n) (j : Fin m) (t : ℕ) :
      w (i,j,t) * L (atom i j t) = L (w (i,j,t) • atom i j t) := by simp
  simp_rw [factor, ← map_sum]
  congr 1
  funext ⟨a,b,v⟩
  simp [Finset.sum_apply, Pi.smul_apply, atom, mul_ite, ite_and, Finset.sum_ite_irrel, Finset.mem_range]

private lemma prob_total (p : PMF (Fin (T+2))) : ∑ s, (p s).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun s _ => p.apply_ne_top s)]
  simpa only [tsum_fintype, ENNReal.toReal_one] using congrArg ENNReal.toReal p.tsum_coe

private lemma used_next (h : History n m) (i : Fin n) (j : Fin m) (s : ℕ) :
    usedCapacity (h ++ [(i,j,s)]) = usedCapacity h + s := by simp [usedCapacity]

private lemma visits_step (I : Instance n m T) (π : AdaptivePolicy n m)
    (g : Reward n m) (k : ℕ) (h : History n m) (i : Fin n) (j : Fin m)
    (hp : π h = some (i,j)) (hf : i ∉ h.map (fun e => e.1)) :
    visits I π (k+1) h g = g (i,j,usedCapacity h) + ∑ s : Fin (T+2), (I.sizeLaw i j s).toReal *
      (if usedCapacity h + s.val ≤ T then visits I π k (h ++ [(i,j,s.val)]) g else 0) := by
  classical
  simp only [visits,hp,hf,if_false,LinearMap.add_apply,LinearMap.proj_apply,
    LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> rfl

private lemma potential (I : Instance n m T) (π : AdaptivePolicy n m)
    (g : Reward n m) (V : History n m → ℝ) (hn : ∀ h, 0 ≤ V h)
    (step : ∀ h i j, usedCapacity h ≤ T → i ∉ h.map (fun e => e.1) →
      g (i,j,usedCapacity h) + ∑ s : Fin (T+2), (I.sizeLaw i j s).toReal *
        (if usedCapacity h + s.val ≤ T then V (h ++ [(i,j,s.val)]) else 0) ≤ V h)
    (k : ℕ) (h : History n m) (hu : usedCapacity h ≤ T) :
    visits I π k h g ≤ V h := by
  induction k generalizing h with
  | zero => simpa [visits] using hn h
  | succ k ih =>
    rcases hp : π h with _ | ⟨i,j⟩
    · simpa [visits,hp] using hn h
    by_cases hf : i ∈ h.map (fun e => e.1)
    · simpa [visits,hp,hf] using hn h
    rw [visits_step I π g k h i j hp hf]
    refine le_trans (add_le_add_right ?_ _) (step h i j hu hf)
    apply Finset.sum_le_sum
    intro s _
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    split_ifs with hs
    · exact ih _ (by simpa only [used_next] using hs)
    · exact le_rfl

private lemma expectation_bound (p : PMF (Fin (T+2))) (z : Fin (T+2) → ℝ)
    (a : ℝ) (hz : ∀ s, z s ≤ a) : ∑ s, (p s).toReal * z s ≤ a := by
  calc
    _ ≤ ∑ s, (p s).toReal * a := Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (hz s) ENNReal.toReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, prob_total, one_mul]

private lemma cap_potential (I : Instance n m T) (π : AdaptivePolicy n m) (u k : ℕ) :
    visits I π k [] (fun z => if z.2.2 ≤ u then mu I z.1 z.2.1 u else 0) ≤ 2 * (u : ℝ) := by
  let budget (S : ℕ) : ℕ := if S ≤ u then 2*u-S else 0
  let V (h : History n m) : ℝ := budget (usedCapacity h)
  have step (h : History n m) (i : Fin n) (j : Fin m) (hu : usedCapacity h ≤ T)
      (_hf : i ∉ h.map (fun e => e.1)) :
      (if usedCapacity h ≤ u then mu I i j u else 0) +
      ∑ s : Fin (T+2), (I.sizeLaw i j s).toReal *
        (if usedCapacity h + s.val ≤ T then V (h ++ [(i,j,s.val)]) else 0) ≤ V h := by
    by_cases hs : usedCapacity h ≤ u
    · rw [if_pos hs]
      unfold mu truncMean
      rw [← Finset.sum_add_distrib]
      simp_rw [← mul_add]
      apply expectation_bound
      intro s
      change min (s.val : ℝ) u + (if _ then (budget (usedCapacity _) : ℝ) else 0) ≤ ↑(budget (usedCapacity h))
      simp only [used_next]
      rw [← Nat.cast_min]
      split_ifs with hf
      · exact_mod_cast (show min s.val u + budget (usedCapacity h + s.val) ≤ budget (usedCapacity h) by
          dsimp [budget]; split_ifs <;> omega)
      · simp only [add_zero]
        exact_mod_cast (show min s.val u ≤ budget (usedCapacity h) by simp [budget, hs]; omega)
    · rw [if_neg hs, zero_add]
      apply expectation_bound
      intro s
      simp [V, used_next, budget, hs, show ¬ usedCapacity h + s.val ≤ u by omega]
  have q := potential I π (fun z => if z.2.2 ≤ u then mu I z.1 z.2.1 u else 0) V
    (fun h => Nat.cast_nonneg _) step k [] (by simp [usedCapacity])
  simpa [V,usedCapacity,budget] using q

private lemma item_potential (I : Instance n m T) (π : AdaptivePolicy n m) (a : Fin n) (k : ℕ) :
    visits I π k [] (fun z => if z.2.2 ≤ T then (if z.1 = a then 1 else 0) else 0) ≤ 1 := by
  let V (h : History n m) : ℝ := if a ∈ h.map (fun e => e.1) then 0 else 1
  have step (h : History n m) (i : Fin n) (j : Fin m) (hu : usedCapacity h ≤ T)
      (hf : i ∉ h.map (fun e => e.1)) :
      (if usedCapacity h ≤ T then (if i = a then (1 : ℝ) else 0) else 0) +
      ∑ s : Fin (T+2), (I.sizeLaw i j s).toReal *
        (if usedCapacity h + s.val ≤ T then V (h ++ [(i,j,s.val)]) else 0) ≤ V h := by
    rw [if_pos hu]
    by_cases hi : i = a
    · subst i
      simp [V,hf]
    · rw [if_neg hi, zero_add]
      apply expectation_bound
      intro s
      simp only [V,List.map_append,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false,Ne.symm hi]
      split_ifs <;> norm_num
  have q := potential I π (fun z => if z.2.2 ≤ T then (if z.1 = a then 1 else 0) else 0) V
    (fun h => by dsimp [V]; split <;> norm_num) step k []
    (by simp [usedCapacity])
  simpa [V] using q

private lemma visits_nonneg (I : Instance n m T) (π : AdaptivePolicy n m) (g : Reward n m)
    (hg : ∀ z, 0 ≤ g z) (k : ℕ) (h : History n m) : 0 ≤ visits I π k h g := by
  induction k generalizing h with
  | zero => simp [visits]
  | succ k ih =>
    rcases hp : π h with _ | ⟨i,j⟩
    · simp [visits,hp]
    by_cases hf : i ∈ h.map (fun e => e.1)
    · simp [visits,hp,hf]
    rw [visits_step I π g k h i j hp hf]
    apply add_nonneg (hg _) (Finset.sum_nonneg _)
    intro s _
    apply mul_nonneg ENNReal.toReal_nonneg
    split_ifs <;> first | apply ih | exact le_rfl

private lemma value_eq (I : Instance n m T) (π : AdaptivePolicy n m) (k : ℕ)
    (h : History n m) (hu : usedCapacity h ≤ T) :
    adaptValueFrom I π k h =
      visits I π k h (fun z => if z.2.2 ≤ T then effWeight I z.1 z.2.1 z.2.2 else 0) := by
  induction k generalizing h with
  | zero => simp [adaptValueFrom, visits]
  | succ k ih =>
    rcases hp : π h with _ | ⟨i,j⟩
    · simp [adaptValueFrom,visits,hp]
    by_cases hf : i ∈ h.map (fun e => e.1)
    · simp [adaptValueFrom,visits,hp,hf]
    rw [visits_step I π _ k h i j hp hf]
    simp only [adaptValueFrom,hp,hf,if_false,hu,if_true]
    conv_rhs => enter [1]; unfold effWeight cdf
    rw [Finset.mul_sum]
    conv_rhs =>
      enter [1,2]
      rw [← one_mul (I.cost i j), ← prob_total (I.sizeLaw i j), Finset.sum_mul]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    have hm : (s.val : ℝ) ≤ (T : ℝ) - usedCapacity h ↔ usedCapacity h + s.val ≤ T := by
      rw [le_sub_iff_add_le, add_comm]
      exact_mod_cast Iff.rfl
    by_cases hs : usedCapacity h + s.val ≤ T
    · simp only [if_pos hs, if_pos (hm.mpr hs)]
      rw [ih _ (by simpa only [used_next] using hs)]
      ring
    · simp only [if_neg hs, if_neg (hm.not.mpr hs)]
      ring

end PandoraOccupation
open PandoraOccupation

theorem solution {n m T : ℕ} (I : Instance n m T) (_hI : IsValid I) (π : AdaptivePolicy n m) :
    ∃ x : LPArray n m, PsiFeasible I T x ∧ adaptValue I π ≤ psiObjective I T x := by
  let L := visits I π n []
  let x : LPArray n m := fun i j t => L (atom i j t)
  have nn (i : Fin n) (j : Fin m) (t : ℕ) : 0 ≤ x i j t :=
    visits_nonneg I π _ (fun z => by dsimp [atom]; split <;> norm_num) n []
  have item (a : Fin n) : ∑ j, ∑ t ∈ Finset.range (T+1), x a j t ≤ 1 := by
    have id := expand L T (fun z => if z.1 = a then (1:ℝ) else 0)
    simp [ite_mul,Finset.sum_ite_irrel] at id
    exact id.trans_le (item_potential I π a n)
  refine ⟨x, ⟨?_,item,?_⟩, ?_⟩
  · intro u _
    have id := expand L u (fun z => mu I z.1 z.2.1 u)
    simp only [mul_comm (mu I _ _ _)] at id
    exact id.trans_le (cap_potential I π u n)
  · intro i j t ht
    refine ⟨nn i j t, ?_⟩
    calc
      _ ≤ ∑ q ∈ Finset.range (T+1), x i j q :=
        Finset.single_le_sum (fun q _ => nn i j q) (Finset.mem_range.mpr (by omega))
      _ ≤ ∑ p, ∑ q ∈ Finset.range (T+1), x i p q :=
        Finset.single_le_sum (fun p _ => Finset.sum_nonneg (fun q _ => nn i p q)) (Finset.mem_univ j)
      _ ≤ 1 := item i
  · exact le_of_eq ((value_eq I π n [] (by simp [usedCapacity])).trans
      (expand L T (fun z => effWeight I z.1 z.2.1 z.2.2)).symm)
