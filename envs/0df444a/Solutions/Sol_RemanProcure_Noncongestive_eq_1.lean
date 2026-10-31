-- Prove2me | solution 1 for RemanProcure.Noncongestive.eq_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:18:54.672407+00:00
-- url     : https://prove2.me/submissions/1aa4a8cf-1c29-4edd-973e-1488de5712a5

import Mathlib
import Definitions.Def_RemanProcure_Noncongestive_Model

open RemanProcure.Noncongestive

lemma reman_fold_min_mono {K : ℕ} (s : Finset (Fin K)) (b c : ℝ) (f g : Fin K → ℝ)
    (hb : b ≤ c) (hfg : ∀ i, f i ≤ g i) : s.fold min b f ≤ s.fold min c g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hb
  | insert a s ha ih =>
    rw [Finset.fold_insert ha, Finset.fold_insert ha]
    exact min_le_min (hfg a) ih

lemma reman_fold_min_tendsto {K : ℕ} (s : Finset (Fin K)) (b : ℕ → ℝ) (b0 : ℝ)
    (F : ℕ → Fin K → ℝ) (F0 : Fin K → ℝ)
    (hb : Filter.Tendsto b Filter.atTop (nhds b0))
    (hF : ∀ i, Filter.Tendsto (fun n => F n i) Filter.atTop (nhds (F0 i))) :
    Filter.Tendsto (fun n => s.fold min (b n) (F n)) Filter.atTop (nhds (s.fold min b0 F0)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hb
  | insert a s ha ih =>
    simp only [Finset.fold_insert ha]
    exact (hF a).min ih

lemma reman_T_mono {K : ℕ} (P : Params K) (hP : Standing P) (v w : (Fin K → ℕ) → ℝ)
    (hvw : ∀ y, v y ≤ w y) : ∀ x, T P v x ≤ T P w x := by
  obtain ⟨-, hp, -, -, -, -, -, -, -, -, -, hμ, hlam, -⟩ := hP
  intro x
  unfold T T1 T2
  have h1 : min (v x) (P.cA + ∑ i, P.p i * v (x + e i))
      ≤ min (w x) (P.cA + ∑ i, P.p i * w (x + e i)) := by
    apply min_le_min (hvw x)
    have : ∑ i, P.p i * v (x + e i) ≤ ∑ i, P.p i * w (x + e i) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hvw _) (hp i)
    linarith
  have h2 := reman_fold_min_mono Finset.univ (v x + P.cL) (w x + P.cL)
    (fun i => if 0 < x i then v (x - e i) + P.r i else v x + P.cL)
    (fun i => if 0 < x i then w (x - e i) + P.r i else w x + P.cL)
    (by linarith [hvw x]) (fun i => by
      split_ifs
      · linarith [hvw (x - e i)]
      · linarith [hvw x])
  have := mul_le_mul_of_nonneg_left h1 hμ.le
  have := mul_le_mul_of_nonneg_left h2 hlam.le
  linarith

lemma reman_T_tendsto {K : ℕ} (P : Params K) (f : ℕ → (Fin K → ℕ) → ℝ) (g : (Fin K → ℕ) → ℝ)
    (hf : ∀ y, Filter.Tendsto (fun n => f n y) Filter.atTop (nhds (g y))) :
    ∀ x, Filter.Tendsto (fun n => T P (f n) x) Filter.atTop (nhds (T P g x)) := by
  intro x
  unfold T T1 T2
  refine ((Filter.Tendsto.const_mul _ ?_).add (Filter.Tendsto.const_mul _ ?_)).add_const _
  · refine (hf x).min (Filter.Tendsto.const_add _ ?_)
    exact tendsto_finset_sum _ fun i _ => (hf _).const_mul _
  · refine reman_fold_min_tendsto _ _ _ _ _ ((hf x).add_const _) fun i => ?_
    by_cases h : 0 < x i
    · simp only [h, if_true]; exact (hf _).add_const _
    · simp only [h, if_false]; exact (hf _).add_const _

theorem solution {K : ℕ} (P : Params K) (hP : Standing P) : (∀ x, Filter.Tendsto (fun n : ℕ => ((T P)^[n] 0) x) Filter.atTop (nhds (vstar P x))) ∧ (∀ x, vstar P x = P.μ * T1 P (vstar P) x + P.lam * T2 P (vstar P) x + hold P x) := by
  have hP' := hP
  obtain ⟨hK, hp, hpsum, -, hr0, -, hh, hrc, hcA, hα, -, hμ, hlam, hsum⟩ := hP
  have hcL : 0 ≤ P.cL := by
    have := hrc ⟨0, hK⟩; have := hr0 ⟨0, hK⟩; linarith
  have hhold : ∀ x, 0 ≤ hold P x := fun x =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hh i).le (Nat.cast_nonneg _)
  set u : (Fin K → ℕ) → ℝ := fun x => (hold P x + P.lam * P.cL) / P.α with hu
  have hu0 : ∀ x, 0 ≤ u x := fun x =>
    div_nonneg (by have := hhold x; nlinarith) hα.le
  have hTu : ∀ x, T P u x ≤ u x := by
    intro x
    unfold T T1 T2
    have h1 : min (u x) (P.cA + ∑ i, P.p i * u (x + e i)) ≤ u x := min_le_left _ _
    have h2 : Finset.univ.fold min (u x + P.cL)
        (fun i => if 0 < x i then u (x - e i) + P.r i else u x + P.cL) ≤ u x + P.cL := by
      rw [Finset.fold_min_le]; exact Or.inl le_rfl
    have hαu : P.α * u x = hold P x + P.lam * P.cL := by
      rw [hu]; field_simp
    have := mul_le_mul_of_nonneg_left h1 hμ.le
    have := mul_le_mul_of_nonneg_left h2 hlam.le
    have hsplit : u x = P.α * u x + P.lam * u x + P.μ * u x := by
      linear_combination (-(u x)) * hsum
    linarith
  -- bounded by u
  have hbound : ∀ n x, ((T P)^[n] 0) x ≤ u x := by
    intro n
    induction n with
    | zero => intro x; simpa using hu0 x
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      exact (reman_T_mono P hP' _ _ ih x).trans (hTu x)
  -- monotone
  have hT0 : ∀ x, (0 : (Fin K → ℕ) → ℝ) x ≤ T P 0 x := by
    intro x
    show (0:ℝ) ≤ T P 0 x
    unfold T T1 T2
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
    have h1 : 0 ≤ min (0:ℝ) P.cA := le_min le_rfl hcA
    have h2 : (0:ℝ) ≤ Finset.univ.fold min P.cL (fun i => if 0 < x i then P.r i else P.cL) := by
      rw [Finset.le_fold_min]
      refine ⟨hcL, fun i _ => ?_⟩
      split_ifs
      · exact hr0 i
      · exact hcL
    have := mul_nonneg hμ.le h1
    have := mul_nonneg hlam.le h2
    linarith [hhold x]
  have hmono : ∀ n x, ((T P)^[n] 0) x ≤ ((T P)^[n+1] 0) x := by
    intro n
    induction n with
    | zero => intro x; simpa using hT0 x
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply' (T P) (n+1)]
      exact reman_T_mono P hP' _ _ ih x
  have hconv : ∀ x, Filter.Tendsto (fun n : ℕ => ((T P)^[n] 0) x) Filter.atTop
      (nhds (vstar P x)) := by
    intro x
    have hm : Monotone (fun n : ℕ => ((T P)^[n] 0) x) := monotone_nat_of_le_succ fun n => hmono n x
    have hbdd : BddAbove (Set.range (fun n : ℕ => ((T P)^[n] 0) x)) :=
      ⟨u x, by rintro _ ⟨n, rfl⟩; exact hbound n x⟩
    have ht := tendsto_atTop_ciSup hm hbdd
    unfold vstar
    rwa [ht.limUnder_eq]
  refine ⟨hconv, fun x => ?_⟩
  have h1 : Filter.Tendsto (fun n : ℕ => T P ((T P)^[n] 0) x) Filter.atTop (nhds (T P (vstar P) x)) :=
    reman_T_tendsto P _ _ hconv x
  have h2 : Filter.Tendsto (fun n : ℕ => T P ((T P)^[n] 0) x) Filter.atTop (nhds (vstar P x)) := by
    have := (hconv x).comp (Filter.tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp [Function.comp, Function.iterate_succ_apply']
  have := tendsto_nhds_unique h2 h1
  rw [this]; rfl
