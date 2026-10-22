-- Prove2me | solution 1 for OnlinePrimalDual.Framework.algorithm1_competitive_ratio_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:46:53.911708+00:00
-- url     : https://prove2.me/submissions/9534ef84-8960-412b-a290-eae70dc64618

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum
import Definitions.Def_OnlinePrimalDual_Framework_alg1Run_v2



namespace OnlinePrimalDual.Framework

section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma a1_step_mem (inst : CoveringInstance I J) (j : J) (y : I → ℝ) (i : I) (hi : i ∈ inst.S j) :
    alg1Step inst j y i = y i * (1 + 1 / inst.c i) + 1 / ((inst.S j).card * inst.c i) := by
  unfold alg1Step; rw [if_pos hi]

lemma a1_step_notmem (inst : CoveringInstance I J) (j : J) (y : I → ℝ) (i : I) (hi : i ∉ inst.S j) :
    alg1Step inst j y i = y i := by
  unfold alg1Step; rw [if_neg hi]

lemma a1_step_nonneg (inst : CoveringInstance I J) (j : J) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ alg1Step inst j x i := by
  intro i
  have hc := inst.hc_pos i
  unfold alg1Step
  split_ifs
  · have := hx i; positivity
  · exact hx i

lemma a1_iter_nonneg (inst : CoveringInstance I J) (j : J) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ m, ∀ i, 0 ≤ (alg1Step inst j)^[m] x i := by
  intro m
  induction m with
  | zero => simpa using hx
  | succ m ih => rw [Function.iterate_succ_apply']; exact a1_step_nonneg inst j _ ih

lemma a1_step_ge (inst : CoveringInstance I J) (j : J) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) (i : I) :
    x i ≤ alg1Step inst j x i := by
  have hc := inst.hc_pos i
  unfold alg1Step
  split_ifs
  · have := hx i
    have : 0 ≤ x i * (1 / inst.c i) := by positivity
    have : 0 ≤ 1 / ((inst.S j).card * inst.c i) := by positivity
    nlinarith
  · exact le_rfl

lemma a1_iter_ge (inst : CoveringInstance I J) (j : J) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ m, ∀ i, x i ≤ (alg1Step inst j)^[m] x i := by
  intro m
  induction m with
  | zero => intro i; simp
  | succ m ih =>
    intro i
    rw [Function.iterate_succ_apply']
    exact (ih i).trans (a1_step_ge inst j _ (a1_iter_nonneg inst j x hx m) i)

lemma a1_iter_notmem (inst : CoveringInstance I J) (j : J) (x : I → ℝ) :
    ∀ m, ∀ i, i ∉ inst.S j → (alg1Step inst j)^[m] x i = x i := by
  intro m
  induction m with
  | zero => intro i _; simp
  | succ m ih =>
    intro i hi
    rw [Function.iterate_succ_apply', a1_step_notmem inst j _ i hi]; exact ih i hi

lemma a1_iter_grow (inst : CoveringInstance I J) (j : J) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i)
    (i0 : I) (hi0 : i0 ∈ inst.S j) :
    ∀ m : ℕ, (m : ℝ) / ((inst.S j).card * inst.c i0) ≤ (alg1Step inst j)^[m] x i0 := by
  intro m
  have hcard : (0:ℝ) < (inst.S j).card := by exact_mod_cast Finset.card_pos.mpr ⟨i0, hi0⟩
  have hc := inst.hc_pos i0
  induction m with
  | zero => simp [hx i0]
  | succ m ih =>
    rw [Function.iterate_succ_apply', a1_step_mem inst j _ i0 hi0]
    have h1 : 0 ≤ (alg1Step inst j)^[m] x i0 * (1 / inst.c i0) :=
      mul_nonneg (a1_iter_nonneg inst j x hx m i0) (by positivity)
    push_cast
    have : ((m:ℝ) + 1) / ((inst.S j).card * inst.c i0) =
      (m:ℝ) / ((inst.S j).card * inst.c i0) + 1 / ((inst.S j).card * inst.c i0) := by ring
    rw [this]
    have h2 : (alg1Step inst j)^[m] x i0 * (1 + 1 / inst.c i0) =
      (alg1Step inst j)^[m] x i0 + (alg1Step inst j)^[m] x i0 * (1 / inst.c i0) := by ring
    rw [h2]
    linarith

lemma a1_count_spec (inst : CoveringInstance I J) (j : J) (hSj : (inst.S j).Nonempty)
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    1 ≤ ∑ i ∈ inst.S j, (alg1Step inst j)^[alg1Count inst j x] x i ∧
    ∀ k < alg1Count inst j x, ∑ i ∈ inst.S j, (alg1Step inst j)^[k] x i < 1 := by
  have hne : {k : ℕ | 1 ≤ ∑ i ∈ inst.S j, (alg1Step inst j)^[k] x i}.Nonempty := by
    obtain ⟨i0, hi0⟩ := hSj
    have hcard : (0:ℝ) < (inst.S j).card := by exact_mod_cast Finset.card_pos.mpr ⟨i0, hi0⟩
    have hc := inst.hc_pos i0
    refine ⟨⌈((inst.S j).card : ℝ) * inst.c i0⌉₊, ?_⟩
    show 1 ≤ ∑ i ∈ inst.S j, (alg1Step inst j)^[⌈((inst.S j).card : ℝ) * inst.c i0⌉₊] x i
    have h1 := a1_iter_grow inst j x hx i0 hi0 ⌈((inst.S j).card : ℝ) * inst.c i0⌉₊
    have h2 : 1 ≤ (⌈((inst.S j).card : ℝ) * inst.c i0⌉₊ : ℝ) / ((inst.S j).card * inst.c i0) := by
      rw [le_div_iff₀ (by positivity)]
      simpa using Nat.le_ceil (((inst.S j).card : ℝ) * inst.c i0)
    calc (1:ℝ) ≤ _ := h2.trans h1
      _ ≤ _ := Finset.single_le_sum (f := fun i => (alg1Step inst j)^[⌈((inst.S j).card : ℝ) * inst.c i0⌉₊] x i)
            (fun i _ => a1_iter_nonneg inst j x hx _ i) hi0
  refine ⟨Nat.sInf_mem hne, ?_⟩
  intro k hk
  have := Nat.notMem_of_lt_sInf hk
  simpa [alg1Count] using this

lemma a1_potential_step (inst : CoveringInstance I J) (j : J) (hSj : (inst.S j).Nonempty)
    (x : I → ℝ) :
    ∑ i, inst.c i * alg1Step inst j x i = ∑ i, inst.c i * x i + (∑ i ∈ inst.S j, x i + 1) := by
  have hcard : (0:ℝ) < (inst.S j).card := by exact_mod_cast Finset.card_pos.mpr hSj
  have hdiff : ∑ i, inst.c i * alg1Step inst j x i - ∑ i, inst.c i * x i =
      ∑ i ∈ inst.S j, (inst.c i * alg1Step inst j x i - inst.c i * x i) := by
    rw [← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    unfold alg1Step
    rw [if_neg hi]; ring
  have hterm : ∀ i ∈ inst.S j, inst.c i * alg1Step inst j x i - inst.c i * x i =
      x i + 1 / (inst.S j).card := by
    intro i hi
    have hc := inst.hc_pos i
    unfold alg1Step
    rw [if_pos hi]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib] at hdiff
  simp only [Finset.sum_const, nsmul_eq_mul] at hdiff
  have : (inst.S j).card * (1 / ((inst.S j).card : ℝ)) = 1 := by field_simp
  linarith

lemma a1_potential (inst : CoveringInstance I J) (j : J) (hSj : (inst.S j).Nonempty)
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ m ≤ alg1Count inst j x, ∑ i, inst.c i * (alg1Step inst j)^[m] x i ≤
      ∑ i, inst.c i * x i + 2 * m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := (a1_count_spec inst j hSj x hx).2 m (by omega)
    rw [Function.iterate_succ_apply', a1_potential_step inst j hSj]
    push_cast
    linarith

lemma a1_upper (inst : CoveringInstance I J) (hc1 : ∀ i, 1 ≤ inst.c i) (j : J)
    (hSj : (inst.S j).Nonempty) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) (hx3 : ∀ i, x i ≤ 3) :
    ∀ m ≤ alg1Count inst j x, ∀ i, (alg1Step inst j)^[m] x i ≤ 3 := by
  intro m
  induction m with
  | zero => intro _ i; simpa using hx3 i
  | succ m ih =>
    intro hm i
    rw [Function.iterate_succ_apply']
    by_cases hi : i ∈ inst.S j
    · have h2 := (a1_count_spec inst j hSj x hx).2 m (by omega)
      have hxi : (alg1Step inst j)^[m] x i < 1 :=
        lt_of_le_of_lt (Finset.single_le_sum (f := fun i => (alg1Step inst j)^[m] x i)
          (fun i _ => a1_iter_nonneg inst j x hx m i) hi) h2
      have hnn := a1_iter_nonneg inst j x hx m i
      have hcard : (1:ℝ) ≤ (inst.S j).card := by exact_mod_cast Finset.card_pos.mpr hSj
      have hc := inst.hc_pos i
      have hc1i := hc1 i
      rw [a1_step_mem inst j _ i hi]
      have h3 : 1 / ((inst.S j).card * inst.c i) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith
      have h4 : 1 / inst.c i ≤ 1 := by rw [div_le_one hc]; exact hc1i
      have h5 : (alg1Step inst j)^[m] x i * (1 + 1 / inst.c i) ≤ 2 := by
        have : 1 + 1 / inst.c i ≤ 2 := by linarith
        nlinarith
      linarith
    · rw [a1_step_notmem inst j _ i hi, a1_iter_notmem inst j x m i hi]
      exact hx3 i

lemma a1_lower (inst : CoveringInstance I J) (hc1 : ∀ i, 1 ≤ inst.c i) (j : J)
    (hSj : (inst.S j).Nonempty) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ m : ℕ, ∀ i ∈ inst.S j, (x i + 1 / inst.d) * (2:ℝ) ^ ((m:ℝ) / inst.c i) ≤
      (alg1Step inst j)^[m] x i + 1 / inst.d := by
  intro m
  induction m with
  | zero => intro i _; simp
  | succ m ih =>
    intro i hi
    have hcard : (1:ℝ) ≤ (inst.S j).card := by exact_mod_cast Finset.card_pos.mpr hSj
    have hc := inst.hc_pos i
    have hc1i := hc1 i
    have hd := inst.hd_pos
    have hcd : ((inst.S j).card : ℝ) ≤ inst.d := inst.hd_bound j
    have hnn := a1_iter_nonneg inst j x hx m i
    have hxnn := hx i
    set w := (alg1Step inst j)^[m] x i with hw
    have ih' := ih i hi
    rw [Function.iterate_succ_apply', a1_step_mem inst j _ i hi]
    rw [← hw]
    have hB : (2:ℝ) ^ (1 / inst.c i) ≤ 1 + 1 / inst.c i := by
      have := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) (p := 1 / inst.c i)
        (by positivity) (by rw [div_le_one hc]; exact hc1i)
      norm_num at this
      simpa only [one_div] using this
    have hpow : (2:ℝ) ^ (((m + 1 : ℕ) : ℝ) / inst.c i) =
        (2:ℝ) ^ ((m:ℝ) / inst.c i) * (2:ℝ) ^ (1 / inst.c i) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; push_cast; ring
    rw [hpow]
    have h1 : 1 / (inst.d * inst.c i) ≤ 1 / ((inst.S j).card * inst.c i) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_right hcd hc.le
    have hp2 : 0 < (2:ℝ) ^ ((m:ℝ) / inst.c i) := by positivity
    have h2 : (w + 1 / inst.d) * (1 + 1 / inst.c i) ≤
        w * (1 + 1 / inst.c i) + 1 / ((inst.S j).card * inst.c i) + 1 / inst.d := by
      have : (w + 1 / inst.d) * (1 + 1 / inst.c i) =
          w * (1 + 1 / inst.c i) + 1 / (inst.d * inst.c i) + 1 / inst.d := by
        field_simp
        ring
      linarith
    have hwd : 0 ≤ w + 1 / inst.d := by positivity
    calc (x i + 1 / inst.d) * ((2:ℝ) ^ ((m:ℝ) / inst.c i) * (2:ℝ) ^ (1 / inst.c i))
        = ((x i + 1 / inst.d) * (2:ℝ) ^ ((m:ℝ) / inst.c i)) * (2:ℝ) ^ (1 / inst.c i) := by ring
      _ ≤ (w + 1 / inst.d) * (2:ℝ) ^ (1 / inst.c i) :=
          mul_le_mul_of_nonneg_right ih' (by positivity)
      _ ≤ (w + 1 / inst.d) * (1 + 1 / inst.c i) := mul_le_mul_of_nonneg_left hB hwd
      _ ≤ _ := h2

end

section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma dualSum_update_H46 (inst : CoveringInstance I J) (y : J → ℝ) (j : J) (hj : y j = 0)
    (t : ℝ) (i : I) :
    dualSum inst (Function.update y j t) i = dualSum inst y i + (if i ∈ inst.S j then t else 0) := by
  unfold dualSum
  by_cases h : i ∈ inst.S j
  · have hmem : j ∈ Finset.univ.filter (fun j => i ∈ inst.S j) := by simp [h]
    rw [if_pos h, Finset.sum_update_of_mem hmem]
    rw [← Finset.add_sum_erase _ y hmem, hj, Finset.sdiff_singleton_eq_erase]
    ring
  · have hmem : j ∉ Finset.univ.filter (fun j => i ∈ inst.S j) := by simp [h]
    rw [if_neg h, Finset.sum_update_of_notMem hmem]
    ring

lemma weak_dual_gen_H46 (inst : CoveringInstance I J) (lam : ℝ) (y : J → ℝ) (x : I → ℝ)
    (hy : ∀ j, 0 ≤ y j)
    (hx0 : ∀ i, 0 ≤ x i) (hcov : ∀ j, 1 ≤ ∑ i ∈ inst.S j, x i)
    (hfeas : ∀ i, dualSum inst y i ≤ lam * inst.c i) :
    ∑ j, y j ≤ lam * ∑ i, inst.c i * x i := by
  calc ∑ j, y j ≤ ∑ j, y j * ∑ i ∈ inst.S j, x i :=
        Finset.sum_le_sum (fun j _ => by nlinarith [hy j, hcov j])
    _ = ∑ j, ∑ i, (if i ∈ inst.S j then y j * x i else 0) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum, ← Finset.sum_filter]
        simp
    _ = ∑ i, ∑ j, (if i ∈ inst.S j then y j * x i else 0) := Finset.sum_comm
    _ = ∑ i, x i * dualSum inst y i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        unfold dualSum
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        split_ifs <;> ring
    _ ≤ ∑ i, x i * (lam * inst.c i) :=
        Finset.sum_le_sum (fun i _ => by nlinarith [hx0 i, hfeas i])
    _ = lam * ∑ i, inst.c i * x i := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_); ring

def Inv1_H46 (inst : CoveringInstance I J) (x : I → ℝ) (y : J → ℕ) (rem : List J) : Prop :=
  (∀ j ∈ rem, y j = 0) ∧ (∀ i, 0 ≤ x i ∧ x i ≤ 3) ∧
  (∀ j, j ∉ rem → 1 ≤ ∑ i ∈ inst.S j, x i) ∧
  (∀ i, (1 / inst.d) * (2:ℝ) ^ (dualSum inst (fun k => (y k : ℝ)) i / inst.c i) ≤ x i + 1 / inst.d) ∧
  ∑ i, inst.c i * x i ≤ 2 * ∑ k, (y k : ℝ)

lemma inv1_fold_H46 (inst : CoveringInstance I J) (hc1 : ∀ i, 1 ≤ inst.c i)
    (hS : ∀ j, (inst.S j).Nonempty) :
    ∀ (rem : List J) (st : (I → ℝ) × (J → ℕ)), rem.Nodup → Inv1_H46 inst st.1 st.2 rem →
    Inv1_H46 inst (rem.foldl
      (fun st j => ((alg1Step inst j)^[alg1Count inst j st.1] st.1,
        Function.update st.2 j (alg1Count inst j st.1))) st).1
      (rem.foldl
      (fun st j => ((alg1Step inst j)^[alg1Count inst j st.1] st.1,
        Function.update st.2 j (alg1Count inst j st.1))) st).2 [] := by
  intro rem
  induction rem with
  | nil => intro st _ h; exact h
  | cons j l ih =>
    intro st hnd hinv
    obtain ⟨x, y⟩ := st
    obtain ⟨h0, hx, hcov, hlow, hP⟩ := hinv
    simp only at h0 hx hcov hlow hP
    have hj : y j = 0 := h0 j (List.mem_cons_self ..)
    have hnd' := List.nodup_cons.mp hnd
    simp only [List.foldl_cons]
    refine ih _ hnd'.2 ?_
    simp only
    set cnt := alg1Count inst j x with hcnt
    have hx0 : ∀ i, 0 ≤ x i := fun i => (hx i).1
    have hx3 : ∀ i, x i ≤ 3 := fun i => (hx i).2
    obtain ⟨hspec1, _⟩ := a1_count_spec inst j (hS j) x hx0
    have hcast : (fun k => ((Function.update y j cnt k : ℕ) : ℝ)) =
        Function.update (fun k => (y k : ℝ)) j (cnt : ℝ) := by
      funext k
      by_cases hk : k = j
      · subst hk; simp
      · simp [Function.update_of_ne hk]
    have hjR : (fun k => (y k : ℝ)) j = 0 := by simp [hj]
    have hDy : ∀ i, dualSum inst (fun k => ((Function.update y j cnt k : ℕ) : ℝ)) i =
        dualSum inst (fun k => (y k : ℝ)) i + (if i ∈ inst.S j then (cnt:ℝ) else 0) := by
      intro i; rw [hcast]; exact dualSum_update_H46 inst _ j hjR _ i
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      have hkj : k ≠ j := fun h => hnd'.1 (h ▸ hk)
      simp [Function.update_of_ne hkj, h0 k (List.mem_cons_of_mem _ hk)]
    · intro i
      exact ⟨a1_iter_nonneg inst j x hx0 cnt i, a1_upper inst hc1 j (hS j) x hx0 hx3 cnt le_rfl i⟩
    · intro k hk
      by_cases hkj : k = j
      · subst hkj; exact hspec1
      · have hk' : k ∉ j :: l := by
          intro hm
          rcases List.mem_cons.mp hm with h | h
          · exact hkj h
          · exact hk h
        exact (hcov k hk').trans (Finset.sum_le_sum (fun i _ => a1_iter_ge inst j x hx0 cnt i))
    · intro i
      rw [hDy]
      by_cases hi : i ∈ inst.S j
      · rw [if_pos hi]
        have hc := inst.hc_pos i
        have hd := inst.hd_pos
        have hl := a1_lower inst hc1 j (hS j) x hx0 cnt i hi
        have := hlow i
        rw [add_div, Real.rpow_add (by norm_num)]
        calc 1 / inst.d * ((2:ℝ) ^ (dualSum inst (fun k => (y k : ℝ)) i / inst.c i) *
              (2:ℝ) ^ ((cnt:ℝ) / inst.c i))
            = (1 / inst.d * (2:ℝ) ^ (dualSum inst (fun k => (y k : ℝ)) i / inst.c i)) *
              (2:ℝ) ^ ((cnt:ℝ) / inst.c i) := by ring
          _ ≤ (x i + 1 / inst.d) * (2:ℝ) ^ ((cnt:ℝ) / inst.c i) :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ ≤ _ := hl
      · rw [if_neg hi, add_zero, a1_iter_notmem inst j x cnt i hi]
        exact hlow i
    · have hsum : ∑ k, ((Function.update y j cnt k : ℕ) : ℝ) = (cnt:ℝ) + ∑ k, (y k : ℝ) := by
        have := congrArg (fun f => ∑ k, f k) hcast
        simp only at this
        rw [this, Finset.sum_update_of_mem (Finset.mem_univ j)]
        rw [Finset.sdiff_singleton_eq_erase]
        have h2 := Finset.add_sum_erase Finset.univ (fun k => (y k : ℝ)) (Finset.mem_univ j)
        simp only [hj, Nat.cast_zero, zero_add] at h2
        linarith
      rw [hsum]
      have := a1_potential inst j (hS j) x hx0 cnt le_rfl
      linarith

theorem alg1_core_H46 (inst : CoveringInstance I J) (hc1 : ∀ i, 1 ≤ inst.c i)
    (hS : ∀ j, (inst.S j).Nonempty) (ord : List J)
    (hord_nodup : ord.Nodup) (hord_mem : ∀ j, j ∈ ord) :
    let x : I → ℝ := (alg1Run inst ord).1
    let y : J → ℝ := fun j => ((alg1Run inst ord).2 j : ℝ)
    (∀ j, 1 ≤ ∑ i ∈ inst.S j, x i) ∧
    (∀ i : I, dualSum inst y i ≤ inst.c i * Real.logb 2 (3 * inst.d + 1)) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * x i ≤ 2 * Real.logb 2 (3 * inst.d + 1) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * ∑ j, y j) := by
  intro x y
  have hinit : Inv1_H46 inst (fun _ => (0:ℝ)) (fun _ => (0:ℕ)) ord := by
    refine ⟨fun _ _ => rfl, fun i => ⟨le_rfl, by norm_num⟩, fun j hj => absurd (hord_mem j) hj,
      ?_, by simp⟩
    intro i
    have : dualSum inst (fun k => (((fun _ => (0:ℕ)) k : ℕ) : ℝ)) i = 0 := by simp [dualSum]
    rw [this]; simp
  have hfin : Inv1_H46 inst x (alg1Run inst ord).2 [] :=
    inv1_fold_H46 inst hc1 hS ord ((fun _ => (0:ℝ)), (fun _ => (0:ℕ))) hord_nodup hinit
  obtain ⟨_, hx, hcov0, hlow, hP⟩ := hfin
  have hcov : ∀ j, 1 ≤ ∑ i ∈ inst.S j, x i := fun j => hcov0 j (by simp)
  have hd := inst.hd_pos
  have hlam : 0 < Real.logb 2 (3 * inst.d + 1) :=
    Real.logb_pos (by norm_num) (by linarith)
  have hx0 : ∀ i, 0 ≤ x i := fun i => (hx i).1
  have hy0 : ∀ j, 0 ≤ y j := fun j => Nat.cast_nonneg _
  have hdual : ∀ i : I, dualSum inst y i ≤ inst.c i * Real.logb 2 (3 * inst.d + 1) := by
    intro i
    have hc := inst.hc_pos i
    have h1 := hlow i
    have h2 := (hx i).2
    have h3 : (2:ℝ) ^ (dualSum inst y i / inst.c i) ≤ 3 * inst.d + 1 := by
      have : 1 / inst.d * (2:ℝ) ^ (dualSum inst y i / inst.c i) ≤ 3 + 1 / inst.d := by linarith
      rw [one_div, inv_mul_le_iff₀ hd] at this
      have h4 : inst.d * (3 + (inst.d)⁻¹) = 3 * inst.d + 1 := by field_simp
      linarith
    have h5 : dualSum inst y i / inst.c i ≤ Real.logb 2 (3 * inst.d + 1) :=
      (Real.le_logb_iff_rpow_le (by norm_num) (by linarith)).mpr h3
    rw [div_le_iff₀ hc] at h5
    linarith
  refine ⟨hcov, hdual, ?_, ?_⟩
  · intro x'' hx''0 hx''cov
    have := weak_dual_gen_H46 inst (Real.logb 2 (3 * inst.d + 1)) y x'' hy0 hx''0 hx''cov
      (fun i => by have := hdual i; linarith)
    calc ∑ i, inst.c i * x i ≤ 2 * ∑ j, y j := hP
      _ ≤ _ := by nlinarith
  · intro y'' hy''0 hy''D
    have := weak_dual_gen_H46 inst 1 y'' x hy''0 hx0 hcov (fun i => by simpa using hy''D i)
    calc ∑ j, y'' j ≤ 1 * ∑ i, inst.c i * x i := this
      _ ≤ _ := by linarith

end

end OnlinePrimalDual.Framework

open OnlinePrimalDual.Framework


theorem solution {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (inst : CoveringInstance I J) (hc1 : ∀ i, 1 ≤ inst.c i)
    (hS : ∀ j, (inst.S j).Nonempty) (ord : List J)
    (hord_nodup : ord.Nodup) (hord_mem : ∀ j, j ∈ ord) :
    let x : I → ℝ := (alg1Run inst ord).1
    let y : J → ℝ := fun j => ((alg1Run inst ord).2 j : ℝ)
    (∀ j, 1 ≤ ∑ i ∈ inst.S j, x i) ∧
    (∀ i : I, dualSum inst y i ≤ inst.c i * Real.logb 2 (3 * inst.d + 1)) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * x i ≤ 2 * Real.logb 2 (3 * inst.d + 1) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * ∑ j, y j) := by
  exact alg1_core_H46 inst hc1 hS ord hord_nodup hord_mem
