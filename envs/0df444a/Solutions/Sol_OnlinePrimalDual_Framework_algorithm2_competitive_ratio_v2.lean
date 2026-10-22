-- Prove2me | solution 1 for OnlinePrimalDual.Framework.algorithm2_competitive_ratio_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:42:54.877002+00:00
-- url     : https://prove2.me/submissions/862d91eb-008e-437c-b9db-7b50f1b54397

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum
import Definitions.Def_OnlinePrimalDual_Framework_alg2X
import Definitions.Def_OnlinePrimalDual_Framework_raiseRun_v2



namespace OnlinePrimalDual.Framework

lemma stop_lemma_H46 (G : ℝ → ℝ) (hc : Continuous G)
    (hne : ∃ s, 0 ≤ s ∧ 1 ≤ G s) :
    0 ≤ sInf {s : ℝ | 0 ≤ s ∧ 1 ≤ G s} ∧ 1 ≤ G (sInf {s : ℝ | 0 ≤ s ∧ 1 ≤ G s}) ∧
      (0 < sInf {s : ℝ | 0 ≤ s ∧ 1 ≤ G s} → G (sInf {s : ℝ | 0 ≤ s ∧ 1 ≤ G s}) ≤ 1) := by
  set A : Set ℝ := {s : ℝ | 0 ≤ s ∧ 1 ≤ G s} with hA
  have hne' : A.Nonempty := hne
  have hbdd : BddBelow A := ⟨0, fun s hs => hs.1⟩
  have hcl : IsClosed A := by
    have : A = Set.Ici 0 ∩ G ⁻¹' Set.Ici 1 := by
      ext s; simp [hA]
    rw [this]
    exact isClosed_Ici.inter (isClosed_Ici.preimage hc)
  have hmem : sInf A ∈ A := hcl.csInf_mem hne' hbdd
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro hpos
  by_contra hgt
  push_neg at hgt
  have hopen : IsOpen {s | 1 < G s} := isOpen_lt continuous_const hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hgt
  set s0 := sInf A
  have h1 : 0 ≤ max 0 (s0 - ε / 2) := le_max_left _ _
  have h2 : max 0 (s0 - ε / 2) < s0 := max_lt hpos (by linarith)
  have h3 : max 0 (s0 - ε / 2) ∈ Metric.ball s0 ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · have := le_max_right 0 (s0 - ε / 2); linarith
    · linarith
  have h4 : 1 < G (max 0 (s0 - ε / 2)) := hball h3
  have h5 : max 0 (s0 - ε / 2) ∈ A := ⟨h1, h4.le⟩
  have := csInf_le hbdd h5
  linarith

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

lemma dualSum_nonneg_H46 (inst : CoveringInstance I J) (y : J → ℝ) (hy : ∀ j, 0 ≤ y j) (i : I) :
    0 ≤ dualSum inst y i :=
  Finset.sum_nonneg (fun j _ => hy j)

lemma dualSum_mono_H46 (inst : CoveringInstance I J) (y y' : J → ℝ) (h : ∀ j, y j ≤ y' j) (i : I) :
    dualSum inst y i ≤ dualSum inst y' i :=
  Finset.sum_le_sum (fun j _ => h j)

lemma Lpos_H46 (inst : CoveringInstance I J) : 0 < Real.log (1 + inst.d) :=
  Real.log_pos (by linarith [inst.hd_pos])

lemma alg2X_nonneg_H46 (inst : CoveringInstance I J) (y : J → ℝ) (i : I)
    (h : 0 ≤ dualSum inst y i) : 0 ≤ alg2X inst y i := by
  unfold alg2X
  have hL := Lpos_H46 inst
  have hc := inst.hc_pos i
  have hd := inst.hd_pos
  have : 1 ≤ Real.exp (Real.log (1 + inst.d) / inst.c i * dualSum inst y i) :=
    Real.one_le_exp (by positivity)
  have : 0 ≤ 1 / inst.d := by positivity
  nlinarith

lemma alg2X_mono_H46 (inst : CoveringInstance I J) (y y' : J → ℝ) (i : I)
    (h : dualSum inst y i ≤ dualSum inst y' i) : alg2X inst y i ≤ alg2X inst y' i := by
  unfold alg2X
  have hL := Lpos_H46 inst
  have hc := inst.hc_pos i
  have hd := inst.hd_pos
  have h1 : Real.exp (Real.log (1 + inst.d) / inst.c i * dualSum inst y i) ≤
      Real.exp (Real.log (1 + inst.d) / inst.c i * dualSum inst y' i) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h (by positivity))
  have : 0 ≤ 1 / inst.d := by positivity
  nlinarith

lemma weak_dual_H46 (inst : CoveringInstance I J) (y : J → ℝ) (x : I → ℝ) (hy : ∀ j, 0 ≤ y j)
    (hx0 : ∀ i, 0 ≤ x i) (hcov : ∀ j, 1 ≤ ∑ i ∈ inst.S j, x i)
    (hfeas : ∀ i, dualSum inst y i ≤ inst.c i) :
    ∑ j, y j ≤ ∑ i, inst.c i * x i := by
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
    _ ≤ ∑ i, inst.c i * x i :=
        Finset.sum_le_sum (fun i _ => by nlinarith [hx0 i, hfeas i])

/-- the single step -/
lemma alg2_step_H46 (inst : CoveringInstance I J) (y : J → ℝ) (j : J) (hSj : (inst.S j).Nonempty)
    (hj : y j = 0) (hy : ∀ j, 0 ≤ y j) (hD : ∀ i, dualSum inst y i ≤ inst.c i) :
    let s := raiseAmount inst (alg2X inst) y j
    let y' := Function.update y j s
    0 ≤ s ∧ 1 ≤ ∑ i ∈ inst.S j, alg2X inst y' i ∧ (∀ i, dualSum inst y' i ≤ inst.c i) ∧
      ∑ i, inst.c i * alg2X inst y' i ≤ ∑ i, inst.c i * alg2X inst y i
        + 2 * Real.log (1 + inst.d) * s := by
  intro s y'
  set L := Real.log (1 + inst.d) with hLdef
  have hL : 0 < L := Lpos_H46 inst
  have hdpos := inst.hd_pos
  let G : ℝ → ℝ := fun t => ∑ i ∈ inst.S j, alg2X inst (Function.update y j t) i
  have hGdef : ∀ t, G t = ∑ i ∈ inst.S j,
      (1 / inst.d) * (Real.exp (L / inst.c i * (dualSum inst y i + t)) - 1) := by
    intro t
    refine Finset.sum_congr rfl (fun i hi => ?_)
    unfold alg2X
    rw [dualSum_update_H46 inst y j hj t i, if_pos hi]
  have hGc : Continuous G := by
    have : G = fun t => ∑ i ∈ inst.S j,
      (1 / inst.d) * (Real.exp (L / inst.c i * (dualSum inst y i + t)) - 1) := funext hGdef
    rw [this]
    fun_prop
  have hne : ∃ s, 0 ≤ s ∧ 1 ≤ G s := by
    obtain ⟨i0, hi0⟩ := hSj
    have hc0 := inst.hc_pos i0
    refine ⟨inst.d * inst.c i0 / L, by positivity, ?_⟩
    rw [hGdef]
    have hterm : ∀ i ∈ inst.S j, 0 ≤ (1 / inst.d) * (Real.exp (L / inst.c i *
        (dualSum inst y i + inst.d * inst.c i0 / L)) - 1) := by
      intro i hi
      have hc := inst.hc_pos i
      have h1 : 1 ≤ Real.exp (L / inst.c i * (dualSum inst y i + inst.d * inst.c i0 / L)) :=
        Real.one_le_exp (by
          have := dualSum_nonneg_H46 inst y hy i
          positivity)
      have : 0 ≤ 1 / inst.d := by positivity
      nlinarith
    calc (1:ℝ) ≤ (1 / inst.d) * (Real.exp (L / inst.c i0 *
        (dualSum inst y i0 + inst.d * inst.c i0 / L)) - 1) := by
          have hD0 := dualSum_nonneg_H46 inst y hy i0
          have h1 := Real.add_one_le_exp (L / inst.c i0 *
            (dualSum inst y i0 + inst.d * inst.c i0 / L))
          have h2 : L / inst.c i0 * (inst.d * inst.c i0 / L) = inst.d := by
            field_simp
          have h3 : 0 ≤ L / inst.c i0 * dualSum inst y i0 := by positivity
          have h4 : inst.d ≤ Real.exp (L / inst.c i0 *
            (dualSum inst y i0 + inst.d * inst.c i0 / L)) - 1 := by
            rw [mul_add, h2] at h1 ⊢
            linarith
          rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hdpos]
          linarith
      _ ≤ _ := Finset.single_le_sum hterm hi0
  obtain ⟨hs0, hs1, hs2⟩ := stop_lemma_H46 G hGc hne
  have hsdef : s = sInf {s : ℝ | 0 ≤ s ∧ 1 ≤ G s} := rfl
  rw [← hsdef] at hs0 hs1 hs2
  have hG_s : G s = ∑ i ∈ inst.S j, alg2X inst y' i := rfl
  -- nonnegativity of new D
  have hy' : ∀ k, 0 ≤ y' k := by
    intro k
    by_cases hk : k = j
    · subst hk; simp [y', hs0]
    · simp [y', hk, hy k]
  have hDy' : ∀ i, dualSum inst y' i = dualSum inst y i + (if i ∈ inst.S j then s else 0) :=
    fun i => dualSum_update_H46 inst y j hj s i
  have hxnn : ∀ i, 0 ≤ alg2X inst y' i := fun i =>
    alg2X_nonneg_H46 inst y' i (dualSum_nonneg_H46 inst y' hy' i)
  -- bound when s > 0
  have hbound : 0 < s → ∑ i ∈ inst.S j, alg2X inst y' i ≤ 1 := fun h => hG_s ▸ hs2 h
  refine ⟨hs0, hG_s ▸ hs1, ?_, ?_⟩
  · intro i
    rw [hDy']
    by_cases hi : i ∈ inst.S j
    · rw [if_pos hi]
      rcases hs0.eq_or_lt with h0 | hpos
      · rw [← h0]; simpa using hD i
      · have hx1 : alg2X inst y' i ≤ 1 :=
          le_trans (Finset.single_le_sum (fun k _ => hxnn k) hi) (hbound hpos)
        have hci := inst.hc_pos i
        unfold alg2X at hx1
        rw [hDy', if_pos hi] at hx1
        have h1 : Real.exp (L / inst.c i * (dualSum inst y i + s)) ≤ 1 + inst.d := by
          have : (1 / inst.d) * (Real.exp (L / inst.c i * (dualSum inst y i + s)) - 1) ≤ 1 := hx1
          rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hdpos] at this
          linarith
        have h2 : L / inst.c i * (dualSum inst y i + s) ≤ L := by
          have := Real.log_le_log (Real.exp_pos _) h1
          rwa [Real.log_exp] at this
        have h3 : dualSum inst y i + s ≤ inst.c i := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hci] at h2
          nlinarith
        exact h3
    · rw [if_neg hi]; simpa using hD i
  · -- potential increase
    have hdiff : ∑ i, inst.c i * alg2X inst y' i - ∑ i, inst.c i * alg2X inst y i =
        ∑ i ∈ inst.S j, (inst.c i * alg2X inst y' i - inst.c i * alg2X inst y i) := by
      rw [← Finset.sum_sub_distrib]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      unfold alg2X
      rw [hDy', if_neg hi]; simp
    have hterm : ∀ i ∈ inst.S j, inst.c i * alg2X inst y' i - inst.c i * alg2X inst y i ≤
        L * s * (alg2X inst y' i + 1 / inst.d) := by
      intro i hi
      have hci := inst.hc_pos i
      unfold alg2X
      rw [hDy', if_pos hi]
      set a := L / inst.c i * dualSum inst y i with ha
      set t := L / inst.c i * s with ht
      have hexp : Real.exp (L / inst.c i * (dualSum inst y i + s)) = Real.exp a * Real.exp t := by
        rw [← Real.exp_add]; congr 1; rw [ha, ht]; ring
      have hcts : inst.c i * t = L * s := by rw [ht]; field_simp
      have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
      have h2 : Real.exp a = Real.exp a * Real.exp t * Real.exp (-t) := by
        rw [mul_assoc, ← Real.exp_add]; simp
      have h3 : Real.exp (a) * Real.exp t - Real.exp a ≤ Real.exp a * Real.exp t * t := by
        have hpos : 0 < Real.exp a * Real.exp t := by positivity
        have : Real.exp a * Real.exp t * (1 - t) ≤ Real.exp a * Real.exp t * Real.exp (-t) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
        rw [← h2] at this
        linarith
      have hz : Real.exp (L / inst.c i * (0:ℝ)) = 1 := by simp
      have hD0 : dualSum inst y i + 0 = dualSum inst y i := by ring
      -- rewrite the old term
      have hold : (1 / inst.d) * (Real.exp (L / inst.c i * dualSum inst y i) - 1) =
        (1 / inst.d) * (Real.exp a - 1) := by rw [ha]
      rw [hold]
      have hdinv : 0 < 1 / inst.d := by positivity
      rw [hexp]
      have : inst.c i * ((1 / inst.d) * (Real.exp a * Real.exp t - 1)) -
          inst.c i * ((1 / inst.d) * (Real.exp a - 1)) =
          (inst.c i / inst.d) * (Real.exp a * Real.exp t - Real.exp a) := by ring
      rw [this]
      have h4 : (inst.c i / inst.d) * (Real.exp a * Real.exp t - Real.exp a) ≤
          (inst.c i / inst.d) * (Real.exp a * Real.exp t * t) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      refine h4.trans (le_of_eq ?_)
      have : (inst.c i / inst.d) * (Real.exp a * Real.exp t * t) =
        (inst.c i * t) * (1 / inst.d) * (Real.exp a * Real.exp t) := by ring
      rw [this, hcts]
      ring
    calc ∑ i, inst.c i * alg2X inst y' i
        = ∑ i, inst.c i * alg2X inst y i +
          ∑ i ∈ inst.S j, (inst.c i * alg2X inst y' i - inst.c i * alg2X inst y i) := by
          rw [← hdiff]; ring
      _ ≤ ∑ i, inst.c i * alg2X inst y i + ∑ i ∈ inst.S j, L * s * (alg2X inst y' i + 1 / inst.d) := by
          have := Finset.sum_le_sum hterm
          linarith
      _ ≤ ∑ i, inst.c i * alg2X inst y i + 2 * L * s := by
          have hsum : ∑ i ∈ inst.S j, L * s * (alg2X inst y' i + 1 / inst.d) =
              L * s * (∑ i ∈ inst.S j, alg2X inst y' i + (inst.S j).card * (1 / inst.d)) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp
          rw [hsum]
          have hcard : ((inst.S j).card : ℝ) * (1 / inst.d) ≤ 1 := by
            have := inst.hd_bound j
            rw [mul_one_div, div_le_one hdpos]; exact this
          rcases hs0.eq_or_lt with h0 | hpos
          · rw [← h0]; simp
          · have := hbound hpos
            have hLs : 0 ≤ L * s := by positivity
            nlinarith

end

section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def Inv2_H46 (inst : CoveringInstance I J) (y : J → ℝ) (rem : List J) : Prop :=
  (∀ j ∈ rem, y j = 0) ∧ (∀ j, 0 ≤ y j) ∧ (∀ i, dualSum inst y i ≤ inst.c i) ∧
  (∀ j, j ∉ rem → 1 ≤ ∑ i ∈ inst.S j, alg2X inst y i) ∧
  ∑ i, inst.c i * alg2X inst y i ≤ 2 * Real.log (1 + inst.d) * ∑ j, y j

lemma inv2_fold_H46 (inst : CoveringInstance I J) (hS : ∀ j, (inst.S j).Nonempty) :
    ∀ (rem : List J) (y : J → ℝ), rem.Nodup → Inv2_H46 inst y rem →
    Inv2_H46 inst (rem.foldl (fun y j => Function.update y j (raiseAmount inst (alg2X inst) y j)) y) [] := by
  intro rem
  induction rem with
  | nil => intro y _ h; exact h
  | cons j l ih =>
    intro y hnd hinv
    obtain ⟨h0, hy, hD, hcov, hP⟩ := hinv
    have hj : y j = 0 := h0 j (List.mem_cons_self ..)
    obtain ⟨hs0, hs1, hs2, hs3⟩ := alg2_step_H46 inst y j (hS j) hj hy hD
    set s := raiseAmount inst (alg2X inst) y j with hs
    have hnd' := List.nodup_cons.mp hnd
    simp only [List.foldl_cons]
    refine ih _ hnd'.2 ?_
    have hDy' : ∀ i, dualSum inst (Function.update y j s) i =
        dualSum inst y i + (if i ∈ inst.S j then s else 0) :=
      fun i => dualSum_update_H46 inst y j hj s i
    have hmono : ∀ i, dualSum inst y i ≤ dualSum inst (Function.update y j s) i := by
      intro i; rw [hDy']; split_ifs <;> linarith
    refine ⟨?_, ?_, hs2, ?_, ?_⟩
    · intro k hk
      have hkj : k ≠ j := fun h => hnd'.1 (h ▸ hk)
      simp [Function.update_of_ne hkj, h0 k (List.mem_cons_of_mem _ hk)]
    · intro k
      by_cases hk : k = j
      · subst hk; simpa using hs0
      · simp [Function.update_of_ne hk, hy k]
    · intro k hk
      by_cases hkj : k = j
      · subst hkj; exact hs1
      · have hk' : k ∉ j :: l := by
          intro hm
          rcases List.mem_cons.mp hm with h | h
          · exact hkj h
          · exact hk h
        refine (hcov k hk').trans (Finset.sum_le_sum (fun i _ => alg2X_mono_H46 inst _ _ i (hmono i)))
    · have hsum : ∑ k, Function.update y j s k = s + ∑ k, y k := by
        rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
        rw [← Finset.add_sum_erase _ y (Finset.mem_univ j), hj, Finset.sdiff_singleton_eq_erase]
        ring
      rw [hsum]
      nlinarith [Lpos_H46 inst]

theorem alg2_core_H46 (inst : CoveringInstance I J) (hS : ∀ j, (inst.S j).Nonempty)
    (ord : List J) (hord_nodup : ord.Nodup) (hord_mem : ∀ j, j ∈ ord) :
    let y : J → ℝ := raiseRun inst (alg2X inst) ord
    let x : I → ℝ := alg2X inst y
    (∀ j, 1 ≤ ∑ i ∈ inst.S j, x i) ∧
    ((∀ j, 0 ≤ y j) ∧ ∀ i : I, dualSum inst y i ≤ inst.c i) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * x i ≤ 2 * Real.log (1 + inst.d) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * Real.log (1 + inst.d) * ∑ j, y j) := by
  intro y x
  have hinit : Inv2_H46 inst (fun _ => 0) ord := by
    refine ⟨fun _ _ => rfl, fun _ => le_rfl, ?_, fun j hj => absurd (hord_mem j) hj, ?_⟩
    · intro i
      have : dualSum inst (fun _ => (0:ℝ)) i = 0 := by simp [dualSum]
      rw [this]; exact (inst.hc_pos i).le
    · simp [alg2X, dualSum]
  obtain ⟨_, hy, hD, hcov, hP⟩ := inv2_fold_H46 inst hS ord (fun _ => 0) hord_nodup hinit
  have hL := Lpos_H46 inst
  have hx0 : ∀ i, 0 ≤ x i := fun i => alg2X_nonneg_H46 inst y i (dualSum_nonneg_H46 inst y hy i)
  have hcov' : ∀ j, 1 ≤ ∑ i ∈ inst.S j, x i := fun j => hcov j (by simp)
  refine ⟨hcov', ⟨hy, hD⟩, ?_, ?_⟩
  · intro x'' hx''0 hx''cov
    have := weak_dual_H46 inst y x'' hy hx''0 hx''cov hD
    calc ∑ i, inst.c i * x i ≤ 2 * Real.log (1 + inst.d) * ∑ j, y j := hP
      _ ≤ _ := by nlinarith
  · intro y'' hy''0 hy''D
    have := weak_dual_H46 inst y'' x hy''0 hx0 hcov' hy''D
    calc ∑ j, y'' j ≤ ∑ i, inst.c i * x i := this
      _ ≤ _ := hP

end

end OnlinePrimalDual.Framework

open OnlinePrimalDual.Framework


theorem solution {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (inst : CoveringInstance I J) (hS : ∀ j, (inst.S j).Nonempty)
    (ord : List J) (hord_nodup : ord.Nodup) (hord_mem : ∀ j, j ∈ ord) :
    let y : J → ℝ := raiseRun inst (alg2X inst) ord
    let x : I → ℝ := alg2X inst y
    (∀ j, 1 ≤ ∑ i ∈ inst.S j, x i) ∧
    ((∀ j, 0 ≤ y j) ∧ ∀ i : I, dualSum inst y i ≤ inst.c i) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * x i ≤ 2 * Real.log (1 + inst.d) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * Real.log (1 + inst.d) * ∑ j, y j) := by
  exact alg2_core_H46 inst hS ord hord_nodup hord_mem
