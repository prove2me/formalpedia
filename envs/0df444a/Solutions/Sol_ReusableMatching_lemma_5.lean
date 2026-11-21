-- Prove2me | solution 1 for ReusableMatching.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:28:24.172284+00:00
-- url     : https://prove2.me/submissions/4557fa4d-f6b8-4616-a7c3-5ce333611ba7

import Mathlib
import Definitions.Def_ReusableMatching_dualAlpha
import Definitions.Def_ReusableMatching_availableInSubperiod
import Definitions.Def_ReusableMatching_twoSeed
import Definitions.Def_ReusableMatching_window

namespace ReusableMatching

namespace Aux_RM

theorem mem_filter_any {α : Type*} (s : Finset α) (p : α → Prop) (inst : DecidablePred p)
    (a : α) : a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := @Finset.mem_filter α p inst s a

theorem leastArgmax_mem {V : Type*} [LinearOrder V] (C : Finset V) (f : V → ℝ) (v : V)
    (h : leastArgmax C f = some v) : v ∈ C := by
  unfold leastArgmax at h
  by_cases hne : C.Nonempty
  · rw [dif_pos hne] at h
    injection h with h
    rw [← h]
    exact ((mem_filter_any _ _ _ _).mp (Finset.min'_mem _ _)).1
  · rw [dif_neg hne] at h
    cases h

theorem leastArgmax_congr {V : Type*} [LinearOrder V] (C : Finset V) (f f' : V → ℝ)
    (hf : ∀ v ∈ C, f v = f' v) : leastArgmax C f = leastArgmax C f' := by
  have hff : ∀ h : C.Nonempty, C.sup' h f = C.sup' h f' := fun h => Finset.sup'_congr h rfl hf
  have key : ∀ (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty), A = B →
      A.min' hA = B.min' hB := by
    rintro A B hA hB rfl
    rfl
  unfold leastArgmax
  by_cases h : C.Nonempty
  · rw [dif_pos h, dif_pos h]
    congr 1
    apply key
    ext v
    rw [mem_filter_any, mem_filter_any]
    constructor
    · rintro ⟨hv, hv2⟩
      exact ⟨hv, by rw [← hf v hv, ← hff h]; exact hv2⟩
    · rintro ⟨hv, hv2⟩
      exact ⟨hv, by rw [hf v hv, hff h]; exact hv2⟩
  · rw [dif_neg h, dif_neg h]

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

theorem assign_succ (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t : ℕ) :
    assignment I β Y (t + 1) = Function.update (assignment I β Y t) t
      (if h : t < n then chooseResource I β Y (assignment I β Y t) ⟨t, h⟩ else none) := rfl

theorem assign_stab (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) :
    ∀ m s, s < m → assignment I β Y m s = assignment I β Y (s + 1) s := by
  intro m
  induction m with
  | zero => intro s hs; exact absurd hs (Nat.not_lt_zero _)
  | succ m ih =>
    intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | h
    · rw [assign_succ, Function.update_of_ne (by omega), ih s h]
    · rw [h]

theorem assign_avail (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (s : ℕ) (v : V)
    (h : assignment I β Y (s + 1) s = some v) :
    s < n ∧ IsAvailable I (assignment I β Y s) v s := by
  rw [assign_succ, Function.update_self] at h
  by_cases hs : s < n
  · rw [dif_pos hs] at h
    refine ⟨hs, ?_⟩
    unfold chooseResource at h
    have := leastArgmax_mem _ _ v h
    exact ((mem_filter_any _ _ _ _).mp this).2.2
  · rw [dif_neg hs] at h
    cases h

end Aux_RM

namespace Aux_RM

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

theorem lemma5_main (I : OBMRRInstance V n) (β : ℝ) (i : V) (j : Fin n) (Y : Seeds V n)
    (y1 : unitInterval) (hi : i ∉ availableInSubperiod I β (twoSeed I Y i j y1 1) j)
    (y2 : unitInterval) :
    I.r i * g β y1 ≤ ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t := by
  obtain ⟨Y1, hY1⟩ : ∃ Z, Z = twoSeed I Y i j y1 y2 := ⟨_, rfl⟩
  obtain ⟨Y1', hY1'⟩ : ∃ Z, Z = twoSeed I Y i j y1 1 := ⟨_, rfl⟩
  rw [← hY1]
  rw [← hY1'] at hi
  have hnot : ∀ t : Fin n, period I t = period I j → t ≤ j →
      ¬ IsAvailable I (assignment I β Y1' t) i t := by
    intro t hpt htj hav
    apply hi
    unfold availableInSubperiod
    rw [mem_filter_any]
    refine ⟨Finset.mem_univ _, t, hpt, htj, ?_⟩
    unfold availableSet
    rw [mem_filter_any]
    exact ⟨Finset.mem_univ _, hav⟩
  have hagree : ∀ m : ℕ, m ≤ (j : ℕ) → assignment I β Y1 m = assignment I β Y1' m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have hmn : m < n := by have := j.isLt; omega
      rw [assign_succ, assign_succ, ih (by omega), dif_pos hmn, dif_pos hmn]
      congr 1
      unfold chooseResource
      apply leastArgmax_congr
      intro v hv
      have hv' := ((mem_filter_any _ _ _ _).mp hv).2.2
      show reducedPrice I β Y1 v ⟨m, hmn⟩ = reducedPrice I β Y1' v ⟨m, hmn⟩
      by_cases hc : v = i ∧ period I ⟨m, hmn⟩ = period I j
      · exfalso
        obtain ⟨rfl, hp⟩ := hc
        exact hnot ⟨m, hmn⟩ hp (show m ≤ (j : ℕ) by omega) hv'
      · have hne : (v, period I ⟨m, hmn⟩) ≠ (i, period I j) := by
          intro h
          apply hc
          exact ⟨(Prod.ext_iff.mp h).1, (Prod.ext_iff.mp h).2⟩
        have hY : Y1 (v, period I ⟨m, hmn⟩) = Y1' (v, period I ⟨m, hmn⟩) := by
          rw [hY1, hY1']
          unfold twoSeed
          rw [Function.update_of_ne hne, Function.update_of_ne hne]
        unfold reducedPrice
        rw [hY]
  have hj := hnot j rfl le_rfl
  unfold IsAvailable at hj
  push_neg at hj
  obtain ⟨s, hsj, hsa, hsd⟩ := hj
  have hsn : s < n := by have := j.isLt; omega
  have hstab' : assignment I β Y1' (s + 1) s = some i := by
    rw [← assign_stab I β Y1' j s hsj]
    exact hsa
  obtain ⟨_, hav⟩ := assign_avail I β Y1' s i hstab'
  have hd0 : 0 < I.d := by have := I.one_le_d; omega
  have hdiv : s / I.d + 1 = (j : ℕ) / I.d := by
    have h1 : s / I.d ≤ (j : ℕ) / I.d := Nat.div_le_div_right hsj.le
    have h2 : (j : ℕ) / I.d ≤ s / I.d + 1 := by
      have : (j : ℕ) ≤ s + I.d := hsd.le
      calc (j : ℕ) / I.d ≤ (s + I.d) / I.d := Nat.div_le_div_right this
        _ = s / I.d + 1 := Nat.add_div_right s hd0
    have h3 : s / I.d ≠ (j : ℕ) / I.d := by
      intro heq
      have hpe : period I ⟨s, hsn⟩ = period I j := by
        apply Fin.ext
        show s / I.d + 1 = (j : ℕ) / I.d + 1
        rw [heq]
      exact hnot ⟨s, hsn⟩ hpe (show s ≤ (j : ℕ) by omega) hav
    generalize s / I.d = a at h1 h2 h3 ⊢
    generalize (j : ℕ) / I.d = b at h1 h2 h3 ⊢
    omega
  have hsa1 : assignment I β Y1 j s = some i := by
    rw [hagree j le_rfl]
    exact hsa
  have hPR : PeriodicReranking I β Y1 ⟨s, hsn⟩ = some i := by
    unfold PeriodicReranking
    show assignment I β Y1 n s = some i
    rw [assign_stab I β Y1 n s hsn, ← assign_stab I β Y1 j s hsj]
    exact hsa1
  have hseed : Y1 (i, period I ⟨s, hsn⟩) = y1 := by
    have hpp : period I ⟨s, hsn⟩ = prevPeriod I j := by
      apply Fin.ext
      show s / I.d + 1 = (j : ℕ) / I.d
      exact hdiv
    have hne : (i, prevPeriod I j) ≠ (i, period I j) := by
      intro h
      have h' : ((prevPeriod I j : Fin (n + 1)) : ℕ) = ((period I j : Fin (n + 1)) : ℕ) := by
        rw [(Prod.mk.inj h).2]
      have e1 : ((prevPeriod I j : Fin (n + 1)) : ℕ) = (j : ℕ) / I.d := rfl
      have e2 : ((period I j : Fin (n + 1)) : ℕ) = (j : ℕ) / I.d + 1 := rfl
      rw [e1, e2] at h'
      exact (Nat.succ_ne_self _) h'.symm
    rw [hpp, hY1]
    unfold twoSeed
    rw [Function.update_of_ne hne, Function.update_self]
  have hval : dualAlpha I β Y1 i ⟨s, hsn⟩ = I.r i * g β y1 := by
    unfold dualAlpha
    rw [if_pos hPR, hseed]
  have hmem : (⟨s, hsn⟩ : Fin n) ∈ window I j := by
    unfold window
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, show s ≤ (j : ℕ) by omega, hsd⟩
  have hnn : ∀ t ∈ window I j, 0 ≤ dualAlpha I β Y1 i t := by
    intro t _
    unfold dualAlpha
    split_ifs
    · exact mul_nonneg (I.r_nonneg i) (by unfold g; exact (Real.exp_pos _).le)
    · exact le_rfl
  rw [← hval]
  exact Finset.single_le_sum hnn hmem

end Aux_RM


end ReusableMatching

open ReusableMatching in
theorem solution {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E) (Y : Seeds V n)
    (y1 : unitInterval) (hi : i ∉ availableInSubperiod I β (twoSeed I Y i j y1 1) j) :
    ∀ y2 : unitInterval,
      I.r i * g β y1 ≤ ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t :=
  fun y2 => Aux_RM.lemma5_main I β i j Y y1 hi y2
