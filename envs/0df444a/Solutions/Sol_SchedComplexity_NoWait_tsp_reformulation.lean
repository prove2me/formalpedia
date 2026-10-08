-- Prove2me | solution 1 for SchedComplexity.NoWait.tsp_reformulation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:49:46.80498+00:00
-- url     : https://prove2.me/submissions/50abccee-7bf5-4669-a9cc-e21a5a9bb59d

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_NoWaitFlowShop



namespace SchedComplexity.NoWait

section tsp
variable {n m : ℕ} (p : Fin n → Fin m → ℕ)

theorem tsp_cum_zero (l : Fin n) : cum p l 0 = 0 := by simp [cum]

theorem tsp_cum_mono (l : Fin n) (r : ℕ) : cum p l r ≤ cum p l (r + 1) := by
  unfold cum
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  omega

theorem tsp_cum_strict (hp : ∀ ℓ r, 0 < p ℓ r) (l : Fin n) (r : ℕ) (hr : r < m) :
    cum p l r < cum p l (r + 1) := by
  unfold cum
  refine Finset.sum_lt_sum_of_subset (i := ⟨r, hr⟩) ?_ ?_ ?_ (hp _ _) (fun _ _ _ => Nat.zero_le _)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    omega
  · simp
  · simp

theorem tsp_cum_end (hm : 0 < m) (l : Fin n) : cum p l (m - 1 + 1) = cum p l m := by
  congr 1; omega

theorem tsp_c_nonneg (hm : 0 < m) (j k : Fin n) : 0 ≤ delay p hm j k := by
  have h := Finset.le_sup' (fun r : Fin m => (cum p j (r.val + 1) : ℤ) - (cum p k r.val : ℤ))
    (Finset.mem_univ (⟨0, hm⟩ : Fin m))
  have h2 : (0:ℤ) ≤ (cum p j (0 + 1) : ℤ) - (cum p k 0 : ℤ) := by
    simp [cum]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  exact le_trans h2 h

theorem tsp_c_ge (hm : 0 < m) (j k : Fin n) (r : Fin m) :
    (cum p j (r.val + 1) : ℤ) ≤ delay p hm j k + (cum p k r.val : ℤ) := by
  have h := Finset.le_sup' (fun r : Fin m => (cum p j (r.val + 1) : ℤ) - (cum p k r.val : ℤ))
    (Finset.mem_univ r)
  unfold delay
  linarith

theorem tsp_c_le (hm : 0 < m) (j k : Fin n) (δ : ℤ)
    (h : ∀ r : Fin m, (cum p j (r.val + 1) : ℤ) ≤ δ + (cum p k r.val : ℤ)) :
    delay p hm j k ≤ δ := by
  unfold delay
  apply Finset.sup'_le
  intro r _
  have := h r
  linarith

theorem tsp_tri (hm : 0 < m) (j l k : Fin n) :
    delay p hm j k ≤ delay p hm j l + delay p hm l k := by
  apply tsp_c_le
  intro r
  have h1 := tsp_c_ge p hm j l r
  have h2 := tsp_c_ge p hm l k r
  have h3 := tsp_cum_mono p l r.val
  have h3' : (cum p l r.val : ℤ) ≤ (cum p l (r.val+1) : ℤ) := by exact_mod_cast h3
  linarith

theorem tsp_end (hm : 0 < m) (j k : Fin n) :
    (cum p j m : ℤ) ≤ delay p hm j k + (cum p k m : ℤ) := by
  have h1 := tsp_c_ge p hm j k ⟨m - 1, by omega⟩
  have h2 := tsp_cum_mono p k (m - 1)
  have h2' : (cum p k (m-1) : ℤ) ≤ (cum p k (m-1+1) : ℤ) := by exact_mod_cast h2
  simp only at h1
  rw [tsp_cum_end p hm] at h1 h2'
  linarith

theorem tsp_disj_of_le {a b c d : ℕ} (h : b ≤ c) : Disjoint (Set.Ico a b) (Set.Ico c d) := by
  rw [Set.Ico_disjoint_Ico]; omega


end tsp

def Jf {N : ℕ} (π : Fin (N+1) ≃ Fin (N+1)) (k : ℕ) : Fin (N+1) := π ⟨min k N, by omega⟩

section seq
variable {N m : ℕ} (p : Fin (N+1) → Fin m → ℕ) (hm : 0 < m) (π : Fin (N+1) ≃ Fin (N+1))

def dd (k : ℕ) : ℤ := if k < N then delay p hm (Jf π k) (Jf π (k+1)) else 0

def SS (k : ℕ) : ℤ := ∑ i ∈ Finset.range k, dd p hm π i

theorem Jf_fin (i : Fin (N+1)) : Jf π i.val = π i := by
  unfold Jf
  have := i.isLt
  exact congrArg π (Fin.ext (by simp only; omega))

theorem dd_nonneg (k : ℕ) : 0 ≤ dd p hm π k := by
  unfold dd
  split_ifs
  · exact tsp_c_nonneg p hm _ _
  · exact le_refl _

theorem SS_nonneg (k : ℕ) : 0 ≤ SS p hm π k :=
  Finset.sum_nonneg (fun i _ => dd_nonneg p hm π i)

theorem SS_succ (k : ℕ) : SS p hm π (k+1) = SS p hm π k + dd p hm π k := by
  unfold SS; rw [Finset.sum_range_succ]

theorem pm_eq : pathMakespan p hm π = SS p hm π N + (cum p (π (Fin.last N)) m : ℤ) := by
  unfold pathMakespan
  have key : ∀ i : Fin (N+1), (if h : i.val + 1 < N + 1 then delay p hm (π i) (π ⟨i.val + 1, h⟩)
      else (cum p (π i) m : ℤ)) =
      (fun k : ℕ => if k < N then dd p hm π k else (cum p (Jf π k) m : ℤ)) i.val := by
    intro i
    have hi := i.isLt
    simp only [dd]
    by_cases h : i.val < N
    · have h' : i.val + 1 < N + 1 := by omega
      rw [dif_pos h', if_pos h, if_pos h, Jf_fin]
      congr 1
      unfold Jf
      exact congrArg π (Fin.ext (by simp only; omega))
    · have h' : ¬ i.val + 1 < N + 1 := by omega
      rw [dif_neg h', if_neg h, Jf_fin]
  rw [Finset.sum_congr rfl (fun i _ => key i),
    Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < N then dd p hm π k else (cum p (Jf π k) m : ℤ)) (N+1),
    Finset.sum_range_succ]
  have h1 : ∑ i ∈ Finset.range N, (if i < N then dd p hm π i else (cum p (Jf π i) m : ℤ))
      = SS p hm π N := by
    unfold SS
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
  rw [h1, if_neg (lt_irrefl N)]
  have : Jf π N = π (Fin.last N) := by
    have := Jf_fin π (Fin.last N)
    simpa using this
  rw [this]

theorem pt_eq : pathTotalCompletion p hm π =
    ∑ k : Fin (N+1), (SS p hm π k.val + (cum p (π k) m : ℤ)) := by
  unfold pathTotalCompletion
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have key : ∀ i : Fin (N+1), (if h : i.val < k.val then
        delay p hm (π i) (π ⟨i.val + 1, by have := k.isLt; omega⟩) else 0) =
      (fun j : ℕ => if j < k.val then dd p hm π j else 0) i.val := by
    intro i
    have hk := k.isLt
    by_cases h : i.val < k.val
    · simp only [dd]
      rw [dif_pos h, if_pos h, if_pos (by omega), Jf_fin]
      congr 1
      unfold Jf
      exact congrArg π (Fin.ext (by simp only; omega))
    · simp [h]
  rw [Finset.sum_congr rfl (fun i _ => key i),
    Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < k.val then dd p hm π j else 0) (N+1),
    ← Finset.sum_filter]
  unfold SS
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  have := k.isLt
  simp only [Finset.mem_filter, Finset.mem_range]
  omega


theorem gap (a b : ℕ) (hab : a < b) (hb : b ≤ N) :
    delay p hm (Jf π a) (Jf π b) ≤ SS p hm π b - SS p hm π a := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [SS_succ]
    have : dd p hm π a = delay p hm (Jf π a) (Jf π (a+1)) := by
      unfold dd; rw [if_pos (by omega)]
    linarith
  | succ b hb1 ih =>
    have ih := ih (by omega)
    rw [SS_succ]
    have : dd p hm π b = delay p hm (Jf π b) (Jf π (b+1)) := by
      unfold dd; rw [if_pos (by omega)]
    have := tsp_tri p hm (Jf π a) (Jf π b) (Jf π (b+1))
    linarith

theorem build : ∃ B : Fin (N+1) → ℕ, IsNoWaitSchedule p B ∧
    ∀ k : Fin (N+1), (B (π k) : ℤ) = SS p hm π k.val := by
  refine ⟨fun ℓ => (SS p hm π (π.symm ℓ).val).toNat, ?_, ?_⟩
  · have hB : ∀ ℓ : Fin (N+1), ((SS p hm π (π.symm ℓ).val).toNat : ℤ) = SS p hm π (π.symm ℓ).val :=
      fun ℓ => Int.toNat_of_nonneg (SS_nonneg p hm π _)
    have main : ∀ j k : Fin (N+1), (π.symm j).val < (π.symm k).val → ∀ r : Fin m,
        (SS p hm π (π.symm j).val).toNat + cum p j (r.val + 1) ≤
          (SS p hm π (π.symm k).val).toNat + cum p k r.val := by
      intro j k hjk r
      have g := gap p hm π _ _ hjk (by have := (π.symm k).isLt; omega)
      rw [Jf_fin, Jf_fin] at g
      simp only [Equiv.apply_symm_apply] at g
      have c := tsp_c_ge p hm j k r
      have h1 := hB j
      have h2 := hB k
      zify
      linarith
    intro j k hjk r
    have hne : (π.symm j).val ≠ (π.symm k).val := by
      intro h
      exact hjk (by simpa using congrArg π (Fin.ext h))
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact tsp_disj_of_le (main j k h r)
    · exact (tsp_disj_of_le (main k j h r)).symm
  · intro k
    simp only [Equiv.symm_apply_apply]
    exact Int.toNat_of_nonneg (SS_nonneg p hm π _)

theorem GG_mono (k t : ℕ) (h : k + t ≤ N) :
    SS p hm π k + (cum p (Jf π k) m : ℤ) ≤ SS p hm π (k + t) + (cum p (Jf π (k + t)) m : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ih := ih (by omega)
    have e := tsp_end p hm (Jf π (k+t)) (Jf π (k+t+1))
    have hd : dd p hm π (k+t) = delay p hm (Jf π (k+t)) (Jf π (k+t+1)) := by
      unfold dd; rw [if_pos (by omega)]
    have := SS_succ p hm π (k+t)
    rw [show k + (t+1) = k + t + 1 by ring]
    linarith


theorem order_key (hp : ∀ ℓ r, 0 < p ℓ r) (B : Fin (N+1) → ℕ) (hB : IsNoWaitSchedule p B)
    (j k : Fin (N+1)) (hjk : j ≠ k) (hlt : B j < B k) :
    ∀ r : ℕ, r < m → B j + cum p j (r + 1) ≤ B k + cum p k r := by
  intro r
  induction r with
  | zero =>
    intro hr
    have h := hB j k hjk ⟨0, hr⟩
    rw [Set.Ico_disjoint_Ico] at h
    simp only [Fin.val_mk] at h
    have h1 := tsp_cum_strict p hp j 0 hr
    have h2 := tsp_cum_strict p hp k 0 hr
    have h3 := tsp_cum_zero p j
    have h4 := tsp_cum_zero p k
    omega
  | succ r ih =>
    intro hr
    have ih := ih (by omega)
    have h := hB j k hjk ⟨r+1, hr⟩
    rw [Set.Ico_disjoint_Ico] at h
    simp only [Fin.val_mk] at h
    have h1 := tsp_cum_strict p hp j (r+1) hr
    have h2 := tsp_cum_strict p hp k (r+1) hr
    have h3 := tsp_cum_strict p hp k r (by omega)
    omega

theorem sort_exists (hp : ∀ ℓ r, 0 < p ℓ r) (B : Fin (N+1) → ℕ) (hB : IsNoWaitSchedule p B) :
    ∃ π : Fin (N+1) ≃ Fin (N+1), ∀ k : ℕ, k < N →
      dd p hm π k ≤ (B (Jf π (k+1)) : ℤ) - (B (Jf π k) : ℤ) := by
  have hinj : ∀ j k : Fin (N+1), j ≠ k → B j ≠ B k := by
    intro j k hjk heq
    have h := hB j k hjk ⟨0, hm⟩
    rw [Set.Ico_disjoint_Ico] at h
    simp only [Fin.val_mk] at h
    have h1 := tsp_cum_strict p hp j 0 hm
    have h2 := tsp_cum_strict p hp k 0 hm
    have h3 := tsp_cum_zero p j
    have h4 := tsp_cum_zero p k
    omega
  refine ⟨Tuple.sort B, ?_⟩
  intro k hk
  have hmono := Tuple.monotone_sort B
  set π := Tuple.sort B with hπ
  have hle : B (π ⟨k, by omega⟩) ≤ B (π ⟨k+1, by omega⟩) :=
    hmono (show (⟨k, by omega⟩ : Fin (N+1)) ≤ ⟨k+1, by omega⟩ from by simp [Fin.le_def])
  have hne : π ⟨k, by omega⟩ ≠ π ⟨k+1, by omega⟩ := by
    intro h
    have := π.injective h
    simp [Fin.ext_iff] at this
  have hlt : B (π ⟨k, by omega⟩) < B (π ⟨k+1, by omega⟩) :=
    lt_of_le_of_ne hle (hinj _ _ hne)
  have e1 : Jf π k = π ⟨k, by omega⟩ := by
    unfold Jf; exact congrArg π (Fin.ext (by simp only; omega))
  have e2 : Jf π (k+1) = π ⟨k+1, by omega⟩ := by
    unfold Jf; exact congrArg π (Fin.ext (by simp only; omega))
  rw [e1, e2]
  have hd : dd p hm π k = delay p hm (π ⟨k, by omega⟩) (π ⟨k+1, by omega⟩) := by
    unfold dd; rw [if_pos hk, e1, e2]
  rw [hd]
  have key := order_key p hp B hB _ _ hne hlt
  apply tsp_c_le
  intro r
  have := key r.val r.isLt
  have : ((B (π ⟨k, by omega⟩) : ℕ) : ℤ) + (cum p (π ⟨k, by omega⟩) (r.val+1) : ℤ) ≤
      (B (π ⟨k+1, by omega⟩) : ℤ) + (cum p (π ⟨k+1, by omega⟩) r.val : ℤ) := by exact_mod_cast this
  linarith

theorem SS_le (π : Fin (N+1) ≃ Fin (N+1)) (B : Fin (N+1) → ℕ)
    (h : ∀ k : ℕ, k < N → dd p hm π k ≤ (B (Jf π (k+1)) : ℤ) - (B (Jf π k) : ℤ)) :
    ∀ k : ℕ, k ≤ N → SS p hm π k ≤ (B (Jf π k) : ℤ) - (B (Jf π 0) : ℤ) := by
  intro k
  induction k with
  | zero => intro _; simp [SS]
  | succ k ih =>
    intro hk
    have := ih (by omega)
    have := h k (by omega)
    rw [SS_succ]
    linarith

end seq

theorem tsp_core {n m : ℕ} (p : Fin n → Fin m → ℕ) (hm : 0 < m)
    (hp : ∀ ℓ r, 0 < p ℓ r) (y : ℕ) :
    ((∃ B, IsNoWaitSchedule p B ∧ ∀ ℓ, completion p B ℓ ≤ y) ↔
        ∃ π : Fin n ≃ Fin n, pathMakespan p hm π ≤ (y : ℤ)) ∧
      ((∃ B, IsNoWaitSchedule p B ∧ ∑ ℓ, completion p B ℓ ≤ y) ↔
        ∃ π : Fin n ≃ Fin n, pathTotalCompletion p hm π ≤ (y : ℤ)) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hB : IsNoWaitSchedule p (fun ℓ : Fin 0 => ℓ.elim0) := fun j => j.elim0
    refine ⟨⟨fun _ => ⟨Equiv.refl _, by simp [pathMakespan]⟩, fun _ => ?_⟩,
      ⟨fun _ => ⟨Equiv.refl _, by simp [pathTotalCompletion]⟩, fun _ => ?_⟩⟩
    · exact ⟨fun ℓ => ℓ.elim0, hB, fun ℓ => ℓ.elim0⟩
    · exact ⟨fun ℓ => ℓ.elim0, hB, by simp⟩
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rintro ⟨B, hB, hC⟩
      obtain ⟨π, hπ⟩ := sort_exists p hm hp B hB
      refine ⟨π, ?_⟩
      rw [pm_eq]
      have h1 := SS_le p hm π B hπ N le_rfl
      have h2 := hC (π (Fin.last N))
      have h3 : Jf π N = π (Fin.last N) := by simpa using Jf_fin π (Fin.last N)
      rw [h3] at h1
      unfold completion at h2
      have h2' : (B (π (Fin.last N)) : ℤ) + (cum p (π (Fin.last N)) m : ℤ) ≤ y := by exact_mod_cast h2
      have : (0:ℤ) ≤ B (Jf π 0) := by positivity
      linarith
    · rintro ⟨π, hπ⟩
      obtain ⟨B, hB, hBπ⟩ := build p hm π
      refine ⟨B, hB, fun ℓ => ?_⟩
      obtain ⟨k, rfl⟩ := π.surjective ℓ
      rw [pm_eq] at hπ
      have h1 := GG_mono p hm π k.val (N - k.val) (by have := k.isLt; omega)
      have hk := k.isLt
      rw [show k.val + (N - k.val) = N by omega] at h1
      rw [Jf_fin] at h1
      have h3 : Jf π N = π (Fin.last N) := by simpa using Jf_fin π (Fin.last N)
      rw [h3] at h1
      have := hBπ k
      unfold completion
      have : ((B (π k) + cum p (π k) m : ℕ) : ℤ) ≤ y := by
        push_cast; linarith
      exact_mod_cast this
    · rintro ⟨B, hB, hC⟩
      obtain ⟨π, hπ⟩ := sort_exists p hm hp B hB
      refine ⟨π, ?_⟩
      rw [pt_eq]
      have hC' : ((∑ ℓ, completion p B ℓ : ℕ) : ℤ) ≤ y := by exact_mod_cast hC
      have e : ∑ ℓ, completion p B ℓ = ∑ k, completion p B (π k) :=
        (Equiv.sum_comp π (fun ℓ => completion p B ℓ)).symm
      rw [e] at hC'
      push_cast at hC'
      refine le_trans ?_ hC'
      apply Finset.sum_le_sum
      intro k _
      have h1 := SS_le p hm π B hπ k.val (by have := k.isLt; omega)
      rw [Jf_fin] at h1
      unfold completion
      have : (0:ℤ) ≤ B (Jf π 0) := by positivity
      push_cast
      linarith
    · rintro ⟨π, hπ⟩
      obtain ⟨B, hB, hBπ⟩ := build p hm π
      refine ⟨B, hB, ?_⟩
      rw [pt_eq] at hπ
      have e : ∑ ℓ, completion p B ℓ = ∑ k, completion p B (π k) :=
        (Equiv.sum_comp π (fun ℓ => completion p B ℓ)).symm
      rw [e]
      have : ((∑ k, completion p B (π k) : ℕ) : ℤ) ≤ y := by
        push_cast
        refine le_trans (le_of_eq ?_) hπ
        apply Finset.sum_congr rfl
        intro k _
        unfold completion
        push_cast
        rw [hBπ k]
      exact_mod_cast this

end SchedComplexity.NoWait

open SchedComplexity.NoWait


theorem solution {n m : ℕ} (p : Fin n → Fin m → ℕ) (hm : 0 < m)
    (hp : ∀ ℓ r, 0 < p ℓ r) (y : ℕ) :
    ((∃ B, IsNoWaitSchedule p B ∧ ∀ ℓ, completion p B ℓ ≤ y) ↔
        ∃ π : Fin n ≃ Fin n, pathMakespan p hm π ≤ (y : ℤ)) ∧
      ((∃ B, IsNoWaitSchedule p B ∧ ∑ ℓ, completion p B ℓ ≤ y) ↔
        ∃ π : Fin n ≃ Fin n, pathTotalCompletion p hm π ≤ (y : ℤ)) := by
  exact tsp_core p hm hp y
