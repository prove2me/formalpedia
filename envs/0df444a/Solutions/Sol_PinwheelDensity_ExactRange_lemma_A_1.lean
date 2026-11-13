-- Prove2me | solution 1 for PinwheelDensity.ExactRange.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:50:00.382852+00:00
-- url     : https://prove2.me/submissions/b7f8918d-b803-4177-9bcc-f4bccd33f43a

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.LA1

open PinwheelDensity.ExactRange

theorem toQ_eq (A : List ℕ) : toQ A = A.map (fun a : ℕ => ((a : ℕ) : ℚ)) := by
  induction A with
  | nil => rfl
  | cons a l ih =>
    have : toQ (a :: l) = (a : ℚ) :: toQ l := by simp [toQ]
    rw [this, ih]; rfl

theorem toQ_getElem (A : List ℕ) (i : ℕ) (hi : i < (toQ A).length) (hi' : i < A.length) :
    (toQ A)[i] = ((A[i] : ℕ) : ℚ) := by
  simp [toQ_eq]

theorem cnt_succ (s : ℕ → Option ℕ) (i t w : ℕ) :
    cnt s i t (w + 1) = cnt s i t w + if s (t + w) = some i then 1 else 0 := by
  unfold cnt
  rw [List.range_succ, List.filter_append]
  by_cases h : s (t + w) = some i <;> simp [h]

theorem cnt_add (s : ℕ → Option ℕ) (i t w1 w2 : ℕ) :
    cnt s i t (w1 + w2) = cnt s i t w1 + cnt s i (t + w1) w2 := by
  induction w2 with
  | zero => simp [cnt]
  | succ n ih =>
    have e : w1 + (n + 1) = (w1 + n) + 1 := rfl
    rw [e, cnt_succ, ih, cnt_succ s i (t + w1) n, add_assoc t w1 n]
    ring

theorem cnt_pos (s : ℕ → Option ℕ) (i t w : ℕ) :
    0 < cnt s i t w ↔ ∃ k, k < w ∧ s (t + k) = some i := by
  unfold cnt
  rw [List.length_pos_iff_exists_mem]
  simp [List.mem_filter, List.mem_range]

theorem cnt_mul (s : ℕ → Option ℕ) (i a : ℕ)
    (h : ∀ t : ℕ, ∃ d : ℕ, t ≤ d ∧ d < t + a ∧ s d = some i) :
    ∀ q t : ℕ, q ≤ cnt s i t (q * a) := by
  intro q
  induction q with
  | zero => intro t; simp
  | succ q ih =>
    intro t
    have e : (q + 1) * a = q * a + a := by ring
    rw [e, cnt_add]
    have h1 := ih t
    have h2 : 0 < cnt s i (t + q * a) a := by
      rw [cnt_pos]
      obtain ⟨d, d1, d2, d3⟩ := h (t + q * a)
      exact ⟨d - (t + q * a), by omega, by rw [show t + q * a + (d - (t + q * a)) = d by omega]; exact d3⟩
    omega

theorem part1 (s : ℕ → Option ℕ) (i a : ℕ) (ha : 1 ≤ a) :
    Serves s i (a : ℚ) ↔ ∀ t : ℕ, ∃ d : ℕ, t ≤ d ∧ d < t + a ∧ s d = some i := by
  constructor
  · intro h t
    have h1 := h t a
    rw [Nat.floor_div_natCast, Nat.floor_natCast, Nat.div_self (by omega)] at h1
    obtain ⟨k, hk, hk2⟩ := (cnt_pos s i t a).mp h1
    exact ⟨t + k, by omega, by omega, hk2⟩
  · intro h t w
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
    have h1 := cnt_mul s i a h (w / a) t
    have h2 : w / a * a ≤ w := Nat.div_mul_le_self w a
    have h3 : cnt s i t (w / a * a) ≤ cnt s i t w := by
      obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le h2
      have := cnt_add s i t (w / a * a) c
      rw [← hc] at this
      omega
    omega

theorem rat_to_sched (A : List ℕ) (hA : ∀ a ∈ A, 1 ≤ a) (h : RatSchedulable (toQ A)) :
    Schedulable A := by
  obtain ⟨_, s, hs⟩ := h
  refine ⟨fun d => match s d with
    | some j => if hj : j < A.length then some ⟨j, hj⟩ else none
    | none => none, ?_⟩
  intro i t
  have hi : i.1 < (toQ A).length := by simpa [toQ] using i.2
  have h1 := hs i.1 hi
  have e : (toQ A)[i.1] = ((A.get i : ℕ) : ℚ) := toQ_getElem A i.1 hi i.2
  rw [e, part1 _ _ _ (hA _ (List.get_mem _ _))] at h1
  obtain ⟨d, d1, d2, d3⟩ := h1 t
  refine ⟨d, d1, d2, ?_⟩
  simp [d3, i.2]

theorem sched_to_rat (A : List ℕ) (hA : ∀ a ∈ A, 1 ≤ a) (h : Schedulable A) :
    RatSchedulable (toQ A) := by
  obtain ⟨s, hs⟩ := h
  refine ⟨?_, fun d => (s d).map Fin.val, ?_⟩
  · intro a ha
    rw [toQ_eq] at ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have := hA b hb
    exact_mod_cast this
  · intro i hi
    have hi' : i < A.length := by simpa [toQ] using hi
    have e : (toQ A)[i] = ((A.get ⟨i, hi'⟩ : ℕ) : ℚ) := toQ_getElem A i hi hi'
    rw [e, part1 _ _ _ (hA _ (List.get_mem _ _))]
    intro t
    obtain ⟨d, d1, d2, d3⟩ := hs ⟨i, hi'⟩ t
    exact ⟨d, d1, d2, by simp [d3]⟩

theorem sched_to_periodic (A : List ℕ) (hne : A ≠ []) (hA : ∀ a ∈ A, 1 ≤ a)
    (h : Schedulable A) : HasPeriodicIdleFreeSchedule A := by
  obtain ⟨s, hs⟩ := h
  have hn : 0 < A.length := List.length_pos_iff.mpr hne
  let i0 : Fin A.length := ⟨0, hn⟩
  let s0 : ℕ → Fin A.length := fun d => (s d).getD i0
  have hs0 : ∀ (i : Fin A.length) (t : ℕ), ∃ d : ℕ, t ≤ d ∧ d < t + A.get i ∧ s0 d = i := by
    intro i t
    obtain ⟨d, h1, h2, h3⟩ := hs i t
    exact ⟨d, h1, h2, by simp [s0, h3]⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ, W = A.sum := ⟨_, rfl⟩
  have hWa : ∀ i : Fin A.length, A.get i ≤ W := fun i => hW ▸ List.le_sum_of_mem (List.get_mem _ _)
  have hW1 : 1 ≤ W := by
    have := hWa i0
    have := hA _ (List.get_mem A i0)
    omega
  let win : ℕ → (Fin W → Fin A.length) := fun k j => s0 (k * W + j)
  obtain ⟨x, y, hxy, hwin⟩ := Finite.exists_ne_map_eq_of_infinite win
  have hex : ∃ k1 c : ℕ, win k1 = win (k1 + (c + 1)) := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨x, y - x - 1, by rw [show x + (y - x - 1 + 1) = y by omega]; exact hwin⟩
    · exact ⟨y, x - y - 1, by rw [show y + (x - y - 1 + 1) = x by omega]; exact hwin.symm⟩
  obtain ⟨k1, c, hw⟩ := hex
  obtain ⟨t1, ht1⟩ : ∃ t1, t1 = k1 * W := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = (c + 1) * W := ⟨_, rfl⟩
  have hPW : W ≤ P := by rw [hPdef]; exact Nat.le_mul_of_pos_left W (by omega)
  have heq : ∀ j, j < W → s0 (t1 + j) = s0 (t1 + P + j) := by
    intro j hj
    have := congrFun hw ⟨j, hj⟩
    simp only [win] at this
    rw [ht1, hPdef]
    rw [this]
    congr 1
    ring
  have hclaim : ∀ u k, u < P → k < W → s0 (t1 + (u + k) % P) = s0 (t1 + u + k) := by
    intro u k hu hk
    by_cases hlt : u + k < P
    · rw [Nat.mod_eq_of_lt hlt, add_assoc]
    · have e1 : u + k = (u + k - P) + P := by omega
      have e2 : (u + k) % P = u + k - P := by
        rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      rw [e2, heq _ (by omega)]
      congr 1
      omega
  refine ⟨P, fun t => s0 (t1 + t % P), by omega, ?_, ?_⟩
  · intro t
    simp [Nat.add_mod_right]
  · intro i t
    obtain ⟨d, d1, d2, d3⟩ := hs0 i (t1 + t % P)
    have hu : t % P < P := Nat.mod_lt _ (by omega)
    have hk : d - (t1 + t % P) < W := by have := hWa i; omega
    refine ⟨t + (d - (t1 + t % P)), by omega, by omega, ?_⟩
    have e : (t + (d - (t1 + t % P))) % P = (t % P + (d - (t1 + t % P))) % P := by
      have ht := (Nat.mod_add_div t P).symm
      have : t + (d - (t1 + t % P)) = (t % P + (d - (t1 + t % P))) + P * (t / P) := by
        linarith
      rw [this, Nat.add_mul_mod_self_left]
    show s0 (t1 + (t + (d - (t1 + t % P))) % P) = i
    rw [e, hclaim _ _ hu hk, show t1 + t % P + (d - (t1 + t % P)) = d by omega]
    exact d3

theorem periodic_to_z (A : List ℕ) (h : HasPeriodicIdleFreeSchedule A) : ZSchedulable A := by
  obtain ⟨P, s, hP, hper, hs⟩ := h
  have hq : ∀ q r, s (r + q * P) = s r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [show r + (q + 1) * P = (r + q * P) + P by ring, hper, ih]
  have hmod : ∀ d, s (d % P) = s d := by
    intro d
    conv_rhs => rw [← Nat.mod_add_div d P]
    rw [mul_comm, hq]
  have hPz : (0 : ℤ) < P := by exact_mod_cast hP
  refine ⟨⟨fun i => {z | s (z % (P : ℤ)).toNat = i}, ?_, ?_⟩⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hi hj
    exact hij (hi.symm.trans hj)
  · intro i t
    obtain ⟨d, d1, d2, d3⟩ := hs i (t % (P : ℤ)).toNat
    have hu0 : 0 ≤ t % (P : ℤ) := Int.emod_nonneg _ hPz.ne'
    have hu1 : t % (P : ℤ) < P := Int.emod_lt_of_pos _ hPz
    have hut : (((t % (P : ℤ)).toNat : ℕ) : ℤ) = t % (P : ℤ) := Int.toNat_of_nonneg hu0
    have hdt := Int.emod_def t (P : ℤ)
    refine ⟨t - t % (P : ℤ) + d, ?_, Set.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · show s ((t - t % (P : ℤ) + d) % (P : ℤ)).toNat = i
      have e : (t - t % (P : ℤ) + d) % (P : ℤ) = ((d % P : ℕ) : ℤ) := by
        rw [show t - t % (P : ℤ) + d = d + (P : ℤ) * (t / P) by rw [hdt]; ring,
          Int.add_mul_emod_self_left]
        push_cast; rfl
      rw [e, Int.toNat_natCast, hmod]
      exact d3
    · have : (((t % (P : ℤ)).toNat : ℕ) : ℤ) ≤ d := by exact_mod_cast d1
      omega
    · have : (d : ℤ) < (((t % (P : ℤ)).toNat : ℕ) : ℤ) + (A.get i : ℕ) := by exact_mod_cast d2
      omega

theorem z_to_sched (A : List ℕ) (h : ZSchedulable A) : Schedulable A := by
  obtain ⟨σ⟩ := h
  classical
  refine ⟨fun d => if hd : ∃ i, (d : ℤ) ∈ σ.days i then some (Classical.choose hd) else none, ?_⟩
  intro i t
  obtain ⟨z, hz1, hz2⟩ := σ.hits i (t : ℤ)
  obtain ⟨h1, h2⟩ := Set.mem_Ico.mp hz2
  refine ⟨z.toNat, by omega, by omega, ?_⟩
  have hzz : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg (by omega)
  have hex : ∃ j, ((z.toNat : ℕ) : ℤ) ∈ σ.days j := ⟨i, by rw [hzz]; exact hz1⟩
  simp only [hex, dite_true]
  have key : ∀ j, ((z.toNat : ℕ) : ℤ) ∈ σ.days j → j = i := by
    intro j hj
    rw [hzz] at hj
    by_contra hne
    exact Set.disjoint_left.mp (σ.disjoint hne) hj hz1
  rw [key _ (Classical.choose_spec hex)]

end PinwheelDensity.ExactRange.Dev.LA1

namespace PinwheelDensity.ExactRange

theorem chk_lemma_A_1 :
    (∀ (s : ℕ → Option ℕ) (i a : ℕ), 1 ≤ a →
      (Serves s i (a : ℚ) ↔ ∀ t : ℕ, ∃ d : ℕ, t ≤ d ∧ d < t + a ∧ s d = some i)) ∧
    (∀ A : List ℕ, (∀ a ∈ A, 1 ≤ a) → (RatSchedulable (toQ A) ↔ Schedulable A)) ∧
    (∀ A : List ℕ, A ≠ [] → (∀ a ∈ A, 1 ≤ a) →
      (RatSchedulable (toQ A) ↔ HasPeriodicIdleFreeSchedule A) ∧
      (RatSchedulable (toQ A) ↔ ZSchedulable A)) := by
  refine ⟨fun s i a ha => Dev.LA1.part1 s i a ha, fun A hA =>
    ⟨Dev.LA1.rat_to_sched A hA, Dev.LA1.sched_to_rat A hA⟩, fun A hne hA => ?_⟩
  have h1 : RatSchedulable (toQ A) → HasPeriodicIdleFreeSchedule A := fun h =>
    Dev.LA1.sched_to_periodic A hne hA (Dev.LA1.rat_to_sched A hA h)
  have h2 : HasPeriodicIdleFreeSchedule A → ZSchedulable A := Dev.LA1.periodic_to_z A
  have h3 : ZSchedulable A → RatSchedulable (toQ A) := fun h =>
    Dev.LA1.sched_to_rat A hA (Dev.LA1.z_to_sched A h)
  have h4 : HasPeriodicIdleFreeSchedule A → RatSchedulable (toQ A) := fun h => h3 (h2 h)
  exact ⟨⟨h1, h4⟩, ⟨fun h => h2 (h1 h), h3⟩⟩

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_lemma_A_1 := @PinwheelDensity.ExactRange.chk_lemma_A_1
