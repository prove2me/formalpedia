-- Prove2me | solution 1 for ProcessingNetworks.PacketNetworks.back_pressure_optimal_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:38:24.875061+00:00
-- url     : https://prove2.me/submissions/46e4f36c-4b37-4fec-a088-c7e778b08929

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_BackPressurePolicy
import Definitions.Def_ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations

set_option autoImplicit false

open ProcessingNetworks.PacketNetworks in
/-- Under Assumption 12.1, a nonzero state has an activity whose input buffer is nonempty and
strictly larger than its output buffer (or whose output exits). Otherwise following activities
from a nonempty buffer never exits, and pigeonhole yields a cycle. -/
theorem d6bc_exists_good_activity {I J : ℕ} (dat : PacketNetworkData I J)
    (h121 : SatisfiesAssumption121 dat) (z : Fin I → ℕ) (hz : z ≠ 0) :
    ∃ j : Fin J, 1 ≤ z (dat.u j) ∧ ∀ i', dat.d j = some i' → z i' < z (dat.u j) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  choose g hg using h121.1
  let nxt : Fin I → Fin I := fun i => (dat.d (g i)).getD i
  have key : ∀ i, 1 ≤ z i → dat.d (g i) = some (nxt i) ∧ z i ≤ z (nxt i) := by
    intro i hi
    obtain ⟨i', h1, h2⟩ := hcon (g i) (by rw [hg i]; exact hi)
    rw [hg i] at h2
    refine ⟨?_, ?_⟩
    · simp [nxt, h1]
    · simp only [nxt, h1, Option.getD_some]
      exact h2
  have hpos : ∀ m, 1 ≤ z (nxt^[m] i0) := by
    intro m
    induction m with
    | zero => simp only [Function.iterate_zero, id]; omega
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (key _ ih).2
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun m : ℕ => nxt^[m] i0)
  have hab' : ∃ a b, a < b ∧ nxt^[a] i0 = nxt^[b] i0 := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, heq⟩
    · exact ⟨b, a, h, heq.symm⟩
  clear a b hab heq
  obtain ⟨a, b, hab, heq⟩ := hab'
  have hper : Function.IsPeriodicPt nxt (b - a) (nxt^[a] i0) := by
    show nxt^[b-a] (nxt^[a] i0) = nxt^[a] i0
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le]
    exact heq.symm
  have hposx : ∀ m, 1 ≤ z (nxt^[m] (nxt^[a] i0)) := by
    intro m
    rw [← Function.iterate_add_apply]
    exact hpos _
  obtain ⟨n, hn⟩ : ∃ n, b - a = n + 1 := ⟨b - a - 1, by omega⟩
  rw [hn] at hper
  apply h121.2 n (fun k => g (nxt^[k.val] (nxt^[a] i0)))
  intro k
  show dat.d (g (nxt^[k.val] (nxt^[a] i0)))
    = some (dat.u (g (nxt^[(k + 1 : Fin (n + 1)).val] (nxt^[a] i0))))
  rw [hg, (key _ (hposx k.val)).1, ← Function.iterate_succ_apply' nxt k.val (nxt^[a] i0),
    ← hper.iterate_mod_apply (k.val.succ)]
  congr 2
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]

open ProcessingNetworks.PacketNetworks in
theorem solution
    {I J K : ℕ} (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (cfg : LinkConfigData J K) (h124 : SatisfiesAssumption124 cfg)
    (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S)
    (z : Fin I → ℕ) (hz : z ≠ 0) :
    ∃ s, IsBPOptimal dat S (fun i => (z i : ℝ)) s ∧ s ≠ 0 := by
  obtain ⟨j, hj1, hj2⟩ := d6bc_exists_good_activity dat h121 z hz
  let e : Fin J → ℕ := fun j' => if j' = j then 1 else 0
  have heS : e ∈ S := by
    rw [hS]
    obtain ⟨k0, hk0, hk0u⟩ := cfg.hA j
    obtain ⟨c, hc, hck⟩ := h124 k0
    refine ⟨c, hc, ?_⟩
    intro k
    have hmv : (cfg.A.mulVec (fun j' => (e j' : ℝ))) k = cfg.A k j := by
      simp [Matrix.mulVec, dotProduct, e]
    rw [hmv]
    by_cases hk : k = k0
    · subst hk
      rw [hk0]
      exact_mod_cast hck
    · have hne : cfg.A k j ≠ 1 := fun h => hk (hk0u k h)
      rw [cfg.hA0 j k hne]
      positivity
  have hrealize : ∀ (M : Matrix (Fin I) (Fin J) ℝ) i, M.mulVec (realize e) i = M i j := by
    intro M i
    simp [Matrix.mulVec, dotProduct, realize, e]
  have heF : e ∈ feasibleSchedulesAt dat S (fun i => (z i : ℝ)) := by
    unfold feasibleSchedulesAt
    rw [Finset.mem_filter]
    refine ⟨heS, fun i => ?_⟩
    rw [hrealize]
    simp only [B]
    split_ifs with h
    · subst h
      exact_mod_cast hj1
    · positivity
  have hobj : 0 < bpObjective dat (fun i => (z i : ℝ)) e := by
    unfold bpObjective
    have hfun : (R dat).mulVec (realize e) = fun i => R dat i j := funext (hrealize _)
    rw [hfun]
    simp only [dotProduct, R, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    cases hd : dat.d j with
    | none =>
      simp
      exact_mod_cast hj1
    | some i' =>
      have hlt := hj2 i' hd
      simp
      have : (z i' : ℝ) < z (dat.u j) := by exact_mod_cast hlt
      linarith
  obtain ⟨s, hs, hmax⟩ :=
    (feasibleSchedulesAt dat S (fun i => (z i : ℝ))).exists_max_image
      (bpObjective dat (fun i => (z i : ℝ))) ⟨e, heF⟩
  refine ⟨s, ⟨hs, hmax⟩, ?_⟩
  rintro rfl
  have h1 := hmax e heF
  have hr0 : realize (0 : Fin J → ℕ) = 0 := by
    funext j'
    simp only [realize, Pi.zero_apply, Nat.cast_zero]
  have h0 : bpObjective dat (fun i => (z i : ℝ)) 0 = 0 := by
    rw [bpObjective, hr0, Matrix.mulVec_zero, dotProduct_zero]
  linarith
