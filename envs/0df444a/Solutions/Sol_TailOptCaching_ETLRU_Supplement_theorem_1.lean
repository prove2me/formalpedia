-- Prove2me | solution 1 for TailOptCaching.ETLRU.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:49:20.034109+00:00
-- url     : https://prove2.me/submissions/90417406-8492-4844-aaf4-9816d4fb7b32

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Supplement_Trace

open TailOptCaching
open TailOptCaching.ETLRU
open TailOptCaching.ETLRU.Supplement

theorem solution {N : ℕ} (tr : Trace N) (C ξ : ℕ) :
    (∃ x, IsTOBRun tr C ξ x) ∧
    ∀ x, IsTOBRun tr C ξ x →
      Feasible tr C x ∧ WithinBudget tr ξ x ∧
        ∀ y, Feasible tr C y → tel tr ξ x ≤ tel tr ξ y := by
          classical
          -- facts on next requests
          have L1 : ∀ (j : Fin N) (p : ℕ), p + 1 ∈ reqTimes tr j →
              nextReq tr j p = ((p + 1 : ℕ) : WithTop ℕ) := by
            intro j p h
            unfold nextReq
            apply le_antisymm
            · apply Finset.min_le
              simp [h]
            · apply Finset.le_min
              intro b hb
              rw [Finset.mem_filter] at hb
              exact WithTop.coe_le_coe.mpr hb.2
          have L2 : ∀ (j : Fin N) (p : ℕ), p + 1 ∉ reqTimes tr j →
              nextReq tr j p = nextReq tr j (p + 1) := by
            intro j p h
            unfold nextReq
            congr 1
            apply Finset.filter_congr
            intro s hs
            constructor
            · intro h1
              have : s ≠ p + 1 := by
                rintro rfl
                exact h hs
              omega
            · intro h1
              omega
          have L3 : ∀ (j : Fin N) (t s : ℕ), nextReq tr j t ≤ (s : WithTop ℕ) → t + 1 ≤ s := by
            intro j t s h
            have h2 : ((t + 1 : ℕ) : WithTop ℕ) ≤ nextReq tr j t := by
              unfold nextReq
              apply Finset.le_min
              intro b hb
              rw [Finset.mem_filter] at hb
              exact WithTop.coe_le_coe.mpr hb.2
            exact WithTop.coe_le_coe.mp (h2.trans h)
          have C1 : ∀ (j : Fin N) (p : ℕ), p + 1 ∈ reqTimes tr j →
              nextCap tr ξ j p = budget tr ξ j (p + 1) := by
            intro j p h
            unfold nextCap
            rw [L1 j p h]
            rfl
          have C2 : ∀ (j : Fin N) (p : ℕ), p + 1 ∉ reqTimes tr j →
              nextCap tr ξ j p = nextCap tr ξ j (p + 1) := by
            intro j p h
            unfold nextCap
            rw [L2 j p h]
          have R : ∀ (j : Fin N) (t : ℕ), t ∈ reqTimes tr j → 1 ≤ t ∧ t ≤ tr.T := by
            intro j t h
            unfold reqTimes at h
            rw [Finset.mem_filter, Finset.mem_Icc] at h
            exact h.1
          -- existence of an eviction
          have evict : ∀ (y : Fin N → ℕ) (r : Fin N → WithTop ℕ) (d : ℕ), d ≤ ∑ j, y j →
              ∃ z : Fin N → ℕ, (∀ j, z j ≤ y j) ∧ ∑ j, z j + d = ∑ j, y j ∧
                (∀ j k, z k < y k → r k < r j → z j = 0) := by
            intro y r d
            induction d with
            | zero =>
              intro _
              exact ⟨y, fun _ => le_rfl, by simp, fun j k h => absurd h (lt_irrefl _)⟩
            | succ d ih =>
              intro hd
              obtain ⟨z, hz1, hz2, hz3⟩ := ih (by omega)
              have hne : (Finset.univ.filter (fun j => 0 < z j)).Nonempty := by
                by_contra hcon
                rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
                have : ∑ j, z j = 0 := by
                  apply Finset.sum_eq_zero
                  intro j hj
                  have := hcon hj
                  omega
                omega
              obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ r hne
              rw [Finset.mem_filter] at hm
              have hs1 : ∑ j, z j = z m + ∑ j ∈ Finset.univ.erase m, z j :=
                (Finset.add_sum_erase _ _ (Finset.mem_univ m)).symm
              have hs2 : ∑ j, Function.update z m (z m - 1) j
                  = (z m - 1) + ∑ j ∈ Finset.univ.erase m, z j := by
                rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
                congr 1
                · simp
                · apply Finset.sum_congr rfl
                  intro j hj
                  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
              have hle : ∀ j, Function.update z m (z m - 1) j ≤ z j := by
                intro j
                by_cases hj : j = m
                · subst hj; simp
                · rw [Function.update_of_ne hj]
              refine ⟨Function.update z m (z m - 1), fun j => (hle j).trans (hz1 j), ?_, ?_⟩
              · have := hm.2
                omega
              · intro j k hk hr
                have hzj : z j = 0 := by
                  by_cases hkm : k = m
                  · subst hkm
                    by_contra hzj
                    have := hmax j (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by omega⟩)
                    exact absurd hr (not_lt.mpr this)
                  · rw [Function.update_of_ne hkm] at hk
                    exact hz3 j k hk hr
                have := hle j
                omega
          refine ⟨?_, ?_⟩
          · -- existence of a run
            have step : ∀ (w : Fin N → ℕ) (t : ℕ), ∃ z : Fin N → ℕ,
                (∀ j, z j ≤ cappedAlloc tr ξ (fun i _ => w i) t j) ∧
                ∑ j, z j = min C (∑ j, cappedAlloc tr ξ (fun i _ => w i) t j) ∧
                (∀ j k, z k < cappedAlloc tr ξ (fun i _ => w i) t k →
                  nextReq tr k t < nextReq tr j t → z j = 0) := by
              intro w t
              obtain ⟨z, h1, h2, h3⟩ := evict (cappedAlloc tr ξ (fun i _ => w i) t)
                (fun j => nextReq tr j t)
                ((∑ j, cappedAlloc tr ξ (fun i _ => w i) t j) - C) (by omega)
              exact ⟨z, h1, by omega, h3⟩
            choose f hf using step
            let g : ℕ → Fin N → ℕ := fun n => Nat.rec (fun _ => 0) (fun k w => f w (k + 1)) n
            have hg : ∀ k, g (k + 1) = f (g k) (k + 1) := fun k => rfl
            refine ⟨fun i t => g (t - 1) i, fun i => rfl, ?_⟩
            intro t ht _
            obtain ⟨p, rfl⟩ : ∃ p, t = p + 1 := ⟨t - 1, by omega⟩
            have hc : ∀ j, cappedAlloc tr ξ (fun i t => g (t - 1) i) (p + 1) j
                = cappedAlloc tr ξ (fun i _ => g p i) (p + 1) j := by
              intro j
              simp [cappedAlloc]
            have := hf (g p) (p + 1)
            unfold TOBStep
            simp only [hc]
            simpa [hg] using this
          intro x hx
          obtain ⟨hx0, hxs⟩ := hx
          have hfeas : Feasible tr C x := by
            refine ⟨hx0, ?_, ?_, ?_⟩
            · intro t h1 hT
              by_cases ht : t = 1
              · subst ht
                simp [hx0]
              · obtain ⟨p, rfl⟩ : ∃ p, t = p + 1 := ⟨t - 1, by omega⟩
                rw [(hxs p (by omega) (by omega)).2.1]
                exact min_le_left _ _
            · intro i t ht hT
              have := (hxs t (R i t ht).1 hT).1 i
              unfold cappedAlloc at this
              rw [if_pos ht] at this
              exact this.trans (min_le_left _ _)
            · intro i t h1 hT ht
              have := (hxs t h1 hT).1 i
              unfold cappedAlloc at this
              rw [if_neg ht] at this
              exact this.trans (min_le_left _ _)
          refine ⟨hfeas, ?_, ?_⟩
          · intro i t ht
            have hR := R i t ht
            by_cases h1 : t = 1
            · subst h1
              simp [hx0]
            · obtain ⟨p, rfl⟩ : ∃ p, t = p + 1 := ⟨t - 1, by omega⟩
              have := (hxs p (by omega) (by omega)).1 i
              unfold cappedAlloc at this
              rw [C1 i p ht] at this
              exact this.trans (min_le_right _ _)
          intro y hy
          obtain ⟨hy0, hyC, hyh, hym⟩ := hy
          -- capped hits through time p
          obtain ⟨H, hH⟩ : ∃ H : (Fin N → ℕ → ℕ) → ℕ → ℕ, ∀ z p, H z p =
              ∑ j, ∑ s ∈ Finset.range (p + 1), if s ∈ reqTimes tr j then min (z j s) (budget tr ξ j s) else 0 :=
            ⟨_, fun _ _ => rfl⟩
          obtain ⟨D, hD⟩ : ∃ D : (Fin N → ℕ → ℕ) → ℕ → ℕ → ℕ, ∀ z p s, D z p s =
              ∑ j, if nextReq tr j p ≤ (s : WithTop ℕ) then min (z j (p + 1)) (nextCap tr ξ j p) else 0 :=
            ⟨_, fun _ _ _ => rfl⟩
          obtain ⟨F, hF⟩ : ∃ F : (Fin N → ℕ → ℕ) → ℕ → ℕ → ℕ, ∀ z t s, F z t s =
              ∑ j, if t ∉ reqTimes tr j ∧ nextReq tr j t ≤ (s : WithTop ℕ)
                then min (z j t) (nextCap tr ξ j t) else 0 :=
            ⟨_, fun _ _ _ => rfl⟩
          have H0 : ∀ z, H z 0 = 0 := by
            intro z
            rw [hH]
            apply Finset.sum_eq_zero
            intro j _
            apply Finset.sum_eq_zero
            intro s hs
            rw [if_neg]
            intro hs'
            have := (R j s hs').1
            rw [Finset.mem_range] at hs
            omega
          have telH : ∀ z, tel tr ξ z + H z tr.T = ∑ i, ∑ t ∈ reqTimes tr i, budget tr ξ i t := by
            intro z
            have e : H z tr.T = ∑ i, ∑ t ∈ reqTimes tr i, min (z i t) (budget tr ξ i t) := by
              rw [hH]
              apply Finset.sum_congr rfl
              intro i _
              rw [← Finset.sum_filter]
              apply Finset.sum_congr _ (fun _ _ => rfl)
              ext s
              rw [Finset.mem_filter, Finset.mem_range]
              constructor
              · exact fun h => h.2
              · intro h
                have := (R i s h).2
                exact ⟨by omega, h⟩
            rw [e]
            unfold tel
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro t _
            unfold budget
            omega
          have A : ∀ z p s, p + 1 ≤ s → H z (p + 1) + F z (p + 1) s = H z p + D z p s := by
            intro z p s hs
            rw [hH, hH, hF, hD, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_range_succ _ (p + 1), add_assoc]
            congr 1
            by_cases h : p + 1 ∈ reqTimes tr j
            · have hle : nextReq tr j p ≤ (s : WithTop ℕ) := by
                rw [L1 j p h]
                exact WithTop.coe_le_coe.mpr hs
              rw [if_pos h, if_neg (fun hh => hh.1 h), if_pos hle, C1 j p h, add_zero]
            · rw [if_neg h, zero_add, L2 j p h, C2 j p h]
              simp [h]
          have F0 : ∀ z t s, s ≤ t → F z t s = 0 := by
            intro z t s hs
            rw [hF]
            apply Finset.sum_eq_zero
            intro j _
            rw [if_neg]
            intro hh
            have := L3 j t s hh.2
            omega
          -- main invariant
          have J : ∀ p, (∀ s, H y p + D y p s ≤ H x p + D x p s) →
              ∀ s, H y (p + 1) + F y (p + 1) s ≤ H x (p + 1) + F x (p + 1) s := by
            intro p hI s
            by_cases hs : p + 1 ≤ s
            · rw [A y p s hs, A x p s hs]
              exact hI s
            · rw [F0 y _ s (by omega), F0 x _ s (by omega)]
              have h1 := A y p (p + 1) le_rfl
              have h2 := A x p (p + 1) le_rfl
              rw [F0 _ _ _ le_rfl] at h1 h2
              have := hI (p + 1)
              omega
          have I : ∀ p, p + 1 ≤ tr.T → ∀ s, H y p + D y p s ≤ H x p + D x p s := by
            intro p
            induction p with
            | zero =>
              intro _ s
              rw [H0, H0, hD, hD]
              simp [hx0, hy0]
            | succ p ih =>
              intro hp s
              have hJ := J p (ih (by omega))
              obtain ⟨hs1, hs2, hs3⟩ := hxs (p + 1) (by omega) (by omega)
              by_cases hk : ∃ k, nextReq tr k (p + 1) ≤ (s : WithTop ℕ) ∧
                  x k (p + 1 + 1) < cappedAlloc tr ξ x (p + 1) k
              · obtain ⟨k, hk1, hk2⟩ := hk
                have hlt : ∑ j, x j (p + 1 + 1) < ∑ j, cappedAlloc tr ξ x (p + 1) j :=
                  Finset.sum_lt_sum (fun j _ => hs1 j) ⟨k, Finset.mem_univ _, hk2⟩
                have hDx : D x (p + 1) s = ∑ j, x j (p + 1 + 1) := by
                  rw [hD]
                  apply Finset.sum_congr rfl
                  intro j _
                  by_cases hj : nextReq tr j (p + 1) ≤ (s : WithTop ℕ)
                  · rw [if_pos hj]
                    apply min_eq_left
                    have := hs1 j
                    unfold cappedAlloc at this
                    exact this.trans (min_le_right _ _)
                  · rw [if_neg hj]
                    exact (hs3 j k hk2 (lt_of_le_of_lt hk1 (not_le.mp hj))).symm
                have hDy : D y (p + 1) s ≤ ∑ j, y j (p + 1 + 1) := by
                  rw [hD]
                  apply Finset.sum_le_sum
                  intro j _
                  split_ifs
                  · exact min_le_left _ _
                  · exact Nat.zero_le _
                have hC := hyC (p + 1 + 1) (by omega) (by omega)
                have h0 := hJ (p + 1)
                rw [F0 _ _ _ le_rfl, F0 _ _ _ le_rfl] at h0
                omega
              · push Not at hk
                have key : D y (p + 1) s + F x (p + 1) s ≤ D x (p + 1) s + F y (p + 1) s := by
                  rw [hD, hD, hF, hF, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
                  apply Finset.sum_le_sum
                  intro j _
                  by_cases hj : nextReq tr j (p + 1) ≤ (s : WithTop ℕ)
                  · have hxj : x j (p + 1 + 1) = cappedAlloc tr ξ x (p + 1) j :=
                      le_antisymm (hs1 j) (hk j hj)
                    unfold cappedAlloc at hxj
                    by_cases hr : p + 1 ∈ reqTimes tr j
                    · rw [if_pos hr] at hxj
                      have h3 := hyh j (p + 1) hr (by omega)
                      simp only [hj, hr, not_true, false_and, if_true, if_false]
                      omega
                    · rw [if_neg hr] at hxj
                      have h3 := hym j (p + 1) (by omega) (by omega) hr
                      simp only [hj, hr, not_false_iff, true_and, if_true]
                      omega
                  · simp [hj]
                have := hJ s
                omega
          have final : H y tr.T ≤ H x tr.T := by
            rcases Nat.eq_zero_or_pos tr.T with h | h
            · rw [h, H0, H0]
            · obtain ⟨p, hp⟩ : ∃ p, tr.T = p + 1 := ⟨tr.T - 1, by omega⟩
              have h0 := J p (I p (by omega)) (p + 1)
              rw [F0 _ _ _ le_rfl, F0 _ _ _ le_rfl] at h0
              rw [hp]
              omega
          have e1 := telH x
          have e2 := telH y
          omega
