-- Prove2me | solution 1 for RobustPoA.Tight.proposition_5_2
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-17T12:31:21.474585+00:00
-- url     : https://prove2.me/submissions/aaa20237-9c69-4e14-9475-6de6818ccd4e

import Definitions.Def_RobustPoA_Tight_Classes
import Mathlib

set_option autoImplicit false

open RobustPoA.Tight
open CongestionPoA.AsymSum
open scoped BigOperators
open scoped ENNReal

/-- Proposition 5.2, p. 24: the robust price of anarchy of any game in the class
is bounded by the resourcewise best smoothness ratio gamma(C).
Proof: inline of the ACCEPTED params_subset argument (sub c3020257) shows every
resourcewise-smooth pair is smooth for this game G; then iInf antitone over the
inclusion smoothParams C ⊆ {p | p.2 < 1 ∧ IsSmoothCG G p.1 p.2} gives
robustPoACG G ≤ gamma C. -/
theorem solution (C : Set (ℕ → ℝ)) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) {k m : ℕ}
    (G : CongestionGame (Fin k) (Fin m)) (hG : InClass C G) :
    robustPoACG G ≤ gamma C := by
  have hkey : ∀ p ∈ smoothParams C, p.2 < 1 ∧ IsSmoothCG G p.1 p.2 := by
    intro p hp
    have hp' : p.2 < 1 ∧ ∀ c ∈ C, ∀ x x' : ℕ, 1 ≤ x' →
        c (x + 1) * (x' : ℝ) ≤ p.1 * (c x' * (x' : ℝ)) + p.2 * (c x * (x : ℝ)) := hp
    obtain ⟨hp2lt1, hsm⟩ := hp'
    -- Auxiliary: p.2 ≥ 0. Suppose p.2 < 0; pick c with c x0 > 0, apply the
    -- resourcewise constraint at (x0 + N, 1) with N large, contradiction.
    have hp2nonneg : 0 ≤ p.2 := by
      by_contra hcon
      have hp2neg : p.2 < 0 := not_le.mp hcon
      obtain ⟨c, hcC⟩ := hne
      have hc : (∀ x, 1 ≤ x → 0 ≤ c x) ∧ (∀ x y, 1 ≤ x → x ≤ y → c x ≤ c y) ∧
          ∃ x, 1 ≤ x ∧ c x ≠ 0 := hC c hcC
      obtain ⟨hc_nonneg, hc_mono, hc_ne⟩ := hc
      obtain ⟨x0, hx0, hx0ne⟩ := hc_ne
      have hc0 : 0 < c x0 := lt_of_le_of_ne (hc_nonneg x0 hx0) (Ne.symm hx0ne)
      have hneg : 0 < -p.2 := neg_pos.mpr hp2neg
      have hpos : 0 < (-p.2) * c x0 := mul_pos hneg hc0
      obtain ⟨N, hN⟩ := exists_nat_gt ((p.1 * c 1) / ((-p.2) * c x0))
      have hsm_inst := hsm c hcC (x0 + N) 1 (by norm_num)
      simp only [Nat.cast_one, mul_one] at hsm_inst
      have hge : c x0 ≤ c (x0 + N) := hc_mono x0 (x0 + N) hx0 (by omega)
      have hNN : p.1 * c 1 < (N : ℝ) * ((-p.2) * c x0) := (div_lt_iff₀ hpos).mp hN
      have hprod : c x0 * (N : ℝ) ≤ c (x0 + N) * ((x0 + N : ℕ) : ℝ) := by
        have h2 : (N : ℝ) ≤ ((x0 + N : ℕ) : ℝ) := by
          rw [Nat.cast_add]
          exact le_add_of_nonneg_left (Nat.cast_nonneg x0)
        exact le_trans (mul_le_mul_of_nonneg_right hge (Nat.cast_nonneg N))
          (mul_le_mul_of_nonneg_left h2 (le_trans hc0.le hge))
      have hmul : p.2 * (c (x0 + N) * ((x0 + N : ℕ) : ℝ)) ≤ p.2 * (c x0 * (N : ℝ)) :=
        mul_le_mul_of_nonpos_left hprod hp2neg.le
      have hlt : p.2 * (c x0 * (N : ℝ)) < -(p.1 * c 1) := by
        have heq : p.2 * (c x0 * (N : ℝ)) = -((N : ℝ) * ((-p.2) * c x0)) := by ring
        rw [heq]
        linarith [hNN]
      have hLHS : (0 : ℝ) ≤ c (x0 + N + 1) := hc_nonneg _ (by omega)
      linarith [hsm_inst, hLHS, hmul, hlt]
    refine ⟨hp2lt1, ?_⟩
    have hG' : (∀ e, G.latency e ∈ C) ∧ ∀ i, (G.strategies i).Nonempty := hG
    obtain ⟨hGlat, _hGstrat⟩ := hG'
    show ∀ (A A' : Fin k → Finset (Fin m)), IsProfile G A → IsProfile G A' →
        (∑ i, cost G (Function.update A i (A' i)) i) ≤
          p.1 * sumCost G A' + p.2 * sumCost G A
    intro A A' _hA _hA'
    -- Swap identity: sum over players of sums over their A'-strategies
    -- equals sum over resources of sums over players using them in A'.
    have hswap : ∀ (B : Fin k → Finset (Fin m)) (g : Fin k → Fin m → ℝ),
        (∑ i, ∑ e ∈ B i, g i e) =
          ∑ e, ∑ i ∈ Finset.univ.filter (fun i => e ∈ B i), g i e := by
      intro B g
      have h1 : ∀ i : Fin k, (∑ e ∈ B i, g i e) =
          ∑ e, (if e ∈ B i then g i e else 0) := by
        intro i
        rw [← Finset.sum_filter, Finset.filter_univ_mem]
      calc (∑ i, ∑ e ∈ B i, g i e)
          = ∑ i, ∑ e, (if e ∈ B i then g i e else 0) :=
            Finset.sum_congr rfl (fun i _ => h1 i)
        _ = ∑ e, ∑ i, (if e ∈ B i then g i e else 0) := Finset.sum_comm
        _ = ∑ e, ∑ i ∈ Finset.univ.filter (fun i => e ∈ B i), g i e :=
            Finset.sum_congr rfl (fun e _ => (Finset.sum_filter _ _).symm)
    -- Social cost regrouped by resource.
    have hsumCost : ∀ B : Fin k → Finset (Fin m), sumCost G B =
        ∑ e, G.latency e (load B e) * (load B e : ℝ) := by
      intro B
      calc sumCost G B = ∑ i, cost G B i := rfl
        _ = ∑ i, ∑ e ∈ B i, G.latency e (load B e) :=
            Finset.sum_congr rfl (fun i _ => rfl)
        _ = ∑ e, ∑ i ∈ Finset.univ.filter (fun i => e ∈ B i),
              G.latency e (load B e) := hswap B _
        _ = ∑ e, G.latency e (load B e) * (load B e : ℝ) := by
            apply Finset.sum_congr rfl
            intro e _
            have hcard : (Finset.univ.filter (fun i => e ∈ B i)).card = load B e := rfl
            rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]
    -- Per-resource bound: for fixed e, the deviation sum splits into
    -- y players with load x (those already using e) and x' - y players
    -- with load x + 1 (those newly using e), where y = |A ∩ A'| at e.
    have key : ∀ e : Fin m,
        (∑ i ∈ Finset.univ.filter (fun i => e ∈ A' i),
            G.latency e (load (Function.update A i (A' i)) e)) ≤
          p.1 * (G.latency e (load A' e) * (load A' e : ℝ)) +
            p.2 * (G.latency e (load A e) * (load A e : ℝ)) := by
      intro e
      have hfC : G.latency e ∈ C := hGlat e
      have hf : (∀ x, 1 ≤ x → 0 ≤ G.latency e x) ∧
          (∀ x y, 1 ≤ x → x ≤ y → G.latency e x ≤ G.latency e y) ∧
            ∃ x, 1 ≤ x ∧ G.latency e x ≠ 0 := hC _ hfC
      obtain ⟨hf_nonneg, hf_mono, _hf_ne⟩ := hf
      have hload_eq : ∀ i : Fin k, e ∈ A' i → e ∈ A i →
          load (Function.update A i (A' i)) e = load A e := by
        intro i hAi' hAi
        show (Finset.univ.filter (fun j => e ∈ Function.update A i (A' i) j)).card =
          (Finset.univ.filter (fun j => e ∈ A j)).card
        congr 1
        apply Finset.ext
        intro j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hji : j = i
        · subst hji
          rw [Function.update_self]
          exact iff_of_true hAi' hAi
        · rw [Function.update_of_ne hji]
      have hload_succ : ∀ i : Fin k, e ∈ A' i → e ∉ A i →
          load (Function.update A i (A' i)) e = load A e + 1 := by
        intro i hAi' hAi
        show (Finset.univ.filter (fun j => e ∈ Function.update A i (A' i) j)).card =
          (Finset.univ.filter (fun j => e ∈ A j)).card + 1
        have hnot : i ∉ Finset.univ.filter (fun j => e ∈ A j) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hAi
        have hset : Finset.univ.filter (fun j => e ∈ Function.update A i (A' i) j) =
            insert i (Finset.univ.filter (fun j => e ∈ A j)) := by
          apply Finset.ext
          intro j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self]
            simp [hAi']
          · rw [Function.update_of_ne hji]
            simp [hji]
        rw [hset, Finset.card_insert_of_notMem hnot]
      by_cases hx'0 : load A' e = 0
      · have hcard : (Finset.univ.filter (fun i => e ∈ A' i)).card = 0 := hx'0
        have hempty : Finset.univ.filter (fun i => e ∈ A' i) = ∅ :=
          Finset.card_eq_zero.mp hcard
        rw [hempty, Finset.sum_empty]
        have h2 : (0 : ℝ) ≤ p.2 * (G.latency e (load A e) * (load A e : ℝ)) := by
          by_cases hx0 : load A e = 0
          · simp [hx0]
          · have hx1 : 1 ≤ load A e := Nat.one_le_iff_ne_zero.mpr hx0
            exact mul_nonneg hp2nonneg
              (mul_nonneg (hf_nonneg _ hx1) (Nat.cast_nonneg _))
        rw [hx'0]
        simp only [Nat.cast_zero, mul_zero, zero_add]
        exact h2
      · have hx'1 : 1 ≤ load A' e := Nat.one_le_iff_ne_zero.mpr hx'0
        have hsplit := Finset.sum_filter_add_sum_filter_not
          (Finset.univ.filter (fun i => e ∈ A' i)) (fun i => e ∈ A i)
          (fun i => G.latency e (load (Function.update A i (A' i)) e))
        have hfirst : (∑ i ∈ (Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i),
            G.latency e (load (Function.update A i (A' i)) e)) =
            (((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card : ℝ) *
              G.latency e (load A e) := by
          calc (∑ i ∈ (Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i),
                G.latency e (load (Function.update A i (A' i)) e))
              = ∑ i ∈ (Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i),
                  G.latency e (load A e) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mem_filter] at hi
                obtain ⟨hi1, hi2⟩ := hi
                rw [Finset.mem_filter] at hi1
                obtain ⟨_, hiA'⟩ := hi1
                exact congrArg _ (hload_eq i hiA' hi2)
            _ = (((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card : ℝ) *
                  G.latency e (load A e) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        have hsecond : (∑ i ∈ (Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => ¬ e ∈ A i),
            G.latency e (load (Function.update A i (A' i)) e)) =
            (((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => ¬ e ∈ A i)).card : ℝ) *
              G.latency e (load A e + 1) := by
          calc (∑ i ∈ (Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => ¬ e ∈ A i),
                G.latency e (load (Function.update A i (A' i)) e))
              = ∑ i ∈ (Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => ¬ e ∈ A i),
                  G.latency e (load A e + 1) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mem_filter] at hi
                obtain ⟨hi1, hi2⟩ := hi
                rw [Finset.mem_filter] at hi1
                obtain ⟨_, hiA'⟩ := hi1
                exact congrArg _ (hload_succ i hiA' hi2)
            _ = (((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => ¬ e ∈ A i)).card : ℝ) *
                  G.latency e (load A e + 1) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card +
            ((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => ¬ e ∈ A i)).card =
              load A' e :=
          Finset.card_filter_add_card_filter_not _
        have hy_le : ((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card ≤
            load A' e := by omega
        have hnum : (((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card : ℝ) *
                G.latency e (load A e) +
              (((load A' e - ((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card : ℕ) : ℝ)) *
                G.latency e (load A e + 1) ≤
            p.1 * (G.latency e (load A' e) * (load A' e : ℝ)) +
              p.2 * (G.latency e (load A e) * (load A e : ℝ)) := by
          have hsm_inst := hsm (G.latency e) hfC (load A e) (load A' e) hx'1
          have hexpand : (((load A' e - ((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card : ℕ) : ℝ)) *
                  G.latency e (load A e + 1) =
              G.latency e (load A e + 1) * (load A' e : ℝ) -
                (((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card : ℝ) *
                  G.latency e (load A e + 1) := by
            rw [Nat.cast_sub hy_le]
            ring
          have hmono' : (((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card : ℝ) *
                  G.latency e (load A e) ≤
              (((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card : ℝ) *
                G.latency e (load A e + 1) := by
            by_cases hy0 : ((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card = 0
            · simp [hy0]
            · have hypos : 0 < ((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card :=
                Nat.pos_of_ne_zero hy0
              obtain ⟨i, hi⟩ := Finset.card_pos.mp hypos
              rw [Finset.mem_filter] at hi
              obtain ⟨hi1, hi2⟩ := hi
              rw [Finset.mem_filter] at hi1
              have hx1 : 1 ≤ load A e := by
                have hmem : i ∈ Finset.univ.filter (fun j => e ∈ A j) := by
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  exact hi2
                have hcard1 : 0 < (Finset.univ.filter (fun j => e ∈ A j)).card :=
                  Finset.card_pos.mpr ⟨i, hmem⟩
                show 1 ≤ (Finset.univ.filter (fun j => e ∈ A j)).card
                omega
              have hmono := hf_mono (load A e) (load A e + 1) hx1 (by omega)
              exact mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)
          rw [hexpand]
          linarith [hsm_inst, hmono']
        have hz : ((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => ¬ e ∈ A i)).card =
            load A' e - ((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card := by
          omega
        calc (∑ i ∈ Finset.univ.filter (fun i => e ∈ A' i),
                G.latency e (load (Function.update A i (A' i)) e))
            = (∑ i ∈ (Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i),
                  G.latency e (load (Function.update A i (A' i)) e)) +
                (∑ i ∈ (Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => ¬ e ∈ A i),
                  G.latency e (load (Function.update A i (A' i)) e)) := hsplit.symm
          _ = (((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card : ℝ) *
                G.latency e (load A e) +
              (((load A' e - ((Finset.univ.filter (fun i => e ∈ A' i)).filter (fun i => e ∈ A i)).card : ℕ) : ℝ)) *
                G.latency e (load A e + 1) := by
              rw [hfirst, hsecond, hz]
          _ ≤ p.1 * (G.latency e (load A' e) * (load A' e : ℝ)) +
                p.2 * (G.latency e (load A e) * (load A e : ℝ)) := hnum
    -- Assemble: deviation sum = resourcewise sum ≤ p.1 * sumCost A' + p.2 * sumCost A.
    have hcost : ∀ i : Fin k, cost G (Function.update A i (A' i)) i =
        ∑ e ∈ A' i, G.latency e (load (Function.update A i (A' i)) e) := by
      intro i
      show (∑ e ∈ Function.update A i (A' i) i,
        G.latency e (load (Function.update A i (A' i)) e)) = _
      rw [Function.update_self]
    calc (∑ i, cost G (Function.update A i (A' i)) i)
        = ∑ i, ∑ e ∈ A' i, G.latency e (load (Function.update A i (A' i)) e) :=
          Finset.sum_congr rfl (fun i _ => hcost i)
      _ = ∑ e, ∑ i ∈ Finset.univ.filter (fun i => e ∈ A' i),
            G.latency e (load (Function.update A i (A' i)) e) := hswap A' _
      _ ≤ ∑ e, (p.1 * (G.latency e (load A' e) * (load A' e : ℝ)) +
            p.2 * (G.latency e (load A e) * (load A e : ℝ))) :=
          Finset.sum_le_sum (fun e _ => key e)
      _ = (∑ e, p.1 * (G.latency e (load A' e) * (load A' e : ℝ))) +
            (∑ e, p.2 * (G.latency e (load A e) * (load A e : ℝ))) :=
          Finset.sum_add_distrib
      _ = p.1 * (∑ e, G.latency e (load A' e) * (load A' e : ℝ)) +
            p.2 * (∑ e, G.latency e (load A e) * (load A e : ℝ)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = p.1 * sumCost G A' + p.2 * sumCost G A := by
          rw [← hsumCost A', ← hsumCost A]
  show (⨅ p ∈ {p : ℝ × ℝ | p.2 < 1 ∧ IsSmoothCG G p.1 p.2},
      ENNReal.ofReal (p.1 / (1 - p.2))) ≤
    ⨅ p ∈ smoothParams C, ENNReal.ofReal (p.1 / (1 - p.2))
  apply le_iInf
  intro p
  apply le_iInf
  intro hp
  obtain ⟨hp2, hsm⟩ := hkey p hp
  exact iInf_le_of_le p (iInf_le_of_le ⟨hp2, hsm⟩ le_rfl)

theorem RobustPoA.Tight.proposition_5_2 (C : Set (ℕ → ℝ)) (hne : C.Nonempty)
    (hC : ∀ c ∈ C, IsCostFn c) {k m : ℕ}
    (G : CongestionGame (Fin k) (Fin m)) (hG : InClass C G) :
    robustPoACG G ≤ gamma C :=
  solution C hne hC G hG
