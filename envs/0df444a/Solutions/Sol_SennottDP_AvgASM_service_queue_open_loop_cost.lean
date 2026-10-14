-- Prove2me | solution 1 for SennottDP.AvgASM.service_queue_open_loop_cost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:51:18.803733+00:00
-- url     : https://prove2.me/submissions/54312615-f176-4a52-9014-b7d586dce193

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Criteria
import Definitions.Def_SennottDP_AvgASM_ServiceQueue

open scoped ENNReal NNReal Topology
open Filter


namespace SennottDP.AvgASM

open Classical

set_option linter.unusedSectionVars false

variable {S : Type*} {Act : Type*} [Countable S]

open Classical in
/-- local copy of the t-step transition probabilities -/
noncomputable def sqN {T : Type*} (Q : T → T → ℝ≥0∞) : ℕ → T → T → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | t + 1, i, j => ∑' k, sqN Q t i k * Q k j

theorem sq_tsum_cons {X : Type*} (F : List X → ℝ≥0∞) (t : ℕ) :
    (∑' h : List X, if h.length = t + 1 then F h else 0) =
      ∑' x : X, ∑' rest : List X, if rest.length = t then F (x :: rest) else 0 := by
  rw [← ENNReal.tsum_prod]
  have hinj : Function.Injective (fun p : X × List X => p.1 :: p.2) := by
    intro p q h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2
  rw [← hinj.tsum_eq]
  · apply tsum_congr
    intro p
    simp
  · intro h hh
    rcases h with _ | ⟨x, rest⟩
    · simp at hh
    · exact ⟨(x, rest), rfl⟩

theorem sq_tsum_len0 {X : Type*} (F : List X → ℝ≥0∞) :
    (∑' h : List X, if h.length = 0 then F h else 0) = F [] := by
  rw [tsum_eq_single []]
  · simp
  · intro b hb
    rw [if_neg]
    intro h
    exact hb (List.length_eq_zero_iff.mp h)

/-- distribution of the state at time t -/
noncomputable def sq_D {M : MDC S Act} (θ : Policy M) (i : S) (t : ℕ) (j : S) : ℝ≥0∞ :=
  ∑' rest : List (S × Act), if rest.length = t then histProb θ i rest * prevWeight M i rest j else 0

theorem sq_D_eq {M : MDC S Act} (e : StationaryPolicy M) (i : S) (t : ℕ) (j : S) :
    sq_D e.toPolicy i t j = sqN e.chain t i j := by
  induction t generalizing j with
  | zero =>
    unfold sq_D
    rw [sq_tsum_len0]
    simp [histProb, prevWeight, sqN, eq_comm]
  | succ t ih =>
    unfold sq_D
    rw [sq_tsum_cons]
    rw [ENNReal.tsum_prod']
    simp only [sqN]
    apply tsum_congr
    intro k
    rw [← ih k]
    unfold sq_D
    rw [tsum_eq_single (e.f k)]
    · rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro rest
      split_ifs
      · simp [histProb, prevWeight, StationaryPolicy.toPolicy, StationaryPolicy.chain]
      · simp
    · intro b hb
      apply ENNReal.tsum_eq_zero.mpr
      intro rest
      split_ifs
      · simp [histProb, StationaryPolicy.toPolicy, hb]
      · rfl

theorem sq_expCost_eq {M : MDC S Act} (e : StationaryPolicy M) (i : S) (t : ℕ) :
    expCost e.toPolicy i t = ∑' j, sqN e.chain t i j * e.cost j := by
  unfold expCost
  rw [sq_tsum_cons, ENNReal.tsum_prod']
  apply tsum_congr
  intro k
  rw [← sq_D_eq]
  unfold sq_D
  rw [tsum_eq_single (e.f k)]
  · rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro rest
    split_ifs
    · simp [histProb, lastCost, StationaryPolicy.toPolicy, StationaryPolicy.cost]
    · simp
  · intro b hb
    apply ENNReal.tsum_eq_zero.mpr
    intro rest
    split_ifs
    · simp [histProb, StationaryPolicy.toPolicy, hb]
    · rfl

theorem sq_horizon_eq {M : MDC S Act} (e : StationaryPolicy M) (n : ℕ) (i : S) :
    horizonCost e.toPolicy n i = ∑ t ∈ Finset.range n, ∑' j, sqN e.chain t i j * e.cost j := by
  unfold horizonCost
  simp only [sq_expCost_eq]

theorem sq_sqN_sum (P : S → S → ℝ≥0∞) (hP : ∀ i, ∑' j, P i j = 1) (t : ℕ) (i : S) :
    ∑' j, sqN P t i j = 1 := by
  induction t with
  | zero => simp [sqN]
  | succ t ih =>
    simp only [sqN]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, hP, mul_one, ih]

theorem sq_sqN_succ_apply (P : S → S → ℝ≥0∞) (t : ℕ) (i : S) (w : S → ℝ≥0∞) :
    ∑' k, sqN P (t + 1) i k * w k = ∑' j, sqN P t i j * ∑' k, P j k * w k := by
  simp only [sqN]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr; intro j; apply tsum_congr; intro k; ring

theorem sq_iter (P : S → S → ℝ≥0∞) (hP : ∀ i, ∑' j, P i j = 1) (c w : S → ℝ≥0∞) (a : ℝ≥0∞)
    (h : ∀ i, c i + ∑' j, P i j * w j ≤ a + w i) (n : ℕ) (i : S) :
    (∑ t ∈ Finset.range n, ∑' j, sqN P t i j * c j) + ∑' j, sqN P n i j * w j
      ≤ n * a + w i := by
  induction n with
  | zero => simp [sqN]
  | succ n ih =>
    rw [Finset.sum_range_succ, sq_sqN_succ_apply, add_assoc, ← ENNReal.tsum_add]
    simp_rw [← mul_add]
    calc (∑ t ∈ Finset.range n, ∑' j, sqN P t i j * c j) +
          ∑' j, sqN P n i j * (c j + ∑' k, P j k * w k)
        ≤ (∑ t ∈ Finset.range n, ∑' j, sqN P t i j * c j) +
          ∑' j, sqN P n i j * (a + w j) := by
          exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (h j))
      _ = (∑ t ∈ Finset.range n, ∑' j, sqN P t i j * c j) + ∑' j, sqN P n i j * w j + a := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, sq_sqN_sum P hP]
          ring
      _ ≤ n * a + w i + a := by gcongr
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * a + w i := by push_cast; ring


theorem sq_avg_le {M : MDC S Act} (f : StationaryPolicy M) (w : S → ℝ≥0∞) (hw : ∀ i, w i < ⊤)
    (a : ℝ≥0∞) (h : ∀ i, f.cost i + ∑' j, f.chain i j * w j ≤ a + w i) (i : S) :
    avgCost f.toPolicy i ≤ a := by
  have hP : ∀ i, ∑' j, f.chain i j = 1 := fun i => M.P_sum i (f.f i) (f.mem i)
  have hb : ∀ n : ℕ, horizonCost f.toPolicy n i ≤ n * a + w i := by
    intro n
    rw [sq_horizon_eq]
    exact le_self_add.trans (sq_iter f.chain hP f.cost w a h n i)
  unfold avgCost
  have ht : Tendsto (fun n : ℕ => a + w i * (n : ℝ≥0∞)⁻¹) atTop (𝓝 a) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr (hw i).ne) (a := w i)
    simpa using tendsto_const_nhds.add this
  refine (limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)).trans_eq ht.limsup_eq
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  calc horizonCost f.toPolicy n i / n ≤ (n * a + w i) / n := by gcongr; exact hb n
    _ = a + w i * (n : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.add_div, mul_comm, ENNReal.mul_div_cancel_right hn0 (ENNReal.natCast_ne_top n),
        div_eq_mul_inv]


theorem sq_iter_eq (P : S → S → ℝ≥0∞) (hP : ∀ i, ∑' j, P i j = 1) (c w : S → ℝ≥0∞) (a : ℝ≥0∞)
    (h : ∀ i, c i + ∑' j, P i j * w j = a + w i) (n : ℕ) (i : S) :
    (∑ t ∈ Finset.range n, ∑' j, sqN P t i j * c j) + ∑' j, sqN P n i j * w j
      = n * a + w i := by
  induction n with
  | zero =>
    simp only [sqN]
    rw [tsum_eq_single i]
    · simp
    · intro j hj; simp [Ne.symm hj]
  | succ n ih =>
    rw [Finset.sum_range_succ, sq_sqN_succ_apply, add_assoc, ← ENNReal.tsum_add]
    simp_rw [← mul_add]
    simp_rw [h]
    simp_rw [mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, sq_sqN_sum P hP]
    calc (∑ t ∈ Finset.range n, ∑' j, sqN P t i j * c j) + (1 * a + ∑' j, sqN P n i j * w j)
        = ((∑ t ∈ Finset.range n, ∑' j, sqN P t i j * c j) + ∑' j, sqN P n i j * w j) + a := by ring
      _ = _ := by rw [ih]; push_cast; ring

theorem sq_lyap_avg {M : MDC S Act} (f : StationaryPolicy M) (i : S) (h k : S → ℝ≥0∞)
    (g c : ℝ≥0∞) (hc : c ≠ ⊤) (hh : ∀ j, h j ≠ ⊤) (hk : k i ≠ ⊤)
    (heq : ∀ j, f.cost j + ∑' l, f.chain j l * h l = g + h j)
    (hle : ∀ j, h j + ∑' l, f.chain j l * k l ≤ c + k j) :
    avgCost f.toPolicy i = g := by
  have hP : ∀ i, ∑' j, f.chain i j = 1 := fun i => M.P_sum i (f.f i) (f.mem i)
  have hEq := sq_iter_eq f.chain hP f.cost h g heq
  have hB : ∀ n : ℕ, (∑ t ∈ Finset.range n, ∑' j, sqN f.chain t i j * h j) ≤ n * c + k i :=
    fun n => le_self_add.trans (sq_iter f.chain hP h k c hle n i)
  apply le_antisymm
  · exact sq_avg_le f h (fun j => (hh j).lt_top) g (fun j => (heq j).le) i
  have hfreq : ∀ ε : ℝ≥0, 0 < ε → ∃ᶠ n : ℕ in atTop,
      ∑' j, sqN f.chain n i j * h j ≤ n * (ε : ℝ≥0∞) := by
    intro ε hε
    by_contra hcon
    rw [not_frequently] at hcon
    obtain ⟨T, hT⟩ := eventually_atTop.mp hcon
    set c' := c.toReal
    set k' := (k i).toReal
    have hε' : (0 : ℝ) < ε := hε
    obtain ⟨m, hm⟩ := exists_nat_gt ((2 * c' + k') / (ε : ℝ) + T + 1)
    have hc' : 0 ≤ c' := ENNReal.toReal_nonneg
    have hk' : 0 ≤ k' := ENNReal.toReal_nonneg
    have hdiv : 0 ≤ (2 * c' + k') / (ε : ℝ) := by positivity
    have hmT : T ≤ m := by
      have : (T : ℝ) < m := by linarith
      exact_mod_cast this.le
    have h1 : (m : ℝ≥0∞) * (m * (ε : ℝ≥0∞)) ≤
        ∑ t ∈ Finset.range (2 * m), ∑' j, sqN f.chain t i j * h j := by
      calc (m : ℝ≥0∞) * (m * (ε : ℝ≥0∞))
          = (Finset.Ico m (2 * m)).card • ((m : ℝ≥0∞) * (ε : ℝ≥0∞)) := by
            rw [Nat.card_Ico, nsmul_eq_mul]; congr 2; push_cast; omega
        _ ≤ ∑ t ∈ Finset.Ico m (2 * m), ∑' j, sqN f.chain t i j * h j := by
            apply Finset.card_nsmul_le_sum
            intro t ht
            rw [Finset.mem_Ico] at ht
            have := hT t (hmT.trans ht.1)
            rw [not_le] at this
            refine le_trans ?_ this.le
            gcongr
            exact_mod_cast ht.1
        _ ≤ _ := Finset.sum_le_sum_of_subset (fun t ht => by
            rw [Finset.mem_Ico] at ht; rw [Finset.mem_range]; exact ht.2)
    have h2 := h1.trans (hB (2 * m))
    have hfin : ((2 * m : ℕ) : ℝ≥0∞) * c + k i ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hc, hk⟩
    have h3 := ENNReal.toReal_mono hfin h2
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hc) hk] at h3
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal] at h3
    push_cast at h3
    have hm1 : (1 : ℝ) ≤ m := by linarith
    have h4 : (2 * c' + k') < m * (ε : ℝ) := by
      have := (div_lt_iff₀ hε').mp (show (2 * c' + k') / (ε : ℝ) < m by linarith)
      linarith
    nlinarith
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [← tsub_le_iff_right]
  unfold avgCost
  refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
  refine ((hfreq ε hε).and_eventually (eventually_ge_atTop 1)).mono fun n hn => ?_
  obtain ⟨hn, hn1⟩ := hn
  rw [sq_horizon_eq]
  have hE := hEq n i
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h5 : (n : ℝ≥0∞) * g ≤ (∑ t ∈ Finset.range n, ∑' j, sqN f.chain t i j * f.cost j) +
      n * (ε : ℝ≥0∞) := by
    calc (n : ℝ≥0∞) * g ≤ n * g + h i := le_self_add
      _ = _ := hE.symm
      _ ≤ _ := by gcongr
  rw [tsub_le_iff_right]
  calc g = n * g / n := by rw [mul_comm, ENNReal.mul_div_cancel_right hn0 (ENNReal.natCast_ne_top n)]
    _ ≤ ((∑ t ∈ Finset.range n, ∑' j, sqN f.chain t i j * f.cost j) + n * (ε : ℝ≥0∞)) / n := by
      gcongr
    _ = _ := by
      rw [ENNReal.add_div, mul_comm, ENNReal.mul_div_cancel_right hn0 (ENNReal.natCast_ne_top n)]


namespace ServiceQueueData

theorem sq_chain_sum (Q : ServiceQueueData) (a : ℝ) (ha : a ∈ Q.rates) (v : ℕ → ℝ≥0∞) (j : ℕ) :
    ∑' l, (Q.serveAt a ha).chain j l * v l =
      if j = 0 then ENNReal.ofReal (1 - Q.p) * v 0 + ENNReal.ofReal Q.p * v 1
      else ENNReal.ofReal (a * (1 - Q.p)) * v (j - 1) +
        ENNReal.ofReal (a * Q.p + (1 - a) * (1 - Q.p)) * v j +
        ENNReal.ofReal ((1 - a) * Q.p) * v (j + 1) := by
  by_cases hj : j = 0
  · subst hj
    simp only [StationaryPolicy.chain, serveAt, toMDC, if_true, add_mul, mul_assoc, ite_mul,
      one_mul, zero_mul]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    simp
  · simp only [StationaryPolicy.chain, serveAt, toMDC, hj, if_false, add_mul, mul_assoc, ite_mul,
      one_mul, zero_mul]
    rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
      ENNReal.tsum_mul_left]
    simp

theorem sq_cost (Q : ServiceQueueData) (a : ℝ) (ha : a ∈ Q.rates) (j : ℕ) :
    (Q.serveAt a ha).cost j = if j = 0 then 0 else
      ENNReal.ofReal ((Q.H : ℝ) * j + (Q.serviceCost a : ℝ)) := by
  by_cases hj : j = 0
  · simp [StationaryPolicy.cost, serveAt, toMDC, hj]
  · simp only [StationaryPolicy.cost, serveAt, toMDC, hj, if_false]
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1

theorem sq_apply (Q : ServiceQueueData) (a : ℝ) (ha : a ∈ Q.rates) (i : ℕ)
    (hR kR : ℝ → ℝ) (gR cR : ℝ) (hRnn : ∀ x, 0 ≤ hR x) (kRnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ kR x)
    (hgR0 : 0 ≤ gR) (hcR0 : 0 ≤ cR)
    (id0 : (1 - Q.p) * hR 0 + Q.p * hR 1 = gR + hR 0)
    (id1 : ∀ x : ℝ, 1 ≤ x → (Q.H : ℝ) * x + (Q.serviceCost a : ℝ) +
      (a * (1 - Q.p) * hR (x - 1) + (a * Q.p + (1 - a) * (1 - Q.p)) * hR x +
        (1 - a) * Q.p * hR (x + 1)) = gR + hR x)
    (in0 : hR 0 + ((1 - Q.p) * kR 0 + Q.p * kR 1) ≤ cR + kR 0)
    (in1 : ∀ x : ℝ, 1 ≤ x → hR x + (a * (1 - Q.p) * kR (x - 1) +
      (a * Q.p + (1 - a) * (1 - Q.p)) * kR x + (1 - a) * Q.p * kR (x + 1)) ≤ cR + kR x) :
    avgCost (Q.serveAt a ha).toPolicy i = ENNReal.ofReal gR := by
  have hp0 := Q.p_pos
  have hp1 := Q.p_lt_one
  have ha0 := Q.rates_pos a ha
  have ha1 := Q.rates_lt_one a ha
  have hp1' : 0 ≤ 1 - Q.p := by linarith
  have hmu0 : 0 ≤ a * (1 - Q.p) := by nlinarith
  have hnu0 : 0 ≤ a * Q.p + (1 - a) * (1 - Q.p) := by nlinarith
  have hlam0 : 0 ≤ (1 - a) * Q.p := by nlinarith
  have hHC : ∀ x : ℝ, 0 ≤ x → 0 ≤ (Q.H : ℝ) * x + (Q.serviceCost a : ℝ) := fun x hx => by
    have := NNReal.coe_nonneg Q.H; have := NNReal.coe_nonneg (Q.serviceCost a); positivity
  refine sq_lyap_avg (Q.serveAt a ha) i (fun j => ENNReal.ofReal (hR j))
    (fun j => ENNReal.ofReal (kR j))
    (ENNReal.ofReal gR) (ENNReal.ofReal cR) ENNReal.ofReal_ne_top (fun _ => ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top ?_ ?_
  · intro j
    rw [sq_chain_sum, sq_cost]
    by_cases hj : j = 0
    · subst hj
      simp only [if_true, zero_add, Nat.cast_zero, Nat.cast_one]
      rw [← ENNReal.ofReal_mul hp1', ← ENNReal.ofReal_mul hp0.le,
        ← ENNReal.ofReal_add (mul_nonneg hp1' (hRnn _)) (mul_nonneg hp0.le (hRnn _)),
        ← ENNReal.ofReal_add hgR0 (hRnn _), id0]
    · simp only [hj, if_false]
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
      have hjc : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hj)]; simp
      rw [hjc]
      push_cast
      have r1 := hRnn ((j:ℝ) - 1)
      have r2 := hRnn (j:ℝ)
      have r3 := hRnn ((j:ℝ) + 1)
      rw [← ENNReal.ofReal_mul hmu0, ← ENNReal.ofReal_mul hnu0, ← ENNReal.ofReal_mul hlam0,
        ← ENNReal.ofReal_add (mul_nonneg hmu0 r1) (mul_nonneg hnu0 r2),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hmu0 r1) (mul_nonneg hnu0 r2))
          (mul_nonneg hlam0 r3),
        ← ENNReal.ofReal_add (hHC _ (by linarith)) (by positivity),
        ← ENNReal.ofReal_add hgR0 r2, id1 _ hj1]
  · intro j
    rw [sq_chain_sum]
    by_cases hj : j = 0
    · subst hj
      simp only [if_true, Nat.cast_zero, Nat.cast_one]
      have k0 := kRnn 0 le_rfl
      have k1 := kRnn 1 zero_le_one
      rw [← ENNReal.ofReal_mul hp1', ← ENNReal.ofReal_mul hp0.le,
        ← ENNReal.ofReal_add (mul_nonneg hp1' k0) (mul_nonneg hp0.le k1),
        ← ENNReal.ofReal_add (hRnn _) (by positivity),
        ← ENNReal.ofReal_add hcR0 k0]
      exact ENNReal.ofReal_le_ofReal in0
    · simp only [hj, if_false]
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
      have hjc : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hj)]; simp
      rw [hjc]
      push_cast
      have k1 := kRnn ((j:ℝ) - 1) (by linarith)
      have k2 := kRnn (j:ℝ) (by linarith)
      have k3 := kRnn ((j:ℝ) + 1) (by linarith)
      rw [← ENNReal.ofReal_mul hmu0, ← ENNReal.ofReal_mul hnu0, ← ENNReal.ofReal_mul hlam0,
        ← ENNReal.ofReal_add (mul_nonneg hmu0 k1) (mul_nonneg hnu0 k2),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hmu0 k1) (mul_nonneg hnu0 k2))
          (mul_nonneg hlam0 k3),
        ← ENNReal.ofReal_add (hRnn _) (by positivity),
        ← ENNReal.ofReal_add hcR0 k2]
      exact ENNReal.ofReal_le_ofReal (in1 _ hj1)


theorem sq_reals (p a H C : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hpa : p < a) (ha1 : a < 1)
    (hH : 0 < H) (hC : 0 ≤ C) :
    ∃ (hR kR : ℝ → ℝ) (cR : ℝ), (∀ x, 0 ≤ hR x) ∧ (∀ x : ℝ, 0 ≤ x → 0 ≤ kR x) ∧ 0 ≤ cR ∧
      (1 - p) * hR 0 + p * hR 1 = (H * p * (1 - p) / (a - p) + p * C / a) + hR 0 ∧
      (∀ x : ℝ, 1 ≤ x → H * x + C +
        (a * (1 - p) * hR (x - 1) + (a * p + (1 - a) * (1 - p)) * hR x +
          (1 - a) * p * hR (x + 1)) = (H * p * (1 - p) / (a - p) + p * C / a) + hR x) ∧
      hR 0 + ((1 - p) * kR 0 + p * kR 1) ≤ cR + kR 0 ∧
      (∀ x : ℝ, 1 ≤ x → hR x + (a * (1 - p) * kR (x - 1) +
        (a * p + (1 - a) * (1 - p)) * kR x + (1 - a) * p * kR (x + 1)) ≤ cR + kR x) := by
  have ha0 : 0 < a := by linarith
  have hδ0 : 0 < a - p := by linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = H / (2 * (a - p)) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (C + α * (a * (1 - 2 * p))) / a := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = β ^ 2 / (4 * α) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = (α + 1) / (3 * (a - p)) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  have hHα : H = 2 * (a - p) * α := by rw [hα]; field_simp
  have hCβ : C = a * β - α * (a * (1 - 2 * p)) := by rw [hβ]; field_simp; ring
  have hg : H * p * (1 - p) / (a - p) + p * C / a = p * (α + β) := by
    rw [hβ, hα]; field_simp; ring
  have h3 : 3 * γ * (a - p) = α + 1 := by rw [hγ]; field_simp
  set σ := (1 - a) * p + a * (1 - p) with hσ
  refine ⟨fun x => α * x ^ 2 + β * x + K, fun x => γ * x ^ 3,
    (β + 3 * γ * σ) ^ 2 / 4 + K + γ, ?_, ?_, by positivity, ?_, ?_, ?_, ?_⟩
  · intro x
    have : α * x ^ 2 + β * x + K = α * (x + β / (2 * α)) ^ 2 := by
      rw [hK]; field_simp; ring
    simp only
    rw [this]; positivity
  · intro x hx; simp only; positivity
  · simp only
    rw [hg]; ring
  · intro x _
    simp only
    rw [hg, hHα, hCβ]; ring
  · simp only
    have : 0 ≤ (β + 3 * γ * σ) ^ 2 / 4 := by positivity
    nlinarith
  · intro x _
    simp only
    have e : α * x ^ 2 + β * x + K + (a * (1 - p) * (γ * (x - 1) ^ 3) +
        (a * p + (1 - a) * (1 - p)) * (γ * x ^ 3) + (1 - a) * p * (γ * (x + 1) ^ 3)) - γ * x ^ 3 =
        (α - 3 * γ * (a - p)) * x ^ 2 + (β + 3 * γ * σ) * x + K - γ * (a - p) := by
      rw [hσ]; ring
    rw [h3] at e
    have : 0 < γ * (a - p) := by positivity
    nlinarith [sq_nonneg (x - (β + 3 * γ * σ) / 2)]

theorem sq_core (Q : ServiceQueueData) (a : ℝ) (ha : a ∈ Q.rates)
    (hpa : Q.p < a) (i : ℕ) :
    avgCost (Q.serveAt a ha).toPolicy i =
      ENNReal.ofReal ((Q.H : ℝ) * Q.p * (1 - Q.p) / (a - Q.p) + Q.p * (Q.serviceCost a : ℝ) / a) := by
  obtain ⟨hR, kR, cR, h1, h2, h3, h4, h5, h6, h7⟩ := sq_reals Q.p a Q.H (Q.serviceCost a)
    Q.p_pos Q.p_lt_one hpa (Q.rates_lt_one a ha) Q.H_pos (NNReal.coe_nonneg _)
  have hg0 : 0 ≤ (Q.H : ℝ) * Q.p * (1 - Q.p) / (a - Q.p) + Q.p * (Q.serviceCost a : ℝ) / a := by
    have := Q.p_pos; have := Q.p_lt_one; have := Q.rates_pos a ha
    have : 0 < a - Q.p := by linarith
    have : 0 < 1 - Q.p := by linarith
    have := NNReal.coe_nonneg Q.H; have := NNReal.coe_nonneg (Q.serviceCost a)
    positivity
  exact sq_apply Q a ha i hR kR _ cR h1 h2 hg0 h3 h4 h5 h6 h7

end ServiceQueueData

end SennottDP.AvgASM

open SennottDP.AvgASM


theorem solution (Q : ServiceQueueData) (a : ℝ) (ha : a ∈ Q.rates)
    (hpa : Q.p < a) (i : ℕ) :
    avgCost (Q.serveAt a ha).toPolicy i =
      ENNReal.ofReal ((Q.H : ℝ) * Q.p * (1 - Q.p) / (a - Q.p) + Q.p * (Q.serviceCost a : ℝ) / a) := by
  exact ServiceQueueData.sq_core Q a ha hpa i
