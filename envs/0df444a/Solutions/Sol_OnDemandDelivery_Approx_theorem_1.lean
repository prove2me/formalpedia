-- Prove2me | solution 1 for OnDemandDelivery.Approx.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T14:30:55.137405+00:00
-- url     : https://prove2.me/submissions/8b4f3163-348c-43ba-81a3-d4da4f4d9599

import Mathlib
import Definitions.Def_OnDemandDelivery_Approx_Setting

set_option autoImplicit false

open scoped ENNReal NNReal

namespace OnDemandDelivery.Approx.P0bfe

open OnDemandDelivery.Approx OnDemandDelivery.Approx.Model

variable {L : Type*}

lemma sf_mono (M : Model L) {A B : ℕ} (hAB : A ≤ B) {d : Demand L} {Y : Decision L}
    (h : M.SingleFeasible A d Y) : M.SingleFeasible B d Y :=
  ⟨le_trans h.1 hAB, h.2⟩

lemma Hs_anti (M : Model L) {A B : ℕ} (hAB : A ≤ B) (d : Demand L) : M.Hs B d ≤ M.Hs A d := by
  unfold Model.Hs
  refine le_iInf₂ fun Y hY => ?_
  exact iInf₂_le Y (sf_mono M hAB hY)

lemma EHs_anti (M : Model L) (n : ℕ) {A B : ℕ} (hAB : A ≤ B) : M.EHs n B ≤ M.EHs n A := by
  unfold Model.EHs
  exact ENNReal.tsum_le_tsum fun d => by gcongr; exact Hs_anti M hAB d

lemma le_next (M : Model L) (n : ℕ) (ζ : ℕ → ℕ) (Y : Decision L) (m : ℕ) :
    ζ m ≤ M.next n ζ Y m := by
  unfold Model.next
  split_ifs <;> omega

lemma H_lt (M : Model L) {n : ℕ} (h : n < M.N) (d : Demand L) (ζ : ℕ → ℕ) :
    M.H n d ζ = ⨅ (Y : Decision L) (_ : M.SingleFeasible (M.Kbar - ζ n) d Y),
      ((M.cost Y : ℝ≥0∞) + M.EH (n + 1) (M.next n ζ Y)) := by
  rw [Model.H, dif_pos h]
  rfl

lemma H_N (M : Model L) (d : Demand L) (ζ : ℕ → ℕ) :
    M.H M.N d ζ = M.Hs (M.Kbar - ζ M.N) d := by
  rw [Model.H, dif_neg (lt_irrefl _)]
  rfl

lemma EH_N (M : Model L) (ζ : ℕ → ℕ) : M.EH M.N ζ = M.EHs M.N (M.Kbar - ζ M.N) := by
  unfold Model.EH Model.EHs
  simp only [H_N]

lemma tsum_pmf_add (p : PMF (Demand L)) (f : Demand L → ℝ≥0∞) (c : ℝ≥0∞) :
    ∑' d, p d * (f d + c) = ∑' d, p d * f d + c := by
  simp only [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma Icc_sum_split (M : Model L) {m : ℕ} (h : m < M.N) (f : ℕ → ℝ≥0∞) :
    ∑ m' ∈ Finset.Icc m M.N, f m' = f m + ∑ m' ∈ Finset.Icc (m + 1) M.N, f m' := by
  rw [Finset.Icc_eq_cons_Ioc (by omega), Finset.sum_cons]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega

/-- Lower bound: the sum of single-period optima with the initially available drivers. -/
lemma lower (M : Model L) : ∀ k m (ζ : ℕ → ℕ), M.N - m = k → m ≤ M.N →
    ∑ m' ∈ Finset.Icc m M.N, M.EHs m' (M.Kbar - ζ m') ≤ M.EH m ζ := by
  intro k
  induction k with
  | zero =>
    intro m ζ hk hm
    have hmN : m = M.N := by omega
    subst hmN
    rw [Finset.Icc_self, Finset.sum_singleton, EH_N]
  | succ k ih =>
    intro m ζ hk hm
    have hlt : m < M.N := by omega
    rw [Icc_sum_split M hlt]
    have key : ∀ d, M.Hs (M.Kbar - ζ m) d +
        ∑ m' ∈ Finset.Icc (m + 1) M.N, M.EHs m' (M.Kbar - ζ m') ≤ M.H m d ζ := by
      intro d
      rw [H_lt M hlt]
      refine le_iInf₂ fun Y hY => ?_
      gcongr
      · exact iInf₂_le Y hY
      · calc ∑ m' ∈ Finset.Icc (m + 1) M.N, M.EHs m' (M.Kbar - ζ m')
            ≤ ∑ m' ∈ Finset.Icc (m + 1) M.N, M.EHs m' (M.Kbar - M.next m ζ Y m') := by
              gcongr with m' _
              exact EHs_anti M m' (by have := le_next M m ζ Y m'; omega)
          _ ≤ M.EH (m + 1) (M.next m ζ Y) := ih (m + 1) _ (by omega) (by omega)
    calc M.EHs m (M.Kbar - ζ m) + ∑ m' ∈ Finset.Icc (m + 1) M.N, M.EHs m' (M.Kbar - ζ m')
        = ∑' d, M.law m d * (M.Hs (M.Kbar - ζ m) d +
            ∑ m' ∈ Finset.Icc (m + 1) M.N, M.EHs m' (M.Kbar - ζ m')) := by
          rw [tsum_pmf_add]; rfl
      _ ≤ ∑' d, M.law m d * M.H m d ζ :=
          ENNReal.tsum_le_tsum fun d => by gcongr; exact key d
      _ = M.EH m ζ := rfl

lemma feas_lt (M : Model L) (π : M.StaticMyopic) {m : ℕ} (h : m < M.N) (ζ : ℕ → ℕ) :
    π.Feasible m ζ ↔ ∀ d ∈ (M.law m).support, π.K m + ζ m ≤ M.Kbar ∧ M.Hs (π.K m) d < ⊤ ∧
      π.Feasible (m + 1) (M.next m ζ (π.sel m d)) := by
  rw [Model.StaticMyopic.Feasible, dif_pos h]

lemma feas_N (M : Model L) (π : M.StaticMyopic) (ζ : ℕ → ℕ) :
    π.Feasible M.N ζ ↔ ∀ d ∈ (M.law M.N).support, π.K M.N + ζ M.N ≤ M.Kbar ∧
      M.Hs (π.K M.N) d < ⊤ := by
  rw [Model.StaticMyopic.Feasible, dif_neg (lt_irrefl _)]

lemma cost_lt (M : Model L) (π : M.StaticMyopic) {m : ℕ} (h : m < M.N) (ζ : ℕ → ℕ) :
    π.cost m ζ = ∑' d : Demand L, M.law m d *
      ((M.cost (π.sel m d) : ℝ≥0∞) + π.cost (m + 1) (M.next m ζ (π.sel m d))) := by
  rw [Model.StaticMyopic.cost, dif_pos h]

lemma cost_N (M : Model L) (π : M.StaticMyopic) (ζ : ℕ → ℕ) :
    π.cost M.N ζ = ∑' d : Demand L, M.law M.N d * (M.cost (π.sel M.N d) : ℝ≥0∞) := by
  rw [Model.StaticMyopic.cost, dif_neg (lt_irrefl _)]

/-- A feasible static myopic policy fits into the fleet in every later period. -/
lemma feas_fit (M : Model L) (π : M.StaticMyopic) : ∀ k m (ζ : ℕ → ℕ), M.N - m = k → m ≤ M.N →
    π.Feasible m ζ → ∀ m', m ≤ m' → m' ≤ M.N → π.K m' + ζ m' ≤ M.Kbar := by
  intro k
  induction k with
  | zero =>
    intro m ζ hk hm hf m' h1 h2
    have hmN : m = M.N := by omega
    subst hmN
    have hm' : m' = M.N := by omega
    subst hm'
    obtain ⟨d, hd⟩ := (M.law M.N).support_nonempty
    exact ((feas_N M π ζ).1 hf d hd).1
  | succ k ih =>
    intro m ζ hk hm hf m' h1 h2
    have hlt : m < M.N := by omega
    obtain ⟨d, hd⟩ := (M.law m).support_nonempty
    obtain ⟨h0, -, hnext⟩ := (feas_lt M π hlt ζ).1 hf d hd
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h; exact h0
    · have := ih (m + 1) _ (by omega) (by omega) hnext m' (by omega) h2
      have := le_next M m ζ (π.sel m d) m'
      omega

lemma tsum_support_le (p : PMF (Demand L)) (f g : Demand L → ℝ≥0∞)
    (h : ∀ d ∈ p.support, f d ≤ g d) : ∑' d, p d * f d ≤ ∑' d, p d * g d := by
  refine ENNReal.tsum_le_tsum fun d => ?_
  by_cases hd : p d = 0
  · simp [hd]
  · gcongr; exact h d ((PMF.mem_support_iff p d).2 hd)

/-- The policy's cost dominates the sum of its single-period optima. -/
lemma pol_lower (M : Model L) (π : M.StaticMyopic) : ∀ k m (ζ : ℕ → ℕ), M.N - m = k → m ≤ M.N →
    π.Feasible m ζ → ∑ m' ∈ Finset.Icc m M.N, M.EHs m' (π.K m') ≤ π.cost m ζ := by
  intro k
  induction k with
  | zero =>
    intro m ζ hk hm hf
    have hmN : m = M.N := by omega
    subst hmN
    rw [Finset.Icc_self, Finset.sum_singleton, cost_N]
    refine tsum_support_le _ _ _ fun d hd => ?_
    have hfin := ((feas_N M π ζ).1 hf d hd).2
    exact le_of_eq (π.myopic M.N d hfin).2.symm
  | succ k ih =>
    intro m ζ hk hm hf
    have hlt : m < M.N := by omega
    rw [Icc_sum_split M hlt, cost_lt M π hlt]
    unfold Model.EHs
    rw [← tsum_pmf_add]
    refine tsum_support_le _ _ _ fun d hd => ?_
    obtain ⟨-, hfin, hnext⟩ := (feas_lt M π hlt ζ).1 hf d hd
    gcongr
    · exact le_of_eq (π.myopic m d hfin).2.symm
    · exact ih (m + 1) _ (by omega) (by omega) hnext

/-- The optimal expected cost-to-go is at most the sum of the policy's single-period optima. -/
lemma pol_upper (M : Model L) (π : M.StaticMyopic) : ∀ k m (ζ : ℕ → ℕ), M.N - m = k → m ≤ M.N →
    π.Feasible m ζ → M.EH m ζ ≤ ∑ m' ∈ Finset.Icc m M.N, M.EHs m' (π.K m') := by
  intro k
  induction k with
  | zero =>
    intro m ζ hk hm hf
    have hmN : m = M.N := by omega
    subst hmN
    rw [Finset.Icc_self, Finset.sum_singleton, EH_N]
    have := feas_fit M π 0 M.N ζ (by omega) le_rfl hf M.N le_rfl le_rfl
    exact EHs_anti M _ (by omega)
  | succ k ih =>
    intro m ζ hk hm hf
    have hlt : m < M.N := by omega
    rw [Icc_sum_split M hlt]
    unfold Model.EH Model.EHs
    rw [← tsum_pmf_add]
    refine tsum_support_le _ _ _ fun d hd => ?_
    obtain ⟨h0, hfin, hnext⟩ := (feas_lt M π hlt ζ).1 hf d hd
    obtain ⟨hsf, hc⟩ := π.myopic m d hfin
    rw [H_lt M hlt]
    refine le_trans (iInf₂_le (π.sel m d) (sf_mono M (by omega) hsf)) ?_
    rw [hc]
    gcongr
    exact ih (m + 1) _ (by omega) (by omega) hnext

/-- Part 3: exactness in the last period. -/
lemma part3 (M : Model L) (ζ : ℕ → ℕ) (hζN : ζ M.N ≤ M.Kbar) (ω : ℕ → ℕ → ℕ → ℝ≥0) :
    M.Vapt M.N ζ ω = M.EH M.N ζ := by
  rw [EH_N]
  unfold Model.Vapt
  apply le_antisymm
  · refine iInf₂_le (fun _ => M.Kbar - ζ M.N) ?_ |>.trans ?_
    · intro n' hn'
      have : n' = M.N := by simp at hn'; omega
      subst this
      simp [Nat.cast_sub hζN]
    · simp
  · refine le_iInf₂ fun K hK => ?_
    have h := hK M.N (by simp)
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero] at h
    have hK' : K M.N ≤ M.Kbar - ζ M.N := by
      have : (K M.N : ℝ) ≤ ((M.Kbar - ζ M.N : ℕ) : ℝ) := by rw [Nat.cast_sub hζN]; exact h
      exact_mod_cast this
    simp only [Finset.Icc_self, Finset.sum_singleton]
    exact EHs_anti M _ hK'

end OnDemandDelivery.Approx.P0bfe

open OnDemandDelivery.Approx OnDemandDelivery.Approx.Model NNReal ENNReal in
theorem solution {L : Type*} [Fintype L] (M : Model L) (hM : M.Standing) (n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ M.N) (ζ : ℕ → ℕ) (hζ : ∀ n', n ≤ n' → n' ≤ M.N → ζ n' ≤ M.Kbar) :
    (∃ ω : ℕ → ℕ → ℕ → ℝ≥0, M.Vapt n ζ ω ≤ M.EH n ζ) ∧
    (∀ π : M.StaticMyopic, π.Feasible n ζ →
      ∃ ω : ℕ → ℕ → ℕ → ℝ≥0, M.EH n ζ ≤ M.Vapt n ζ ω ∧ M.Vapt n ζ ω ≤ π.cost n ζ) ∧
    (∀ ω : ℕ → ℕ → ℕ → ℝ≥0, M.Vapt M.N ζ ω = M.EH M.N ζ) := by
  have hζN : ζ M.N ≤ M.Kbar := hζ M.N hnN le_rfl
  refine ⟨?_, ?_, fun ω => P0bfe.part3 M ζ hζN ω⟩
  · -- P0bfe.lower bound with ω = 0
    refine ⟨fun _ _ _ => 0, ?_⟩
    refine le_trans ?_ (P0bfe.lower M (M.N - n) n ζ rfl hnN)
    unfold Model.Vapt
    refine iInf₂_le (fun m => M.Kbar - ζ m) ?_
    intro n' hn'
    rw [Finset.mem_Icc] at hn'
    simp [Nat.cast_sub (hζ n' hn'.1 hn'.2)]
  · intro π hπ
    have fit := P0bfe.feas_fit M π (M.N - n) n ζ rfl hnN hπ
    set c : ℝ≥0 := ((M.Kbar - ζ M.N - π.K M.N : ℕ) : ℝ≥0) with hc
    let ω : ℕ → ℕ → ℕ → ℝ≥0 := fun n' m k =>
      if k ≤ π.K m then (if n' = M.N ∧ m = n then c else 0) else ((M.Kbar : ℝ≥0) + 1)
    have hUp := P0bfe.pol_upper M π (M.N - n) n ζ rfl hnN hπ
    have hLo := P0bfe.pol_lower M π (M.N - n) n ζ rfl hnN hπ
    -- the policy's counts are feasible for APT
    have hVle : M.Vapt n ζ ω ≤ ∑ m' ∈ Finset.Icc n M.N, M.EHs m' (π.K m') := by
      unfold Model.Vapt
      refine iInf₂_le π.K ?_
      intro n' hn'
      rw [Finset.mem_Icc] at hn'
      have hfit := fit n' hn'.1 hn'.2
      have hsum : ∑ m ∈ Finset.Ico n n', ((ω n' m (π.K m) : ℝ≥0) : ℝ) ≤
          (if n' = M.N then (c : ℝ) else 0) := by
        simp only [ω, le_refl, if_true]
        by_cases hN : n' = M.N
        · simp only [hN, true_and, if_true]
          rw [← NNReal.coe_sum]
          rw [Finset.sum_ite_eq']
          split_ifs <;> simp
        · simp [hN]
      have hcN : (c : ℝ) = (M.Kbar : ℝ) - ζ M.N - π.K M.N := by
        have h1 := fit M.N hnN le_rfl
        rw [hc, NNReal.coe_natCast, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      by_cases hN : n' = M.N
      · subst hN
        rw [if_pos rfl] at hsum
        linarith
      · rw [if_neg hN] at hsum
        have : ((π.K n' : ℕ) : ℝ) + ζ n' ≤ M.Kbar := by exact_mod_cast hfit
        linarith
    refine ⟨ω, ?_, le_trans hVle hLo⟩
    rcases Nat.eq_or_lt_of_le hnN with hEq | hlt
    · subst hEq
      rw [P0bfe.part3 M ζ hζN ω]
    · refine le_trans hUp ?_
      unfold Model.Vapt
      refine le_iInf₂ fun K hK => ?_
      have hN := hK M.N (by simp [hnN])
      have hnonneg : ∀ m ∈ Finset.Ico n M.N, (0 : ℝ) ≤ ((ω M.N m (K m) : ℝ≥0) : ℝ) :=
        fun m _ => NNReal.coe_nonneg _
      have hKle : ∀ m ∈ Finset.Ico n M.N, K m ≤ π.K m := by
        intro m hm
        by_contra hgt
        have h1 := Finset.single_le_sum hnonneg hm
        have h2 : ((ω M.N m (K m) : ℝ≥0) : ℝ) = (M.Kbar : ℝ) + 1 := by
          simp [ω, hgt]
        have h3 : (0 : ℝ) ≤ K M.N := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ ζ M.N := Nat.cast_nonneg _
        linarith
      have hnmem : n ∈ Finset.Ico n M.N := by simp [hlt]
      have hKN : K M.N ≤ π.K M.N := by
        have h1 := Finset.single_le_sum hnonneg hnmem
        have h2 : ((ω M.N n (K n) : ℝ≥0) : ℝ) = (c : ℝ) := by
          simp [ω, hKle n hnmem]
        have h5 := fit M.N hnN le_rfl
        have hcN : (c : ℝ) = (M.Kbar : ℝ) - ζ M.N - π.K M.N := by
          rw [hc, NNReal.coe_natCast, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        have : (K M.N : ℝ) ≤ π.K M.N := by linarith
        exact_mod_cast this
      refine Finset.sum_le_sum fun m hm => P0bfe.EHs_anti M m ?_
      rw [Finset.mem_Icc] at hm
      rcases Nat.eq_or_lt_of_le hm.2 with h | h
      · subst h; exact hKN
      · exact hKle m (Finset.mem_Ico.2 ⟨hm.1, h⟩)
