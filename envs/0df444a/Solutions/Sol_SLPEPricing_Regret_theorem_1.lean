-- Prove2me | solution 1 for SLPEPricing.Regret.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:25:47.949623+00:00
-- url     : https://prove2.me/submissions/84a2944d-5b15-4e23-b9fc-6d2cd8408b0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model
import Theorems.Thm_SLPEPricing_Regret_lemma_4
import Theorems.Thm_SLPEPricing_Regret_round_count

open SLPEPricing.Regret

namespace SLPEAux

lemma delta_pow (μ : ℝ) (k : ℕ) : μ * Delta μ (k + 1) = (μ / 2) ^ (2 ^ k) := by
  induction k with
  | zero => simp [Delta]; ring
  | succ k ih =>
    have : Delta μ (k + 2) = μ * Delta μ (k + 1) ^ 2 := rfl
    rw [show k + 1 + 1 = k + 2 by ring, this, pow_succ 2 k, pow_mul, ← ih]
    ring

lemma delta_pos {μ : ℝ} (hμ : 0 < μ) (i : ℕ) : 0 < Delta μ i := by
  rcases i with _ | k
  · simp [Delta]
  · have h := delta_pow μ k
    have : Delta μ (k + 1) = (μ / 2) ^ (2 ^ k) / μ := by
      rw [eq_div_iff hμ.ne', mul_comm]; exact h
    rw [this]; positivity

lemma delta_le_half {μ : ℝ} (hμ : 0 < μ) (hμ2 : μ < 2) (i : ℕ) : Delta μ i ≤ 1 / 2 := by
  rcases i with _ | k
  · simp [Delta]
  · have h := delta_pow μ k
    have h1 : (μ / 2) ^ (2 ^ k) ≤ μ / 2 := by
      calc (μ / 2) ^ (2 ^ k) ≤ (μ / 2) ^ 1 :=
            pow_le_pow_of_le_one (by positivity) (by linarith) (Nat.one_le_two_pow)
        _ = μ / 2 := pow_one _
    have : μ * Delta μ (k + 1) ≤ μ * (1 / 2) := by rw [h]; linarith
    exact le_of_mul_le_mul_left this hμ

lemma delta_succ (μ : ℝ) (j : ℕ) (hj : 1 ≤ j) : Delta μ (j + 1) = μ * Delta μ j ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rfl

lemma nRound_pos {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) {T : ℕ} (hT : 2 ≤ T) (i : ℕ) :
    1 ≤ nRound μ ρ T i := by
  unfold nRound
  rw [Nat.one_le_ceil_iff]
  have hT' : (1 : ℝ) < T := by exact_mod_cast hT
  have := Real.log_pos hT'
  have := delta_pos hμ i
  positivity

lemma roundStart_succ (μ ρ : ℝ) (T i : ℕ) (hi : 1 ≤ i) :
    roundStart μ ρ T (i + 1) = roundStart μ ρ T i + 3 * nRound μ ρ T i := by
  unfold roundStart
  rw [Finset.sum_Ico_succ_top hi]; ring

lemma roundStart_mono (μ ρ : ℝ) (T : ℕ) {i j : ℕ} (hij : i ≤ j) :
    roundStart μ ρ T i ≤ roundStart μ ρ T j := by
  unfold roundStart
  apply Nat.mul_le_mul_left
  apply Finset.sum_le_sum_of_subset
  intro x hx; simp only [Finset.mem_Ico] at hx ⊢; omega

lemma roundStart_one (μ ρ : ℝ) (T : ℕ) : roundStart μ ρ T 1 = 0 := by
  simp [roundStart]

lemma roundStart_ge {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) {T : ℕ} (hT : 2 ≤ T) (i : ℕ) :
    3 * i ≤ roundStart μ ρ T (i + 1) := by
  unfold roundStart
  apply Nat.mul_le_mul_left
  calc i = ∑ _j ∈ Finset.Ico 1 (i + 1), 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun j _ => nRound_pos hμ hρ hT j)

lemma roundOf_spec {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) {T : ℕ} (hT : 2 ≤ T) (t : ℕ) :
    1 ≤ roundOf μ ρ T t ∧ roundOf μ ρ T t ≤ t + 1 ∧
      roundStart μ ρ T (roundOf μ ρ T t) ≤ t ∧ t < roundStart μ ρ T (roundOf μ ρ T t + 1) := by
  have hP1 : roundStart μ ρ T 1 ≤ t := by rw [roundStart_one]; exact Nat.zero_le _
  refine ⟨Nat.le_findGreatest (by omega) hP1, Nat.findGreatest_le _,
    Nat.findGreatest_spec (P := fun i => roundStart μ ρ T i ≤ t) (by omega) hP1, ?_⟩
  by_contra hcon
  push Not at hcon
  have hle : roundOf μ ρ T t + 1 ≤ t + 1 := by
    by_contra h2
    have heq : roundOf μ ρ T t = t + 1 := le_antisymm (Nat.findGreatest_le _) (by omega)
    rw [heq] at hcon
    have := roundStart_ge hμ hρ hT (t + 1)
    omega
  exact Nat.findGreatest_is_greatest (P := fun i => roundStart μ ρ T i ≤ t)
    (by unfold roundOf; omega) hle hcon

lemma roundOf_le {μ ρ : ℝ} (T t i : ℕ) (hi : i ≤ t + 1) (hs : roundStart μ ρ T i ≤ t) :
    i ≤ roundOf μ ρ T t :=
  Nat.le_findGreatest hi hs

/-- the set of rounds counted by `iMax` -/
noncomputable def F (μ ρ : ℝ) (T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter (fun i => roundStart μ ρ T i < T)

lemma roundOf_mem {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) {T : ℕ} (hT : 2 ≤ T) {t : ℕ}
    (ht : t < T) : roundOf μ ρ T t ∈ F μ ρ T := by
  obtain ⟨h1, h2, h3, -⟩ := roundOf_spec hμ hρ hT t
  simp only [F, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨h1, by omega⟩, by omega⟩

lemma blockPrice_near (q Δ : ℝ) (hΔ : 0 ≤ Δ) (s n t : ℕ) : |blockPrice q Δ s n t - q| ≤ Δ := by
  unfold blockPrice
  split_ifs <;> simp [abs_of_nonneg hΔ, hΔ]

end SLPEAux

open SLPEAux

/-! ### The price-change count -/

lemma slpe_lpc_le (d : ℝ → ℝ) (μ ρ : ℝ) (hμ : 0 < μ) (hρ : 0 < ρ)
    (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T : ℕ) (hT : 2 ≤ T) :
    lpc d μ ρ amax sel ε T ≤ 1 + 3 * iMax μ ρ T := by
  classical
  unfold lpc
  have hsub : (Finset.Ico 1 T).filter
      (fun t => price d μ ρ amax sel ε T t ≠ price d μ ρ amax sel ε T (t - 1)) ⊆
      (F μ ρ T ×ˢ Finset.range 3).image
        (fun x => roundStart μ ρ T x.1 + x.2 * nRound μ ρ T x.1) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Ico] at ht
    obtain ⟨⟨ht1, htT⟩, hne⟩ := ht
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
    obtain ⟨hi1, hit, his, hit2⟩ := roundOf_spec hμ hρ hT t
    have hmem := roundOf_mem hμ hρ hT htT
    set i := roundOf μ ρ T t with hi
    by_cases hst : roundStart μ ρ T i = t
    · exact ⟨i, 0, ⟨hmem, by norm_num⟩, by simp [hst]⟩
    · -- then `t - 1` lies in the same round
      have hlt : roundStart μ ρ T i ≤ t - 1 := by omega
      have hi' : roundOf μ ρ T (t - 1) = i := by
        apply le_antisymm
        · obtain ⟨-, h2, h3, -⟩ := roundOf_spec hμ hρ hT (t - 1)
          exact roundOf_le T t _ (by omega) (by omega)
        · have hg := roundStart_ge hμ hρ hT (i - 1)
          rw [show i - 1 + 1 = i by omega] at hg
          exact roundOf_le T (t - 1) i (by omega) hlt
      have hsplit := roundStart_succ μ ρ T i hi1
      have hn := nRound_pos hμ hρ hT i
      by_cases h1 : t = roundStart μ ρ T i + nRound μ ρ T i
      · exact ⟨i, 1, ⟨hmem, by norm_num⟩, by rw [h1]; ring⟩
      by_cases h2 : t = roundStart μ ρ T i + 2 * nRound μ ρ T i
      · exact ⟨i, 2, ⟨hmem, by norm_num⟩, by rw [h2]⟩
      exfalso
      apply hne
      unfold price
      rw [hi', ← hi]
      unfold blockPrice
      split_ifs <;> first | rfl | omega
  calc 1 + ((Finset.Ico 1 T).filter
        (fun t => price d μ ρ amax sel ε T t ≠ price d μ ρ amax sel ε T (t - 1))).card
      ≤ 1 + ((F μ ρ T ×ˢ Finset.range 3).image
        (fun x => roundStart μ ρ T x.1 + x.2 * nRound μ ρ T x.1)).card := by
        have := Finset.card_le_card hsub; omega
    _ ≤ 1 + (F μ ρ T ×ˢ Finset.range 3).card := by
        have := Finset.card_image_le (s := F μ ρ T ×ˢ Finset.range 3)
          (f := fun x => roundStart μ ρ T x.1 + x.2 * nRound μ ρ T x.1)
        omega
    _ = 1 + 3 * iMax μ ρ T := by
        rw [Finset.card_product, Finset.card_range]; unfold iMax F; ring

/-! ### Second-order revenue loss near the optimum -/

lemma slpe_revenue_loss (d : ℝ → ℝ) (pstar κ K₁ c μ ρ : ℝ) (h : Standing d pstar κ K₁ c μ ρ)
    (p : ℝ) (hp : |p - pstar| ≤ 1) : r d pstar - r d p ≤ 4 * K₁ * (p - pstar) ^ 2 := by
  have hd1 : Differentiable ℝ d := h.smooth.differentiable (by norm_num)
  have h2 : ContDiff ℝ 2 (deriv d) := by
    have h3 : ContDiff ℝ (2 + 1) d := by convert h.smooth using 1; first | rfl | norm_num | decide
    rw [contDiff_succ_iff_deriv] at h3
    exact h3.2.2
  have hdd : Differentiable ℝ (deriv d) := h2.differentiable (by norm_num)
  have hb0 : ∀ x ∈ Set.Icc (-1 : ℝ) 2, |d x| ≤ K₁ := fun x hx => by
    simpa using h.K1_bound 0 (by norm_num) x hx
  have hb1 : ∀ x ∈ Set.Icc (-1 : ℝ) 2, |deriv d x| ≤ K₁ := fun x hx => by
    simpa using h.K1_bound 1 (by norm_num) x hx
  have hb2 : ∀ x ∈ Set.Icc (-1 : ℝ) 2, |deriv (deriv d) x| ≤ K₁ := fun x hx => by
    have := h.K1_bound 2 (by norm_num) x hx
    simpa [iteratedDeriv_succ] using this
  set g : ℝ → ℝ := fun x => d x + x * deriv d x with hg
  have hr : ∀ x, HasDerivAt (r d) (g x) x := by
    intro x
    have h0 : HasDerivAt (fun y => y * d y) (1 * d x + x * deriv d x) x :=
      (hasDerivAt_id' x).mul (hd1 x).hasDerivAt
    show HasDerivAt (fun y => y * d y) _ x
    simpa using h0
  have hgd : ∀ x, HasDerivAt g (deriv d x + (deriv d x + x * deriv (deriv d) x)) x := by
    intro x
    have h0 : HasDerivAt (fun y => d y + y * deriv d y)
        (deriv d x + (1 * deriv d x + x * deriv (deriv d) x)) x :=
      (hd1 x).hasDerivAt.add ((hasDerivAt_id' x).mul (hdd x).hasDerivAt)
    simpa using h0
  -- `g p* = 0` since `p*` is an interior maximiser of `r`
  have hmax : IsLocalMax (r d) pstar := by
    have hpos := h.pstar_pos
    have hlt := h.pstar_lt_one
    filter_upwards [Ioo_mem_nhds hpos hlt] with x hx
    by_cases hxe : x = pstar
    · rw [hxe]
    · exact (h.unique_max x ⟨hx.1.le, hx.2.le⟩ hxe).le
  have hg0 : g pstar = 0 := by
    rw [← (hr pstar).deriv]; exact hmax.deriv_eq_zero
  set S := Set.uIcc pstar p with hS
  have hSsub : S ⊆ Set.Icc (-1 : ℝ) 2 := by
    have hpos := h.pstar_pos
    have hlt := h.pstar_lt_one
    have := abs_le.mp hp
    intro x hx
    rcases Set.mem_uIcc.mp hx with hx | hx <;> constructor <;> linarith [hx.1, hx.2]
  have hconv : Convex ℝ S := convex_uIcc _ _
  have hpS : pstar ∈ S := Set.left_mem_uIcc
  have hpS' : p ∈ S := Set.right_mem_uIcc
  have hdist : ∀ x ∈ S, |x - pstar| ≤ |p - pstar| := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with hx | hx
    · rw [abs_of_nonneg (by linarith [hx.1]), abs_of_nonneg (by linarith [hx.1, hx.2])]
      linarith [hx.2]
    · rw [abs_of_nonpos (by linarith [hx.2]), abs_of_nonpos (by linarith [hx.1, hx.2])]
      linarith [hx.1]
  have hK : 0 ≤ K₁ := le_trans (abs_nonneg _) (hb0 0 (by norm_num))
  have hgbound : ∀ x ∈ S, ‖g x‖ ≤ 4 * K₁ * |p - pstar| := by
    intro x hx
    have hder : ∀ y ∈ S, ‖deriv g y‖ ≤ 4 * K₁ := by
      intro y hy
      rw [(hgd y).deriv, Real.norm_eq_abs]
      have hy' := hSsub hy
      have h1 := hb1 y hy'
      have h2 := hb2 y hy'
      have hyabs : |y| ≤ 2 := abs_le.mpr ⟨by linarith [hy'.1], hy'.2⟩
      calc |deriv d y + (deriv d y + y * deriv (deriv d) y)|
          ≤ |deriv d y| + (|deriv d y| + |y| * |deriv (deriv d) y|) := by
            have e1 := abs_add_le (deriv d y) (deriv d y + y * deriv (deriv d) y)
            have e2 := abs_add_le (deriv d y) (y * deriv (deriv d) y)
            rw [abs_mul] at e2
            linarith
        _ ≤ K₁ + (K₁ + 2 * K₁) := by gcongr
        _ = 4 * K₁ := by ring
    have := hconv.norm_image_sub_le_of_norm_deriv_le (fun y _ => (hgd y).differentiableAt)
      hder hpS hx
    rw [hg0, sub_zero, Real.norm_eq_abs] at this
    calc ‖g x‖ ≤ 4 * K₁ * |x - pstar| := this
      _ ≤ 4 * K₁ * |p - pstar| := mul_le_mul_of_nonneg_left (hdist x hx) (by positivity)
  have hderr : ∀ y ∈ S, ‖deriv (r d) y‖ ≤ 4 * K₁ * |p - pstar| := by
    intro y hy; rw [(hr y).deriv]; exact hgbound y hy
  have := hconv.norm_image_sub_le_of_norm_deriv_le (fun y _ => (hr y).differentiableAt)
    hderr hpS hpS'
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  have hsq : |p - pstar| * |p - pstar| = (p - pstar) ^ 2 := by
    rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]
  have := neg_abs_le (r d p - r d pstar)
  nlinarith

/-! ### Per-period losses -/

lemma slpe_K_nonneg {d : ℝ → ℝ} {pstar κ K₁ c μ ρ : ℝ} (h : Standing d pstar κ K₁ c μ ρ) :
    0 ≤ K₁ := le_trans (abs_nonneg _) (by simpa using h.K1_bound 0 (by norm_num) 0 (by norm_num))

lemma slpe_mu_pos {d : ℝ → ℝ} {pstar κ K₁ c μ ρ : ℝ} (h : Standing d pstar κ K₁ c μ ρ) :
    0 < μ := by
  have hK := slpe_K_nonneg h
  have hc := h.c_pos
  have hρ := h.rho_pos
  have hκ := h.kappa_pos
  have : 0 < Mconst c ρ K₁ κ := by unfold Mconst; positivity
  exact lt_of_lt_of_le this h.mu_ge

lemma slpe_loss_round1 (d : ℝ → ℝ) (pstar κ K₁ c μ ρ : ℝ) (h : Standing d pstar κ K₁ c μ ρ)
    (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T t : ℕ)
    (h1 : roundOf μ ρ T t = 1) :
    r d pstar - r d (price d μ ρ amax sel ε T t) ≤ K₁ := by
  have hc : centre d μ ρ amax sel ε T 1 = 1 / 2 := rfl
  have hD : Delta μ 1 = 1 / 2 := rfl
  have hp : price d μ ρ amax sel ε T t ∈ Set.Icc (0 : ℝ) 1 := by
    unfold price; rw [h1, hc, hD]; unfold blockPrice
    split_ifs <;> norm_num
  have hrp : 0 ≤ r d (price d μ ρ amax sel ε T t) :=
    mul_nonneg hp.1 (h.nonneg _ hp)
  have hps : pstar ∈ Set.Icc (0 : ℝ) 1 := ⟨h.pstar_pos.le, h.pstar_lt_one.le⟩
  have hdK : d pstar ≤ K₁ := by
    have := h.K1_bound 0 (by norm_num) pstar ⟨by linarith [h.pstar_pos], by linarith [h.pstar_lt_one]⟩
    simp at this; exact le_trans (le_abs_self _) this
  have hd0 := h.nonneg pstar hps
  have : r d pstar ≤ K₁ := by
    unfold r
    nlinarith [h.pstar_lt_one, h.pstar_pos]
  linarith

lemma slpe_loss_later (d : ℝ → ℝ) (pstar κ K₁ c μ ρ : ℝ) (h : Standing d pstar κ K₁ c μ ρ)
    (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (hamax : IsArgmaxSelector amax)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T : ℕ) (hT : 2 ≤ T)
    (hA2 : Assumption2 μ ρ T sel ε) (hC : Concentration d μ ρ amax sel ε T)
    (t : ℕ) (ht : t < T) (hi : 2 ≤ roundOf μ ρ T t) :
    r d pstar - r d (price d μ ρ amax sel ε T t) ≤
      16 * K₁ * Delta μ (roundOf μ ρ T t) ^ 2 := by
  have hμ := slpe_mu_pos h
  have hρ := h.rho_pos
  obtain ⟨-, -, his, -⟩ := roundOf_spec hμ hρ hT t
  obtain ⟨j, hj⟩ : ∃ j, roundOf μ ρ T t = j + 1 := ⟨roundOf μ ρ T t - 1, by omega⟩
  have hj1 : 1 ≤ j := by omega
  rw [hj] at his
  have hgood : ∀ j' ∈ Finset.Icc 1 j,
      Assumption2At μ ρ T sel ε j' ∧ ConcentrationAt d μ ρ amax sel ε T j' := by
    intro j' hj'
    simp only [Finset.mem_Icc] at hj'
    have hU : UsedRound μ ρ T j' := by
      unfold UsedRound
      have := roundStart_mono μ ρ T (show j' + 1 ≤ j + 1 by omega)
      omega
    exact ⟨hA2 j' hj'.1 hU, hC j' hj'.1 hU⟩
  have h4 := lemma_4 d pstar κ K₁ c μ ρ h amax hamax sel ε T hT j hj1 hgood
  have hcen : ptilde d μ ρ amax sel ε T j = centre d μ ρ amax sel ε T (j + 1) := rfl
  rw [hcen] at h4
  have hDs := delta_succ μ j hj1
  have hMle : Mconst c ρ K₁ κ * Delta μ j ^ 2 ≤ Delta μ (j + 1) := by
    rw [hDs]; exact mul_le_mul_of_nonneg_right h.mu_ge (sq_nonneg _)
  have hDpos := delta_pos hμ (j + 1)
  have hbp := blockPrice_near (centre d μ ρ amax sel ε T (j + 1)) (Delta μ (j + 1)) hDpos.le
    (roundStart μ ρ T (j + 1)) (nRound μ ρ T (j + 1)) t
  have hprice : price d μ ρ amax sel ε T t = blockPrice (centre d μ ρ amax sel ε T (j + 1))
      (Delta μ (j + 1)) (roundStart μ ρ T (j + 1)) (nRound μ ρ T (j + 1)) t := by
    unfold price; rw [hj]
  rw [hj, hprice]
  set p := blockPrice (centre d μ ρ amax sel ε T (j + 1))
      (Delta μ (j + 1)) (roundStart μ ρ T (j + 1)) (nRound μ ρ T (j + 1)) t
  have hdist : |p - pstar| ≤ 2 * Delta μ (j + 1) := by
    have e := abs_sub_le p (centre d μ ρ amax sel ε T (j + 1)) pstar
    rw [abs_sub_comm (centre d μ ρ amax sel ε T (j + 1)) pstar] at e
    linarith
  have hhalf := delta_le_half hμ h.mu_lt (j + 1)
  have hloss := slpe_revenue_loss d pstar κ K₁ c μ ρ h p (by linarith)
  have hK := slpe_K_nonneg h
  have hsq : (p - pstar) ^ 2 ≤ (2 * Delta μ (j + 1)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hdist 2
  nlinarith

/-! ### Round lengths -/

lemma slpe_fiber_card {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) {T : ℕ} (hT : 2 ≤ T) (i : ℕ)
    (hi : 1 ≤ i) :
    ((Finset.range T).filter (fun t => roundOf μ ρ T t = i)).card ≤ 3 * nRound μ ρ T i ∧
    ((Finset.range T).filter (fun t => roundOf μ ρ T t = i)).card ≤ T := by
  constructor
  · have hsub : (Finset.range T).filter (fun t => roundOf μ ρ T t = i) ⊆
        Finset.Ico (roundStart μ ρ T i) (roundStart μ ρ T (i + 1)) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      obtain ⟨-, -, h3, h4⟩ := roundOf_spec hμ hρ hT t
      rw [ht.2] at h3 h4
      exact Finset.mem_Ico.mpr ⟨h3, h4⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico, roundStart_succ μ ρ T i hi] at this
    omega
  · exact (Finset.card_filter_le _ _).trans (by simp)

lemma slpe_sqrt_aux (a ρ L T : ℝ) (ha : 0 ≤ a) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (h : a ^ 2 ≤ 9 * ρ ^ 4 * L ^ 2 * T) : a ≤ 3 * ρ ^ 2 * L * Real.sqrt T := by
  have hb : 0 ≤ 3 * ρ ^ 2 * L * Real.sqrt T := by positivity
  have e : (3 * ρ ^ 2 * L * Real.sqrt T) ^ 2 = 9 * ρ ^ 4 * L ^ 2 * T := by
    rw [mul_pow, Real.sq_sqrt hT]; ring
  rw [← e] at h
  exact (pow_le_pow_iff_left₀ ha hb (by norm_num)).mp h

theorem solution (d : ℝ → ℝ) (pstar κ K₁ c μ ρ : ℝ) (h : Standing d pstar κ K₁ c μ ρ) :
    ∃ C₁ C₂ C₃ : ℝ, ∀ amax : (ℝ → ℝ) → ℝ → ℝ → ℝ, IsArgmaxSelector amax →
      ∀ T : ℕ, 3 ≤ T → ∀ (ε : ℕ → ℝ) (sel : ℕ → ℕ × ℕ × ℕ × ℕ),
        (lpc d μ ρ amax sel ε T : ℝ) ≤ C₃ + 3 * Real.logb 2 (Real.log (T : ℝ)) ∧
        (Assumption2 μ ρ T sel ε → Concentration d μ ρ amax sel ε T →
          regret d pstar μ ρ amax sel ε T ≤
            (C₁ + C₂ * Real.log (Real.log (T : ℝ))) * Real.sqrt (T : ℝ) * Real.log (T : ℝ)) := by
  have hμ := slpe_mu_pos h
  have hρ := h.rho_pos
  have hK := slpe_K_nonneg h
  obtain ⟨C₀, hC₀⟩ := SLPEPricing.Regret.round_count μ ρ hμ h.mu_lt hρ
  set D := 3 * K₁ * (32 * ρ ^ 4 + 1) + 16 * K₁ * (1 + 3 * ρ ^ 2) with hDdef
  have hD0 : 0 ≤ D := by positivity
  refine ⟨D * |C₀|, D / Real.log 2, 1 + 3 * C₀, ?_⟩
  intro amax hamax T hT ε sel
  have hT2 : 2 ≤ T := by omega
  have hT3 : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have hround := hC₀ T hT
  constructor
  · have := slpe_lpc_le d μ ρ hμ hρ amax sel ε T hT2
    have hc : (lpc d μ ρ amax sel ε T : ℝ) ≤ 1 + 3 * (iMax μ ρ T : ℝ) := by exact_mod_cast this
    linarith
  · intro hA2 hC
    set L := Real.log (T : ℝ) with hLdef
    have hL1 : 1 < L := by
      have : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9; norm_num at this; linarith
      rw [hLdef, Real.lt_log_iff_exp_lt (by linarith)]; linarith
    have hsT : 1 ≤ Real.sqrt (T : ℝ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    set W := Real.sqrt (T : ℝ) * L with hW
    have hLW : L ≤ W := by rw [hW]; nlinarith
    have hW1 : 1 ≤ W := by linarith
    -- each round contributes at most `D * W`
    have hfib : ∀ i ∈ F μ ρ T, ∑ t ∈ (Finset.range T).filter (fun t => roundOf μ ρ T t = i),
        (r d pstar - r d (price d μ ρ amax sel ε T t)) ≤ D * W := by
      intro i hiF
      have hi1 : 1 ≤ i := by simp only [F, Finset.mem_filter, Finset.mem_Icc] at hiF; exact hiF.1.1
      obtain ⟨hc1, hc2⟩ := slpe_fiber_card hμ hρ hT2 i hi1
      set S := (Finset.range T).filter (fun t => roundOf μ ρ T t = i) with hS
      have hnle : (nRound μ ρ T i : ℝ) < 2 * ρ ^ 4 * L / Delta μ i ^ 4 + 1 := by
        unfold nRound
        exact Nat.ceil_lt_add_one (by have := delta_pos hμ i; positivity)
      have hc1' : (S.card : ℝ) ≤ 3 * (nRound μ ρ T i : ℝ) := by exact_mod_cast hc1
      have hc2' : (S.card : ℝ) ≤ T := by exact_mod_cast hc2
      rcases Nat.lt_or_ge i 2 with hlt | hge
      · have hi : i = 1 := by omega
        have hb : ∀ t ∈ S, r d pstar - r d (price d μ ρ amax sel ε T t) ≤ K₁ := by
          intro t ht
          simp only [hS, Finset.mem_filter] at ht
          exact slpe_loss_round1 d pstar κ K₁ c μ ρ h amax sel ε T t (ht.2.trans hi)
        have hsum := Finset.sum_le_card_nsmul S _ K₁ hb
        rw [nsmul_eq_mul] at hsum
        have hD1 : Delta μ i = 1 / 2 := by rw [hi]; rfl
        rw [hD1] at hnle
        have : (S.card : ℝ) * K₁ ≤ 3 * K₁ * (32 * ρ ^ 4 + 1) * W := by
          have e1 : (S.card : ℝ) ≤ 3 * (32 * ρ ^ 4 * L + 1) := by
            have : 2 * ρ ^ 4 * L / (1 / 2) ^ 4 = 32 * ρ ^ 4 * L := by ring
            rw [this] at hnle; linarith
          have e2 : 32 * ρ ^ 4 * L + 1 ≤ (32 * ρ ^ 4 + 1) * W := by
            have : 0 ≤ ρ ^ 4 := by positivity
            nlinarith
          calc (S.card : ℝ) * K₁ ≤ 3 * (32 * ρ ^ 4 * L + 1) * K₁ :=
                mul_le_mul_of_nonneg_right e1 hK
            _ ≤ 3 * ((32 * ρ ^ 4 + 1) * W) * K₁ := by gcongr
            _ = _ := by ring
        have hp1 : 0 ≤ 16 * K₁ * (1 + 3 * ρ ^ 2) * W :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) (by positivity)) (by linarith)
        have hDW : D * W = 3 * K₁ * (32 * ρ ^ 4 + 1) * W + 16 * K₁ * (1 + 3 * ρ ^ 2) * W := by
          rw [hDdef]; ring
        linarith
      · set x := Delta μ i ^ 2 with hx
        have hxpos : 0 < x := by have := delta_pos hμ i; positivity
        have hxq : x ≤ 1 / 4 := by
          have := delta_le_half hμ h.mu_lt i
          have := delta_pos hμ i
          rw [hx]; nlinarith
        have hb : ∀ t ∈ S, r d pstar - r d (price d μ ρ amax sel ε T t) ≤ 16 * K₁ * x := by
          intro t ht
          simp only [hS, Finset.mem_filter, Finset.mem_range] at ht
          have := slpe_loss_later d pstar κ K₁ c μ ρ h amax hamax sel ε T hT2 hA2 hC t ht.1
            (by omega)
          rwa [ht.2] at this
        have hsum := Finset.sum_le_card_nsmul S _ _ hb
        rw [nsmul_eq_mul] at hsum
        have hD4 : Delta μ i ^ 4 = x ^ 2 := by rw [hx]; ring
        rw [hD4] at hnle
        -- `card * x ≤ 3 x + 3 ρ² L √T`
        have key : (S.card : ℝ) * x ≤ 3 * x + 3 * ρ ^ 2 * L * Real.sqrt T := by
          have hT0 : (0 : ℝ) ≤ T := by linarith
          have hprod : (T * x) * (6 * ρ ^ 4 * L / x) ≤ 9 * ρ ^ 4 * L ^ 2 * T := by
            have : (T * x) * (6 * ρ ^ 4 * L / x) = 6 * ρ ^ 4 * L * T := by
              field_simp
            rw [this]
            have h6 : 6 * L ≤ 9 * L ^ 2 := by nlinarith
            have h7 : 0 ≤ ρ ^ 4 * T := by positivity
            nlinarith [mul_le_mul_of_nonneg_left h6 h7]
          have hA0 : 0 ≤ 6 * ρ ^ 4 * L / x := by positivity
          have hB0 : 0 ≤ T * x := by positivity
          rcases le_total (T * x) (6 * ρ ^ 4 * L / x) with hab | hab
          · have : T * x ≤ 3 * ρ ^ 2 * L * Real.sqrt T := by
              apply slpe_sqrt_aux _ _ _ _ hB0 (by linarith) hT0
              nlinarith
            have : (S.card : ℝ) * x ≤ T * x := mul_le_mul_of_nonneg_right hc2' hxpos.le
            linarith
          · have h1 : 6 * ρ ^ 4 * L / x ≤ 3 * ρ ^ 2 * L * Real.sqrt T := by
              apply slpe_sqrt_aux _ _ _ _ hA0 (by linarith) hT0
              nlinarith
            have h2 : (S.card : ℝ) * x ≤ 3 * (2 * ρ ^ 4 * L / x ^ 2 + 1) * x :=
              mul_le_mul_of_nonneg_right (by linarith) hxpos.le
            have h3 : 3 * (2 * ρ ^ 4 * L / x ^ 2 + 1) * x = 6 * ρ ^ 4 * L / x + 3 * x := by
              field_simp; ring
            linarith
        have : (S.card : ℝ) * (16 * K₁ * x) ≤ 16 * K₁ * (1 + 3 * ρ ^ 2) * W := by
          have e : (S.card : ℝ) * (16 * K₁ * x) = 16 * K₁ * ((S.card : ℝ) * x) := by ring
          rw [e]
          have : (S.card : ℝ) * x ≤ (1 + 3 * ρ ^ 2) * W := by
            have : 3 * ρ ^ 2 * L * Real.sqrt T = 3 * ρ ^ 2 * W := by rw [hW]; ring
            have : 0 ≤ ρ ^ 2 := by positivity
            nlinarith
          calc 16 * K₁ * ((S.card : ℝ) * x) ≤ 16 * K₁ * ((1 + 3 * ρ ^ 2) * W) := by gcongr
            _ = _ := by ring
        have hp1 : 0 ≤ 3 * K₁ * (32 * ρ ^ 4 + 1) * W :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) (by positivity)) (by linarith)
        have hDW : D * W = 3 * K₁ * (32 * ρ ^ 4 + 1) * W + 16 * K₁ * (1 + 3 * ρ ^ 2) * W := by
          rw [hDdef]; ring
        linarith
    -- sum over the rounds
    have hmaps : ∀ t ∈ Finset.range T, roundOf μ ρ T t ∈ F μ ρ T := fun t ht =>
      roundOf_mem hμ hρ hT2 (Finset.mem_range.mp ht)
    have hreg : regret d pstar μ ρ amax sel ε T ≤ (iMax μ ρ T : ℝ) * (D * W) := by
      have e1 := Finset.sum_fiberwise_of_maps_to (s := Finset.range T) (t := F μ ρ T)
        (g := roundOf μ ρ T) (f := fun t => r d pstar - r d (price d μ ρ amax sel ε T t)) hmaps
      have := Finset.sum_le_card_nsmul (F μ ρ T) _ (D * W) hfib
      rw [nsmul_eq_mul, e1] at this
      exact this
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hll : 0 < Real.log L := Real.log_pos hL1
    have hiM : (iMax μ ρ T : ℝ) ≤ |C₀| + Real.log L / Real.log 2 := by
      have : Real.logb 2 L = Real.log L / Real.log 2 := rfl
      linarith [le_abs_self C₀]
    have hW0 : 0 ≤ W := by linarith
    calc regret d pstar μ ρ amax sel ε T ≤ (iMax μ ρ T : ℝ) * (D * W) := hreg
      _ ≤ (|C₀| + Real.log L / Real.log 2) * (D * W) :=
          mul_le_mul_of_nonneg_right hiM (mul_nonneg hD0 hW0)
      _ = (D * |C₀| + D / Real.log 2 * Real.log L) * Real.sqrt T * L := by
          rw [hW]; ring
