-- Prove2me | solution 1 for ServiceParts.StockLevels.expected_on_hand
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:34:30.378838+00:00
-- url     : https://prove2.me/submissions/c410fe79-6ce0-4905-b337-39ea0cd1d514

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems



namespace ServiceParts.StockLevels

section CoreLemmas

lemma spc_cv_nonneg (u : ℕ → ℝ) (hun : ∀ j, 0 ≤ u j) :
    ∀ y n, 0 ≤ ServiceParts.Palm.convPow u y n := by
  intro y
  induction y with
  | zero => intro n; simp only [ServiceParts.Palm.convPow]; split_ifs <;> norm_num
  | succ y ih =>
    intro n; simp only [ServiceParts.Palm.convPow]
    exact Finset.sum_nonneg fun m _ => mul_nonneg (ih m) (hun _)

lemma spc_cv_zero (u : ℕ → ℝ) (hu0 : u 0 = 0) :
    ∀ y n, n < y → ServiceParts.Palm.convPow u y n = 0 := by
  intro y
  induction y with
  | zero => intro n h; omega
  | succ y ih =>
    intro n hn; simp only [ServiceParts.Palm.convPow]
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_range] at hm
    rcases lt_or_ge m y with h | h
    · rw [ih m h, zero_mul]
    · have : n - m = 0 := by omega
      rw [this, hu0, mul_zero]

lemma spc_cv_diag (u : ℕ → ℝ) (hun : ∀ j, 0 ≤ u j) :
    ∀ y, u 1 ^ y ≤ ServiceParts.Palm.convPow u y y := by
  intro y
  induction y with
  | zero => simp [ServiceParts.Palm.convPow]
  | succ y ih =>
    simp only [ServiceParts.Palm.convPow]
    have hy : y ∈ Finset.range (y + 1 + 1) := by simp
    have := Finset.single_le_sum (f := fun m => ServiceParts.Palm.convPow u y m * u (y + 1 - m))
      (fun m _ => mul_nonneg (spc_cv_nonneg u hun y m) (hun _)) hy
    have h1 : y + 1 - y = 1 := by omega
    simp only [h1] at this
    rw [pow_succ]
    exact le_trans (mul_le_mul_of_nonneg_right ih (hun 1)) this

lemma spc_snorm {f : ℕ → ℝ} (hf : Summable f) : Summable fun x => ‖f x‖ :=
  summable_norm_iff.mpr hf

lemma spc_cv_hasSum (u : ℕ → ℝ) (hun : ∀ j, 0 ≤ u j) (hus : HasSum u 1) (ub : ℝ)
    (hum : HasSum (fun j : ℕ => (j : ℝ) * u j) ub) :
    ∀ y, HasSum (ServiceParts.Palm.convPow u y) 1 ∧
      HasSum (fun n : ℕ => (n : ℝ) * ServiceParts.Palm.convPow u y n) (y * ub) := by
  intro y
  induction y with
  | zero =>
    constructor
    · have : ServiceParts.Palm.convPow u 0 = fun n => if n = 0 then (1 : ℝ) else 0 := by
        funext n; simp [ServiceParts.Palm.convPow]
      rw [this]; exact hasSum_ite_eq 0 1
    · have : (fun n : ℕ => (n : ℝ) * ServiceParts.Palm.convPow u 0 n) = fun _ => 0 := by
        funext n; simp only [ServiceParts.Palm.convPow]; split_ifs with h <;> simp [h]
      rw [this]; simpa using hasSum_zero
  | succ y ih =>
    have hdef : ServiceParts.Palm.convPow u (y + 1) =
        fun n => ∑ k ∈ Finset.range (n + 1), ServiceParts.Palm.convPow u y k * u (n - k) := by
      funext n; rfl
    constructor
    · have h1 := hasSum_sum_range_mul_of_summable_norm (spc_snorm ih.1.summable)
        (spc_snorm hus.summable)
      rw [ih.1.tsum_eq, hus.tsum_eq, one_mul] at h1
      rw [hdef]; exact h1
    · have hA := hasSum_sum_range_mul_of_summable_norm (spc_snorm ih.2.summable)
        (spc_snorm hus.summable)
      have hB := hasSum_sum_range_mul_of_summable_norm (spc_snorm ih.1.summable)
        (spc_snorm hum.summable)
      rw [ih.2.tsum_eq, hus.tsum_eq, ih.1.tsum_eq, hum.tsum_eq] at *
      have hC := hA.add hB
      have e1 : ((y + 1 : ℕ) : ℝ) * ub = y * ub * 1 + 1 * ub := by push_cast; ring
      rw [e1]
      have e2 : (fun n : ℕ => (n : ℝ) * ServiceParts.Palm.convPow u (y + 1) n) =
          fun n => ∑ k ∈ Finset.range (n + 1), (k : ℝ) * ServiceParts.Palm.convPow u y k
            * u (n - k) + ∑ k ∈ Finset.range (n + 1), ServiceParts.Palm.convPow u y k *
            (((n - k : ℕ) : ℝ) * u (n - k)) := by
        funext n
        rw [hdef]; dsimp only
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [Nat.cast_sub (by omega)]
        ring
      rw [e2]; exact hC

/-- Poisson weights. -/
noncomputable def spcW (a : ℝ) (y : ℕ) : ℝ := Real.exp (-a) * a ^ y / (y.factorial : ℝ)

lemma spcW_nonneg (a : ℝ) (ha : 0 ≤ a) (y : ℕ) : 0 ≤ spcW a y := by
  unfold spcW; positivity

lemma spcW_hasSum (a : ℝ) : HasSum (spcW a) 1 := by
  have := (NormedSpace.expSeries_div_hasSum_exp (a : ℝ)).mul_left (Real.exp (-a))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  have e : spcW a = fun i : ℕ => Real.exp (-a) * (a ^ i / (i.factorial : ℝ)) := by
    funext n; unfold spcW; ring
  rw [e]; exact this

lemma spcW_mean (a : ℝ) : HasSum (fun y : ℕ => spcW a y * y) a := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  have : (fun n : ℕ => spcW a (n + 1) * ((n + 1 : ℕ) : ℝ)) = fun n => a * spcW a n := by
    funext n; unfold spcW
    rw [Nat.factorial_succ]; push_cast
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp; ring
  rw [this]
  simpa using (spcW_hasSum a).mul_left a

variable (d : CompoundPoissonDemand)

lemma spc_pmf_eq (x : ℕ) : d.pmf x = ∑ y ∈ Finset.range (x + 1),
    spcW (d.lam * d.tbar) y * ServiceParts.Palm.convPow d.u y x := by
  unfold CompoundPoissonDemand.pmf
  split_ifs with hx
  · subst hx; simp [spcW, ServiceParts.Palm.convPow]
  · rw [Finset.sum_range_succ']
    have h0 : ServiceParts.Palm.convPow d.u 0 x = 0 := by simp [ServiceParts.Palm.convPow, hx]
    rw [h0, mul_zero, add_zero]
    rw [tsum_eq_sum (s := Finset.range x)]
    · apply Finset.sum_congr rfl; intro j _; unfold spcW; ring
    · intro j hj
      rw [Finset.mem_range, not_lt] at hj
      rw [spc_cv_zero d.u d.u_zero (j + 1) x (by omega), mul_zero]

lemma spc_pmf_nonneg (x : ℕ) : 0 ≤ d.pmf x := by
  rw [spc_pmf_eq]
  exact Finset.sum_nonneg fun y _ => mul_nonneg
    (spcW_nonneg _ (mul_pos d.lam_pos d.tbar_pos).le y) (spc_cv_nonneg d.u d.u_nonneg y x)

lemma spc_ubar : HasSum (fun j : ℕ => (j : ℝ) * d.u j) d.ubar := d.u_mean.hasSum

/-- joint hasSum machinery -/
lemma spc_joint (F : ℕ → ℕ → ℝ) (hF : ∀ y x, 0 ≤ F y x) (G : ℕ → ℝ) (A : ℝ)
    (hrow : ∀ y, HasSum (F y) (G y)) (hG : HasSum G A) (P : ℕ → ℝ)
    (hcol : ∀ x, HasSum (fun y => F y x) (P x)) : HasSum P A := by
  have hS : Summable (fun p : ℕ × ℕ => F p.1 p.2) := by
    rw [summable_prod_of_nonneg (fun p => hF p.1 p.2)]
    refine ⟨fun y => (hrow y).summable, ?_⟩
    have : (fun y => ∑' x, F y x) = G := funext fun y => (hrow y).tsum_eq
    simp only; rw [this]; exact hG.summable
  have h1 := hS.hasSum
  have h2 := h1.prod_fiberwise (fun y => hrow y)
  have hA : ∑' p : ℕ × ℕ, F p.1 p.2 = A := h2.unique hG
  rw [hA] at h1
  have h3 : HasSum ((fun p : ℕ × ℕ => F p.1 p.2) ∘ (Equiv.prodComm ℕ ℕ)) A :=
    (Equiv.hasSum_iff (Equiv.prodComm ℕ ℕ)).mpr h1
  exact h3.prod_fiberwise (fun x => by simpa using hcol x)

lemma spc_col (x : ℕ) (g : ℕ → ℝ) :
    HasSum (fun y => spcW (d.lam * d.tbar) y * (g x * ServiceParts.Palm.convPow d.u y x))
      (g x * d.pmf x) := by
  rw [spc_pmf_eq, Finset.mul_sum]
  have e : ∑ i ∈ Finset.range (x + 1), g x * (spcW (d.lam * d.tbar) i *
      ServiceParts.Palm.convPow d.u i x) = ∑ i ∈ Finset.range (x + 1),
      spcW (d.lam * d.tbar) i * (g x * ServiceParts.Palm.convPow d.u i x) := by
    apply Finset.sum_congr rfl; intro y _; ring
  rw [e]
  apply hasSum_sum_of_ne_finset_zero
  intro y hy
  rw [Finset.mem_range, not_lt] at hy
  rw [spc_cv_zero d.u d.u_zero y x (by omega)]; simp

lemma spc_pmf_hasSum : HasSum d.pmf 1 := by
  have hcv := spc_cv_hasSum d.u d.u_nonneg d.u_hasSum d.ubar (spc_ubar d)
  have ha := (mul_pos d.lam_pos d.tbar_pos).le
  have hrow : ∀ y, HasSum (fun x => spcW (d.lam * d.tbar) y * ((fun _ : ℕ => (1:ℝ)) x *
      ServiceParts.Palm.convPow d.u y x)) (spcW (d.lam * d.tbar) y) := by
    intro y
    have := (hcv y).1.mul_left (spcW (d.lam * d.tbar) y)
    rw [mul_one] at this
    have e : (fun x => spcW (d.lam * d.tbar) y * ((fun _ : ℕ => (1:ℝ)) x *
      ServiceParts.Palm.convPow d.u y x)) = fun x => spcW (d.lam * d.tbar) y *
        ServiceParts.Palm.convPow d.u y x := by funext x; simp only [one_mul]
    rw [e]; exact this
  have := spc_joint (fun y x => spcW (d.lam * d.tbar) y * ((fun _ : ℕ => (1:ℝ)) x *
      ServiceParts.Palm.convPow d.u y x))
    (fun y x => by
      simp only [one_mul]
      exact mul_nonneg (spcW_nonneg _ ha y) (spc_cv_nonneg d.u d.u_nonneg y x))
    (spcW (d.lam * d.tbar)) 1 hrow
    (spcW_hasSum _) (fun x => (fun _ : ℕ => (1:ℝ)) x * d.pmf x) (fun x => spc_col d x (fun _ : ℕ => (1:ℝ)))
  have e : (fun x => (fun _ : ℕ => (1:ℝ)) x * d.pmf x) = d.pmf := by funext x; simp only [one_mul]
  rw [e] at this; exact this

lemma spc_pmf_mean : HasSum (fun x : ℕ => (x : ℝ) * d.pmf x) (d.lam * d.tbar * d.ubar) := by
  have hcv := spc_cv_hasSum d.u d.u_nonneg d.u_hasSum d.ubar (spc_ubar d)
  have ha := (mul_pos d.lam_pos d.tbar_pos).le
  exact spc_joint (fun y x => spcW (d.lam * d.tbar) y * ((fun n : ℕ => (n : ℝ)) x *
      ServiceParts.Palm.convPow d.u y x))
    (fun y x => mul_nonneg (spcW_nonneg _ ha y)
      (mul_nonneg (Nat.cast_nonneg _) (spc_cv_nonneg d.u d.u_nonneg y x)))
    (fun y => spcW (d.lam * d.tbar) y * y * d.ubar) _
    (fun y => by
      have := (hcv y).2.mul_left (spcW (d.lam * d.tbar) y)
      rw [← mul_assoc] at this; exact this)
    ((spcW_mean _).mul_right d.ubar) _ (fun x => spc_col d x (fun n : ℕ => (n : ℝ)))

lemma spc_pmf_pos_of_u1 (h1 : d.u 1 = 1) (x : ℕ) : 0 < d.pmf x := by
  rw [spc_pmf_eq]
  have ha := mul_pos d.lam_pos d.tbar_pos
  have hx : x ∈ Finset.range (x + 1) := by simp
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun y => spcW (d.lam * d.tbar) y *
    ServiceParts.Palm.convPow d.u y x) (fun y _ => mul_nonneg (spcW_nonneg _ ha.le y)
      (spc_cv_nonneg d.u d.u_nonneg y x)) hx)
  have := spc_cv_diag d.u d.u_nonneg x
  rw [h1, one_pow] at this
  apply mul_pos _ (by linarith)
  unfold spcW; positivity

/-- tail of the pmf -/
lemma spc_tail (s : ℕ) : HasSum (fun x => if s < x then d.pmf x else 0) (1 - d.readyRate s) := by
  have hfin : HasSum (fun x => if x ∈ Finset.range (s + 1) then d.pmf x else 0) (d.readyRate s) := by
    unfold CompoundPoissonDemand.readyRate
    have e : ∑ x ∈ Finset.range (s + 1), d.pmf x = ∑ x ∈ Finset.range (s + 1),
        (if x ∈ Finset.range (s + 1) then d.pmf x else 0) := by
      apply Finset.sum_congr rfl; intro x hx; simp [hx]
    rw [e]
    apply hasSum_sum_of_ne_finset_zero
    intro x hx; simp [hx]
  have h3 := (spc_pmf_hasSum d).sub hfin
  have e : (fun x => d.pmf x - if x ∈ Finset.range (s + 1) then d.pmf x else 0) =
      (fun x => if s < x then d.pmf x else 0) := by
    funext x
    by_cases h : s < x
    · have : x ∉ Finset.range (s + 1) := by simp; omega
      simp [h, this]
    · have : x ∈ Finset.range (s + 1) := by simp; omega
      simp [h, this]
  rw [e] at h3; exact h3

lemma spc_bo_summable (s : ℕ) :
    Summable (fun x : ℕ => if s < x then ((x : ℝ) - s) * d.pmf x else 0) := by
  apply Summable.of_nonneg_of_le (f := fun x : ℕ => (x : ℝ) * d.pmf x)
  · intro x; split_ifs with h
    · have : (s : ℝ) < x := by exact_mod_cast h
      exact mul_nonneg (by linarith) (spc_pmf_nonneg d x)
    · exact le_rfl
  · intro x; split_ifs with h
    · have : (0:ℝ) ≤ s := Nat.cast_nonneg s
      nlinarith [spc_pmf_nonneg d x]
    · exact mul_nonneg (Nat.cast_nonneg _) (spc_pmf_nonneg d x)
  · exact (spc_pmf_mean d).summable

lemma spc_bo_hasSum (s : ℕ) :
    HasSum (fun x : ℕ => if s < x then ((x : ℝ) - s) * d.pmf x else 0) (d.backorders s) :=
  (spc_bo_summable d s).hasSum

lemma spc_bo_fdiff (s : ℕ) : fdiff d.backorders s = -(1 - d.readyRate s) := by
  unfold fdiff
  have h := (spc_bo_hasSum d s).sub (spc_bo_hasSum d (s + 1))
  have h2 : HasSum (fun x => if s < x then d.pmf x else 0) (d.backorders s - d.backorders (s+1)) := by
    refine (congrArg (HasSum · _) ?_).mp h
    funext x
    by_cases h1 : s < x
    · by_cases h2 : s + 1 < x
      · simp [h1, h2]; push_cast; ring
      · have : x = s + 1 := by omega
        subst this; simp
    · have : ¬ (s + 1 < x) := by omega
      simp [h1, this]
  have := h2.unique (spc_tail d s)
  linarith

lemma spc_ready_succ (s : ℕ) : d.readyRate (s + 1) = d.readyRate s + d.pmf (s + 1) := by
  unfold CompoundPoissonDemand.readyRate; rw [Finset.sum_range_succ]

lemma spc_bo_fdiff2 (s : ℕ) : fdiff2 d.backorders s = d.pmf (s + 1) := by
  unfold fdiff2; rw [spc_bo_fdiff, spc_bo_fdiff, spc_ready_succ]; ring

lemma spc_ready_mono {s t : ℕ} (h : s ≤ t) : d.readyRate s ≤ d.readyRate t := by
  unfold CompoundPoissonDemand.readyRate
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    (fun x _ _ => spc_pmf_nonneg d x)

lemma spc_ready_tendsto : Filter.Tendsto d.readyRate Filter.atTop (nhds 1) := by
  have := (spc_pmf_hasSum d).tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  exact this

end CoreLemmas

theorem backorder_differences_core (d : CompoundPoissonDemand) (s : ℕ) :
    fdiff d.backorders s = -(1 - d.readyRate s) ∧
    fdiff2 d.backorders s = d.pmf (s + 1) ∧
    0 ≤ fdiff2 d.backorders s ∧
    (d.u 1 = 1 → fdiff d.backorders s < 0 ∧ 0 < fdiff2 d.backorders s) := by
  refine ⟨spc_bo_fdiff d s, spc_bo_fdiff2 d s, by rw [spc_bo_fdiff2]; exact spc_pmf_nonneg d _, ?_⟩
  intro h1
  have hp := spc_pmf_pos_of_u1 d h1 (s + 1)
  refine ⟨?_, by rw [spc_bo_fdiff2]; exact hp⟩
  rw [spc_bo_fdiff]
  have := le_hasSum (spc_tail d s) (s + 1) (fun j _ => by
    split_ifs
    · exact spc_pmf_nonneg d j
    · exact le_rfl)
  simp only [lt_add_iff_pos_right, Nat.lt_one_iff, if_true, zero_lt_one] at this
  linarith

theorem expected_on_hand_core (d : CompoundPoissonDemand) (s : ℕ) :
    d.expectedOnHand s = (s : ℝ) - d.lam * d.tbar * d.ubar + d.backorders s := by
  have h1 := ((spc_pmf_hasSum d).mul_left (s : ℝ)).sub (spc_pmf_mean d)
  have hfin : HasSum (fun x : ℕ => if x ∈ Finset.range (s + 1) then ((s : ℝ) - x) * d.pmf x
      else 0) (d.expectedOnHand s) := by
    unfold CompoundPoissonDemand.expectedOnHand
    have e : ∑ x ∈ Finset.range (s + 1), ((s : ℝ) - x) * d.pmf x = ∑ x ∈ Finset.range (s + 1),
        (if x ∈ Finset.range (s + 1) then ((s : ℝ) - x) * d.pmf x else 0) := by
      apply Finset.sum_congr rfl; intro x hx; simp [hx]
    rw [e]
    apply hasSum_sum_of_ne_finset_zero
    intro x hx; simp [hx]
  have h2 := hfin.sub (spc_bo_hasSum d s)
  have e : (fun x : ℕ => (if x ∈ Finset.range (s + 1) then ((s : ℝ) - x) * d.pmf x else 0) -
      (if s < x then ((x : ℝ) - s) * d.pmf x else 0)) =
      fun x : ℕ => (s : ℝ) * d.pmf x - (x : ℝ) * d.pmf x := by
    funext x
    by_cases h : s < x
    · have : x ∉ Finset.range (s + 1) := by simp; omega
      simp only [h, this, if_true, if_false]; ring
    · have : x ∈ Finset.range (s + 1) := by simp; omega
      simp only [h, this, if_true, if_false]; ring
  rw [e] at h2
  have := h2.unique h1
  linarith

lemma spc_rc_fdiff (d : CompoundPoissonDemand) (c θ : ℝ) (s : ℕ) :
    fdiff (relaxedCost d c θ) s = -(1 + θ * c) * (1 - d.readyRate s) + θ * c := by
  have h := spc_bo_fdiff d s
  unfold fdiff at h ⊢
  unfold relaxedCost
  push_cast
  linear_combination (1 + θ * c) * h

lemma spc_mem_iff (d : CompoundPoissonDemand) (c θ : ℝ) (hc : 0 < c) (hθ : 0 < θ) (s : ℕ) :
    0 ≤ fdiff (relaxedCost d c θ) s ↔ s ∈ stockSet d c θ := by
  rw [spc_rc_fdiff]
  show _ ↔ 1 / (1 + θ * c) ≤ d.readyRate s
  have hk : 0 < 1 + θ * c := by positivity
  rw [div_le_iff₀ hk]
  constructor <;> intro h <;> nlinarith

theorem optimal_stock_criterion_core (d : CompoundPoissonDemand) (c θ : ℝ) (hc : 0 < c)
    (hθ : 0 < θ) :
    (∀ s, 0 ≤ fdiff2 (relaxedCost d c θ) s) ∧
    (∀ s, fdiff (relaxedCost d c θ) s = -(1 + θ * c) * (1 - d.readyRate s) + θ * c) ∧
    (∀ s, 0 ≤ fdiff (relaxedCost d c θ) s ↔ s ∈ stockSet d c θ) ∧
    (stockSet d c θ).Nonempty ∧
    ∀ sStar : ℕ, IsLeast (stockSet d c θ) sStar →
      (∀ s, relaxedCost d c θ sStar ≤ relaxedCost d c θ s) ∧
      (∀ s, s < sStar → relaxedCost d c θ sStar < relaxedCost d c θ s) := by
  have hk : 0 < 1 + θ * c := by positivity
  refine ⟨?_, spc_rc_fdiff d c θ, spc_mem_iff d c θ hc hθ, ?_, ?_⟩
  · intro s
    unfold fdiff2
    rw [spc_rc_fdiff, spc_rc_fdiff, spc_ready_succ]
    nlinarith [spc_pmf_nonneg d (s + 1)]
  · have hlt : 1 / (1 + θ * c) < 1 := by
      rw [div_lt_one hk]; nlinarith
    obtain ⟨s, hs⟩ := ((spc_ready_tendsto d).eventually (lt_mem_nhds hlt)).exists
    exact ⟨s, le_of_lt hs⟩
  · intro sStar hS
    have hdown : ∀ n s, s + (n + 1) = sStar →
        relaxedCost d c θ sStar < relaxedCost d c θ s := by
      intro n
      induction n with
      | zero =>
        intro s hs
        have hnot : s ∉ stockSet d c θ := fun hm => by
          have := hS.2 hm; omega
        rw [← spc_mem_iff d c θ hc hθ, not_le] at hnot
        unfold fdiff at hnot
        subst hs; simpa using hnot
      | succ n ih =>
        intro s hs
        have h1 := ih (s + 1) (by omega)
        have hnot : s ∉ stockSet d c θ := fun hm => by
          have := hS.2 hm; omega
        rw [← spc_mem_iff d c θ hc hθ, not_le] at hnot
        unfold fdiff at hnot
        linarith
    have hup : ∀ n, relaxedCost d c θ sStar ≤ relaxedCost d c θ (sStar + n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hm : sStar + n ∈ stockSet d c θ := by
          have := hS.1
          show 1 / (1 + θ * c) ≤ d.readyRate (sStar + n)
          exact le_trans this (spc_ready_mono d (by omega))
        rw [← spc_mem_iff d c θ hc hθ] at hm
        unfold fdiff at hm
        rw [← add_assoc]; linarith
    refine ⟨fun s => ?_, fun s hs => hdown (sStar - s - 1) s (by omega)⟩
    rcases le_or_gt sStar s with h | h
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
      exact hup n
    · exact (hdown (sStar - s - 1) s (by omega)).le

lemma spc_inv_mono (d : CompoundPoissonDemand) :
    Monotone (fun s : ℕ => (s : ℝ) + d.backorders s) := by
  apply monotone_nat_of_le_succ
  intro s
  have h := spc_bo_fdiff d s
  unfold fdiff at h
  have : 0 ≤ d.readyRate s := Finset.sum_nonneg fun x _ => spc_pmf_nonneg d x
  push_cast
  linarith

theorem optStock_antitone_core {ι : Type*} [Fintype ι] (d : ι → CompoundPoissonDemand)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂)
    (s₁ s₂ : ι → ℕ) (hs₁ : ∀ i, IsLeast (stockSet (d i) (c i) θ₁) (s₁ i))
    (hs₂ : ∀ i, IsLeast (stockSet (d i) (c i) θ₂) (s₂ i)) :
    (∀ i, s₂ i ≤ s₁ i) ∧ totalInvestment d c s₂ ≤ totalInvestment d c s₁ := by
  have hle : ∀ i, s₂ i ≤ s₁ i := by
    intro i
    apply (hs₂ i).2
    have h1 := (hs₁ i).1
    show 1 / (1 + θ₂ * c i) ≤ (d i).readyRate (s₁ i)
    refine le_trans ?_ h1
    have := hc i
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  refine ⟨hle, ?_⟩
  unfold totalInvestment
  apply Finset.sum_le_sum
  intro i _
  have := spc_inv_mono (d i) (hle i)
  simp only at this
  have := hc i
  nlinarith

lemma spc_sum_rc {ι : Type*} [Fintype ι] (d : ι → CompoundPoissonDemand) (c : ι → ℝ) (θ : ℝ)
    (s : ι → ℕ) : ∑ i, relaxedCost (d i) (c i) θ (s i) =
      totalBackorders d s + θ * totalInvestment d c s + θ * ∑ i, c i * (d i).mu := by
  unfold relaxedCost totalBackorders totalInvestment
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem lagrangian_stock_levels_optimal_core {ι : Type*} [Fintype ι]
    (d : ι → CompoundPoissonDemand) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (θ : ℝ) (hθ : 0 < θ) :
    (∀ i, (stockSet (d i) (c i) θ).Nonempty) ∧
    ∀ sStar : ι → ℕ, (∀ i, IsLeast (stockSet (d i) (c i) θ) (sStar i)) →
      ∀ s : ι → ℕ, totalInvestment d c s ≤ totalInvestment d c sStar →
        totalBackorders d sStar ≤ totalBackorders d s := by
  refine ⟨fun i => (optimal_stock_criterion_core (d i) (c i) θ (hc i) hθ).2.2.2.1, ?_⟩
  intro sStar hS s hinv
  have hsum : ∑ i, relaxedCost (d i) (c i) θ (sStar i) ≤ ∑ i, relaxedCost (d i) (c i) θ (s i) :=
    Finset.sum_le_sum fun i _ =>
      ((optimal_stock_criterion_core (d i) (c i) θ (hc i) hθ).2.2.2.2 (sStar i) (hS i)).1 (s i)
  rw [spc_sum_rc, spc_sum_rc] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hinv hθ.le]

end ServiceParts.StockLevels

open ServiceParts.StockLevels


theorem solution (d : CompoundPoissonDemand) (s : ℕ) :
    d.expectedOnHand s = (s : ℝ) - d.lam * d.tbar * d.ubar + d.backorders s := by
  exact expected_on_hand_core d s
