-- Prove2me | solution 1 for TwoEchelonCVRP.LowerBound.rfbar_elimination
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:55:04.612165+00:00
-- url     : https://prove2.me/submissions/f6849898-6643-4f2f-a2e0-78d5e7ff8bfc

import Definitions.Def_TwoEchelonCVRP_LowerBound_RFbar
open TwoEchelonCVRP.LowerBound
open scoped BigOperators

private lemma a_eq {I : Instance} (RS : RouteSystem I) (i : Fin I.nc) (l : RS.SR) :
    RS.a i l = if i ∈ RS.tour2 l then 1 else 0 := by
  by_cases h : i ∈ RS.tour2 l
  · simp [RouteSystem.a, h, List.count_eq_one_of_mem (RS.tour2_nodup l) h]
  · simp [RouteSystem.a, h, List.count_eq_zero_of_not_mem h]

private def ac {I : Instance} {RS : RouteSystem I} (s : SolF RS) (i : Fin I.nc) (k : Fin I.ns) : ℕ :=
  ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), RS.a i l * (s.x l).toNat

private lemma cover_sum {I : Instance} {RS : RouteSystem I} (s : SolF RS)
    (hs : IsFeasibleF RS s) (i : Fin I.nc) : ∑ l, RS.a i l * (s.x l).toNat = 1 := by
  simpa only [Finset.sum_filter, a_eq, ite_mul, one_mul, zero_mul] using hs.1 i

private lemma ac_sum {I : Instance} {RS : RouteSystem I} (s : SolF RS)
    (hs : IsFeasibleF RS s) (i : Fin I.nc) : ∑ k, ac s i k = 1 := by
  simp only [ac, Finset.sum_filter]
  rw [Finset.sum_comm]
  simpa using cover_sum s hs i

private def convertF {I : Instance} {RS : RouteSystem I} (s : SolF RS) : SolRF RS where
  ξ i k := decide (ac s i k = 1)
  y := s.y
  qd := s.qd

private lemma convert_count {I : Instance} {RS : RouteSystem I} (s : SolF RS)
    (hs : IsFeasibleF RS s) (i : Fin I.nc) (k : Fin I.ns) : ((convertF s).ξ i k).toNat = ac s i k := by
  have hc : ac s i k ≤ 1 := by
    rw [← ac_sum s hs i]
    exact Finset.single_le_sum (f := ac s i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  by_cases he : ac s i k = 1
  · simp [convertF, he]
  · have hz : ac s i k = 0 := by omega
    simp [convertF, hz]

private lemma q_a_sum {I : Instance} (RS : RouteSystem I) (l : RS.SR) :
    ∑ i, I.q i * RS.a i l = RS.w l := by
  simp only [a_eq, mul_ite, mul_one, mul_zero, RouteSystem.w, RouteSystem.Rcust]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

private lemma convert_load {I : Instance} {RS : RouteSystem I} (s : SolF RS)
    (hs : IsFeasibleF RS s) (k : Fin I.ns) : (convertF s).load k =
      ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), RS.w l*(s.x l).toNat := by
  simp only [SolRF.load, convert_count s hs, ac, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [← mul_assoc, ← Finset.sum_mul, q_a_sum]

private lemma convert_feasible {I : Instance} {RS : RouteSystem I} (s : SolF RS)
    (hs : IsFeasibleF RS s) : IsFeasibleRF RS (convertF s) := by
  refine ⟨?_, ?_, ?_, hs.2.2.2.2.1, hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2⟩
  · intro i
    simp only [convert_count s hs]
    exact ac_sum s hs i
  · intro k
    rw [convert_load s hs]
    exact hs.2.2.2.2.2.1 k
  · intro k
    rw [convert_load s hs]
    exact hs.2.2.2.1 k

private lemma convert_fleet {I : Instance} {RS : RouteSystem I} (s : SolF RS)
    (hs : IsFeasibleF RS s) (k : Fin I.ns) : (convertF s).load k ≤ I.m k*I.Q2 := by
  rw [convert_load s hs]
  calc
    _ ≤ ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), I.Q2*(s.x l).toNat := by
      exact Finset.sum_le_sum (fun l hl => Nat.mul_le_mul_right _ (RS.cap2 l))
    _ = I.Q2*(∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), (s.x l).toNat) := by rw [Finset.mul_sum]
    _ ≤ _ := by nlinarith [hs.2.1 k]

private lemma assignment_bill {I : Instance} {RS : RouteSystem I} (s : SolF RS)
    (hs : IsFeasibleF RS s) (β : Fin I.nc → Fin I.ns → ℝ) :
    (∑ k, ∑ i, β i k*((convertF s).ξ i k).toNat) =
      ∑ l, (∑ i, (RS.a i l : ℝ)*β i (RS.sat l))*((s.x l).toNat : ℝ) := by
  simp only [convert_count s hs, ac, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum, Finset.sum_filter,
    Nat.cast_ite, Nat.cast_mul, Nat.cast_zero, mul_ite, mul_zero]
  calc
    _ = ∑ i, ∑ l, ∑ k, if RS.sat l = k then β i k*((RS.a i l : ℝ)*(s.x l).toNat) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ l, β i (RS.sat l)*((RS.a i l : ℝ)*(s.x l).toNat) := by simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private lemma lambda_bill {I : Instance} {RS : RouteSystem I} (s : SolF RS)
    (hs : IsFeasibleF RS s) (lam : Fin I.nc → ℝ) :
    (∑ l, (∑ i, (RS.a i l : ℝ)*lam i)*((s.x l).toNat : ℝ)) = ∑ i, lam i := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = lam i * ∑ l, ((RS.a i l : ℝ)*(s.x l).toNat) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = _ := by
      have hc : ∑ l, ((RS.a i l : ℝ)*(s.x l).toNat) = 1 := by exact_mod_cast cover_sum s hs i
      simp [hc]

private lemma mu_bill {I : Instance} {RS : RouteSystem I} (s : SolF RS)
    (μ : Fin I.ns → ℝ) : ∑ l, μ (RS.sat l)*((s.x l).toNat : ℝ) =
      ∑ k, μ k*(∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), (s.x l).toNat : ℕ) := by
  simp only [Nat.cast_sum, Finset.mul_sum, Finset.sum_filter, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

private lemma reduced_nonneg {I : Instance} {RS : RouteSystem I}
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hβ : SatisfiesPenalty RS β lam μ μ0) (l : RS.SR) : 0 ≤ reducedCost RS β lam μ μ0 l := by
  have h := hβ l
  dsimp [reducedCost]
  simp only [mul_add, Finset.sum_add_distrib]
  linarith

private lemma gap_bound {I : Instance} {RS : RouteSystem I} (s : SolF RS)
    (hs : IsFeasibleF RS s) (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ)
    (μ : Fin I.ns → ℝ) (μ0 : ℝ) (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) :
    objRF RS β lam μ μ0 (convertF s) +
      ∑ l, reducedCost RS β lam μ μ0 l*((s.x l).toNat : ℝ) ≤ costF RS s := by
  have hm : ∑ k, (I.m k : ℝ)*μ k ≤
      ∑ k, μ k*(∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), (s.x l).toNat : ℕ) := by
    apply Finset.sum_le_sum
    intro k hk
    have hc : (∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), (s.x l).toNat : ℕ) ≤ I.m k := hs.2.1 k
    have hcr : ((∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), (s.x l).toNat : ℕ):ℝ) ≤ I.m k := by exact_mod_cast hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hcr) (hμ k)]
  have hm0 : (I.m2 : ℝ)*μ0 ≤ (∑ l, ((s.x l).toNat : ℝ))*μ0 := by
    have hc : (∑ l, ((s.x l).toNat : ℝ)) ≤ I.m2 := by exact_mod_cast hs.2.2.1
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc) hμ0]
  have hid : objRF RS β lam μ μ0 (convertF s) +
      ∑ l, reducedCost RS β lam μ μ0 l*((s.x l).toNat : ℝ) =
      costF RS s + (∑ k, (I.m k : ℝ)*μ k - ∑ l, μ (RS.sat l)*((s.x l).toNat : ℝ)) +
      ((I.m2 : ℝ)*μ0 - (∑ l, ((s.x l).toNat : ℝ))*μ0) := by
    unfold objRF
    rw [assignment_bill s hs]
    simp only [reducedCost, mul_add, Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib,
      Finset.sum_mul, convertF, costF, penaltyConst, add_mul]
    have hl := lambda_bill s hs lam
    simp only [Finset.sum_mul] at hl
    simp only [mul_comm μ0] at *
    linarith
  rw [hid, mu_bill s μ]
  linarith



private lemma f_obj_bound {I : Instance} {RS : RouteSystem I} (s : SolF RS)
    (hs : IsFeasibleF RS s) (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ)
    (μ : Fin I.ns → ℝ) (μ0 : ℝ) (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0)
    (hβ : SatisfiesPenalty RS β lam μ μ0) : objRF RS β lam μ μ0 (convertF s) ≤ costF RS s := by
  have hg := gap_bound s hs β lam μ μ0 hμ hμ0
  have hn : 0 ≤ ∑ l, reducedCost RS β lam μ μ0 l*((s.x l).toNat : ℝ) :=
    Finset.sum_nonneg (fun l hl => mul_nonneg (reduced_nonneg β lam μ μ0 hβ l) (Nat.cast_nonneg _))
  linarith

private lemma f_selected_bound {I : Instance} {RS : RouteSystem I} (s : SolF RS)
    (hs : IsFeasibleF RS s) (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ)
    (μ : Fin I.ns → ℝ) (μ0 : ℝ) (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0)
    (hβ : SatisfiesPenalty RS β lam μ μ0) (l : RS.SR) (hl : s.x l = true) :
    reducedCost RS β lam μ μ0 l + objRF RS β lam μ μ0 (convertF s) ≤ costF RS s := by
  have hg := gap_bound s hs β lam μ μ0 hμ hμ0
  have hn := Finset.single_le_sum
    (f := fun t => reducedCost RS β lam μ μ0 t*((s.x t).toNat : ℝ))
    (fun t ht => mul_nonneg (reduced_nonneg β lam μ μ0 hβ t) (Nat.cast_nonneg _)) (Finset.mem_univ l)
  simp only [hl, Bool.toNat_true, Nat.cast_one, mul_one] at hn
  linarith

private lemma sum_subset_univ {α M : Type*} [Fintype α] [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → M) (hz : ∀ a, a ∉ s → f a = 0) :
    ∑ a ∈ s, f a = ∑ a, f a := by
  apply Finset.sum_subset (Finset.subset_univ s)
  intro a ha hn
  exact hz a hn

private lemma flow_sum {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (k : Fin I.ns) : ∑ r, σ.qd r k = σ.load k := by
  rw [← hσ.2.1 k]
  symm
  apply sum_subset_univ
  intro r hr
  exact hσ.2.2.2.2.2 r k (by simpa using hr)

private lemma row_sum {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (r : RS.FR) :
    ∑ k, σ.qd r k = ∑ k ∈ RS.Rsat r, σ.qd r k := by
  symm
  exact sum_subset_univ _ _ (hσ.2.2.2.2.2 r)

private lemma load_sum {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) : ∑ k, σ.load k = I.qtot := by
  simp only [SolRF.load]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hσ.1, mul_one, Instance.qtot]

private lemma total_flow {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) : ∑ r, ∑ k, σ.qd r k = I.qtot := by
  rw [Finset.sum_comm]
  simp only [flow_sum σ hσ]
  exact load_sum σ hσ

private lemma qd_le_load {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (r : RS.FR) (k : Fin I.ns) : σ.qd r k ≤ σ.load k := by
  rw [← flow_sum σ hσ]
  exact Finset.single_le_sum (f := fun t => σ.qd t k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)

private lemma load_zero_assign {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (k : Fin I.ns) (hk : σ.load k = 0) (i : Fin I.nc) : σ.ξ i k = false := by
  have h : I.q i * (σ.ξ i k).toNat ≤ σ.load k :=
    Finset.single_le_sum (f := fun j => I.q j * (σ.ξ j k).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hpos := I.q_pos i
  cases hξ : σ.ξ i k <;> simp_all <;> omega

private def amount {I : Instance} {RS : RouteSystem I} (σ : SolRF RS) (r : RS.FR) : ℕ := ∑ k, σ.qd r k

private noncomputable def frac {I : Instance} {RS : RouteSystem I} (σ : SolRF RS) (r : RS.FR) (k : Fin I.ns) : ℝ :=
  (σ.qd r k : ℝ) / (σ.load k : ℝ)

private noncomputable def kz {I : Instance} {RS : RouteSystem I} (σ : SolRF RS) (r : RS.FR) (i : Fin I.nc) : ℝ :=
  ∑ k, ((σ.ξ i k).toNat : ℝ) * frac σ r k

private lemma frac_bounds {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (r : RS.FR) (k : Fin I.ns) : 0 ≤ frac σ r k ∧ frac σ r k ≤ 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact div_le_one_of_le₀ (by exact_mod_cast qd_le_load σ hσ r k) (Nat.cast_nonneg _)

private lemma frac_total {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (k : Fin I.ns) (hk : σ.load k ≠ 0) : ∑ r, frac σ r k = 1 := by
  simp only [frac, ← Finset.sum_div, ← Nat.cast_sum, flow_sum σ hσ]
  exact div_self (by exact_mod_cast hk)

private lemma kp_feasible {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (r : RS.FR) : kz σ r ∈ KPFeasible I (amount σ r) := by
  constructor
  · intro i
    constructor
    · exact Finset.sum_nonneg (fun k hk => mul_nonneg (Nat.cast_nonneg _) (frac_bounds σ hσ r k).1)
    · calc
        _ ≤ ∑ k, ((σ.ξ i k).toNat : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_of_le_one_right (Nat.cast_nonneg _) (frac_bounds σ hσ r k).2
        _ = 1 := by exact_mod_cast hσ.1 i
  · simp only [kz, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ k, (σ.load k : ℝ) * frac σ r k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [SolRF.load, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ k, (σ.qd r k : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases he : σ.load k = 0
        · have hq : σ.qd r k = 0 := Nat.eq_zero_of_le_zero (he ▸ qd_le_load σ hσ r k)
          simp [frac, he, hq]
        · dsimp [frac]
          field_simp
      _ = _ := by simp [amount]

private lemma amount_cap {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (r : RS.FR) : amount σ r ≤ I.Q1 * (σ.y r).toNat := by
  rw [amount, row_sum σ hσ]
  exact hσ.2.2.2.2.1 r

private lemma amount_mem {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (hload : ∀ k, σ.load k ≤ I.m k*I.Q2)
    (r : RS.FR) (hy : σ.y r = true) : amount σ r ∈ Wset RS r := by
  have htotal : ∑ r, amount σ r = I.qtot := total_flow σ hσ
  have hcap := amount_cap σ hσ r
  simp only [hy, Bool.toNat_true, mul_one] at hcap
  have htot : amount σ r ≤ I.qtot := by
    rw [← htotal]
    exact Finset.single_le_sum (f := amount σ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  have hfleet : amount σ r ≤ ∑ k ∈ RS.Rsat r, I.m k*I.Q2 := by
    rw [amount, row_sum σ hσ]
    exact Finset.sum_le_sum (fun k hk => (qd_le_load σ hσ r k).trans (hload k))
  have heq := Finset.sum_erase_add Finset.univ (amount σ) (Finset.mem_univ r)
  have heqy := Finset.sum_erase_add Finset.univ (fun r => (σ.y r).toNat) (Finset.mem_univ r)
  have hc := Finset.sum_le_sum (s := Finset.univ.erase r) (fun t ht => amount_cap σ hσ t)
  rw [← Finset.mul_sum] at hc
  have hcZ : (I.qtot : ℤ) ≤ (amount σ r : ℤ) + (I.Q1 : ℤ)*((I.m1 : ℤ)-1) := by
    have hycount : (∑ t ∈ Finset.univ.erase r, (σ.y t).toNat)+1 ≤ I.m1 := by
      simpa [hy, ← heqy] using hσ.2.2.2.1
    have hc' : (∑ t ∈ Finset.univ.erase r, amount σ t : ℤ) ≤
        (I.Q1 : ℤ)*(∑ t ∈ Finset.univ.erase r, (σ.y t).toNat : ℕ) := by exact_mod_cast hc
    have heq' : (∑ t ∈ Finset.univ.erase r, amount σ t : ℤ)+(amount σ r : ℤ) = I.qtot := by
      exact_mod_cast heq.trans htotal
    have hy' : (∑ t ∈ Finset.univ.erase r, (σ.y t).toNat : ℤ)+1 ≤ I.m1 := by exact_mod_cast hycount
    nlinarith [mul_nonneg (show (0:ℤ)≤I.Q1 by positivity)
      (show (0:ℤ)≤(I.m1:ℤ)-1-(∑ t ∈ Finset.univ.erase r, (σ.y t).toNat : ℤ) by omega)]
  refine Finset.mem_Icc.mpr ⟨?_, le_min (le_min hcap htot) hfleet⟩
  unfold wmin
  apply Int.toNat_le.mpr
  apply max_le
  · nlinarith
  · positivity



private lemma kp_cost_le {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (β : Fin I.nc → Fin I.ns → ℝ) :
    (∑ r, ∑ i, minBeta RS β r i * kz σ r i) ≤ ∑ k, ∑ i, β i k*((σ.ξ i k).toNat : ℝ) := by
  calc
    _ = ∑ r, ∑ i, ∑ k, minBeta RS β r i*((σ.ξ i k).toNat : ℝ)*frac σ r k := by
      simp only [kz, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ r, ∑ i, ∑ k, β i k*((σ.ξ i k).toNat : ℝ)*frac σ r k := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro k hk
      by_cases hkr : k ∈ RS.Rsat r
      · apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right (Finset.inf'_le _ hkr) (Nat.cast_nonneg _)
        · exact (frac_bounds σ hσ r k).1
      · simp [frac, hσ.2.2.2.2.2 r k hkr]
    _ = ∑ i, ∑ k, ∑ r, β i k*((σ.ξ i k).toNat : ℝ)*frac σ r k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ k, β i k*((σ.ξ i k).toNat : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.mul_sum]
      by_cases he : σ.load k = 0
      · simp [load_zero_assign σ k he i]
      · simp [frac_total σ hσ k he]
    _ = _ := Finset.sum_comm

private lemma decide_nat (p : Prop) [Decidable p] : (decide p).toNat = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

private def chosen {I : Instance} {RS : RouteSystem I} (σ : SolRF RS) (r : RS.FR) (w : ℕ) : Bool :=
  if σ.y r then decide (w = amount σ r) else false

private lemma amount_zero {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (r : RS.FR) (hy : σ.y r = false) : amount σ r = 0 := by
  have h := amount_cap σ hσ r
  simpa [hy] using h

private lemma kz_zero {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (r : RS.FR) (hy : σ.y r = false) (i : Fin I.nc) : kz σ r i = 0 := by
  have hz := amount_zero σ hσ r hy
  have hq (k : Fin I.ns) : σ.qd r k = 0 := by
    have hk : σ.qd r k ≤ amount σ r :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    omega
  simp [kz, frac, hq]

private lemma chosen_feasible {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (hload : ∀ k, σ.load k ≤ I.m k*I.Q2) :
    IsFeasibleRFbar RS (chosen σ) := by
  constructor
  · have he (r : RS.FR) : ∑ w ∈ Wset RS r, w*(chosen σ r w).toNat = amount σ r := by
      cases hy : σ.y r
      · simp [chosen, hy, amount_zero σ hσ r hy]
      · simp [chosen, hy, decide_nat, mul_ite, amount_mem σ hσ hload r hy]
    simp only [he]
    exact total_flow σ hσ
  · intro r
    cases hy : σ.y r
    · simp [chosen, hy]
    · simp [chosen, hy, decide_nat, mul_ite, amount_mem σ hσ hload r hy]

private lemma ereal_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    ∑ a ∈ s, (f a : EReal) = ((∑ a ∈ s, f a : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, EReal.coe_add]

private lemma rfbar_bound {I : Instance} {RS : RouteSystem I} (σ : SolRF RS)
    (hσ : IsFeasibleRF RS σ) (hload : ∀ k, σ.load k ≤ I.m k*I.Q2)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ) :
    zRFbar RS β lam μ μ0 ≤ ((objRF RS β lam μ μ0 σ : ℝ) : EReal) := by
  have hp (r : RS.FR) : phi RS β r (amount σ r) ≤
      ((∑ i, minBeta RS β r i*kz σ r i : ℝ) : EReal) :=
    iInf_le_of_le (kz σ r) (iInf_le_of_le (kp_feasible σ hσ r) le_rfl)
  have hr (r : RS.FR) :
      (∑ w ∈ Wset RS r, if chosen σ r w then (RS.g r : EReal)+phi RS β r w else 0) ≤
      ((RS.g r*((σ.y r).toNat : ℝ) + ∑ i, minBeta RS β r i*kz σ r i : ℝ) : EReal) := by
    cases hy : σ.y r
    · simp [chosen, hy, kz_zero σ hσ r hy]
    · simpa [chosen, hy, amount_mem σ hσ hload r hy, EReal.coe_add] using
        add_le_add_right (hp r) (RS.g r : EReal)
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hr r)
  rw [ereal_sum] at hs
  have hreal : (∑ r, (RS.g r*((σ.y r).toNat : ℝ) + ∑ i, minBeta RS β r i*kz σ r i)) +
      penaltyConst I lam μ μ0 ≤ objRF RS β lam μ μ0 σ := by
    dsimp [objRF]
    rw [Finset.sum_add_distrib]
    linarith [kp_cost_le σ hσ β]
  calc
    _ ≤ objRFbar RS β lam μ μ0 (chosen σ) :=
      iInf_le_of_le (chosen σ) (iInf_le_of_le (chosen_feasible σ hσ hload) le_rfl)
    _ ≤ ((objRF RS β lam μ μ0 σ : ℝ) : EReal) := by
      unfold objRFbar
      exact (add_le_add_left hs _).trans (by simpa only [← EReal.coe_add, EReal.coe_le_coe_iff] using hreal)



/-- §3.2, the sentence after theorem solution (p. 302): if `β` solves (12) and `μ ≤ 0`, `μ_0 ≤ 0`, a
feasible solution of F of cost smaller than `zUB` uses no second-level route `l` with
`c̃_l ≥ zUB − z(RF-bar(β, λ, μ))`; stated as `c̃_l + z(RF-bar) < zUB` for every used route. -/
theorem solution (I : Instance) (RS : RouteSystem I)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (zUB : ℝ) (s : SolF RS) (hs : IsFeasibleF RS s) (hcost : costF RS s < zUB)
    (l : RS.SR) (hl : s.x l = true) :
    ((reducedCost RS β lam μ μ0 l : ℝ) : EReal) + zRFbar RS β lam μ μ0
      < ((zUB : ℝ) : EReal) := by 
  have hz := rfbar_bound (convertF s) (convert_feasible s hs) (convert_fleet s hs) β lam μ μ0
  have hb := f_selected_bound s hs β lam μ μ0 hμ hμ0 hβ l hl
  calc
    _ ≤ (reducedCost RS β lam μ μ0 l : EReal) +
        ((objRF RS β lam μ μ0 (convertF s) : ℝ) : EReal) := add_le_add le_rfl hz
    _ ≤ ((costF RS s : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      exact_mod_cast hb
    _ < _ := by exact_mod_cast hcost

