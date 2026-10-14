-- Prove2me | solution 1 for TwoEchelonCVRP.LowerBound.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:53:45.081091+00:00
-- url     : https://prove2.me/submissions/905d0894-ca4a-4e30-989a-3db56a27895c

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

/-- Corollary 1 (p. 301): if `β` solves (12) and `μ ≤ 0`, `μ_0 ≤ 0`, then a feasible solution of F
of cost smaller than `zUB` uses no second-level route `l` with `c̃_l ≥ zUB − z(RF(β, λ, μ))`;
stated without subtraction as `c̃_l + z(RF) < zUB` for every used route. -/
theorem solution (I : Instance) (RS : RouteSystem I)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (zUB : ℝ) (s : SolF RS) (hs : IsFeasibleF RS s) (hcost : costF RS s < zUB)
    (l : RS.SR) (hl : s.x l = true) :
    ((reducedCost RS β lam μ μ0 l : ℝ) : EReal) + zRF RS β lam μ μ0 < ((zUB : ℝ) : EReal) := by 
  have hz : zRF RS β lam μ μ0 ≤ ((objRF RS β lam μ μ0 (convertF s) : ℝ) : EReal) :=
    iInf_le_of_le (convertF s) (iInf_le_of_le (convert_feasible s hs) le_rfl)
  have hb := f_selected_bound s hs β lam μ μ0 hμ hμ0 hβ l hl
  calc
    _ ≤ (reducedCost RS β lam μ μ0 l : EReal) +
        ((objRF RS β lam μ μ0 (convertF s) : ℝ) : EReal) := add_le_add le_rfl hz
    _ ≤ ((costF RS s : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      exact_mod_cast hb
    _ < _ := by exact_mod_cast hcost

