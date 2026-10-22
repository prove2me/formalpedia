-- Prove2me | solution 1 for TwoEchelonCVRP.Config.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T15:22:45.560368+00:00
-- url     : https://prove2.me/submissions/3b885dec-799c-4599-a32b-597bb51d32f6

import Mathlib
import Definitions.Def_TwoEchelonCVRP_Config_Bounds

set_option autoImplicit false

namespace TwoEchelonCVRP.Config.P1Aux
open TwoEchelonCVRP.Config

variable {I : Instance} (RS : RouteSystem I)

lemma toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> simp

lemma w_pos (l : RS.SR) : 0 < RS.w l := by
  unfold RouteSystem.w RouteSystem.Rcust
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ (RS.tour2_ne l)
  exact Finset.sum_pos (fun j _ => I.q_pos j) ⟨i, List.mem_toFinset.mpr hi⟩

lemma a_eq (i : Fin I.nc) (l : RS.SR) : RS.a i l = if i ∈ RS.tour2 l then 1 else 0 := by
  unfold RouteSystem.a
  by_cases hi : i ∈ RS.tour2 l
  · rw [if_pos hi]; exact List.count_eq_one_of_mem (RS.tour2_nodup l) hi
  · rw [if_neg hi]; exact List.count_eq_zero.mpr hi

/-- every used second-level route starts at a satellite of `N_S(conf s)` -/
lemma sat_mem_NS (s : SolF RS) (hs : IsFeasibleF RS s) (l : RS.SR) (hl : s.x l = true) :
    RS.sat l ∈ NS RS (conf s) := by
  obtain ⟨-, -, -, -, -, h7, h8, -⟩ := hs
  have hpos : ∑ r ∈ Finset.univ.filter (fun r => RS.sat l ∈ RS.Rsat r), s.qd r (RS.sat l) ≠ 0 := by
    rw [h7 (RS.sat l)]
    have h1 : RS.w l * (s.x l).toNat ≤
        ∑ l' ∈ Finset.univ.filter (fun l' => RS.sat l' = RS.sat l), RS.w l' * (s.x l').toNat :=
      Finset.single_le_sum (f := fun l' => RS.w l' * (s.x l').toNat)
        (fun _ _ => Nat.zero_le _) (by simp)
    have h2 : 0 < RS.w l * (s.x l).toNat := by rw [hl]; simpa using w_pos RS l
    omega
  obtain ⟨r, hr, hqr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
  have hkr : RS.sat l ∈ RS.Rsat r := (Finset.mem_filter.mp hr).2
  have hyr : s.y r = true := by
    by_contra hy
    have hy' : s.y r = false := by simpa using hy
    have h8r := h8 r
    rw [hy', Bool.toNat_false, mul_zero] at h8r
    have : s.qd r (RS.sat l) ≤ ∑ k ∈ RS.Rsat r, s.qd r k :=
      Finset.single_le_sum (f := fun k => s.qd r k) (fun _ _ => Nat.zero_le _) hkr
    omega
  unfold NS
  exact Finset.mem_biUnion.mpr ⟨r, by simp [conf, hyr], hkr⟩

lemma x_false_of_not_mem (s : SolF RS) (hs : IsFeasibleF RS s) (l : RS.SR)
    (hl : RS.sat l ∉ NS RS (conf s)) : s.x l = false := by
  cases h : s.x l
  · rfl
  · exact absurd (sat_mem_NS RS s hs l h) hl

/-- customers counted with multiplicity one -/
lemma sum_xa (s : SolF RS) (hs : IsFeasibleF RS s) (i : Fin I.nc) :
    ∑ l, (s.x l).toNat * RS.a i l = 1 := by
  rw [← hs.1 i, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [a_eq]; split_ifs <;> simp

lemma sum_wx (s : SolF RS) (hs : IsFeasibleF RS s) :
    ∑ l, RS.w l * (s.x l).toNat = I.qtot := by
  calc ∑ l, RS.w l * (s.x l).toNat
      = ∑ l, ∑ i, I.q i * ((s.x l).toNat * RS.a i l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [RouteSystem.w, RouteSystem.Rcust, Finset.sum_mul]
        rw [← Finset.sum_subset (Finset.subset_univ (RS.tour2 l).toFinset)]
        · refine Finset.sum_congr rfl fun i hi => ?_
          rw [a_eq, if_pos (List.mem_toFinset.mp hi)]; ring
        · intro i _ hi
          rw [a_eq, if_neg (fun h => hi (List.mem_toFinset.mpr h))]; ring
    _ = ∑ i, ∑ l, I.q i * ((s.x l).toNat * RS.a i l) := Finset.sum_comm
    _ = ∑ i, I.q i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, sum_xa RS s hs i, mul_one]
    _ = I.qtot := rfl

/-- total delivery of route `r` -/
def D (s : SolF RS) (r : RS.FR) : ℕ := ∑ k ∈ RS.Rsat r, s.qd r k

lemma D_eq_univ (s : SolF RS) (hs : IsFeasibleF RS s) (r : RS.FR) :
    D RS s r = ∑ k, s.qd r k := by
  unfold D
  exact Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => hs.2.2.2.2.2.2.2 r k hk)

lemma sum_D (s : SolF RS) (hs : IsFeasibleF RS s) : ∑ r, D RS s r = I.qtot := by
  have h7 := hs.2.2.2.2.2.1
  have h9 := hs.2.2.2.2.2.2.2
  rw [← sum_wx RS s hs, ← Finset.sum_fiberwise Finset.univ RS.sat]
  simp_rw [D_eq_univ RS s hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← h7 k]
  symm
  refine Finset.sum_filter_of_ne fun r _ hr => ?_
  by_contra hk
  exact hr (h9 r k hk)

lemma D_le_Q1 (s : SolF RS) (hs : IsFeasibleF RS s) (r : RS.FR) :
    D RS s r ≤ I.Q1 * (s.y r).toNat := hs.2.2.2.2.2.2.1 r

lemma D_eq_zero (s : SolF RS) (hs : IsFeasibleF RS s) (r : RS.FR) (hr : s.y r = false) :
    D RS s r = 0 := by
  have := D_le_Q1 RS s hs r
  rw [hr] at this
  simpa using this

lemma qd_le (s : SolF RS) (hs : IsFeasibleF RS s) (r : RS.FR) (k : Fin I.ns) :
    s.qd r k ≤ I.m k * I.Q2 := by
  obtain ⟨-, h3, -, -, -, h7, -, h9⟩ := hs
  by_cases hk : k ∈ RS.Rsat r
  · calc s.qd r k ≤ ∑ r' ∈ Finset.univ.filter (fun r' => k ∈ RS.Rsat r'), s.qd r' k :=
          Finset.single_le_sum (f := fun r' => s.qd r' k) (fun _ _ => Nat.zero_le _) (by simp [hk])
      _ = ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), RS.w l * (s.x l).toNat := h7 k
      _ ≤ ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), I.Q2 * (s.x l).toNat :=
          Finset.sum_le_sum fun l _ => Nat.mul_le_mul_right _ (RS.cap2 l)
      _ = I.Q2 * ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), (s.x l).toNat := by
          rw [Finset.mul_sum]
      _ ≤ I.Q2 * I.m k := Nat.mul_le_mul_left _ (h3 k)
      _ = I.m k * I.Q2 := by ring
  · rw [h9 r k hk]; exact Nat.zero_le _

lemma sum_conf_D (s : SolF RS) (hs : IsFeasibleF RS s) :
    ∑ r ∈ conf s, D RS s r = I.qtot := by
  rw [← sum_D RS s hs]
  unfold conf
  refine Finset.sum_filter_of_ne fun r _ hr => ?_
  by_contra hy
  exact hr (D_eq_zero RS s hs r (by simpa using hy))

lemma card_conf (s : SolF RS) : (conf s).card = ∑ r, (s.y r).toNat := by
  unfold conf
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  cases s.y r <;> rfl

lemma sum_x_le (s : SolF RS) (hs : IsFeasibleF RS s) :
    ∑ l, (s.x l).toNat ≤ ∑ k ∈ NS RS (conf s), I.m k := by
  rw [← Finset.sum_fiberwise Finset.univ RS.sat]
  rw [← Finset.sum_subset (Finset.subset_univ (NS RS (conf s)))]
  · exact Finset.sum_le_sum fun k _ => hs.2.1 k
  · intro k _ hk
    refine Finset.sum_eq_zero fun l hl => ?_
    have hlk : RS.sat l = k := (Finset.mem_filter.mp hl).2
    rw [x_false_of_not_mem RS s hs l (hlk ▸ hk)]
    rfl

lemma sum_biUnion_le' {α β : Type} [DecidableEq β] (M : Finset α) (t : α → Finset β) (f : β → ℕ) :
    ∑ k ∈ M.biUnion t, f k ≤ ∑ r ∈ M, ∑ k ∈ t r, f k := by
  classical
  induction M using Finset.induction_on with
  | empty => simp
  | insert a M ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    calc ∑ k ∈ t a ∪ M.biUnion t, f k
        ≤ ∑ k ∈ t a ∪ M.biUnion t, f k + ∑ k ∈ t a ∩ M.biUnion t, f k := Nat.le_add_right _ _
      _ = ∑ k ∈ t a, f k + ∑ k ∈ M.biUnion t, f k := Finset.sum_union_inter
      _ ≤ ∑ k ∈ t a, f k + ∑ r ∈ M, ∑ k ∈ t r, f k := Nat.add_le_add_left ih _

lemma U_add (s : SolF RS) : costF RS s = secondLevelCost RS s + U RS (conf s) := by
  unfold costF secondLevelCost U conf
  rw [Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  cases s.y r <;> simp

/-- the Lagrangian lower bound on the second-level cost -/
lemma LBW_le (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (s : SolF RS) (hs : IsFeasibleF RS s) (hM : (NS RS (conf s)).Nonempty) :
    LBW RS β lam μ μ0 (conf s) hM ≤ secondLevelCost RS s := by
  have hxa : ∀ i, ∑ l, ((s.x l).toNat : ℝ) * (RS.a i l : ℝ) = 1 := by
    intro i
    have := sum_xa RS s hs i
    exact_mod_cast this
  have hx0 : ∀ l, (0 : ℝ) ≤ ((s.x l).toNat : ℝ) := fun l => Nat.cast_nonneg _
  -- step 1: termwise penalty bound
  have step1 : ∑ l, ((s.x l).toNat : ℝ) *
      (∑ i, (RS.a i l : ℝ) * β i (RS.sat l) + ∑ i, (RS.a i l : ℝ) * lam i + μ (RS.sat l) + μ0)
      ≤ secondLevelCost RS s := by
    unfold secondLevelCost
    refine Finset.sum_le_sum fun l _ => ?_
    have := hβ l
    rw [mul_comm (RS.c l)]
    exact mul_le_mul_of_nonneg_left (by linarith) (hx0 l)
  -- the four parts
  have pβ : ∑ i, (NS RS (conf s)).inf' hM (fun k => β i k) ≤
      ∑ l, ((s.x l).toNat : ℝ) * ∑ i, (RS.a i l : ℝ) * β i (RS.sat l) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i _ => ?_
    calc (NS RS (conf s)).inf' hM (fun k => β i k)
        = ∑ l, ((s.x l).toNat : ℝ) * (RS.a i l : ℝ) * (NS RS (conf s)).inf' hM (fun k => β i k) := by
          rw [← Finset.sum_mul, hxa i, one_mul]
      _ ≤ ∑ l, ((s.x l).toNat : ℝ) * ((RS.a i l : ℝ) * β i (RS.sat l)) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [← mul_assoc]
          cases h : s.x l
          · simp
          · have hmem := sat_mem_NS RS s hs l h
            exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ hmem)
              (mul_nonneg (by simp) (Nat.cast_nonneg _))
  have plam : ∑ l, ((s.x l).toNat : ℝ) * ∑ i, (RS.a i l : ℝ) * lam i = ∑ i, lam i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ∑ l, ((s.x l).toNat : ℝ) * ((RS.a i l : ℝ) * lam i)
        = (∑ l, ((s.x l).toNat : ℝ) * (RS.a i l : ℝ)) * lam i := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => by ring
      _ = lam i := by rw [hxa i, one_mul]
  have pμ : ∑ k ∈ NS RS (conf s), (I.m k : ℝ) * μ k ≤ ∑ l, ((s.x l).toNat : ℝ) * μ (RS.sat l) := by
    rw [← Finset.sum_fiberwise Finset.univ RS.sat]
    rw [← Finset.sum_subset (Finset.subset_univ (NS RS (conf s)))]
    · refine Finset.sum_le_sum fun k _ => ?_
      have hcount : (∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), ((s.x l).toNat : ℝ))
          ≤ (I.m k : ℝ) := by exact_mod_cast hs.2.1 k
      calc (I.m k : ℝ) * μ k
          ≤ (∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), ((s.x l).toNat : ℝ)) * μ k :=
            mul_le_mul_of_nonpos_right hcount (hμ k)
        _ = ∑ l ∈ Finset.univ.filter (fun l => RS.sat l = k), ((s.x l).toNat : ℝ) * μ (RS.sat l) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun l hl => ?_
            rw [(Finset.mem_filter.mp hl).2]
    · intro k _ hk
      refine Finset.sum_eq_zero fun l hl => ?_
      have hlk : RS.sat l = k := (Finset.mem_filter.mp hl).2
      rw [x_false_of_not_mem RS s hs l (hlk ▸ hk)]
      simp
  have pμ0 : (I.m2 : ℝ) * μ0 ≤ ∑ l, ((s.x l).toNat : ℝ) * μ0 := by
    rw [← Finset.sum_mul]
    have : (∑ l, ((s.x l).toNat : ℝ)) ≤ (I.m2 : ℝ) := by exact_mod_cast hs.2.2.1
    exact mul_le_mul_of_nonpos_right this hμ0
  have hsplit : ∑ l, ((s.x l).toNat : ℝ) *
      (∑ i, (RS.a i l : ℝ) * β i (RS.sat l) + ∑ i, (RS.a i l : ℝ) * lam i + μ (RS.sat l) + μ0)
      = ∑ l, ((s.x l).toNat : ℝ) * ∑ i, (RS.a i l : ℝ) * β i (RS.sat l)
        + ∑ l, ((s.x l).toNat : ℝ) * ∑ i, (RS.a i l : ℝ) * lam i
        + ∑ l, ((s.x l).toNat : ℝ) * μ (RS.sat l) + ∑ l, ((s.x l).toNat : ℝ) * μ0 := by
    simp only [mul_add, Finset.sum_add_distrib]
  unfold LBW
  linarith

lemma LBR_le_LBW (hns : 0 < I.ns) (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ)
    (μ : Fin I.ns → ℝ) (μ0 : ℝ) (hμ : ∀ k, μ k ≤ 0) (M : Finset RS.FR) (hM : (NS RS M).Nonempty) :
    LBR hns β lam μ μ0 ≤ LBW RS β lam μ μ0 M hM := by
  unfold LBR LBW
  have h1 : ∑ i, (Finset.univ : Finset (Fin I.ns)).inf'
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hns⟩⟩) (fun k => β i k)
      ≤ ∑ i, (NS RS M).inf' hM (fun k => β i k) := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.le_inf' _ _ fun k _ => Finset.inf'_le _ (Finset.mem_univ k)
  have h2 : ∑ k, (I.m k : ℝ) * μ k ≤ ∑ k ∈ NS RS M, (I.m k : ℝ) * μ k := by
    rw [← Finset.sum_sdiff (Finset.subset_univ (NS RS M))]
    have : ∑ k ∈ Finset.univ \ NS RS M, (I.m k : ℝ) * μ k ≤ 0 :=
      Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hμ k)
    linarith
  linarith

end TwoEchelonCVRP.Config.P1Aux

open TwoEchelonCVRP.Config in
theorem solution (I : Instance) (RS : RouteSystem I) (hns : 0 < I.ns) (hnc : 0 < I.nc)
    (β : Fin I.nc → Fin I.ns → ℝ) (lam : Fin I.nc → ℝ) (μ : Fin I.ns → ℝ) (μ0 : ℝ)
    (hμ : ∀ k, μ k ≤ 0) (hμ0 : μ0 ≤ 0) (hβ : SatisfiesPenalty RS β lam μ μ0)
    (zUB : ℝ) (s : SolF RS) (hs : IsFeasibleF RS s) (hcost : costF RS s < zUB) :
    InP RS (conf s) ∧
    -- (b)
    I.qtot ≤ ∑ r ∈ conf s, min I.Q1 (∑ k ∈ RS.Rsat r, I.m k * I.Q2) ∧
    -- (c)
    ⌈(I.qtot : ℚ) / (I.Q2 : ℚ)⌉₊ ≤ ∑ r ∈ conf s, ∑ k ∈ RS.Rsat r, I.m k ∧
    -- (d)
    U RS (conf s) < zUB - LBR hns β lam μ μ0 ∧
    -- (e)
    ∃ hM : (NS RS (conf s)).Nonempty,
      U RS (conf s) < zUB - LBW RS β lam μ μ0 (conf s) hM := by
  -- N_S(M) is nonempty: customer 0 is served
  have hM : (NS RS (conf s)).Nonempty := by
    have h := hs.1 ⟨0, hnc⟩
    have hne : ∑ l ∈ Finset.univ.filter (fun l => (⟨0, hnc⟩ : Fin I.nc) ∈ RS.tour2 l),
        (s.x l).toNat ≠ 0 := by omega
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hxl : s.x l = true := by
      cases h' : s.x l
      · rw [h'] at hl; exact absurd rfl hl
      · rfl
    exact ⟨_, P1Aux.sat_mem_NS RS s hs l hxl⟩
  have hLBW := P1Aux.LBW_le RS β lam μ μ0 hμ hμ0 hβ s hs hM
  have hLBR := P1Aux.LBR_le_LBW RS hns β lam μ μ0 hμ (conf s) hM
  have hU := P1Aux.U_add RS s
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, hM, ?_⟩
  · -- qtot ≤ |M| Q1
    rw [← P1Aux.sum_D RS s hs, P1Aux.card_conf]
    calc ∑ r, P1Aux.D RS s r ≤ ∑ r, I.Q1 * (s.y r).toNat :=
          Finset.sum_le_sum fun r _ => P1Aux.D_le_Q1 RS s hs r
      _ = (∑ r, (s.y r).toNat) * I.Q1 := by rw [← Finset.mul_sum, mul_comm]
  · rw [P1Aux.card_conf]; exact hs.2.2.2.2.1
  · rw [← P1Aux.sum_conf_D RS s hs]
    refine Finset.sum_le_sum fun r hr => ?_
    have hy : s.y r = true := by simpa [conf] using hr
    refine le_min ?_ ?_
    · have := P1Aux.D_le_Q1 RS s hs r
      rw [hy] at this
      simpa using this
    · exact Finset.sum_le_sum fun k _ => P1Aux.qd_le RS s hs r k
  · rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast I.Q2_pos)]
    have h1 : I.qtot ≤ I.Q2 * ∑ l, (s.x l).toNat := by
      rw [← P1Aux.sum_wx RS s hs, Finset.mul_sum]
      exact Finset.sum_le_sum fun l _ => Nat.mul_le_mul_right _ (RS.cap2 l)
    have h2 := P1Aux.sum_x_le RS s hs
    have h3 := P1Aux.sum_biUnion_le' (conf s) RS.Rsat I.m
    have h4 : I.qtot ≤ (∑ r ∈ conf s, ∑ k ∈ RS.Rsat r, I.m k) * I.Q2 := by
      unfold NS at h2
      calc I.qtot ≤ I.Q2 * ∑ l, (s.x l).toNat := h1
        _ ≤ I.Q2 * ∑ r ∈ conf s, ∑ k ∈ RS.Rsat r, I.m k :=
            Nat.mul_le_mul_left _ (h2.trans h3)
        _ = _ := mul_comm _ _
    exact_mod_cast h4
  · linarith
  · linarith

