-- Prove2me | solution 1 for RobustAuction.ROM.rom_feasible
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-22T05:14:15.612422+00:00
-- url     : https://prove2.me/submissions/bd4d8655-9f13-403a-bd4e-ed28e9dc40cf

import Mathlib
import Definitions.Def_RobustAuction_ROM_AuctionLP
import Definitions.Def_RobustAuction_ROM_Mechanism

open RobustAuction.ROM
open Finset
open Classical

set_option autoImplicit false

/-- ROM's allocation/payments are feasible for the robust auction LP (5)
    minus the revenue constraints: (7), x ≥ 0, (8), (9), (10).
    Propositions 3-5 of Bandi-Bertsimas 2014, combined. -/
theorem solution {n m : ℕ} (U : Set (Fin n → Fin m → ℝ)) (B : Fin n → ℝ)
    (hU : ∀ u ∈ U, ∀ i j, 0 ≤ u i j) (hB : ∀ i, 0 ≤ B i)
    (d : ROMData n m) (hd : IsROM U B d) :
    IsFeasibleMechanism U B (alloc U d) (pay U d) := by
  obtain ⟨hROMa, hROMb⟩ := hd
  obtain ⟨hzU, hInner, hOpt12, hUt, hDualFeas, hOpt13⟩ := hROMa
  have hxs_nn : ∀ i j, 0 ≤ d.xs i j := hInner.1
  have hth_nn : ∀ i, 0 ≤ d.θ i := hDualFeas.2.2.1
  have hutU : ∀ i, d.ut i ∈ U := fun i => (hUt i).1
  have hut_nn : ∀ i j, 0 ≤ d.ut i i j := fun i j => hU (d.ut i) (hutU i) i j
  -- extra (12)/(13)/(14) components for the duality-gap squeeze and the lift
  obtain ⟨_, hx1, hxB, hxR⟩ := hInner
  have hUtmin : ∀ i, ∀ u ∈ U, ∑ j, d.xs i j * d.ut i i j ≤ ∑ j, d.xs i j * u i j :=
    fun i u hu => (hUt i).2 u hu
  obtain ⟨hξ, hη, _, hdf⟩ := hDualFeas
  -- PSet / QSet membership and optimality accessors
  have hYmem : ∀ v ∈ U, d.y v ∈ PSet U B d := fun v hv => (hROMb v hv).1.1
  have hYopt : ∀ v ∈ U, ∀ y ∈ PSet U B d, welfare d v y ≤ welfare d v (d.y v) :=
    fun v hv => (hROMb v hv).1.2
  have hZmem : ∀ v ∈ U, ∀ k : Fin n, d.yk k v ∈ QSet U B d k :=
    fun v hv k => ((hROMb v hv).2 k).1
  have hZopt : ∀ v ∈ U, ∀ k : Fin n, ∀ y ∈ QSet U B d k,
      welfareExcept d k v y ≤ welfareExcept d k v (d.yk k v) :=
    fun v hv k => ((hROMb v hv).2 k).2
  -- (†): both minimizers of u ↦ ∑ x* u over U attain the same value
  have hceq : ∀ i, ∑ j, d.xs i j * d.ut i i j = ∑ j, d.xs i j * d.z i j := by
    intro i
    apply le_antisymm (hUtmin i _ hzU)
    exact hxR (d.ut i) (hutU i) i
  have hc0 : ∀ i, 0 ≤ ∑ j, d.xs i j * d.ut i i j := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hxs_nn i j) (hU _ (hutU i) i j)
  -- dual objective ≤ ∑_i c_i, via the feasible test point (ξ,η,θ) = (0,0,1)
  have hdual : dualObj B d.xs d.ut d.ξ d.η d.θ
      ≤ ∑ i, ∑ j, d.xs i j * d.ut i i j := by
    have hfeas : DualFeasible d.z (fun _ => 0) (fun _ => 0) (fun _ => 1) :=
      ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ => zero_le_one, fun i j => by simp⟩
    have h := hOpt13 _ _ _ hfeas
    have e : dualObj B d.xs d.ut (fun _ => 0) (fun _ => 0) (fun _ => 1)
        = ∑ i, ∑ j, d.xs i j * d.ut i i j := by
      simp [dualObj]
    rwa [e] at h
  -- termwise slack is nonnegative: x* ≥ 0 and r* ≥ z by dual feasibility
  have hT : ∀ i j, 0 ≤ d.xs i j * (rStar d i j - d.z i j) := by
    intro i j
    apply mul_nonneg (hxs_nn i j)
    have h := hdf i j
    simp only [rStar]
    nlinarith
  -- ∑_i ∑_j x*_ij * r*_ij ≤ dual objective (supply + budget + c)
  have hle : ∑ i, ∑ j, d.xs i j * rStar d i j
      ≤ dualObj B d.xs d.ut d.ξ d.η d.θ := by
    have e : ∑ i, ∑ j, d.xs i j * rStar d i j =
        ∑ j, d.ξ j * ∑ i, d.xs i j + ∑ i, (d.η i * ∑ j, d.xs i j * d.z i j +
          d.θ i * ∑ j, d.xs i j * d.z i j) := by
      have e1 : ∀ i, ∑ j, d.xs i j * rStar d i j = ∑ j, d.xs i j * d.ξ j +
          (d.η i * ∑ j, d.xs i j * d.z i j + d.θ i * ∑ j, d.xs i j * d.z i j) := by
        intro i
        simp only [rStar, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      have e2 : ∑ i, ∑ j, d.xs i j * d.ξ j = ∑ j, d.ξ j * ∑ i, d.xs i j := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib, e2]
    rw [e, dualObj]
    apply add_le_add
    · apply Finset.sum_le_sum; intro j _
      calc d.ξ j * ∑ i, d.xs i j ≤ d.ξ j * 1 := mul_le_mul_of_nonneg_left (hx1 j) (hξ j)
        _ = d.ξ j := mul_one _
    · apply Finset.sum_le_sum; intro i _
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hxB i) (hη i)
      · rw [← hceq i]
  -- duality-gap squeeze: the per-row collapse ∑ x* r* = ∑ x* z
  have hrow : ∀ i, ∑ j, d.xs i j * rStar d i j = ∑ j, d.xs i j * d.z i j := by
    have hsum : ∑ i, ∑ j, d.xs i j * (rStar d i j - d.z i j) ≤ 0 := by
      have e : ∑ i, ∑ j, d.xs i j * (rStar d i j - d.z i j) =
          ∑ i, ∑ j, d.xs i j * rStar d i j - ∑ i, ∑ j, d.xs i j * d.ut i i j := by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _
        rw [hceq i, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
      rw [e]; linarith
    have h0 : ∀ i, 0 ≤ ∑ j, d.xs i j * (rStar d i j - d.z i j) :=
      fun i => Finset.sum_nonneg fun j _ => hT i j
    have hTi : ∀ i, ∑ j, d.xs i j * (rStar d i j - d.z i j) = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h0 i)).1
        (le_antisymm hsum (Finset.sum_nonneg fun i _ => h0 i)) i (Finset.mem_univ i)
    intro i
    have e : ∑ j, d.xs i j * rStar d i j = ∑ j, d.xs i j * d.z i j := by
      have h := hTi i
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
      rw [← h]; apply Finset.sum_congr rfl; intro j _; ring
    exact e
  -- factor the θ-term out of the PSet budget slack
  have hfactor : ∀ i, ∑ j, d.xs i j * d.θ i * d.ut i i j
      = d.θ i * ∑ j, d.xs i j * d.ut i i j := by
    intro i; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  -- C_k ≥ 0 (the (10) half): (∑ x* v_k − c_k) + θ*_k * c_k
  have hCk : ∀ (v : Fin n → Fin m → ℝ), v ∈ U → ∀ k : Fin n,
      0 ≤ (∑ j, (v k j - rStar d k j) * d.xs k j)
        + d.θ k * (∑ j, d.xs k j * d.ut k k j) := by
    intro v hv k
    have hmin : ∑ j, d.xs k j * d.ut k k j ≤ ∑ j, d.xs k j * v k j := by
      have h := hxR v hv k
      rwa [← hceq k] at h
    have e1 : (∑ j, (v k j - rStar d k j) * d.xs k j)
        = (∑ j, d.xs k j * v k j) - ∑ j, d.xs k j * d.ut k k j := by
      have e : ∀ j, (v k j - rStar d k j) * d.xs k j
          = d.xs k j * v k j - d.xs k j * rStar d k j := fun j => by ring
      rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib, hrow k, ← hceq k]
    rw [e1]
    have hθc : 0 ≤ d.θ k * (∑ j, d.xs k j * d.ut k k j) :=
      mul_nonneg (hth_nn k) (hc0 k)
    linarith
  -- the lift: zeroing row k of the (17)-optimizer lands in PSet, so
  -- W(v, z^v) = welfare(v, φ) ≤ welfare(v, y^v) by (16)-optimality
  have hWlift : ∀ (v : Fin n → Fin m → ℝ), v ∈ U → ∀ k : Fin n,
      welfareExcept d k v (d.yk k v) ≤ welfare d v (d.y v) := by
    intro v hv k
    have hZmemk : d.yk k v ∈ QSet U B d k := ((hROMb v hv).2 k).1
    obtain ⟨hzynn, hzsup, hzB⟩ := hZmemk
    set φ : Fin n → Fin m → ℝ := fun i j => if i = k then 0 else d.yk k v i j
      with hφdef
    have hφk : ∀ j, φ k j = 0 := by
      intro j; rw [hφdef]; exact if_pos rfl
    have hφne : ∀ i, i ≠ k → ∀ j, φ i j = d.yk k v i j := by
      intro i hik j; rw [hφdef]; exact if_neg hik
    have hφnn : ∀ i j, 0 ≤ φ i j := by
      intro i j; by_cases hik : i = k
      · rw [hik, hφk j]
      · rw [hφne i hik j]; exact hzynn i j
    have hφsup : ∀ j, ∑ i, φ i j ≤ 1 - ∑ i, d.xs i j := by
      intro j
      have e : ∑ i, φ i j = ∑ i ∈ Finset.univ.erase k, d.yk k v i j := by
        have h1 : φ k j + ∑ i ∈ Finset.univ.erase k, φ i j = ∑ i, φ i j :=
          Finset.add_sum_erase _ (fun i => φ i j) (Finset.mem_univ k)
        rw [← h1, hφk j, zero_add]
        apply Finset.sum_congr rfl; intro i hi
        rw [Finset.mem_erase] at hi
        exact hφne i hi.1 j
      rw [e]; exact hzsup j
    have hφB : ∀ u ∈ U, ∀ i, ∑ j, φ i j * u i j
        ≤ B i - ∑ j, d.xs i j * rStar d i j
          + ∑ j, d.xs i j * d.θ i * d.ut i i j := by
      intro u hu i
      by_cases hik : i = k
      · -- row k: LHS = 0; RHS ≥ 0 by the collapse (★)
        have e1 : ∀ j, φ i j * u i j = 0 := by
          intro j; rw [hik, hφk j, zero_mul]
        have hLHS : ∑ j, φ i j * u i j = 0 :=
          Finset.sum_eq_zero fun j _ => e1 j
        rw [hLHS, hik]
        have hck : ∑ j, d.xs k j * d.ut k k j ≤ B k := by
          rw [hceq k]; exact hxB k
        have hθc : 0 ≤ d.θ k * ∑ j, d.xs k j * d.ut k k j :=
          mul_nonneg (hth_nn k) (hc0 k)
        have hrw : ∑ j, d.xs k j * rStar d k j
            = ∑ j, d.xs k j * d.ut k k j := by
          rw [hrow k, hceq k]
        rw [hrw, hfactor k]
        linarith
      · -- rows i ≠ k: QSet budget plus the nonnegative θ-slack
        have hLHS : ∑ j, φ i j * u i j = ∑ j, d.yk k v i j * u i j := by
          apply Finset.sum_congr rfl; intro j _
          rw [hφne i hik j]
        rw [hLHS]
        have hQ := hzB u hu i hik
        have hθc : 0 ≤ ∑ j, d.xs i j * d.θ i * d.ut i i j := by
          rw [hfactor i]; exact mul_nonneg (hth_nn i) (hc0 i)
        linarith
    have hφmem : φ ∈ PSet U B d := ⟨hφnn, hφsup, hφB⟩
    have hWφ : welfareExcept d k v (d.yk k v) = welfare d v φ := by
      unfold welfareExcept welfare
      have h1 : (∑ j, φ k j * (v k j - rStar d k j))
          + ∑ i ∈ Finset.univ.erase k, ∑ j, φ i j * (v i j - rStar d i j)
          = ∑ i, ∑ j, φ i j * (v i j - rStar d i j) :=
        Finset.add_sum_erase _ (fun i => ∑ j, φ i j * (v i j - rStar d i j))
          (Finset.mem_univ k)
      rw [← h1]
      have hk0 : ∑ j, φ k j * (v k j - rStar d k j) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [hφk j, zero_mul]
      rw [hk0, zero_add]
      apply Finset.sum_congr rfl; intro i hi
      rw [Finset.mem_erase] at hi
      apply Finset.sum_congr rfl; intro j _
      rw [hφne i hi.1 j]
    rw [hWφ]
    exact hYopt v hv φ hφmem
  -- welfare split at row k (shared by (9) and (10))
  have hsplit_gen : ∀ (w y : Fin n → Fin m → ℝ) (k : Fin n),
      welfare d w y = (∑ j, y k j * (w k j - rStar d k j))
        + welfareExcept d k w y := by
    intro w y k
    unfold welfare welfareExcept
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  -- unfold helpers for alloc / pay at v ∈ U
  have e_alloc : ∀ (v : Fin n → Fin m → ℝ), v ∈ U → ∀ i j,
      alloc U d v i j = d.y v i j + d.xs i j := by
    intro v hv i j; unfold alloc; rw [if_pos hv]
  have e_pay : ∀ (v : Fin n → Fin m → ℝ), v ∈ U → ∀ k,
      pay U d v k = (∑ j, d.y v k j * rStar d k j + ∑ j, d.xs k j * rStar d k j
        - ∑ j, d.xs k j * d.θ k * d.ut k k j
        + welfareExcept d k v (d.yk k v) - welfareExcept d k v (d.y v)) := by
    intro v hv k; unfold pay; rw [if_pos hv]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (7) SupplyFeasible
    intro v hv j
    obtain ⟨hynn, hysup, _⟩ := hYmem v hv
    calc ∑ i, alloc U d v i j
        = ∑ i, (d.y v i j + d.xs i j) :=
          Finset.sum_congr rfl (fun i _ => e_alloc v hv i j)
      _ = ∑ i, d.y v i j + ∑ i, d.xs i j := Finset.sum_add_distrib
      _ ≤ (1 - ∑ i, d.xs i j) + ∑ i, d.xs i j := by linarith [hysup j]
      _ = 1 := by ring
  · -- x ≥ 0
    intro v hv i j
    obtain ⟨hynn, _, _⟩ := hYmem v hv
    rw [e_alloc v hv i j]
    linarith [hynn i j, hxs_nn i j]
  · -- (8) IncentiveCompatible
    intro v hv k uk hw
    -- abbreviations
    set w : (Fin n → Fin m → ℝ) := Function.update v k uk with hwdef
    have hweq_ij : ∀ i : Fin n, i ≠ k → ∀ j, w i j = v i j := by
      intro i hik j
      have h : Function.update v k uk i = v i := Function.update_of_ne hik uk v
      rw [hwdef]
      exact congrFun h j
    -- the (17)-objective ignores row k, so it is the same function at w and v
    have hWeq : ∀ y, welfareExcept d k w y = welfareExcept d k v y := by
      intro y
      unfold welfareExcept
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_erase] at hi
      obtain ⟨hik, _⟩ := hi
      apply Finset.sum_congr rfl
      intro j _
      rw [hweq_ij i hik j]
    -- both (17)-optimizers attain the same optimal value
    have hWopt_eq : welfareExcept d k w (d.yk k w) = welfareExcept d k v (d.yk k v) := by
      have g1 : welfareExcept d k w (d.yk k v) ≤ welfareExcept d k w (d.yk k w) :=
        hZopt w hw k _ (hZmem v hv k)
      have g2 : welfareExcept d k v (d.yk k w) ≤ welfareExcept d k v (d.yk k v) :=
        hZopt v hv k _ (hZmem w hw k)
      have r1 : welfareExcept d k w (d.yk k v) = welfareExcept d k v (d.yk k v) := hWeq _
      have r2 : welfareExcept d k w (d.yk k w) = welfareExcept d k v (d.yk k w) := hWeq _
      linarith
    -- (16)-optimality at v
    have hYopt_le : welfare d v (d.y w) ≤ welfare d v (d.y v) :=
      hYopt v hv _ (hYmem w hw)
    -- split welfare at v into row k + the rest (for y' = d.y w)
    have hsplit_w : welfare d v (d.y w)
        = (∑ j, d.y w k j * (v k j - rStar d k j))
          + welfareExcept d k w (d.y w) := by
      have e1 : welfare d v (d.y w)
          = (∑ j, d.y w k j * (v k j - rStar d k j))
            + ∑ i ∈ Finset.univ.erase k, ∑ j, d.y w i j * (v i j - rStar d i j) := by
        unfold welfare
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      have e2 : (∑ i ∈ Finset.univ.erase k, ∑ j, d.y w i j * (v i j - rStar d i j))
          = welfareExcept d k w (d.y w) := by
        unfold welfareExcept
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_erase] at hi
        obtain ⟨hik, _⟩ := hi
        apply Finset.sum_congr rfl
        intro j _
        rw [hweq_ij i hik j]
      rw [e1, e2]
    -- split welfare at v into row k + the rest (for y = d.y v)
    have hsplit_v : welfare d v (d.y v)
        = (∑ j, d.y v k j * (v k j - rStar d k j))
          + welfareExcept d k v (d.y v) := by
      unfold welfare welfareExcept
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    -- expand the goal
    simp only [e_alloc w hw, e_alloc v hv, e_pay w hw k, e_pay v hv k,
      Finset.sum_add_distrib, mul_add]
    -- relate the row-k sums to the welfare splits
    have e3 : ∑ j, d.y w k j * (v k j - rStar d k j)
        = ∑ j, v k j * d.y w k j - ∑ j, d.y w k j * rStar d k j := by
      have h : ∀ j, d.y w k j * (v k j - rStar d k j)
          = v k j * d.y w k j - d.y w k j * rStar d k j := fun j => by ring
      rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib]
    have e4 : ∑ j, d.y v k j * (v k j - rStar d k j)
        = ∑ j, v k j * d.y v k j - ∑ j, d.y v k j * rStar d k j := by
      have h : ∀ j, d.y v k j * (v k j - rStar d k j)
          = v k j * d.y v k j - d.y v k j * rStar d k j := fun j => by ring
      rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib]
    rw [e3] at hsplit_w
    rw [e4] at hsplit_v
    -- now linarith with hsplit_w, hsplit_v, hWopt_eq, hYopt_le
    linarith
  · -- (9) BudgetFeasible
    intro v hv k
    rw [e_pay v hv k]
    obtain ⟨_, _, hyB⟩ := hYmem v hv
    have hbud : ∑ j, d.y v k j * v k j
        ≤ B k - ∑ j, d.xs k j * rStar d k j
          + ∑ j, d.xs k j * d.θ k * d.ut k k j := hyB v hv k
    have hsplit : welfare d v (d.y v)
        = (∑ j, d.y v k j * v k j - ∑ j, d.y v k j * rStar d k j)
          + welfareExcept d k v (d.y v) := by
      have hsg := hsplit_gen v (d.y v) k
      have e5 : ∑ j, d.y v k j * (v k j - rStar d k j)
          = ∑ j, d.y v k j * v k j - ∑ j, d.y v k j * rStar d k j := by
        have hj : ∀ j, d.y v k j * (v k j - rStar d k j)
            = d.y v k j * v k j - d.y v k j * rStar d k j := fun j => by ring
        rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_sub_distrib]
      rw [hsg, e5]
    have hlift : welfareExcept d k v (d.yk k v) ≤ welfare d v (d.y v) :=
      hWlift v hv k
    linarith
  · -- (10) IndividuallyRational
    intro v hv k
    rw [e_pay v hv k]
    have eA : ∀ j, v k j * alloc U d v k j
        = v k j * d.y v k j + v k j * d.xs k j := by
      intro j; rw [e_alloc v hv k j]; ring
    have eAsum : ∑ j, v k j * alloc U d v k j
        = ∑ j, v k j * d.y v k j + ∑ j, v k j * d.xs k j := by
      rw [Finset.sum_congr rfl (fun j _ => eA j), Finset.sum_add_distrib]
    rw [eAsum]
    have hsplit : welfare d v (d.y v)
        = (∑ j, d.y v k j * v k j - ∑ j, d.y v k j * rStar d k j)
          + welfareExcept d k v (d.y v) := by
      have hsg := hsplit_gen v (d.y v) k
      have e5 : ∑ j, d.y v k j * (v k j - rStar d k j)
          = ∑ j, d.y v k j * v k j - ∑ j, d.y v k j * rStar d k j := by
        have hj : ∀ j, d.y v k j * (v k j - rStar d k j)
            = d.y v k j * v k j - d.y v k j * rStar d k j := fun j => by ring
        rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_sub_distrib]
      rw [hsg, e5]
    have eS : ∑ j, v k j * d.y v k j = ∑ j, d.y v k j * v k j :=
      Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    have hlift : welfareExcept d k v (d.yk k v) ≤ welfare d v (d.y v) :=
      hWlift v hv k
    have hCk0 := hCk v hv k
    have eCx : (∑ j, (v k j - rStar d k j) * d.xs k j)
        = ∑ j, v k j * d.xs k j - ∑ j, d.xs k j * rStar d k j := by
      have e : ∀ j, (v k j - rStar d k j) * d.xs k j
          = v k j * d.xs k j - d.xs k j * rStar d k j := fun j => by ring
      rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib]
    have eT : ∑ j, d.xs k j * d.θ k * d.ut k k j
        = d.θ k * ∑ j, d.xs k j * d.ut k k j := hfactor k
    linarith

/-- Dual-named alias for the platform. -/
theorem RobustAuction.ROM.rom_feasible {n m : ℕ} (U : Set (Fin n → Fin m → ℝ))
    (B : Fin n → ℝ)
    (hU : ∀ u ∈ U, ∀ i j, 0 ≤ u i j) (hB : ∀ i, 0 ≤ B i)
    (d : ROMData n m) (hd : IsROM U B d) :
    IsFeasibleMechanism U B (alloc U d) (pay U d) :=
  solution U B hU hB d hd
