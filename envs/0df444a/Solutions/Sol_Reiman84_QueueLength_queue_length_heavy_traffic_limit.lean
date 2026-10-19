-- Prove2me | solution 1 for Reiman84.QueueLength.queue_length_heavy_traffic_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T13:56:40.753328+00:00
-- url     : https://prove2.me/submissions/a4ede6b3-65ef-4c24-a4e0-85c6bdb771bf

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic
import Theorems.Thm_Reiman84_QueueLength_proposition_5

set_option autoImplicit false

/-! Reduction of Reiman (1984) Theorem 1 (`queue_length_heavy_traffic_limit`) to Proposition 5.
Deterministic glue: a measurable, sup-norm Lipschitz, time-change-equivariant reflection map `Phi`
on `D[0,1]` (countable-sup Picard construction); the scaled queue is `Phi` of the scaled netput
(queue length nonnegative and right continuous a.s., by the strong law); the limit `Z` is `Phi` of `ξ`.
Theorem 1 then follows from Proposition 5 by transporting its coupling through `Phi`. -/

namespace A76

open Filter Topology MeasureTheory Matrix

variable {K : ℕ}

/-- time selector: rational `q ∈ [0, t]` or else `t` itself. -/
noncomputable def sel (t : ℝ) (q : ℚ) : ℝ := if 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ t then (q : ℝ) else t

lemma sel_mem {t : ℝ} (ht : 0 ≤ t) (q : ℚ) : sel t q ∈ Set.Icc 0 t := by
  unfold sel; split_ifs with h
  · exact h
  · exact ⟨ht, le_rfl⟩

lemma sel_mem01 {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (q : ℚ) : sel t q ∈ Set.Icc (0:ℝ) 1 :=
  ⟨(sel_mem ht.1 q).1, (sel_mem ht.1 q).2.trans ht.2⟩

lemma sel_neg (t : ℝ) : sel t (-1) = t := by
  unfold sel; rw [if_neg]; push_cast; intro h; linarith [h.1]

lemma sel_rat {t : ℝ} (q : ℚ) (h0 : 0 ≤ (q:ℝ)) (h1 : (q:ℝ) ≤ t) : sel t q = q := by
  unfold sel; rw [if_pos ⟨h0, h1⟩]

/-- `π_x(y)(t)_j = sup_{s ∈ S_t} ((y(s)P − x(s))_j)^+`. -/
noncomputable def piOp (P : Matrix (Fin K) (Fin K) ℝ) (x y : ℝ → Fin K → ℝ) :
    ℝ → Fin K → ℝ :=
  fun t j => ⨆ q : ℚ, max ((vecMul (y (sel t q)) P - x (sel t q)) j) 0

/-- Picard iterates. -/
noncomputable def iter (P : Matrix (Fin K) (Fin K) ℝ) (x : ℝ → Fin K → ℝ) :
    ℕ → ℝ → Fin K → ℝ
  | 0 => 0
  | m + 1 => piOp P x (iter P x m)

noncomputable def ylim (P : Matrix (Fin K) (Fin K) ℝ) (x : ℝ → Fin K → ℝ) : ℝ → Fin K → ℝ :=
  fun t j => limsup (fun m => iter P x m t j) atTop

/-- the reflection map. -/
noncomputable def Phi (P : Matrix (Fin K) (Fin K) ℝ) (x : ℝ → Fin K → ℝ) : ℝ → Fin K → ℝ :=
  Reiman84.QueueLength.onUnit (fun t => x t + vecMul (ylim P x t) (1 - P))

def Bd (y : ℝ → Fin K → ℝ) : Prop := ∃ M : ℝ, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ i, |y s i| ≤ M

def LB (x : ℝ → Fin K → ℝ) : Prop := ∃ M : ℝ, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ i, -M ≤ x s i

lemma vecMul_abs_le {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (a v : Fin K → ℝ) (h : ∀ i, |a i| ≤ v i) (j : Fin K) : |vecMul a P j| ≤ vecMul v P j := by
  simp only [vecMul, dotProduct]
  calc |∑ i, a i * P i j| ≤ ∑ i, |a i * P i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, v i * P i j := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (hP0 i j)]; exact mul_le_mul_of_nonneg_right (h i) (hP0 i j)

lemma vecMul_smul_const (P : Matrix (Fin K) (Fin K) ℝ) (c : ℝ) (v : Fin K → ℝ) (j : Fin K) :
    vecMul (fun i => c * v i) P j = c * vecMul v P j := by
  simp [vecMul, dotProduct, Finset.mul_sum, mul_assoc]

lemma piOp_bdd {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    {x y : ℝ → Fin K → ℝ} (hy : Bd y) (hx : LB x) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (j : Fin K) :
    BddAbove (Set.range fun q : ℚ => max ((vecMul (y (sel t q)) P - x (sel t q)) j) 0) := by
  obtain ⟨M, hM⟩ := hy
  obtain ⟨Mx, hMx⟩ := hx
  refine ⟨max (vecMul (fun _ => M) P j + Mx) 0, ?_⟩
  rintro _ ⟨q, rfl⟩
  have hs := sel_mem01 ht q
  refine max_le_max ?_ le_rfl
  have h1 := (abs_le.1 (vecMul_abs_le hP0 (y (sel t q)) (fun _ => M) (fun i => hM _ hs i) j)).2
  have h2 := hMx _ hs j
  simp only [Pi.sub_apply]
  linarith

lemma ciSup_le_ciSup_add {f g : ℚ → ℝ} (hg : BddAbove (Set.range g)) {c : ℝ}
    (h : ∀ q, f q ≤ g q + c) : (⨆ q, f q) ≤ (⨆ q, g q) + c :=
  ciSup_le fun q => (h q).trans (by linarith [le_ciSup hg q])

/-- Lipschitz estimate for one application of `π`. -/
lemma piOp_diff {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    {x x' y y' : ℝ → Fin K → ℝ} (hx : LB x) (hx' : LB x') (hy : Bd y) (hy' : Bd y')
    {c δ : ℝ} {v : Fin K → ℝ}
    (hc : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ i, |y s i - y' s i| ≤ c * v i)
    (hδ : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ i, |x s i - x' s i| ≤ δ) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ j,
      |piOp P x y t j - piOp P x' y' t j| ≤ c * vecMul v P j + δ := by
  intro t ht j
  have key : ∀ q : ℚ, |max ((vecMul (y (sel t q)) P - x (sel t q)) j) 0
      - max ((vecMul (y' (sel t q)) P - x' (sel t q)) j) 0| ≤ c * vecMul v P j + δ := by
    intro q
    have hs := sel_mem01 ht q
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have e : (vecMul (y (sel t q)) P - x (sel t q)) j - (vecMul (y' (sel t q)) P - x' (sel t q)) j
        = vecMul (y (sel t q) - y' (sel t q)) P j - (x (sel t q) j - x' (sel t q) j) := by
      rw [Matrix.sub_vecMul]; simp only [Pi.sub_apply]; ring
    rw [e]
    have h1 := vecMul_abs_le hP0 (y (sel t q) - y' (sel t q)) (fun i => c * v i)
      (fun i => by simpa using hc _ hs i) j
    rw [vecMul_smul_const] at h1
    have h2 := hδ _ hs j
    calc _ ≤ |vecMul (y (sel t q) - y' (sel t q)) P j| + |x (sel t q) j - x' (sel t q) j| :=
          abs_sub _ _
      _ ≤ _ := add_le_add h1 h2
  have hb := piOp_bdd hP0 hy hx ht j
  have hb' := piOp_bdd hP0 hy' hx' ht j
  rw [abs_sub_le_iff]
  constructor
  · have := ciSup_le_ciSup_add hb' (c := c * vecMul v P j + δ)
      (f := fun q => max ((vecMul (y (sel t q)) P - x (sel t q)) j) 0)
      (fun q => by have := (abs_sub_le_iff.1 (key q)).1; linarith)
    simp only [piOp]; linarith
  · have := ciSup_le_ciSup_add hb (c := c * vecMul v P j + δ)
      (f := fun q => max ((vecMul (y' (sel t q)) P - x' (sel t q)) j) 0)
      (fun q => by have := (abs_sub_le_iff.1 (key q)).2; linarith)
    simp only [piOp]; linarith

lemma pow_entry_nonneg {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (m : ℕ) :
    ∀ i j, 0 ≤ (P ^ m) i j := by
  induction m with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ m ih =>
    intro i j; rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (hP0 k j)

/-- Weight vector: `v ≥ 1`, `v P ≤ θ v` with `θ < 1` (from `Pᵐ → 0`, `P ≥ 0`). -/
lemma weight {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP : Tendsto (fun m : ℕ => P ^ m) atTop (𝓝 0)) :
    ∃ (v : Fin K → ℝ) (θ W : ℝ), (∀ i, 1 ≤ v i) ∧ (∀ i, v i ≤ W) ∧ 0 ≤ θ ∧ θ < 1 ∧
      ∀ j, vecMul v P j ≤ θ * v j := by
  set ε : ℝ := 1 / (2 * ((K : ℝ) + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have h1 : ∀ i j, Tendsto (fun m => (P ^ m) i j) atTop (𝓝 0) := by
    intro i j
    have := ((continuous_apply j).tendsto _).comp (((continuous_apply i).tendsto _).comp hP)
    exact this
  have hev : ∀ᶠ m in atTop, ∀ i j, (P ^ m) i j < ε :=
    eventually_all.2 fun i => eventually_all.2 fun j => (h1 i j).eventually (gt_mem_nhds hεpos)
  obtain ⟨N, hN, hN1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  set col : ℕ → Fin K → ℝ := fun m j => ∑ k, (P ^ m) k j with hcol
  have hcol0 : ∀ j, col 0 j = 1 := by
    intro j; simp [hcol, Matrix.one_apply]
  have hcolnn : ∀ m j, 0 ≤ col m j := fun m j =>
    Finset.sum_nonneg fun k _ => pow_entry_nonneg hP0 m k j
  have hcolN : ∀ j, col N j ≤ 1 / 2 := by
    intro j
    have : col N j ≤ ∑ _k : Fin K, ε := Finset.sum_le_sum fun k _ => (hN k j).le
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    refine this.trans ?_
    rw [hε]
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hcolsucc : ∀ m j, ∑ i, col m i * P i j = col (m + 1) j := by
    intro m j
    simp only [hcol, pow_succ, Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_comm
  set v : Fin K → ℝ := fun j => ∑ m ∈ Finset.range N, col m j with hv
  have hv1 : ∀ i, 1 ≤ v i := by
    intro i
    have := Finset.single_le_sum (f := fun m => col m i) (fun m _ => hcolnn m i)
      (Finset.mem_range.2 (by omega : 0 < N))
    rw [hcol0] at this; exact this
  have hvP : ∀ j, vecMul v P j ≤ v j - 1 / 2 := by
    intro j
    have e1 : vecMul v P j = ∑ m ∈ Finset.range N, col (m + 1) j := by
      simp only [vecMul, dotProduct, hv, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => hcolsucc m j
    have e2 : ∑ m ∈ Finset.range N, col (m + 1) j = v j - col 0 j + col N j := by
      have := Finset.sum_range_succ' (fun m => col m j) N
      have h' := Finset.sum_range_succ (fun m => col m j) N
      simp only [hv]; linarith
    rw [e1, e2, hcol0]; linarith [hcolN j]
  set W : ℝ := 1 + ∑ j, v j with hW
  have hvW : ∀ i, v i ≤ W := by
    intro i
    have := Finset.single_le_sum (f := v) (fun j _ => by linarith [hv1 j]) (Finset.mem_univ i)
    linarith
  have hW1 : 1 ≤ W := by
    have : 0 ≤ ∑ j, v j := Finset.sum_nonneg fun j _ => by linarith [hv1 j]
    linarith
  have hWpos : 0 < W := by linarith
  refine ⟨v, 1 - 1 / (2 * W), W, hv1, hvW, ?_, ?_, ?_⟩
  · rw [sub_nonneg, div_le_one (by positivity)]; linarith
  · exact sub_lt_self _ (by positivity)
  · intro j
    have h1 := hvP j
    have h2 : v j / (2 * W) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith [hvW j]
    calc vecMul v P j ≤ v j - 1 / 2 := h1
      _ ≤ v j - v j / (2 * W) := by linarith
      _ = (1 - 1 / (2 * W)) * v j := by ring

/-- packaged weight data. -/
structure Wt (P : Matrix (Fin K) (Fin K) ℝ) where
  v : Fin K → ℝ
  θ : ℝ
  W : ℝ
  hv1 : ∀ i, 1 ≤ v i
  hvW : ∀ i, v i ≤ W
  hW : 1 ≤ W
  hθ : 0 ≤ θ
  hθ1 : θ < 1
  hvP : ∀ j, vecMul v P j ≤ θ * v j

lemma wt_exists {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP : Tendsto (fun m : ℕ => P ^ m) atTop (𝓝 0)) : Nonempty (Wt P) := by
  obtain ⟨v, θ, W, hv1, hvW, hθ, hθ1, hvP⟩ := weight hP0 hP
  have hW : 1 ≤ max W 1 := le_max_right _ _
  exact ⟨⟨v, θ, max W 1, hv1, fun i => (hvW i).trans (le_max_left _ _), hW, hθ, hθ1, hvP⟩⟩

lemma clamp01_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : Reiman84.QueueLength.clamp01 t = t := by
  unfold Reiman84.QueueLength.clamp01; rw [max_eq_left ht.1, min_eq_left ht.2]

lemma onUnit_of_mem {f : ℝ → Fin K → ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Reiman84.QueueLength.onUnit f t = f t := by
  simp only [Reiman84.QueueLength.onUnit, clamp01_of_mem ht]

lemma piOp_nonneg (P : Matrix (Fin K) (Fin K) ℝ) (x y : ℝ → Fin K → ℝ) (t : ℝ) (j : Fin K) :
    0 ≤ piOp P x y t j := Real.iSup_nonneg fun _ => le_max_right _ _

lemma piOp_bd {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    {x y : ℝ → Fin K → ℝ} (hy : Bd y) (hx : LB x) : Bd (piOp P x y) := by
  obtain ⟨M, hM⟩ := hy
  obtain ⟨Mx, hMx⟩ := hx
  refine ⟨∑ j, max (vecMul (fun _ => M) P j + Mx) 0, fun t ht j => ?_⟩
  rw [abs_of_nonneg (piOp_nonneg P x y t j)]
  have hle : piOp P x y t j ≤ max (vecMul (fun _ => M) P j + Mx) 0 := by
    refine ciSup_le fun q => ?_
    have hs := sel_mem01 ht q
    refine max_le_max ?_ le_rfl
    have h1 := (abs_le.1 (vecMul_abs_le hP0 (y (sel t q)) (fun _ => M) (fun i => hM _ hs i) j)).2
    have h2 := hMx _ hs j
    simp only [Pi.sub_apply]
    linarith
  exact hle.trans (Finset.single_le_sum (f := fun j => max (vecMul (fun _ => M) P j + Mx) 0)
    (fun j _ => le_max_right _ _) (Finset.mem_univ j))

lemma iter_bd {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    {x : ℝ → Fin K → ℝ} (hx : LB x) : ∀ m, Bd (iter P x m)
  | 0 => ⟨0, fun s _ i => by simp [iter]⟩
  | m + 1 => piOp_bd hP0 (iter_bd hP0 hx m) hx

lemma iter_succ_sub {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    {x : ℝ → Fin K → ℝ} (hx : LB x) (w : Wt P) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ m, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ i,
      |iter P x (m + 1) s i - iter P x m s i| ≤ c0 * w.θ ^ m * w.v i := by
  obtain ⟨M1, hM1⟩ := iter_bd hP0 hx 1
  refine ⟨max M1 0, le_max_right _ _, fun m => ?_⟩
  induction m with
  | zero =>
    intro s hs i
    have h := hM1 s hs i
    have e : iter P x 0 s i = 0 := rfl
    rw [e, sub_zero, pow_zero, mul_one]
    exact (h.trans (le_max_left _ _)).trans (le_mul_of_one_le_right (le_max_right _ _) (w.hv1 i))
  | succ m ih =>
    intro s hs i
    have := piOp_diff hP0 hx hx (iter_bd hP0 hx (m+1)) (iter_bd hP0 hx m)
      (c := max M1 0 * w.θ ^ m) (δ := 0) (v := w.v) ih (fun s _ i => by simp) s hs i
    calc |iter P x (m + 1 + 1) s i - iter P x (m + 1) s i|
        = |piOp P x (iter P x (m + 1)) s i - piOp P x (iter P x m) s i| := rfl
      _ ≤ max M1 0 * w.θ ^ m * vecMul w.v P i + 0 := this
      _ ≤ max M1 0 * w.θ ^ m * (w.θ * w.v i) := by
          rw [add_zero]
          exact mul_le_mul_of_nonneg_left (w.hvP i)
            (mul_nonneg (le_max_right _ _) (pow_nonneg w.hθ m))
      _ = max M1 0 * w.θ ^ (m + 1) * w.v i := by ring

lemma picard {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    {x : ℝ → Fin K → ℝ} (hx : LB x) (w : Wt P) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ i,
      Tendsto (fun m => iter P x m s i) atTop (𝓝 (ylim P x s i)) ∧
      ∀ m, |iter P x m s i - ylim P x s i| ≤ c0 * w.v i * w.θ ^ m / (1 - w.θ) := by
  obtain ⟨c0, hc0, h⟩ := iter_succ_sub hP0 hx w
  refine ⟨c0, hc0, fun s hs i => ?_⟩
  have hu : ∀ m, dist (iter P x m s i) (iter P x (m+1) s i) ≤ (c0 * w.v i) * w.θ ^ m := by
    intro m
    rw [Real.dist_eq, abs_sub_comm]
    calc _ ≤ c0 * w.θ ^ m * w.v i := h m s hs i
      _ = c0 * w.v i * w.θ ^ m := by ring
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric w.θ (c0 * w.v i) w.hθ1 hu)
  have hl : ylim P x s i = a := ha.limsup_eq
  rw [hl]
  refine ⟨ha, fun m => ?_⟩
  have := dist_le_of_le_geometric_of_tendsto w.θ (c0 * w.v i) w.hθ1 hu ha m
  rwa [Real.dist_eq] at this

lemma ylim_bd {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    {x : ℝ → Fin K → ℝ} (hx : LB x) (w : Wt P) : Bd (ylim P x) := by
  obtain ⟨c0, hc0, h⟩ := picard hP0 hx w
  have h1 : 0 < 1 - w.θ := by linarith [w.hθ1]
  refine ⟨c0 * w.W / (1 - w.θ), fun s hs i => ?_⟩
  have := (h s hs i).2 0
  have e : iter P x 0 s i = 0 := rfl
  rw [e, zero_sub, abs_neg, pow_zero, mul_one] at this
  exact this.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (w.hvW i) hc0) h1.le)

lemma eq_zero_of_le_geom {d C θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ m : ℕ, |d| ≤ C * θ ^ m) : d = 0 := by
  have ht : Tendsto (fun m : ℕ => C * θ ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).const_mul C
  exact abs_nonpos_iff.1 (ge_of_tendsto' ht h)

lemma ylim_fixed {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    {x : ℝ → Fin K → ℝ} (hx : LB x) (w : Wt P) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, piOp P x (ylim P x) t = ylim P x t := by
  obtain ⟨c0, hc0, h⟩ := picard hP0 hx w
  have hyb := ylim_bd hP0 hx w
  have h1 : 0 < 1 - w.θ := by linarith [w.hθ1]
  intro t ht; funext j
  refine sub_eq_zero.1 (eq_zero_of_le_geom (C := 2 * c0 * w.v j * w.θ / (1 - w.θ))
    w.hθ w.hθ1 fun m => ?_)
  have hA := piOp_diff hP0 hx hx hyb (iter_bd hP0 hx m) (c := c0 * w.θ ^ m / (1 - w.θ))
    (δ := 0) (v := w.v)
    (fun s hs i => by
      rw [abs_sub_comm]; refine ((h s hs i).2 m).trans (le_of_eq ?_); ring)
    (fun s _ i => by simp) t ht j
  have hB := (h t ht j).2 (m + 1)
  have e : piOp P x (iter P x m) t j = iter P x (m + 1) t j := rfl
  rw [e] at hA
  calc |piOp P x (ylim P x) t j - ylim P x t j|
      ≤ |piOp P x (ylim P x) t j - iter P x (m+1) t j| + |iter P x (m+1) t j - ylim P x t j| :=
        abs_sub_le _ _ _
    _ ≤ (c0 * w.θ ^ m / (1 - w.θ) * vecMul w.v P j + 0)
          + c0 * w.v j * w.θ ^ (m+1) / (1 - w.θ) := add_le_add hA hB
    _ ≤ (c0 * w.θ ^ m / (1 - w.θ) * (w.θ * w.v j))
          + c0 * w.v j * w.θ ^ (m+1) / (1 - w.θ) := by
        rw [add_zero]
        exact add_le_add (mul_le_mul_of_nonneg_left (w.hvP j)
          (div_nonneg (mul_nonneg hc0 (pow_nonneg w.hθ m)) h1.le)) le_rfl
    _ = 2 * c0 * w.v j * w.θ / (1 - w.θ) * w.θ ^ m := by ring

/-- bounded fixed points are unique and Lipschitz in the input. -/
lemma fixed_unique {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (w : Wt P)
    {x x' y y' : ℝ → Fin K → ℝ} (hx : LB x) (hx' : LB x')
    (hy : Bd y) (hy' : Bd y') (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, piOp P x y t = y t)
    (hf' : ∀ t ∈ Set.Icc (0:ℝ) 1, piOp P x' y' t = y' t) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ i, |x s i - x' s i| ≤ δ) :
    ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ i, |y s i - y' s i| ≤ δ / (1 - w.θ) * w.v i := by
  obtain ⟨M, hM⟩ := hy
  obtain ⟨M', hM'⟩ := hy'
  have h1 : 0 < 1 - w.θ := by linarith [w.hθ1]
  have h1' : (1 - w.θ) ≠ 0 := h1.ne'
  set c0 := max (M + M') 0 with hc0
  have hc0n : 0 ≤ c0 := le_max_right _ _
  have hD : 0 ≤ δ / (1 - w.θ) := div_nonneg hδ0 h1.le
  have claim : ∀ k : ℕ, ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ i,
      |y s i - y' s i| ≤ (w.θ ^ k * c0 + δ / (1 - w.θ)) * w.v i := by
    intro k
    induction k with
    | zero =>
      intro s hs i
      have : |y s i - y' s i| ≤ M + M' :=
        (abs_sub _ _).trans (add_le_add (hM s hs i) (hM' s hs i))
      rw [pow_zero, one_mul]
      calc |y s i - y' s i| ≤ c0 := this.trans (le_max_left _ _)
        _ ≤ (c0 + δ / (1 - w.θ)) * 1 := by linarith
        _ ≤ (c0 + δ / (1 - w.θ)) * w.v i := mul_le_mul_of_nonneg_left (w.hv1 i) (by linarith)
    | succ k ih =>
      intro s hs i
      have hstep := piOp_diff hP0 hx hx' ⟨M, hM⟩ ⟨M', hM'⟩ ih hδ s hs i
      rw [hf s hs, hf' s hs] at hstep
      have hcn : 0 ≤ w.θ ^ k * c0 + δ / (1 - w.θ) :=
        add_nonneg (mul_nonneg (pow_nonneg w.hθ k) hc0n) hD
      calc |y s i - y' s i| ≤ (w.θ ^ k * c0 + δ / (1 - w.θ)) * vecMul w.v P i + δ := hstep
        _ ≤ (w.θ ^ k * c0 + δ / (1 - w.θ)) * (w.θ * w.v i) + δ * w.v i :=
            add_le_add (mul_le_mul_of_nonneg_left (w.hvP i) hcn)
              (le_mul_of_one_le_right hδ0 (w.hv1 i))
        _ = (w.θ ^ (k+1) * c0 + δ / (1 - w.θ)) * w.v i := by field_simp; ring
  intro s hs i
  have hlim : Tendsto (fun k : ℕ => (w.θ ^ k * c0 + δ / (1 - w.θ)) * w.v i) atTop
      (𝓝 ((0 * c0 + δ / (1 - w.θ)) * w.v i)) :=
    (((tendsto_pow_atTop_nhds_zero_of_lt_one w.hθ w.hθ1).mul_const c0).add_const _).mul_const _
  rw [zero_mul, zero_add] at hlim
  exact ge_of_tendsto' hlim fun k => claim k s hs i

lemma Phi_eq (P : Matrix (Fin K) (Fin K) ℝ) (x : ℝ → Fin K → ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : Phi P x t = x t + vecMul (ylim P x t) (1 - P) :=
  onUnit_of_mem ht

/-- the reflection map is Lipschitz in the sup norm on `[0, 1]`. -/
lemma Phi_close {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (w : Wt P)
    {x x' : ℝ → Fin K → ℝ} (hx : LB x) (hx' : LB x') {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ i, |x s i - x' s i| ≤ δ) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, ‖Phi P x t - Phi P x' t‖ ≤ (1 + 2 * w.W / (1 - w.θ)) * δ := by
  have h1 : 0 < 1 - w.θ := by linarith [w.hθ1]
  have hy := fixed_unique hP0 w hx hx' (ylim_bd hP0 hx w) (ylim_bd hP0 hx' w)
    (ylim_fixed hP0 hx w) (ylim_fixed hP0 hx' w) hδ0 hδ
  intro t ht
  rw [Phi_eq P x ht, Phi_eq P x' ht]
  have hD : 0 ≤ δ / (1 - w.θ) := div_nonneg hδ0 h1.le
  have hL : 0 ≤ (1 + 2 * w.W / (1 - w.θ)) * δ :=
    mul_nonneg (add_nonneg zero_le_one (div_nonneg (by linarith [w.hW]) h1.le)) hδ0
  refine (pi_norm_le_iff_of_nonneg hL).2 fun j => ?_
  rw [Real.norm_eq_abs]
  have ej : (x t + vecMul (ylim P x t) (1 - P) - (x' t + vecMul (ylim P x' t) (1 - P)) :
      Fin K → ℝ) j
      = (x t j - x' t j) + ((ylim P x t j - ylim P x' t j)
          - vecMul (ylim P x t - ylim P x' t) P j) := by
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.vecMul_sub, Matrix.vecMul_one,
      Matrix.sub_vecMul]
    ring
  rw [ej]
  have hb1 := hδ t ht j
  have hb2 := hy t ht j
  have hb3 := vecMul_abs_le hP0 (ylim P x t - ylim P x' t) (fun i => δ / (1 - w.θ) * w.v i)
    (fun i => hy t ht i) j
  rw [vecMul_smul_const] at hb3
  have hvPW : vecMul w.v P j ≤ w.W := by
    have := w.hvP j
    have hv0 : 0 ≤ w.v j := le_trans zero_le_one (w.hv1 j)
    nlinarith [w.hvW j, w.hθ1, w.hθ]
  calc |(x t j - x' t j) + ((ylim P x t j - ylim P x' t j) - vecMul (ylim P x t - ylim P x' t) P j)|
      ≤ |x t j - x' t j| + (|ylim P x t j - ylim P x' t j|
          + |vecMul (ylim P x t - ylim P x' t) P j|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
    _ ≤ δ + (δ / (1 - w.θ) * w.v j + δ / (1 - w.θ) * vecMul w.v P j) :=
        add_le_add hb1 (add_le_add hb2 hb3)
    _ ≤ δ + (δ / (1 - w.θ) * w.W + δ / (1 - w.θ) * w.W) :=
        add_le_add le_rfl (add_le_add (mul_le_mul_of_nonneg_left (w.hvW j) hD)
          (mul_le_mul_of_nonneg_left hvPW hD))
    _ = (1 + 2 * w.W / (1 - w.θ)) * δ := by field_simp; ring

/-! ### Running sups, right continuity, cadlag -/

lemma sup_le_of {g : ℝ → ℝ} {t c : ℝ} (ht : 0 ≤ t)
    (h : ∀ s ∈ Set.Icc (0:ℝ) t, max (g s) 0 ≤ c) : (⨆ q : ℚ, max (g (sel t q)) 0) ≤ c :=
  ciSup_le fun q => h _ (sel_mem ht q)

lemma le_sup_of {g : ℝ → ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hb : BddAbove (Set.range fun q : ℚ => max (g (sel t q)) 0))
    (hg : ∀ s ∈ Set.Ico (0:ℝ) 1, ContinuousWithinAt g (Set.Icc s 1) s) :
    ∀ s ∈ Set.Icc (0:ℝ) t, max (g s) 0 ≤ ⨆ q : ℚ, max (g (sel t q)) 0 := by
  intro s hs
  rcases eq_or_lt_of_le hs.2 with h | h
  · rw [h]; have := le_ciSup hb (-1); rwa [sel_neg] at this
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hs1 : s ∈ Set.Ico (0:ℝ) 1 := ⟨hs.1, lt_of_lt_of_le h ht.2⟩
    obtain ⟨η, hη, hηg⟩ := Metric.continuousWithinAt_iff.1 (hg s hs1) ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right s hη) h)
    have hq0 : 0 ≤ (q:ℝ) := hs.1.trans hq1.le
    have hqt : (q:ℝ) ≤ t := (lt_of_lt_of_le hq2 (min_le_right _ _)).le
    have hqη : (q:ℝ) < s + η := lt_of_lt_of_le hq2 (min_le_left _ _)
    have hd := hηg (x := (q:ℝ)) ⟨hq1.le, hqt.trans ht.2⟩
      (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith)
    rw [Real.dist_eq] at hd
    have hle := le_ciSup hb q
    rw [sel_rat q hq0 hqt] at hle
    have h3 := (abs_lt.1 hd).1
    have : max (g s) 0 ≤ max (g q) 0 + ε := by
      rcases le_total (g s) 0 with h0 | h0
      · rw [max_eq_right h0]; linarith [le_max_right (g q) 0]
      · rw [max_eq_left h0]; linarith [le_max_left (g q) 0]
    linarith

lemma rsup_bdd {g : ℝ → ℝ} {M : ℝ} (hM : ∀ s ∈ Set.Icc (0:ℝ) 1, g s ≤ M) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : BddAbove (Set.range fun q : ℚ => max (g (sel t q)) 0) :=
  ⟨max M 0, by rintro _ ⟨q, rfl⟩; exact max_le_max (hM _ (sel_mem01 ht q)) le_rfl⟩

lemma rsup_mono_rc {g : ℝ → ℝ}
    (hg : ∀ s ∈ Set.Ico (0:ℝ) 1, ContinuousWithinAt g (Set.Icc s 1) s)
    {M : ℝ} (hM : ∀ s ∈ Set.Icc (0:ℝ) 1, g s ≤ M) :
    MonotoneOn (fun t => ⨆ q : ℚ, max (g (sel t q)) 0) (Set.Icc 0 1) ∧
    ∀ t ∈ Set.Ico (0:ℝ) 1,
      ContinuousWithinAt (fun t => ⨆ q : ℚ, max (g (sel t q)) 0) (Set.Icc t 1) t := by
  have hmono : MonotoneOn (fun t => ⨆ q : ℚ, max (g (sel t q)) 0) (Set.Icc 0 1) := by
    intro a ha b hb hab
    exact sup_le_of ha.1 fun s hs =>
      le_sup_of hb (rsup_bdd hM hb) hg s ⟨hs.1, hs.2.trans hab⟩
  refine ⟨hmono, fun t ht => Metric.continuousWithinAt_iff.2 fun ε hε => ?_⟩
  have ht01 : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, ht.2.le⟩
  obtain ⟨η, hη, hηg⟩ := Metric.continuousWithinAt_iff.1 (hg t ht) (ε / 2) (by linarith)
  refine ⟨η, hη, fun {t'} ht' hd => ?_⟩
  have ht'01 : t' ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.trans ht'.1, ht'.2⟩
  have h1 := hmono ht01 ht'01 ht'.1
  have h2 : (⨆ q : ℚ, max (g (sel t' q)) 0) ≤ (⨆ q : ℚ, max (g (sel t q)) 0) + ε / 2 := by
    refine sup_le_of ht'01.1 fun s hs => ?_
    rcases le_total s t with hst | hst
    · have := le_sup_of ht01 (rsup_bdd hM ht01) hg s ⟨hs.1, hst⟩
      linarith
    · have hd' : dist s t < η := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
        rw [Real.dist_eq, abs_of_nonneg (by linarith [ht'.1])] at hd
        linarith [hs.2]
      have hgs := hηg (x := s) ⟨hst, hs.2.trans ht'.2⟩ hd'
      rw [Real.dist_eq] at hgs
      have h3 := (abs_lt.1 hgs).2
      have h4 := le_sup_of ht01 (rsup_bdd hM ht01) hg t ⟨ht.1, le_rfl⟩
      have : max (g s) 0 ≤ max (g t) 0 + ε / 2 := by
        rcases le_total (g s) 0 with h0 | h0
        · rw [max_eq_right h0]; linarith [le_max_right (g t) 0]
        · rw [max_eq_left h0]; linarith [le_max_left (g t) 0]
      linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- right continuity on `[0, 1)`. -/
def RCv (x : ℝ → Fin K → ℝ) : Prop :=
  ∀ s ∈ Set.Ico (0:ℝ) 1, ContinuousWithinAt x (Set.Icc s 1) s

lemma piOp_rc_mono {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    {x y : ℝ → Fin K → ℝ} (hx : RCv x) (hy : RCv y) (hxb : LB x) (hyb : Bd y) :
    RCv (piOp P x y) ∧ MonotoneOn (piOp P x y) (Set.Icc 0 1) := by
  obtain ⟨M, hM⟩ := hyb
  obtain ⟨Mx, hMx⟩ := hxb
  have hcont : Continuous fun v : Fin K → ℝ => vecMul v P :=
    continuous_id.matrix_vecMul continuous_const
  have key : ∀ j : Fin K,
      MonotoneOn (fun t => ⨆ q : ℚ, max ((fun r => (vecMul (y r) P - x r) j) (sel t q)) 0)
        (Set.Icc 0 1) ∧
      ∀ t ∈ Set.Ico (0:ℝ) 1, ContinuousWithinAt
        (fun t => ⨆ q : ℚ, max ((fun r => (vecMul (y r) P - x r) j) (sel t q)) 0)
        (Set.Icc t 1) t := by
    intro j
    refine rsup_mono_rc (g := fun r => (vecMul (y r) P - x r) j) (fun s hs => ?_) (M := vecMul (fun _ => M) P j + Mx) (fun s hs => ?_)
    · exact (continuous_apply j).continuousAt.comp_continuousWithinAt
        ((hcont.continuousAt.comp_continuousWithinAt (hy s hs)).sub (hx s hs))
    · have h1 := (abs_le.1 (vecMul_abs_le hP0 (y s) (fun _ => M) (fun i => hM _ hs i) j)).2
      have h2 := hMx _ hs j
      simp only [Pi.sub_apply]
      linarith
  refine ⟨fun s hs => continuousWithinAt_pi.2 fun j => (key j).2 s hs,
    fun a ha b hb hab j => (key j).1 ha hb hab⟩

lemma iter_rc_mono {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    {x : ℝ → Fin K → ℝ} (hx : RCv x) (hxb : LB x) :
    ∀ m, RCv (iter P x m) ∧ MonotoneOn (iter P x m) (Set.Icc 0 1)
  | 0 => ⟨fun _ _ => continuous_zero.continuousWithinAt, fun _ _ _ _ _ => le_rfl⟩
  | m + 1 => piOp_rc_mono hP0 hx (iter_rc_mono hP0 hx hxb m).1 hxb (iter_bd hP0 hxb m)

lemma ylim_rc_mono {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (w : Wt P)
    {x : ℝ → Fin K → ℝ} (hx : RCv x) (hxb : LB x) :
    RCv (ylim P x) ∧ MonotoneOn (ylim P x) (Set.Icc 0 1) := by
  obtain ⟨c0, hc0, h⟩ := picard hP0 hxb w
  have hit := iter_rc_mono hP0 hx hxb
  have h1 : 0 < 1 - w.θ := by linarith [w.hθ1]
  constructor
  · intro s hs
    refine continuousWithinAt_pi.2 fun j => Metric.continuousWithinAt_iff.2 fun ε hε => ?_
    have ht : Tendsto (fun m : ℕ => c0 * w.W * w.θ ^ m / (1 - w.θ)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one w.hθ w.hθ1).const_mul
        (c0 * w.W)).div_const (1 - w.θ)
      simpa using this
    obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 3))).exists
    have hbd : ∀ r ∈ Set.Icc (0:ℝ) 1, |iter P x m r j - ylim P x r j| < ε / 3 := by
      intro r hr
      refine lt_of_le_of_lt ((h r hr j).2 m) (lt_of_le_of_lt ?_ hm)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (w.hvW j) hc0) (pow_nonneg w.hθ m)) h1.le
    have hcm := continuousWithinAt_pi.1 ((hit m).1 s hs) j
    obtain ⟨η, hη, hηm⟩ := Metric.continuousWithinAt_iff.1 hcm (ε / 3) (by linarith)
    refine ⟨η, hη, fun {r} hr hrs => ?_⟩
    have hr01 : r ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1.trans hr.1, hr.2⟩
    have hs01 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have a1 := abs_lt.1 (hbd r hr01)
    have a2 := abs_lt.1 (hbd s hs01)
    have a3 := hηm hr hrs
    rw [Real.dist_eq] at a3 ⊢
    have a3' := abs_lt.1 a3
    rw [abs_lt]; constructor <;> linarith
  · intro a ha b hb hab j
    exact le_of_tendsto_of_tendsto' ((h a ha j).1) ((h b hb j).1) fun m => (hit m).2 ha hb hab j

lemma clamp01_mem (r : ℝ) : Reiman84.QueueLength.clamp01 r ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

lemma clamp01_mono : Monotone Reiman84.QueueLength.clamp01 :=
  fun _ _ hab => min_le_min (max_le_max hab le_rfl) le_rfl

lemma left_lim_of_mono {f : ℝ → Fin K → ℝ} (hf : MonotoneOn f (Set.Icc 0 1)) {t : ℝ}
    (ht : t ∈ Set.Ioc (0:ℝ) 1) : ∃ l, Tendsto f (𝓝[Set.Ico 0 t] t) (𝓝 l) := by
  set g : ℝ → Fin K → ℝ := fun r => f (Reiman84.QueueLength.clamp01 r) with hg
  have hgm : ∀ j, Monotone fun r => g r j := fun j a b hab =>
    hf (clamp01_mem a) (clamp01_mem b) (clamp01_mono hab) j
  refine ⟨fun j => sSup ((fun r => g r j) '' Set.Iio t), tendsto_pi_nhds.2 fun j => ?_⟩
  have h1 := ((hgm j).tendsto_nhdsLT t).mono_left (nhdsWithin_mono t (Set.Ico_subset_Iio_self (a := 0)))
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [hg, clamp01_of_mem ⟨hr.1, hr.2.le.trans ht.2⟩]

lemma cadlag_congr {f g : ℝ → Fin K → ℝ} (h : ∀ s ∈ Set.Icc (0:ℝ) 1, f s = g s)
    (hf : Reiman84.QueueLength.IsCadlag01 f) : Reiman84.QueueLength.IsCadlag01 g := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · exact (hf.1 t ht).congr (fun s hs => (h s ⟨ht.1.trans hs.1, hs.2⟩).symm)
      (h t ⟨ht.1, ht.2.le⟩).symm
  · obtain ⟨l, hl⟩ := hf.2 t ht
    refine ⟨l, hl.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact h s ⟨hs.1, hs.2.le.trans ht.2⟩

lemma Phi_cadlag {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (w : Wt P)
    {x : ℝ → Fin K → ℝ} (hx : Reiman84.QueueLength.IsCadlag01 x) (hxb : LB x) :
    Reiman84.QueueLength.IsCadlag01 (Phi P x) := by
  obtain ⟨hyr, hym⟩ := ylim_rc_mono hP0 w hx.1 hxb
  have hcont : Continuous fun v : Fin K → ℝ => vecMul v (1 - P) :=
    continuous_id.matrix_vecMul continuous_const
  refine cadlag_congr (f := fun t => x t + vecMul (ylim P x t) (1 - P))
    (fun s hs => (Phi_eq P x hs).symm) ⟨fun t ht => ?_, fun t ht => ?_⟩
  · exact (hx.1 t ht).add (hcont.continuousAt.comp_continuousWithinAt (hyr t ht))
  · obtain ⟨l, hl⟩ := hx.2 t ht
    obtain ⟨l', hl'⟩ := left_lim_of_mono hym ht
    exact ⟨l + vecMul l' (1 - P), hl.add ((hcont.tendsto l').comp hl')⟩

/-- identification: a continuous complementary regulator is a fixed point of `π`. -/
lemma fixed_of_compl {P : Matrix (Fin K) (Fin K) ℝ} {x y : ℝ → Fin K → ℝ}
    (hyc : ContinuousOn y (Set.Icc 0 1)) (hym : MonotoneOn y (Set.Icc 0 1)) (hy0 : y 0 = 0)
    (hz : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ x s + vecMul (y s) (1 - P))
    (hzr : ∀ s ∈ Set.Ico (0:ℝ) 1,
      ContinuousWithinAt (fun r => x r + vecMul (y r) (1 - P)) (Set.Icc s 1) s)
    (hcomp : ∀ j : Fin K, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
      (∀ r ∈ Set.Icc s t, 0 < (x r + vecMul (y r) (1 - P) : Fin K → ℝ) j) → y t j = y s j) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, piOp P x y t = y t := by
  intro t ht; funext j
  set z : ℝ → ℝ := fun r => (x r + vecMul (y r) (1 - P) : Fin K → ℝ) j with hzdef
  have hw : ∀ r, (vecMul (y r) P - x r) j = y r j - z r := by
    intro r
    simp only [hzdef, Pi.add_apply, Pi.sub_apply, Matrix.vecMul_sub, Matrix.vecMul_one]
    ring
  have hy0' : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ y s j := fun s hs => by
    have := hym ⟨le_rfl, zero_le_one⟩ hs hs.1 j
    rw [hy0] at this; exact this
  have hub : ∀ q : ℚ, max ((vecMul (y (sel t q)) P - x (sel t q)) j) 0 ≤ y t j := by
    intro q
    have hs := sel_mem ht.1 q
    have hs01 := sel_mem01 ht q
    rw [hw]
    refine max_le ?_ (hy0' t ht)
    have h1 : 0 ≤ z (sel t q) := hz _ hs01 j
    have h2 := hym hs01 ht hs.2 j
    linarith
  have hb : BddAbove (Set.range fun q : ℚ => max ((vecMul (y (sel t q)) P - x (sel t q)) j) 0) :=
    ⟨y t j, by rintro _ ⟨q, rfl⟩; exact hub q⟩
  show (⨆ q : ℚ, max ((vecMul (y (sel t q)) P - x (sel t q)) j) 0) = y t j
  apply le_antisymm (ciSup_le hub)
  have hsupnn : 0 ≤ ⨆ q : ℚ, max ((vecMul (y (sel t q)) P - x (sel t q)) j) 0 :=
    Real.iSup_nonneg fun _ => le_max_right _ _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hsmall : y t j ≤ ε / 2
  · linarith
  push Not at hsmall
  have hsub : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc le_rfl ht.2
  have hcj : ContinuousOn (fun r => y r j) (Set.Icc 0 t) :=
    ((continuous_apply j).comp_continuousOn hyc).mono hsub
  have hivt := intermediate_value_Icc ht.1 hcj
  obtain ⟨s1, hs1, hys1⟩ := hivt (show y t j - ε / 2 ∈ Set.Icc (y 0 j) (y t j) from
    ⟨by rw [hy0, Pi.zero_apply]; linarith, by linarith⟩)
  have hys1' : y s1 j = y t j - ε / 2 := hys1
  have hne : y t j ≠ y s1 j := by rw [hys1']; linarith
  have hnot : ¬ ∀ r ∈ Set.Icc s1 t, 0 < z r := fun hall =>
    hne (hcomp j s1 t hs1.1 hs1.2 ht.2 hall)
  push Not at hnot
  obtain ⟨r, hr, hzr0⟩ := hnot
  have hr01 : r ∈ Set.Icc (0:ℝ) 1 := ⟨hs1.1.trans hr.1, hr.2.trans ht.2⟩
  have hzr' : z r = 0 := le_antisymm hzr0 (hz r hr01 j)
  have hyr : y t j - ε / 2 ≤ y r j := by
    have := hym ⟨hs1.1, hs1.2.trans ht.2⟩ hr01 hr.1 j
    linarith
  rcases eq_or_lt_of_le hr.2 with hrt | hrt
  · have h1 := le_ciSup hb (-1)
    rw [sel_neg, hw] at h1
    rw [hrt] at hzr' hyr
    have h2 : y t j - z t ≤ max (y t j - z t) 0 := le_max_left _ _
    linarith
  · have hr1 : r ∈ Set.Ico (0:ℝ) 1 := ⟨hr01.1, lt_of_lt_of_le hrt ht.2⟩
    have hzc : ContinuousWithinAt z (Set.Icc r 1) r :=
      (continuous_apply j).continuousAt.comp_continuousWithinAt (hzr r hr1)
    obtain ⟨η, hη, hηz⟩ := Metric.continuousWithinAt_iff.1 hzc (ε / 2) (by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right r hη) hrt)
    have hq0 : 0 ≤ (q:ℝ) := hr01.1.trans hq1.le
    have hqt : (q:ℝ) ≤ t := (lt_of_lt_of_le hq2 (min_le_right _ _)).le
    have hqη : (q:ℝ) < r + η := lt_of_lt_of_le hq2 (min_le_left _ _)
    have hd := hηz (x := (q:ℝ)) ⟨hq1.le, hqt.trans ht.2⟩
      (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith)
    rw [Real.dist_eq, hzr'] at hd
    have hyq : y r j ≤ y q j := hym hr01 ⟨hq0, hqt.trans ht.2⟩ hq1.le j
    have h1 := le_ciSup hb q
    rw [sel_rat q hq0 hqt, hw] at h1
    have h2 : y q j - z q ≤ max (y q j - z q) 0 := le_max_left _ _
    have h3 := (abs_lt.1 hd).2
    linarith

lemma lam_maps {lam : ℝ → ℝ} (hlm : StrictMonoOn lam (Set.Icc 0 1)) (hl0 : lam 0 = 0)
    (hl1 : lam 1 = 1) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) : lam s ∈ Set.Icc (0:ℝ) 1 := by
  have hm := hlm.monotoneOn
  exact ⟨hl0 ▸ hm ⟨le_rfl, zero_le_one⟩ hs hs.1, hl1 ▸ hm hs ⟨zero_le_one, le_rfl⟩ hs.2⟩

lemma LB_comp {x : ℝ → Fin K → ℝ} (hx : LB x) {lam : ℝ → ℝ}
    (hl : ∀ s ∈ Set.Icc (0:ℝ) 1, lam s ∈ Set.Icc (0:ℝ) 1) : LB (x ∘ lam) := by
  obtain ⟨M, hM⟩ := hx; exact ⟨M, fun s hs i => hM _ (hl s hs) i⟩

lemma Bd_comp {x : ℝ → Fin K → ℝ} (hx : Bd x) {lam : ℝ → ℝ}
    (hl : ∀ s ∈ Set.Icc (0:ℝ) 1, lam s ∈ Set.Icc (0:ℝ) 1) : Bd (x ∘ lam) := by
  obtain ⟨M, hM⟩ := hx; exact ⟨M, fun s hs i => hM _ (hl s hs) i⟩

/-- a fixed point composed with a time change is a fixed point for the time-changed input. -/
lemma fixed_comp {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    {x y : ℝ → Fin K → ℝ} (hx : RCv x) (hy : RCv y) (hxb : LB x) (hyb : Bd y)
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, piOp P x y t = y t) {lam : ℝ → ℝ}
    (hlc : ContinuousOn lam (Set.Icc 0 1)) (hlm : StrictMonoOn lam (Set.Icc 0 1))
    (hl0 : lam 0 = 0) (hl1 : lam 1 = 1) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, piOp P (x ∘ lam) (y ∘ lam) t = (y ∘ lam) t := by
  intro t ht; funext j
  obtain ⟨M, hM⟩ := hyb
  obtain ⟨Mx, hMx⟩ := hxb
  have hcont : Continuous fun v : Fin K → ℝ => vecMul v P :=
    continuous_id.matrix_vecMul continuous_const
  set g : ℝ → ℝ := fun r => (vecMul (y r) P - x r) j with hgdef
  have hgM : ∀ s ∈ Set.Icc (0:ℝ) 1, g s ≤ vecMul (fun _ => M) P j + Mx := by
    intro s hs
    have h1 := (abs_le.1 (vecMul_abs_le hP0 (y s) (fun _ => M) (fun i => hM _ hs i) j)).2
    have h2 := hMx _ hs j
    simp only [hgdef, Pi.sub_apply]
    linarith
  have hgr : ∀ s ∈ Set.Ico (0:ℝ) 1, ContinuousWithinAt g (Set.Icc s 1) s := fun s hs =>
    (continuous_apply j).continuousAt.comp_continuousWithinAt
      ((hcont.continuousAt.comp_continuousWithinAt (hy s hs)).sub (hx s hs))
  have hmaps := fun s hs => lam_maps hlm hl0 hl1 (s := s) hs
  have hhM : ∀ s ∈ Set.Icc (0:ℝ) 1, (g ∘ lam) s ≤ vecMul (fun _ => M) P j + Mx :=
    fun s hs => hgM _ (hmaps s hs)
  have hhr : ∀ s ∈ Set.Ico (0:ℝ) 1, ContinuousWithinAt (g ∘ lam) (Set.Icc s 1) s := by
    intro s hs
    have hs01 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have hls : lam s ∈ Set.Ico (0:ℝ) 1 := ⟨(hmaps s hs01).1, by
      rw [← hl1]; exact hlm hs01 ⟨zero_le_one, le_rfl⟩ hs.2⟩
    refine (hgr (lam s) hls).comp ((hlc s hs01).mono (Set.Icc_subset_Icc hs.1 le_rfl)) ?_
    intro r hr
    have hr01 : r ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1.trans hr.1, hr.2⟩
    exact ⟨hlm.monotoneOn hs01 hr01 hr.1, (hmaps r hr01).2⟩
  have hlt := hmaps t ht
  have hfy := congrFun (hf (lam t) hlt) j
  show (⨆ q : ℚ, max ((g ∘ lam) (sel t q)) 0) = y (lam t) j
  rw [← hfy]
  show (⨆ q : ℚ, max ((g ∘ lam) (sel t q)) 0) = ⨆ q : ℚ, max (g (sel (lam t) q)) 0
  apply le_antisymm
  · refine sup_le_of ht.1 fun s hs => ?_
    have hs01 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
    exact le_sup_of hlt (rsup_bdd hgM hlt) hgr (lam s)
      ⟨(hmaps s hs01).1, hlm.monotoneOn hs01 ht hs.2⟩
  · refine sup_le_of hlt.1 fun s' hs' => ?_
    have hivt := intermediate_value_Icc ht.1 (hlc.mono (Set.Icc_subset_Icc le_rfl ht.2))
    rw [hl0] at hivt
    obtain ⟨s, hs, rfl⟩ := hivt hs'
    exact le_sup_of ht (rsup_bdd hhM ht) hhr s hs

lemma Phi_comp {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (w : Wt P)
    {x : ℝ → Fin K → ℝ} (hx : RCv x) (hxb : LB x) {lam : ℝ → ℝ}
    (hlc : ContinuousOn lam (Set.Icc 0 1)) (hlm : StrictMonoOn lam (Set.Icc 0 1))
    (hl0 : lam 0 = 0) (hl1 : lam 1 = 1) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, Phi P x (lam t) = Phi P (x ∘ lam) t := by
  intro t ht
  have hmaps := fun s hs => lam_maps hlm hl0 hl1 (s := s) hs
  have hxl : LB (x ∘ lam) := LB_comp hxb hmaps
  obtain ⟨hyr, -⟩ := ylim_rc_mono hP0 w hx hxb
  have hfix := fixed_comp hP0 hx hyr hxb (ylim_bd hP0 hxb w) (ylim_fixed hP0 hxb w) hlc hlm hl0 hl1
  have hu := fixed_unique hP0 w hxl hxl (Bd_comp (ylim_bd hP0 hxb w) hmaps) (ylim_bd hP0 hxl w)
    hfix (ylim_fixed hP0 hxl w) le_rfl (fun s _ i => by simp)
  have he : ylim P x (lam t) = ylim P (x ∘ lam) t := by
    funext i
    have := hu t ht i
    rw [zero_div, zero_mul] at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  rw [Phi_eq P x (hmaps t ht), Phi_eq P (x ∘ lam) ht, he]
  simp only [Function.comp]

/-- cadlag paths are bounded on `[0, 1]`. -/
lemma cadlag_bdd {x : ℝ → Fin K → ℝ} (hx : Reiman84.QueueLength.IsCadlag01 x) :
    ∃ M, ∀ s ∈ Set.Icc (0:ℝ) 1, ‖x s‖ ≤ M := by
  refine isCompact_Icc.induction_on (p := fun S => ∃ M, ∀ s ∈ S, ‖x s‖ ≤ M) ⟨0, by simp⟩
    (fun S T hST ⟨M, hM⟩ => ⟨M, fun s hs => hM s (hST hs)⟩)
    (fun S T ⟨M, hM⟩ ⟨M', hM'⟩ => ⟨max M M', fun s hs => hs.elim
      (fun h => (hM s h).trans (le_max_left _ _)) (fun h => (hM' s h).trans (le_max_right _ _))⟩)
    (fun t ht => ?_)
  have hR : {s | ‖x s‖ ≤ ‖x t‖ + 1} ∈ 𝓝[Set.Icc t 1] t := by
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have : s = t := le_antisymm (hs.2.trans h1.ge) hs.1
      rw [this]; linarith
    · have hc := hx.1 t ⟨ht.1, h1⟩
      filter_upwards [hc.eventually (Metric.ball_mem_nhds (x t) one_pos)] with s hs
      rw [dist_eq_norm] at hs
      have := norm_le_norm_add_norm_sub' (x s) (x t)
      linarith
  have hL : ∃ B, {s | ‖x s‖ ≤ B} ∈ 𝓝[Set.Ico 0 t] t := by
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · refine ⟨0, ?_⟩
      rw [← h0, Set.Ico_self, nhdsWithin_empty]; exact Filter.mem_bot
    · obtain ⟨l, hl⟩ := hx.2 t ⟨h0, ht.2⟩
      refine ⟨‖l‖ + 1, ?_⟩
      filter_upwards [hl.eventually (Metric.ball_mem_nhds l one_pos)] with s hs
      rw [dist_eq_norm] at hs
      have := norm_le_norm_add_norm_sub' (x s) l
      linarith
  obtain ⟨B, hB⟩ := hL
  refine ⟨{s | ‖x s‖ ≤ max (‖x t‖ + 1) B}, ?_, ⟨max (‖x t‖ + 1) B, fun s hs => hs⟩⟩
  have hU : Set.Icc (0:ℝ) 1 = Set.Ico 0 t ∪ Set.Icc t 1 := (Set.Ico_union_Icc_eq_Icc ht.1 ht.2).symm
  rw [hU, nhdsWithin_union]
  exact Filter.mem_sup.2 ⟨mem_of_superset hB fun s (hs : ‖x s‖ ≤ B) =>
      (show ‖x s‖ ≤ max (‖x t‖ + 1) B from le_trans hs (le_max_right _ _)),
    mem_of_superset hR fun s (hs : ‖x s‖ ≤ ‖x t‖ + 1) =>
      (show ‖x s‖ ≤ max (‖x t‖ + 1) B from le_trans hs (le_max_left _ _))⟩

lemma LB_of_cadlag {x : ℝ → Fin K → ℝ} (hx : Reiman84.QueueLength.IsCadlag01 x) : LB x := by
  obtain ⟨M, hM⟩ := cadlag_bdd hx
  refine ⟨M, fun s hs i => ?_⟩
  have := (norm_le_pi_norm (x s) i).trans (hM s hs)
  rw [Real.norm_eq_abs] at this
  linarith [neg_abs_le (x s i)]

/-- `J₁` continuity of the reflection map. -/
lemma Phi_skorohod {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (w : Wt P)
    {xs : ℕ → ℝ → Fin K → ℝ} {x : ℝ → Fin K → ℝ}
    (h : Reiman84.QueueLength.SkorohodTendsto xs x) :
    Reiman84.QueueLength.SkorohodTendsto (fun n => Phi P (xs n)) (Phi P x) := by
  obtain ⟨hxs, hx, lam, hlam, hconv⟩ := h
  have h1 : 0 < 1 - w.θ := by linarith [w.hθ1]
  set L : ℝ := 1 + 2 * w.W / (1 - w.θ) with hL
  have hLpos : 0 < L := by
    have : 0 ≤ 2 * w.W / (1 - w.θ) := div_nonneg (by linarith [w.hW]) h1.le
    linarith
  refine ⟨fun n => Phi_cadlag hP0 w (hxs n) (LB_of_cadlag (hxs n)),
    Phi_cadlag hP0 w hx (LB_of_cadlag hx), lam, hlam, fun ε hε => ?_⟩
  have hε' : 0 < min ε (ε / (2 * L)) := lt_min hε (by positivity)
  filter_upwards [hconv _ hε'] with n hn t ht
  obtain ⟨hlc, hlm, hl0, hl1⟩ := hlam n
  refine ⟨lt_of_lt_of_le (hn t ht).1 (min_le_left _ _), ?_⟩
  rw [Phi_comp hP0 w (hxs n).1 (LB_of_cadlag (hxs n)) hlc hlm hl0 hl1 t ht]
  have hmaps := fun s hs => lam_maps hlm hl0 hl1 (s := s) hs
  have hb := Phi_close hP0 w (LB_comp (LB_of_cadlag (hxs n)) hmaps) (LB_of_cadlag hx)
    (δ := min ε (ε / (2 * L))) hε'.le (fun s hs i => by
      have := (norm_le_pi_norm (xs n (lam n s) - x s) i).trans (hn s hs).2.le
      rw [Real.norm_eq_abs] at this
      exact this) t ht
  refine lt_of_le_of_lt hb ?_
  have : L * min ε (ε / (2 * L)) ≤ L * (ε / (2 * L)) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hLpos.le
  have e : L * (ε / (2 * L)) = ε / 2 := by field_simp
  linarith

/-- the reflection map on a complementary pair. -/
lemma Phi_of_compl {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (w : Wt P)
    {x y z : ℝ → Fin K → ℝ}
    (hxyz : ∀ s ∈ Set.Icc (0:ℝ) 1, z s = x s + vecMul (y s) (1 - P))
    (hyc : ContinuousOn y (Set.Icc 0 1)) (hym : MonotoneOn y (Set.Icc 0 1)) (hy0 : y 0 = 0)
    (hz : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ z s)
    (hzr : ∀ s ∈ Set.Ico (0:ℝ) 1, ContinuousWithinAt z (Set.Icc s 1) s)
    (hcomp : ∀ j : Fin K, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
      (∀ r ∈ Set.Icc s t, 0 < z r j) → y t j = y s j) :
    ∀ t, Phi P (Reiman84.QueueLength.onUnit x) t = Reiman84.QueueLength.onUnit z t := by
  set x' := Reiman84.QueueLength.onUnit x with hx'
  have hxx : ∀ s ∈ Set.Icc (0:ℝ) 1, x' s = x s := fun s hs => onUnit_of_mem hs
  have hxyz' : ∀ s ∈ Set.Icc (0:ℝ) 1, z s = x' s + vecMul (y s) (1 - P) := fun s hs => by
    rw [hxx s hs]; exact hxyz s hs
  obtain ⟨My, hMy⟩ := isCompact_Icc.exists_bound_of_continuousOn hyc
  have hyb : Bd y := ⟨My, fun s hs i => by
    have := (norm_le_pi_norm (y s) i).trans (hMy s hs); rwa [Real.norm_eq_abs] at this⟩
  have hxb : LB x' := by
    obtain ⟨M, hM⟩ := hyb
    set M0 := max M 0 with hM0
    refine ⟨∑ i, ∑ k, M0 * |(1 - P) k i|, fun s hs i => ?_⟩
    have h1 : |vecMul (y s) (1 - P) i| ≤ ∑ k, M0 * |(1 - P) k i| := by
      simp only [vecMul, dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right ((hM s hs k).trans (le_max_left _ _)) (abs_nonneg _)
    have h2 : ∑ k, M0 * |(1 - P) k i| ≤ ∑ i, ∑ k, M0 * |(1 - P) k i| :=
      Finset.single_le_sum (f := fun i => ∑ k, M0 * |(1 - P) k i|)
        (fun i _ => Finset.sum_nonneg fun k _ => mul_nonneg (le_max_right _ _) (abs_nonneg _))
        (Finset.mem_univ i)
    have h3 := hz s hs i
    have h4 := congrFun (hxyz' s hs) i
    simp only [Pi.add_apply] at h4
    have h5 := (abs_le.1 h1).2
    simp only [Pi.zero_apply] at h3
    linarith
  have hfix : ∀ t ∈ Set.Icc (0:ℝ) 1, piOp P x' y t = y t :=
    fixed_of_compl hyc hym hy0 (fun s hs => by rw [← hxyz' s hs]; exact hz s hs)
      (fun s hs => (hzr s hs).congr (fun r hr => (hxyz' r ⟨hs.1.trans hr.1, hr.2⟩).symm)
        (hxyz' s ⟨hs.1, hs.2.le⟩).symm)
      (fun j s t h0 hst ht1 hall => hcomp j s t h0 hst ht1 fun r hr => by
        rw [hxyz' r ⟨h0.trans hr.1, hr.2.trans ht1⟩]; exact hall r hr)
  have hu := fixed_unique hP0 w hxb hxb (ylim_bd hP0 hxb w) hyb (ylim_fixed hP0 hxb w) hfix
    le_rfl (fun s _ i => by simp)
  intro t
  have hc := clamp01_mem t
  have he : ylim P x' (Reiman84.QueueLength.clamp01 t) = y (Reiman84.QueueLength.clamp01 t) := by
    funext i
    have := hu _ hc i
    rw [zero_div, zero_mul] at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  show x' (Reiman84.QueueLength.clamp01 t) + vecMul (ylim P x' (Reiman84.QueueLength.clamp01 t)) (1 - P)
    = z (Reiman84.QueueLength.clamp01 t)
  rw [he, hxyz' _ hc]

/-! ### Measurability -/

lemma meas_eval (t : ℝ) (j : Fin K) : Measurable fun x : ℝ → Fin K → ℝ => x t j :=
  (measurable_pi_apply j).comp (measurable_pi_apply t)

lemma iter_meas (P : Matrix (Fin K) (Fin K) ℝ) :
    ∀ m (t : ℝ) (j : Fin K), Measurable fun x : ℝ → Fin K → ℝ => iter P x m t j
  | 0, _, _ => measurable_const
  | m + 1, t, j => by
    show Measurable fun x : ℝ → Fin K → ℝ =>
      ⨆ q : ℚ, max ((vecMul (iter P x m (sel t q)) P - x (sel t q)) j) 0
    refine Measurable.iSup fun q => Measurable.max ?_ measurable_const
    simp only [Pi.sub_apply, vecMul, dotProduct]
    exact (Finset.measurable_sum _ fun i _ => (iter_meas P m (sel t q) i).mul_const _).sub
      (meas_eval _ j)

lemma Phi_meas (P : Matrix (Fin K) (Fin K) ℝ) : Measurable (Phi P (K := K)) := by
  refine measurable_pi_lambda _ fun t => measurable_pi_lambda _ fun j => ?_
  have hy : ∀ s i, Measurable fun x : ℝ → Fin K → ℝ => ylim P x s i := fun s i =>
    Measurable.limsup fun m => iter_meas P m s i
  show Measurable fun x : ℝ → Fin K → ℝ =>
    (x (Reiman84.QueueLength.clamp01 t)
      + vecMul (ylim P x (Reiman84.QueueLength.clamp01 t)) (1 - P) : Fin K → ℝ) j
  simp only [Pi.add_apply, vecMul, dotProduct]
  exact (meas_eval _ j).add (Finset.measurable_sum _ fun i _ => (hy _ i).mul_const _)

/-! ### Counting functions -/

lemma cnt_spec {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F)
    (hFt : Tendsto F atTop atTop) {b : ℝ} (hb : 0 ≤ b) :
    F (sSup {l | F l ≤ b}) ≤ b ∧ b < F (sSup {l | F l ≤ b} + 1) := by
  obtain ⟨L, hL⟩ := (hFt.eventually (eventually_gt_atTop b)).exists
  have hbdd : BddAbove {l | F l ≤ b} := ⟨L, fun l (hl : F l ≤ b) => by
    by_contra h; push Not at h; linarith [hFm h]⟩
  have hne : ({l | F l ≤ b} : Set ℕ).Nonempty := ⟨0, by show F 0 ≤ b; rw [hF0]; exact hb⟩
  refine ⟨Nat.sSup_mem hne hbdd, ?_⟩
  by_contra h; push Not at h
  have := le_csSup hbdd (show F (sSup {l | F l ≤ b} + 1) ≤ b from h)
  omega

lemma cnt_eq {F : ℕ → ℝ} (hFm : StrictMono F) {b : ℝ} {m n : ℕ} (h1 : F m ≤ b)
    (h2 : b < F (m + 1)) (h3 : F n ≤ b) (h4 : b < F (n + 1)) : n = m := by
  have a : n < m + 1 := hFm.lt_iff_lt.1 (lt_of_le_of_lt h3 h2)
  have c : m < n + 1 := hFm.lt_iff_lt.1 (lt_of_le_of_lt h1 h4)
  omega

lemma cnt_mono {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F)
    (hFt : Tendsto F atTop atTop) {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    sSup {l | F l ≤ b} ≤ sSup {l | F l ≤ b'} := by
  have h1 := cnt_spec hF0 hFm hFt hb
  have h2 := cnt_spec hF0 hFm hFt (hb.trans hbb)
  have := hFm.lt_iff_lt.1 (lt_of_le_of_lt (h1.1.trans hbb) h2.2)
  omega

lemma cnt_rc {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F)
    (hFt : Tendsto F atTop atTop) {b : ℝ} (hb : 0 ≤ b) :
    ∀ᶠ b' in 𝓝[≥] b, b' < F (sSup {l | F l ≤ b} + 1) ∧
      sSup {l | F l ≤ b'} = sSup {l | F l ≤ b} := by
  have h1 := cnt_spec hF0 hFm hFt hb
  filter_upwards [Ico_mem_nhdsGE h1.2] with b' hb'
  have h2 := cnt_spec hF0 hFm hFt (hb.trans hb'.1)
  exact ⟨hb'.2, cnt_eq hFm (h1.1.trans hb'.1) hb'.2 h2.1 h2.2⟩

/-! ### One network -/

section Net

open Reiman84.QueueLength

variable {J : Finset (Fin K)} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}

lemma U_zero (N : Network K J μP) (k : Fin K) (ω : Ω) : N.U k 0 ω = 0 := by
  simp [Network.U]

lemma V_zero (N : Network K J μP) (k : Fin K) (ω : Ω) : N.V k 0 ω = 0 := by
  simp [Network.V]

lemma U_mono (N : Network K J μP) {k : Fin K} (hk : k ∈ J) (ω : Ω) :
    StrictMono fun l => N.U k l ω :=
  strictMono_nat_of_lt_succ fun l => by
    simp only [Network.U, Finset.sum_range_succ]; linarith [N.pos_u k hk l ω]

lemma V_mono (N : Network K J μP) (k : Fin K) (ω : Ω) : StrictMono fun l => N.V k l ω :=
  strictMono_nat_of_lt_succ fun l => by
    simp only [Network.V, Finset.sum_range_succ]; linarith [N.pos_v k l ω]

lemma ind_intervalIntegrable (Q : ℝ → Fin K → ℝ) (k : Fin K) (hQ : Measurable fun s => Q s k)
    (a b : ℝ) : IntervalIntegrable (fun s => if 0 < Q s k then (1:ℝ) else 0) volume a b := by
  refine ((show Continuous (fun _ : ℝ => (1:ℝ)) from continuous_const).intervalIntegrable a b).mono_fun
    ?_ (ae_of_all _ fun s => ?_)
  · exact (Measurable.ite (measurableSet_lt measurable_const hQ) measurable_const
      measurable_const).aestronglyMeasurable
  · simp only [Real.norm_eq_abs]; split_ifs <;> norm_num

variable (N : Network K J μP) (ω : Ω) (Q B : ℝ → Fin K → ℝ) (h : N.IsQueueSolution ω Q B)
include h

lemma B_diff (k : Fin K) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    B t k - B s k = ∫ r in s..t, (if 0 < Q r k then (1:ℝ) else 0) := by
  rw [h.2.2.2.1 k t (hs.trans hst), h.2.2.2.1 k s hs]
  exact intervalIntegral.integral_interval_sub_left
    (ind_intervalIntegrable Q k (h.2.2.1 k) 0 t) (ind_intervalIntegrable Q k (h.2.2.1 k) 0 s)

lemma B_bounds (k : Fin K) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ B t k - B s k ∧ B t k - B s k ≤ t - s := by
  rw [B_diff N ω Q B h k hs hst]
  constructor
  · exact intervalIntegral.integral_nonneg hst fun u _ => by split_ifs <;> norm_num
  · have := intervalIntegral.integral_mono_on hst
      (ind_intervalIntegrable Q k (h.2.2.1 k) s t)
      ((show Continuous (fun _ : ℝ => (1:ℝ)) from continuous_const).intervalIntegrable s t)
      (fun u _ => by split_ifs <;> norm_num)
    simpa using this

lemma B_full (k : Fin K) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hpos : ∀ r ∈ Set.Icc s t, 0 < Q r k) : B t k - B s k = t - s := by
  rw [B_diff N ω Q B h k hs hst]
  rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) (fun r hr => by
    rw [Set.uIcc_of_le hst] at hr; simp only [if_pos (hpos r hr)])]
  simp

lemma B_flat (k : Fin K) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hz : ∀ r ∈ Set.Icc s t, Q r k ≤ 0) : B t k = B s k := by
  have := B_diff N ω Q B h k hs hst
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun r hr => by
    rw [Set.uIcc_of_le hst] at hr; simp only [if_neg (not_lt.2 (hz r hr))])] at this
  simp at this; linarith

lemma B_nonneg (k : Fin K) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ B t k := by
  have := (B_bounds N ω Q B h k le_rfl ht).1
  rw [h.2.1 k, sub_zero] at this; exact this

lemma B_cont (k : Fin K) : ContinuousOn (fun r => B r k) (Set.Ici 0) := by
  refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun a ha b hb => ?_).continuousOn
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total a b with hab | hab
  · have := B_bounds N ω Q B h k ha hab
    rw [abs_sub_comm, abs_of_nonneg this.1, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact this.2
  · have := B_bounds N ω Q B h k hb hab
    rw [abs_of_nonneg this.1, abs_of_nonneg (by linarith)]
    exact this.2

/-- `Q_j(t) = Inc_j(t) − S_j(B_j(t))`. -/
lemma Q_formula {r : ℝ} (hr : 0 ≤ r) (j : Fin K) :
    Q r j = ((N.A j r ω : ℝ) + ∑ k, ∑ i ∈ Finset.range (N.S k (B r k) ω),
      routeVec (N.φ k i ω) j) - (N.S j (B r j) ω : ℝ) := by
  have := congrFun (h.2.2.2.2 r hr) j
  rw [this]
  simp only [Network.Avec, Pi.add_apply, Finset.sum_apply, Network.Shat, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

omit h in
lemma routeVec_nonneg (r : Fin (K + 1)) (j : Fin K) : 0 ≤ routeVec r j := by
  unfold routeVec; split_ifs <;> norm_num

variable (hU : ∀ k ∈ J, Tendsto (fun l => N.U k l ω) atTop atTop)
  (hV : ∀ k, Tendsto (fun l => N.V k l ω) atTop atTop)
include hU hV

lemma S_mono (k : Fin K) {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    N.S k b ω ≤ N.S k b' ω :=
  cnt_mono (F := fun l => N.V k l ω) (V_zero N k ω) (V_mono N k ω) (hV k) hb hbb

lemma A_mono (k : Fin K) {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    N.A k b ω ≤ N.A k b' ω := by
  unfold Network.A
  split_ifs with hk
  · exact cnt_mono (F := fun l => N.U k l ω) (U_zero N k ω) (U_mono N hk ω) (hU k hk) hb hbb
  · exact le_rfl

lemma Inc_mono (j : Fin K) {r r' : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r') :
    ((N.A j r ω : ℝ) + ∑ k, ∑ i ∈ Finset.range (N.S k (B r k) ω), routeVec (N.φ k i ω) j) ≤
    ((N.A j r' ω : ℝ) + ∑ k, ∑ i ∈ Finset.range (N.S k (B r' k) ω), routeVec (N.φ k i ω) j) := by
  refine add_le_add (Nat.cast_le.2 (A_mono N ω Q B h hU hV j hr hrr))
    (Finset.sum_le_sum fun k _ => ?_)
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ?_)
    (fun i _ _ => routeVec_nonneg _ _)
  exact S_mono N ω Q B h hU hV k (B_nonneg N ω Q B h k hr)
    (by linarith [(B_bounds N ω Q B h k hr hrr).1])

omit h hU hV in
lemma Inc_nat (j : Fin K) (r : ℝ) : ∃ n : ℕ,
    ((N.A j r ω : ℝ) + ∑ k, ∑ i ∈ Finset.range (N.S k (B r k) ω), routeVec (N.φ k i ω) j)
      = n :=
  ⟨N.A j r ω + ∑ k, ∑ i ∈ Finset.range (N.S k (B r k) ω),
      (if N.φ k i ω = j.succ then 1 else 0), by push_cast; simp only [routeVec]⟩

/-- the queue length is nonnegative. -/
lemma Q_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Q t := by
  intro j
  by_contra hneg; push Not at hneg
  simp only [Pi.zero_apply] at hneg
  have hf := Q_formula N ω Q B h ht j
  have hBt : 0 ≤ B t j := B_nonneg N ω Q B h j ht
  have hspec := cnt_spec (F := fun l => N.V j l ω) (V_zero N j ω) (V_mono N j ω) (hV j) hBt
  have hS : N.S j (B t j) ω = sSup {l | N.V j l ω ≤ B t j} := rfl
  rw [← hS] at hspec
  have hInc0 : 0 ≤ ((N.A j t ω : ℝ) + ∑ k, ∑ i ∈ Finset.range (N.S k (B t k) ω),
      routeVec (N.φ k i ω) j) := by
    obtain ⟨n, hn⟩ := Inc_nat N ω B j t; rw [hn]; exact Nat.cast_nonneg n
  obtain ⟨m', hm'⟩ : ∃ m', N.S j (B t j) ω = m' + 1 := by
    rcases Nat.eq_zero_or_pos (N.S j (B t j) ω) with h0 | h0
    · exfalso; rw [h0] at hf; simp only [Nat.cast_zero, sub_zero] at hf; linarith
    · exact ⟨N.S j (B t j) ω - 1, by omega⟩
  rw [hm'] at hspec hf
  set a := N.V j m' ω with ha
  set b := N.V j (m' + 1) ω with hb
  have hab : a < b := V_mono N j ω (Nat.lt_succ_self m')
  have ha0 : 0 ≤ a := by
    have : N.V j 0 ω ≤ N.V j m' ω := (V_mono N j ω).monotone (Nat.zero_le m')
    rw [V_zero] at this; exact this
  have hbB : b ≤ B t j := hspec.1
  have hBc : ContinuousOn (fun r => B r j) (Set.Icc 0 t) :=
    (B_cont N ω Q B h j).mono fun r hr => hr.1
  have hivt := intermediate_value_Icc ht hBc
  have hB0 : B 0 j = 0 := h.2.1 j
  obtain ⟨r1, hr1, e1⟩ := hivt (show (2 * a + b) / 3 ∈ Set.Icc (B 0 j) (B t j) from
    ⟨by rw [hB0]; linarith, by linarith⟩)
  obtain ⟨r2, hr2, e2⟩ := hivt (show (a + 2 * b) / 3 ∈ Set.Icc (B 0 j) (B t j) from
    ⟨by rw [hB0]; linarith, by linarith⟩)
  simp only at e1 e2
  have hr12 : r1 ≤ r2 := by
    by_contra hc; push Not at hc
    have := (B_bounds N ω Q B h j hr2.1 hc.le).1
    linarith
  have hex : ∃ r ∈ Set.Icc r1 r2, 0 < Q r j := by
    by_contra hc; push Not at hc
    have := B_flat N ω Q B h j hr1.1 hr12 hc
    linarith
  obtain ⟨r, hr, hQr⟩ := hex
  have hr0 : 0 ≤ r := hr1.1.trans hr.1
  have hrt : r ≤ t := hr.2.trans hr2.2
  have hBr1 := (B_bounds N ω Q B h j hr1.1 hr.1).1
  have hBr2 := (B_bounds N ω Q B h j hr0 hr.2).1
  have hSr : N.S j (B r j) ω = m' := by
    have hsp := cnt_spec (F := fun l => N.V j l ω) (V_zero N j ω) (V_mono N j ω) (hV j)
      (B_nonneg N ω Q B h j hr0)
    exact cnt_eq (F := fun l => N.V j l ω) (V_mono N j ω) (b := B r j)
      (show a ≤ B r j by linarith) (show B r j < b by linarith) hsp.1 hsp.2
  have hfr := Q_formula N ω Q B h hr0 j
  rw [hSr] at hfr
  obtain ⟨n, hn⟩ := Inc_nat N ω B j r
  rw [hn] at hfr
  have hQ1 : (m' : ℝ) + 1 ≤ n := by
    have : (m' : ℝ) < n := by linarith
    have : m' < n := by exact_mod_cast this
    have : m' + 1 ≤ n := this
    exact_mod_cast this
  have hmono := Inc_mono N ω Q B h hU hV j hr0 hrt
  rw [hn] at hmono
  push_cast at hf
  linarith

/-- the queue length is right continuous (locally constant from the right). -/
lemma Q_rc {t : ℝ} (ht : 0 ≤ t) : ContinuousWithinAt Q (Set.Ici t) t := by
  have hA : ∀ k, ∀ᶠ r in 𝓝[≥] t, N.A k r ω = N.A k t ω := by
    intro k
    unfold Network.A
    split_ifs with hk
    · filter_upwards [cnt_rc (F := fun l => N.U k l ω) (U_zero N k ω) (U_mono N hk ω)
        (hU k hk) ht] with r hr
      exact hr.2
    · exact Eventually.of_forall fun _ => rfl
  have hS : ∀ k, ∀ᶠ r in 𝓝[≥] t, N.S k (B r k) ω = N.S k (B t k) ω := by
    intro k
    have hBt := B_nonneg N ω Q B h k ht
    have hsp := cnt_spec (F := fun l => N.V k l ω) (V_zero N k ω) (V_mono N k ω) (hV k) hBt
    have hSk : N.S k (B t k) ω = sSup {l | N.V k l ω ≤ B t k} := rfl
    rw [← hSk] at hsp
    set η := N.V k (N.S k (B t k) ω + 1) ω - B t k with hη
    have hηpos : 0 < η := by simp only [hη]; linarith [hsp.2]
    filter_upwards [Ico_mem_nhdsGE (show t < t + η by linarith)] with r hr
    have hb := B_bounds N ω Q B h k ht hr.1
    have hsp' := cnt_spec (F := fun l => N.V k l ω) (V_zero N k ω) (V_mono N k ω) (hV k)
      (B_nonneg N ω Q B h k (ht.trans hr.1))
    exact cnt_eq (F := fun l => N.V k l ω) (V_mono N k ω) (b := B r k)
      (hsp.1.trans (by linarith)) (by linarith [hr.2]) hsp'.1 hsp'.2
  have hev : ∀ᶠ r in 𝓝[≥] t, Q r = Q t := by
    filter_upwards [eventually_all.2 hA, eventually_all.2 hS, self_mem_nhdsWithin]
      with r hAr hSr (hr : t ≤ r)
    rw [h.2.2.2.2 r (ht.trans hr), h.2.2.2.2 t ht]
    congr 1
    · funext k; simp only [Network.Avec, hAr k]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Network.Shat, hSr k]
  exact tendsto_const_nhds.congr' (hev.mono fun r hr => hr.symm)

end Net

/-! ### Assembly helpers -/

section Assembly

open Reiman84.QueueLength

lemma Phi_of_IRP {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (w : Wt P)
    {x y z : ℝ → Fin K → ℝ} (h : IsReflectionPair P x y z) :
    Phi P (onUnit x) = onUnit z := by
  obtain ⟨-, hyc, hzc, hxyz, hz, ⟨hym, hy0⟩, hcomp⟩ := h
  funext t
  exact Phi_of_compl hP0 w (fun s hs => hxyz s hs.1) (hyc.mono fun s hs => hs.1)
    (hym.mono fun s hs => hs.1) hy0 (fun s hs => hz s hs.1)
    (fun s hs => (hzc s hs.1).mono fun r hr => hs.1.trans hr.1)
    (fun j s t hs hst _ hall => hcomp j s t hs hst hall) t

variable {J : Finset (Fin K)} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}

lemma routing_nonneg (N : Network K J μP) : ∀ i j, 0 ≤ N.routing i j :=
  fun _ _ => measureReal_nonneg

lemma integral_pos_of_pos' [IsProbabilityMeasure μP] {f : Ω → ℝ} (hf : ∀ ω, 0 < f ω)
    (hint : Integrable f μP) : 0 < ∫ ω, f ω ∂μP := by
  rw [integral_pos_iff_support_of_nonneg (fun ω => (hf ω).le) hint]
  have : Function.support f = Set.univ := Set.eq_univ_of_forall fun ω => (hf ω).ne'
  rw [this, measure_univ]; exact one_pos

lemma mu_pos (N : Network K J μP) (k : Fin K) : 0 < N.mu k := by
  have := N.isProb
  exact inv_pos.2 (integral_pos_of_pos' (N.pos_v k 0) ((N.memLp_v k).integrable one_le_two))

lemma eq13 (N : Network K J μP) (ω : Ω) (Q B : ℝ → Fin K → ℝ) (h : N.IsQueueSolution ω Q B) :
    ∀ t, 0 ≤ t → Q t = N.Xtilde B t ω + Matrix.vecMul (N.Y B t) (1 - N.routing) := by
  intro t ht
  have h3 := h.2.2.2.2 t ht
  rw [h3, show (1 - N.routing) = -(N.routing - 1) from (neg_sub _ _).symm]
  funext j
  simp only [Network.Xtilde, Network.Atilde, Network.Stilde, Network.eta]
  generalize N.routing - 1 = M
  simp only [Matrix.vecMul, dotProduct, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Matrix.neg_apply, Finset.sum_apply, smul_eq_mul, mul_neg, Finset.sum_neg_distrib]
  have h1 : ∑ c, (N.Shat c (B t c) ω j - N.mu c * B t c * M c j)
      = ∑ c, N.Shat c (B t c) ω j - ∑ c, N.mu c * B t c * M c j := Finset.sum_sub_distrib ..
  have h2 : ∑ i, N.Y B t i * M i j
      = t * ∑ i, N.mu i * M i j - ∑ i, N.mu i * B t i * M i j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by
      show N.mu i * (t - B t i) * M i j = t * (N.mu i * M i j) - N.mu i * B t i * M i j
      ring)
  linarith [h1, h2]

/-- one network: the scaled queue is the reflection of the scaled netput. -/
lemma net_Phi (N : Network K J μP) (ω : Ω) (Q B : ℝ → Fin K → ℝ)
    (h : N.IsQueueSolution ω Q B)
    (hU : ∀ k ∈ J, Tendsto (fun l => N.U k l ω) atTop atTop)
    (hV : ∀ k, Tendsto (fun l => N.V k l ω) atTop atTop)
    {R : Matrix (Fin K) (Fin K) ℝ} (hR : N.routing = R) (w : Wt R) {n : ℕ} (hn : 1 ≤ n) :
    Phi R (onUnit (diffScale n (fun t => N.Xtilde B t ω))) = onUnit (diffScale n Q) := by
  funext t
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hcpos : 0 < (Real.sqrt n)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hnpos)
  have hmu := mu_pos N
  have hP0 : ∀ i j, 0 ≤ R i j := hR ▸ routing_nonneg N
  have hns : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ (n:ℝ) * s := fun s hs => mul_nonneg hnpos.le hs.1
  have hYc : ContinuousOn (fun r => N.Y B r) (Set.Ici 0) := by
    refine continuousOn_pi.2 fun k => ?_
    simp only [Network.Y, Network.idle]
    exact continuousOn_const.mul (continuousOn_id.sub (B_cont N ω Q B h k))
  refine Phi_of_compl hP0 w (y := diffScale n (N.Y B)) (fun s hs => ?_) ?_ ?_ ?_ (fun s hs => ?_)
    (fun s hs => ?_) (fun j s t hs hst ht hall => ?_) t
  · simp only [diffScale]
    rw [eq13 N ω Q B h _ (hns s hs), hR, smul_add, Matrix.smul_vecMul]
  · show ContinuousOn (fun t => (Real.sqrt n)⁻¹ • N.Y B (n * t)) (Set.Icc 0 1)
    exact (hYc.comp (continuousOn_const.mul continuousOn_id)
      fun s hs => hns s hs).const_smul ((Real.sqrt n)⁻¹)
  · intro a ha b hb hab k
    simp only [diffScale, Pi.smul_apply, smul_eq_mul, Network.Y, Network.idle]
    have hb' := B_bounds N ω Q B h k (hns a ha) (mul_le_mul_of_nonneg_left hab hnpos.le)
    apply mul_le_mul_of_nonneg_left _ hcpos.le
    apply mul_le_mul_of_nonneg_left _ (hmu k).le
    nlinarith [hb'.2]
  · funext k; simp [diffScale, Network.Y, Network.idle, h.2.1 k]
  · simp only [diffScale]
    exact smul_nonneg hcpos.le (Q_nonneg N ω Q B h hU hV (hns s hs))
  · show ContinuousWithinAt (fun t => (Real.sqrt n)⁻¹ • Q (n * t)) (Set.Icc s 1) s
    have hq : ContinuousWithinAt (fun t => Q (n * t)) (Set.Icc s 1) s :=
      (Q_rc N ω Q B h hU hV (mul_nonneg hnpos.le hs.1)).comp
        ((continuous_const.mul continuous_id).continuousWithinAt)
        (fun r hr => mul_le_mul_of_nonneg_left hr.1 hnpos.le)
    exact hq.const_smul ((Real.sqrt n)⁻¹)
  · simp only [diffScale, Pi.smul_apply, smul_eq_mul, Network.Y, Network.idle]
    have hpos : ∀ r ∈ Set.Icc ((n:ℝ) * s) (n * t), 0 < Q r j := by
      intro r hr
      have := hall (r / n) ⟨by rw [le_div_iff₀ hnpos]; linarith [hr.1],
        by rw [div_le_iff₀ hnpos]; linarith [hr.2]⟩
      have e : (n:ℝ) * (r / n) = r := by field_simp
      simp only [diffScale, Pi.smul_apply, smul_eq_mul, e] at this
      exact lt_of_mul_lt_mul_left (by rwa [mul_zero]) hcpos.le
    have := B_full N ω Q B h j (mul_nonneg hnpos.le hs) (mul_le_mul_of_nonneg_left hst hnpos.le)
      hpos
    congr 2
    linarith

lemma tendsto_atTop_of_avg {S : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (h : Tendsto (fun n : ℕ => S n / n) atTop (𝓝 a)) : Tendsto S atTop atTop := by
  have hev : ∀ᶠ n : ℕ in atTop, a / 2 < S n / n := h.eventually (lt_mem_nhds (by linarith))
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith : (0:ℝ) < a / 2))
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have : (0:ℝ) < n := by exact_mod_cast hn0
  rw [lt_div_iff₀ this] at hn
  linarith

lemma ae_V (N : Network K J μP) (k : Fin K) :
    ∀ᵐ ω ∂μP, Tendsto (fun l => N.V k l ω) atTop atTop := by
  have := N.isProb
  have hint : Integrable (N.v k 0) μP := (N.memLp_v k).integrable one_le_two
  have hind : Pairwise (fun i i' => ProbabilityTheory.IndepFun (N.v k i) (N.v k i') μP) := by
    intro i i' hii
    exact N.indep.indep (i := Sum.inr (Sum.inl (k, i))) (j := Sum.inr (Sum.inl (k, i')))
      (by simp [hii])
  have hpos : 0 < ∫ ω, N.v k 0 ω ∂μP := integral_pos_of_pos' (N.pos_v k 0) hint
  filter_upwards [ProbabilityTheory.strong_law_ae_real (fun i => N.v k i) hint hind (N.ident_v k)] with ω hω
  exact tendsto_atTop_of_avg hpos hω

lemma ae_U (N : Network K J μP) {k : Fin K} (hk : k ∈ J) :
    ∀ᵐ ω ∂μP, Tendsto (fun l => N.U k l ω) atTop atTop := by
  have := N.isProb
  have hint : Integrable (N.u k 0) μP := (N.memLp_u k hk).integrable one_le_two
  have hind : Pairwise (fun i i' => ProbabilityTheory.IndepFun (N.u k i) (N.u k i') μP) := by
    intro i i' hii
    exact N.indep.indep (i := Sum.inl (⟨k, hk⟩, i)) (j := Sum.inl (⟨k, hk⟩, i'))
      (by simp [hii])
  have hpos : 0 < ∫ ω, N.u k 0 ω ∂μP := integral_pos_of_pos' (N.pos_u k hk 0) hint
  filter_upwards [ProbabilityTheory.strong_law_ae_real (fun i => N.u k i) hint hind (N.ident_u k hk)] with ω hω
  exact tendsto_atTop_of_avg hpos hω

lemma ae_good (N : Network K J μP) :
    ∀ᵐ ω ∂μP, (∀ k ∈ J, Tendsto (fun l => N.U k l ω) atTop atTop) ∧
      (∀ k, Tendsto (fun l => N.V k l ω) atTop atTop) := by
  have h1 : ∀ᵐ ω ∂μP, ∀ k, k ∈ J → Tendsto (fun l => N.U k l ω) atTop atTop :=
    ae_all_iff.2 fun k => by
      by_cases hk : k ∈ J
      · filter_upwards [ae_U N hk] with ω hω _ using hω
      · exact Eventually.of_forall fun ω hk' => absurd hk' hk
  have h2 := ae_all_iff.2 fun k => ae_V N k
  filter_upwards [h1, h2] with ω h1 h2 using ⟨h1, h2⟩

end Assembly

/-- Theorem 1 from Proposition 5 (given as the hypothesis `h5`). -/
theorem main_glue {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    (net : ∀ n, Reiman84.QueueLength.Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : Reiman84.QueueLength.HeavyTrafficAssumptions net R mu s lam a c)
    (Q B : ∀ n, Ω n → ℝ → Fin K → ℝ)
    (hQ : ∀ n, ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (ξ Z : Ω' → ℝ → Fin K → ℝ)
    (hξ : Reiman84.QueueLength.IsDriftedBM c (Reiman84.QueueLength.covA lam a mu s R) P' ξ)
    (hZ : ∀ ω, ∃ y, Reiman84.QueueLength.IsReflectionPair R (ξ ω) y (Z ω))
    (h5 : Reiman84.QueueLength.WeakConvD P
      (fun n ω => Reiman84.QueueLength.diffScale n (fun t => (net n).Xtilde (B n ω) t ω)) P' ξ) :
    Reiman84.QueueLength.WeakConvD P
      (fun n ω => Reiman84.QueueLength.diffScale n (Q n ω)) P' Z := by
  obtain ⟨Ω₀, mΩ₀, Q₀, Y, Y', hprob, hYm, hY'm, hlaw, hlaw', hconv⟩ := h5
  have hR : ∀ n, (net n).routing = R := hA.1
  have hP0 : ∀ i j, 0 ≤ R i j := hR 0 ▸ routing_nonneg (net 0)
  have hPm : Tendsto (fun m : ℕ => R ^ m) atTop (𝓝 0) := hR 0 ▸ (net 0).spectral
  obtain ⟨w⟩ := wt_exists hP0 hPm
  have hΦ := Phi_meas R (K := K)
  refine ⟨Ω₀, mΩ₀, Q₀, fun n ω => Phi R (Y n ω), fun ω => Phi R (Y' ω), hprob,
    fun n => hΦ.comp (hYm n), hΦ.comp hY'm, ?_, ?_, ?_⟩
  · filter_upwards [hlaw, eventually_ge_atTop 1] with n hn hn1
    have e1 : Q₀.map (fun ω => Phi R (Y n ω)) = (Q₀.map (Y n)).map (Phi R) :=
      (Measure.map_map hΦ (hYm n)).symm
    have hfae : AEMeasurable (fun ω => Reiman84.QueueLength.onUnit
        (Reiman84.QueueLength.diffScale n (fun t => (net n).Xtilde (B n ω) t ω))) (P n) := by
      by_contra hnot
      have h0 := Measure.map_of_not_aemeasurable hnot
      haveI := hprob
      have h1 : (Q₀.map (Y n)) Set.univ = 1 := by
        rw [Measure.map_apply (hYm n) MeasurableSet.univ]; simp
      rw [hn, h0] at h1; simp at h1
    rw [e1, hn, AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hfae]
    refine Measure.map_congr ?_
    filter_upwards [hQ n, ae_good (net n)] with ω hω hg
    exact net_Phi (net n) ω (Q n ω) (B n ω) hω hg.1 hg.2 (hR n) w hn1
  · have e2 : Q₀.map (fun ω => Phi R (Y' ω)) = (Q₀.map Y').map (Phi R) :=
      (Measure.map_map hΦ hY'm).symm
    have hξm : Measurable fun ω => Reiman84.QueueLength.onUnit (ξ ω) :=
      measurable_pi_lambda _ fun t => hξ.2.1 _
    rw [e2, hlaw', Measure.map_map hΦ hξm]
    congr 1
    funext ω
    obtain ⟨y, hy⟩ := hZ ω
    exact Phi_of_IRP hP0 w hy
  · filter_upwards [hconv] with ω hω
    exact Phi_skorohod hP0 w hω

end A76

open Filter Topology MeasureTheory Reiman84.QueueLength in
theorem solution {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c)
    (Q B : ∀ n, Ω n → ℝ → Fin K → ℝ)
    (hQ : ∀ n, ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (ξ Z : Ω' → ℝ → Fin K → ℝ)
    (hξ : IsDriftedBM c (covA lam a mu s R) P' ξ)
    (hZ : ∀ ω, ∃ y, IsReflectionPair R (ξ ω) y (Z ω)) :
    WeakConvD P (fun n ω => diffScale n (Q n ω)) P' Z := by
  exact A76.main_glue net R mu s lam a c hA Q B hQ P' ξ Z hξ hZ
    (Reiman84.QueueLength.proposition_5 net R mu s lam a c hA Q B hQ P' ξ hξ)
