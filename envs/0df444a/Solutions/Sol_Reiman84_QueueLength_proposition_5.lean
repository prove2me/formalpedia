-- Prove2me | solution 1 for Reiman84.QueueLength.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T13:41:37.629669+00:00
-- url     : https://prove2.me/submissions/6dba494c-cdb5-49e1-b55a-3c749951a3c8

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic
import Theorems.Thm_Reiman84_QueueLength_weakConvD_of_fdd_and_modulus
import Theorems.Thm_Reiman84_QueueLength_scaled_netput_fdd_convergence
import Theorems.Thm_Reiman84_QueueLength_primitive_netput_modulus_tight
import Theorems.Thm_Reiman84_QueueLength_scaled_netput_measurable_cadlag
import Theorems.Thm_Reiman84_QueueLength_proposition_4

set_option autoImplicit false

/-! Reduction of Reiman (1984) Proposition 5 (755ffe80) to five children: the weak-convergence
criterion `weakConvD_of_fdd_and_modulus`, the fdd convergence of the netput
`scaled_netput_fdd_convergence`, the tightness of the primitive processes
`primitive_netput_modulus_tight`, the measurability of the scaled netputs
`scaled_netput_measurable_cadlag`, and the sibling `proposition_4`. -/
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

end A76

namespace P5

open Filter Topology MeasureTheory Reiman84.QueueLength

/-- Finite-dimensional convergence on `[0,1]`, tested against bounded Lipschitz functions. -/
def FddConv {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (X : ∀ n, Ω n → ℝ → Fin K → ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (X' : Ω' → ℝ → Fin K → ℝ) : Prop :=
  ∀ (m : ℕ) (τ : Fin m → ℝ), (∀ i, τ i ∈ Set.Icc (0:ℝ) 1) →
    ∀ (f : (Fin m → Fin K → ℝ) → ℝ), (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      (∃ L : NNReal, LipschitzWith L f) →
      Tendsto (fun n => ∫ ω, f (fun i => X n ω (τ i)) ∂(P n)) atTop
        (𝓝 (∫ ω, f (fun i => X' ω (τ i)) ∂P'))

/-- Modulus-of-continuity tightness on `[0,1]` (outer measure of the bad set). -/
def ModTight {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (X : ∀ n, Ω n → ℝ → Fin K → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
    P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
      ε ≤ ‖X n ω s - X n ω t‖} ≤ ENNReal.ofReal η

/-- a.e.-measurable (path-space product σ-algebra) and a.s. cadlag on `[0,1]`. -/
def AECadlagMeas {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (X : ∀ n, Ω n → ℝ → Fin K → ℝ) : Prop :=
  ∀ n, AEMeasurable (fun ω => onUnit (X n ω)) (P n) ∧ ∀ᵐ ω ∂(P n), IsCadlag01 (X n ω)

/-- CHILD C_R (Billingsley 1999, Thm 7.5 + Thm 6.7; continuous limit): fdd convergence plus
modulus tightness give the coupling form of weak convergence in `D`. -/
def RepThm : Prop :=
  ∀ (K : ℕ) (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (X : ∀ n, Ω n → ℝ → Fin K → ℝ) (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
    (X' : Ω' → ℝ → Fin K → ℝ),
    (∀ n, IsProbabilityMeasure (P n)) → IsProbabilityMeasure P' →
    AECadlagMeas P X → (∀ t, Measurable fun ω => X' ω t) →
    (∀ ω, ContinuousOn (X' ω) (Set.Icc 0 1)) →
    FddConv P X P' X' → ModTight P X → WeakConvD P X P' X'

/-- The scaled netput `ζⁿ` (deterministic time, Prop 3). -/
noncomputable def zeta {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n)) : ∀ n, Ω n → ℝ → Fin K → ℝ :=
  fun n ω => diffScale n (fun t => (net n).X t ω)

/-- The scaled centred netput `ζ̃ⁿ` (time-changed by `Bⁿ`, Prop 5). -/
noncomputable def zetaT {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n)) (B : ∀ n, Ω n → ℝ → Fin K → ℝ) :
    ∀ n, Ω n → ℝ → Fin K → ℝ :=
  fun n ω => diffScale n (fun t => (net n).Xtilde (B n ω) t ω)

/-- CHILD C_fdd0 (Reiman Lemmas 3–5 / Prop 3, fdd part): `ζⁿ` fdd-converges to `ζ`. -/
def FddNetput : Prop :=
  ∀ (K : ℕ) (J : Finset (Fin K)) (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ),
    HeavyTrafficAssumptions net R mu s lam a c →
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (ζ : Ω' → ℝ → Fin K → ℝ),
    IsDriftedBM c (covA lam a mu s R) P' ζ → FddConv P (zeta net) P' ζ

/-- CHILD C_tight0 (Reiman Lemmas 3–5, tightness part; Billingsley Thm 14.6 / 8.4):
the scaled centred arrival process and every scaled centred service-routing process are
modulus-tight on `[0,1]`. -/
def TightPrim : Prop :=
  ∀ (K : ℕ) (J : Finset (Fin K)) (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ),
    HeavyTrafficAssumptions net R mu s lam a c →
    ModTight P (fun n ω => diffScale n (fun t => (net n).Atilde t ω)) ∧
    ∀ k : Fin K, ModTight P (fun n ω => diffScale n (fun t => (net n).Stilde k t ω))

/-- CHILD C_meas (Reiman §2, p. 443; needs `queue_equations_exists_unique`): the time-changed
scaled netput is a.e.-measurable as a random path and a.s. cadlag on `[0,1]`. -/
def MeasNetputT : Prop :=
  ∀ (K : ℕ) (J : Finset (Fin K)) (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (net : ∀ n, Network K J (P n))
    (Q B : ∀ n, Ω n → ℝ → Fin K → ℝ),
    (∀ n, ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω)) →
    AECadlagMeas P (zeta net) ∧ AECadlagMeas P (zetaT net B)

/-- Existing sibling Proposition 4 (366195cb), restated verbatim as a `Prop`. -/
def Prop4 : Prop :=
  ∀ (K : ℕ) (J : Finset (Fin K)) (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ),
    HeavyTrafficAssumptions net R mu s lam a c →
    ∀ (Q B : ∀ n, Ω n → ℝ → Fin K → ℝ),
    (∀ n, ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω)) →
    ∀ k : Fin K, ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => P n {ω | δ ≤ |(n : ℝ)⁻¹ * Network.idle (B n ω) n k|})
        atTop (𝓝 0)

/-! ### Glue lemmas (proved) -/

/-- `X̃(t) − X(t) = ∑ₖ (S̃ₖ(Bₖ(t)) − S̃ₖ(t))`: the only difference between the time-changed
centred netput and the plain netput. -/
lemma Xtilde_sub_X {K : ℕ} {J : Finset (Fin K)} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (N : Network K J P) (B : ℝ → Fin K → ℝ) (t : ℝ) (ω : Ω) :
    N.Xtilde B t ω - N.X t ω = ∑ k, (N.Stilde k (B t k) ω - N.Stilde k t ω) := by
  ext j
  simp only [Network.Xtilde, Network.X, Network.Atilde, Network.Stilde, Network.eta,
    Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, Matrix.vecMul, dotProduct]
  have : ∀ k : Fin K, (N.mu k * t) * (N.routing - 1) k j = t * (N.mu k * (N.routing - 1) k j) :=
    fun k => by ring
  simp only [this, ← Finset.mul_sum]
  ring

section Glue

variable {K : ℕ} {J : Finset (Fin K)}

lemma ind_ii (Q : ℝ → Fin K → ℝ) (k : Fin K) (hQ : Measurable fun s => Q s k)
    (a b : ℝ) : IntervalIntegrable (fun s => if 0 < Q s k then (1:ℝ) else 0) volume a b := by
  refine ((show Continuous (fun _ : ℝ => (1:ℝ)) from continuous_const).intervalIntegrable a b).mono_fun
    ?_ (ae_of_all _ fun s => ?_)
  · exact (Measurable.ite (measurableSet_lt measurable_const hQ) measurable_const
      measurable_const).aestronglyMeasurable
  · simp only [Real.norm_eq_abs]; split_ifs <;> norm_num

lemma B_bounds {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP) (ω : Ω)
    (Q B : ℝ → Fin K → ℝ) (h : N.IsQueueSolution ω Q B) (k : Fin K) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) : 0 ≤ B t k - B s k ∧ B t k - B s k ≤ t - s := by
  have hd : B t k - B s k = ∫ r in s..t, (if 0 < Q r k then (1:ℝ) else 0) := by
    rw [h.2.2.2.1 k t (hs.trans hst), h.2.2.2.1 k s hs]
    exact intervalIntegral.integral_interval_sub_left
      (ind_ii Q k (h.2.2.1 k) 0 t) (ind_ii Q k (h.2.2.1 k) 0 s)
  rw [hd]
  constructor
  · exact intervalIntegral.integral_nonneg hst fun u _ => by split_ifs <;> norm_num
  · have := intervalIntegral.integral_mono_on hst
      (ind_ii Q k (h.2.2.1 k) s t)
      ((show Continuous (fun _ : ℝ => (1:ℝ)) from continuous_const).intervalIntegrable s t)
      (fun u _ => by split_ifs <;> norm_num)
    simpa using this

/-- The time change `Bₖ(nt)/n` stays in `[0,1]` and is within `n⁻¹ Iₖ(n)` of `t`. -/
lemma timechange_bound {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP)
    (ω : Ω) (Q B : ℝ → Fin K → ℝ) (h : N.IsQueueSolution ω Q B) (n : ℕ) (hn : 0 < n)
    (k : Fin K) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    B (n * t) k / n ∈ Set.Icc (0:ℝ) 1 ∧
      |B (n * t) k / n - t| ≤ |(n:ℝ)⁻¹ * Network.idle B n k| := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hnt0 : 0 ≤ (n:ℝ) * t := mul_nonneg hn'.le ht.1
  have hnt1 : (n:ℝ) * t ≤ n := by nlinarith [ht.2]
  have h1 := B_bounds N ω Q B h k le_rfl hnt0
  have h2 := B_bounds N ω Q B h k hnt0 hnt1
  rw [h.2.1 k, sub_zero] at h1
  set b := B (n * t) k
  have hid : Network.idle B n k = n - B n k := rfl
  have hI0 : 0 ≤ (n:ℝ)⁻¹ * Network.idle B n k := by
    rw [hid]; exact mul_nonneg (inv_nonneg.2 hn'.le) (by linarith)
  have eb : b / n = (n:ℝ)⁻¹ * b := div_eq_inv_mul b n
  have et : t = (n:ℝ)⁻¹ * (n * t) := by field_simp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [eb]; exact mul_nonneg (inv_nonneg.2 hn'.le) h1.1
  · rw [div_le_one hn']; linarith
  · rw [abs_of_nonneg hI0, abs_sub_comm, eb]
    have : t - (n:ℝ)⁻¹ * b = (n:ℝ)⁻¹ * (n * t - b) := by rw [mul_sub, ← et]
    rw [this, hid, abs_of_nonneg (mul_nonneg (inv_nonneg.2 hn'.le) (by linarith))]
    exact mul_le_mul_of_nonneg_left (by linarith : (n:ℝ) * t - b ≤ n - B n k)
      (inv_nonneg.2 hn'.le)

lemma zetaT_sub_zeta {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
    (net : ∀ n, Network K J (P n)) (B : ∀ n, Ω n → ℝ → Fin K → ℝ) (n : ℕ) (hn : 0 < n)
    (ω : Ω n) (t : ℝ) :
    zetaT net B n ω t - zeta net n ω t = ∑ k, (diffScale n (fun r => (net n).Stilde k r ω)
      (B n ω (n * t) k / n) - diffScale n (fun r => (net n).Stilde k r ω) t) := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [zetaT, zeta, diffScale]
  rw [← smul_sub, Xtilde_sub_X, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_sub]
  congr 3
  field_simp

end Glue

section Close

variable {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)}

/-- `sup_{t ≤ 1} ‖ζ̃ⁿ(t) − ζⁿ(t)‖ → 0` in (outer) probability, from tightness of the scaled
service-routing processes and Proposition 4 (`n⁻¹ Iₖ(n) → 0`). -/
lemma close (net : ∀ n, Network K J (P n)) (Q B : ∀ n, Ω n → ℝ → Fin K → ℝ)
    (hQ : ∀ n, ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω))
    (hS : ∀ k, ModTight P (fun n ω => diffScale n (fun t => (net n).Stilde k t ω)))
    (h4 : ∀ k : Fin K, ∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ =>
      P n {ω | δ ≤ |(n : ℝ)⁻¹ * Network.idle (B n ω) n k|}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, P n {ω | ∃ t ∈ Set.Icc (0:ℝ) 1,
      ε ≤ ‖zetaT net B n ω t - zeta net n ω t‖} ≤ ENNReal.ofReal η := by
  rcases (Finset.univ (α := Fin K)).eq_empty_or_nonempty with hK | hK
  · refine Filter.Eventually.of_forall fun n => ?_
    have hE : IsEmpty (Fin K) := ⟨fun i => by simpa [hK] using Finset.mem_univ i⟩
    have : {ω | ∃ t ∈ Set.Icc (0:ℝ) 1, ε ≤ ‖zetaT net B n ω t - zeta net n ω t‖} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
        not_le]
      intro t _
      rw [Subsingleton.elim (zetaT net B n ω t - zeta net n ω t) 0, norm_zero]; exact hε
    rw [this, measure_empty]; exact bot_le
  have hK0 : 0 < K := Fin.pos_iff_nonempty.2 (Finset.univ_nonempty_iff.1 hK)
  have hKr : (0:ℝ) < K := by exact_mod_cast hK0
  set ε' := ε / K with hε'
  set η' := η / (2 * K) with hη'
  have hε'0 : 0 < ε' := div_pos hε hKr
  have hη'0 : 0 < η' := div_pos hη (by linarith)
  choose δk hδk Nk hNk using fun k => hS k ε' hε'0 η' hη'0
  set δ := Finset.univ.inf' hK δk with hδdef
  have hδpos : 0 < δ := (Finset.lt_inf'_iff hK).2 fun k _ => hδk k
  have hδle : ∀ k, δ ≤ δk k := fun k => Finset.inf'_le _ (Finset.mem_univ k)
  have hev : ∀ᶠ n in atTop, ∀ k, P n {ω | δ ≤ |(n : ℝ)⁻¹ * Network.idle (B n ω) n k|}
      ≤ ENNReal.ofReal η' := by
    rw [Filter.eventually_all]; intro k
    exact (h4 k δ hδpos).eventually (Iic_mem_nhds (ENNReal.ofReal_pos.2 hη'0))
  have hevN : ∀ᶠ n in atTop, ∀ k, Nk k ≤ n :=
    Filter.eventually_all.2 fun k => Filter.eventually_ge_atTop _
  filter_upwards [hev, hevN, Filter.eventually_gt_atTop 0] with n hn1 hn2 hn3
  have hsub : {ω | ∃ t ∈ Set.Icc (0:ℝ) 1, ε ≤ ‖zetaT net B n ω t - zeta net n ω t‖} ⊆
      {ω | ¬ (net n).IsQueueSolution ω (Q n ω) (B n ω)} ∪
      ⋃ k, ({ω | δ ≤ |(n : ℝ)⁻¹ * Network.idle (B n ω) n k|} ∪
        {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δk k ∧
          ε' ≤ ‖diffScale n (fun t => (net n).Stilde k t ω) s -
            diffScale n (fun t => (net n).Stilde k t ω) t‖}) := by
    rintro ω ⟨t, ht, hle⟩
    by_cases hsol : (net n).IsQueueSolution ω (Q n ω) (B n ω)
    · right
      rw [zetaT_sub_zeta net B n hn3 ω t] at hle
      obtain ⟨k, hk⟩ : ∃ k, ε' ≤ ‖diffScale n (fun r => (net n).Stilde k r ω)
          (B n ω (n * t) k / n) - diffScale n (fun r => (net n).Stilde k r ω) t‖ := by
        by_contra hcon
        push_neg at hcon
        have h1 := norm_sum_le (Finset.univ : Finset (Fin K)) (fun k =>
          diffScale n (fun r => (net n).Stilde k r ω) (B n ω (n * t) k / n) -
            diffScale n (fun r => (net n).Stilde k r ω) t)
        have h2 := Finset.sum_lt_sum_of_nonempty hK fun k (_ : k ∈ Finset.univ) => hcon k
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hε'] at h2
        have h3 : (K:ℝ) * (ε / K) = ε := by field_simp
        linarith
      refine Set.mem_iUnion.2 ⟨k, ?_⟩
      by_cases hi : δ ≤ |(n:ℝ)⁻¹ * Network.idle (B n ω) n k|
      · left; exact hi
      · right
        push_neg at hi
        obtain ⟨hm, hd⟩ := timechange_bound (net n) ω (Q n ω) (B n ω) hsol n hn3 k ht
        exact ⟨_, hm, t, ht, (hd.trans hi.le).trans (hδle k), hk⟩
    · left; exact hsol
  calc P n {ω | ∃ t ∈ Set.Icc (0:ℝ) 1, ε ≤ ‖zetaT net B n ω t - zeta net n ω t‖}
      ≤ P n ({ω | ¬ (net n).IsQueueSolution ω (Q n ω) (B n ω)} ∪
      ⋃ k, ({ω | δ ≤ |(n : ℝ)⁻¹ * Network.idle (B n ω) n k|} ∪
        {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δk k ∧
          ε' ≤ ‖diffScale n (fun t => (net n).Stilde k t ω) s -
            diffScale n (fun t => (net n).Stilde k t ω) t‖})) := measure_mono hsub
    _ ≤ P n {ω | ¬ (net n).IsQueueSolution ω (Q n ω) (B n ω)} +
        ∑ k, (P n {ω | δ ≤ |(n : ℝ)⁻¹ * Network.idle (B n ω) n k|} +
          P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δk k ∧
          ε' ≤ ‖diffScale n (fun t => (net n).Stilde k t ω) s -
            diffScale n (fun t => (net n).Stilde k t ω) t‖}) :=
        (measure_union_le _ _).trans (add_le_add le_rfl ((measure_iUnion_fintype_le _ _).trans
          (Finset.sum_le_sum fun k _ => measure_union_le _ _)))
    _ ≤ 0 + ∑ _k : Fin K, (ENNReal.ofReal η' + ENNReal.ofReal η') :=
        add_le_add (le_of_eq (ae_iff.1 (hQ n)))
          (Finset.sum_le_sum fun k _ => add_le_add (hn1 k) (hNk k n (hn2 k)))
    _ = ENNReal.ofReal η := by
        rw [zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← ENNReal.ofReal_add hη'0.le hη'0.le, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        rw [hη']; field_simp; ring

end Close

section Tight

variable {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}

lemma ModTight.zero : ModTight P (fun _ _ _ => (0 : Fin K → ℝ)) := by
  intro ε hε η hη
  refine ⟨1, one_pos, 0, fun n _ => ?_⟩
  refine le_trans (measure_mono (show _ ⊆ (∅ : Set (Ω n)) from ?_)) (by rw [measure_empty]; exact bot_le)
  rintro ω ⟨s, -, t, -, -, hle⟩
  simp only [sub_self, norm_zero] at hle
  exact absurd hle (not_le.2 hε)

lemma ModTight.add {X Y : ∀ n, Ω n → ℝ → Fin K → ℝ} (hX : ModTight P X) (hY : ModTight P Y) :
    ModTight P (fun n ω t => X n ω t + Y n ω t) := by
  intro ε hε η hη
  obtain ⟨δ1, hδ1, N1, hN1⟩ := hX (ε/2) (by linarith) (η/2) (by linarith)
  obtain ⟨δ2, hδ2, N2, hN2⟩ := hY (ε/2) (by linarith) (η/2) (by linarith)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, max N1 N2, fun n hn => ?_⟩
  have hsub : {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ min δ1 δ2 ∧
      ε ≤ ‖(X n ω s + Y n ω s) - (X n ω t + Y n ω t)‖} ⊆
      {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ1 ∧
        ε/2 ≤ ‖X n ω s - X n ω t‖} ∪
      {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ2 ∧
        ε/2 ≤ ‖Y n ω s - Y n ω t‖} := by
    rintro ω ⟨s, hs, t, ht, hst, hle⟩
    have htri : ‖(X n ω s + Y n ω s) - (X n ω t + Y n ω t)‖ ≤
        ‖X n ω s - X n ω t‖ + ‖Y n ω s - Y n ω t‖ := by
      rw [add_sub_add_comm]; exact norm_add_le _ _
    by_cases h1 : ε/2 ≤ ‖X n ω s - X n ω t‖
    · left; exact ⟨s, hs, t, ht, hst.trans (min_le_left _ _), h1⟩
    · right
      refine ⟨s, hs, t, ht, hst.trans (min_le_right _ _), ?_⟩
      push_neg at h1; linarith
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) :=
        add_le_add (hN1 n (le_of_max_le_left hn)) (hN2 n (le_of_max_le_right hn))
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

lemma ModTight.sum {ι : Type} (S : Finset ι) (Y : ι → ∀ n, Ω n → ℝ → Fin K → ℝ)
    (h : ∀ i ∈ S, ModTight P (Y i)) : ModTight P (fun n ω t => ∑ i ∈ S, Y i n ω t) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (ModTight.zero (P := P) (K := K))
  | @insert a S ha ih =>
    have e : (fun n ω t => ∑ i ∈ insert a S, Y i n ω t) =
        (fun n (ω : Ω n) t => Y a n ω t + ∑ i ∈ S, Y i n ω t) := by
      funext n ω t; rw [Finset.sum_insert ha]
    rw [e]
    exact (h a (Finset.mem_insert_self a S)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma ModTight.drift (g : ℕ → ℝ) (v : ℕ → Fin K → ℝ) (M : ℝ)
    (hM : ∀ᶠ n in atTop, ‖g n • v n‖ ≤ M) :
    ModTight P (fun n (_ : Ω n) t => (g n * t) • v n) := by
  intro ε hε η hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 hM
  have hM1 : (0:ℝ) < |M| + 1 := by positivity
  refine ⟨ε / (2 * (|M| + 1)), by positivity, N, fun n hn => ?_⟩
  refine le_trans (measure_mono (show _ ⊆ (∅ : Set (Ω n)) from ?_)) (by rw [measure_empty]; exact bot_le)
  rintro ω ⟨s, -, t, -, hst, hle⟩
  have e : (g n * s) • v n - (g n * t) • v n = (s - t) • (g n • v n) := by
    rw [smul_smul, ← sub_smul]; congr 1; ring
  rw [e, norm_smul, Real.norm_eq_abs] at hle
  have h0 := hN n hn
  have h1 : |s - t| * ‖g n • v n‖ ≤ ε / (2 * (|M| + 1)) * (|M| + 1) :=
    mul_le_mul hst (by linarith [le_abs_self M]) (norm_nonneg _) (by positivity)
  have h2 : ε / (2 * (|M| + 1)) * (|M| + 1) = ε / 2 := by field_simp
  linarith

end Tight

section TightZeta

variable {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)}

lemma X_eq {Ω₁ : Type} [MeasurableSpace Ω₁] {μP : Measure Ω₁} (N : Network K J μP) (t : ℝ)
    (ω : Ω₁) : N.X t ω = N.Atilde t ω + ∑ k, N.Stilde k t ω + t • (N.lam + N.eta) := by
  have := Xtilde_sub_X N (fun r _ => r) t ω
  simp only [sub_self, Finset.sum_const_zero, sub_eq_zero] at this
  rw [← this]; rfl

lemma zeta_eq (net : ∀ n, Network K J (P n)) (n : ℕ) (ω : Ω n) (t : ℝ) :
    zeta net n ω t = diffScale n (fun r => (net n).Atilde r ω) t +
      ∑ k, diffScale n (fun r => (net n).Stilde k r ω) t +
      (((Real.sqrt n)⁻¹ * n) * t) • ((net n).lam + (net n).eta) := by
  simp only [zeta, diffScale, X_eq]
  rw [smul_add, smul_add, Finset.smul_sum, smul_smul, mul_assoc]

lemma nu_sub_mu {Ω₁ : Type} [MeasurableSpace Ω₁] {μP : Measure Ω₁} (N : Network K J μP)
    (k : Fin K) : N.nu k - N.mu k = (N.lam + N.eta) k := by
  simp only [Network.nu, Network.eta, Pi.add_apply, Matrix.vecMul_sub, Matrix.vecMul_one,
    Pi.sub_apply]
  ring

lemma drift_bdd (net : ∀ n, Network K J (P n)) (c : Fin K → ℝ)
    (hc : ∀ k, Tendsto (fun n : ℕ => Real.sqrt n * ((net n).nu k - (net n).mu k)) atTop
      (𝓝 (c k))) :
    ∀ᶠ n : ℕ in atTop, ‖((Real.sqrt n)⁻¹ * n) • ((net n).lam + (net n).eta)‖ ≤
      ∑ k, (|c k| + 1) := by
  have hev : ∀ᶠ n : ℕ in atTop, ∀ k, |Real.sqrt n * ((net n).nu k - (net n).mu k)| ≤ |c k| + 1 := by
    rw [Filter.eventually_all]; intro k
    filter_upwards [(hc k).eventually (Metric.ball_mem_nhds _ one_pos)] with n hn
    rw [Real.dist_eq] at hn
    have := abs_sub_abs_le_abs_sub (Real.sqrt n * ((net n).nu k - (net n).mu k)) (c k)
    linarith
  filter_upwards [hev] with n hn
  have hg : (Real.sqrt n)⁻¹ * n = Real.sqrt n := by
    rw [inv_mul_eq_div, Real.div_sqrt]
  rw [hg]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  rw [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, ← nu_sub_mu]
  refine (hn k).trans ?_
  exact Finset.single_le_sum (f := fun k => |c k| + 1) (fun i _ => by positivity)
    (Finset.mem_univ k)

lemma tight_zeta (net : ∀ n, Network K J (P n)) (c : Fin K → ℝ)
    (hc : ∀ k, Tendsto (fun n : ℕ => Real.sqrt n * ((net n).nu k - (net n).mu k)) atTop
      (𝓝 (c k)))
    (hA : ModTight P (fun n ω => diffScale n (fun t => (net n).Atilde t ω)))
    (hS : ∀ k, ModTight P (fun n ω => diffScale n (fun t => (net n).Stilde k t ω))) :
    ModTight P (zeta net) := by
  have e : zeta net = fun n ω t => (diffScale n (fun r => (net n).Atilde r ω) t +
      ∑ k, diffScale n (fun r => (net n).Stilde k r ω) t) +
      (((Real.sqrt n)⁻¹ * n) * t) • ((net n).lam + (net n).eta) := by
    funext n ω t; exact zeta_eq net n ω t
  rw [e]
  exact (hA.add (ModTight.sum Finset.univ
    (fun k n ω t => diffScale n (fun r => (net n).Stilde k r ω) t) fun k _ => hS k)).add
    (ModTight.drift (fun n => (Real.sqrt n)⁻¹ * n) (fun n => (net n).lam + (net n).eta)
      (∑ k, (|c k| + 1)) (drift_bdd net c hc))

end TightZeta

section Fdd

variable {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}

lemma clamp01_of_mem' {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : clamp01 t = t := by
  simp [clamp01, max_eq_left ht.1, min_eq_left ht.2]

lemma aem_fdd {X : ∀ n, Ω n → ℝ → Fin K → ℝ} (hX : AECadlagMeas P X) (n : ℕ) {m : ℕ}
    (τ : Fin m → ℝ) (hτ : ∀ i, τ i ∈ Set.Icc (0:ℝ) 1) :
    AEMeasurable (fun ω => fun i => X n ω (τ i)) (P n) := by
  have hev : Measurable (fun x : ℝ → Fin K → ℝ => fun i : Fin m => x (τ i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (τ i)
  refine (hev.comp_aemeasurable (hX n).1).congr (ae_of_all _ fun ω => ?_)
  funext i
  simp only [Function.comp, onUnit, clamp01_of_mem' (hτ i)]

lemma tight_of_close {D : ∀ n, Ω n → ℝ → Fin K → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      P n {ω | ∃ t ∈ Set.Icc (0:ℝ) 1, ε ≤ ‖D n ω t‖} ≤ ENNReal.ofReal η) : ModTight P D := by
  intro ε hε η hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (ε/2) (by linarith) η hη)
  refine ⟨1, one_pos, N, fun n hn => le_trans (measure_mono ?_) (hN n hn)⟩
  rintro ω ⟨s, hs, t, ht, -, hle⟩
  by_contra hcon
  simp only [Set.mem_setOf_eq, not_exists, not_and, not_le] at hcon
  have h1 := hcon s hs
  have h2 := hcon t ht
  have := norm_sub_le (D n ω s) (D n ω t)
  linarith

/-- Slutsky step: fdd convergence transfers along `sup_{t ≤ 1} ‖Yⁿ − Xⁿ‖ → 0` in probability. -/
lemma fdd_of_close {X Y : ∀ n, Ω n → ℝ → Fin K → ℝ} {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} {X' : Ω' → ℝ → Fin K → ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (P n))
    (hX : AECadlagMeas P X) (hY : AECadlagMeas P Y) (hF : FddConv P X P' X')
    (hcl : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      P n {ω | ∃ t ∈ Set.Icc (0:ℝ) 1, ε ≤ ‖Y n ω t - X n ω t‖} ≤ ENNReal.ofReal η) :
    FddConv P Y P' X' := by
  intro m τ hτ f hfC hfL
  obtain ⟨C, hC⟩ := hfC
  obtain ⟨L, hL⟩ := hfL
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have key : Tendsto (fun n => ∫ ω, f (fun i => Y n ω (τ i)) ∂(P n) -
      ∫ ω, f (fun i => X n ω (τ i)) ∂(P n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro e he
    set ε := e / (3 * ((L:ℝ) + 1)) with hε
    set η := e / (3 * (2 * C + 1)) with hη
    have hε0 : 0 < ε := by positivity
    have hη0 : 0 < η := by positivity
    filter_upwards [hcl ε hε0 η hη0] with n hn
    have := hprob n
    set E := {ω | ∃ t ∈ Set.Icc (0:ℝ) 1, ε ≤ ‖Y n ω t - X n ω t‖} with hEdef
    set E' := toMeasurable (P n) E
    have hE'm : MeasurableSet E' := measurableSet_toMeasurable _ _
    have hPE : (P n).real E' ≤ η := by
      rw [measureReal_def, measure_toMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hη0.le hn
    have hfc : Continuous f := hL.continuous
    have hg1 : Integrable (fun ω => f (fun i => Y n ω (τ i))) (P n) :=
      Integrable.of_bound (hfc.measurable.comp_aemeasurable (aem_fdd hY n τ hτ)).aestronglyMeasurable
        C (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC _)
    have hg2 : Integrable (fun ω => f (fun i => X n ω (τ i))) (P n) :=
      Integrable.of_bound (hfc.measurable.comp_aemeasurable (aem_fdd hX n τ hτ)).aestronglyMeasurable
        C (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC _)
    have hLε : 0 ≤ (L:ℝ) * ε := mul_nonneg L.coe_nonneg hε0.le
    have hpt : ∀ ω, ‖f (fun i => Y n ω (τ i)) - f (fun i => X n ω (τ i))‖ ≤
        (L:ℝ) * ε + E'.indicator (fun _ => 2 * C) ω := by
      intro ω
      rw [Real.norm_eq_abs]
      by_cases hω : ω ∈ E'
      · rw [Set.indicator_of_mem hω]
        have h1 := abs_sub (f (fun i => Y n ω (τ i))) (f (fun i => X n ω (τ i)))
        have h2 := hC (fun i => Y n ω (τ i))
        have h3 := hC (fun i => X n ω (τ i))
        linarith
      · rw [Set.indicator_of_notMem hω, add_zero]
        have hωE : ω ∉ E := fun h => hω (subset_toMeasurable _ _ h)
        have hd : dist (fun i => Y n ω (τ i)) (fun i => X n ω (τ i)) ≤ ε := by
          refine (dist_pi_le_iff hε0.le).2 fun i => ?_
          rw [dist_eq_norm]
          by_contra hlt
          push_neg at hlt
          exact hωE ⟨τ i, hτ i, hlt.le⟩
        rw [← Real.dist_eq]
        exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
    have hint : ‖∫ ω, f (fun i => Y n ω (τ i)) ∂(P n) - ∫ ω, f (fun i => X n ω (τ i)) ∂(P n)‖
        ≤ (L:ℝ) * ε + 2 * C * η := by
      rw [← integral_sub hg1 hg2]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hgi : Integrable (fun ω => (L:ℝ) * ε + E'.indicator (fun _ => 2 * C) ω) (P n) :=
        (integrable_const ((L:ℝ) * ε)).add ((integrable_const (2 * C)).indicator hE'm)
      have hval : ∫ ω, ((L:ℝ) * ε + E'.indicator (fun _ => 2 * C) ω) ∂(P n) =
          (L:ℝ) * ε + (P n).real E' * (2 * C) := by
        rw [integral_add (integrable_const ((L:ℝ) * ε))
          ((integrable_const (2 * C)).indicator hE'm), integral_const,
          integral_indicator_const _ hE'm]
        simp only [probReal_univ, smul_eq_mul, one_mul]
      refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hgi
        (ae_of_all _ hpt)).trans ?_
      rw [hval]
      have : (P n).real E' * (2 * C) ≤ η * (2 * C) :=
        mul_le_mul_of_nonneg_right hPE (by linarith)
      linarith
    rw [dist_eq_norm, sub_zero]
    refine lt_of_le_of_lt hint ?_
    have h1 : (L:ℝ) * ε ≤ e / 3 := by
      have : ((L:ℝ) + 1) * ε = e / 3 := by rw [hε]; field_simp
      nlinarith
    have h2 : 2 * C * η ≤ e / 3 := by
      have : (2 * C + 1) * η = e / 3 := by rw [hη]; field_simp
      nlinarith
    linarith
  have := (hF m τ hτ f ⟨C, hC⟩ ⟨L, hL⟩).add key
  rw [add_zero] at this
  exact this.congr fun n => by ring

end Fdd

section Main

variable {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)}

/-- REDUCTION: Proposition 5 from the children `RepThm`, `FddNetput`, `TightPrim`,
`MeasNetputT` and the sibling Proposition 4. -/
theorem prop5_of_children (hR : RepThm) (hF : FddNetput) (hT : TightPrim)
    (hM : MeasNetputT) (h4 : Prop4)
    (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c)
    (Q B : ∀ n, Ω n → ℝ → Fin K → ℝ)
    (hQ : ∀ n, ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (ζ : Ω' → ℝ → Fin K → ℝ)
    (hζ : IsDriftedBM c (covA lam a mu s R) P' ζ) :
    WeakConvD P (fun n ω => diffScale n (fun t => (net n).Xtilde (B n ω) t ω)) P' ζ := by
  obtain ⟨hTA, hTS⟩ := hT K J Ω P net R mu s lam a c hA
  obtain ⟨hMz, hMT⟩ := hM K J Ω P net Q B hQ
  have hcl := close net Q B hQ hTS (h4 K J Ω P net R mu s lam a c hA Q B hQ)
  have hTz := tight_zeta net c hA.2.2.2.2.2.1 hTA hTS
  have hTT : ModTight P (zetaT net B) := by
    have e : zetaT net B = fun n ω t => zeta net n ω t + (zetaT net B n ω t - zeta net n ω t) := by
      funext n ω t; abel
    rw [e]
    exact hTz.add (tight_of_close hcl)
  have hFT : FddConv P (zetaT net B) P' ζ :=
    fdd_of_close (fun n => (net n).isProb) hMz hMT (hF K J Ω P net R mu s lam a c hA Ω' P' ζ hζ) hcl
  exact hR K Ω P (zetaT net B) Ω' P' ζ (fun n => (net n).isProb) hζ.1 hMT hζ.2.1
    (fun ω => (hζ.2.2.2.1 ω).mono Set.Icc_subset_Ici_self) hFT hTT

end Main

end P5

open Filter Topology MeasureTheory Reiman84.QueueLength in
theorem solution {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c)
    (Q B : ∀ n, Ω n → ℝ → Fin K → ℝ)
    (hQ : ∀ n, ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (ζ : Ω' → ℝ → Fin K → ℝ)
    (hζ : IsDriftedBM c (covA lam a mu s R) P' ζ) :
    WeakConvD P (fun n ω => diffScale n (fun t => (net n).Xtilde (B n ω) t ω)) P' ζ := by
  refine P5.prop5_of_children ?_ ?_ ?_ ?_ ?_ net R mu s lam a c hA Q B hQ P' ζ hζ
  · intro K Ω _ P X Ω' _ P' X' hP hP' hXa hX'm hc hF hT
    exact weakConvD_of_fdd_and_modulus P X P' X' hP hP' hXa hX'm hc hF hT
  · intro K J Ω _ P net R mu s lam a c hA Ω' _ P' ζ hζ m τ hτ f hfC hfL
    exact scaled_netput_fdd_convergence net R mu s lam a c hA P' ζ hζ m τ hτ f hfC hfL
  · intro K J Ω _ P net R mu s lam a c hA
    exact primitive_netput_modulus_tight net R mu s lam a c hA
  · intro K J Ω _ P net Q B hQ
    exact ⟨fun n => (scaled_netput_measurable_cadlag (net n) (Q n) (B n) (hQ n) n).1,
      fun n => (scaled_netput_measurable_cadlag (net n) (Q n) (B n) (hQ n) n).2⟩
  · intro K J Ω _ P net R mu s lam a c hA Q B hQ
    exact proposition_4 net R mu s lam a c hA Q B hQ
