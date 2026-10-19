-- Prove2me | solution 1 for Reiman84.QueueLength.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T09:17:05.604457+00:00
-- url     : https://prove2.me/submissions/4190b603-73cd-45ac-bd3a-87e8e02c40ad

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_Reiman84_QueueLength_Network
import Definitions.Def_Reiman84_QueueLength_HeavyTraffic

set_option autoImplicit false

/-! Draft for Reiman (1984) Proposition 5 (755ffe80). DECOMPOSITION SKELETON.
Children are stated as `Prop`-valued definitions (no proofs yet); see
scratch/bailed/755ffe80.md section DECOMPOSE for the plan. -/

/-! ### Deterministic glue copied from the A76 reduction (scratch/decomp/a76e29e9/reduction.lean). -/

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

lemma clamp01_mem (r : ℝ) : Reiman84.QueueLength.clamp01 r ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

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

/-! ### Random-walk and renewal tightness (TightPrim), from scratch/probe/755ffe80_net.lean -/



/-! Random-walk tools for TightPrim (755ffe80): fourth moments of sums of independent centred
bounded variables, and Etemadi's maximal inequality. -/

namespace RW

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma int_of_bdd {f : Ω → ℝ} (B : ℝ) (hf : Measurable f) (hB : ∀ ω, |f ω| ≤ B) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB ω)

/-- second and fourth moments of a sum of independent centred bounded variables. -/
lemma moments (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (C : ℝ) (hb : ∀ i ω, |Y i ω| ≤ C) (h0 : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (σ2 M4 : ℝ) (h2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ σ2) (h4 : ∀ i, ∫ ω, Y i ω ^ 4 ∂μ ≤ M4)
    (j : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range j, Y i ω) ^ 2 ∂μ ≤ j * σ2 ∧
    ∫ ω, (∑ i ∈ Finset.range j, Y i ω) ^ 4 ∂μ ≤ 3 * j ^ 2 * σ2 ^ 2 + j * M4 := by
  have hσ : 0 ≤ σ2 := (integral_nonneg fun ω => sq_nonneg (Y 0 ω)).trans (h2 0)
  induction j with
  | zero => simp [hσ]
  | succ j ih =>
    set T : Ω → ℝ := fun ω => ∑ i ∈ Finset.range j, Y i ω with hTdef
    have hT : Measurable T := Finset.measurable_sum _ fun i _ => hmeas i
    have hTb : ∀ ω, |T ω| ≤ j * C := by
      intro ω
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hb i ω).trans ?_
      simp
    have hind' : IndepFun T (Y j) μ := by
      have := hind.indepFun_finsetSum_of_notMem hmeas (s := Finset.range j) (i := j) (by simp)
      convert this using 1
      funext ω; simp [hTdef, Finset.sum_apply]
    have hI : ∀ a b : ℕ, Integrable (fun ω => T ω ^ a * Y j ω ^ b) μ := fun a b =>
      int_of_bdd ((j * C) ^ a * C ^ b) ((hT.pow_const a).mul ((hmeas j).pow_const b))
        fun ω => by
          rw [abs_mul, abs_pow, abs_pow]
          exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hTb ω) a)
            (pow_le_pow_left₀ (abs_nonneg _) (hb j ω) b) (by positivity)
            (pow_nonneg ((abs_nonneg _).trans (hTb ω)) a)
    have hE : ∀ a b : ℕ, ∫ ω, T ω ^ a * Y j ω ^ b ∂μ =
        (∫ ω, T ω ^ a ∂μ) * ∫ ω, Y j ω ^ b ∂μ := fun a b =>
      (hind'.comp (measurable_id.pow_const a) (measurable_id.pow_const b)).integral_mul_eq_mul_integral
        (hT.pow_const a).aestronglyMeasurable ((hmeas j).pow_const b).aestronglyMeasurable
    have hexp : ∀ n : ℕ, ∫ ω, (T ω + Y j ω) ^ n ∂μ = ∑ m ∈ Finset.range (n + 1),
        (∫ ω, T ω ^ m ∂μ) * (∫ ω, Y j ω ^ (n - m) ∂μ) * n.choose m := by
      intro n
      simp_rw [add_pow]
      rw [integral_finsetSum _ fun m _ => (hI m (n - m)).mul_const _]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [integral_mul_const, hE]
    have i1 : ∫ ω, T ω ∂μ = 0 := by
      rw [hTdef, integral_finsetSum _ fun i _ => int_of_bdd C (hmeas i) (hb i)]
      simp [h0]
    have hsum : ∀ ω, ∑ i ∈ Finset.range (j + 1), Y i ω = T ω + Y j ω :=
      fun ω => Finset.sum_range_succ _ _
    simp only [hsum, hexp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, zero_add]
    norm_num only [pow_zero, pow_one, integral_const, probReal_univ, smul_eq_mul, mul_one,
      one_mul, zero_mul, i1, h0]
    have hT2 : 0 ≤ ∫ ω, T ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have hY2 : 0 ≤ ∫ ω, Y j ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    obtain ⟨ih1, ih2⟩ := ih
    change ∫ ω, T ω ^ 2 ∂μ ≤ _ at ih1
    have hm := mul_le_mul ih1 (h2 j) hY2 (by positivity)
    change ∫ ω, T ω ^ 4 ∂μ ≤ _ at ih2
    have h4j := h4 j
    have h2j := h2 j
    push_cast
    constructor <;> nlinarith

/-- partial sums `S_j = ∑_{i<j} Y_i`. -/
noncomputable def psum (Y : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range j, Y i ω

/-- Etemadi's maximal inequality. -/
lemma etemadi (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (L : ℕ) (x : ℝ) (q : ENNReal)
    (hq : ∀ j ≤ L, μ {ω | x ≤ |psum Y j ω|} ≤ q) :
    μ {ω | ∃ j ≤ L, 3 * x ≤ |psum Y j ω|} ≤ 3 * q := by
  classical
  let F : ∀ j : ℕ, (Finset.range j → ℝ) → (ℕ → ℝ) :=
    fun j v i => if h : i ∈ Finset.range j then v ⟨i, h⟩ else 0
  have hF : ∀ j, Measurable (F j) := fun j => measurable_pi_lambda _ fun i => by
    by_cases h : i ∈ Finset.range j
    · simp only [F, dif_pos h]; exact measurable_pi_apply _
    · simp only [F, dif_neg h]; exact measurable_const
  let V1 : ∀ j, Ω → (Finset.range j → ℝ) := fun j ω i => Y i ω
  have hV1 : ∀ j, Measurable (V1 j) := fun j => measurable_pi_lambda _ fun i => hmeas i
  have hFV : ∀ j ω, ∀ i' ≤ j, ∑ i ∈ Finset.range i', F j (V1 j ω) i = psum Y i' ω := by
    intro j ω i' hi'
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i ∈ Finset.range j := Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hi')
    simp only [F, V1, dif_pos this]
  have hV2 : ∀ j ≤ L, ∀ ω, (∑ i : Finset.Ico j L, Y i ω) = psum Y L ω - psum Y j ω := by
    intro j hj ω
    rw [Finset.sum_coe_sort (Finset.Ico j L) (fun i => Y i ω), psum, psum,
      ← Finset.sum_range_add_sum_Ico _ hj]
    ring
  have hg : ∀ m, Measurable fun y : ℕ → ℝ => |∑ i ∈ Finset.range m, y i| := fun m =>
    continuous_abs.measurable.comp (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  let s : ℕ → Set (ℕ → ℝ) := fun j => {y | 3 * x ≤ |∑ i ∈ Finset.range j, y i| ∧
    ∀ i' ∈ Finset.range j, |∑ i ∈ Finset.range i', y i| < 3 * x}
  have hsm : ∀ j, MeasurableSet (s j) := by
    intro j
    have : s j = {y | 3 * x ≤ |∑ i ∈ Finset.range j, y i|} ∩
        ⋂ i' ∈ Finset.range j, {y | |∑ i ∈ Finset.range i', y i| < 3 * x} := by
      ext y; simp [s]
    rw [this]
    exact (measurableSet_le measurable_const (hg j)).inter
      (Finset.measurableSet_biInter _ fun i' _ => measurableSet_lt (hg i') measurable_const)
  let E : ℕ → Set Ω := fun j => (F j ∘ V1 j) ⁻¹' (s j)
  have hEm : ∀ j, MeasurableSet (E j) := fun j => ((hF j).comp (hV1 j)) (hsm j)
  let D : ℕ → Set Ω := fun j =>
    ((fun v : Finset.Ico j L → ℝ => ∑ i, v i) ∘ (fun ω (i : Finset.Ico j L) => Y i ω)) ⁻¹'
      {r | 2 * x ≤ |r|}
  have hind2 : ∀ j, μ (E j ∩ D j) = μ (E j) * μ (D j) := by
    intro j
    have h1 := hind.indepFun_finset (Finset.range j) (Finset.Ico j L)
      (Finset.disjoint_left.2 fun i hi hi' => by
        simp only [Finset.mem_range, Finset.mem_Ico] at hi hi'; omega) hmeas
    have h2 := h1.comp (hF j) (Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i)
    exact h2.measure_inter_preimage_eq_mul _ _ (hsm j)
      (measurableSet_le measurable_const continuous_abs.measurable)
  have hD : ∀ j ≤ L, μ (D j) ≤ 2 * q := by
    intro j hj
    have hsub : D j ⊆ {ω | x ≤ |psum Y L ω|} ∪ {ω | x ≤ |psum Y j ω|} := by
      intro ω hω
      have hω' : 2 * x ≤ |∑ i : Finset.Ico j L, Y i ω| := hω
      rw [hV2 j hj ω] at hω'
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
      have := abs_sub (psum Y L ω) (psum Y j ω)
      linarith [hcon.1, hcon.2]
    calc μ (D j) ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ q + q := add_le_add (hq L le_rfl) (hq j hj)
      _ = 2 * q := by ring
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (L + 1))) E := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω ha hb
    have ha' : F a (V1 a ω) ∈ s a := ha
    have hb' : F b (V1 b ω) ∈ s b := hb
    simp only [s, Set.mem_setOf_eq] at ha' hb'
    rcases lt_or_gt_of_ne hab with h | h
    · have h1 := ha'.1
      have h2 := hb'.2 a (Finset.mem_range.2 h)
      rw [hFV a ω a le_rfl] at h1; rw [hFV b ω a h.le] at h2; linarith
    · have h1 := hb'.1
      have h2 := ha'.2 b (Finset.mem_range.2 h)
      rw [hFV b ω b le_rfl] at h1; rw [hFV a ω b h.le] at h2; linarith
  have hsub : {ω | ∃ j ≤ L, 3 * x ≤ |psum Y j ω|} ⊆
      {ω | x ≤ |psum Y L ω|} ∪ ⋃ j ∈ Finset.range (L + 1), (E j ∩ D j) := by
    rintro ω ⟨j, hjL, hj⟩
    by_cases hL : x ≤ |psum Y L ω|
    · left; exact hL
    · right
      have hex : ∃ j, j ≤ L ∧ 3 * x ≤ |psum Y j ω| := ⟨j, hjL, hj⟩
      have hj0 := Nat.find_spec hex
      have hmin : ∀ i < Nat.find hex, ¬ (i ≤ L ∧ 3 * x ≤ |psum Y i ω|) :=
        fun i hi => Nat.find_min hex hi
      refine Set.mem_biUnion (x := Nat.find hex)
        (Finset.mem_coe.2 (Finset.mem_range.2 (by omega))) ⟨?_, ?_⟩
      · show F (Nat.find hex) (V1 (Nat.find hex) ω) ∈ s (Nat.find hex)
        refine ⟨by rw [hFV _ ω _ le_rfl]; exact hj0.2, fun i' hi' => ?_⟩
        rw [hFV _ ω i' (Finset.mem_range.1 hi').le]
        have := hmin i' (Finset.mem_range.1 hi')
        push_neg at this
        exact this (by have := Finset.mem_range.1 hi'; omega)
      · show 2 * x ≤ |∑ i : Finset.Ico (Nat.find hex) L, Y i ω|
        rw [hV2 _ hj0.1 ω]
        push_neg at hL
        have := abs_sub_abs_le_abs_sub (psum Y (Nat.find hex) ω) (psum Y L ω)
        rw [abs_sub_comm] at this
        linarith [hj0.2]
  calc μ {ω | ∃ j ≤ L, 3 * x ≤ |psum Y j ω|}
      ≤ μ ({ω | x ≤ |psum Y L ω|} ∪ ⋃ j ∈ Finset.range (L + 1), (E j ∩ D j)) := measure_mono hsub
    _ ≤ μ {ω | x ≤ |psum Y L ω|} + ∑ j ∈ Finset.range (L + 1), μ (E j ∩ D j) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ q + ∑ j ∈ Finset.range (L + 1), μ (E j) * (2 * q) := by
        refine add_le_add (hq L le_rfl) (Finset.sum_le_sum fun j hj => ?_)
        rw [hind2 j]
        gcongr
        exact hD j (by have := Finset.mem_range.1 hj; omega)
    _ = q + μ (⋃ j ∈ Finset.range (L + 1), E j) * (2 * q) := by
        rw [← Finset.sum_mul, measure_biUnion_finset hdisj fun j _ => hEm j]
    _ ≤ q + 1 * (2 * q) := by gcongr; exact prob_le_one
    _ = 3 * q := by ring

lemma markov4 (Z : Ω → ℝ) (hint : Integrable (fun ω => Z ω ^ 4) μ) {x : ℝ} (hx : 0 < x) :
    μ {ω | x ≤ |Z ω|} ≤ ENNReal.ofReal ((∫ ω, Z ω ^ 4 ∂μ) / x ^ 4) := by
  have hx4 : 0 < x ^ 4 := by positivity
  have h := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun ω => by positivity : 0 ≤ᵐ[μ] fun ω => Z ω ^ 4) hint (x ^ 4)
  have hsub : {ω | x ≤ |Z ω|} ⊆ {ω | x ^ 4 ≤ Z ω ^ 4} := by
    intro ω hω
    have h1 : x ^ 4 ≤ |Z ω| ^ 4 := pow_le_pow_left₀ hx.le hω 4
    rwa [Even.pow_abs (⟨2, rfl⟩ : Even 4)] at h1
  calc μ {ω | x ≤ |Z ω|} ≤ μ {ω | x ^ 4 ≤ Z ω ^ 4} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | x ^ 4 ≤ Z ω ^ 4}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal ((∫ ω, Z ω ^ 4 ∂μ) / x ^ 4) :=
        ENNReal.ofReal_le_ofReal (by rw [le_div_iff₀ hx4]; linarith [h])

/-- maximal inequality for one block of a centred bounded independent sequence. -/
lemma block_bound (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (B : ℝ) (hb : ∀ i ω, |Y i ω| ≤ B) (h0 : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (σ2 : ℝ) (h2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ σ2) (a L : ℕ) {x : ℝ} (hx : 0 < x) :
    μ {ω | ∃ l ≤ L, 3 * x ≤ |psum (Y ∘ (fun i => a + i)) l ω|} ≤
      3 * ENNReal.ofReal ((3 * L ^ 2 * σ2 ^ 2 + L * (B ^ 2 * σ2)) / x ^ 4) := by
  have hσ : 0 ≤ σ2 := (integral_nonneg fun ω => sq_nonneg (Y 0 ω)).trans (h2 0)
  have hind' : iIndepFun (Y ∘ (fun i => a + i)) μ := iIndepFun.precomp (g := fun i : ℕ => a + i) (add_right_injective a) hind
  have hmeas' : ∀ i, Measurable ((Y ∘ (fun i => a + i)) i) := fun i => hmeas _
  have hb' : ∀ i ω, |(Y ∘ (fun i => a + i)) i ω| ≤ B := fun i ω => hb _ ω
  have h4 : ∀ i, ∫ ω, (Y ∘ (fun i => a + i)) i ω ^ 4 ∂μ ≤ B ^ 2 * σ2 := by
    intro i
    have hY := hmeas (a + i)
    have hi2 : Integrable (fun ω => Y (a + i) ω ^ 2) μ :=
      int_of_bdd (B ^ 2) (hY.pow_const 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb _ ω) 2
    have hi4 : Integrable (fun ω => Y (a + i) ω ^ 4) μ :=
      int_of_bdd (B ^ 4) (hY.pow_const 4) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb _ ω) 4
    calc ∫ ω, Y (a + i) ω ^ 4 ∂μ ≤ ∫ ω, B ^ 2 * Y (a + i) ω ^ 2 ∂μ := by
          refine integral_mono hi4 (hi2.const_mul _) fun ω => ?_
          have h1 : Y (a + i) ω ^ 2 ≤ B ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb _ ω) 2
          have h2' : 0 ≤ Y (a + i) ω ^ 2 := sq_nonneg _
          show Y (a + i) ω ^ 4 ≤ B ^ 2 * Y (a + i) ω ^ 2
          nlinarith
      _ = B ^ 2 * ∫ ω, Y (a + i) ω ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ B ^ 2 * σ2 := mul_le_mul_of_nonneg_left (h2 _) (sq_nonneg _)
  refine etemadi _ hind' hmeas' L x _ fun j hj => ?_
  have hmom := (moments _ hind' hmeas' B hb' (fun i => h0 _) σ2 (B ^ 2 * σ2)
    (fun i => h2 _) h4 j).2
  have hpm : Measurable (psum (Y ∘ (fun i => a + i)) j) :=
    Finset.measurable_sum _ fun i _ => hmeas' i
  have hint : Integrable (fun ω => psum (Y ∘ (fun i => a + i)) j ω ^ 4) μ := by
    refine int_of_bdd ((j * B) ^ 4) (hpm.pow_const 4) fun ω => ?_
    rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 4
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hb' i ω).trans ?_
    simp
  refine (markov4 _ hint hx).trans (ENNReal.ofReal_le_ofReal ?_)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hjL : (j:ℝ) ≤ L := by exact_mod_cast hj
  have hB2 : 0 ≤ B ^ 2 * σ2 := mul_nonneg (sq_nonneg _) hσ
  refine hmom.trans ?_
  have : (j:ℝ) ^ 2 ≤ (L:ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hjL 2
  nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg σ2),
    mul_le_mul_of_nonneg_right hjL hB2]

/-- truncation at level `τ`. -/
noncomputable def trunc (τ : ℝ) (x : ℝ) : ℝ := if |x| ≤ τ then x else 0

lemma trunc_meas (τ : ℝ) : Measurable (trunc τ) :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_id
    measurable_const

lemma trunc_abs {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) : |trunc τ x| ≤ τ := by
  unfold trunc; split_ifs with h
  · exact h
  · simpa using hτ

lemma trunc_sq (τ x : ℝ) : trunc τ x ^ 2 ≤ x ^ 2 := by
  unfold trunc; split_ifs
  · exact le_rfl
  · simpa using sq_nonneg x

lemma trunc_tail {τ : ℝ} (hτ : 0 < τ) (x : ℝ) : |x - trunc τ x| ≤ x ^ 2 / τ := by
  unfold trunc; split_ifs with h
  · simp only [sub_self, abs_zero]; positivity
  · push_neg at h
    rw [sub_zero, le_div_iff₀ hτ, ← sq_abs]
    nlinarith [abs_nonneg x]

/-- one-space modulus bound for a centred i.i.d. square-integrable sequence, by truncation at
`τ`, block decomposition and Etemadi's inequality. -/
lemma mod_bound (ξ : ℕ → Ω → ℝ) (hind : iIndepFun ξ μ) (hmeas : ∀ i, Measurable (ξ i))
    (hid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ) (hL2 : MemLp (ξ 0) 2 μ)
    (h0 : ∫ ω, ξ 0 ω ∂μ = 0) (σ2 : ℝ) (hσ : ∫ ω, ξ 0 ω ^ 2 ∂μ ≤ σ2)
    {τ : ℝ} (hτ : 0 < τ) (Nmax L : ℕ) (hL : 1 ≤ L) {x : ℝ} (hx : 0 < x)
    (hdrift : (L:ℝ) * (σ2 / τ) ≤ x / 2) :
    μ {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ i + L ∧ j ≤ Nmax ∧ x ≤ |psum ξ j ω - psum ξ i ω|} ≤
      Nmax * μ {ω | τ < |ξ 0 ω|} + ((Nmax / L + 1 : ℕ) : ENNReal) *
        (3 * ENNReal.ofReal ((3 * ((2 * L : ℕ) : ℝ) ^ 2 * σ2 ^ 2 +
          ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * σ2)) / (x / 12) ^ 4)) := by
  classical
  set c := ∫ ω, trunc τ (ξ 0 ω) ∂μ with hc
  set Y : ℕ → Ω → ℝ := fun i => (fun r => trunc τ r - c) ∘ ξ i with hY
  have hYind : iIndepFun Y μ := hind.comp (fun _ r => trunc τ r - c)
    (fun _ => (trunc_meas τ).sub_const c)
  have hYm : ∀ i, Measurable (Y i) := fun i => ((trunc_meas τ).sub_const c).comp (hmeas i)
  have htr_int : ∀ i, Integrable (fun ω => trunc τ (ξ i ω)) μ := fun i =>
    int_of_bdd τ ((trunc_meas τ).comp (hmeas i)) fun ω => trunc_abs hτ.le _
  have hcabs : |c| ≤ τ := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => trunc τ (ξ 0 ω)) (C := τ)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact trunc_abs hτ.le _)
    simpa [Real.norm_eq_abs] using this
  have hYb : ∀ i ω, |Y i ω| ≤ 2 * τ := by
    intro i ω
    simp only [hY, Function.comp]
    have := abs_sub (trunc τ (ξ i ω)) c
    linarith [trunc_abs hτ.le (ξ i ω)]
  have hY0 : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    simp only [hY, Function.comp]
    rw [integral_sub (htr_int i) (integrable_const c), integral_const, probReal_univ, one_smul]
    have := ((hid i).comp (trunc_meas τ)).integral_eq
    simp only [Function.comp] at this
    rw [this, hc, sub_self]
  have hY2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ σ2 := by
    intro i
    have e : ∫ ω, Y i ω ^ 2 ∂μ = ∫ ω, (trunc τ (ξ 0 ω) - c) ^ 2 ∂μ := by
      have := ((hid i).comp (((trunc_meas τ).sub_const c).pow_const 2)).integral_eq
      simpa [hY, Function.comp] using this
    rw [e]
    have hsq : Integrable (fun ω => trunc τ (ξ 0 ω) ^ 2) μ :=
      int_of_bdd (τ ^ 2) (((trunc_meas τ).comp (hmeas 0)).pow_const 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (trunc_abs hτ.le _) 2
    have e2 : ∫ ω, (trunc τ (ξ 0 ω) - c) ^ 2 ∂μ = ∫ ω, trunc τ (ξ 0 ω) ^ 2 ∂μ - c ^ 2 := by
      have hp : ∀ ω, (trunc τ (ξ 0 ω) - c) ^ 2 =
          trunc τ (ξ 0 ω) ^ 2 + ((-2 * c) * trunc τ (ξ 0 ω) + c ^ 2) := fun ω => by ring
      simp only [hp]
      have hg1 : Integrable (fun ω => -2 * c * trunc τ (ξ 0 ω)) μ := (htr_int 0).const_mul _
      have hg : Integrable (fun ω => -2 * c * trunc τ (ξ 0 ω) + c ^ 2) μ :=
        hg1.add (integrable_const _)
      rw [integral_add hsq hg, integral_add hg1 (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul, ← hc]
      ring
    rw [e2]
    have h1 : ∫ ω, trunc τ (ξ 0 ω) ^ 2 ∂μ ≤ ∫ ω, ξ 0 ω ^ 2 ∂μ :=
      integral_mono hsq hL2.integrable_sq fun ω => trunc_sq τ _
    nlinarith [sq_nonneg c]
  have hcσ : |c| ≤ σ2 / τ := by
    have hξi : Integrable (ξ 0) μ := hL2.integrable one_le_two
    have e : c = -∫ ω, (ξ 0 ω - trunc τ (ξ 0 ω)) ∂μ := by
      rw [integral_sub hξi (htr_int 0), h0, hc]; ring
    rw [e, abs_neg]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |ξ 0 ω - trunc τ (ξ 0 ω)| ∂μ ≤ ∫ ω, ξ 0 ω ^ 2 / τ ∂μ :=
          integral_mono (hξi.sub (htr_int 0)).abs (hL2.integrable_sq.div_const τ)
            fun ω => trunc_tail hτ _
      _ = (∫ ω, ξ 0 ω ^ 2 ∂μ) / τ := integral_div _ _
      _ ≤ σ2 / τ := div_le_div_of_nonneg_right hσ hτ.le
  -- the event inclusion
  set Blk : ℕ → Set Ω := fun b =>
    {ω | ∃ l ≤ 2 * L, 3 * (x / 12) ≤ |psum (Y ∘ (fun i => b * L + i)) l ω|} with hBlk
  have hsub : {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ i + L ∧ j ≤ Nmax ∧ x ≤ |psum ξ j ω - psum ξ i ω|} ⊆
      (⋃ i ∈ Finset.range Nmax, {ω | τ < |ξ i ω|}) ∪ ⋃ b ∈ Finset.range (Nmax / L + 1), Blk b := by
    rintro ω ⟨i, j, hij, hjL, hjN, hxij⟩
    by_cases hbad : ∃ i' < Nmax, τ < |ξ i' ω|
    · obtain ⟨i', hi', h'⟩ := hbad
      left; exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hi')) h'
    · right
      push_neg at hbad
      have hpsum : ∀ k ≤ Nmax, psum ξ k ω = psum Y k ω + k * c := by
        intro k hk
        have e : ∀ i ∈ Finset.range k, ξ i ω = Y i ω + c := fun i hi => by
          simp only [hY, Function.comp, trunc,
            if_pos (hbad i (by have := Finset.mem_range.1 hi; omega))]
          ring
        rw [psum, psum, Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
      have hdiff : x / 2 ≤ |psum Y j ω - psum Y i ω| := by
        rw [hpsum j hjN, hpsum i (hij.trans hjN)] at hxij
        have hji : ((j:ℝ) - i) ≤ L := by
          have : (j:ℝ) ≤ i + L := by exact_mod_cast hjL
          linarith
        have hji0 : 0 ≤ (j:ℝ) - i := by
          have : (i:ℝ) ≤ j := by exact_mod_cast hij
          linarith
        have hcd : |((j:ℝ) - i) * c| ≤ L * (σ2 / τ) := by
          rw [abs_mul, abs_of_nonneg hji0]
          exact mul_le_mul hji hcσ (abs_nonneg _) (Nat.cast_nonneg _)
        have e : psum Y j ω + j * c - (psum Y i ω + i * c) =
            (psum Y j ω - psum Y i ω) + ((j:ℝ) - i) * c := by ring
        rw [e] at hxij
        have := abs_add_le (psum Y j ω - psum Y i ω) (((j:ℝ) - i) * c)
        linarith
      set b := i / L with hb
      have ha : b * L ≤ i := Nat.div_mul_le_self i L
      have ha2 : i < b * L + L := Nat.lt_div_mul_add hL
      have hshift : ∀ k, b * L ≤ k →
          psum (Y ∘ (fun i => b * L + i)) (k - b * L) ω = psum Y k ω - psum Y (b * L) ω := by
        intro k hk
        have : psum Y k ω = psum Y (b * L) ω + psum (Y ∘ (fun i => b * L + i)) (k - b * L) ω := by
          simp only [psum, Function.comp]
          rw [← Finset.sum_range_add (fun i => Y i ω) (b * L) (k - b * L), Nat.add_sub_cancel' hk]
        linarith
      refine Set.mem_biUnion (x := b) (Finset.mem_coe.2 (Finset.mem_range.2 ?_)) ?_
      · have : b ≤ Nmax / L := Nat.div_le_div_right (hij.trans hjN)
        omega
      · by_contra hno
        simp only [hBlk, Set.mem_setOf_eq, not_exists, not_and, not_le] at hno
        have h1 := hno (j - b * L) (by omega)
        have h2 := hno (i - b * L) (by omega)
        rw [hshift j (by omega)] at h1
        rw [hshift i ha] at h2
        have := abs_sub_le (psum Y j ω) (psum Y (b * L) ω) (psum Y i ω)
        rw [abs_sub_comm (psum Y (b * L) ω)] at this
        linarith
  calc μ {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ i + L ∧ j ≤ Nmax ∧ x ≤ |psum ξ j ω - psum ξ i ω|}
      ≤ μ ((⋃ i ∈ Finset.range Nmax, {ω | τ < |ξ i ω|}) ∪
          ⋃ b ∈ Finset.range (Nmax / L + 1), Blk b) := measure_mono hsub
    _ ≤ μ (⋃ i ∈ Finset.range Nmax, {ω | τ < |ξ i ω|}) +
          μ (⋃ b ∈ Finset.range (Nmax / L + 1), Blk b) := measure_union_le _ _
    _ ≤ ∑ i ∈ Finset.range Nmax, μ {ω | τ < |ξ i ω|} +
          ∑ b ∈ Finset.range (Nmax / L + 1), μ (Blk b) :=
        add_le_add (measure_biUnion_finset_le _ _) (measure_biUnion_finset_le _ _)
    _ ≤ ∑ i ∈ Finset.range Nmax, μ {ω | τ < |ξ 0 ω|} +
          ∑ b ∈ Finset.range (Nmax / L + 1), (3 * ENNReal.ofReal ((3 * ((2 * L : ℕ) : ℝ) ^ 2 *
            σ2 ^ 2 + ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * σ2)) / (x / 12) ^ 4)) := by
        refine add_le_add (le_of_eq (Finset.sum_congr rfl fun i _ =>
          (hid i).measure_mem_eq (measurableSet_lt measurable_const continuous_abs.measurable)))
          (Finset.sum_le_sum fun b _ => ?_)
        exact block_bound Y hYind hYm (2 * τ) hYb hY0 σ2 hY2 (b * L) (2 * L) (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
          nsmul_eq_mul, nsmul_eq_mul]

section Tri

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)]

/-- lattice modulus tightness of the scaled partial-sum process of a triangular array of centred
i.i.d. rows with bounded variances and a Lindeberg-type jump condition. -/
lemma rw_tight (P : ∀ n, Measure (Ωs n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (ξ : ∀ n, ℕ → Ωs n → ℝ) (hind : ∀ n, iIndepFun (ξ n) (P n))
    (hmeas : ∀ n i, Measurable (ξ n i)) (hid : ∀ n i, IdentDistrib (ξ n i) (ξ n 0) (P n) (P n))
    (hL2 : ∀ n, MemLp (ξ n 0) 2 (P n)) (h0 : ∀ n, ∫ ω, ξ n 0 ω ∂(P n) = 0)
    (σ2 : ℝ) (hσ : ∀ᶠ n in atTop, ∫ ω, ξ n 0 ω ^ 2 ∂(P n) ≤ σ2)
    (hUI : ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) atTop (𝓝 0))
    (T : ℝ) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧
      (j:ℝ) ≤ T * n ∧ ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ≤
        ENNReal.ofReal η := by
  set s' := max σ2 1 with hs'
  have hs'1 : 1 ≤ s' := le_max_right _ _
  have hs'0 : 0 < s' := by linarith
  set K := 6 * 12 ^ 4 * T / ε ^ 4 with hK
  have hK0 : 0 < K := by positivity
  set θ := Real.sqrt (η / (64 * K * s')) with hθ
  have hθ0 : 0 < θ := Real.sqrt_pos.2 (by positivity)
  have hθ2 : θ ^ 2 = η / (64 * K * s') := Real.sq_sqrt (by positivity)
  set δ := min T (min (η / (192 * K * s' ^ 2)) (θ * ε / (4 * s'))) with hδ
  have hδ0 : 0 < δ := lt_min hT (lt_min (by positivity) (by positivity))
  have hδT : δ ≤ T := min_le_left _ _
  have hδ1 : δ ≤ η / (192 * K * s' ^ 2) := (min_le_right _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ θ * ε / (4 * s') := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ0, ?_⟩
  have hJ : ∀ᶠ n : ℕ in atTop, ((⌈T⌉₊ : ℕ) : ENNReal) *
      ((n : ENNReal) * P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) < ENNReal.ofReal (η / 2) := by
    have := ENNReal.Tendsto.const_mul (a := ((⌈T⌉₊ : ℕ) : ENNReal)) (hUI θ hθ0)
      (Or.inr (ENNReal.natCast_ne_top _))
    rw [mul_zero] at this
    exact (tendsto_order.1 this).2 _ (ENNReal.ofReal_pos.2 (by linarith))
  filter_upwards [hJ, hσ, eventually_ge_atTop ⌈1 / δ⌉₊, eventually_ge_atTop 1]
    with n hJn hσn hnδ hn1
  have := hP n
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hδn : 1 ≤ δ * n := by
    have h1 : 1 / δ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnδ)
    rw [div_le_iff₀ hδ0] at h1; linarith
  set Nmax := ⌊T * n⌋₊ with hNmax
  set L := ⌈δ * n⌉₊ with hLdef
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hLr : (L:ℝ) ≤ 2 * δ * n := by
    have := Nat.ceil_lt_add_one (by positivity : 0 ≤ δ * n); linarith
  have hLr' : δ * n ≤ L := Nat.le_ceil _
  have hNr : (Nmax:ℝ) ≤ T * n := Nat.floor_le (by positivity)
  set τ := θ * Real.sqrt n with hτdef
  have hτ : 0 < τ := by positivity
  set x := ε * Real.sqrt n with hxdef
  have hx : 0 < x := by positivity
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  have hdrift : (L:ℝ) * (s' / τ) ≤ x / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hτ]
    have hxτ : x / 2 * τ = ε * θ * n / 2 := by
      rw [hxdef, hτdef, show ε * Real.sqrt n / 2 * (θ * Real.sqrt n) =
        ε * θ * (Real.sqrt n * Real.sqrt n) / 2 by ring, hsn]
    rw [hxτ]
    calc (L:ℝ) * s' ≤ 2 * δ * n * s' := mul_le_mul_of_nonneg_right hLr hs'0.le
      _ ≤ 2 * (θ * ε / (4 * s')) * n * s' := by gcongr
      _ = ε * θ * n / 2 := by field_simp; ring
  have hmb := mod_bound (ξ n) (hind n) (hmeas n) (hid n) (hL2 n) (h0 n) s'
    (hσn.trans (le_max_left _ _)) hτ Nmax L hL1 hx hdrift
  have hsub : {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧
      (j:ℝ) ≤ T * n ∧ ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ⊆
      {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ i + L ∧ j ≤ Nmax ∧ x ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} := by
    rintro ω ⟨i, j, hij, hj1, hj2, hjx⟩
    refine ⟨i, j, hij, ?_, Nat.le_floor hj2, hjx⟩
    have : (j:ℝ) ≤ i + L := hj1.trans (by linarith [hLr'])
    exact_mod_cast this
  refine (measure_mono hsub).trans (hmb.trans ?_)
  have hjump : (Nmax : ENNReal) * P n {ω | τ < |ξ n 0 ω|} ≤ ENNReal.ofReal (η / 2) := by
    refine le_trans ?_ hJn.le
    rw [← mul_assoc]
    gcongr
    have : Nmax ≤ ⌈T⌉₊ * n := by
      have h1 : (Nmax:ℝ) ≤ ⌈T⌉₊ * n :=
        hNr.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) hnpos.le)
      exact_mod_cast h1
    exact_mod_cast this
  set Z := 48 * δ * s' ^ 2 + 16 * θ ^ 2 * s' with hZ
  have hZ0 : 0 < Z := by positivity
  set r := (3 * ((2 * L : ℕ) : ℝ) ^ 2 * s' ^ 2 + ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * s')) /
    (x / 12) ^ 4 with hr
  have hr0 : 0 ≤ r := by positivity
  have hx4 : (x / 12) ^ 4 = ε ^ 4 * (n:ℝ) ^ 2 / 12 ^ 4 := by
    rw [hxdef, div_pow, mul_pow, show Real.sqrt n ^ 4 = (Real.sqrt n * Real.sqrt n) ^ 2 by ring, hsn]
  have h2L : ((2 * L : ℕ) : ℝ) ≤ 4 * δ * n := by push_cast; linarith
  have hτ2 : (2 * τ) ^ 2 = 4 * θ ^ 2 * n := by
    rw [hτdef, show (2 * (θ * Real.sqrt n)) ^ 2 = 4 * θ ^ 2 * (Real.sqrt n * Real.sqrt n) by ring,
      hsn]
  have hnum : 3 * ((2 * L : ℕ) : ℝ) ^ 2 * s' ^ 2 + ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * s') ≤
      (n:ℝ) ^ 2 * δ * Z := by
    rw [hτ2]
    have h0' : 0 ≤ ((2 * L : ℕ) : ℝ) := Nat.cast_nonneg _
    calc 3 * ((2 * L : ℕ) : ℝ) ^ 2 * s' ^ 2 + ((2 * L : ℕ) : ℝ) * (4 * θ ^ 2 * n * s')
        ≤ 3 * (4 * δ * n) ^ 2 * s' ^ 2 + (4 * δ * n) * (4 * θ ^ 2 * n * s') := by
          gcongr
      _ = (n:ℝ) ^ 2 * δ * Z := by rw [hZ]; ring
  have hrb : r ≤ 12 ^ 4 * δ * Z / ε ^ 4 := by
    calc r = (3 * ((2 * L : ℕ) : ℝ) ^ 2 * s' ^ 2 + ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * s')) /
          (ε ^ 4 * (n:ℝ) ^ 2 / 12 ^ 4) := by rw [hr, hx4]
      _ ≤ ((n:ℝ) ^ 2 * δ * Z) / (ε ^ 4 * (n:ℝ) ^ 2 / 12 ^ 4) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = 12 ^ 4 * δ * Z / ε ^ 4 := by field_simp
  have hk : (((Nmax / L + 1 : ℕ)) : ℝ) ≤ 2 * T / δ := by
    push_cast
    have h1 : ((Nmax / L : ℕ) : ℝ) ≤ (Nmax : ℝ) / L := Nat.cast_div_le
    have h2 : (Nmax : ℝ) / L ≤ T / δ := by
      rw [div_le_div_iff₀ (by positivity) hδ0]
      calc (Nmax:ℝ) * δ ≤ T * n * δ := mul_le_mul_of_nonneg_right hNr hδ0.le
        _ = T * (δ * n) := by ring
        _ ≤ T * L := mul_le_mul_of_nonneg_left hLr' hT.le
    have h3 : 1 ≤ T / δ := by rw [le_div_iff₀ hδ0]; linarith
    have : 2 * T / δ = T / δ + T / δ := by ring
    linarith
  have hblock : (((Nmax / L + 1 : ℕ)) : ENNReal) * (3 * ENNReal.ofReal r) ≤
      ENNReal.ofReal (η / 2) := by
    rw [← ENNReal.ofReal_natCast, show (3 : ENNReal) = ENNReal.ofReal 3 by simp,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hk0 : (0:ℝ) ≤ ((Nmax / L + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (((Nmax / L + 1 : ℕ)) : ℝ) * (3 * r) ≤ (2 * T / δ) * (3 * (12 ^ 4 * δ * Z / ε ^ 4)) :=
          mul_le_mul hk (by linarith) (by positivity) (by positivity)
      _ = K * (48 * δ * s' ^ 2) + K * (16 * θ ^ 2 * s') := by rw [hK, hZ]; field_simp; ring
      _ ≤ K * (48 * (η / (192 * K * s' ^ 2)) * s' ^ 2) + K * (16 * θ ^ 2 * s') := by gcongr
      _ = η / 2 := by rw [hθ2]; field_simp; ring
  calc (Nmax : ENNReal) * P n {ω | τ < |ξ n 0 ω|} +
        (((Nmax / L + 1 : ℕ)) : ENNReal) * (3 * ENNReal.ofReal r)
      ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hjump hblock
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

/-- boundedness in probability of the scaled partial sums up to time `T n`, by chaining the
modulus bound of `rw_tight`. -/
lemma rw_bdd (P : ∀ n, Measure (Ωs n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (ξ : ∀ n, ℕ → Ωs n → ℝ) (T : ℝ)
    (hmod : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧ (j:ℝ) ≤ T * n ∧
        ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ≤ ENNReal.ofReal η)
    (hT : 0 < T) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, P n {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧
      M * Real.sqrt n ≤ |psum (ξ n) l ω|} ≤ ENNReal.ofReal η := by
  obtain ⟨δ, hδ, hev⟩ := hmod 1 one_pos η hη
  set k0 : ℕ := ⌈2 * T / δ⌉₊ with hk0
  refine ⟨k0 + 1, by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop ⌈2 / δ⌉₊, eventually_ge_atTop 1] with n hn hn2 hn1
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨l, hlT, hlM⟩
  by_contra hcon
  simp only [Set.mem_setOf_eq, not_exists, not_and, not_le] at hcon
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hδn : 2 ≤ δ * n := by
    have h1 : 2 / δ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn2)
    rw [div_le_iff₀ hδ] at h1; linarith
  set d : ℕ := ⌊δ * n⌋₊ with hd
  have hd1 : δ * n / 2 ≤ d := by
    have := Nat.lt_floor_add_one (δ * n); linarith
  have hdle : (d:ℝ) ≤ δ * n := Nat.floor_le (by positivity)
  have hd0 : 0 < d := by
    have : (0:ℝ) < d := by linarith
    exact_mod_cast this
  have chain : ∀ k : ℕ, ∀ l' : ℕ, l' ≤ k * d → (l':ℝ) ≤ T * n →
      |psum (ξ n) l' ω| < (k + 1) * Real.sqrt n := by
    intro k
    induction k with
    | zero =>
      intro l' hl' _
      have : l' = 0 := by simpa using hl'
      subst this
      simp [psum, hsq]
    | succ k ih =>
      intro l' hl' hlT'
      by_cases hle : l' ≤ k * d
      · have := ih l' hle hlT'
        push_cast; linarith
      · push_neg at hle
        have hi := ih (k * d) le_rfl (by
          have : ((k * d : ℕ) : ℝ) ≤ l' := by exact_mod_cast hle.le
          linarith)
        have hstep := hcon (k * d) l' hle.le (by
          have : (l':ℝ) ≤ ((k * d : ℕ) : ℝ) + d := by
            have : l' ≤ k * d + d := by rw [Nat.succ_mul] at hl'; exact hl'
            exact_mod_cast this
          linarith) hlT'
        have := abs_sub_abs_le_abs_sub (psum (ξ n) l' ω) (psum (ξ n) (k * d) ω)
        push_cast
        linarith
  have hlk : l ≤ k0 * d := by
    have h1 : (l:ℝ) ≤ k0 * d := by
      calc (l:ℝ) ≤ T * n := hlT
        _ = (2 * T / δ) * (δ * n / 2) := by field_simp
        _ ≤ k0 * d := mul_le_mul (Nat.le_ceil _) hd1 (by positivity) (by positivity)
    exact_mod_cast h1
  have := chain k0 l hlk hlT
  push_cast at hlM
  linarith

/-- no jump of size `θ √n` before time `T n`, with high probability. -/
lemma jump_small (P : ∀ n, Measure (Ωs n)) (ξ : ∀ n, ℕ → Ωs n → ℝ)
    (hmeas : ∀ n i, Measurable (ξ n i))
    (hid : ∀ n i, IdentDistrib (ξ n i) (ξ n 0) (P n) (P n))
    (hUI : ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) atTop (𝓝 0))
    (T : ℝ) (hT : 0 < T) (θ : ℝ) (hθ : 0 < θ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, P n {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ θ * Real.sqrt n < |ξ n l ω|} ≤
      ENNReal.ofReal η := by
  have h := ENNReal.Tendsto.const_mul (a := ((⌈T⌉₊ + 1 : ℕ) : ENNReal)) (hUI θ hθ)
    (Or.inr (ENNReal.natCast_ne_top _))
  rw [mul_zero] at h
  filter_upwards [(tendsto_order.1 h).2 _ (ENNReal.ofReal_pos.2 hη), eventually_ge_atTop 1]
    with n hn hn1
  refine le_trans ?_ hn.le
  have hsub : {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ θ * Real.sqrt n < |ξ n l ω|} ⊆
      ⋃ l ∈ Finset.range (⌊T * n⌋₊ + 1), {ω | θ * Real.sqrt n < |ξ n l ω|} := by
    rintro ω ⟨l, hl, h'⟩
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le
      (Nat.le_floor hl)))) h'
  calc P n {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ θ * Real.sqrt n < |ξ n l ω|}
      ≤ ∑ l ∈ Finset.range (⌊T * n⌋₊ + 1), P n {ω | θ * Real.sqrt n < |ξ n l ω|} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ∑ l ∈ Finset.range (⌊T * n⌋₊ + 1), P n {ω | θ * Real.sqrt n < |ξ n 0 ω|} :=
        Finset.sum_congr rfl fun l _ =>
          (hid n l).measure_mem_eq (measurableSet_lt measurable_const continuous_abs.measurable)
    _ = ((⌊T * n⌋₊ + 1 : ℕ) : ENNReal) * P n {ω | θ * Real.sqrt n < |ξ n 0 ω|} := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((⌈T⌉₊ + 1 : ℕ) : ENNReal) * ((n : ENNReal) * P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) := by
        rw [← mul_assoc]
        gcongr
        have hnpos : (1:ℝ) ≤ n := by exact_mod_cast hn1
        have h1 : ((⌊T * n⌋₊ + 1 : ℕ) : ℝ) ≤ ((⌈T⌉₊ + 1 : ℕ) : ℝ) * n := by
          push_cast
          have := Nat.floor_le (by positivity : 0 ≤ T * n)
          have h2 : T * n ≤ ⌈T⌉₊ * n := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by linarith)
          nlinarith
        exact_mod_cast h1

/-- renewal counting function `max {l | F l ≤ b}`. -/
noncomputable def cnt (F : ℕ → ℝ) (b : ℝ) : ℕ := sSup {l | F l ≤ b}

lemma cnt_spec {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F)
    (hFt : Tendsto F atTop atTop) {b : ℝ} (hb : 0 ≤ b) :
    F (cnt F b) ≤ b ∧ b < F (cnt F b + 1) := by
  obtain ⟨L, hL⟩ := (hFt.eventually (eventually_gt_atTop b)).exists
  have hbdd : BddAbove {l | F l ≤ b} := ⟨L, fun l (hl : F l ≤ b) => by
    by_contra h; push_neg at h; linarith [hFm h]⟩
  have hne : ({l | F l ≤ b} : Set ℕ).Nonempty := ⟨0, by show F 0 ≤ b; rw [hF0]; exact hb⟩
  refine ⟨Nat.sSup_mem hne hbdd, ?_⟩
  by_contra h; push_neg at h
  have := le_csSup hbdd (show F (sSup {l | F l ≤ b} + 1) ≤ b from h)
  unfold cnt at *
  omega

lemma cnt_mono {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F)
    (hFt : Tendsto F atTop atTop) {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    cnt F b ≤ cnt F b' := by
  have h1 := cnt_spec hF0 hFm hFt hb
  have h2 := cnt_spec hF0 hFm hFt (hb.trans hbb)
  have := hFm.lt_iff_lt.1 (lt_of_le_of_lt (h1.1.trans hbb) h2.2)
  omega

/-- scalar modulus tightness on `[0,1]`. -/
def MT (P : ∀ n, Measure (Ωs n)) (X : ∀ n, Ωs n → ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
    P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
      ε ≤ |X n ω s - X n ω t|} ≤ ENNReal.ofReal η

/-- deterministic renewal inversion: on the good event, the scaled centred counting process has
small oscillation. -/
lemma renewal_core (F W ξv : ℕ → ℝ) (m : ℝ) (hm : 0 < m) (hF : ∀ l, F l = l * m + W l)
    (hξv : ∀ l, F (l + 1) - F l = m + ξv l) (hF0 : F 0 = 0) (hFm : StrictMono F)
    (hFt : Tendsto F atTop atTop) (n : ℕ) (hn : 1 ≤ n)
    (μb T M θ εr δr ε : ℝ) (hmμ : m⁻¹ ≤ μb) (hT : T = 2 * μb + 2) (hM0 : 0 < M)
    (hθ0 : 0 ≤ θ) (hδr : 0 < δr)
    (hMω : ∀ l : ℕ, (l:ℝ) ≤ T * n → |W l| < M * Real.sqrt n)
    (hJω : ∀ l : ℕ, (l:ℝ) ≤ T * n → |ξv l| ≤ θ * Real.sqrt n)
    (hRω : ∀ i j : ℕ, i ≤ j → (j:ℝ) ≤ i + δr * n → (j:ℝ) ≤ T * n →
      |W j - W i| < εr * Real.sqrt n)
    (hMn : M ^ 2 < n) (hl3 : 1 + μb * (θ + 2 * M) * Real.sqrt n ≤ δr * n / 2)
    (hsmall : (Real.sqrt n)⁻¹ + μb * εr + μb * θ < ε)
    {s t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) (hts : t ≤ s)
    (hst : s - t ≤ δr / (2 * μb)) :
    |(Real.sqrt n)⁻¹ * ((cnt F (n * s) : ℝ) - m⁻¹ * (n * s)) -
      (Real.sqrt n)⁻¹ * ((cnt F (n * t) : ℝ) - m⁻¹ * (n * t))| < ε := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  have hμb : 0 < μb := lt_of_lt_of_le (inv_pos.2 hm) hmμ
  have hμm : 1 ≤ μb * m := by
    have := mul_le_mul_of_nonneg_right hmμ hm.le
    rwa [inv_mul_cancel₀ hm.ne'] at this
  have hMlt : M * Real.sqrt n < n := by
    have hM : M < Real.sqrt n := by
      rw [show M = Real.sqrt (M ^ 2) from (Real.sqrt_sq hM0.le).symm]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hMn
    nlinarith
  have hnt : 0 ≤ (n:ℝ) * t := mul_nonneg hnpos.le ht.1
  have hns : 0 ≤ (n:ℝ) * s := mul_nonneg hnpos.le hs.1
  set i := cnt F (n * t) with hi
  set j := cnt F (n * s) with hj
  have hspi := cnt_spec hF0 hFm hFt hnt
  have hspj := cnt_spec hF0 hFm hFt hns
  have hij : i ≤ j := cnt_mono hF0 hFm hFt hnt (mul_le_mul_of_nonneg_left hts hnpos.le)
  -- step A: `j + 1 ≤ T n`
  have hjT : ((j + 1 : ℕ) : ℝ) ≤ T * n := by
    set l0 := ⌈2 * μb * n⌉₊ with hl0
    have hl0r : (l0:ℝ) ≤ 2 * μb * n + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hl0T : (l0:ℝ) ≤ T * n := by rw [hT]; nlinarith
    have hFl0 : (n:ℝ) < F l0 := by
      rw [hF l0]
      have h1 : 2 * μb * n ≤ l0 := Nat.le_ceil _
      have h2 : 2 * (n:ℝ) ≤ l0 * m := by
        calc 2 * (n:ℝ) ≤ 2 * n * (μb * m) := by nlinarith
          _ = (2 * μb * n) * m := by ring
          _ ≤ l0 * m := mul_le_mul_of_nonneg_right h1 hm.le
      have h3 := (abs_lt.1 (hMω l0 hl0T)).1
      linarith
    have hcn := cnt_spec hF0 hFm hFt hnpos.le
    have hjn : j ≤ cnt F n := by
      have := cnt_mono hF0 hFm hFt hns (b' := n) (by nlinarith [hs.2])
      simpa using this
    have hlt : cnt F n < l0 := hFm.lt_iff_lt.1 (lt_of_le_of_lt hcn.1 hFl0)
    have : j + 1 ≤ l0 := by omega
    calc ((j + 1 : ℕ) : ℝ) ≤ l0 := by exact_mod_cast this
      _ ≤ T * n := hl0T
  have hjT' : (j:ℝ) ≤ T * n := by push_cast at hjT; linarith
  have hiT' : (i:ℝ) ≤ T * n := (by exact_mod_cast hij : (i:ℝ) ≤ j).trans hjT'
  -- residuals
  set Rt := (n:ℝ) * t - F i with hRt
  set Rs := (n:ℝ) * s - F j with hRs
  have hRt0 : 0 ≤ Rt := by linarith [hspi.1]
  have hRs0 : 0 ≤ Rs := by linarith [hspj.1]
  have hRt1 : Rt ≤ m + θ * Real.sqrt n := by
    have := hξv i
    have := hJω i hiT'
    linarith [hspi.2, le_abs_self (ξv i)]
  have hRs1 : Rs ≤ m + θ * Real.sqrt n := by
    have := hξv j
    have := hJω j hjT'
    linarith [hspj.2, le_abs_self (ξv j)]
  have hFi := hF i
  have hFj := hF j
  -- the gap `j - i`
  have hWi := hMω i hiT'
  have hWj := hMω j hjT'
  have hgap : (j:ℝ) ≤ i + δr * n := by
    have h1 : ((j:ℝ) - i) * m = (n:ℝ) * (s - t) - (Rs - Rt) - (W j - W i) := by
      rw [hRs, hRt, hFi, hFj]; ring
    have h2 : (n:ℝ) * (s - t) - (Rs - Rt) - (W j - W i) ≤
        (n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n) + m := by
      have := mul_le_mul_of_nonneg_left hst hnpos.le
      have h3 := abs_lt.1 hWi
      have h4 := abs_lt.1 hWj
      have e5 : (θ + 2 * M) * Real.sqrt n = θ * Real.sqrt n + 2 * (M * Real.sqrt n) := by ring
      rw [e5]
      linarith [h3.1, h3.2, h4.1, h4.2]
    have hA0 : 0 ≤ n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n := by positivity
    have h3 : (j:ℝ) - i ≤ μb * (n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n) + 1 := by
      have e1 : (j:ℝ) - i = m⁻¹ * (((j:ℝ) - i) * m) := by field_simp
      rw [e1, h1]
      calc m⁻¹ * ((n:ℝ) * (s - t) - (Rs - Rt) - (W j - W i))
          ≤ m⁻¹ * ((n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n) + m) :=
            mul_le_mul_of_nonneg_left h2 (inv_pos.2 hm).le
        _ = m⁻¹ * (n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n) + 1 := by
            rw [mul_add, inv_mul_cancel₀ hm.ne']
        _ ≤ μb * (n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n) + 1 := by
            gcongr
    have h4 : μb * (n * (δr / (2 * μb)) + (θ + 2 * M) * Real.sqrt n) =
        δr * n / 2 + μb * (θ + 2 * M) * Real.sqrt n := by field_simp
    linarith
  have hW := hRω i j hij hgap hjT'
  have hεr : 0 ≤ εr := by
    by_contra hneg
    push_neg at hneg
    have h1 := (abs_nonneg _).trans_lt hW
    have h2 := mul_neg_of_neg_of_pos hneg hsq
    linarith
  have es : (n:ℝ) * s = j * m + W j + Rs := by rw [hRs, hFj]; ring
  have et : (n:ℝ) * t = i * m + W i + Rt := by rw [hRt, hFi]; ring
  have e : (Real.sqrt n)⁻¹ * ((j:ℝ) - m⁻¹ * (n * s)) - (Real.sqrt n)⁻¹ * ((i:ℝ) - m⁻¹ * (n * t)) =
      -((Real.sqrt n)⁻¹ * m⁻¹) * ((W j - W i) + (Rs - Rt)) := by
    rw [es, et]; field_simp; ring
  rw [e, abs_mul, abs_neg, abs_of_pos (by positivity)]
  have hRd : |Rs - Rt| ≤ m + θ * Real.sqrt n := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have hsum : |(W j - W i) + (Rs - Rt)| ≤ εr * Real.sqrt n + (m + θ * Real.sqrt n) :=
    (abs_add_le _ _).trans (add_le_add hW.le hRd)
  calc (Real.sqrt n)⁻¹ * m⁻¹ * |(W j - W i) + (Rs - Rt)|
      ≤ (Real.sqrt n)⁻¹ * m⁻¹ * (εr * Real.sqrt n + (m + θ * Real.sqrt n)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = m⁻¹ * εr + (Real.sqrt n)⁻¹ + m⁻¹ * θ := by field_simp; ring
    _ ≤ μb * εr + (Real.sqrt n)⁻¹ + μb * θ := by
        have h1 := mul_le_mul_of_nonneg_right hmμ hεr
        have h2 := mul_le_mul_of_nonneg_right hmμ hθ0
        linarith
    _ < ε := by linarith

/-- tightness of the scaled centred renewal counting process of a triangular array. -/
lemma renewal_tight (P : ∀ n, Measure (Ωs n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (v : ∀ n, ℕ → Ωs n → ℝ) (hind : ∀ n, iIndepFun (v n) (P n))
    (hmeas : ∀ n i, Measurable (v n i)) (hid : ∀ n i, IdentDistrib (v n i) (v n 0) (P n) (P n))
    (hL2 : ∀ n, MemLp (v n 0) 2 (P n)) (hpos : ∀ n i ω, 0 < v n i ω)
    (hdiv : ∀ n, ∀ᵐ ω ∂(P n), Tendsto (fun l => psum (v n) l ω) atTop atTop)
    (a : ℝ) (ha : 0 < a) (hm : ∀ᶠ n in atTop, a ≤ ∫ ω, v n 0 ω ∂(P n))
    (σ2 : ℝ) (hσ : ∀ᶠ n in atTop,
      ∫ ω, (v n 0 ω - ∫ ω', v n 0 ω' ∂(P n)) ^ 2 ∂(P n) ≤ σ2)
    (hUI : ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |v n 0 ω - ∫ ω', v n 0 ω' ∂(P n)|}) atTop (𝓝 0)) :
    MT P (fun n ω t => (Real.sqrt n)⁻¹ * ((cnt (fun l => psum (v n) l ω) (n * t) : ℝ) -
      (∫ ω', v n 0 ω' ∂(P n))⁻¹ * (n * t))) := by
  intro ε hε η hη
  set m : ℕ → ℝ := fun n => ∫ ω', v n 0 ω' ∂(P n) with hmdef
  set ξ : ∀ n, ℕ → Ωs n → ℝ := fun n i => (fun x => x - m n) ∘ v n i with hξdef
  have hξind : ∀ n, iIndepFun (ξ n) (P n) := fun n =>
    (hind n).comp (fun _ x => x - m n) (fun _ => measurable_id.sub_const _)
  have hξm : ∀ n i, Measurable (ξ n i) := fun n i => (measurable_id.sub_const _).comp (hmeas n i)
  have hξid : ∀ n i, IdentDistrib (ξ n i) (ξ n 0) (P n) (P n) := fun n i =>
    (hid n i).comp (measurable_id.sub_const _)
  have hξL2 : ∀ n, MemLp (ξ n 0) 2 (P n) := fun n => (hL2 n).sub (memLp_const (m n))
  have hξ0 : ∀ n, ∫ ω, ξ n 0 ω ∂(P n) = 0 := by
    intro n
    have := hP n
    show ∫ ω, (v n 0 ω - m n) ∂(P n) = 0
    rw [integral_sub ((hL2 n).integrable one_le_two) (integrable_const _), integral_const,
      probReal_univ, one_smul]
    exact sub_self _
  have hξσ : ∀ᶠ n in atTop, ∫ ω, ξ n 0 ω ^ 2 ∂(P n) ≤ σ2 := hσ
  have hξUI : ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) atTop (𝓝 0) := hUI
  set μb := a⁻¹ with hμbdef
  have hμb : 0 < μb := inv_pos.2 ha
  set T := 2 * μb + 2 with hTdef
  have hT : 0 < T := by positivity
  have hmod := fun ε hε η hη =>
    rw_tight P hP ξ hξind hξm hξid hξL2 hξ0 σ2 hξσ hξUI T hT ε hε η hη
  obtain ⟨M, hM0, hMev⟩ := rw_bdd P hP ξ T hmod hT (η / 4) (by linarith)
  set θ := ε / (8 * μb) with hθdef
  have hθ : 0 < θ := by positivity
  have hJ := jump_small P ξ hξm hξid hξUI T hT θ hθ (η / 4) (by linarith)
  set εr := ε / (4 * μb) with hεrdef
  obtain ⟨δr, hδr, hrw⟩ := hmod εr (by positivity) (η / 4) (by linarith)
  refine ⟨δr / (2 * μb), by positivity, ?_⟩
  set c := μb * (θ + 2 * M) with hc
  have hsqt := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hl3 : ∀ᶠ n : ℕ in atTop, 1 + c * Real.sqrt n ≤ δr * n / 2 := by
    filter_upwards [hsqt.eventually_ge_atTop (max 1 (2 * (1 + c) / δr)),
      eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    simp only [Function.comp] at hn
    have h1 : 1 ≤ Real.sqrt n := (le_max_left _ _).trans hn
    have h2 : 2 * (1 + c) / δr ≤ Real.sqrt n := (le_max_right _ _).trans hn
    have hc0 : 0 ≤ c := by positivity
    rw [div_le_iff₀ hδr] at h2
    nlinarith
  have hl1 : ∀ᶠ n : ℕ in atTop, (Real.sqrt n)⁻¹ ≤ ε / 4 := by
    filter_upwards [hsqt.eventually_ge_atTop (4 / ε)] with n hn
    simp only [Function.comp] at hn
    rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) hn) (by positivity), inv_div]
    exact hn
  have hl2 : ∀ᶠ n : ℕ in atTop, M ^ 2 < n :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hMev.and (hJ.and (hrw.and (hm.and (hl1.and
    (hl2.and (hl3.and (eventually_ge_atTop 1))))))))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hMn, hJn, hrwn, hmn, hl1n, hl2n, hl3n, hn1⟩ := hN n hn
  have := hP n
  have hmpos : 0 < m n := lt_of_lt_of_le ha hmn
  have hmμ : (m n)⁻¹ ≤ μb := inv_anti₀ ha hmn
  set BadM := {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ M * Real.sqrt n ≤ |psum (ξ n) l ω|}
  set BadJ := {ω | ∃ l : ℕ, (l:ℝ) ≤ T * n ∧ θ * Real.sqrt n < |ξ n l ω|}
  set BadR := {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δr * n ∧ (j:ℝ) ≤ T * n ∧
    εr * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|}
  set BadD := {ω | ¬ Tendsto (fun l => psum (v n) l ω) atTop atTop}
  have hsub : {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δr / (2 * μb) ∧
      ε ≤ |(Real.sqrt n)⁻¹ * ((cnt (fun l => psum (v n) l ω) (n * s) : ℝ) - (m n)⁻¹ * (n * s)) -
        (Real.sqrt n)⁻¹ * ((cnt (fun l => psum (v n) l ω) (n * t) : ℝ) -
          (m n)⁻¹ * (n * t))|} ⊆ BadD ∪ (BadM ∪ (BadJ ∪ BadR)) := by
    rintro ω ⟨s, hs, t, ht, hst, hX⟩
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨hD, hM', hJ', hR'⟩ := hcon
    have hdivω : Tendsto (fun l => psum (v n) l ω) atTop atTop := by
      by_contra h; exact hD h
    have hMω : ∀ l : ℕ, (l:ℝ) ≤ T * n → |psum (ξ n) l ω| < M * Real.sqrt n := by
      intro l hl; by_contra h; push_neg at h; exact hM' ⟨l, hl, h⟩
    have hJω : ∀ l : ℕ, (l:ℝ) ≤ T * n → |ξ n l ω| ≤ θ * Real.sqrt n := by
      intro l hl; by_contra h; push_neg at h; exact hJ' ⟨l, hl, h⟩
    have hRω : ∀ i j : ℕ, i ≤ j → (j:ℝ) ≤ i + δr * n → (j:ℝ) ≤ T * n →
        |psum (ξ n) j ω - psum (ξ n) i ω| < εr * Real.sqrt n := by
      intro i j h1 h2 h3; by_contra h; push_neg at h; exact hR' ⟨i, j, h1, h2, h3, h⟩
    have hF : ∀ l, psum (v n) l ω = l * m n + psum (ξ n) l ω := by
      intro l
      simp only [psum, hξdef, Function.comp, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring
    have hξv : ∀ l, psum (v n) (l + 1) ω - psum (v n) l ω = m n + ξ n l ω := by
      intro l
      simp only [psum, Finset.sum_range_succ, hξdef, Function.comp]
      ring
    have hF0 : psum (v n) 0 ω = 0 := by simp [psum]
    have hFm : StrictMono fun l => psum (v n) l ω :=
      strictMono_nat_of_lt_succ fun l => by
        simp only [psum, Finset.sum_range_succ]; linarith [hpos n l ω]
    have hsmall : (Real.sqrt n)⁻¹ + μb * εr + μb * θ < ε := by
      have e1 : μb * εr = ε / 4 := by rw [hεrdef]; field_simp
      have e2 : μb * θ = ε / 8 := by rw [hθdef]; field_simp
      linarith
    rcases le_total t s with hts | hst'
    · have := renewal_core (fun l => psum (v n) l ω) (fun l => psum (ξ n) l ω)
        (fun l => ξ n l ω) (m n) hmpos hF hξv hF0 hFm hdivω n hn1 μb T M θ εr δr ε hmμ rfl hM0
        hθ.le hδr hMω hJω hRω hl2n hl3n hsmall ht hs hts (by rw [abs_le] at hst; linarith)
      linarith
    · have := renewal_core (fun l => psum (v n) l ω) (fun l => psum (ξ n) l ω)
        (fun l => ξ n l ω) (m n) hmpos hF hξv hF0 hFm hdivω n hn1 μb T M θ εr δr ε hmμ rfl hM0
        hθ.le hδr hMω hJω hRω hl2n hl3n hsmall hs ht hst' (by rw [abs_le] at hst; linarith)
      rw [abs_sub_comm] at this
      linarith
  calc _ ≤ P n (BadD ∪ (BadM ∪ (BadJ ∪ BadR))) := measure_mono hsub
    _ ≤ P n BadD + (P n BadM + (P n BadJ + P n BadR)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl ((measure_union_le _ _).trans
          (add_le_add le_rfl (measure_union_le _ _))))
    _ ≤ 0 + (ENNReal.ofReal (η / 4) + (ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4))) :=
        add_le_add (le_of_eq (ae_iff.1 (hdiv n))) (add_le_add hMn (add_le_add hJn hrwn))
    _ ≤ ENNReal.ofReal η := by
        rw [zero_add, ← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        exact ENNReal.ofReal_le_ofReal (by linarith)

lemma MT.add {P : ∀ n, Measure (Ωs n)} {X Y : ∀ n, Ωs n → ℝ → ℝ} (hX : MT P X) (hY : MT P Y) :
    MT P (fun n ω t => X n ω t + Y n ω t) := by
  intro ε hε η hη
  obtain ⟨δ1, hδ1, N1, hN1⟩ := hX (ε / 2) (by linarith) (η / 2) (by linarith)
  obtain ⟨δ2, hδ2, N2, hN2⟩ := hY (ε / 2) (by linarith) (η / 2) (by linarith)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, max N1 N2, fun n hn => ?_⟩
  have hsub : {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ min δ1 δ2 ∧
      ε ≤ |(X n ω s + Y n ω s) - (X n ω t + Y n ω t)|} ⊆
      {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ1 ∧
        ε / 2 ≤ |X n ω s - X n ω t|} ∪
      {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ2 ∧
        ε / 2 ≤ |Y n ω s - Y n ω t|} := by
    rintro ω ⟨s, hs, t, ht, hst, hle⟩
    have htri : |(X n ω s + Y n ω s) - (X n ω t + Y n ω t)| ≤
        |X n ω s - X n ω t| + |Y n ω s - Y n ω t| := by
      rw [add_sub_add_comm]; exact abs_add_le _ _
    by_cases h1 : ε / 2 ≤ |X n ω s - X n ω t|
    · left; exact ⟨s, hs, t, ht, hst.trans (min_le_left _ _), h1⟩
    · right
      refine ⟨s, hs, t, ht, hst.trans (min_le_right _ _), ?_⟩
      push_neg at h1; linarith
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        add_le_add (hN1 n (le_of_max_le_left hn)) (hN2 n (le_of_max_le_right hn))
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

lemma MT.const_mul {P : ∀ n, Measure (Ωs n)} {X : ∀ n, Ωs n → ℝ → ℝ} (hX : MT P X) (c : ℝ) :
    MT P (fun n ω t => c * X n ω t) := by
  intro ε hε η hη
  obtain ⟨δ, hδ, N, hN⟩ := hX (ε / (|c| + 1)) (by positivity) η hη
  refine ⟨δ, hδ, N, fun n hn => le_trans (measure_mono ?_) (hN n hn)⟩
  rintro ω ⟨s, hs, t, ht, hst, hle⟩
  refine ⟨s, hs, t, ht, hst, ?_⟩
  rw [← mul_sub, abs_mul] at hle
  rw [div_le_iff₀ (by positivity)]
  nlinarith [abs_nonneg c, abs_nonneg (X n ω s - X n ω t)]

lemma MT.zero {P : ∀ n, Measure (Ωs n)} : MT P (fun _ _ _ => (0:ℝ)) := by
  intro ε hε η hη
  refine ⟨1, one_pos, 0, fun n _ => ?_⟩
  refine le_trans (measure_mono (show _ ⊆ (∅ : Set (Ωs n)) from ?_)) (by simp)
  rintro ω ⟨s, -, t, -, -, hle⟩
  simp only [sub_self, abs_zero] at hle
  linarith

lemma MT.congr {P : ∀ n, Measure (Ωs n)} {X Y : ∀ n, Ωs n → ℝ → ℝ} (hX : MT P X)
    (h : ∀ n ω, ∀ t ∈ Set.Icc (0:ℝ) 1, X n ω t = Y n ω t) : MT P Y := by
  intro ε hε η hη
  obtain ⟨δ, hδ, N, hN⟩ := hX ε hε η hη
  refine ⟨δ, hδ, N, fun n hn => le_trans (measure_mono ?_) (hN n hn)⟩
  rintro ω ⟨s, hs, t, ht, hst, hle⟩
  exact ⟨s, hs, t, ht, hst, by rw [h n ω s hs, h n ω t ht]; exact hle⟩

/-- modulus tightness with value `0` at `0` gives boundedness in probability on `[0,1]`. -/
lemma MT_bdd {P : ∀ n, Measure (Ωs n)} {X : ∀ n, Ωs n → ℝ → ℝ} (hT : MT P X)
    (h0 : ∀ n ω, X n ω 0 = 0) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, M < |X n ω s|} ≤ ENNReal.ofReal η := by
  obtain ⟨δ, hδ, N, hN⟩ := hT 1 one_pos η hη
  set m : ℕ := ⌈1 / δ⌉₊ + 1 with hm
  have hm0 : (0:ℝ) < m := by positivity
  have hmδ : 1 / (m:ℝ) ≤ δ := by
    rw [div_le_iff₀ hm0]
    have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (m:ℝ) = ⌈1 / δ⌉₊ + 1 := by rw [hm]; push_cast; ring
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  refine ⟨m, hm0, N, fun n hn => le_trans (measure_mono ?_) (hN n hn)⟩
  intro ω hω
  obtain ⟨s, hs, hlt⟩ := hω
  by_contra hcon
  simp only [Set.mem_setOf_eq, not_exists, not_and, not_le] at hcon
  have step : ∀ j : ℕ, j ≤ m → |X n ω (s * j / m)| ≤ j := by
    intro j
    induction j with
    | zero => intro _; simp [h0]
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hmem : ∀ i : ℕ, i ≤ m → s * i / m ∈ Set.Icc (0:ℝ) 1 := by
        intro i hi
        have hi' : (i:ℝ) ≤ m := by exact_mod_cast hi
        refine ⟨by have := hs.1; positivity, ?_⟩
        rw [div_le_one hm0]
        nlinarith [hs.1, hs.2]
      have hd : |s * ((j + 1 : ℕ) : ℝ) / m - s * j / m| ≤ δ := by
        have e : s * ((j + 1 : ℕ) : ℝ) / m - s * j / m = s * (1 / m) := by
          push_cast; field_simp; ring
        rw [e, abs_of_nonneg (by have := hs.1; positivity)]
        calc s * (1 / (m:ℝ)) ≤ 1 * (1 / m) :=
              mul_le_mul_of_nonneg_right hs.2 (by positivity)
          _ ≤ δ := by rw [one_mul]; exact hmδ
      have hlt1 := hcon _ (hmem (j+1) hj) _ (hmem j (by omega)) hd
      have := abs_sub_abs_le_abs_sub (X n ω (s * ((j + 1 : ℕ) : ℝ) / m)) (X n ω (s * j / m))
      push_cast at this hlt1 ⊢
      linarith
  have := step m le_rfl
  have e : s * (m:ℝ) / m = s := by field_simp
  rw [e] at this
  linarith

/-- the partial-sum walk evaluated at a random time that is bounded and fluid. -/
lemma randtime_tight (P : ∀ n, Measure (Ωs n)) (ξ : ∀ n, ℕ → Ωs n → ℝ)
    (hmod : ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n : ℕ in atTop, P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧ (j:ℝ) ≤ T * n ∧
        ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ≤ ENNReal.ofReal η)
    (Nc : ∀ n, Ωs n → ℝ → ℕ)
    (hbd : ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | ∃ t ∈ Set.Icc (0:ℝ) 1, T * n < Nc n ω t} ≤ ENNReal.ofReal η)
    (hfl : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
        ε * n < |(Nc n ω s : ℝ) - Nc n ω t|} ≤ ENNReal.ofReal η) :
    MT P (fun n ω t => (Real.sqrt n)⁻¹ * psum (ξ n) (Nc n ω t) ω) := by
  intro ε hε η hη
  obtain ⟨T, hT, hTev⟩ := hbd (η / 3) (by linarith)
  obtain ⟨δr, hδr, hrw⟩ := hmod T hT ε hε (η / 3) (by linarith)
  obtain ⟨δ, hδ, hfev⟩ := hfl δr hδr (η / 3) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hTev.and (hrw.and (hfev.and (eventually_ge_atTop 1))))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2, h3, hn1⟩ := hN n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsub : {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
      ε ≤ |(Real.sqrt n)⁻¹ * psum (ξ n) (Nc n ω s) ω - (Real.sqrt n)⁻¹ * psum (ξ n) (Nc n ω t) ω|}
      ⊆ {ω | ∃ t ∈ Set.Icc (0:ℝ) 1, T * n < Nc n ω t} ∪
        ({ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δr * n ∧ (j:ℝ) ≤ T * n ∧
          ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ∪
        {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
          δr * n < |(Nc n ω s : ℝ) - Nc n ω t|}) := by
    rintro ω ⟨s, hs, t, ht, hst, hle⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and, not_lt,
      not_le] at hcon
    obtain ⟨hA, hB, hC⟩ := hcon
    have hgap := hC s hs t ht hst
    have hle' : ε * Real.sqrt n ≤ |psum (ξ n) (Nc n ω s) ω - psum (ξ n) (Nc n ω t) ω| := by
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hsq)] at hle
      rwa [le_inv_mul_iff₀ hsq, mul_comm] at hle
    rcases le_total (Nc n ω t) (Nc n ω s) with hts | hts
    · have := hB (Nc n ω t) (Nc n ω s) hts (by
        have := (abs_le.1 hgap).1; have := (abs_le.1 hgap).2; linarith) (hA s hs)
      linarith
    · have := hB (Nc n ω s) (Nc n ω t) hts (by
        have := (abs_le.1 hgap).1; have := (abs_le.1 hgap).2; linarith) (hA t ht)
      rw [abs_sub_comm] at this
      linarith
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ENNReal.ofReal (η / 3) + (ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3)) :=
        add_le_add h1 (add_le_add h2 h3)
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1; ring

/-- a counting process whose scaled centred version is modulus-tight is bounded by `T n` and
fluid. -/
lemma bd_fl_of_MT (P : ∀ n, Measure (Ωs n)) (Nc : ∀ n, Ωs n → ℝ → ℕ) (μ : ℕ → ℝ) (μb : ℝ)
    (hμ0 : ∀ n, 0 ≤ μ n) (hμb : ∀ᶠ n in atTop, μ n ≤ μb)
    (hX : MT P (fun n ω t => (Real.sqrt n)⁻¹ * ((Nc n ω t : ℝ) - μ n * (n * t))))
    (h0 : ∀ n ω, Nc n ω 0 = 0) :
    (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | ∃ t ∈ Set.Icc (0:ℝ) 1, T * n < Nc n ω t} ≤ ENNReal.ofReal η) ∧
    (∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
        ε * n < |(Nc n ω s : ℝ) - Nc n ω t|} ≤ ENNReal.ofReal η) := by
  have hμb0 : ∀ᶠ n in atTop, 0 ≤ μb := hμb.mono fun n h => (hμ0 n).trans h
  constructor
  · intro η hη
    obtain ⟨M, hM, N, hN⟩ := MT_bdd hX (fun n ω => by simp [h0]) η hη
    refine ⟨max μb 0 + M + 1, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1, hμb] with n hn hn1 hμn
    refine le_trans (measure_mono ?_) (hN n hn)
    rintro ω ⟨t, ht, hlt⟩
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_exists, not_and, not_lt] at hcon
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    have hsqn : Real.sqrt n ≤ n := by
      have hs1 : 1 ≤ Real.sqrt n := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hn1'
      have h1 : Real.sqrt n * 1 ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left hs1 hsq.le
      linarith [Real.mul_self_sqrt hnpos.le]
    have h1 := hcon t ht
    have h2 : (Nc n ω t : ℝ) - μ n * (n * t) ≤ M * Real.sqrt n := by
      have := (abs_le.1 h1).2
      rw [inv_mul_le_iff₀ hsq] at this
      linarith
    have h3 : μ n * (n * t) ≤ max μb 0 * n := by
      have : n * t ≤ n := by nlinarith [ht.2]
      calc μ n * (n * t) ≤ μb * (n * t) := mul_le_mul_of_nonneg_right hμn (by nlinarith [ht.1])
        _ ≤ max μb 0 * (n * t) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by nlinarith [ht.1])
        _ ≤ max μb 0 * n := mul_le_mul_of_nonneg_left this (le_max_right _ _)
    nlinarith
  · intro ε hε η hη
    obtain ⟨δ0, hδ0, N, hN⟩ := hX 1 one_pos η hη
    refine ⟨min δ0 (ε / (2 * (max μb 0 + 1))), lt_min hδ0 (by positivity), ?_⟩
    have hsqt := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1, hμb,
      hsqt.eventually_ge_atTop (4 / ε)] with n hn hn1 hμn hsqn
    refine le_trans (measure_mono ?_) (hN n hn)
    rintro ω ⟨s, hs, t, ht, hst, hlt⟩
    refine ⟨s, hs, t, ht, hst.trans (min_le_left _ _), ?_⟩
    by_contra hcon
    push_neg at hcon
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    simp only [Function.comp] at hsqn
    have e : (Real.sqrt n)⁻¹ * ((Nc n ω s : ℝ) - μ n * (n * s)) -
        (Real.sqrt n)⁻¹ * ((Nc n ω t : ℝ) - μ n * (n * t)) =
        (Real.sqrt n)⁻¹ * (((Nc n ω s : ℝ) - Nc n ω t) - μ n * n * (s - t)) := by ring
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hsq), inv_mul_lt_iff₀ hsq, mul_one] at hcon
    have hst' : |s - t| ≤ ε / (2 * (max μb 0 + 1)) := hst.trans (min_le_right _ _)
    have hdr : |μ n * n * (s - t)| ≤ ε * n / 2 := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hμ0 n) hnpos.le)]
      calc μ n * n * |s - t| ≤ (max μb 0 + 1) * n * (ε / (2 * (max μb 0 + 1))) := by
            gcongr
            exact (hμn.trans (le_max_left _ _)).trans (by linarith)
        _ = ε * n / 2 := by field_simp
    have hsq2 : Real.sqrt n ≤ ε * n / 4 := by
      rw [div_le_iff₀ hε] at hsqn
      nlinarith
    have := abs_sub_abs_le_abs_sub ((Nc n ω s : ℝ) - Nc n ω t) (μ n * n * (s - t))
    linarith

/-- the jump condition from a uniform `p`-th moment bound, `p > 2`, for positive variables
with bounded means. -/
lemma hUI_of_moment (P : ∀ n, Measure (Ωs n)) (w : ∀ n, Ωs n → ℝ)
    (hmeas : ∀ n, Measurable (w n)) (hpos : ∀ n ω, 0 < w n ω) (m : ℕ → ℝ)
    (hm0 : ∀ n, 0 ≤ m n) (Bm : ℝ) (hm : ∀ᶠ n in atTop, m n ≤ Bm) (p : ℝ) (hp : 2 < p)
    (C : ℝ) (hC : ∀ᶠ n in atTop, ∫⁻ ω, ENNReal.ofReal (w n ω ^ p) ∂(P n) ≤ ENNReal.ofReal C) :
    ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |w n ω - m n|}) atTop (𝓝 0) := by
  intro θ hθ
  set C' := max C 0 * (2 / θ) ^ p with hC'
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C' * (n:ℝ) ^ (-(p / 2 - 1)))) atTop
      (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop (by linarith : 0 < p / 2 - 1)).comp
      tendsto_natCast_atTop_atTop
    have h2 := (h1.const_mul C')
    rw [mul_zero] at h2
    have := ENNReal.tendsto_ofReal h2
    rwa [ENNReal.ofReal_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => bot_le) ?_
  have hsqt := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hm, hC, eventually_ge_atTop 1, hsqt.eventually_ge_atTop (2 * max Bm 0 / θ)]
    with n hmn hCn hn1 hsqn
  simp only [Function.comp] at hsqn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  set a := θ * Real.sqrt n / 2 with ha
  have ha0 : 0 < a := by positivity
  have hsub : {ω | θ * Real.sqrt n < |w n ω - m n|} ⊆
      {ω | ENNReal.ofReal (a ^ p) ≤ ENNReal.ofReal (w n ω ^ p)} := by
    intro ω hω
    have hw := hpos n ω
    have h1 : |w n ω - m n| ≤ w n ω + m n := by
      rw [abs_le]; constructor <;> linarith [hm0 n]
    have h2 : m n ≤ a := by
      have : 2 * max Bm 0 ≤ θ * Real.sqrt n := by
        have h := hsqn
        rw [div_le_iff₀ hθ] at h
        linarith
      rw [ha]; linarith [le_max_left Bm 0]
    have h3 : a ≤ w n ω := by
      have : θ * Real.sqrt n = 2 * a := by rw [ha]; ring
      have h4 : θ * Real.sqrt n < |w n ω - m n| := hω
      linarith
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ha0.le h3 (by linarith))
  have hmark := meas_ge_le_lintegral_div
    ((ENNReal.measurable_ofReal.comp ((hmeas n).pow_const p)).aemeasurable)
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ha0 p)).ne' ENNReal.ofReal_ne_top
    (μ := P n)
  have hap : a ^ p = (θ / 2) ^ p * (n:ℝ) ^ (p / 2) := by
    rw [ha, show θ * Real.sqrt n / 2 = (θ / 2) * Real.sqrt n by ring,
      Real.mul_rpow (by positivity) hsq.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le]
    ring_nf
  calc (n : ENNReal) * P n {ω | θ * Real.sqrt n < |w n ω - m n|}
      ≤ (n : ENNReal) * ((∫⁻ ω, ENNReal.ofReal (w n ω ^ p) ∂(P n)) / ENNReal.ofReal (a ^ p)) :=
        by gcongr; exact (measure_mono hsub).trans hmark
    _ ≤ (n : ENNReal) * (ENNReal.ofReal (max C 0) / ENNReal.ofReal (a ^ p)) := by
        gcongr
        exact hCn.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (n * (max C 0 / a ^ p)) := by
        rw [ENNReal.ofReal_mul hnpos.le, ENNReal.ofReal_natCast,
          ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos ha0 p)]
    _ = ENNReal.ofReal (C' * (n:ℝ) ^ (-(p / 2 - 1))) := by
        congr 1
        have h1 : (0:ℝ) < (n:ℝ) ^ (p / 2) := Real.rpow_pos_of_pos hnpos _
        have h2 : (0:ℝ) < θ ^ p := Real.rpow_pos_of_pos hθ _
        have h3 : (0:ℝ) < (2:ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
        rw [hap, hC', show -(p / 2 - 1) = 1 - p / 2 by ring, Real.rpow_sub hnpos, Real.rpow_one,
          Real.div_rpow (by norm_num : (0:ℝ) ≤ 2) hθ.le, Real.div_rpow hθ.le (by norm_num : (0:ℝ) ≤ 2)]
        field_simp

end Tri

end RW

/-! ### Network hookups for `TightPrim` -/

namespace NetT

open MeasureTheory ProbabilityTheory Filter Topology Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)} {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω}

lemma indep_v (N : Network K J μP) (k : Fin K) : iIndepFun (fun i => N.v k i) μP := by
  rw [iIndepFun_iff_iIndep]
  exact N.indep.precomp (g := fun i : ℕ => (Sum.inr (Sum.inl (k, i)) : PrimIndex K J))
    (fun a b h => by simpa using h)

lemma indep_u (N : Network K J μP) {k : Fin K} (hk : k ∈ J) :
    iIndepFun (fun i => N.u k i) μP := by
  rw [iIndepFun_iff_iIndep]
  exact N.indep.precomp (g := fun i : ℕ => (Sum.inl (⟨k, hk⟩, i) : PrimIndex K J))
    (fun a b h => by simpa using h)

lemma indep_φ (N : Network K J μP) (k : Fin K) : iIndepFun (fun i => N.φ k i) μP := by
  rw [iIndepFun_iff_iIndep]
  exact N.indep.precomp (g := fun i : ℕ => (Sum.inr (Sum.inr (k, i)) : PrimIndex K J))
    (fun a b h => by simpa using h)

lemma integral_pos_of_pos [IsProbabilityMeasure μP] {f : Ω → ℝ} (hf : ∀ ω, 0 < f ω)
    (hint : Integrable f μP) : 0 < ∫ ω, f ω ∂μP := by
  rw [integral_pos_iff_support_of_nonneg (fun ω => (hf ω).le) hint]
  have : Function.support f = Set.univ := Set.eq_univ_of_forall fun ω => (hf ω).ne'
  rw [this, measure_univ]; exact one_pos

/-- a uniform `p`-th moment bound (`p ≥ 1`) bounds the mean. -/
lemma mean_le_of_moment [IsProbabilityMeasure μP] {w : Ω → ℝ} (hw : ∀ ω, 0 < w ω)
    (hint : Integrable w μP) {p C : ℝ} (hp : 1 ≤ p)
    (hC : ∫⁻ ω, ENNReal.ofReal (w ω ^ p) ∂μP ≤ ENNReal.ofReal C) :
    ∫ ω, w ω ∂μP ≤ 1 + max C 0 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => (hw ω).le)
    hint.aestronglyMeasurable]
  have h1 : ∫⁻ ω, ENNReal.ofReal (w ω) ∂μP ≤ ∫⁻ ω, (1 + ENNReal.ofReal (w ω ^ p)) ∂μP := by
    refine lintegral_mono fun ω => ?_
    have hv := hw ω
    have hpp : 0 ≤ w ω ^ p := by positivity
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hpp]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_or_gt (w ω) 1 with h | h
    · linarith
    · have : w ω ≤ w ω ^ p := by
        calc _ = w ω ^ (1:ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h.le hp
      linarith
  have h2 : ∫⁻ ω, (1 + ENNReal.ofReal (w ω ^ p)) ∂μP = 1 + ∫⁻ ω, ENNReal.ofReal (w ω ^ p) ∂μP := by
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  have h4 : (1 : ENNReal) + ENNReal.ofReal C ≤ ENNReal.ofReal (1 + max C 0) := by
    rw [ENNReal.ofReal_add zero_le_one (le_max_right _ _), ENNReal.ofReal_one]
    exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    ((h1.trans (h2.le.trans (add_le_add le_rfl hC))).trans h4)

lemma ae_V (N : Network K J μP) (k : Fin K) :
    ∀ᵐ ω ∂μP, Tendsto (fun l => RW.psum (fun i => N.v k i) l ω) atTop atTop := by
  have := N.isProb
  have hint : Integrable (N.v k 0) μP := (N.memLp_v k).integrable one_le_two
  have hind : Pairwise (fun i i' => ProbabilityTheory.IndepFun (N.v k i) (N.v k i') μP) := by
    intro i i' hii
    exact N.indep.indep (i := Sum.inr (Sum.inl (k, i))) (j := Sum.inr (Sum.inl (k, i')))
      (by simp [hii])
  have hpos : 0 < ∫ ω, N.v k 0 ω ∂μP := integral_pos_of_pos (N.pos_v k 0) hint
  filter_upwards [ProbabilityTheory.strong_law_ae_real (fun i => N.v k i) hint hind
    (N.ident_v k)] with ω hω
  have hev : ∀ᶠ n : ℕ in atTop, (∫ ω, N.v k 0 ω ∂μP) / 2 <
      (∑ i ∈ Finset.range n, N.v k i ω) / n := hω.eventually (lt_mem_nhds (by linarith))
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith : (0:ℝ) < (∫ ω, N.v k 0 ω ∂μP) / 2))
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have : (0:ℝ) < n := by exact_mod_cast hn0
  rw [lt_div_iff₀ this] at hn
  simp only [RW.psum]
  linarith

lemma ae_U (N : Network K J μP) {k : Fin K} (hk : k ∈ J) :
    ∀ᵐ ω ∂μP, Tendsto (fun l => RW.psum (fun i => N.u k i) l ω) atTop atTop := by
  have := N.isProb
  have hint : Integrable (N.u k 0) μP := (N.memLp_u k hk).integrable one_le_two
  have hind : Pairwise (fun i i' => ProbabilityTheory.IndepFun (N.u k i) (N.u k i') μP) := by
    intro i i' hii
    exact N.indep.indep (i := Sum.inl (⟨k, hk⟩, i)) (j := Sum.inl (⟨k, hk⟩, i'))
      (by simp [hii])
  have hpos : 0 < ∫ ω, N.u k 0 ω ∂μP := integral_pos_of_pos (N.pos_u k hk 0) hint
  filter_upwards [ProbabilityTheory.strong_law_ae_real (fun i => N.u k i) hint hind
    (N.ident_u k hk)] with ω hω
  have hev : ∀ᶠ n : ℕ in atTop, (∫ ω, N.u k 0 ω ∂μP) / 2 <
      (∑ i ∈ Finset.range n, N.u k i ω) / n := hω.eventually (lt_mem_nhds (by linarith))
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith : (0:ℝ) < (∫ ω, N.u k 0 ω ∂μP) / 2))
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have : (0:ℝ) < n := by exact_mod_cast hn0
  rw [lt_div_iff₀ this] at hn
  simp only [RW.psum]
  linarith

lemma cnt_zero {F : ℕ → ℝ} (hF0 : F 0 = 0) (hFm : StrictMono F) : RW.cnt F 0 = 0 := by
  have : {l : ℕ | F l ≤ 0} = {0} := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hl
      by_contra h0
      have := hFm (Nat.pos_of_ne_zero h0)
      linarith
    · rintro rfl; rw [hF0]
  unfold RW.cnt; rw [this, csSup_singleton]

end NetT

namespace NetT

open MeasureTheory ProbabilityTheory Filter Topology Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}

lemma mu_pos' {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP)
    (k : Fin K) : 0 < N.mu k := by
  have := N.isProb
  exact inv_pos.2 (integral_pos_of_pos (N.pos_v k 0) ((N.memLp_v k).integrable one_le_two))

lemma lam_pos' {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP)
    {k : Fin K} (hk : k ∈ J) : 0 < N.lam k := by
  have := N.isProb
  simp only [Network.lam, if_pos hk]
  exact inv_pos.2 (integral_pos_of_pos (N.pos_u k hk 0) ((N.memLp_u k hk).integrable one_le_two))

variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {P : ∀ n, Measure (Ωs n)}

/-- the scaled centred service renewal process of station `k` is modulus tight. -/
lemma ren_S (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) (k : Fin K) :
    RW.MT P (fun n ω t => (Real.sqrt n)⁻¹ *
      ((RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t) : ℝ) -
        (∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹ * (n * t))) := by
  obtain ⟨ε0, hε0, C, hC⟩ := hA.2.2.2.2.2.2.1
  have hP := fun n => (net n).isProb
  have hmu0 : 0 ≤ mu k :=
    ge_of_tendsto (hA.2.1 k) (Eventually.of_forall fun n => (mu_pos' (net n) k).le)
  have hmeas : ∀ n, Measurable ((net n).v k 0) := fun n => (net n).meas_v k 0
  refine RW.renewal_tight P hP (fun n i => (net n).v k i) (fun n => indep_v (net n) k)
    (fun n i => (net n).meas_v k i) (fun n i => (net n).ident_v k i) (fun n => (net n).memLp_v k)
    (fun n i ω => (net n).pos_v k i ω) (fun n => ae_V (net n) k) (mu k + 1)⁻¹ (by positivity)
    ?_ (s k + 1) ?_ ?_
  · filter_upwards [(hA.2.1 k).eventually (Iio_mem_nhds (by linarith : mu k < mu k + 1))]
      with n hn
    have h1 : ∫ ω', (net n).v k 0 ω' ∂(P n) = ((net n).mu k)⁻¹ := by
      simp only [Network.mu, inv_inv]
    rw [h1]
    exact inv_anti₀ (mu_pos' (net n) k) hn.le
  · filter_upwards [(hA.2.2.2.2.1 k).eventually (Iio_mem_nhds (by linarith : s k < s k + 1))]
      with n hn
    have := (net n).isProb
    have h1 : (net n).sVar k = ∫ ω, ((net n).v k 0 ω - ∫ ω', (net n).v k 0 ω' ∂(P n)) ^ 2 ∂(P n) :=
      variance_eq_integral (hmeas n).aemeasurable
    rw [← h1]; exact hn.le
  · refine RW.hUI_of_moment P (fun n => (net n).v k 0) hmeas (fun n ω => (net n).pos_v k 0 ω)
      (fun n => ∫ ω', (net n).v k 0 ω' ∂(P n))
      (fun n => by
        have := hP n
        exact (integral_pos_of_pos ((net n).pos_v k 0) (((net n).memLp_v k).integrable
          one_le_two)).le) (1 + max C 0) ?_ (2 + ε0) (by linarith) C ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have := hP n
      exact mean_le_of_moment ((net n).pos_v k 0) (((net n).memLp_v k).integrable one_le_two)
        (by linarith) (hC n hn k)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact hC n hn k

end NetT

namespace NetT

open MeasureTheory ProbabilityTheory Filter Topology Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}
variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {P : ∀ n, Measure (Ωs n)}

/-- the scaled centred arrival renewal process of station `k ∈ 𝒥` is modulus tight. -/
lemma ren_A (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) {k : Fin K}
    (hk : k ∈ J) :
    RW.MT P (fun n ω t => (Real.sqrt n)⁻¹ *
      ((RW.cnt (fun l => RW.psum (fun i => (net n).u k i) l ω) (n * t) : ℝ) -
        (∫ ω', (net n).u k 0 ω' ∂(P n))⁻¹ * (n * t))) := by
  obtain ⟨ε0, hε0, C, hC⟩ := hA.2.2.2.2.2.2.2
  have hP := fun n => (net n).isProb
  have hlam0 : 0 ≤ lam k :=
    ge_of_tendsto (hA.2.2.1 k) (Eventually.of_forall fun n => (lam_pos' (net n) hk).le)
  have hmeas : ∀ n, Measurable ((net n).u k 0) := fun n => (net n).meas_u k hk 0
  refine RW.renewal_tight P hP (fun n i => (net n).u k i) (fun n => indep_u (net n) hk)
    (fun n i => (net n).meas_u k hk i) (fun n i => (net n).ident_u k hk i)
    (fun n => (net n).memLp_u k hk)
    (fun n i ω => (net n).pos_u k hk i ω) (fun n => ae_U (net n) hk) (lam k + 1)⁻¹ (by positivity)
    ?_ (a k + 1) ?_ ?_
  · filter_upwards [(hA.2.2.1 k).eventually (Iio_mem_nhds (by linarith : lam k < lam k + 1))]
      with n hn
    have h1 : ∫ ω', (net n).u k 0 ω' ∂(P n) = ((net n).lam k)⁻¹ := by
      simp only [Network.lam, if_pos hk, inv_inv]
    rw [h1]
    exact inv_anti₀ (lam_pos' (net n) hk) hn.le
  · filter_upwards [(hA.2.2.2.1 k hk).eventually (Iio_mem_nhds (by linarith : a k < a k + 1))]
      with n hn
    have := (net n).isProb
    have h1 : (net n).aVar k = ∫ ω, ((net n).u k 0 ω - ∫ ω', (net n).u k 0 ω' ∂(P n)) ^ 2 ∂(P n) :=
      variance_eq_integral (hmeas n).aemeasurable
    rw [← h1]; exact hn.le
  · refine RW.hUI_of_moment P (fun n => (net n).u k 0) hmeas (fun n ω => (net n).pos_u k hk 0 ω)
      (fun n => ∫ ω', (net n).u k 0 ω' ∂(P n))
      (fun n => by
        have := hP n
        exact (integral_pos_of_pos ((net n).pos_u k hk 0) (((net n).memLp_u k hk).integrable
          one_le_two)).le) (1 + max C 0) ?_ (2 + ε0) (by linarith) C ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have := hP n
      exact mean_le_of_moment ((net n).pos_u k hk 0)
        (((net n).memLp_u k hk).integrable one_le_two) (by linarith) (hC n hn k hk)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact hC n hn k hk

lemma routeVec_mem (r : Fin (K + 1)) (j : Fin K) : 0 ≤ routeVec r j ∧ routeVec r j ≤ 1 := by
  unfold routeVec; split_ifs <;> norm_num

lemma routing_mem {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP)
    (k j : Fin K) : 0 ≤ N.routing k j ∧ N.routing k j ≤ 1 := by
  have := N.isProb
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

lemma routeVec_integral {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP)
    (k j : Fin K) : ∫ ω, routeVec (N.φ k 0 ω) j ∂μP = N.routing k j := by
  have hs : MeasurableSet {ω | N.φ k 0 ω = j.succ} :=
    (N.meas_φ k 0) (measurableSet_singleton _)
  have e : (fun ω => routeVec (N.φ k 0 ω) j) = Set.indicator {ω | N.φ k 0 ω = j.succ} 1 := by
    funext ω
    simp only [routeVec, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  rw [e, integral_indicator_one hs]
  rfl

/-- the scaled centred routing walk of station `k`, coordinate `j`, run at the service count, is
modulus tight. -/
lemma route_walk (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) (k j : Fin K) :
    RW.MT P (fun n ω t => (Real.sqrt n)⁻¹ *
      RW.psum (fun i ω => routeVec ((net n).φ k i ω) j - R k j)
        (RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t)) ω) := by
  have hP := fun n => (net n).isProb
  have hRm : ∀ n, R k j = (net n).routing k j := fun n => by rw [hA.1 n]
  have hg : Measurable fun r : Fin (K + 1) => routeVec r j - R k j := measurable_of_finite _
  set ξ : ∀ n, ℕ → Ωs n → ℝ := fun n i => (fun r => routeVec r j - R k j) ∘ (net n).φ k i
    with hξ
  have hξind : ∀ n, iIndepFun (ξ n) (P n) := fun n =>
    (indep_φ (net n) k).comp (fun _ r => routeVec r j - R k j) (fun _ => hg)
  have hξm : ∀ n i, Measurable (ξ n i) := fun n i => hg.comp ((net n).meas_φ k i)
  have hξid : ∀ n i, IdentDistrib (ξ n i) (ξ n 0) (P n) (P n) := fun n i =>
    ((net n).ident_φ k i).comp hg
  have hξb : ∀ n i ω, |ξ n i ω| ≤ 1 := by
    intro n i ω
    have h1 := routeVec_mem ((net n).φ k i ω) j
    have h2 := routing_mem (net n) k j
    rw [← hRm n] at h2
    simp only [hξ, Function.comp]
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hξL2 : ∀ n, MemLp (ξ n 0) 2 (P n) := fun n =>
    MemLp.of_bound (hξm n 0).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hξb n 0 ω)
  have hξ0 : ∀ n, ∫ ω, ξ n 0 ω ∂(P n) = 0 := by
    intro n
    have := hP n
    have hi : Integrable (fun ω => routeVec ((net n).φ k 0 ω) j) (P n) :=
      Integrable.of_bound (measurable_of_finite (fun r : Fin (K + 1) => routeVec r j) |>.comp
        ((net n).meas_φ k 0)).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
          have := routeVec_mem ((net n).φ k 0 ω) j
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
    show ∫ ω, (routeVec ((net n).φ k 0 ω) j - R k j) ∂(P n) = 0
    rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul,
      routeVec_integral, hRm n, sub_self]
  have hξσ : ∀ᶠ n in atTop, ∫ ω, ξ n 0 ω ^ 2 ∂(P n) ≤ 1 := Eventually.of_forall fun n => by
    have := hP n
    calc ∫ ω, ξ n 0 ω ^ 2 ∂(P n) ≤ ∫ ω, (1:ℝ) ∂(P n) := by
          refine integral_mono (hξL2 n).integrable_sq (integrable_const _) fun ω => ?_
          have := hξb n 0 ω
          show ξ n 0 ω ^ 2 ≤ 1
          rw [← sq_abs]; nlinarith [abs_nonneg (ξ n 0 ω)]
      _ = 1 := by simp
  have hξUI : ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) atTop (𝓝 0) := by
    intro θ hθ
    refine tendsto_const_nhds.congr' ?_
    have hsqt := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hsqt.eventually_ge_atTop (1 / θ)] with n hn
    simp only [Function.comp] at hn
    have h1 : 1 ≤ θ * Real.sqrt n := by rwa [div_le_iff₀ hθ, mul_comm] at hn
    have : {ω | θ * Real.sqrt n < |ξ n 0 ω|} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      linarith [hξb n 0 ω]
    rw [this, measure_empty, mul_zero]
  have hmod : ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n : ℕ in atTop, P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧ (j:ℝ) ≤ T * n ∧
        ε * Real.sqrt n ≤ |RW.psum (ξ n) j ω - RW.psum (ξ n) i ω|} ≤ ENNReal.ofReal η :=
    fun T hT ε hε η hη => RW.rw_tight P hP ξ hξind hξm hξid hξL2 hξ0 1 hξσ hξUI T hT ε hε η hη
  have hmu0 : 0 ≤ mu k :=
    ge_of_tendsto (hA.2.1 k) (Eventually.of_forall fun n => (mu_pos' (net n) k).le)
  have hX := ren_S net hA k
  have hbf := RW.bd_fl_of_MT P
    (fun n ω t => RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t))
    (fun n => (∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹) (mu k + 1)
    (fun n => (mu_pos' (net n) k).le)
    ((hA.2.1 k).eventually (Iic_mem_nhds (by linarith : mu k < mu k + 1))) hX
    (fun n ω => by
      simp only [mul_zero]
      exact cnt_zero (by simp [RW.psum])
        (strictMono_nat_of_lt_succ fun l => by
          simp only [RW.psum, Finset.sum_range_succ]; linarith [(net n).pos_v k l ω]))
  exact RW.randtime_tight P ξ hmod _ hbf.1 hbf.2

end NetT

namespace NetT

open MeasureTheory ProbabilityTheory Filter Topology Reiman84.QueueLength

variable {K : ℕ} {J : Finset (Fin K)}
variable {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {P : ∀ n, Measure (Ωs n)}

/-- vector modulus tightness (the body of `P5.ModTight`) from coordinatewise tightness. -/
lemma vec_of_coords {X : ∀ n, Ωs n → ℝ → Fin K → ℝ}
    (h : ∀ j, RW.MT P (fun n ω t => X n ω t j)) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
        ε ≤ ‖X n ω s - X n ω t‖} ≤ ENNReal.ofReal η := by
  intro ε hε η hη
  rcases (Finset.univ (α := Fin K)).eq_empty_or_nonempty with hK | hK
  · refine ⟨1, one_pos, 0, fun n _ => ?_⟩
    have hE : IsEmpty (Fin K) := ⟨fun i => by simpa [hK] using Finset.mem_univ i⟩
    have : {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ 1 ∧
        ε ≤ ‖X n ω s - X n ω t‖} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and,
        not_le]
      intro s _ t _ _
      rw [Subsingleton.elim (X n ω s - X n ω t) 0, norm_zero]; exact hε
    rw [this, measure_empty]; exact bot_le
  have hK0 : (0:ℝ) < K := by
    have : 0 < K := Fin.pos_iff_nonempty.2 (Finset.univ_nonempty_iff.1 hK)
    exact_mod_cast this
  choose δj hδj Nj hNj using fun j => h j ε hε (η / K) (by positivity)
  refine ⟨Finset.univ.inf' hK δj, (Finset.lt_inf'_iff hK).2 fun j _ => hδj j,
    Finset.univ.sup Nj, fun n hn => ?_⟩
  have hsub : {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1,
      |s - t| ≤ Finset.univ.inf' hK δj ∧ ε ≤ ‖X n ω s - X n ω t‖} ⊆
      ⋃ j, {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δj j ∧
        ε ≤ |X n ω s j - X n ω t j|} := by
    rintro ω ⟨s, hs, t, ht, hst, hle⟩
    obtain ⟨j, hj⟩ : ∃ j, ε ≤ |X n ω s j - X n ω t j| := by
      by_contra hcon
      push_neg at hcon
      have : ‖X n ω s - X n ω t‖ < ε := (pi_norm_lt_iff hε).2 fun j => by
        rw [Pi.sub_apply, Real.norm_eq_abs]; exact hcon j
      linarith
    exact Set.mem_iUnion.2 ⟨j, s, hs, t, ht,
      hst.trans (Finset.inf'_le _ (Finset.mem_univ j)), hj⟩
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ∑ j, P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δj j ∧
        ε ≤ |X n ω s j - X n ω t j|} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin K, ENNReal.ofReal (η / K) :=
        Finset.sum_le_sum fun j _ => hNj j n ((Finset.le_sup (Finset.mem_univ j)).trans hn)
    _ = ENNReal.ofReal η := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        field_simp

lemma Stilde_coord (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    (hR : ∀ n, (net n).routing = R) (k j : Fin K) (n : ℕ) (ω : Ωs n) (t : ℝ) :
    diffScale n (fun t => (net n).Stilde k t ω) t j =
      (Real.sqrt n)⁻¹ * RW.psum (fun i ω => routeVec ((net n).φ k i ω) j - R k j)
        (RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t)) ω +
      (R k j - if k = j then 1 else 0) * ((Real.sqrt n)⁻¹ *
        ((RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t) : ℝ) -
          (∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹ * (n * t))) := by
  have hS : (net n).S k (n * t) ω =
      RW.cnt (fun l => RW.psum (fun i => (net n).v k i) l ω) (n * t) := rfl
  have hmu : (net n).mu k = (∫ ω', (net n).v k 0 ω' ∂(P n))⁻¹ := rfl
  simp only [diffScale, Network.Stilde, Network.Shat, Pi.smul_apply, Pi.sub_apply,
    Finset.sum_apply, smul_eq_mul, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply, hR n,
    hS, ← hmu]
  simp only [RW.psum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  by_cases hkj : k = j
  · subst hkj; simp; ring
  · simp [hkj, Ne.symm hkj]; ring

lemma Atilde_coord (net : ∀ n, Network K J (P n)) (j : Fin K) (hj : j ∈ J) (n : ℕ)
    (ω : Ωs n) (t : ℝ) :
    diffScale n (fun t => (net n).Atilde t ω) t j = (Real.sqrt n)⁻¹ *
      ((RW.cnt (fun l => RW.psum (fun i => (net n).u j i) l ω) (n * t) : ℝ) -
        (∫ ω', (net n).u j 0 ω' ∂(P n))⁻¹ * (n * t)) := by
  simp only [diffScale, Network.Atilde, Network.Avec, Network.A, Network.lam, if_pos hj,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  show (Real.sqrt n)⁻¹ * ((RW.cnt (fun l => RW.psum (fun i => (net n).u j i) l ω) (n * t) : ℝ) -
    (n * t) * (∫ ω', (net n).u j 0 ω' ∂(P n))⁻¹) = _
  ring

lemma Atilde_coord0 (net : ∀ n, Network K J (P n)) (j : Fin K) (hj : j ∉ J) (n : ℕ)
    (ω : Ωs n) (t : ℝ) : diffScale n (fun t => (net n).Atilde t ω) t j = 0 := by
  simp [diffScale, Network.Atilde, Network.Avec, Network.A, Network.lam, hj]

lemma tight_A (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
        ε ≤ ‖diffScale n (fun t => (net n).Atilde t ω) s -
          diffScale n (fun t => (net n).Atilde t ω) t‖} ≤ ENNReal.ofReal η := by
  refine vec_of_coords (X := fun n ω => diffScale n (fun t => (net n).Atilde t ω)) fun j => ?_
  by_cases hj : j ∈ J
  · exact (ren_A net hA hj).congr fun n ω t _ => (Atilde_coord net j hj n ω t).symm
  · exact RW.MT.zero.congr fun n ω t _ => (Atilde_coord0 net j hj n ω t).symm

lemma tight_S (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) (k : Fin K) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
        ε ≤ ‖diffScale n (fun t => (net n).Stilde k t ω) s -
          diffScale n (fun t => (net n).Stilde k t ω) t‖} ≤ ENNReal.ofReal η := by
  refine vec_of_coords (X := fun n ω => diffScale n (fun t => (net n).Stilde k t ω)) fun j => ?_
  exact ((route_walk net hA k j).add ((ren_S net hA k).const_mul
    (R k j - if k = j then 1 else 0))).congr
    fun n ω t _ => (Stilde_coord net hA.1 k j n ω t).symm

end NetT

namespace P5

open Filter Topology MeasureTheory Reiman84.QueueLength

/-- Modulus-of-continuity tightness on `[0,1]` (outer measure of the bad set). -/
def ModTight {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (X : ∀ n, Ω n → ℝ → Fin K → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n, N ≤ n →
    P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, ∃ t ∈ Set.Icc (0:ℝ) 1, |s - t| ≤ δ ∧
      ε ≤ ‖X n ω s - X n ω t‖} ≤ ENNReal.ofReal η

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

end Glue

section Close

variable {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)}

end Close

section Tight

variable {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}

end Tight

section TightZeta

variable {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)}

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

end TightZeta

section Fdd

variable {K : ℕ} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}

end Fdd

section Prop4

open Reiman84.QueueLength Matrix

variable {K : ℕ} {J : Finset (Fin K)}

/-- Quantitative form of the A76 complementarity argument: the regulator `y` is bounded by the
sup of the free path `x` on `[0,1]`. -/
lemma y_bound_of_compl {P : Matrix (Fin K) (Fin K) ℝ} (hP0 : ∀ i j, 0 ≤ P i j) (w : A76.Wt P)
    {x y z : ℝ → Fin K → ℝ}
    (hxyz : ∀ s ∈ Set.Icc (0:ℝ) 1, z s = x s + vecMul (y s) (1 - P))
    (hyc : ContinuousOn y (Set.Icc 0 1)) (hym : MonotoneOn y (Set.Icc 0 1)) (hy0 : y 0 = 0)
    (hz : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ z s)
    (hzr : ∀ s ∈ Set.Ico (0:ℝ) 1, ContinuousWithinAt z (Set.Icc s 1) s)
    (hcomp : ∀ j : Fin K, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 →
      (∀ r ∈ Set.Icc s t, 0 < z r j) → y t j = y s j)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ i, |x s i| ≤ δ) :
    ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ i, |y s i| ≤ δ / (1 - w.θ) * w.v i := by
  set x' := Reiman84.QueueLength.onUnit x with hx'
  have hxx : ∀ s ∈ Set.Icc (0:ℝ) 1, x' s = x s := fun s hs => A76.onUnit_of_mem hs
  have hxyz' : ∀ s ∈ Set.Icc (0:ℝ) 1, z s = x' s + vecMul (y s) (1 - P) := fun s hs => by
    rw [hxx s hs]; exact hxyz s hs
  obtain ⟨My, hMy⟩ := isCompact_Icc.exists_bound_of_continuousOn hyc
  have hyb : A76.Bd y := ⟨My, fun s hs i => by
    have := (norm_le_pi_norm (y s) i).trans (hMy s hs); rwa [Real.norm_eq_abs] at this⟩
  have hxb : A76.LB x' := ⟨δ, fun s hs i => by
    rw [hxx s hs]; exact (abs_le.1 (hδ s hs i)).1⟩
  have hfix : ∀ t ∈ Set.Icc (0:ℝ) 1, A76.piOp P x' y t = y t :=
    A76.fixed_of_compl hyc hym hy0 (fun s hs => by rw [← hxyz' s hs]; exact hz s hs)
      (fun s hs => (hzr s hs).congr (fun r hr => (hxyz' r ⟨hs.1.trans hr.1, hr.2⟩).symm)
        (hxyz' s ⟨hs.1, hs.2.le⟩).symm)
      (fun j s t h0 hst ht1 hall => hcomp j s t h0 hst ht1 fun r hr => by
        rw [hxyz' r ⟨h0.trans hr.1, hr.2.trans ht1⟩]; exact hall r hr)
  have h0b : A76.Bd (0 : ℝ → Fin K → ℝ) := ⟨0, fun s _ i => by simp⟩
  have h0l : A76.LB (0 : ℝ → Fin K → ℝ) := ⟨0, fun s _ i => by simp⟩
  have h0fix : ∀ t ∈ Set.Icc (0:ℝ) 1,
      A76.piOp P (0 : ℝ → Fin K → ℝ) 0 t = (0 : ℝ → Fin K → ℝ) t := by
    intro t _; funext j; simp [A76.piOp]
  have hu := A76.fixed_unique hP0 w hxb h0l hyb h0b hfix h0fix hδ0
    (fun s hs i => by rw [hxx s hs]; simpa using hδ s hs i)
  intro s hs i
  simpa using hu s hs i

/-- One network: the scaled idleness `n^{-1/2} μₖ Iₖ(n)` is bounded by the sup of the scaled
time-changed netput on `[0,1]`. -/
lemma idle_bound {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP) (ω : Ω)
    (Q B : ℝ → Fin K → ℝ) (h : N.IsQueueSolution ω Q B)
    (hU : ∀ k ∈ J, Tendsto (fun l => N.U k l ω) atTop atTop)
    (hV : ∀ k, Tendsto (fun l => N.V k l ω) atTop atTop)
    {R : Matrix (Fin K) (Fin K) ℝ} (hR : N.routing = R) (w : A76.Wt R) {n : ℕ} (hn : 1 ≤ n)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖diffScale n (fun t => N.Xtilde B t ω) s‖ ≤ δ) (k : Fin K) :
    |(Real.sqrt n)⁻¹ * (N.mu k * Network.idle B n k)| ≤ δ / (1 - w.θ) * w.W := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hcpos : 0 < (Real.sqrt n)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hnpos)
  have hmu := A76.mu_pos N
  have hP0 : ∀ i j, 0 ≤ R i j := hR ▸ A76.routing_nonneg N
  have hns : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ (n:ℝ) * s := fun s hs => mul_nonneg hnpos.le hs.1
  have hYc : ContinuousOn (fun r => N.Y B r) (Set.Ici 0) := by
    refine continuousOn_pi.2 fun k => ?_
    simp only [Network.Y, Network.idle]
    exact continuousOn_const.mul (continuousOn_id.sub (A76.B_cont N ω Q B h k))
  have key := y_bound_of_compl hP0 w (x := diffScale n (fun t => N.Xtilde B t ω))
    (y := diffScale n (N.Y B)) (z := diffScale n Q) (fun s hs => ?_) ?_ ?_ ?_ (fun s hs => ?_)
    (fun s hs => ?_) (fun j s t hs hst ht hall => ?_) hδ0
    (fun s hs i => ((norm_le_pi_norm _ i).trans (hδ s hs)).trans' (le_of_eq
      (Real.norm_eq_abs _).symm)) 1 ⟨zero_le_one, le_rfl⟩ k
  · have e : diffScale n (N.Y B) 1 k = (Real.sqrt n)⁻¹ * (N.mu k * Network.idle B n k) := by
      simp [diffScale, Network.Y]
    rw [e] at key
    exact key.trans (mul_le_mul_of_nonneg_left (w.hvW k)
      (div_nonneg hδ0 (by linarith [w.hθ1])))
  · simp only [diffScale]
    rw [A76.eq13 N ω Q B h _ (hns s hs), hR, smul_add, Matrix.smul_vecMul]
  · show ContinuousOn (fun t => (Real.sqrt n)⁻¹ • N.Y B (n * t)) (Set.Icc 0 1)
    exact (hYc.comp (continuousOn_const.mul continuousOn_id)
      fun s hs => hns s hs).const_smul ((Real.sqrt n)⁻¹)
  · intro a ha b hb hab k
    simp only [diffScale, Pi.smul_apply, smul_eq_mul, Network.Y, Network.idle]
    have hb' := A76.B_bounds N ω Q B h k (hns a ha) (mul_le_mul_of_nonneg_left hab hnpos.le)
    apply mul_le_mul_of_nonneg_left _ hcpos.le
    apply mul_le_mul_of_nonneg_left _ (hmu k).le
    nlinarith [hb'.2]
  · funext k; simp [diffScale, Network.Y, Network.idle, h.2.1 k]
  · simp only [diffScale]
    exact smul_nonneg hcpos.le (A76.Q_nonneg N ω Q B h hU hV (hns s hs))
  · show ContinuousWithinAt (fun t => (Real.sqrt n)⁻¹ • Q (n * t)) (Set.Icc s 1) s
    have hq : ContinuousWithinAt (fun t => Q (n * t)) (Set.Icc s 1) s :=
      (A76.Q_rc N ω Q B h hU hV (mul_nonneg hnpos.le hs.1)).comp
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
    have := A76.B_full N ω Q B h j (mul_nonneg hnpos.le hs) (mul_le_mul_of_nonneg_left hst hnpos.le)
      hpos
    congr 2
    linarith

/-- The scaled time-changed netput is bounded by the scaled primitives at times in `[0,1]`. -/
lemma zetaT_norm_le {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP)
    (ω : Ω) (B : ℝ → Fin K → ℝ) (n : ℕ) (hn : 0 < n) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    ‖diffScale n (fun t => N.Xtilde B t ω) s‖ ≤ ‖diffScale n (fun t => N.Atilde t ω) s‖ +
      ∑ k, ‖diffScale n (fun t => N.Stilde k t ω) (B (n * s) k / n)‖ +
      ‖((Real.sqrt n)⁻¹ * n) • (N.lam + N.eta)‖ := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have e : diffScale n (fun t => N.Xtilde B t ω) s = diffScale n (fun t => N.Atilde t ω) s +
      ∑ k, diffScale n (fun t => N.Stilde k t ω) (B (n * s) k / n) +
      s • (((Real.sqrt n)⁻¹ * n) • (N.lam + N.eta)) := by
    have e1 : (Real.sqrt n)⁻¹ * (n * s) = s * ((Real.sqrt n)⁻¹ * n) := by ring
    have e2 : ∀ k, (n:ℝ) * (B (n * s) k / n) = B (n * s) k := fun k => by field_simp
    simp only [diffScale, Network.Xtilde, smul_add, Finset.smul_sum, smul_smul, e1, e2]
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add le_rfl (norm_sum_le _ _))) ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hs.2

lemma Atilde_zero {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP)
    (ω : Ω) : N.Atilde 0 ω = 0 := by
  funext k
  simp only [Network.Atilde, Network.Avec, Network.A, zero_smul, sub_zero, Pi.zero_apply]
  split_ifs with hk
  · have : {l : ℕ | N.U k l ω ≤ 0} = {0} := by
      ext l
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hl
        by_contra hl0
        have : 0 < N.U k l ω := Finset.sum_pos (fun i _ => N.pos_u k hk i ω)
          (Finset.nonempty_range_iff.2 hl0)
        linarith
      · rintro rfl; simp [Network.U]
    rw [this, csSup_singleton]; simp
  · simp

lemma Stilde_zero {Ω : Type} [MeasurableSpace Ω] {μP : Measure Ω} (N : Network K J μP)
    (k : Fin K) (ω : Ω) : N.Stilde k 0 ω = 0 := by
  have hS : N.S k 0 ω = 0 := by
    have : {l : ℕ | N.V k l ω ≤ 0} = {0} := by
      ext l
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hl
        by_contra hl0
        have : 0 < N.V k l ω := Finset.sum_pos (fun i _ => N.pos_v k i ω)
          (Finset.nonempty_range_iff.2 hl0)
        linarith
      · rintro rfl; simp [Network.V]
    simp only [Network.S, this, csSup_singleton]
  simp [Network.Stilde, Network.Shat, hS]

variable {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}

/-- Modulus tightness with value `0` at time `0` gives boundedness in probability on `[0,1]`. -/
lemma bdd_of_tight {X : ∀ n, Ω n → ℝ → Fin K → ℝ} (hT : ModTight P X)
    (h0 : ∀ n ω, X n ω 0 = 0) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      P n {ω | ∃ s ∈ Set.Icc (0:ℝ) 1, M < ‖X n ω s‖} ≤ ENNReal.ofReal η := by
  obtain ⟨δ, hδ, N, hN⟩ := hT 1 one_pos η hη
  set m : ℕ := ⌈1 / δ⌉₊ + 1 with hm
  have hm0 : (0:ℝ) < m := by positivity
  have hmδ : 1 / (m:ℝ) ≤ δ := by
    rw [div_le_iff₀ hm0]
    have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (m:ℝ) = ⌈1 / δ⌉₊ + 1 := by rw [hm]; push_cast; ring
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  refine ⟨m, hm0.le, N, fun n hn => le_trans (measure_mono ?_) (hN n hn)⟩
  intro ω hω
  obtain ⟨s, hs, hlt⟩ := hω
  by_contra hcon
  simp only [Set.mem_setOf_eq, not_exists, not_and, not_le] at hcon
  have step : ∀ j : ℕ, j ≤ m → ‖X n ω (s * j / m)‖ ≤ j := by
    intro j
    induction j with
    | zero => intro _; simp [h0]
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hjm : ((j:ℝ) + 1) ≤ m := by exact_mod_cast hj
      have hmem : ∀ i : ℕ, i ≤ m → s * i / m ∈ Set.Icc (0:ℝ) 1 := by
        intro i hi
        have hi' : (i:ℝ) ≤ m := by exact_mod_cast hi
        refine ⟨by have := hs.1; positivity, ?_⟩
        rw [div_le_one hm0]
        nlinarith [hs.1, hs.2]
      have hd : |s * ((j + 1 : ℕ) : ℝ) / m - s * j / m| ≤ δ := by
        have e : s * ((j + 1 : ℕ) : ℝ) / m - s * j / m = s * (1 / m) := by
          push_cast; field_simp; ring
        rw [e, abs_of_nonneg (by have := hs.1; positivity)]
        calc s * (1 / (m:ℝ)) ≤ 1 * (1 / m) :=
              mul_le_mul_of_nonneg_right hs.2 (by positivity)
          _ ≤ δ := by rw [one_mul]; exact hmδ
      have hlt1 := hcon _ (hmem (j+1) hj) _ (hmem j (by omega)) hd
      have := norm_le_norm_add_norm_sub' (X n ω (s * ((j + 1 : ℕ) : ℝ) / m)) (X n ω (s * j / m))
      push_cast at this hlt1 ⊢
      linarith
  have := step m le_rfl
  have e : s * (m:ℝ) / m = s := by field_simp
  rw [e] at this
  linarith

lemma tendsto_zero_of_ofReal {f : ℕ → ENNReal}
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, f n ≤ ENNReal.ofReal η) : Tendsto f atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hne
  · exact ⟨0, fun _ _ => le_top⟩
  · obtain ⟨N, hN⟩ := eventually_atTop.1 (h ε.toReal (ENNReal.toReal_pos hε.ne' hne))
    exact ⟨N, fun n hn => (hN n hn).trans (ENNReal.ofReal_toReal hne).le⟩

lemma mu_lower (net : ∀ n, Network K J (P n)) {R : Matrix (Fin K) (Fin K) ℝ}
    {mu s lam a c : Fin K → ℝ} (hA : HeavyTrafficAssumptions net R mu s lam a c) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ n, 1 ≤ n → ∀ k, Cm ≤ (net n).mu k := by
  obtain ⟨ε, hε, C, hC⟩ := hA.2.2.2.2.2.2.1
  refine ⟨(1 + max C 0)⁻¹, by positivity, fun n hn k => ?_⟩
  have := (net n).isProb
  have hint : Integrable ((net n).v k 0) (P n) := ((net n).memLp_v k).integrable one_le_two
  have hpos : 0 < ∫ ω, (net n).v k 0 ω ∂(P n) :=
    A76.integral_pos_of_pos' ((net n).pos_v k 0) hint
  have hle : ∫ ω, (net n).v k 0 ω ∂(P n) ≤ 1 + max C 0 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => ((net n).pos_v k 0 ω).le)
      hint.aestronglyMeasurable]
    have h1 : ∫⁻ ω, ENNReal.ofReal ((net n).v k 0 ω) ∂(P n) ≤
        ∫⁻ ω, (1 + ENNReal.ofReal ((net n).v k 0 ω ^ (2 + ε))) ∂(P n) := by
      refine lintegral_mono fun ω => ?_
      have hv := (net n).pos_v k 0 ω
      have hp : 0 ≤ (net n).v k 0 ω ^ (2 + ε) := by positivity
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hp]
      refine ENNReal.ofReal_le_ofReal ?_
      rcases le_or_gt ((net n).v k 0 ω) 1 with h | h
      · linarith
      · have : (net n).v k 0 ω ≤ (net n).v k 0 ω ^ (2 + ε) := by
          calc _ = (net n).v k 0 ω ^ (1:ℝ) := (Real.rpow_one _).symm
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h.le (by linarith)
        linarith
    have h2 : ∫⁻ ω, (1 + ENNReal.ofReal ((net n).v k 0 ω ^ (2 + ε))) ∂(P n) =
        1 + ∫⁻ ω, ENNReal.ofReal ((net n).v k 0 ω ^ (2 + ε)) ∂(P n) := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    have h4 : (1 : ENNReal) + ENNReal.ofReal C ≤ ENNReal.ofReal (1 + max C 0) := by
      rw [ENNReal.ofReal_add zero_le_one (le_max_right _ _), ENNReal.ofReal_one]
      exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    exact ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((h1.trans (h2.le.trans (add_le_add le_rfl (hC n hn k)))).trans h4)
  simp only [Network.mu]
  exact inv_anti₀ hpos hle

/-- CHILD REDUCTION: Proposition 4 follows from the tightness child `TightPrim` and the A76
deterministic reflection glue (no measurability needed: outer measure throughout). -/
theorem prop4_of_tight (hT : TightPrim) : Prop4 := by
  intro K J Ω _ P net R mu s lam a c hA Q B hQ k δ' hδ'
  obtain ⟨hTA, hTS⟩ := hT K J Ω P net R mu s lam a c hA
  have hR0 : ∀ i j, 0 ≤ R i j := (hA.1 0) ▸ A76.routing_nonneg (net 0)
  have hRsp : Tendsto (fun m : ℕ => R ^ m) atTop (𝓝 0) := by
    have := (net 0).spectral
    rwa [show routingMatrixOf (P 0) (net 0).φ = R from hA.1 0] at this
  obtain ⟨w⟩ := A76.wt_exists hR0 hRsp
  obtain ⟨Cm, hCm, hmu⟩ := mu_lower net hA
  apply tendsto_zero_of_ofReal
  intro η hη
  set η' := η / (K + 1) with hη'
  have hη'0 : 0 < η' := by positivity
  obtain ⟨MA, hMA0, NA, hNA⟩ := bdd_of_tight hTA
    (fun n ω => by simp [diffScale, Atilde_zero]) η' hη'0
  choose MS hMS0 NS hNS using fun k => bdd_of_tight (hTS k)
    (fun n ω => by simp [diffScale, Stilde_zero]) η' hη'0
  set D := ∑ k, (|c k| + 1) with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun k _ => by positivity
  set Mt := MA + ∑ k, MS k + D with hMt
  have hMt0 : 0 ≤ Mt := add_nonneg (add_nonneg hMA0 (Finset.sum_nonneg fun k _ => hMS0 k)) hD0
  have h1θ : 0 < 1 - w.θ := by linarith [w.hθ1]
  set T := Mt / (1 - w.θ) * w.W with hT
  have hT0 : 0 ≤ T := mul_nonneg (div_nonneg hMt0 h1θ.le) (by linarith [w.hW])
  have hsq : ∀ᶠ n : ℕ in atTop, T / (Cm * δ') < Real.sqrt n :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  filter_upwards [drift_bdd net c hA.2.2.2.2.2.1, eventually_ge_atTop NA,
    eventually_all.2 fun k => eventually_ge_atTop (NS k), eventually_ge_atTop 1, hsq]
    with n hdr hnA hnS hn1 hnsq
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hgood : ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω) ∧
      ((∀ k ∈ J, Tendsto (fun l => (net n).U k l ω) atTop atTop) ∧
      (∀ k, Tendsto (fun l => (net n).V k l ω) atTop atTop)) := by
    filter_upwards [hQ n, A76.ae_good (net n)] with ω h1 h2 using ⟨h1, h2⟩
  have hsub : {ω | δ' ≤ |(n : ℝ)⁻¹ * Network.idle (B n ω) n k|} ⊆
      {ω | ¬ ((net n).IsQueueSolution ω (Q n ω) (B n ω) ∧
        ((∀ k ∈ J, Tendsto (fun l => (net n).U k l ω) atTop atTop) ∧
        (∀ k, Tendsto (fun l => (net n).V k l ω) atTop atTop)))} ∪
      ({ω | ∃ s ∈ Set.Icc (0:ℝ) 1, MA < ‖diffScale n (fun t => (net n).Atilde t ω) s‖} ∪
      ⋃ k, {ω | ∃ s ∈ Set.Icc (0:ℝ) 1,
        MS k < ‖diffScale n (fun t => (net n).Stilde k t ω) s‖}) := by
    intro ω hω
    rw [Set.mem_union, or_iff_not_imp_left]
    intro hg
    simp only [Set.mem_setOf_eq, not_not] at hg
    obtain ⟨hsol, hU, hV⟩ := hg
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists,
      not_and, not_lt] at hcon
    obtain ⟨hAb, hSb⟩ := hcon
    have hz : ∀ s ∈ Set.Icc (0:ℝ) 1,
        ‖diffScale n (fun t => (net n).Xtilde (B n ω) t ω) s‖ ≤ Mt := by
      intro s hs
      refine (zetaT_norm_le (net n) ω (B n ω) n (by omega) hs).trans ?_
      have h3 : ∑ k, ‖diffScale n (fun t => (net n).Stilde k t ω) (B n ω (n * s) k / n)‖ ≤
          ∑ k, MS k := Finset.sum_le_sum fun k _ =>
        hSb k _ (timechange_bound (net n) ω (Q n ω) (B n ω) hsol n (by omega) k hs).1
      have := hAb s hs
      rw [hMt]
      linarith
    have hb := idle_bound (net n) ω (Q n ω) (B n ω) hsol hU hV (hA.1 n) w hn1 hMt0 hz k
    rw [← hT] at hb
    set I := Network.idle (B n ω) n k
    have hmk := hmu n hn1 k
    have hmkpos : 0 < (net n).mu k := lt_of_lt_of_le hCm hmk
    have e : (n:ℝ)⁻¹ * I = ((Real.sqrt n)⁻¹ * ((net n).mu k * I)) * ((Real.sqrt n)⁻¹ * ((net n).mu k)⁻¹) := by
      have hs2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
      rw [show ((Real.sqrt n)⁻¹ * ((net n).mu k * I)) * ((Real.sqrt n)⁻¹ * ((net n).mu k)⁻¹) =
        (Real.sqrt n * Real.sqrt n)⁻¹ * ((net n).mu k * ((net n).mu k)⁻¹) * I by ring,
        mul_inv_cancel₀ hmkpos.ne', hs2, mul_one]
    have hω' : δ' ≤ |(n : ℝ)⁻¹ * I| := hω
    rw [e, abs_mul, abs_of_pos (mul_pos (inv_pos.2 hsqpos) (inv_pos.2 hmkpos))] at hω'
    have h5 : |(Real.sqrt n)⁻¹ * ((net n).mu k * I)| * ((Real.sqrt n)⁻¹ * ((net n).mu k)⁻¹) ≤
        T * ((Real.sqrt n)⁻¹ * Cm⁻¹) :=
      mul_le_mul hb (mul_le_mul_of_nonneg_left (inv_anti₀ hCm hmk) (inv_pos.2 hsqpos).le)
        (by positivity) hT0
    have h6 : T * ((Real.sqrt n)⁻¹ * Cm⁻¹) < δ' := by
      rw [div_lt_iff₀ (mul_pos hCm hδ')] at hnsq
      have : T * ((Real.sqrt n)⁻¹ * Cm⁻¹) = T / (Real.sqrt n * Cm) := by field_simp
      rw [this, div_lt_iff₀ (mul_pos hsqpos hCm)]
      nlinarith
    linarith
  calc P n {ω | δ' ≤ |(n : ℝ)⁻¹ * Network.idle (B n ω) n k|}
      ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ 0 + (ENNReal.ofReal η' + ∑ _k : Fin K, ENNReal.ofReal η') := by
        refine add_le_add (le_of_eq (ae_iff.1 hgood)) ((measure_union_le _ _).trans
          (add_le_add (hNA n hnA) ((measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun k _ => hNS k n (hnS k)))))
    _ = ENNReal.ofReal η := by
        rw [zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_add hη'0.le (by positivity)]
        congr 1
        rw [hη']; field_simp; ring

end Prop4

/-- CHILD `TightPrim` PROVED: renewal inversion + Etemadi/truncation random-walk tightness. -/
theorem tightPrim_proof : TightPrim := fun _K _J _Ω _ _P net _R _mu _s _lam _a _c hA =>
  ⟨NetT.tight_A net hA, fun k => NetT.tight_S net hA k⟩

/-- Sibling Proposition 4 (366195cb), now fully proved. -/
theorem prop4_proof : Prop4 := prop4_of_tight tightPrim_proof

section Main

variable {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)}

end Main

end P5


open Reiman84.QueueLength Filter Topology MeasureTheory in
theorem solution {K : ℕ} {J : Finset (Fin K)} {Ω : ℕ → Type}
    [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)} (net : ∀ n, Network K J (P n))
    (R : Matrix (Fin K) (Fin K) ℝ) (mu s lam a c : Fin K → ℝ)
    (hA : HeavyTrafficAssumptions net R mu s lam a c)
    (Q B : ∀ n, Ω n → ℝ → Fin K → ℝ)
    (hQ : ∀ n, ∀ᵐ ω ∂(P n), (net n).IsQueueSolution ω (Q n ω) (B n ω)) :
    ∀ k : Fin K, ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n : ℕ => P n {ω | δ ≤ |(n : ℝ)⁻¹ * Network.idle (B n ω) n k|})
        atTop (𝓝 0) := by
  exact P5.prop4_proof K J Ω P net R mu s lam a c hA Q B hQ
