-- Prove2me | solution 1 for PolylogKServer.Main.polylog_competitive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T09:40:15.745473+00:00
-- url     : https://prove2.me/submissions/c51dfe16-7d2c-4ecd-a33c-5fc07fce9b60

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PolylogKServer_Allocation_Problem
import Definitions.Def_PolylogKServer_Fractional_KServer
import Theorems.Thm_PolylogKServer_Allocation_frac_alloc_competitive
import Theorems.Thm_PolylogKServer_Fractional_kserver_from_allocation
import Theorems.Thm_PolylogKServer_Rounding_fractional_to_randomized
import Theorems.Thm_PolylogKServer_HST_exists_shallow_weighted_hst
import Theorems.Thm_PolylogKServer_HST_exists_hst_embedding_distribution
import Theorems.Thm_PolylogKServer_Fractional_frac_competitive_transfer


-- ===== Assembly.lean =====
/-!
Conditional assembly for b5077a04 (PolylogKServer.Main.polylog_competitive):
the parent follows from Theorems 5-8 (posted Open children) and the new children K1, K3, K4,
K5, K6, K8 (statements below). Everything in this file is proved; the children enter as
hypotheses.
-/

set_option autoImplicit false

namespace B5077a04

open PolylogKServer.HST PolylogKServer.Fractional PolylogKServer.Allocation

/-- The parent statement, verbatim. -/
def ParentStmt : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (M : Type) [MetricSpace M] [Fintype M]
      (C₀ : KServer.Config k M), 2 ≤ k → 3 ≤ Fintype.card M →
      ∃ A : KServer.RandomizedAlgorithm k M,
        A.IsCompetitiveFrom C₀
          (C * Real.log k ^ 2 * Real.log (Fintype.card M) ^ 3 *
            Real.log (Real.log (Fintype.card M)))

/-- Theorem 5 (ba300cc1), verbatim. -/
def T5 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (d k : ℕ) (w : Fin d → ℝ) (n₀ : Fin d → ℕ) (κ₀ : ℕ), 2 ≤ k →
        (∀ i, 0 < w i) → (∀ i, n₀ i ≤ k) → ∑ i, n₀ i ≤ κ₀ → κ₀ ≤ k →
        ∃ A : FracAlg d k, A.IsCompetitive w n₀ κ₀ (1 + ε) (C * Real.log (k / ε))

/-- Theorem 6 (17428d40), verbatim. -/
def T6 : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (d : ℕ) (w : Fin d → ℝ) (n₀ : Fin d → ℕ) (κ₀ : ℕ),
          (∀ i, 0 < w i) → (∀ i, n₀ i ≤ k) → ∑ i, n₀ i ≤ κ₀ → κ₀ ≤ k →
          ∃ A : FracAlg d k, A.IsCompetitive w n₀ κ₀ (1 + ε) (c₀ * Real.log (k / ε))) →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V) (σ : ℝ) (ℓ : ℕ),
        1 ≤ ℓ → T.height = ℓ → T.IsWeightedHST σ →
        C * ℓ * Real.log (k * ℓ) ≤ σ →
        ∀ (M : Type) [MetricSpace M] [Fintype M] (e : M ≃ T.Leaf),
          T.IsLeafMetric M e →
          ∀ C₀ : KServer.Config k M, Function.Injective C₀ →
          ∃ F : FracKServerAlg k M,
            F.IsCompetitiveFrom T e C₀ (C * ℓ * Real.log (k * ℓ))

/-- Theorem 7 (1c810f69), verbatim. -/
def T7 : Prop :=
  ∀ σ : ℝ, 5 < σ → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M] (e : M ≃ T.Leaf), T.IsLeafMetric M e →
      ∀ (k : ℕ) (C₀ : KServer.Config k M), Function.Injective C₀ →
      ∀ (F : FracKServerAlg k M) (c : ℝ), 0 ≤ c → F.IsCompetitiveFrom T e C₀ c →
        ∃ A : KServer.RandomizedAlgorithm k M, A.IsCompetitiveFrom C₀ (C * c)

/-- Theorem 8 (f43509a3), verbatim. -/
def T8 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), 1 < σ →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V), T.IsHST σ →
        2 ≤ Fintype.card T.Leaf →
        ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (T' : WTree V')
          (e : T.Leaf ≃ T'.Leaf),
          T'.IsWeightedHST σ ∧
          (T'.height : ℝ) ≤ C * Real.log (Fintype.card T.Leaf) ∧
          ∀ u v : T.Leaf,
            T'.treeDist (e u) (e v) ≤ T.treeDist u v ∧
            T.treeDist u v ≤ 2 * σ / (σ - 1) * T'.treeDist (e u) (e v)

/-- K1: Bartal/FRT probabilistic embedding into exact σ-HSTs, stretch O(σ log n / log σ). -/
def K1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ), 2 ≤ σ →
      ∀ (M : Type) [MetricSpace M] [Fintype M], 2 ≤ Fintype.card M →
        ∃ (r : ℕ) (p : Fin r → ℝ) (V : Fin r → Type) (_ : ∀ i, Fintype (V i))
          (_ : ∀ i, DecidableEq (V i)) (T : (i : Fin r) → WTree (V i))
          (e : (i : Fin r) → M ≃ (T i).Leaf),
          (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ (∀ i, (T i).IsHST σ) ∧
          (∀ i (x y : M), dist x y ≤ (T i).treeDist (e i x) (e i y)) ∧
          ∀ x y : M, ∑ i, p i * (T i).treeDist (e i x) (e i y) ≤
            C * σ * Real.log (Fintype.card M) / Real.log σ * dist x y

/-- K3: subdivide a 6^m-HST into a 6-HST; leaf distances scale by one constant c ∈ [1, 6/5]. -/
def K3 : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ {V : Type} [Fintype V] [DecidableEq V]
    (T : WTree V), T.IsHST ((6 : ℝ) ^ m) →
    ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (T' : WTree V') (e : T.Leaf ≃ T'.Leaf)
      (c : ℝ), 1 ≤ c ∧ c ≤ 6 / 5 ∧ T'.IsHST 6 ∧
      ∀ u v : T.Leaf, T'.treeDist (e u) (e v) = c * T.treeDist u v

/-- K4: dominating metrics with expected stretch D transfer c-competitive algorithms
(ratio c·D). -/
def K4 : Prop :=
  ∀ (k : ℕ) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : KServer.Config k M) (r : ℕ) (p : Fin r → ℝ) (X : Fin r → Type)
    [∀ i, MetricSpace (X i)] [∀ i, Fintype (X i)] (f : (i : Fin r) → M ≃ X i) (D c : ℝ),
    0 ≤ c → (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
    (∀ i (x y : M), dist x y ≤ dist (f i x) (f i y)) →
    (∀ x y : M, ∑ i, p i * dist (f i x) (f i y) ≤ D * dist x y) →
    (∀ i, ∃ A : KServer.RandomizedAlgorithm k (X i),
      A.IsCompetitiveFrom (fun j => f i (C₀ j)) c) →
    ∃ A : KServer.RandomizedAlgorithm k M, A.IsCompetitiveFrom C₀ (c * D)

/-- K5: the leaves of a weighted tree with the tree distance form a metric space. -/
def K5 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : WTree V),
    ∃ _ : MetricSpace T.Leaf, ∀ u v : T.Leaf, dist u v = T.treeDist u v

/-- K6: reduce to injective initial configurations (k > |M| by a lazy algorithm). -/
def K6 : Prop :=
  ∀ (k : ℕ) (M : Type) [MetricSpace M] [Fintype M] [Nonempty M] (c : ℝ), 0 ≤ c →
    (∀ C₀ : KServer.Config k M, Function.Injective C₀ →
      ∃ A : KServer.RandomizedAlgorithm k M, A.IsCompetitiveFrom C₀ c) →
    ∀ C₀ : KServer.Config k M, ∃ A : KServer.RandomizedAlgorithm k M, A.IsCompetitiveFrom C₀ c

/-- K8: a fractional algorithm competitive on one tree transfers to a tree whose leaf metric
dominates it within a factor c₁. -/
def K8 : Prop :=
  ∀ {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (T : WTree V) (T' : WTree V') (k : ℕ)
    (M : Type) [MetricSpace M] [Fintype M] (e : M ≃ T.Leaf), T.IsLeafMetric M e →
    ∀ (M' : Type) [MetricSpace M'] [Fintype M'] (e' : M' ≃ T'.Leaf), T'.IsLeafMetric M' e' →
    ∀ (g : M ≃ M') (c₁ c₂ : ℝ), 0 ≤ c₁ →
    (∀ x y : M, dist (g x) (g y) ≤ dist x y) →
    (∀ x y : M, dist x y ≤ c₁ * dist (g x) (g y)) →
    ∀ (C₀ : KServer.Config k M) (F : FracKServerAlg k M'),
    F.IsCompetitiveFrom T' e' (fun j => g (C₀ j)) c₂ → 0 ≤ c₂ →
    ∃ F' : FracKServerAlg k M, F'.IsCompetitiveFrom T e C₀ (c₁ * c₂)

/-! ## Small proved helpers -/

theorem offlineCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (C₀ : KServer.Config k M)
    (σ : List M) : 0 ≤ KServer.offlineCost C₀ σ := by
  unfold KServer.offlineCost
  apply Real.sInf_nonneg
  rintro c ⟨S, -, rfl⟩
  exact Finset.sum_nonneg fun j _ => by
    unfold KServer.moveCost
    exact Finset.sum_nonneg fun i _ => dist_nonneg

theorem rand_mono {k : ℕ} {M : Type} [MetricSpace M] {A : KServer.RandomizedAlgorithm k M}
    {C₀ : KServer.Config k M} {c c' : ℝ} (h : A.IsCompetitiveFrom C₀ c) (hcc : c ≤ c') :
    A.IsCompetitiveFrom C₀ c' := by
  obtain ⟨h0, a, ha⟩ := h
  refine ⟨h0, a, fun σ => (ha σ).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have h1 := mul_le_mul_of_nonneg_right hcc (offlineCost_nonneg C₀ σ)
  linarith

theorem frac_mono {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] {V : Type} [Fintype V]
    [DecidableEq V] {T : WTree V} {e : M ≃ T.Leaf} {F : FracKServerAlg k M}
    {C₀ : KServer.Config k M} {c c' : ℝ} (h : F.IsCompetitiveFrom T e C₀ c) (hcc : c ≤ c') :
    F.IsCompetitiveFrom T e C₀ c' := by
  obtain ⟨h1, h2, h3, a, ha⟩ := h
  refine ⟨h1, h2, h3, a, fun ρ => (ha ρ).trans ?_⟩
  have h4 := mul_le_mul_of_nonneg_right hcc (offlineCost_nonneg C₀ ρ)
  linarith

/-- A tree with two distinct leaves has height at least one. -/
theorem one_le_height {V : Type} [Fintype V] [DecidableEq V] (T : WTree V)
    (h : 2 ≤ Fintype.card T.Leaf) : 1 ≤ T.height := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card T.Leaf)
  have hab' : a.1 ≠ b.1 := fun h' => hab (Subtype.ext h')
  have key : ∀ u : T.Leaf, u.1 ≠ T.root → 1 ≤ T.height := by
    intro u hu
    have hd := T.depth_parent u.1 hu
    have hle : T.depth u.1 ≤ T.height := by
      unfold WTree.height
      exact Finset.le_sup (f := T.depth) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩)
    omega
  by_cases ha : a.1 = T.root
  · exact key b (fun hb => hab' (ha.trans hb.symm))
  · exact key a ha

/-! ## Arithmetic -/

theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem one_lt_log_six : 1 < Real.log 6 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- The ratio bound used at the end of the assembly. -/
theorem final_arith (K0 A L LL lk LL0 a2 x σ : ℝ) (hK0 : 0 ≤ K0) (hA : 6 ≤ A)
    (hL : 1 ≤ L) (hLL0 : 0 < LL0) (hLL : LL0 ≤ LL) (ha2 : 0 < a2) (hlk : a2 ≤ lk)
    (hx : x = A * L * (lk + LL + 1)) (hxσ : x ≤ σ) (hσx : σ ≤ 6 * x)
    (hlogσ : Real.log 6 + LL ≤ Real.log σ) :
    K0 * x * σ * L / Real.log σ ≤
      (6 * K0 * A ^ 2 * 3 * (1 / (Real.log 6 * LL0) + 1 / a2 ^ 2 + 1 / (a2 ^ 2 * LL0))) *
        lk ^ 2 * L ^ 3 * LL := by
  have h6 := one_lt_log_six
  set q := Real.log 6 + LL with hq
  set w := lk + LL + 1 with hw
  have hLLpos : 0 < LL := lt_of_lt_of_le hLL0 hLL
  have hlkpos : 0 < lk := lt_of_lt_of_le ha2 hlk
  have hqpos : 0 < q := by rw [hq]; linarith
  have hspos : 0 < Real.log σ := lt_of_lt_of_le hqpos hlogσ
  have hwpos : 1 ≤ w := by rw [hw]; linarith
  have hxpos : 0 ≤ x := by
    rw [hx]; have : 0 ≤ A * L := by nlinarith
    exact mul_nonneg this (by linarith)
  set B := 1 / (Real.log 6 * LL0) + 1 / a2 ^ 2 + 1 / (a2 ^ 2 * LL0) with hB
  -- the three terms
  have t1 : lk ^ 2 ≤ 1 / (Real.log 6 * LL0) * (lk ^ 2 * LL * q) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have e1 : Real.log 6 * LL0 ≤ LL * q := by
      have : Real.log 6 ≤ q := by rw [hq]; linarith
      nlinarith
    have e2 : 0 ≤ lk ^ 2 := sq_nonneg _
    nlinarith
  have t2 : LL ^ 2 ≤ 1 / a2 ^ 2 * (lk ^ 2 * LL * q) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have e1 : a2 ^ 2 ≤ lk ^ 2 := by nlinarith
    have e2 : LL ≤ q := by rw [hq]; linarith
    have e3 : LL ^ 2 ≤ LL * q := by nlinarith
    have e4 : 0 ≤ LL * q := by positivity
    nlinarith
  have t3 : (1 : ℝ) ≤ 1 / (a2 ^ 2 * LL0) * (lk ^ 2 * LL * q) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity), one_mul]
    have e1 : a2 ^ 2 ≤ lk ^ 2 := by nlinarith
    have e2 : 1 ≤ q := by rw [hq]; linarith
    have e3 : a2 ^ 2 * LL0 ≤ lk ^ 2 * LL := by
      have : 0 ≤ a2 ^ 2 := sq_nonneg _
      nlinarith
    have e4 : 0 ≤ lk ^ 2 * LL := by positivity
    nlinarith
  have hsum : lk ^ 2 + LL ^ 2 + 1 ≤ B * (lk ^ 2 * LL * q) := by
    rw [hB, add_mul, add_mul]; linarith
  have hw2 : w ^ 2 ≤ 3 * (lk ^ 2 + LL ^ 2 + 1) := by
    rw [hw]; nlinarith [sq_nonneg (lk - LL), sq_nonneg (lk - 1), sq_nonneg (LL - 1)]
  have hwq : w ^ 2 ≤ 3 * B * lk ^ 2 * LL * q := by nlinarith
  -- LHS ≤ K0 * x * (6x) * L / q
  have step1 : K0 * x * σ * L / Real.log σ ≤ K0 * x * (6 * x) * L / q := by
    have hnum : K0 * x * σ * L ≤ K0 * x * (6 * x) * L := by
      have : 0 ≤ K0 * x := mul_nonneg hK0 hxpos
      have := mul_le_mul_of_nonneg_left hσx this
      nlinarith
    have hnum0 : 0 ≤ K0 * x * σ * L := by
      have : 0 ≤ σ := le_trans hxpos hxσ
      positivity
    calc K0 * x * σ * L / Real.log σ ≤ K0 * x * σ * L / q :=
          div_le_div_of_nonneg_left hnum0 hqpos hlogσ
      _ ≤ K0 * x * (6 * x) * L / q := div_le_div_of_nonneg_right hnum hqpos.le
  refine step1.trans ?_
  rw [div_le_iff₀ hqpos, hx]
  have hA2 : 0 ≤ 6 * K0 * A ^ 2 * L ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_left hwq hA2
  have expand : K0 * (A * L * w) * (6 * (A * L * w)) * L = 6 * K0 * A ^ 2 * L ^ 3 * w ^ 2 := by
    ring
  rw [expand]
  calc 6 * K0 * A ^ 2 * L ^ 3 * w ^ 2 ≤ 6 * K0 * A ^ 2 * L ^ 3 * (3 * B * lk ^ 2 * LL * q) := this
    _ = 6 * K0 * A ^ 2 * 3 * B * lk ^ 2 * L ^ 3 * LL * q := by ring

/-- The ratio needed for Theorem 6 is below `x`. -/
theorem ratio6_le (C6 C8 L lk : ℝ) (hC6 : 0 < C6) (hC8 : 0 < C8) (hL : 1 ≤ L) (k ℓ : ℕ)
    (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) (hℓL : (ℓ : ℝ) ≤ C8 * L) (hlk : lk = Real.log k) :
    C6 * ℓ * Real.log (k * ℓ) ≤
      max 6 (C6 * max C8 1 * (1 + Real.log (max C8 1))) * L * (lk + Real.log L + 1) := by
  set C8' := max C8 1 with hC8'
  have hC8'1 : 1 ≤ C8' := le_max_right _ _
  have hlogC8' : 0 ≤ Real.log C8' := Real.log_nonneg hC8'1
  have hℓpos : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hkpos : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hℓ' : (ℓ : ℝ) ≤ C8' * L := by
    have : C8 * L ≤ C8' * L := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    linarith
  have hlogk : 0 ≤ lk := by rw [hlk]; exact Real.log_nonneg (by linarith)
  have hLL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogkl : Real.log (k * ℓ) = lk + Real.log ℓ := by
    rw [hlk, Real.log_mul (by positivity) (by positivity)]
  have hlogℓ : Real.log ℓ ≤ Real.log C8' + Real.log L := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) hℓ'
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓpos
  rw [hlogkl]
  have s1 : C6 * ℓ * (lk + Real.log ℓ) ≤ C6 * (C8' * L) * (lk + Real.log C8' + Real.log L) := by
    have h1 : lk + Real.log ℓ ≤ lk + Real.log C8' + Real.log L := by linarith
    have h2 : 0 ≤ lk + Real.log ℓ := by linarith
    have h3 : C6 * ℓ ≤ C6 * (C8' * L) := mul_le_mul_of_nonneg_left hℓ' hC6.le
    have h4 : 0 ≤ C6 * (C8' * L) := by positivity
    calc C6 * ℓ * (lk + Real.log ℓ) ≤ C6 * (C8' * L) * (lk + Real.log ℓ) :=
          mul_le_mul_of_nonneg_right h3 h2
      _ ≤ C6 * (C8' * L) * (lk + Real.log C8' + Real.log L) :=
          mul_le_mul_of_nonneg_left h1 h4
  have s2 : lk + Real.log C8' + Real.log L ≤ (1 + Real.log C8') * (lk + Real.log L + 1) := by
    nlinarith
  have s3 : C6 * (C8' * L) * (lk + Real.log C8' + Real.log L) ≤
      C6 * C8' * (1 + Real.log C8') * L * (lk + Real.log L + 1) := by
    have h4 : 0 ≤ C6 * (C8' * L) := by positivity
    have := mul_le_mul_of_nonneg_left s2 h4
    nlinarith
  have s4 : C6 * C8' * (1 + Real.log C8') * L * (lk + Real.log L + 1) ≤
      max 6 (C6 * C8' * (1 + Real.log C8')) * L * (lk + Real.log L + 1) := by
    have h5 : 0 ≤ L * (lk + Real.log L + 1) := by positivity
    have := mul_le_mul_of_nonneg_right (le_max_right 6 (C6 * C8' * (1 + Real.log C8'))) h5
    nlinarith
  linarith

theorem treeDist_nonneg' {V : Type} [Fintype V] [DecidableEq V] (T : WTree V) (u v : V) :
    0 ≤ T.treeDist u v := by
  unfold WTree.treeDist
  apply Finset.sum_nonneg
  intro y hy
  split_ifs
  · exact le_rfl
  · exact (T.W_pos y (Finset.mem_filter.mp hy).2).le

/-- **Assembly**: the parent from Theorems 5-8 and K1, K3, K4, K5, K6, K8. -/
theorem parent_of_children (h5 : T5) (h6 : T6) (h7 : T7) (h8 : T8) (k1 : K1) (k3 : K3)
    (k4 : K4) (k5 : K5) (k6 : K6) (k8 : K8) : ParentStmt := by
  obtain ⟨C5, hC5, H5⟩ := h5
  obtain ⟨C6, hC6, H6⟩ := h6 C5 hC5
  obtain ⟨C7, hC7, H7⟩ := h7 6 (by norm_num)
  obtain ⟨C8, hC8, H8⟩ := h8
  obtain ⟨C1, hC1, H1⟩ := k1
  have hlog3 := one_lt_log_three
  have hlog6 := one_lt_log_six
  have hLL0 : 0 < Real.log (Real.log 3) := Real.log_pos hlog3
  have ha2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = max 6 (C6 * max C8 1 * (1 + Real.log (max C8 1))) := ⟨_, rfl⟩
  have hA6 : (6 : ℝ) ≤ A := hAdef ▸ le_max_left _ _
  obtain ⟨K0, hK0def⟩ : ∃ K0 : ℝ, K0 = C7 * (72 / 25) * (6 / 5) * C1 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K0 := by rw [hK0def]; positivity
  have hB : 0 < 1 / (Real.log 6 * Real.log (Real.log 3)) + 1 / Real.log 2 ^ 2 +
      1 / (Real.log 2 ^ 2 * Real.log (Real.log 3)) :=
    add_pos (add_pos (div_pos one_pos (mul_pos (by linarith) hLL0)) (div_pos one_pos (pow_pos ha2 2)))
      (div_pos one_pos (mul_pos (pow_pos ha2 2) hLL0))
  have hK0pos : 0 < K0 := by rw [hK0def]; positivity
  refine ⟨6 * K0 * A ^ 2 * 3 * (1 / (Real.log 6 * Real.log (Real.log 3)) + 1 / Real.log 2 ^ 2 +
      1 / (Real.log 2 ^ 2 * Real.log (Real.log 3))), by
        have : 0 < A := by linarith
        positivity, ?_⟩
  intro k M _ _ C₀ hk hn
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (Fintype.card M) := ⟨_, rfl⟩
  obtain ⟨LL, hLLdef⟩ : ∃ LL : ℝ, LL = Real.log L := ⟨_, rfl⟩
  obtain ⟨lk, hlkdef⟩ : ∃ lk : ℝ, lk = Real.log k := ⟨_, rfl⟩
  rw [← hLdef, ← hLLdef, ← hlkdef]
  have hn' : (3 : ℝ) ≤ Fintype.card M := by exact_mod_cast hn
  have hL3 : Real.log 3 ≤ L := hLdef ▸ Real.log_le_log (by norm_num) hn'
  have hL1 : 1 ≤ L := by linarith
  have hLL : Real.log (Real.log 3) ≤ LL := hLLdef ▸ Real.log_le_log (by linarith) hL3
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlk : Real.log 2 ≤ lk := hlkdef ▸ Real.log_le_log (by norm_num) hk'
  haveI : Nonempty M := Fintype.card_pos_iff.mp (by omega)
  have hratio0 : 0 ≤ 6 * K0 * A ^ 2 * 3 * (1 / (Real.log 6 * Real.log (Real.log 3)) +
      1 / Real.log 2 ^ 2 + 1 / (Real.log 2 ^ 2 * Real.log (Real.log 3))) * lk ^ 2 * L ^ 3 * LL := by
    have h1 : 0 ≤ LL := by linarith
    have h2 : 0 ≤ L := by linarith
    have : 0 < A := by linarith
    positivity
  refine k6 k M _ hratio0 ?_ C₀
  intro C₀ hinj
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = A * L * (lk + LL + 1) := ⟨_, rfl⟩
  have hx6 : 6 ≤ x := by
    have h1 : 6 ≤ A * L := by nlinarith
    have h2 : 1 ≤ lk + LL + 1 := by linarith
    rw [hxdef]; nlinarith
  obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, x ≤ (6 : ℝ) ^ m ∧ ∀ j < m, ¬ x ≤ (6 : ℝ) ^ j := by
    classical
    have hex : ∃ m : ℕ, x ≤ (6 : ℝ) ^ m :=
      (pow_unbounded_of_one_lt x (by norm_num : (1:ℝ) < 6)).imp fun _ h => h.le
    exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hm; linarith
    · exact h
  have hσx : (6 : ℝ) ^ m ≤ 6 * x := by
    have h1 := hmin (m - 1) (by omega)
    push_neg at h1
    have : (6 : ℝ) ^ m = 6 * 6 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; linarith
  have hσ6 : (6 : ℝ) ≤ 6 ^ m := le_trans hx6 hm
  have hlogσ : Real.log 6 + LL ≤ Real.log ((6 : ℝ) ^ m) := by
    have hxpos : 0 < x := by linarith
    have h1 : Real.log x ≤ Real.log ((6 : ℝ) ^ m) := Real.log_le_log hxpos hm
    have hApos : 0 < A := by linarith
    have hw : 0 < lk + LL + 1 := by linarith
    have h2 : Real.log x = Real.log A + Real.log L + Real.log (lk + LL + 1) := by
      rw [hxdef, Real.log_mul (by positivity) hw.ne', Real.log_mul hApos.ne' (by positivity)]
    have h3 : Real.log 6 ≤ Real.log A := Real.log_le_log (by norm_num) hA6
    have h4 : 0 ≤ Real.log (lk + LL + 1) := Real.log_nonneg (by linarith)
    rw [hLLdef]; linarith
  have hn2 : 2 ≤ Fintype.card M := by omega
  obtain ⟨r, p, V, iF, iD, T, e, hp, hp1, hT, hdom, hstr⟩ := H1 ((6 : ℝ) ^ m) (by linarith) M hn2
  have hcardT : ∀ i, Fintype.card (T i).Leaf = Fintype.card M :=
    fun i => (Fintype.card_congr (e i)).symm
  have h8i := fun i => H8 ((6 : ℝ) ^ m) (by linarith) (V i) (T i) (hT i)
    (by rw [hcardT i]; exact hn2)
  choose V' iF' iD' T' f hT'w hT'h hT'd using h8i
  choose V6 iF6 iD6 T6 g c hc1 hc2 hT6 hd6 using fun i => k3 m hm1 (T i) (hT i)
  choose mT' hmT' using fun i => k5 (T' i)
  choose m6 hm6 using fun i => k5 (T6 i)
  have hAi : ∀ i, ∃ Ai : KServer.RandomizedAlgorithm k (T6 i).Leaf,
      Ai.IsCompetitiveFrom (fun j => ((e i).trans (g i)) (C₀ j)) (C7 * (72 / 25 * x)) := by
    intro i
    let G : (T6 i).Leaf ≃ (T' i).Leaf := (g i).symm.trans (f i)
    let C6c : KServer.Config k (T6 i).Leaf := fun j => ((e i).trans (g i)) (C₀ j)
    have hinj6 : Function.Injective C6c :=
      fun a b hab => hinj (((e i).trans (g i)).injective hab)
    have hinj' : Function.Injective (fun j => G (C6c j)) := fun a b hab => hinj6 (G.injective hab)
    have hcard' : 2 ≤ Fintype.card (T' i).Leaf := by
      rw [← Fintype.card_congr (f i), hcardT i]; exact hn2
    have hℓ1 : 1 ≤ (T' i).height := one_le_height (T' i) hcard'
    have hℓL : ((T' i).height : ℝ) ≤ C8 * L := by
      have := hT'h i; rwa [hcardT i, ← hLdef] at this
    have hr6 := ratio6_le C6 C8 L lk hC6 hC8 hL1 k (T' i).height hk hℓ1 hℓL hlkdef
    rw [← hAdef, ← hLLdef, ← hxdef] at hr6
    obtain ⟨F', hF'⟩ := H6 k hk
      (fun ε hε hε1 d w n₀ κ₀ hw hn₀ hs hκ => H5 ε hε hε1 d k w n₀ κ₀ hk hw hn₀ hs hκ)
      (V' i) (T' i) ((6 : ℝ) ^ m) (T' i).height hℓ1 rfl (hT'w i) (by linarith) (T' i).Leaf
      (Equiv.refl _) (fun a b => hmT' i a b) (fun j => G (C6c j)) hinj'
    have hF'x := frac_mono hF' hr6
    have hle : ∀ a b : (T6 i).Leaf, dist (G a) (G b) ≤ dist a b := by
      intro a b
      rw [hmT' i, hm6 i]
      have h1 : (T' i).treeDist (G a) (G b) ≤ (T i).treeDist ((g i).symm a) ((g i).symm b) :=
        (hT'd i ((g i).symm a) ((g i).symm b)).1
      have h2 := hd6 i ((g i).symm a) ((g i).symm b)
      simp only [Equiv.apply_symm_apply] at h2
      have hnn := treeDist_nonneg' (T i) ((g i).symm a) ((g i).symm b)
      rw [h2]
      exact h1.trans (le_mul_of_one_le_left hnn (hc1 i))
    have hge : ∀ a b : (T6 i).Leaf, dist a b ≤ 72 / 25 * dist (G a) (G b) := by
      intro a b
      rw [hmT' i, hm6 i]
      have h1 : (T i).treeDist ((g i).symm a) ((g i).symm b) ≤
          2 * (6 : ℝ) ^ m / ((6 : ℝ) ^ m - 1) * (T' i).treeDist (G a) (G b) :=
        (hT'd i ((g i).symm a) ((g i).symm b)).2
      have h2 := hd6 i ((g i).symm a) ((g i).symm b)
      simp only [Equiv.apply_symm_apply] at h2
      rw [h2]
      have hσ' : 2 * (6 : ℝ) ^ m / ((6 : ℝ) ^ m - 1) ≤ 12 / 5 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have ht' := treeDist_nonneg' (T' i) (G a) (G b)
      have ht := treeDist_nonneg' (T i) ((g i).symm a) ((g i).symm b)
      have h3 := le_trans h1 (mul_le_mul_of_nonneg_right hσ' ht')
      have h4 := mul_le_mul_of_nonneg_right (hc2 i) ht
      linarith
    obtain ⟨F6, hF6⟩ := k8 (T6 i) (T' i) k (T6 i).Leaf (Equiv.refl _) (fun a b => hm6 i a b)
      (T' i).Leaf (Equiv.refl _) (fun a b => hmT' i a b) G (72 / 25) x (by norm_num) hle hge
      C6c F' hF'x (by linarith)
    exact H7 (V6 i) (T6 i) (hT6 i) (T6 i).Leaf (Equiv.refl _) (fun a b => hm6 i a b) k C6c
      hinj6 F6 (72 / 25 * x) (by linarith) hF6
  have hdom' : ∀ i (a b : M), dist a b ≤ dist (((e i).trans (g i)) a) (((e i).trans (g i)) b) := by
    intro i a b
    rw [hm6 i]
    have h2 : (T6 i).treeDist (((e i).trans (g i)) a) (((e i).trans (g i)) b) =
        c i * (T i).treeDist (e i a) (e i b) := hd6 i (e i a) (e i b)
    rw [h2]
    have hnn := treeDist_nonneg' (T i) (e i a) (e i b)
    exact (hdom i a b).trans (le_mul_of_one_le_left hnn (hc1 i))
  have hstr' : ∀ a b : M, ∑ i, p i * dist (((e i).trans (g i)) a) (((e i).trans (g i)) b) ≤
      (6 / 5 * (C1 * (6 : ℝ) ^ m * L / Real.log ((6 : ℝ) ^ m))) * dist a b := by
    intro a b
    have h1 : ∀ i, p i * dist (((e i).trans (g i)) a) (((e i).trans (g i)) b) ≤
        6 / 5 * (p i * (T i).treeDist (e i a) (e i b)) := by
      intro i
      rw [hm6 i]
      have h2 : (T6 i).treeDist (((e i).trans (g i)) a) (((e i).trans (g i)) b) =
          c i * (T i).treeDist (e i a) (e i b) := hd6 i (e i a) (e i b)
      rw [h2]
      have hnn := treeDist_nonneg' (T i) (e i a) (e i b)
      have h3 := mul_le_mul_of_nonneg_right (hc2 i) hnn
      have h4 := mul_le_mul_of_nonneg_left h3 (hp i)
      linarith
    have h5 := hstr a b
    rw [← hLdef] at h5
    calc ∑ i, p i * dist (((e i).trans (g i)) a) (((e i).trans (g i)) b)
        ≤ ∑ i, 6 / 5 * (p i * (T i).treeDist (e i a) (e i b)) := Finset.sum_le_sum fun i _ => h1 i
      _ = 6 / 5 * ∑ i, p i * (T i).treeDist (e i a) (e i b) := by rw [Finset.mul_sum]
      _ ≤ 6 / 5 * (C1 * (6 : ℝ) ^ m * L / Real.log ((6 : ℝ) ^ m) * dist a b) := by linarith
      _ = (6 / 5 * (C1 * (6 : ℝ) ^ m * L / Real.log ((6 : ℝ) ^ m))) * dist a b := by ring
  obtain ⟨A0, hA0⟩ := k4 k M C₀ r p (fun i => (T6 i).Leaf) (fun i => (e i).trans (g i)) _
    (C7 * (72 / 25 * x)) (by positivity) hp hp1 hdom' hstr' hAi
  refine ⟨A0, rand_mono hA0 ?_⟩
  have hfin := final_arith K0 A L LL lk (Real.log (Real.log 3)) (Real.log 2) x ((6 : ℝ) ^ m)
    hK0 hA6 hL1 hLL0 hLL ha2 hlk hxdef hm hσx hlogσ
  have hspos : 0 < Real.log ((6 : ℝ) ^ m) := by linarith
  calc C7 * (72 / 25 * x) * (6 / 5 * (C1 * (6 : ℝ) ^ m * L / Real.log ((6 : ℝ) ^ m)))
      = K0 * x * (6 : ℝ) ^ m * L / Real.log ((6 : ℝ) ^ m) := by
        rw [hK0def]; field_simp
    _ ≤ _ := hfin

end B5077a04

-- ===== K3.lean =====
set_option autoImplicit false

namespace B5077a04K3

open PolylogKServer.HST

variable {V : Type} [Fintype V] [DecidableEq V]

/-- K3 statement (verbatim from Assembly.lean). -/
def K3 : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ {V : Type} [Fintype V] [DecidableEq V]
    (T : WTree V), T.IsHST ((6 : ℝ) ^ m) →
    ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (T' : WTree V') (e : T.Leaf ≃ T'.Leaf)
      (c : ℝ), 1 ≤ c ∧ c ≤ 6 / 5 ∧ T'.IsHST 6 ∧
      ∀ u v : T.Leaf, T'.treeDist (e u) (e v) = c * T.treeDist u v

theorem anc_trans (T : WTree V) {a b c : V} (h1 : T.IsAnc a b) (h2 : T.IsAnc b c) :
    T.IsAnc a c := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := h2
  exact ⟨i + j, by rw [Function.iterate_add_apply, hj, hi]⟩

theorem anc_parent (T : WTree V) {a b : V} (h : T.IsAnc a b) : T.IsAnc (T.parent a) b := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i + 1, by rw [Function.iterate_succ_apply', hi]⟩

theorem root_anc (T : WTree V) (v : V) : T.IsAnc T.root v := by
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ d ih =>
    by_cases hv : v = T.root
    · exact ⟨0, hv⟩
    · have h := T.depth_parent v hv
      obtain ⟨i, hi⟩ := ih (T.depth (T.parent v)) (by omega) (T.parent v) rfl
      exact ⟨i + 1, by rw [Function.iterate_succ_apply]; exact hi⟩

/-- Depth in the subdivided tree. -/
def sdepth (T : WTree V) (n : ℕ) (p : V × Fin (n + 1)) : ℕ :=
  (n + 1) * T.depth p.1 + (n - p.2.val)

/-- Parent in the subdivided tree. -/
def sparent (T : WTree V) (n : ℕ) (p : V × Fin (n + 1)) : V × Fin (n + 1) :=
  if h : p.2.val < n then (p.1, ⟨p.2.val + 1, by omega⟩)
  else if p.1 = T.root then (T.root, Fin.last n) else (T.parent p.1, 0)

/-- Subdivide every edge into `n + 1` geometric pieces (ratio 6); the root carries a chain of
`n` extra edges above it, used by no leaf path. -/
noncomputable def subdiv (T : WTree V) (n : ℕ) (L : ℝ) (hL : 0 < L) :
    WTree (V × Fin (n + 1)) where
  root := (T.root, Fin.last n)
  parent := sparent T n
  depth := sdepth T n
  parent_root := by simp [sparent]
  depth_root := by simp [sdepth, T.depth_root]
  depth_parent := by
    rintro ⟨v, j⟩ hne
    unfold sparent sdepth
    by_cases h : j.val < n
    · simp only [h, dite_true]; omega
    · simp only [h, dite_false]
      have hj : j = Fin.last n := Fin.ext (by simp; omega)
      by_cases hv : v = T.root
      · exact absurd (by rw [hv, hj]) hne
      · simp only [hv, if_false]
        have := T.depth_parent v hv
        simp only [Fin.val_zero, hj, Fin.val_last] at *
        rw [← this]; ring_nf; omega
  W p := L * 6 ^ n / (6 : ℝ) ^ (sdepth T n p - 1)
  W_pos _ _ := by positivity

variable (T : WTree V) (n : ℕ) (L : ℝ) (hL : 0 < L)

theorem iter_chain (v : V) (i : ℕ) (hi : i ≤ n) :
    (sparent T n)^[i] (v, 0) = (v, ⟨i, by omega⟩) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp [sparent, show i < n by omega]

theorem anc_up (v : V) (hv : v ≠ T.root) :
    (subdiv T n L hL).IsAnc (T.parent v, 0) (v, 0) := by
  refine ⟨n + 1, ?_⟩
  show (sparent T n)^[n + 1] (v, 0) = _
  rw [Function.iterate_succ_apply', iter_chain T n v n le_rfl]
  simp [sparent, hv]

theorem anc_iter (u : V) (k : ℕ) :
    (subdiv T n L hL).IsAnc (T.parent^[k] u, 0) (u, 0) := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases hx : T.parent^[k] u = T.root
    · rw [hx, T.parent_root]; rw [hx] at ih; exact ih
    · exact anc_trans _ (anc_up T n L hL _ hx) ih

theorem anc_of_anc (w u : V) (i : Fin (n + 1)) (h : T.IsAnc w u) :
    (subdiv T n L hL).IsAnc (w, i) (u, 0) := by
  obtain ⟨k, hk⟩ := h
  have h1 := anc_iter T n L hL u k
  rw [hk] at h1
  refine anc_trans _ ⟨i.val, ?_⟩ h1
  show (sparent T n)^[i.val] (w, 0) = (w, i)
  rw [iter_chain T n w i.val (by omega)]

theorem anc_proj (x : V × Fin (n + 1)) (u : V) (h : (subdiv T n L hL).IsAnc x (u, 0)) :
    T.IsAnc x.1 u := by
  obtain ⟨k, hk⟩ := h
  subst hk
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show T.IsAnc (sparent T n _).1 u
    unfold sparent
    split_ifs with h1 h2
    · exact ih
    · rw [h2] at ih; exact ih
    · exact anc_parent T ih

theorem anc_iff (w u : V) (i : Fin (n + 1)) :
    (subdiv T n L hL).IsAnc (w, i) (u, 0) ↔ T.IsAnc w u :=
  ⟨fun h => anc_proj T n L hL (w, i) u h, anc_of_anc T n L hL w u i⟩

theorem leaf_iff (v : V) (j : Fin (n + 1)) :
    (subdiv T n L hL).IsLeaf (v, j) ↔ j = 0 ∧ T.IsLeaf v := by
  constructor
  · intro h
    by_cases hj : j = 0
    · refine ⟨hj, fun u hu hp => ?_⟩
      refine h (u, Fin.last n) ?_ ?_
      · intro he; exact hu (congrArg Prod.fst he)
      · show sparent T n (u, Fin.last n) = (v, j)
        simp [sparent, hu, hp, hj]
    · exfalso
      have hj0 : 0 < j.val := Nat.pos_of_ne_zero (fun h0 => hj (Fin.ext h0))
      refine h (v, ⟨j.val - 1, by omega⟩) ?_ ?_
      · intro he
        change (v, _) = (T.root, Fin.last n) at he
        have := congrArg (fun p => p.2.val) he
        simp at this; omega
      · show sparent T n (v, ⟨j.val - 1, by omega⟩) = (v, j)
        simp only [sparent, show j.val - 1 < n by omega, dite_true]
        exact Prod.ext rfl (Fin.ext (by simp; omega))
  · rintro ⟨rfl, hv⟩ ⟨u, i⟩ hne hp
    change sparent T n (u, i) = (v, 0) at hp
    unfold sparent at hp
    split_ifs at hp with h1 h2
    · have := congrArg (fun p => p.2.val) hp
      simp at this
    · apply hne
      simp only at h1 h2
      have hi : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
      show (u, i) = (T.root, Fin.last n)
      rw [h2, hi]
    · have hpu := congrArg Prod.fst hp
      simp at hpu
      exact hv u h2 hpu

/-- The bijection of leaves. -/
noncomputable def leafEquiv : T.Leaf ≃ (subdiv T n L hL).Leaf where
  toFun u := ⟨(u.1, 0), (leaf_iff T n L hL u.1 0).2 ⟨rfl, u.2⟩⟩
  invFun x := ⟨x.1.1, ((leaf_iff T n L hL x.1.1 x.1.2).1 x.2).2⟩
  left_inv u := rfl
  right_inv x := by
    obtain ⟨⟨v, j⟩, hx⟩ := x
    have hj := ((leaf_iff T n L hL v j).1 hx).1
    subst hj; rfl

/-- The scale factor. -/
noncomputable def cfac (n : ℕ) : ℝ := ∑ i : Fin (n + 1), (1 / 6 : ℝ) ^ (n - i.val)

theorem cfac_eq : cfac n = ∑ j ∈ Finset.range (n + 1), (1 / 6 : ℝ) ^ j := by
  unfold cfac
  rw [Fin.sum_univ_eq_sum_range (fun i => (1 / 6 : ℝ) ^ (n - i)) (n + 1)]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  congr 1; omega

theorem one_le_cfac : 1 ≤ cfac n := by
  rw [cfac_eq, Finset.sum_range_succ']
  have : 0 ≤ ∑ j ∈ Finset.range n, (1 / 6 : ℝ) ^ (j + 1) :=
    Finset.sum_nonneg fun _ _ => by positivity
  rw [pow_zero]; linarith

theorem cfac_le : cfac n ≤ 6 / 5 := by
  rw [cfac_eq, geom_sum_eq (by norm_num)]
  have h : 0 ≤ (1 / 6 : ℝ) ^ (n + 1) := by positivity
  rw [div_le_iff_of_neg (by norm_num)]
  linarith

theorem W_sum (w : V) (hw : w ≠ T.root) :
    ∑ i : Fin (n + 1), (subdiv T n L hL).W (w, i) =
      cfac n * (L / ((6 : ℝ) ^ (n + 1)) ^ (T.depth w - 1)) := by
  have hd : 1 ≤ T.depth w := by have := T.depth_parent w hw; omega
  unfold cfac
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  show L * 6 ^ n / (6 : ℝ) ^ (sdepth T n (w, i) - 1) = _
  have he : sdepth T n (w, i) - 1 = (n + 1) * (T.depth w - 1) + n + (n - i.val) := by
    unfold sdepth; simp only
    have := i.isLt
    obtain ⟨d, hd'⟩ : ∃ d, T.depth w = d + 1 := ⟨T.depth w - 1, by omega⟩
    rw [hd']; simp only [Nat.add_sub_cancel]; ring_nf; omega
  rw [he, pow_add, pow_add, pow_mul, one_div_pow]
  field_simp

open Classical in
theorem treeDist_sub (u v : V) :
    (subdiv T n L hL).treeDist (u, 0) (v, 0) =
      cfac n * ∑ x ∈ Finset.univ.filter (fun x => x ≠ T.root),
        if (T.IsAnc x u ↔ T.IsAnc x v) then 0 else L / ((6 : ℝ) ^ (n + 1)) ^ (T.depth x - 1) := by
  classical
  unfold WTree.treeDist
  rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : w = T.root
  · subst hw
    simp only [ne_eq, not_true_eq_false, if_false, mul_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 := anc_of_anc T n L hL T.root u i (root_anc T u)
    have h2 := anc_of_anc T n L hL T.root v i (root_anc T v)
    simp [h1, h2]
  · have hne : ∀ i : Fin (n + 1), (w, i) ≠ (subdiv T n L hL).root := by
      intro i he; exact hw (congrArg Prod.fst he)
    simp only [hne, hw, ne_eq, not_false_eq_true, if_true, anc_iff]
    by_cases h : (T.IsAnc w u ↔ T.IsAnc w v)
    · simp [h]
    · simp only [h, if_false]
      exact W_sum T n L hL w hw

theorem k3_proof : K3 := by
  intro m hm V _ _ T hT
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨L, hL, hW⟩ := hT
  refine ⟨V × Fin (n + 1), inferInstance, inferInstance, subdiv T n L hL,
    leafEquiv T n L hL, cfac n, one_le_cfac n, cfac_le n, ⟨L * 6 ^ n, by positivity, ?_⟩, ?_⟩
  · intro p _; rfl
  · intro u v
    show (subdiv T n L hL).treeDist (u.1, 0) (v.1, 0) = _
    rw [treeDist_sub]
    congr 1
    unfold WTree.treeDist
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := (Finset.mem_filter.1 hx).2
    rw [hW x hx']

end B5077a04K3

-- ===== K5.lean =====
set_option autoImplicit false

namespace B5077a04K5

open PolylogKServer.HST

variable {V : Type} [Fintype V] [DecidableEq V]

open Classical in
theorem treeDist_eq (T : WTree V) (u v : V) :
    T.treeDist u v = ∑ x ∈ Finset.univ.filter (fun x => x ≠ T.root),
      if (T.IsAnc x u ↔ T.IsAnc x v) then 0 else T.W x := by
  unfold WTree.treeDist
  congr 1

/-- A non-root leaf is an ancestor of itself only. -/
theorem anc_leaf_eq (T : WTree V) {u : V} (hu : T.IsLeaf u) (hr : u ≠ T.root) {v : V}
    (h : T.IsAnc u v) : v = u := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | zero => simpa using hi
  | succ j =>
    exfalso
    rw [Function.iterate_succ_apply'] at hi
    by_cases hy : T.parent^[j] v = T.root
    · rw [hy, T.parent_root] at hi
      exact hr hi.symm
    · exact hu _ hy hi

theorem anc_self (T : WTree V) (u : V) : T.IsAnc u u := ⟨0, rfl⟩

theorem exists_sep (T : WTree V) (u v : T.Leaf) (huv : u ≠ v) :
    ∃ x, x ≠ T.root ∧ ¬ (T.IsAnc x u.1 ↔ T.IsAnc x v.1) := by
  by_cases hu : u.1 = T.root
  · have hv : v.1 ≠ T.root := by
      intro hv; exact huv (Subtype.ext (hu.trans hv.symm))
    refine ⟨v.1, hv, fun h => ?_⟩
    have := anc_leaf_eq T v.2 hv (h.2 (anc_self T v.1))
    exact huv (Subtype.ext this)
  · refine ⟨u.1, hu, fun h => ?_⟩
    have := anc_leaf_eq T u.2 hu (h.1 (anc_self T u.1))
    exact huv (Subtype.ext this.symm)

theorem treeDist_self (T : WTree V) (u : V) : T.treeDist u u = 0 := by
  rw [treeDist_eq]; simp

theorem treeDist_comm (T : WTree V) (u v : V) : T.treeDist u v = T.treeDist v u := by
  rw [treeDist_eq, treeDist_eq]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases a : T.IsAnc x u <;> by_cases b : T.IsAnc x v <;> simp [a, b]

theorem treeDist_triangle (T : WTree V) (u v w : V) :
    T.treeDist u w ≤ T.treeDist u v + T.treeDist v w := by
  rw [treeDist_eq, treeDist_eq, treeDist_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x hx => ?_
  have hW : 0 ≤ T.W x := (T.W_pos x (Finset.mem_filter.1 hx).2).le
  by_cases a : T.IsAnc x u <;> by_cases b : T.IsAnc x v <;> by_cases c : T.IsAnc x w <;>
    simp [a, b, c, hW]

theorem treeDist_pos (T : WTree V) (u v : T.Leaf) (huv : u ≠ v) : 0 < T.treeDist u.1 v.1 := by
  obtain ⟨x, hx, hsep⟩ := exists_sep T u v huv
  rw [treeDist_eq]
  apply Finset.sum_pos'
  · intro y hy
    have := T.W_pos y (Finset.mem_filter.1 hy).2
    split_ifs <;> linarith
  · refine ⟨x, by simp [hx], ?_⟩
    rw [if_neg hsep]; exact T.W_pos x hx

/-- The leaf metric of a weighted tree. -/
noncomputable def leafMetric (T : WTree V) : MetricSpace T.Leaf where
  dist u v := T.treeDist u.1 v.1
  dist_self u := treeDist_self T u.1
  dist_comm u v := treeDist_comm T u.1 v.1
  dist_triangle u v w := treeDist_triangle T u.1 v.1 w.1
  eq_of_dist_eq_zero {u v} h := by
    by_contra huv
    exact (treeDist_pos T u v huv).ne' h

end B5077a04K5

open PolylogKServer.HST in
theorem k5_proof :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (T : WTree V),
      ∃ _ : MetricSpace T.Leaf, ∀ u v : T.Leaf, dist u v = T.treeDist u v :=
  fun T => ⟨B5077a04K5.leafMetric T, fun _ _ => rfl⟩

-- ===== K46.lean =====
/-!
Lemma R (measurable regularization) for b5077a04: a family of deterministic online algorithms
over a probability space whose costs are bounded pointwise by integrable functions `h σ`
(the costs themselves need not be measurable) yields a genuine `RandomizedAlgorithm` whose
expected costs are at most `∫ h σ`. Proof: upper integral `upper` (sublinear), Hahn-Banach,
Riesz-Markov-Kakutani on the compact space `List M → Config k M`.
-/

set_option autoImplicit false

namespace B5077a04R

open MeasureTheory KServer CompactlySupported CompactlySupportedContinuousMap
open scoped Pointwise

section Upper

variable {ι : Type} [MeasurableSpace ι] (μ : Measure ι)

/-- The integrals of integrable majorants of `F`. -/
def majSet (F : ι → ℝ) : Set ℝ :=
  {x | ∃ g : ι → ℝ, Integrable g μ ∧ (∀ i, F i ≤ g i) ∧ x = ∫ i, g i ∂μ}

/-- The upper integral. -/
noncomputable def upper (F : ι → ℝ) : ℝ := sInf (majSet μ F)

def Bnd (F : ι → ℝ) : Prop := ∃ c, ∀ i, |F i| ≤ c

variable [IsProbabilityMeasure μ]

theorem majSet_ne_bdd {F : ι → ℝ} (hF : Bnd F) :
    (majSet μ F).Nonempty ∧ BddBelow (majSet μ F) := by
  obtain ⟨c, hc⟩ := hF
  refine ⟨⟨_, fun _ => c, integrable_const c, fun i => (le_abs_self _).trans (hc i), rfl⟩, -c, ?_⟩
  rintro x ⟨g, hg, hFg, rfl⟩
  have h1 : ∫ _i, (-c) ∂μ ≤ ∫ i, g i ∂μ :=
    integral_mono (integrable_const _) hg (fun i => (neg_le_of_abs_le (hc i)).trans (hFg i))
  simpa using h1

theorem upper_le_integral {F : ι → ℝ} (hF : Bnd F) {g : ι → ℝ} (hg : Integrable g μ)
    (h : ∀ i, F i ≤ g i) : upper μ F ≤ ∫ i, g i ∂μ :=
  csInf_le (majSet_ne_bdd μ hF).2 ⟨g, hg, h, rfl⟩

theorem upper_nonneg {F : ι → ℝ} (hF : Bnd F) (h0 : ∀ i, 0 ≤ F i) : 0 ≤ upper μ F := by
  refine le_csInf (majSet_ne_bdd μ hF).1 ?_
  rintro x ⟨g, -, hFg, rfl⟩
  exact integral_nonneg fun i => (h0 i).trans (hFg i)

theorem upper_add {F G : ι → ℝ} (hF : Bnd F) (hG : Bnd G) :
    upper μ (fun i => F i + G i) ≤ upper μ F + upper μ G := by
  have hFG : Bnd (fun i => F i + G i) := by
    obtain ⟨a, ha⟩ := hF; obtain ⟨b, hb⟩ := hG
    exact ⟨a + b, fun i => (abs_add_le _ _).trans (add_le_add (ha i) (hb i))⟩
  have key : ∀ x ∈ majSet μ F, ∀ y ∈ majSet μ G, upper μ (fun i => F i + G i) ≤ x + y := by
    rintro _ ⟨g1, hg1, h1, rfl⟩ _ ⟨g2, hg2, h2, rfl⟩
    rw [← integral_add hg1 hg2]
    exact upper_le_integral μ hFG (hg1.add hg2) (fun i => add_le_add (h1 i) (h2 i))
  have h1 : ∀ y ∈ majSet μ G, upper μ (fun i => F i + G i) - y ≤ upper μ F :=
    fun y hy => le_csInf (majSet_ne_bdd μ hF).1 (fun x hx => by linarith [key x hx y hy])
  have h2 : upper μ (fun i => F i + G i) - upper μ F ≤ upper μ G :=
    le_csInf (majSet_ne_bdd μ hG).1 (fun y hy => by linarith [h1 y hy])
  linarith

theorem upper_smul {F : ι → ℝ} {c : ℝ} (hc : 0 < c) :
    upper μ (fun i => c * F i) = c * upper μ F := by
  have hset : majSet μ (fun i => c * F i) = c • majSet μ F := by
    ext x
    constructor
    · rintro ⟨g, hg, h, rfl⟩
      refine ⟨∫ i, c⁻¹ * g i ∂μ, ⟨fun i => c⁻¹ * g i, hg.const_mul _, fun i => ?_, rfl⟩, ?_⟩
      · show F i ≤ c⁻¹ * g i
        rw [inv_mul_eq_div, le_div_iff₀ hc]; linarith [h i]
      · rw [integral_const_mul]
        show c * (c⁻¹ * ∫ a, g a ∂μ) = _
        rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    · intro hx
      rw [Set.mem_smul_set] at hx
      obtain ⟨y, ⟨g, hg, h, rfl⟩, rfl⟩ := hx
      exact ⟨fun i => c * g i, hg.const_mul _,
        fun i => mul_le_mul_of_nonneg_left (h i) hc.le, by rw [integral_const_mul, smul_eq_mul]⟩
  unfold upper
  rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]

end Upper

section Fix

variable {k : ℕ} {M : Type} [MetricSpace M]

open Classical in
/-- Repair a configuration so that it serves the last request of `l`. -/
noncomputable def fixG (C₀ : Config k M) (l : List M) (p : Config k M) : Config k M :=
  match l.getLast? with
  | none => C₀
  | some r => if ∃ s, p s = r then p else fun _ => r

noncomputable def fixAlg (C₀ : Config k M) (hk : M → 0 < k) (ω : List M → Config k M) :
    OnlineAlgorithm k M where
  conf l := fixG C₀ l (ω l)
  serves l r := by
    have hl : (l ++ [r]).getLast? = some r := by simp
    unfold fixG
    rw [hl]
    dsimp only
    split_ifs with h
    · exact h
    · exact ⟨⟨0, hk r⟩, rfl⟩

theorem fixAlg_nil (C₀ : Config k M) (hk : M → 0 < k) (ω : List M → Config k M) :
    (fixAlg C₀ hk ω).conf [] = C₀ := by
  simp [fixAlg, fixG]

theorem fixAlg_conf (C₀ : Config k M) (hk : M → 0 < k) (A : OnlineAlgorithm k M)
    (h0 : A.conf [] = C₀) : (fixAlg C₀ hk A.conf).conf = A.conf := by
  funext l
  rcases List.eq_nil_or_concat l with rfl | ⟨L, r, rfl⟩
  · rw [fixAlg_nil, h0]
  · rw [List.concat_eq_append]
    have hl : (L ++ [r]).getLast? = some r := by simp
    show fixG C₀ (L ++ [r]) (A.conf (L ++ [r])) = _
    unfold fixG
    rw [hl]
    dsimp only
    rw [if_pos (A.serves L r)]

theorem fixAlg_cost (C₀ : Config k M) (hk : M → 0 < k) (A : OnlineAlgorithm k M)
    (h0 : A.conf [] = C₀) (σ : List M) : (fixAlg C₀ hk A.conf).cost σ = A.cost σ := by
  unfold OnlineAlgorithm.cost
  rw [fixAlg_conf C₀ hk A h0]

theorem cost_nonneg (A : OnlineAlgorithm k M) (σ : List M) : 0 ≤ A.cost σ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg

variable [Fintype M]

theorem cont_cost (C₀ : Config k M) (hk : M → 0 < k) (σ : List M) :
    Continuous fun ω : List M → Config k M => (fixAlg C₀ hk ω).cost σ := by
  unfold OnlineAlgorithm.cost
  refine continuous_finsetSum _ fun j _ => ?_
  have hc : ∀ l : List M, Continuous fun ω : List M → Config k M => fixG C₀ l (ω l) :=
    fun l => (continuous_of_discreteTopology (f := fixG C₀ l)).comp (continuous_apply l)
  exact (continuous_of_discreteTopology
    (f := fun q : Config k M × Config k M => moveCost q.1 q.2)).comp ((hc _).prodMk (hc _))

end Fix

/-- The borel structure on the space of deterministic strategies. -/
noncomputable def omMeas (k : ℕ) (M : Type) [MetricSpace M] :
    MeasurableSpace (List M → Config k M) := borel _

attribute [local instance] omMeas

theorem omBorel (k : ℕ) (M : Type) [MetricSpace M] : BorelSpace (List M → Config k M) := ⟨rfl⟩

attribute [local instance] omBorel

theorem regularize {k : ℕ} {M : Type} [MetricSpace M] [Fintype M]
    (C₀ : Config k M) {ι : Type} [MeasurableSpace ι] (μ : Measure ι) [IsProbabilityMeasure μ]
    (alg : ι → OnlineAlgorithm k M) (h0 : ∀ i, (alg i).conf [] = C₀)
    (h : List M → ι → ℝ) (hint : ∀ σ, Integrable (h σ) μ)
    (hle : ∀ σ i, (alg i).cost σ ≤ h σ i) :
    ∃ A : RandomizedAlgorithm k M, (∀ ω, (A.alg ω).conf [] = C₀) ∧
      ∀ σ, A.expCost σ ≤ ENNReal.ofReal (∫ i, h σ i ∂μ) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exfalso
    have h1 := measure_univ (μ := μ)
    rw [Measure.eq_zero_of_isEmpty μ] at h1
    simp at h1
  have hk : M → 0 < k := fun r => ((alg i₀).serves [] r).choose.pos
  let π : ι → (List M → Config k M) := fun i => (alg i).conf
  have bnd : ∀ f : C_c(List M → Config k M, ℝ), Bnd (fun i => f (π i)) := by
    intro f
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn f.continuous.continuousOn
    exact ⟨C, fun i => by simpa [Real.norm_eq_abs] using hC (π i) (Set.mem_univ _)⟩
  let N : C_c(List M → Config k M, ℝ) → ℝ := fun f => upper μ (fun i => f (π i))
  have hNhom : ∀ c : ℝ, 0 < c → ∀ f, N (c • f) = c * N f := by
    intro c hc f
    show upper μ (fun i => (c • f) (π i)) = c * upper μ (fun i => f (π i))
    simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact upper_smul μ hc
  have hNadd : ∀ f g, N (f + g) ≤ N f + N g := by
    intro f g
    show upper μ (fun i => (f + g) (π i)) ≤ upper μ (fun i => f (π i)) + upper μ (fun i => g (π i))
    simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
    exact upper_add μ (bnd f) (bnd g)
  obtain ⟨g, -, hgN⟩ := exists_extension_of_le_sublinear
    (⟨⊥, 0⟩ : C_c(List M → Config k M, ℝ) →ₗ.[ℝ] ℝ) N hNhom hNadd (by
      rintro ⟨x, hx⟩
      rw [Submodule.mem_bot] at hx
      subst hx
      show (0 : ℝ) ≤ upper μ (fun i => (0 : C_c(List M → Config k M, ℝ)) (π i))
      exact upper_nonneg μ (bnd 0) (fun i => by simp))
  have hpos : ∀ f : C_c(List M → Config k M, ℝ), 0 ≤ f → 0 ≤ g f := by
    intro f hf
    have h1 := hgN (-f)
    have h2 : N (-f) ≤ ∫ _i, (0 : ℝ) ∂μ :=
      upper_le_integral μ (bnd (-f)) (integrable_const 0) (fun i => by
        simp only [CompactlySupportedContinuousMap.coe_neg, Pi.neg_apply, neg_nonpos]
        exact hf (π i))
    rw [map_neg] at h1
    simp at h2
    linarith
  let Λ : C_c(List M → Config k M, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ g hpos
  let ν : Measure (List M → Config k M) := RealRMK.rieszMeasure Λ
  let one : C_c(List M → Config k M, ℝ) := continuousMapEquiv (ContinuousMap.const _ 1)
  have hone : ∀ ω, one ω = 1 := fun _ => rfl
  have hg1 : g one = 1 := by
    have a1 : N one ≤ ∫ _i, (1 : ℝ) ∂μ :=
      upper_le_integral μ (bnd one) (integrable_const 1) (fun i => by rw [hone])
    have a2 : N (-one) ≤ ∫ _i, (-1 : ℝ) ∂μ :=
      upper_le_integral μ (bnd (-one)) (integrable_const (-1)) (fun i => by
        simp only [CompactlySupportedContinuousMap.coe_neg, Pi.neg_apply, hone, le_refl])
    have b1 := hgN one
    have b2 := hgN (-one)
    rw [map_neg] at b2
    simp at a1 a2
    linarith
  have hprob : IsProbabilityMeasure ν := by
    have h1 : ∫ ω, one ω ∂ν = Λ one := RealRMK.integral_rieszMeasure Λ one
    have h2 : Λ one = g one := rfl
    simp only [hone, integral_const, smul_eq_mul, mul_one, h2, hg1] at h1
    constructor
    rw [measureReal_def] at h1
    exact (ENNReal.toReal_eq_one_iff _).1 h1
  let A : RandomizedAlgorithm k M :=
    @RandomizedAlgorithm.mk k M _ (List M → Config k M) _ ν hprob (fixAlg C₀ hk)
      (fun σ => (cont_cost C₀ hk σ).measurable)
  refine ⟨A, fun ω => fixAlg_nil C₀ hk ω, fun σ => ?_⟩
  let F : C_c(List M → Config k M, ℝ) :=
    continuousMapEquiv ⟨fun ω => (fixAlg C₀ hk ω).cost σ, cont_cost C₀ hk σ⟩
  have hF : ∀ ω, F ω = (fixAlg C₀ hk ω).cost σ := fun _ => rfl
  show ∫⁻ ω, ENNReal.ofReal ((fixAlg C₀ hk ω).cost σ) ∂ν ≤ _
  have hFi : Integrable (fun ω => (fixAlg C₀ hk ω).cost σ) ν :=
    (cont_cost C₀ hk σ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hFi
    (Filter.Eventually.of_forall fun ω => cost_nonneg _ σ)]
  apply ENNReal.ofReal_le_ofReal
  calc ∫ ω, (fixAlg C₀ hk ω).cost σ ∂ν = ∫ ω, F ω ∂ν := rfl
    _ = Λ F := RealRMK.integral_rieszMeasure Λ F
    _ = g F := rfl
    _ ≤ N F := hgN F
    _ ≤ ∫ i, h σ i ∂μ := upper_le_integral μ (bnd F) (hint σ) (fun i => by
        rw [hF]
        show (fixAlg C₀ hk (alg i).conf).cost σ ≤ h σ i
        rw [fixAlg_cost C₀ hk (alg i) (h0 i)]
        exact hle σ i)

end B5077a04R

namespace B5077a04K6

open MeasureTheory KServer B5077a04R

variable {k : ℕ} {M : Type} [MetricSpace M]

theorem moveCost_self (C : Config k M) : moveCost C C = 0 := by
  simp [moveCost]

theorem moveCost_nonneg (C C' : Config k M) : 0 ≤ moveCost C C' :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

theorem moveCost_triangle (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun s _ => dist_triangle _ _ _

theorem sum_shift_le (n : ℕ) (t t' : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (h0 : 0 < n → t' 0 ≤ t 0 + D) (hj : ∀ j, 0 < j → j < n → t' j ≤ t j) :
    ∑ j ∈ Finset.range n, t' j ≤ ∑ j ∈ Finset.range n, t j + D := by
  cases n with
  | zero => simpa using hD
  | succ m =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h1 : ∑ j ∈ Finset.range m, t' (j + 1) ≤ ∑ j ∈ Finset.range m, t (j + 1) :=
      Finset.sum_le_sum fun j hj' => hj (j + 1) (Nat.succ_pos j) (by
        rw [Finset.mem_range] at hj'; omega)
    linarith [h0 (Nat.succ_pos m)]

theorem take_ne_nil {σ : List M} {j : ℕ} (hj : 0 < j) (hn : j ≤ σ.length) (hσ : 0 < σ.length) :
    σ.take j ≠ [] := by
  rw [Ne, List.take_eq_nil_iff]
  rintro (h | h)
  · omega
  · subst h; simp at hσ

open Classical in
/-- Start at `C₀` and then follow `A`. -/
noncomputable def startAt (C₀ : Config k M) (A : OnlineAlgorithm k M) : OnlineAlgorithm k M where
  conf l := if l = [] then C₀ else A.conf l
  serves l r := by
    have : l ++ [r] ≠ [] := by simp
    simp only [if_neg this]
    exact A.serves l r

theorem startAt_nil (C₀ : Config k M) (A : OnlineAlgorithm k M) : (startAt C₀ A).conf [] = C₀ := by
  simp [startAt]

theorem startAt_ne (C₀ : Config k M) (A : OnlineAlgorithm k M) {l : List M} (hl : l ≠ []) :
    (startAt C₀ A).conf l = A.conf l := by
  simp [startAt, hl]

theorem startAt_cost_le (C₀ : Config k M) (A : OnlineAlgorithm k M) (σ : List M) :
    (startAt C₀ A).cost σ ≤ A.cost σ + moveCost C₀ (A.conf []) := by
  unfold OnlineAlgorithm.cost
  apply sum_shift_le _ _ _ _ (moveCost_nonneg _ _)
  · intro hn
    have h1 : σ.take (0 + 1) ≠ [] := take_ne_nil (by omega) (by omega) hn
    show moveCost ((startAt C₀ A).conf (σ.take 0)) ((startAt C₀ A).conf (σ.take (0 + 1))) ≤
      moveCost (A.conf (σ.take 0)) (A.conf (σ.take (0 + 1))) + moveCost C₀ (A.conf [])
    rw [List.take_zero, startAt_nil, startAt_ne C₀ A h1]
    linarith [moveCost_triangle C₀ (A.conf []) (A.conf (σ.take (0 + 1)))]
  · intro j hj hjn
    have h1 : σ.take j ≠ [] := take_ne_nil hj (by omega) (by omega)
    have h2 : σ.take (j + 1) ≠ [] := take_ne_nil (by omega) (by omega) (by omega)
    simp only [startAt, if_neg h1, if_neg h2, le_refl]

/-- The algorithm that sits at `C` forever (valid when `C` is surjective). -/
def constAlg (C : Config k M) (hC : Function.Surjective C) : OnlineAlgorithm k M where
  conf _ := C
  serves _ r := hC r

theorem constAlg_cost (C : Config k M) (hC : Function.Surjective C) (σ : List M) :
    (constAlg C hC).cost σ = 0 := by
  simp [OnlineAlgorithm.cost, constAlg, moveCost_self]

theorem sched_shift (C₀ C₀' : Config k M) (σ : List M) (S : ℕ → Config k M)
    (hS : ServesFrom C₀ σ S) :
    ServesFrom C₀' σ (fun n => if n = 0 then C₀' else S n) ∧
      ∑ j ∈ Finset.range σ.length, moveCost ((fun n => if n = 0 then C₀' else S n) j)
          ((fun n => if n = 0 then C₀' else S n) (j + 1)) ≤
        ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) + moveCost C₀' C₀ := by
  refine ⟨⟨by simp, fun j => ?_⟩, ?_⟩
  · simpa using hS.2 j
  · apply sum_shift_le _ _ _ _ (moveCost_nonneg _ _)
    · intro _
      show moveCost (if (0 : ℕ) = 0 then C₀' else S 0) (if 0 + 1 = 0 then C₀' else S (0 + 1)) ≤
        moveCost (S 0) (S (0 + 1)) + moveCost C₀' C₀
      rw [if_pos rfl, if_neg (by omega), hS.1]
      linarith [moveCost_triangle C₀' C₀ (S (0 + 1))]
    · intro j hj _
      have h1 : j ≠ 0 := by omega
      simp only [h1, if_false, Nat.succ_ne_zero, le_refl]

theorem offlineCost_shift (C₀ C₀' : Config k M) (σ : List M) :
    offlineCost C₀' σ ≤ offlineCost C₀ σ + moveCost C₀' C₀ := by
  have hD := moveCost_nonneg C₀' C₀
  unfold offlineCost
  have hBbdd : BddBelow {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀' σ S ∧
      c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))} := by
    refine ⟨0, ?_⟩
    rintro c ⟨S, -, rfl⟩
    exact Finset.sum_nonneg fun j _ => moveCost_nonneg _ _
  rcases Set.eq_empty_or_nonempty {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
      c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))} with hA | hA
  · have hB : {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀' σ S ∧
        c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem] at hA ⊢
      rintro c ⟨S, hS, -⟩
      exact hA _ ⟨_, (sched_shift C₀' C₀ σ S hS).1, rfl⟩
    rw [hA, hB, Real.sInf_empty]
    linarith
  · have key : ∀ x ∈ {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
        c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))},
        sInf {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀' σ S ∧
          c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))} - moveCost C₀' C₀ ≤ x := by
      rintro x ⟨S, hS, rfl⟩
      obtain ⟨h1, h2⟩ := sched_shift C₀ C₀' σ S hS
      have := csInf_le hBbdd ⟨_, h1, rfl⟩
      linarith
    linarith [le_csInf hA key]

theorem offlineCost_nonneg' (C₀ : Config k M) (σ : List M) : 0 ≤ offlineCost C₀ σ :=
  Real.sInf_nonneg (by rintro c ⟨S, -, rfl⟩; exact Finset.sum_nonneg fun j _ => moveCost_nonneg _ _)

theorem cost_le_bound [Fintype M] (A : OnlineAlgorithm k M) (σ : List M) :
    A.cost σ ≤ σ.length * (k * ∑ p : M × M, dist p.1 p.2) := by
  unfold OnlineAlgorithm.cost
  have hd : ∀ x y : M, dist x y ≤ ∑ p : M × M, dist p.1 p.2 := fun x y =>
    Finset.single_le_sum (f := fun p : M × M => dist p.1 p.2) (fun p _ => dist_nonneg)
      (Finset.mem_univ (x, y))
  have hm : ∀ C C' : Config k M, moveCost C C' ≤ k * ∑ p : M × M, dist p.1 p.2 := by
    intro C C'
    unfold moveCost
    calc ∑ i, dist (C i) (C' i) ≤ ∑ _i : Fin k, ∑ p : M × M, dist p.1 p.2 :=
          Finset.sum_le_sum fun i _ => hd _ _
      _ = _ := by simp
  calc _ ≤ ∑ _j ∈ Finset.range σ.length, (k * ∑ p : M × M, dist p.1 p.2) :=
        Finset.sum_le_sum fun j _ => hm _ _
    _ = _ := by simp

end B5077a04K6

open B5077a04R B5077a04K6 MeasureTheory KServer in
theorem k6_proof : ∀ (k : ℕ) (M : Type) [MetricSpace M] [Fintype M] [Nonempty M] (c : ℝ), 0 ≤ c →
    (∀ C₀ : KServer.Config k M, Function.Injective C₀ →
      ∃ A : KServer.RandomizedAlgorithm k M, A.IsCompetitiveFrom C₀ c) →
    ∀ C₀ : KServer.Config k M, ∃ A : KServer.RandomizedAlgorithm k M, A.IsCompetitiveFrom C₀ c := by
  intro k M _ _ _ c hc hinj C₀
  obtain ⟨x₀⟩ := ‹Nonempty M›
  by_cases hkM : k ≤ Fintype.card M
  · obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (by simpa using hkM : Fintype.card (Fin k) ≤ Fintype.card M)
    obtain ⟨⟨ι, μ, prob, alg, meas⟩, h0', a, ha⟩ := hinj e e.injective
    have := prob
    have hint : ∀ σ, Integrable (fun i => (alg i).cost σ) μ := fun σ =>
      Integrable.of_bound (meas σ).aestronglyMeasurable
        (σ.length * (k * ∑ p : M × M, dist p.1 p.2))
        (Filter.Eventually.of_forall fun i => by
          rw [Real.norm_eq_abs, abs_of_nonneg (cost_nonneg _ σ)]; exact cost_le_bound _ σ)
    obtain ⟨B, hB0, hB⟩ := regularize C₀ μ (fun i => startAt C₀ (alg i)) (fun i => startAt_nil _ _)
      (fun σ i => (alg i).cost σ + moveCost C₀ e) (fun σ => (hint σ).add (integrable_const _))
      (fun σ i => by
        have := startAt_cost_le C₀ (alg i) σ
        rw [h0' i] at this
        exact this)
    refine ⟨B, hB0, c * moveCost e C₀ + |a| + moveCost C₀ e,
      fun σ => (hB σ).trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hc1 : ∫ _i, moveCost C₀ e ∂μ = moveCost C₀ e := by simp
    rw [integral_add (hint σ) (integrable_const _), hc1]
    have h1 := ha σ
    change ∫⁻ i, ENNReal.ofReal ((alg i).cost σ) ∂μ ≤ _ at h1
    rw [← ofReal_integral_eq_lintegral_ofReal (hint σ)
      (Filter.Eventually.of_forall fun i => cost_nonneg _ σ), ENNReal.ofReal_le_ofReal_iff'] at h1
    have hopt := mul_le_mul_of_nonneg_left (offlineCost_shift C₀ (⇑e) σ) hc
    have hO := mul_nonneg hc (offlineCost_nonneg' C₀ σ)
    have hO' := mul_nonneg hc (offlineCost_nonneg' (⇑e) σ)
    rcases h1 with h1 | h1 <;> nlinarith [le_abs_self a, abs_nonneg a]
  · push Not at hkM
    let eM := Fintype.equivFin M
    let Cs : KServer.Config k M := fun j =>
      if h : (j : ℕ) < Fintype.card M then eM.symm ⟨j, h⟩ else x₀
    have hCs : Function.Surjective Cs := by
      intro m
      refine ⟨⟨eM m, lt_trans (eM m).isLt hkM⟩, ?_⟩
      simp only [Cs, dif_pos (eM m).isLt, Fin.eta, Equiv.symm_apply_apply]
    obtain ⟨B, hB0, hB⟩ := regularize C₀ (Measure.dirac ())
      (fun _ : Unit => startAt C₀ (constAlg Cs hCs)) (fun _ => startAt_nil _ _)
      (fun _ _ => KServer.moveCost C₀ Cs) (fun σ => integrable_const _) (fun σ _ => by
        have := startAt_cost_le C₀ (constAlg Cs hCs) σ
        rw [constAlg_cost, zero_add] at this
        exact this)
    refine ⟨B, hB0, KServer.moveCost C₀ Cs, fun σ => (hB σ).trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hO := mul_nonneg hc (offlineCost_nonneg' C₀ σ)
    have hc1 : ∫ _ : Unit, KServer.moveCost C₀ Cs ∂(Measure.dirac ()) = KServer.moveCost C₀ Cs := by
      simp
    rw [hc1]
    linarith

namespace B5077a04K4

open MeasureTheory KServer B5077a04R B5077a04K6

theorem measurable_sigmaMk' {α : Type} {β : α → Type} [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (Sigma.mk (β := β) a) :=
  fun _ hs => MeasurableSpace.measurableSet_iInf.1 hs a

theorem measurable_of_sigma' {α : Type} {β : α → Type} [∀ a, MeasurableSpace (β a)] {γ : Type}
    [MeasurableSpace γ] {g : Sigma β → γ} (hg : ∀ a, Measurable fun x => g ⟨a, x⟩) :
    Measurable g :=
  fun _ ht => MeasurableSpace.measurableSet_iInf.2 fun a => hg a ht

variable {k : ℕ} {M : Type} [MetricSpace M]

/-- Run an algorithm for `X` on `M` through a bijection. -/
def transAlg {X : Type} [MetricSpace X] (e : M ≃ X) (A : OnlineAlgorithm k X) :
    OnlineAlgorithm k M where
  conf l := fun s => e.symm (A.conf (l.map e) s)
  serves l r := by
    obtain ⟨s, hs⟩ := A.serves (l.map e) (e r)
    refine ⟨s, ?_⟩
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [hs, Equiv.symm_apply_apply]

theorem transAlg_cost_le {X : Type} [MetricSpace X] (e : M ≃ X)
    (hdom : ∀ x y : M, dist x y ≤ dist (e x) (e y)) (A : OnlineAlgorithm k X) (σ : List M) :
    (transAlg e A).cost σ ≤ A.cost (σ.map e) := by
  unfold OnlineAlgorithm.cost
  rw [List.length_map]
  refine Finset.sum_le_sum fun j _ => ?_
  unfold moveCost
  refine Finset.sum_le_sum fun s _ => ?_
  simp only [transAlg, List.map_take]
  have := hdom (e.symm (A.conf (List.take j (σ.map e)) s))
    (e.symm (A.conf (List.take (j + 1) (σ.map e)) s))
  simpa using this

theorem opt_mix (C₀ : Config k M) (r : ℕ) (p : Fin r → ℝ) (X : Fin r → Type)
    [∀ i, MetricSpace (X i)] (f : (i : Fin r) → M ≃ X i) (D : ℝ) (hp : ∀ i, 0 ≤ p i)
    (hstretch : ∀ x y : M, ∑ i, p i * dist (f i x) (f i y) ≤ D * dist x y) (σ : List M)
    (hne : {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
      c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))}.Nonempty) :
    ∑ i, p i * offlineCost (fun j => f i (C₀ j)) (σ.map (f i)) ≤ D * offlineCost C₀ σ := by
  have key : ∀ S, ServesFrom C₀ σ S →
      ∑ i, p i * offlineCost (fun j => f i (C₀ j)) (σ.map (f i)) ≤
        D * ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) := by
    intro S hS
    have h1 : ∀ i, offlineCost (fun j => f i (C₀ j)) (σ.map (f i)) ≤
        ∑ j ∈ Finset.range σ.length, ∑ s, dist (f i (S j s)) (f i (S (j + 1) s)) := by
      intro i
      refine csInf_le ⟨0, ?_⟩ ⟨fun n s => f i (S n s), ⟨?_, ?_⟩, ?_⟩
      · rintro c ⟨T, -, rfl⟩
        exact Finset.sum_nonneg fun j _ => moveCost_nonneg _ _
      · funext s; simp [hS.1]
      · intro j
        obtain ⟨s, hs⟩ := hS.2 ⟨j, by simpa using j.2⟩
        refine ⟨s, ?_⟩
        simp only [List.get_eq_getElem, List.getElem_map] at hs ⊢
        rw [hs]
      · simp [moveCost]
    calc ∑ i, p i * offlineCost (fun j => f i (C₀ j)) (σ.map (f i))
        ≤ ∑ i, p i * ∑ j ∈ Finset.range σ.length, ∑ s, dist (f i (S j s)) (f i (S (j + 1) s)) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h1 i) (hp i)
      _ = ∑ j ∈ Finset.range σ.length, ∑ s, ∑ i, p i * dist (f i (S j s)) (f i (S (j + 1) s)) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ ≤ ∑ j ∈ Finset.range σ.length, ∑ s, D * dist (S j s) (S (j + 1) s) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun s _ => hstretch _ _
      _ = D * ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) := by
          simp only [moveCost, Finset.mul_sum]
  obtain ⟨x0, S0, hS0, rfl⟩ := hne
  have hbdd : BddBelow {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
      c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))} := by
    refine ⟨0, ?_⟩
    rintro c ⟨T, -, rfl⟩
    exact Finset.sum_nonneg fun j _ => moveCost_nonneg _ _
  rcases le_or_gt D 0 with hD | hD
  · have hinf : offlineCost C₀ σ ≤ ∑ j ∈ Finset.range σ.length, moveCost (S0 j) (S0 (j + 1)) :=
      csInf_le hbdd ⟨S0, hS0, rfl⟩
    exact (key S0 hS0).trans (mul_le_mul_of_nonpos_left hinf hD)
  · have h2 : (∑ i, p i * offlineCost (fun j => f i (C₀ j)) (σ.map (f i))) / D ≤
        offlineCost C₀ σ := by
      refine le_csInf ⟨_, S0, hS0, rfl⟩ ?_
      rintro x ⟨S, hS, rfl⟩
      rw [div_le_iff₀ hD, mul_comm]
      exact key S hS
    rw [div_le_iff₀ hD, mul_comm] at h2
    exact h2

theorem sched_nonempty (C₀ : Config k M) (σ : List M) (h : 0 < k ∨ σ = []) :
    {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
      c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))}.Nonempty := by
  rcases h with hk | rfl
  · refine ⟨_, fun n => if n = 0 then C₀ else fun _ => σ.getD (n - 1) (C₀ ⟨0, hk⟩),
      ⟨by simp, fun j => ⟨⟨0, hk⟩, ?_⟩⟩, rfl⟩
    simp [List.getD_eq_getElem?_getD]
  · exact ⟨_, fun _ => C₀, ⟨rfl, fun j => j.elim0⟩, rfl⟩

end B5077a04K4

attribute [local instance] KServer.RandomizedAlgorithm.ms

open B5077a04R B5077a04K6 B5077a04K4 MeasureTheory KServer in
theorem k4_proof : ∀ (k : ℕ) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : KServer.Config k M) (r : ℕ) (p : Fin r → ℝ) (X : Fin r → Type)
    [∀ i, MetricSpace (X i)] [∀ i, Fintype (X i)] (f : (i : Fin r) → M ≃ X i) (D c : ℝ),
    0 ≤ c → (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
    (∀ i (x y : M), dist x y ≤ dist (f i x) (f i y)) →
    (∀ x y : M, ∑ i, p i * dist (f i x) (f i y) ≤ D * dist x y) →
    (∀ i, ∃ A : KServer.RandomizedAlgorithm k (X i),
      A.IsCompetitiveFrom (fun j => f i (C₀ j)) c) →
    ∃ A : KServer.RandomizedAlgorithm k M, A.IsCompetitiveFrom C₀ (c * D) := by
  intro k M _ _ C₀ r p X _ _ f D c hc hp hp1 hdom hstretch hA
  choose A hAc using hA
  have hA0 : ∀ i ω, ((A i).alg ω).conf [] = fun j => f i (C₀ j) := fun i => (hAc i).1
  choose a ha using fun i => (hAc i).2
  let μmix : Measure (Σ i : Fin r, (A i).ι) :=
    ∑ i, ENNReal.ofReal (p i) • (A i).μ.map (Sigma.mk i)
  have hprob : IsProbabilityMeasure μmix := by
    constructor
    simp only [μmix, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.map_apply (measurable_sigmaMk' _) MeasurableSet.univ, Set.preimage_univ,
      (A _).prob.measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hp1, ENNReal.ofReal_one]
  let h : List M → (Σ i : Fin r, (A i).ι) → ℝ :=
    fun (σ : List M) (z : Σ i : Fin r, (A i).ι) => ((A z.1).alg z.2).cost (σ.map (f z.1))
  have hmeas : ∀ σ : List M, Measurable (h σ) := fun σ =>
    measurable_of_sigma' fun i => (A i).meas (σ.map (f i))
  have hintI : ∀ (i : Fin r) (σ : List M), Integrable (fun ω => ((A i).alg ω).cost (σ.map (f i))) (A i).μ := by
    intro i σ
    have := (A i).prob
    exact Integrable.of_bound ((A i).meas _).aestronglyMeasurable
      ((σ.map (f i)).length * (k * ∑ q : X i × X i, dist q.1 q.2))
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cost_nonneg _ _)]; exact cost_le_bound _ _)
  have hintP : ∀ σ : List M, ∀ i ∈ (Finset.univ : Finset (Fin r)),
      Integrable (h σ) (ENNReal.ofReal (p i) • (A i).μ.map (Sigma.mk i)) := fun σ i _ =>
    ((integrable_map_measure (hmeas σ).aestronglyMeasurable
      (measurable_sigmaMk' i).aemeasurable).2 (hintI i σ)).smul_measure ENNReal.ofReal_ne_top
  have hI : ∀ σ : List M, ∫ z, h σ z ∂μmix =
      ∑ i, p i * ∫ ω, ((A i).alg ω).cost (σ.map (f i)) ∂(A i).μ := by
    intro σ
    rw [integral_finsetSum_measure (hintP σ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, integral_map (measurable_sigmaMk' i).aemeasurable
      (hmeas σ).aestronglyMeasurable, ENNReal.toReal_ofReal (hp i), smul_eq_mul]
  obtain ⟨B, hB0, hB⟩ := regularize C₀ μmix (fun z => transAlg (f z.1) ((A z.1).alg z.2))
    (fun z => by
      funext s
      show (f z.1).symm (((A z.1).alg z.2).conf ([].map (f z.1)) s) = C₀ s
      rw [List.map_nil, hA0]
      simp)
    h (fun σ => integrable_finsetSum_measure.2 (hintP σ))
    (fun σ z => transAlg_cost_le (f z.1) (hdom z.1) _ σ)
  refine ⟨B, hB0, ∑ i, p i * |a i|, fun σ => (hB σ).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [hI]
  have hi : ∀ i, ∫ ω, ((A i).alg ω).cost (σ.map (f i)) ∂(A i).μ ≤
      c * offlineCost (fun j => f i (C₀ j)) (σ.map (f i)) + |a i| := by
    intro i
    have h1 := ha i (σ.map (f i))
    change ∫⁻ ω, ENNReal.ofReal (((A i).alg ω).cost (σ.map (f i))) ∂(A i).μ ≤ _ at h1
    rw [← ofReal_integral_eq_lintegral_ofReal (hintI i σ)
      (Filter.Eventually.of_forall fun ω => cost_nonneg _ _), ENNReal.ofReal_le_ofReal_iff'] at h1
    have hO := mul_nonneg hc (offlineCost_nonneg' (fun j => f i (C₀ j)) (σ.map (f i)))
    rcases h1 with h1 | h1 <;> linarith [le_abs_self (a i), abs_nonneg (a i)]
  have hne : 0 < k ∨ σ = [] := by
    by_cases hσ : σ = []
    · exact Or.inr hσ
    · left
      obtain ⟨x, -⟩ := List.exists_mem_of_ne_nil σ hσ
      have hr : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h0 | h0
        · subst h0; simp at hp1
        · exact h0
      have := (A ⟨0, hr⟩).prob
      rcases isEmpty_or_nonempty (A ⟨0, hr⟩).ι with hι | ⟨⟨ω⟩⟩
      · exfalso
        have h1 := measure_univ (μ := (A ⟨0, hr⟩).μ)
        rw [Measure.eq_zero_of_isEmpty (A ⟨0, hr⟩).μ] at h1
        simp at h1
      · exact (((A ⟨0, hr⟩).alg ω).serves [] (f ⟨0, hr⟩ x)).choose.pos
  have hmix := opt_mix C₀ r p X f D hp hstretch σ (sched_nonempty C₀ σ hne)
  calc ∑ i, p i * ∫ ω, ((A i).alg ω).cost (σ.map (f i)) ∂(A i).μ
      ≤ ∑ i, p i * (c * offlineCost (fun j => f i (C₀ j)) (σ.map (f i)) + |a i|) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i) (hp i)
    _ = c * ∑ i, p i * offlineCost (fun j => f i (C₀ j)) (σ.map (f i)) + ∑ i, p i * |a i| := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ c * (D * offlineCost C₀ σ) + ∑ i, p i * |a i| := by
        gcongr
    _ = c * D * offlineCost C₀ σ + ∑ i, p i * |a i| := by ring

/-- Reduction for PolylogKServer.Main.polylog_competitive (BBMN Theorem 1): Theorems 5-8 and the
two new children (FRT-type HST embedding distribution; fractional competitiveness transfer) are
imported; the lemmas K3, K4, K5, K6 are proved above. -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (M : Type) [MetricSpace M] [Fintype M]
      (C₀ : KServer.Config k M), 2 ≤ k → 3 ≤ Fintype.card M →
      ∃ A : KServer.RandomizedAlgorithm k M,
        A.IsCompetitiveFrom C₀
          (C * Real.log k ^ 2 * Real.log (Fintype.card M) ^ 3 *
            Real.log (Real.log (Fintype.card M))) := by
  exact B5077a04.parent_of_children PolylogKServer.Allocation.frac_alloc_competitive
    PolylogKServer.Fractional.kserver_from_allocation
    PolylogKServer.Rounding.fractional_to_randomized
    PolylogKServer.HST.exists_shallow_weighted_hst
    PolylogKServer.HST.exists_hst_embedding_distribution
    B5077a04K3.k3_proof k4_proof k5_proof k6_proof
    PolylogKServer.Fractional.frac_competitive_transfer
