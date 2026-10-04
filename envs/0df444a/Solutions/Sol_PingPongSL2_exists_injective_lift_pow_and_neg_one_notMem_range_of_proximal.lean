-- Prove2me | solution 1 for PingPongSL2.exists_injective_lift_pow_and_neg_one_notMem_range_of_proximal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T06:28:24.720455+00:00
-- url     : https://prove2.me/submissions/041b1724-7186-46ea-b81d-af72f0588633

import Mathlib


section
section
/-!
# Part 3P: ping-pong over a normed field

`x ∈ SL(2, L)` with eigenvalues `μ, μ⁻¹`, `‖μ‖ > 1`, and `y = c x c⁻¹` sharing no eigenvector with
`x` (`tr [x, y] ≠ 2`). We conjugate `x` to `D = diag(μ, μ⁻¹)`; then `y` becomes `g⁻¹ D g` with all
four entries of `g` nonzero. On nonzero vectors of `L²` the sets `Bp ε = {‖u₁‖ ≤ ε ‖u₀‖}` and
`Bm ε = {‖u₀‖ ≤ ε ‖u₁‖}` (and their pull-backs by `g`) are ping-pong sets for `Dᴺ`, `g⁻¹ Dᴺ g`,
and Mathlib's `FreeGroup.injective_lift_of_ping_pong` gives freeness. `-1 ∉ range` follows from
injectivity, since free groups are torsion-free and `(-1)² = 1 ≠ -1`.
-/

open MeasureTheory Matrix Filter Topology

namespace PingPongSL2

open scoped Pointwise

section Vectors

variable {L : Type} [NormedField L]

lemma smul_apply0 (M : SpecialLinearGroup (Fin 2) L) (w : Fin 2 → L) :
    (M • w) 0 = M 0 0 * w 0 + M 0 1 * w 1 := by
  change ((M : Matrix (Fin 2) (Fin 2) L) *ᵥ w) 0 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma smul_apply1 (M : SpecialLinearGroup (Fin 2) L) (w : Fin 2 → L) :
    (M • w) 1 = M 1 0 * w 0 + M 1 1 * w 1 := by
  change ((M : Matrix (Fin 2) (Fin 2) L) *ᵥ w) 1 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The nonzero vectors of `L²`, as a sub-`SL(2, L)`-set. -/
def NZ (L : Type) [NormedField L] : SubMulAction (SpecialLinearGroup (Fin 2) L) (Fin 2 → L) where
  carrier := {v | v ≠ 0}
  smul_mem' g v hv := by
    change g • v ≠ 0
    rwa [Ne, smul_eq_zero_iff_eq]

/-- Near the line `L e₀`. -/
def Bp (ε : ℝ) (u : Fin 2 → L) : Prop := ‖u 1‖ ≤ ε * ‖u 0‖

/-- Near the line `L e₁`. -/
def Bm (ε : ℝ) (u : Fin 2 → L) : Prop := ‖u 0‖ ≤ ε * ‖u 1‖

lemma eq_zero_of_norms {u : Fin 2 → L} (h0 : ‖u 0‖ = 0) (h1 : ‖u 1‖ = 0) : u = 0 := by
  funext i; fin_cases i
  · simpa using h0
  · simpa using h1

lemma not_Bp_and_Bm {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {u : Fin 2 → L} (hu : u ≠ 0)
    (hp : Bp ε u) (hm : Bm ε u) : False := by
  unfold Bp at hp; unfold Bm at hm
  have a0 := norm_nonneg (u 0)
  have a1 := norm_nonneg (u 1)
  have h1 : ‖u 1‖ = 0 := by nlinarith
  have h0 : ‖u 0‖ = 0 := by nlinarith
  exact hu (eq_zero_of_norms h0 h1)

/-- Two-sided bounds for `α p + β q` when `‖q‖ ≤ ε ‖p‖`. -/
lemma lin_bounds {ε : ℝ} (p q α β : L) (h : ‖q‖ ≤ ε * ‖p‖) :
    (‖α‖ - ε * ‖β‖) * ‖p‖ ≤ ‖α * p + β * q‖ ∧ ‖α * p + β * q‖ ≤ (‖α‖ + ε * ‖β‖) * ‖p‖ := by
  have hb : ‖β * q‖ ≤ ε * ‖β‖ * ‖p‖ := by
    rw [norm_mul]; nlinarith [norm_nonneg β]
  constructor
  · have := norm_sub_le (α * p + β * q) (β * q)
    rw [add_sub_cancel_right, norm_mul] at this
    nlinarith
  · have := norm_add_le (α * p) (β * q)
    rw [norm_mul] at this
    nlinarith

lemma real_contra {ε a b c d x y z : ℝ} (hx : 0 < x) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hd0 : 0 ≤ d) (hb : 3 * ε * b < a) (hc : 3 * ε * c < a) (hd : 3 * ε * d < a)
    (h1 : (a - ε * b) * x ≤ y) (h2 : y ≤ ε * z) (h3 : z ≤ (c + ε * d) * x) : False := by
  have h4 : (a - ε * b) * x ≤ ε * ((c + ε * d) * x) :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hε0))
  have h5 : a - ε * b ≤ ε * (c + ε * d) := by
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_right hcon hx
    linarith
  nlinarith [mul_nonneg hε0 (mul_nonneg (sub_nonneg.2 hε1) hd0)]

/-- The cross lemma: if all entries of `g` dominate `3 ε` times every entry, then `v` and `g • v`
cannot both lie in `Bp ε ∪ Bm ε`. -/
lemma cross {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (g : SpecialLinearGroup (Fin 2) L)
    (hsm : ∀ i j k l : Fin 2, 3 * ε * ‖g i j‖ < ‖g k l‖) {v : Fin 2 → L} (hv : v ≠ 0)
    (h1 : Bp ε v ∨ Bm ε v) (h2 : Bp ε (g • v) ∨ Bm ε (g • v)) : False := by
  have n0 := norm_nonneg (v 0)
  have n1 := norm_nonneg (v 1)
  rcases h1 with h1 | h1
  · have hv0 : 0 < ‖v 0‖ := by
      rcases n0.lt_or_eq with h | h
      · exact h
      · exfalso; unfold Bp at h1; rw [← h] at h1
        exact hv (eq_zero_of_norms h.symm (by linarith))
    have w0 := lin_bounds (v 0) (v 1) (g 0 0) (g 0 1) h1
    have w1 := lin_bounds (v 0) (v 1) (g 1 0) (g 1 1) h1
    rcases h2 with h2 | h2
    · unfold Bp at h2; rw [smul_apply0, smul_apply1] at h2
      exact real_contra hv0 hε0.le hε1 (norm_nonneg _) (hsm 1 1 1 0) (hsm 0 0 1 0) (hsm 0 1 1 0)
        w1.1 h2 w0.2
    · unfold Bm at h2; rw [smul_apply0, smul_apply1] at h2
      exact real_contra hv0 hε0.le hε1 (norm_nonneg _) (hsm 0 1 0 0) (hsm 1 0 0 0) (hsm 1 1 0 0)
        w0.1 h2 w1.2
  · have hv1 : 0 < ‖v 1‖ := by
      rcases n1.lt_or_eq with h | h
      · exact h
      · exfalso; unfold Bm at h1; rw [← h] at h1
        exact hv (eq_zero_of_norms (by linarith) h.symm)
    have w0 := lin_bounds (v 1) (v 0) (g 0 1) (g 0 0) h1
    have w1 := lin_bounds (v 1) (v 0) (g 1 1) (g 1 0) h1
    rw [add_comm] at w0 w1
    rcases h2 with h2 | h2
    · unfold Bp at h2; rw [smul_apply0, smul_apply1] at h2
      exact real_contra hv1 hε0.le hε1 (norm_nonneg _) (hsm 1 0 1 1) (hsm 0 1 1 1) (hsm 0 0 1 1)
        w1.1 h2 w0.2
    · unfold Bm at h2; rw [smul_apply0, smul_apply1] at h2
      exact real_contra hv1 hε0.le hε1 (norm_nonneg _) (hsm 0 0 0 1) (hsm 1 1 0 1) (hsm 1 0 0 1)
        w0.1 h2 w1.2

end Vectors

section Diag

variable {L : Type} [NormedField L]

/-- The matrix `diag(λ, λ⁻¹)`. -/
noncomputable def dgM (l : Lˣ) : SpecialLinearGroup (Fin 2) L :=
  ⟨!![(l : L), 0; 0, ((l⁻¹ : Lˣ) : L)], by simp [det_fin_two]⟩

lemma coe_dgM (l : Lˣ) :
    ((dgM l : SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      !![(l : L), 0; 0, ((l⁻¹ : Lˣ) : L)] := rfl

/-- The diagonal embedding `λ ↦ diag(λ, λ⁻¹)` of `Lˣ` into `SL(2, L)`. -/
noncomputable def dg : Lˣ →* SpecialLinearGroup (Fin 2) L where
  toFun := dgM
  map_one' := by
    ext i j
    rw [coe_dgM, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_dgM, coe_dgM, coe_dgM, mul_fin_two]
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

lemma coe_dg (l : Lˣ) :
    ((dg l : SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      !![(l : L), 0; 0, ((l⁻¹ : Lˣ) : L)] := rfl

lemma dg_smul0 (l : Lˣ) (u : Fin 2 → L) : (dg l • u) 0 = (l : L) * u 0 := by
  rw [smul_apply0]; simp [coe_dg]

lemma dg_smul1 (l : Lˣ) (u : Fin 2 → L) : (dg l • u) 1 = ((l⁻¹ : Lˣ) : L) * u 1 := by
  rw [smul_apply1]; simp [coe_dg]

lemma dg_Bp {ε : ℝ} (hε : 0 < ε) (l : Lˣ) (hl : 1 ≤ ε * ‖(l : L)‖) {u : Fin 2 → L}
    (hu : ¬ Bm ε u) : Bp ε (dg l • u) := by
  unfold Bm at hu; unfold Bp
  push Not at hu
  rw [dg_smul0, dg_smul1, norm_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv]
  have hr : 0 < ‖(l : L)‖ := by
    rcases (norm_nonneg (l : L)).lt_or_eq with h | h
    · exact h
    · rw [← h] at hl; simp at hl; linarith
  rw [inv_mul_le_iff₀ hr]
  have n0 := norm_nonneg (u 0)
  have n1 := norm_nonneg (u 1)
  have h2 : 1 ≤ (ε * ‖(l : L)‖) ^ 2 := by nlinarith
  have : ε * ‖u 1‖ ≤ ε * (‖(l : L)‖ * (ε * (‖(l : L)‖ * ‖u 0‖))) := by nlinarith
  exact le_of_mul_le_mul_left this hε

lemma dg_Bm {ε : ℝ} (hε : 0 < ε) (l : Lˣ) (hl : 1 ≤ ε * ‖(l : L)‖) {u : Fin 2 → L}
    (hu : ¬ Bp ε u) : Bm ε (dg l⁻¹ • u) := by
  unfold Bp at hu; unfold Bm
  push Not at hu
  rw [dg_smul0, dg_smul1, inv_inv, norm_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv]
  have hr : 0 < ‖(l : L)‖ := by
    rcases (norm_nonneg (l : L)).lt_or_eq with h | h
    · exact h
    · rw [← h] at hl; simp at hl; linarith
  rw [inv_mul_le_iff₀ hr]
  have n0 := norm_nonneg (u 0)
  have n1 := norm_nonneg (u 1)
  have h2 : 1 ≤ (ε * ‖(l : L)‖) ^ 2 := by nlinarith
  have : ε * ‖u 0‖ ≤ ε * (‖(l : L)‖ * (ε * (‖(l : L)‖ * ‖u 1‖))) := by nlinarith
  exact le_of_mul_le_mul_left this hε

/-- The commutator trace of `D = dg l` and `g⁻¹ D g`. -/
lemma trace_comm (l : Lˣ) (g : SpecialLinearGroup (Fin 2) L) :
    ((dg l * (g⁻¹ * dg l * g) * (dg l)⁻¹ * (g⁻¹ * dg l * g)⁻¹ : SpecialLinearGroup (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L).trace =
      2 + ((l : L) - ((l⁻¹ : Lˣ) : L)) ^ 4 * (g 0 0 * g 0 1 * g 1 0 * g 1 1) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2; rw [det_fin_two] at this; exact this
  have hl : (l : L) * ((l⁻¹ : Lˣ) : L) = 1 := Units.mul_inv l
  rw [← map_inv, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← map_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_dg]
  conv_lhs => rw [Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) L)]
  simp only [adjugate_fin_two_of, mul_fin_two, trace_fin_two_of, inv_inv]
  set a := g 0 0
  set b := g 0 1
  set c := g 1 0
  set d := g 1 1
  set μ := (l : L)
  set ν := ((l⁻¹ : Lˣ) : L)
  linear_combination (2 * (μ * ν * (a * d - b * c) + 1) * μ * ν) * hdet +
    (2 * (μ * ν * (a * d - b * c) + 1)) * hl

end Diag

section PingPong

variable {L : Type} [NormedField L]

/-- In `SL(2, L)` with `2 ≠ 0`, an injective lift of a free group misses `-1`: free groups are
torsion-free and `(-1)² = 1 ≠ -1`. -/
lemma neg_one_not_mem_range (h2 : (2 : L) ≠ 0) (a : Fin 2 → SpecialLinearGroup (Fin 2) L)
    (hinj : Function.Injective (FreeGroup.lift a)) :
    (-1 : SpecialLinearGroup (Fin 2) L) ∉ (FreeGroup.lift a).range := by
  rintro ⟨w, hw⟩
  have hw2 : w ^ 2 = 1 ^ 2 := by
    apply hinj
    rw [map_pow, hw, one_pow, map_one, neg_one_sq]
  have hw1 : w = 1 := IsMulTorsionFree.pow_left_injective two_ne_zero hw2
  rw [hw1, map_one] at hw
  apply h2
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) L => (A : Matrix (Fin 2) (Fin 2) L) 0 0) hw
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_neg] at this
  simp at this
  linear_combination this

/-- Ping-pong for `D = diag(λ, λ⁻¹)` and `g⁻¹ D g`, all entries of `g` nonzero. -/
theorem free_diag (l : Lˣ) (hl : 1 < ‖(l : L)‖) (g : SpecialLinearGroup (Fin 2) L)
    (hg : ∀ i j, g i j ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift ![dg l ^ N, g⁻¹ * dg l ^ N * g]) := by
  obtain ⟨ε, hε0, hε1, hsm⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ i j k m : Fin 2, 3 * ε * ‖g i j‖ < ‖g k m‖ := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i j k m : Fin 2, 3 * ε * ‖g i j‖ < ‖g k m‖ := by
      simp only [Filter.eventually_all]
      intro i j k m
      have hc : Continuous fun ε : ℝ => 3 * ε * ‖g i j‖ := by fun_prop
      exact (hc.tendsto' 0 0 (by simp)).eventually_lt_const (by simpa using hg k m)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 := eventually_lt_nhds one_pos
    obtain ⟨ε, ⟨hA, hB⟩, hC⟩ :=
      (((h1.and h2).filter_mono nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
    exact ⟨ε, hC, hB, hA⟩
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 / ε) hl
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, pow_zero, div_lt_one hε0] at hN; linarith
    · exact h
  have hlN : 1 ≤ ε * ‖((l ^ N : Lˣ) : L)‖ := by
    rw [Units.val_pow_eq_pow_val, norm_pow]
    rw [div_lt_iff₀ hε0] at hN; linarith
  refine ⟨N, hNpos, ?_⟩
  let T : Fin 2 → SpecialLinearGroup (Fin 2) L := ![1, g]
  let D := dg (l ^ N)
  have ha : ![dg l ^ N, g⁻¹ * dg l ^ N * g] = fun i => (T i)⁻¹ * D * T i := by
    funext i; fin_cases i <;> simp [T, D, map_pow]
  rw [ha]
  let X : Fin 2 → Set (NZ L) := fun i => {v | Bp ε (T i • (v : Fin 2 → L))}
  let Y : Fin 2 → Set (NZ L) := fun i => {v | Bm ε (T i • (v : Fin 2 → L))}
  have hT0 : ∀ v : Fin 2 → L, T 0 • v = v := fun v => by simp [T]
  have hT1 : ∀ v : Fin 2 → L, T 1 • v = g • v := fun v => by simp [T]
  have hne : ∀ (i : Fin 2) (v : NZ L), T i • (v : Fin 2 → L) ≠ 0 := by
    intro i v
    rw [Ne, smul_eq_zero_iff_eq]; exact v.2
  have hcr : ∀ v : NZ L, (Bp ε (v : Fin 2 → L) ∨ Bm ε (v : Fin 2 → L)) →
      (Bp ε (g • (v : Fin 2 → L)) ∨ Bm ε (g • (v : Fin 2 → L))) → False :=
    fun v h1 h2 => cross hε0 hε1.le g hsm v.2 h1 h2
  apply FreeGroup.injective_lift_of_ping_pong _ X Y
  · intro i
    have he : (T i)⁻¹ • (![1, 0] : Fin 2 → L) ∈ NZ L := by
      change _ ≠ 0
      rw [Ne, smul_eq_zero_iff_eq]
      intro h; have := congrFun h 0; simp at this
    refine ⟨⟨_, he⟩, ?_⟩
    change Bp ε (T i • (T i)⁻¹ • (![1, 0] : Fin 2 → L))
    rw [smul_inv_smul]
    simp [Bp, hε0.le]
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro v hvi hvj
    change Bp ε _ at hvi; change Bp ε _ at hvj
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · simp only [Fin.zero_eta, Fin.mk_one] at hvi hvj
      rw [hT0] at hvi; rw [hT1] at hvj
      exact hcr v (Or.inl hvi) (Or.inl hvj)
    · simp only [Fin.zero_eta, Fin.mk_one] at hvi hvj
      rw [hT1] at hvi; rw [hT0] at hvj
      exact hcr v (Or.inl hvj) (Or.inl hvi)
    · exact hij rfl
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro v hvi hvj
    change Bm ε _ at hvi; change Bm ε _ at hvj
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · simp only [Fin.zero_eta, Fin.mk_one] at hvi hvj
      rw [hT0] at hvi; rw [hT1] at hvj
      exact hcr v (Or.inr hvi) (Or.inr hvj)
    · simp only [Fin.zero_eta, Fin.mk_one] at hvi hvj
      rw [hT1] at hvi; rw [hT0] at hvj
      exact hcr v (Or.inr hvj) (Or.inr hvi)
    · exact hij rfl
  · intro i j
    rw [Set.disjoint_left]
    intro v hvi hvj
    change Bp ε _ at hvi; change Bm ε _ at hvj
    by_cases hij : i = j
    · subst hij
      exact not_Bp_and_Bm hε0 hε1 (hne i v) hvi hvj
    · fin_cases i <;> fin_cases j
      · exact hij rfl
      · simp only [Fin.zero_eta, Fin.mk_one] at hvi hvj
        rw [hT0] at hvi; rw [hT1] at hvj
        exact hcr v (Or.inl hvi) (Or.inr hvj)
      · simp only [Fin.zero_eta, Fin.mk_one] at hvi hvj
        rw [hT1] at hvi; rw [hT0] at hvj
        exact hcr v (Or.inr hvj) (Or.inl hvi)
      · exact hij rfl
  · intro i
    rw [Set.smul_set_subset_iff]
    intro v hv
    change ¬ Bm ε _ at hv
    change Bp ε (T i • ((((T i)⁻¹ * D * T i) • v : NZ L) : Fin 2 → L))
    rw [SubMulAction.val_smul, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
      mul_smul]
    exact dg_Bp hε0 (l ^ N) hlN hv
  · intro i
    rw [Set.smul_set_subset_iff]
    intro v hv
    change ¬ Bp ε _ at hv
    change Bm ε (T i • ((((T i)⁻¹ * D * T i)⁻¹ • v : NZ L) : Fin 2 → L))
    rw [SubMulAction.val_smul, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_smul,
      ← mul_assoc, mul_inv_cancel, one_mul, mul_smul]
    have : D⁻¹ = dg (l ^ N)⁻¹ := (map_inv dg (l ^ N)).symm
    rw [this]
    exact dg_Bm hε0 (l ^ N) hlN hv

end PingPong

section Diagonalize

variable {L : Type} [NormedField L]

/-- An element of `SL(2, L)` from its entries. -/
def mkSL (a b c d : L) (h : a * d - b * c = 1) : SpecialLinearGroup (Fin 2) L :=
  ⟨!![a, b; c, d], by rw [det_fin_two_of]; exact h⟩

lemma coe_mkSL (a b c d : L) (h : a * d - b * c = 1) :
    ((mkSL a b c d h : SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      !![a, b; c, d] := rfl

/-- Entrywise check of `x P = P diag(λ, λ⁻¹)`. -/
lemma mul_mkSL_eq (x : SpecialLinearGroup (Fin 2) L) (l : Lˣ) (a b c d : L)
    (h : a * d - b * c = 1)
    (e00 : x 0 0 * a + x 0 1 * c = a * l) (e01 : x 0 0 * b + x 0 1 * d = b * ((l⁻¹ : Lˣ) : L))
    (e10 : x 1 0 * a + x 1 1 * c = c * l) (e11 : x 1 0 * b + x 1 1 * d = d * ((l⁻¹ : Lˣ) : L)) :
    x * mkSL a b c d h = mkSL a b c d h * dg l := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_mkSL, coe_dg]
  conv_lhs => rw [Matrix.eta_fin_two (x : Matrix (Fin 2) (Fin 2) L)]
  rw [mul_fin_two, mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

/-- The eigenvector computation for `[[p, q], [r, s]]` with eigenvalues `μ ≠ ν`, `μ ν = 1`. -/
lemma exists_eigenbasis (p q r s μ ν : L) (hμν : μ * ν = 1) (hdiff : μ - ν ≠ 0)
    (hdet : p * s - q * r = 1) (htr : μ + ν = p + s) :
    ∃ (a b c d : L) (_ : a * d - b * c = 1), p * a + q * c = a * μ ∧ p * b + q * d = b * ν ∧
      r * a + s * c = c * μ ∧ r * b + s * d = d * ν := by
  by_cases hq : q = 0
  · subst hq
    have hroots : (p - μ) * (p - ν) = 0 := by
      linear_combination (-1 : L) * hdet + (-p) * htr + hμν
    set k : L := (μ - ν)⁻¹
    have hk : k * (μ - ν) = 1 := inv_mul_cancel₀ hdiff
    rcases mul_eq_zero.1 hroots with h | h
    · -- `p = μ`, `s = ν`
      have hp : p = μ := sub_eq_zero.1 h
      have hs : s = ν := by linear_combination -htr - hp
      subst hp hs
      exact ⟨1, 0, r * k, 1, by ring, by ring, by ring, by linear_combination (-r) * hk, by ring⟩
    · -- `p = ν`, `s = μ`
      have hp : p = ν := sub_eq_zero.1 h
      have hs : s = μ := by linear_combination -htr - hp
      subst hp hs
      exact ⟨0, -1, 1, r * k, by ring, by ring, by ring, by ring, by linear_combination r * hk⟩
  · set k : L := (q * (ν - μ))⁻¹
    have hk : k * (q * (ν - μ)) = 1 :=
      inv_mul_cancel₀ (mul_ne_zero hq (fun h => hdiff (by linear_combination -h)))
    exact ⟨q, q * k, μ - p, (ν - p) * k, by linear_combination hk, by ring, by ring,
      by linear_combination (-1 : L) * hdet + (-μ) * htr + hμν,
      by linear_combination k * ((-1 : L) * hdet + (-ν) * htr + hμν)⟩

/-- Diagonalization of `x` with trace `λ + λ⁻¹`, `‖λ‖ > 1`. -/
lemma exists_diag (x : SpecialLinearGroup (Fin 2) L) (l : Lˣ) (hl : 1 < ‖(l : L)‖)
    (hx : (l : L) + ((l⁻¹ : Lˣ) : L) = (x : Matrix (Fin 2) (Fin 2) L).trace) :
    ∃ P : SpecialLinearGroup (Fin 2) L, x * P = P * dg l := by
  have hμν : (l : L) * ((l⁻¹ : Lˣ) : L) = 1 := Units.mul_inv l
  have hdiff : (l : L) - ((l⁻¹ : Lˣ) : L) ≠ 0 := by
    intro h
    have h' : (l : L) = ((l⁻¹ : Lˣ) : L) := sub_eq_zero.1 h
    have hn : ‖((l⁻¹ : Lˣ) : L)‖ * ‖(l : L)‖ = 1 := by
      rw [← norm_mul, mul_comm, hμν, norm_one]
    rw [← h'] at hn
    nlinarith
  have hdet : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1 := by
    have := x.2; rw [det_fin_two] at this; exact this
  have htr : (l : L) + ((l⁻¹ : Lˣ) : L) = x 0 0 + x 1 1 := by rw [hx, trace_fin_two]
  obtain ⟨a, b, c, d, h, e00, e01, e10, e11⟩ :=
    exists_eigenbasis (x 0 0) (x 0 1) (x 1 0) (x 1 1) _ _ hμν hdiff hdet htr
  exact ⟨mkSL a b c d h, mul_mkSL_eq x l a b c d h e00 e01 e10 e11⟩

end Diagonalize

/-- Part 3P: ping-pong over a normed field. -/
theorem exists_injective_lift_pow_and_neg_one_notMem_range_of_proximal {L : Type} [NormedField L] (h2 : (2 : L) ≠ 0)
    (x c : Matrix.SpecialLinearGroup (Fin 2) L) (μ : L) (hμ : 1 < ‖μ‖)
    (hx : μ + μ⁻¹ = (x : Matrix (Fin 2) (Fin 2) L).trace)
    (hc : ((x * (c * x * c⁻¹) * x⁻¹ * (c * x * c⁻¹)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L).trace ≠ 2) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift ![x ^ N, c * x ^ N * c⁻¹]) ∧
      (-1 : Matrix.SpecialLinearGroup (Fin 2) L) ∉ (FreeGroup.lift ![x ^ N, c * x ^ N * c⁻¹]).range := by
  have hμ0 : μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hμ; linarith
  set l : Lˣ := Units.mk0 μ hμ0
  have hl : (l : L) = μ := rfl
  have hli : ((l⁻¹ : Lˣ) : L) = μ⁻¹ := by simp [l]
  obtain ⟨P, hP⟩ := exists_diag x l (by rwa [hl]) (by rw [hl, hli]; exact hx)
  have hxP : x = P * dg l * P⁻¹ := eq_mul_inv_of_mul_eq hP
  set g : SpecialLinearGroup (Fin 2) L := P⁻¹ * c⁻¹ * P with hg
  have hcomm : x * (c * x * c⁻¹) * x⁻¹ * (c * x * c⁻¹)⁻¹ =
      P * (dg l * (g⁻¹ * dg l * g) * (dg l)⁻¹ * (g⁻¹ * dg l * g)⁻¹) * P⁻¹ := by
    rw [hxP, hg]; group
  have htr : ((x * (c * x * c⁻¹) * x⁻¹ * (c * x * c⁻¹)⁻¹ : SpecialLinearGroup (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L).trace =
      ((dg l * (g⁻¹ * dg l * g) * (dg l)⁻¹ * (g⁻¹ * dg l * g)⁻¹ : SpecialLinearGroup (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L).trace := by
    rw [hcomm, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  rw [htr, trace_comm] at hc
  have hprod : g 0 0 * g 0 1 * g 1 0 * g 1 1 ≠ 0 := by
    intro h; apply hc; rw [h, mul_zero, add_zero]
  have hgne : ∀ i j, g i j ≠ 0 := by
    simp only [mul_ne_zero_iff] at hprod
    intro i j; fin_cases i <;> fin_cases j
    · exact hprod.1.1.1
    · exact hprod.1.1.2
    · exact hprod.1.2
    · exact hprod.2
  obtain ⟨N, hN, hinj⟩ := free_diag l (by rwa [hl]) g hgne
  have hlift : FreeGroup.lift ![x ^ N, c * x ^ N * c⁻¹] =
      (MulAut.conj P).toMonoidHom.comp (FreeGroup.lift ![dg l ^ N, g⁻¹ * dg l ^ N * g]) := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i
    · simp [hxP, conj_pow]
    · simp [hxP, conj_pow, hg]
      group
  have hinj' : Function.Injective (FreeGroup.lift ![x ^ N, c * x ^ N * c⁻¹]) := by
    rw [hlift]; exact (MulAut.conj P).injective.comp hinj
  exact ⟨N, hN, hinj', neg_one_not_mem_range h2 _ hinj'⟩

end PingPongSL2

end
end

section
open PingPongSL2

theorem solution {L : Type} [NormedField L] (h2 : (2 : L) ≠ 0)
    (x c : Matrix.SpecialLinearGroup (Fin 2) L) (μ : L) (hμ : 1 < ‖μ‖)
    (hx : μ + μ⁻¹ = (x : Matrix (Fin 2) (Fin 2) L).trace)
    (hc : ((x * (c * x * c⁻¹) * x⁻¹ * (c * x * c⁻¹)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L).trace ≠ 2) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift ![x ^ N, c * x ^ N * c⁻¹]) ∧
      (-1 : Matrix.SpecialLinearGroup (Fin 2) L) ∉ (FreeGroup.lift ![x ^ N, c * x ^ N * c⁻¹]).range := by
  apply PingPongSL2.exists_injective_lift_pow_and_neg_one_notMem_range_of_proximal <;> assumption

end
