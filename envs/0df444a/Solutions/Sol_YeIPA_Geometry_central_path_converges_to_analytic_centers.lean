-- Prove2me | solution 1 for YeIPA.Geometry.central_path_converges_to_analytic_centers
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:29:46.44467+00:00
-- url     : https://prove2.me/submissions/2b42e650-12ac-4608-a40b-a49d73223a24

import Mathlib
import Definitions.Def_YeIPA_Geometry_CentralPath

open Matrix Filter Topology
open YeIPA.Geometry

theorem g69c_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hx : A *ᵥ x = b)
    (hs : Aᵀ *ᵥ y + s = c) : c ⬝ᵥ x = b ⬝ᵥ y + x ⬝ᵥ s := by
  rw [← hs, ← hx, add_dotProduct, mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm s x,
    dotProduct_comm (A *ᵥ x) y]

theorem g69c_nonneg_dot {n : ℕ} (x s : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (hs : ∀ j, 0 ≤ s j)
    (j : Fin n) : x j * s j ≤ x ⬝ᵥ s := by
  unfold dotProduct
  exact Finset.single_le_sum (f := fun i => x i * s i) (fun i _ => mul_nonneg (hx i) (hs i))
    (Finset.mem_univ j)

theorem g69c_dot_nonneg {n : ℕ} (x s : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (hs : ∀ j, 0 ≤ s j) :
    0 ≤ x ⬝ᵥ s := Finset.sum_nonneg (fun j _ => mul_nonneg (hx j) (hs j))

theorem g69c_xs_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ) (hx0 : A *ᵥ x0 = b)
    (hx0p : ∀ j, 0 < x0 j) (hs0 : Aᵀ *ᵥ y0 + s0 = c) (hs0p : ∀ j, 0 < s0 j) (K : ℝ) :
    ∃ R, 0 ≤ R ∧ ∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ), A *ᵥ x = b →
      (∀ j, 0 ≤ x j) → Aᵀ *ᵥ y + s = c → (∀ j, 0 ≤ s j) → x ⬝ᵥ s ≤ K →
      ∀ j, |x j| ≤ R ∧ |s j| ≤ R := by
  set L := |K| + x0 ⬝ᵥ s0
  have hL : 0 ≤ L := add_nonneg (abs_nonneg K)
    (g69c_dot_nonneg x0 s0 (fun j => (hx0p j).le) (fun j => (hs0p j).le))
  set T := ∑ j, (1 / s0 j + 1 / x0 j)
  have hT : ∀ j, 1 / s0 j ≤ T ∧ 1 / x0 j ≤ T := by
    intro j
    have h1 : 1 / s0 j + 1 / x0 j ≤ T :=
      Finset.single_le_sum (f := fun j => 1 / s0 j + 1 / x0 j)
        (fun i _ => add_nonneg (by have := hs0p i; positivity) (by have := hx0p i; positivity))
        (Finset.mem_univ j)
    have := hs0p j; have := hx0p j
    have a1 : 0 ≤ 1 / s0 j := by positivity
    have a2 : 0 ≤ 1 / x0 j := by positivity
    constructor <;> linarith
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ =>
    add_nonneg (by have := hs0p i; positivity) (by have := hx0p i; positivity))
  refine ⟨L * T, mul_nonneg hL hT0, ?_⟩
  intro x y s hx hxn hs hsn hK j
  have e1 := g69c_gap A b c x y s hx hs
  have e2 := g69c_gap A b c x0 y0 s0 hx0 hs0
  have e3 := g69c_gap A b c x y0 s0 hx hs0
  have e4 := g69c_gap A b c x0 y s hx0 hs
  have hid : x ⬝ᵥ s0 + x0 ⬝ᵥ s = x ⬝ᵥ s + x0 ⬝ᵥ s0 := by linarith
  have d1 := g69c_dot_nonneg x0 s (fun j => (hx0p j).le) hsn
  have d2 := g69c_dot_nonneg x s0 hxn (fun j => (hs0p j).le)
  have hKa := le_abs_self K
  have b1 := g69c_nonneg_dot x s0 hxn (fun j => (hs0p j).le) j
  have b2 := g69c_nonneg_dot x0 s (fun j => (hx0p j).le) hsn j
  have hx1 : x j * s0 j ≤ L := by linarith
  have hs1 : x0 j * s j ≤ L := by linarith
  have hsj := hs0p j
  have hxj := hx0p j
  obtain ⟨t1, t2⟩ := hT j
  rw [abs_of_nonneg (hxn j), abs_of_nonneg (hsn j)]
  constructor
  · have : x j ≤ L * (1 / s0 j) := by
      rw [mul_one_div, le_div_iff₀ hsj]; exact hx1
    exact this.trans (mul_le_mul_of_nonneg_left t1 hL)
  · have : s j ≤ L * (1 / x0 j) := by
      rw [mul_one_div, le_div_iff₀ hxj]; linarith
    exact this.trans (mul_le_mul_of_nonneg_left t2 hL)

theorem g69c_AAt_unit {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hrank : A.rank = m) :
    IsUnit (A * Aᵀ).det := by
  have hr : (A * Aᵀ).rank = m := by rw [Matrix.rank_self_mul_transpose]; exact hrank
  have htop : LinearMap.range (A * Aᵀ).mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [show Module.finrank ℝ (LinearMap.range (A * Aᵀ).mulVecLin) = (A * Aᵀ).rank from rfl, hr]
    simp
  have hsurj : Function.Surjective (A * Aᵀ).mulVec := LinearMap.range_eq_top.mp htop
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)

theorem g69c_y_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hrank : A.rank = m)
    (c s : Fin n → ℝ) (y : Fin m → ℝ) (hs : Aᵀ *ᵥ y + s = c) :
    y = ((A * Aᵀ)⁻¹ * A) *ᵥ (c - s) := by
  have h1 : c - s = Aᵀ *ᵥ y := by rw [← hs]; abel
  rw [h1, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (g69c_AAt_unit A hrank),
    Matrix.one_mulVec]

theorem g69geo_cl {α X : Type*} [TopologicalSpace X] {F : Filter α} {f : α → X} {p : X}
    (hp : MapClusterPt p F f) {g : X → ℝ} (hg : ContinuousAt g p) {v : ℝ}
    (hv : Tendsto (g ∘ f) F (𝓝 v)) : g p = v :=
  eq_of_nhds_neBot ((hp.continuousAt_comp hg).clusterPt.mono hv).neBot

theorem g69geo_pi {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (μ : ℝ) (hμ : 0 < μ) (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (h : IsCentralPathPoint A b c μ x y s) (x' : Fin n → ℝ) (y' : Fin m → ℝ) (s' : Fin n → ℝ)
    (hx' : A *ᵥ x' = b) (hs' : Aᵀ *ᵥ y' + s' = c) (hc' : ∀ j, x' j * s' j = 0) :
    ∑ j, (x' j / x j + s' j / s j) = (n : ℝ) := by
  obtain ⟨⟨hAx, hxp⟩, ⟨hys, hsp⟩, hc⟩ := h
  have e1 := g69c_gap A b c x y s hAx hys
  have e2 := g69c_gap A b c x' y' s' hx' hs'
  have e3 := g69c_gap A b c x y' s' hAx hs'
  have e4 := g69c_gap A b c x' y s hx' hys
  have h0 : x' ⬝ᵥ s' = 0 := by simp [dotProduct, hc']
  have hxs : x ⬝ᵥ s = n * μ := by
    unfold dotProduct; simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hterm : ∀ j, x' j / x j + s' j / s j = (x' j * s j + x j * s' j) / μ := by
    intro j; have := hxp j; have := hsp j; rw [← hc j]; field_simp
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_div, Finset.sum_add_distrib]
  have h5 : ∑ j, x' j * s j = x' ⬝ᵥ s := rfl
  have h6 : ∑ j, x j * s' j = x ⬝ᵥ s' := rfl
  have : ∑ j, x' j * s j + ∑ j, x j * s' j = n * μ := by linarith
  rw [this]; field_simp

theorem g69geo_L {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ) (s : ℝ → Fin n → ℝ)
    (hcp : ∀ μ : ℝ, 0 < μ → IsCentralPathPoint A b c μ (x μ) (y μ) (s μ))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) (hp : MapClusterPt p (𝓝[>] (0:ℝ)) (fun μ => (x μ, s μ)))
    (x' : Fin n → ℝ) (y' : Fin m → ℝ) (s' : Fin n → ℝ)
    (hx' : A *ᵥ x' = b) (hs' : Aᵀ *ᵥ y' + s' = c) (hc' : ∀ j, x' j * s' j = 0)
    (hsx : ∀ j, x' j = 0 ∨ p.1 j ≠ 0) (hss : ∀ j, s' j = 0 ∨ p.2 j ≠ 0) :
    ∑ j, (x' j / p.1 j + s' j / p.2 j) = (n : ℝ) := by
  refine g69geo_cl hp (g := fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
    ∑ j, (x' j / q.1 j + s' j / q.2 j)) ?_ ?_
  · refine tendsto_finsetSum _ (fun j _ => ?_)
    refine ContinuousAt.add ?_ ?_
    · rcases hsx j with h | h
      · simp only [h, zero_div]; exact continuousAt_const
      · exact continuousAt_const.div ((continuous_apply j).comp continuous_fst).continuousAt h
    · rcases hss j with h | h
      · simp only [h, zero_div]; exact continuousAt_const
      · exact continuousAt_const.div ((continuous_apply j).comp continuous_snd).continuousAt h
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with μ hμ
    exact (g69geo_pi A b c μ hμ _ _ _ (hcp μ hμ) x' y' s' hx' hs' hc').symm

theorem g69geo_basic {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hrank : A.rank = m)
    (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ) (s : ℝ → Fin n → ℝ)
    (hcp : ∀ μ : ℝ, 0 < μ → IsCentralPathPoint A b c μ (x μ) (y μ) (s μ))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) (hp : MapClusterPt p (𝓝[>] (0:ℝ)) (fun μ => (x μ, s μ))) :
    A *ᵥ p.1 = b ∧ (∀ j, 0 ≤ p.1 j) ∧ Aᵀ *ᵥ (((A * Aᵀ)⁻¹ * A) *ᵥ (c - p.2)) + p.2 = c ∧
      (∀ j, 0 ≤ p.2 j) ∧ ∀ j, p.1 j * p.2 j = 0 := by
  have hev : ∀ᶠ μ in 𝓝[>] (0:ℝ), IsCentralPathPoint A b c μ (x μ) (y μ) (s μ) ∧ 0 < μ := by
    filter_upwards [self_mem_nhdsWithin] with μ hμ using ⟨hcp μ hμ, hμ⟩
  refine ⟨?_, fun j => ?_, ?_, fun j => ?_, fun j => ?_⟩
  · exact IsClosed.mem_of_mapClusterPt (s := {q : (Fin n → ℝ) × (Fin n → ℝ) | A *ᵥ q.1 = b})
      (isClosed_eq (continuous_const.matrix_mulVec continuous_fst) continuous_const) hp
      (hev.mono fun μ h => h.1.1.1)
  · exact IsClosed.mem_of_mapClusterPt (s := {q : (Fin n → ℝ) × (Fin n → ℝ) | 0 ≤ q.1 j})
      (isClosed_le continuous_const ((continuous_apply j).comp continuous_fst)) hp
      (hev.mono fun μ h => (h.1.1.2 j).le)
  · exact IsClosed.mem_of_mapClusterPt (s := {q : (Fin n → ℝ) × (Fin n → ℝ) |
        Aᵀ *ᵥ (((A * Aᵀ)⁻¹ * A) *ᵥ (c - q.2)) + q.2 = c})
      (isClosed_eq ((continuous_const.matrix_mulVec (continuous_const.matrix_mulVec
        (continuous_const.sub continuous_snd))).add continuous_snd) continuous_const) hp
      (hev.mono fun μ h => by
        simp only [Set.mem_ofPred_eq]
        rw [← g69c_y_eq A hrank c (s μ) (y μ) h.1.2.1.1]; exact h.1.2.1.1)
  · exact IsClosed.mem_of_mapClusterPt (s := {q : (Fin n → ℝ) × (Fin n → ℝ) | 0 ≤ q.2 j})
      (isClosed_le continuous_const ((continuous_apply j).comp continuous_snd)) hp
      (hev.mono fun μ h => (h.1.2.1.2 j).le)
  · refine g69geo_cl hp (g := fun q : (Fin n → ℝ) × (Fin n → ℝ) => q.1 j * q.2 j)
      ((((continuous_apply j).comp continuous_fst).mul
        ((continuous_apply j).comp continuous_snd)).continuousAt) ?_
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hev] with μ h
    exact (h.1.2.2 j).symm

theorem g69geo_t1 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = 0) :
    0 ≤ 1 - (a / a + b / b) ∧ (1 - (a / a + b / b) = 0 → 0 < a + b) := by
  rcases mul_eq_zero.1 hab with h | h
  · subst h
    rcases eq_or_lt_of_le hb with h' | h'
    · subst h'; norm_num
    · rw [div_self h'.ne']; norm_num; linarith
  · subst h
    rcases eq_or_lt_of_le ha with h' | h'
    · subst h'; norm_num
    · rw [div_self h'.ne']; norm_num; linarith

theorem g69geo_strict {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hrank : A.rank = m)
    (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ) (s : ℝ → Fin n → ℝ)
    (hcp : ∀ μ : ℝ, 0 < μ → IsCentralPathPoint A b c μ (x μ) (y μ) (s μ))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) (hp : MapClusterPt p (𝓝[>] (0:ℝ)) (fun μ => (x μ, s μ))) :
    ∀ j, 0 < p.1 j + p.2 j := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := g69geo_basic A b c hrank x y s hcp p hp
  have E := g69geo_L A b c x y s hcp p hp p.1 _ p.2 h1 h3 h5 (fun j => em _) (fun j => em _)
  have hz : ∑ j, (1 - (p.1 j / p.1 j + p.2 j / p.2 j)) = 0 := by
    rw [Finset.sum_sub_distrib, E]; simp
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (g69geo_t1 _ _ (h2 j) (h4 j) (h5 j)).1)] at hz
  intro j
  exact (g69geo_t1 _ _ (h2 j) (h4 j) (h5 j)).2 (hz j (Finset.mem_univ j))

theorem g69geo_cross {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x1 : Fin n → ℝ) (y1 : Fin m → ℝ) (s1 : Fin n → ℝ)
    (x2 : Fin n → ℝ) (y2 : Fin m → ℝ) (s2 : Fin n → ℝ)
    (hx1 : A *ᵥ x1 = b) (hs1 : Aᵀ *ᵥ y1 + s1 = c) (hc1 : ∀ j, x1 j * s1 j = 0)
    (hx1n : ∀ j, 0 ≤ x1 j) (hs1n : ∀ j, 0 ≤ s1 j)
    (hx2 : A *ᵥ x2 = b) (hs2 : Aᵀ *ᵥ y2 + s2 = c) (hc2 : ∀ j, x2 j * s2 j = 0)
    (hx2n : ∀ j, 0 ≤ x2 j) (hs2n : ∀ j, 0 ≤ s2 j) :
    ∀ j, x1 j * s2 j = 0 := by
  have e1 := g69c_gap A b c x1 y1 s1 hx1 hs1
  have e2 := g69c_gap A b c x2 y2 s2 hx2 hs2
  have e3 := g69c_gap A b c x1 y2 s2 hx1 hs2
  have e4 := g69c_gap A b c x2 y1 s1 hx2 hs1
  have z1 : x1 ⬝ᵥ s1 = 0 := by simp [dotProduct, hc1]
  have z2 : x2 ⬝ᵥ s2 = 0 := by simp [dotProduct, hc2]
  have d1 := g69c_dot_nonneg x1 s2 hx1n hs2n
  have d2 := g69c_dot_nonneg x2 s1 hx2n hs1n
  intro j
  have := g69c_nonneg_dot x1 s2 hx1n hs2n j
  exact le_antisymm (by linarith) (mul_nonneg (hx1n j) (hs2n j))

theorem g69geo_char {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xb : Fin n → ℝ) (yb : Fin m → ℝ) (sb : Fin n → ℝ)
    (hsc : IsStrictlyComplementary A b c xb yb sb) :
    (∀ j, j ∈ Pstar A b c ↔ 0 < xb j) ∧ (∀ j, j ∈ Zstar A b c ↔ 0 < sb j) := by
  classical
  obtain ⟨⟨hx, hxn⟩, ⟨hs, hsn⟩, hc, hpos⟩ := hsc
  constructor
  · intro j
    unfold Pstar
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, x1, y1, s1, ⟨⟨hx1, hx1n⟩, ⟨hs1, hs1n⟩, hc1, -⟩, hj⟩
      have h := g69geo_cross A b c x1 y1 s1 xb yb sb hx1 hs1 hc1 hx1n hs1n hx hs hc hxn hsn j
      have hsj : sb j = 0 := by
        rcases mul_eq_zero.1 h with h | h
        · linarith
        · exact h
      have := hpos j; linarith
    · intro hj; exact ⟨Finset.mem_univ j, xb, yb, sb, ⟨⟨hx, hxn⟩, ⟨hs, hsn⟩, hc, hpos⟩, hj⟩
  · intro j
    unfold Zstar
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, x1, y1, s1, ⟨⟨hx1, hx1n⟩, ⟨hs1, hs1n⟩, hc1, -⟩, hj⟩
      have h := g69geo_cross A b c xb yb sb x1 y1 s1 hx hs hc hxn hsn hx1 hs1 hc1 hx1n hs1n j
      have hxj : xb j = 0 := by
        rcases mul_eq_zero.1 h with h | h
        · exact h
        · linarith
      have := hpos j; linarith
    · intro hj; exact ⟨Finset.mem_univ j, xb, yb, sb, ⟨⟨hx, hxn⟩, ⟨hs, hsn⟩, hc, hpos⟩, hj⟩

theorem g69geo_cp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ) (s : ℝ → Fin n → ℝ)
    (hcp : ∀ μ : ℝ, 0 < μ → IsCentralPathPoint A b c μ (x μ) (y μ) (s μ))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) (hp : MapClusterPt p (𝓝[>] (0:ℝ)) (fun μ => (x μ, s μ)))
    (yb : Fin m → ℝ) (hyb : Aᵀ *ᵥ yb + p.2 = c) (hx : A *ᵥ p.1 = b)
    (hc : ∀ j, p.1 j * p.2 j = 0) (hxn : ∀ j, 0 ≤ p.1 j) (hsn : ∀ j, 0 ≤ p.2 j)
    (hpos : ∀ j, 0 < p.1 j + p.2 j)
    (hP : ∀ j, j ∈ Pstar A b c ↔ 0 < p.1 j) (hZ : ∀ j, j ∈ Zstar A b c ↔ 0 < p.2 j) :
    IsPrimalFaceAnalyticCenter A b c p.1 := by
  have E0 := g69geo_L A b c x y s hcp p hp p.1 yb p.2 hx hyb hc (fun j => em _) (fun j => em _)
  refine ⟨⟨hx, fun j _ => hxn j, fun j hj => ?_⟩, fun j hj => (hP j).1 hj, fun x' hx' hx'p => ?_⟩
  · have := (hZ j).1 hj
    rcases mul_eq_zero.1 (hc j) with h | h
    · exact h
    · linarith
  · obtain ⟨hAx', -, hx'z⟩ := hx'
    have hzero : ∀ j, ¬ 0 < p.1 j → x' j = 0 := by
      intro j hj; apply hx'z; rw [hZ]; have := hpos j; push_neg at hj; linarith
    have hc' : ∀ j, x' j * p.2 j = 0 := by
      intro j
      by_cases h : 0 < p.1 j
      · rcases mul_eq_zero.1 (hc j) with h' | h'
        · linarith
        · rw [h', mul_zero]
      · rw [hzero j h, zero_mul]
    have E1 := g69geo_L A b c x y s hcp p hp x' yb p.2 hAx' hyb hc'
      (fun j => by
        by_cases h : 0 < p.1 j
        · exact Or.inr h.ne'
        · exact Or.inl (hzero j h)) (fun j => em _)
    rw [Finset.sum_add_distrib] at E0 E1
    have hsum : ∑ j, (x' j / p.1 j - p.1 j / p.1 j) = 0 := by
      rw [Finset.sum_sub_distrib]; linarith
    have hsub : ∑ j ∈ Pstar A b c, (x' j / p.1 j - p.1 j / p.1 j) =
        ∑ j, (x' j / p.1 j - p.1 j / p.1 j) := by
      refine Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => ?_)
      have : p.1 j = 0 := by
        have := hxn j; rw [hP] at hj; push_neg at hj; linarith
      simp [this]
    have key : ∑ j ∈ Pstar A b c, (Real.log (x' j) - Real.log (p.1 j)) ≤
        ∑ j ∈ Pstar A b c, (x' j / p.1 j - p.1 j / p.1 j) := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      have h1 := (hP j).1 hj
      have h2 := hx'p j hj
      rw [← Real.log_div h2.ne' h1.ne', div_self h1.ne']
      exact Real.log_le_sub_one_of_pos (div_pos h2 h1)
    rw [Finset.sum_sub_distrib] at key
    linarith

theorem g69geo_cd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ) (s : ℝ → Fin n → ℝ)
    (hcp : ∀ μ : ℝ, 0 < μ → IsCentralPathPoint A b c μ (x μ) (y μ) (s μ))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) (hp : MapClusterPt p (𝓝[>] (0:ℝ)) (fun μ => (x μ, s μ)))
    (yb : Fin m → ℝ) (hyb : Aᵀ *ᵥ yb + p.2 = c) (hx : A *ᵥ p.1 = b)
    (hc : ∀ j, p.1 j * p.2 j = 0) (hxn : ∀ j, 0 ≤ p.1 j) (hsn : ∀ j, 0 ≤ p.2 j)
    (hpos : ∀ j, 0 < p.1 j + p.2 j)
    (hP : ∀ j, j ∈ Pstar A b c ↔ 0 < p.1 j) (hZ : ∀ j, j ∈ Zstar A b c ↔ 0 < p.2 j) :
    IsDualFaceAnalyticCenter A b c p.2 := by
  have E0 := g69geo_L A b c x y s hcp p hp p.1 yb p.2 hx hyb hc (fun j => em _) (fun j => em _)
  refine ⟨⟨⟨yb, hyb⟩, fun j _ => hsn j, fun j hj => ?_⟩, fun j hj => (hZ j).1 hj,
    fun s' hs' hs'p => ?_⟩
  · have := (hP j).1 hj
    rcases mul_eq_zero.1 (hc j) with h | h
    · linarith
    · exact h
  · obtain ⟨⟨y', hy'⟩, -, hs'z⟩ := hs'
    have hzero : ∀ j, ¬ 0 < p.2 j → s' j = 0 := by
      intro j hj; apply hs'z; rw [hP]; have := hpos j; push_neg at hj; linarith
    have hc' : ∀ j, p.1 j * s' j = 0 := by
      intro j
      by_cases h : 0 < p.2 j
      · rcases mul_eq_zero.1 (hc j) with h' | h'
        · rw [h', zero_mul]
        · linarith
      · rw [hzero j h, mul_zero]
    have E1 := g69geo_L A b c x y s hcp p hp p.1 y' s' hx hy' hc' (fun j => em _)
      (fun j => by
        by_cases h : 0 < p.2 j
        · exact Or.inr h.ne'
        · exact Or.inl (hzero j h))
    rw [Finset.sum_add_distrib] at E0 E1
    have hsum : ∑ j, (s' j / p.2 j - p.2 j / p.2 j) = 0 := by
      rw [Finset.sum_sub_distrib]; linarith
    have hsub : ∑ j ∈ Zstar A b c, (s' j / p.2 j - p.2 j / p.2 j) =
        ∑ j, (s' j / p.2 j - p.2 j / p.2 j) := by
      refine Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => ?_)
      have : p.2 j = 0 := by
        have := hsn j; rw [hZ] at hj; push_neg at hj; linarith
      simp [this]
    have key : ∑ j ∈ Zstar A b c, (Real.log (s' j) - Real.log (p.2 j)) ≤
        ∑ j ∈ Zstar A b c, (s' j / p.2 j - p.2 j / p.2 j) := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      have h1 := (hZ j).1 hj
      have h2 := hs'p j hj
      rw [← Real.log_div h2.ne' h1.ne', div_self h1.ne']
      exact Real.log_le_sub_one_of_pos (div_pos h2 h1)
    rw [Finset.sum_sub_distrib] at key
    linarith

theorem g69geo_tt (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ b / a + a / b - 2 ∧ (b / a + a / b - 2 = 0 → a = b) := by
  have e : b / a + a / b - 2 = (a - b) ^ 2 / (a * b) := by field_simp; ring
  rw [e]
  refine ⟨div_nonneg (sq_nonneg _) (mul_pos ha hb).le, fun h => ?_⟩
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h; linarith
  · exact absurd h (mul_pos ha hb).ne'

theorem g69geo_pair (a1 a2 b1 b2 : ℝ) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (ha : a1 * a2 = 0) (hpos : 0 < a1 + a2) (h1 : 0 < a1 ↔ 0 < b1) (h2 : 0 < a2 ↔ 0 < b2) :
    0 ≤ (b1 / a1 + b2 / a2) + (a1 / b1 + a2 / b2) - 2 ∧
      ((b1 / a1 + b2 / a2) + (a1 / b1 + a2 / b2) - 2 = 0 → a1 = b1 ∧ a2 = b2) := by
  rcases mul_eq_zero.1 ha with h | h
  · subst h
    have pa2 : 0 < a2 := by linarith
    have pb2 := h2.1 pa2
    have zb1 : b1 = 0 := by
      rcases eq_or_lt_of_le hb1 with h | h
      · exact h.symm
      · exact absurd (h1.2 h) (lt_irrefl 0)
    subst zb1
    have := g69geo_tt a2 b2 pa2 pb2
    simp only [div_zero, zero_add]
    exact ⟨this.1, fun h => ⟨trivial, this.2 h⟩⟩
  · subst h
    have pa1 : 0 < a1 := by linarith
    have pb1 := h1.1 pa1
    have zb2 : b2 = 0 := by
      rcases eq_or_lt_of_le hb2 with h | h
      · exact h.symm
      · exact absurd (h2.2 h) (lt_irrefl 0)
    subst zb2
    have := g69geo_tt a1 b1 pa1 pb1
    simp only [div_zero, add_zero]
    exact ⟨this.1, fun h => ⟨this.2 h, trivial⟩⟩

theorem g69geo_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ) (s : ℝ → Fin n → ℝ)
    (hcp : ∀ μ : ℝ, 0 < μ → IsCentralPathPoint A b c μ (x μ) (y μ) (s μ))
    (p q : (Fin n → ℝ) × (Fin n → ℝ))
    (hp : MapClusterPt p (𝓝[>] (0:ℝ)) (fun μ => (x μ, s μ)))
    (hq : MapClusterPt q (𝓝[>] (0:ℝ)) (fun μ => (x μ, s μ)))
    (yp yq : Fin m → ℝ) (hyp : Aᵀ *ᵥ yp + p.2 = c) (hyq : Aᵀ *ᵥ yq + q.2 = c)
    (hxp : A *ᵥ p.1 = b) (hxq : A *ᵥ q.1 = b)
    (hcpp : ∀ j, p.1 j * p.2 j = 0) (hcq : ∀ j, q.1 j * q.2 j = 0)
    (hpxn : ∀ j, 0 ≤ p.1 j) (hpsn : ∀ j, 0 ≤ p.2 j) (hqxn : ∀ j, 0 ≤ q.1 j) (hqsn : ∀ j, 0 ≤ q.2 j)
    (hppos : ∀ j, 0 < p.1 j + p.2 j)
    (h1 : ∀ j, 0 < p.1 j ↔ 0 < q.1 j) (h2 : ∀ j, 0 < p.2 j ↔ 0 < q.2 j) : p = q := by
  have z1 : ∀ j, q.1 j = 0 ∨ p.1 j ≠ 0 := fun j => by
    by_cases h : 0 < p.1 j
    · exact Or.inr h.ne'
    · left; have := hqxn j; rw [h1] at h; linarith
  have z2 : ∀ j, q.2 j = 0 ∨ p.2 j ≠ 0 := fun j => by
    by_cases h : 0 < p.2 j
    · exact Or.inr h.ne'
    · left; have := hqsn j; rw [h2] at h; linarith
  have z3 : ∀ j, p.1 j = 0 ∨ q.1 j ≠ 0 := fun j => by
    by_cases h : 0 < q.1 j
    · exact Or.inr h.ne'
    · left; have := hpxn j; rw [← h1] at h; linarith
  have z4 : ∀ j, p.2 j = 0 ∨ q.2 j ≠ 0 := fun j => by
    by_cases h : 0 < q.2 j
    · exact Or.inr h.ne'
    · left; have := hpsn j; rw [← h2] at h; linarith
  have E1 := g69geo_L A b c x y s hcp p hp q.1 yq q.2 hxq hyq hcq z1 z2
  have E2 := g69geo_L A b c x y s hcp q hq p.1 yp p.2 hxp hyp hcpp z3 z4
  have hz : ∑ j, ((q.1 j / p.1 j + q.2 j / p.2 j) + (p.1 j / q.1 j + p.2 j / q.2 j) - 2) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, E1, E2]; simp; ring
  have H := fun j => g69geo_pair (p.1 j) (p.2 j) (q.1 j) (q.2 j) (hpxn j) (hpsn j) (hqxn j)
    (hqsn j) (hcpp j) (hppos j) (h1 j) (h2 j)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (H j).1)] at hz
  exact Prod.ext (funext fun j => ((H j).2 (hz j (Finset.mem_univ j))).1)
    (funext fun j => ((H j).2 (hz j (Finset.mem_univ j))).2)

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hrank : A.rank = m) (hmn : m < n)
    (hP : ∃ x, PrimalInterior A b x) (hD : ∃ y s, DualInterior A c y s)
    (x : ℝ → Fin n → ℝ) (y : ℝ → Fin m → ℝ) (s : ℝ → Fin n → ℝ)
    (hcp : ∀ μ : ℝ, 0 < μ → IsCentralPathPoint A b c μ (x μ) (y μ) (s μ)) :
    ∃ (x₀ : Fin n → ℝ) (y₀ : Fin m → ℝ) (s₀ : Fin n → ℝ),
      Tendsto x (𝓝[>] 0) (𝓝 x₀) ∧ Tendsto s (𝓝[>] 0) (𝓝 s₀) ∧
      IsPrimalOptimal A b c x₀ ∧ IsDualOptimal A b c y₀ s₀ ∧
      IsPrimalFaceAnalyticCenter A b c x₀ ∧ IsDualFaceAnalyticCenter A b c s₀ := by
  obtain ⟨x0, hx0, hx0p⟩ := hP
  obtain ⟨y0, s0, hs0, hs0p⟩ := hD
  obtain ⟨R, hR, hB⟩ := g69c_xs_bound A b c x0 y0 s0 hx0 hx0p hs0 hs0p ((n : ℝ) * 1)
  have hK : IsCompact (Metric.closedBall (0 : (Fin n → ℝ) × (Fin n → ℝ)) R) :=
    isCompact_closedBall _ _
  have hmem : ∀ᶠ μ in 𝓝[>] (0:ℝ), (fun μ => (x μ, s μ)) μ ∈ Metric.closedBall 0 R := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with μ hμ
    obtain ⟨⟨hx, hxp⟩, ⟨hs, hsp⟩, hc⟩ := hcp μ hμ.1
    have hxs : x μ ⬝ᵥ s μ ≤ (n : ℝ) * 1 := by
      have : x μ ⬝ᵥ s μ = n * μ := by
        unfold dotProduct; simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      rw [this]; exact mul_le_mul_of_nonneg_left hμ.2.le (Nat.cast_nonneg n)
    have H := hB (x μ) (y μ) (s μ) hx (fun j => (hxp j).le) hs (fun j => (hsp j).le) hxs
    rw [Metric.mem_closedBall, dist_zero_right, norm_prod_le_iff]
    constructor
    · rw [pi_norm_le_iff_of_nonneg hR]; intro j; rw [Real.norm_eq_abs]; exact (H j).1
    · rw [pi_norm_le_iff_of_nonneg hR]; intro j; rw [Real.norm_eq_abs]; exact (H j).2
  obtain ⟨p, -, hp⟩ := hK.exists_mapClusterPt (tendsto_principal.2 hmem)
  have props : ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
      MapClusterPt q (𝓝[>] (0:ℝ)) (fun μ => (x μ, s μ)) →
      A *ᵥ q.1 = b ∧ (∀ j, 0 ≤ q.1 j) ∧ Aᵀ *ᵥ (((A * Aᵀ)⁻¹ * A) *ᵥ (c - q.2)) + q.2 = c ∧
      (∀ j, 0 ≤ q.2 j) ∧ (∀ j, q.1 j * q.2 j = 0) ∧ (∀ j, 0 < q.1 j + q.2 j) ∧
      (∀ j, j ∈ Pstar A b c ↔ 0 < q.1 j) ∧ (∀ j, j ∈ Zstar A b c ↔ 0 < q.2 j) := by
    intro q hq
    obtain ⟨h1, h2, h3, h4, h5⟩ := g69geo_basic A b c hrank x y s hcp q hq
    have h6 := g69geo_strict A b c hrank x y s hcp q hq
    obtain ⟨h7, h8⟩ := g69geo_char A b c q.1 _ q.2 ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := props p hp
  have huniq : ∀ q ∈ Metric.closedBall (0 : (Fin n → ℝ) × (Fin n → ℝ)) R,
      MapClusterPt q (𝓝[>] (0:ℝ)) (fun μ => (x μ, s μ)) → q = p := by
    intro q _ hq
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := props q hq
    exact g69geo_unique A b c x y s hcp q p hq hp _ _ k3 h3 k1 h1 k5 h5 k2 k4 h2 h4 k6
      (fun j => by rw [← k7, h7]) (fun j => by rw [← k8, h8])
  have hT := hK.tendsto_nhds_of_unique_mapClusterPt hmem huniq
  have hdot : p.1 ⬝ᵥ p.2 = 0 := by simp [dotProduct, h5]
  refine ⟨p.1, ((A * Aᵀ)⁻¹ * A) *ᵥ (c - p.2), p.2, (continuous_fst.tendsto p).comp hT,
    (continuous_snd.tendsto p).comp hT, ⟨⟨h1, h2⟩, fun x' hx' => ?_⟩, ⟨⟨h3, h4⟩, fun y' s' hd => ?_⟩,
    g69geo_cp A b c x y s hcp p hp _ h3 h1 h5 h2 h4 h6 h7 h8,
    g69geo_cd A b c x y s hcp p hp _ h3 h1 h5 h2 h4 h6 h7 h8⟩
  · have e1 := g69c_gap A b c p.1 _ p.2 h1 h3
    have e2 := g69c_gap A b c x' _ p.2 hx'.1 h3
    have := g69c_dot_nonneg x' p.2 hx'.2 h4
    linarith
  · have e1 := g69c_gap A b c p.1 _ p.2 h1 h3
    have e2 := g69c_gap A b c p.1 y' s' h1 hd.1
    have := g69c_dot_nonneg p.1 s' h2 hd.2
    linarith
