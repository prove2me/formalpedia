-- Prove2me | solution 1 for RobustLS.Structured.s_procedure_lossless
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:20:08.085619+00:00
-- url     : https://prove2.me/submissions/fb16a8df-62c1-4cdc-a584-48e62b2ea765

import Mathlib
import Definitions.Def_RobustLS_Structured_Core

open Matrix

namespace RobustLS.Structured

lemma aux_slp_expand {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x y : ι → ℝ) (a b : ℝ) :
    (a • x + b • y) ⬝ᵥ (A *ᵥ (a • x + b • y)) =
      a ^ 2 * (x ⬝ᵥ (A *ᵥ x)) + a * b * (x ⬝ᵥ (A *ᵥ y) + y ⬝ᵥ (A *ᵥ x))
        + b ^ 2 * (y ⬝ᵥ (A *ᵥ y)) := by
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

lemma aux_slp_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) (τ : ℝ) (x : ι → ℝ) :
    x ⬝ᵥ ((A - τ • B) *ᵥ x) = x ⬝ᵥ (A *ᵥ x) - τ * (x ⬝ᵥ (B *ᵥ x)) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma aux_slp_key {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) (τ : ℝ)
    (himp0 : ∀ z : ι → ℝ, z ⬝ᵥ (B *ᵥ z) = 0 → 0 ≤ z ⬝ᵥ (A *ᵥ z))
    (p n : ι → ℝ) (hp : 0 < p ⬝ᵥ (B *ᵥ p)) (hn : n ⬝ᵥ (B *ᵥ n) < 0)
    (hpM : p ⬝ᵥ ((A - τ • B) *ᵥ p) < 0) (hnM : n ⬝ᵥ ((A - τ • B) *ᵥ n) < 0) : False := by
  set M := A - τ • B with hM
  set c := p ⬝ᵥ (M *ᵥ n) + n ⬝ᵥ (M *ᵥ p) with hc
  obtain ⟨σ, hσ2, hσc⟩ : ∃ σ : ℝ, σ ^ 2 = 1 ∧ σ * c ≤ 0 := by
    rcases le_total c 0 with h | h
    · exact ⟨1, by norm_num, by linarith⟩
    · exact ⟨-1, by norm_num, by linarith⟩
  have hsq : ∀ (C : Matrix ι ι ℝ), (σ • n) ⬝ᵥ (C *ᵥ (σ • n)) = n ⬝ᵥ (C *ᵥ n) := by
    intro C
    have := aux_slp_expand C n n 0 σ
    simp only [zero_smul, zero_add] at this
    rw [this, hσ2]; ring
  have hcross : p ⬝ᵥ (M *ᵥ (σ • n)) + (σ • n) ⬝ᵥ (M *ᵥ p) = σ * c := by
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, hc]; ring
  set f : ℝ → ℝ := fun t => ((1 - t) • p + t • (σ • n)) ⬝ᵥ (B *ᵥ ((1 - t) • p + t • (σ • n)))
    with hf
  have hf' : f = fun t => (1 - t) ^ 2 * (p ⬝ᵥ (B *ᵥ p)) + (1 - t) * t *
      (p ⬝ᵥ (B *ᵥ (σ • n)) + (σ • n) ⬝ᵥ (B *ᵥ p)) + t ^ 2 * (n ⬝ᵥ (B *ᵥ n)) := by
    funext t
    rw [hf]
    simp only
    rw [aux_slp_expand, hsq]
  have hcont : Continuous f := by rw [hf']; fun_prop
  have h01 : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := by
    rw [hf']; simp only; constructor <;> nlinarith
  obtain ⟨t, ⟨ht0, ht1⟩, hft⟩ := intermediate_value_Icc' zero_le_one hcont.continuousOn h01
  set z := (1 - t) • p + t • (σ • n) with hz
  have hBz : z ⬝ᵥ (B *ᵥ z) = 0 := hft
  have hAz := himp0 z hBz
  have hMz : z ⬝ᵥ (M *ᵥ z) = z ⬝ᵥ (A *ᵥ z) := by
    rw [hM, aux_slp_sub, hBz, mul_zero, sub_zero]
  have hMz' : z ⬝ᵥ (M *ᵥ z) = (1 - t) ^ 2 * (p ⬝ᵥ (M *ᵥ p)) + (1 - t) * t * (σ * c)
      + t ^ 2 * (n ⬝ᵥ (M *ᵥ n)) := by
    rw [hz, aux_slp_expand, hcross, hsq]
  have hneg : z ⬝ᵥ (M *ᵥ z) < 0 := by
    rw [hMz']
    have h1 : 0 ≤ (1 - t) * t := mul_nonneg (by linarith) ht0
    have h2 : (1 - t) * t * (σ * c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 hσc
    rcases eq_or_lt_of_le ht0 with h | h
    · subst h; nlinarith
    · have : 0 < t ^ 2 := by positivity
      nlinarith [sq_nonneg (1 - t)]
  linarith

lemma aux_slp_hom {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ)
    (hsl : ∃ x : ι → ℝ, 0 < x ⬝ᵥ (B *ᵥ x))
    (himp : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (B *ᵥ x) → 0 ≤ x ⬝ᵥ (A *ᵥ x)) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ ((A - τ • B) *ᵥ x) := by
  obtain ⟨x0, hx0⟩ := hsl
  set S : Set ℝ := {r | ∃ x : ι → ℝ, 0 < x ⬝ᵥ (B *ᵥ x) ∧ r = x ⬝ᵥ (A *ᵥ x) / x ⬝ᵥ (B *ᵥ x)}
    with hS
  have hne : S.Nonempty := ⟨_, x0, hx0, rfl⟩
  have hlb : ∀ r ∈ S, 0 ≤ r := by
    rintro r ⟨x, hx, rfl⟩
    exact div_nonneg (himp x hx.le) hx.le
  have hbdd : BddBelow S := ⟨0, hlb⟩
  refine ⟨sInf S, le_csInf hne hlb, ?_⟩
  intro x
  rw [aux_slp_sub]
  set R := sInf S with hR
  rcases lt_trichotomy (x ⬝ᵥ (B *ᵥ x)) 0 with hb | hb | hb
  · by_contra hcon
    rw [not_le] at hcon
    set d := -(x ⬝ᵥ (A *ᵥ x) - R * x ⬝ᵥ (B *ᵥ x)) with hd
    have hdpos : 0 < d := by linarith
    set ε := d / (2 * -(x ⬝ᵥ (B *ᵥ x))) with hε
    have hεpos : 0 < ε := div_pos hdpos (by linarith)
    have hεb : ε * (x ⬝ᵥ (B *ᵥ x)) = -(d / 2) := by
      have hbne : x ⬝ᵥ (B *ᵥ x) ≠ 0 := hb.ne
      rw [hε]; field_simp
    obtain ⟨r, ⟨y, hy, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hne (show R < R + ε by linarith)
    have hpy : y ⬝ᵥ (A *ᵥ y) - (R + ε) * y ⬝ᵥ (B *ᵥ y) < 0 := by
      rw [div_lt_iff₀ hy] at hr; linarith
    refine aux_slp_key A B (R + ε) (fun z hz => himp z hz.ge) y x hy hb ?_ ?_
    · rw [aux_slp_sub]; exact hpy
    · rw [aux_slp_sub]; nlinarith
  · rw [hb, mul_zero, sub_zero]; exact himp x hb.ge
  · have := csInf_le hbdd ⟨x, hb, rfl⟩
    rw [le_div_iff₀ hb] at this; linarith

lemma aux_slp_block {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) (v : ℝ)
    (x : Fin m ⊕ Unit → ℝ) :
    x ⬝ᵥ (quadBlockMat T u v *ᵥ x) =
      (fun i => x (Sum.inl i)) ⬝ᵥ (T *ᵥ fun i => x (Sum.inl i))
        + 2 * x (Sum.inr ()) * (u ⬝ᵥ fun i => x (Sum.inl i)) + x (Sum.inr ()) ^ 2 * v := by
  simp only [quadBlockMat, dotProduct, mulVec, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Finset.univ_unique,
    Finset.sum_singleton, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [PUnit.default_eq_unit]
  have e : ∀ i, x (Sum.inl i) * (u i * x (Sum.inr ())) = x (Sum.inr ()) * u i * x (Sum.inl i) :=
    fun i => by ring
  have e' : ∀ i, x (Sum.inr ()) * (u i * x (Sum.inl i)) = x (Sum.inr ()) * u i * x (Sum.inl i) :=
    fun i => by ring
  simp only [e, e']
  ring_nf
  rw [Finset.sum_mul]

lemma aux_slp_scale {m : ℕ} (T : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) (v : ℝ)
    (ζ : Fin m → ℝ) (t : ℝ) (ht : t ≠ 0) :
    t ^ 2 * quadFn T u v (t⁻¹ • ζ) = ζ ⬝ᵥ (T *ᵥ ζ) + 2 * t * (u ⬝ᵥ ζ) + t ^ 2 * v := by
  simp only [quadFn, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  field_simp

lemma aux_slp_herm {m : ℕ} (T0 : Matrix (Fin m) (Fin m) ℝ) (u0 : Fin m → ℝ)
    (v0 : ℝ) (T1 : Matrix (Fin m) (Fin m) ℝ) (u1 : Fin m → ℝ) (v1 : ℝ)
    (hT0 : T0ᵀ = T0) (hT1 : T1ᵀ = T1) (τ : ℝ) :
    (quadBlockMat T0 u0 v0 - τ • quadBlockMat T1 u1 v1).IsHermitian := by
  have hT0' : ∀ i j, T0 j i = T0 i j := fun i j => by
    simpa using congrFun (congrFun hT0 i) j
  have hT1' : ∀ i j, T1 j i = T1 i j := fun i j => by
    simpa using congrFun (congrFun hT1 i) j
  ext i j
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
    simp [quadBlockMat, conjTranspose_apply, hT0', hT1']


end RobustLS.Structured

open Matrix
open RobustLS.Structured

theorem solution {m : ℕ} (T0 : Matrix (Fin m) (Fin m) ℝ) (u0 : Fin m → ℝ)
    (v0 : ℝ) (T1 : Matrix (Fin m) (Fin m) ℝ) (u1 : Fin m → ℝ) (v1 : ℝ)
    (hT0 : T0ᵀ = T0) (hT1 : T1ᵀ = T1)
    (hslater : ∃ ζ0 : Fin m → ℝ, 0 < quadFn T1 u1 v1 ζ0)
    (himp : ∀ ζ : Fin m → ℝ, 0 ≤ quadFn T1 u1 v1 ζ → 0 ≤ quadFn T0 u0 v0 ζ) :
    ∃ τ1 : ℝ, 0 ≤ τ1 ∧ (quadBlockMat T0 u0 v0 - τ1 • quadBlockMat T1 u1 v1).PosSemidef := by
  set M0 := quadBlockMat T0 u0 v0 with hM0
  set M1 := quadBlockMat T1 u1 v1 with hM1
  -- Step A: the homogeneous implication off the hyperplane `t = 0`
  have hA : ∀ x : Fin m ⊕ Unit → ℝ, x (Sum.inr ()) ≠ 0 →
      0 ≤ x ⬝ᵥ (M1 *ᵥ x) → 0 ≤ x ⬝ᵥ (M0 *ᵥ x) := by
    intro x hx h1
    have e0 := aux_slp_block T0 u0 v0 x
    have e1 := aux_slp_block T1 u1 v1 x
    have s0 := aux_slp_scale T0 u0 v0 (fun i => x (Sum.inl i)) _ hx
    have s1 := aux_slp_scale T1 u1 v1 (fun i => x (Sum.inl i)) _ hx
    have ht2 : 0 < x (Sum.inr ()) ^ 2 := by positivity
    have hF1 : 0 ≤ quadFn T1 u1 v1 ((x (Sum.inr ()))⁻¹ • fun i => x (Sum.inl i)) := by
      have h : 0 ≤ x (Sum.inr ()) ^ 2 *
          quadFn T1 u1 v1 ((x (Sum.inr ()))⁻¹ • fun i => x (Sum.inl i)) := by
        rw [s1, ← e1]; exact h1
      exact nonneg_of_mul_nonneg_right h ht2
    have hF0 := himp _ hF1
    rw [e0, ← s0]; positivity
  -- the homogenized Slater point
  obtain ⟨ζ0, hζ0⟩ := hslater
  set xh : Fin m ⊕ Unit → ℝ := Sum.elim ζ0 (fun _ => 1) with hxh_def
  have hxh : ∀ (T : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) (v : ℝ),
      xh ⬝ᵥ (quadBlockMat T u v *ᵥ xh) = quadFn T u v ζ0 := by
    intro T u v
    rw [aux_slp_block]
    simp [xh, quadFn]
  -- Step B: the full homogeneous implication
  have hB : ∀ z : Fin m ⊕ Unit → ℝ, 0 ≤ z ⬝ᵥ (M1 *ᵥ z) → 0 ≤ z ⬝ᵥ (M0 *ᵥ z) := by
    intro z hz
    set c1 := z ⬝ᵥ (M1 *ᵥ xh) + xh ⬝ᵥ (M1 *ᵥ z) with hc1
    obtain ⟨σ, hσ2, hσc⟩ : ∃ σ : ℝ, σ ^ 2 = 1 ∧ 0 ≤ σ * c1 := by
      rcases le_total c1 0 with h | h
      · exact ⟨-1, by norm_num, by linarith⟩
      · exact ⟨1, by norm_num, by linarith⟩
    have hσne : σ ≠ 0 := by rintro rfl; norm_num at hσ2
    obtain ⟨δ, hδ, hδp⟩ : ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → z (Sum.inr ()) + ε * σ ≠ 0 := by
      by_cases hz0 : z (Sum.inr ()) = 0
      · refine ⟨1, one_pos, fun ε hε _ => ?_⟩
        rw [hz0, zero_add]; exact mul_ne_zero hε.ne' hσne
      · refine ⟨|z (Sum.inr ())|, abs_pos.2 hz0, fun ε hε hεδ h => ?_⟩
        have h' : z (Sum.inr ()) ^ 2 = ε ^ 2 := by
          have : z (Sum.inr ()) = -(ε * σ) := by linarith
          rw [this, neg_sq, mul_pow, hσ2, mul_one]
        have : |z (Sum.inr ())| = ε := by
          rw [← abs_of_pos hε]; exact sq_eq_sq_iff_abs_eq_abs _ _ |>.1 h'
        linarith
    set g : ℝ → ℝ := fun ε => (1 : ℝ) ^ 2 * (z ⬝ᵥ (M0 *ᵥ z))
      + 1 * (ε * σ) * (z ⬝ᵥ (M0 *ᵥ xh) + xh ⬝ᵥ (M0 *ᵥ z))
      + (ε * σ) ^ 2 * (xh ⬝ᵥ (M0 *ᵥ xh)) with hg
    have hgc : Continuous g := by rw [hg]; fun_prop
    have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ g ε := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      have hw := hA (z + (ε * σ) • xh) ?_ ?_
      · have := aux_slp_expand M0 z xh 1 (ε * σ)
        rw [one_smul] at this
        rw [this] at hw
        exact hw
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, xh, Sum.elim_inr, mul_one]
        exact hδp ε hε.1 hε.2
      · have := aux_slp_expand M1 z xh 1 (ε * σ)
        rw [one_smul] at this
        rw [this]
        have h3 : 0 ≤ (ε * σ) ^ 2 * (xh ⬝ᵥ (M1 *ᵥ xh)) := by
          rw [hM1, hxh]; positivity
        have h4 : 0 ≤ ε * (σ * c1) := mul_nonneg hε.1.le hσc
        nlinarith
    have ht : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (g 0)) :=
      (hgc.tendsto 0).mono_left nhdsWithin_le_nhds
    have := ge_of_tendsto ht hev
    simpa [g] using this
  obtain ⟨τ, hτ, hpos⟩ := aux_slp_hom M0 M1 ⟨xh, by rw [hM1, hxh]; exact hζ0⟩ hB
  refine ⟨τ, hτ, ?_⟩
  refine PosSemidef.of_dotProduct_mulVec_nonneg (aux_slp_herm T0 u0 v0 T1 u1 v1 hT0 hT1 τ) ?_
  intro x
  simpa using hpos x
