-- Prove2me | solution 1 for RelaxedPRS.Linear.lemma_1_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:07:11.076779+00:00
-- url     : https://prove2.me/submissions/05c9efab-f383-4246-9b37-0f8d70146e9c

import Mathlib
import Definitions.Def_RelaxedPRS_Linear_Setting

set_option autoImplicit false
open scoped InnerProductSpace
open ThreeOpSplitting.ConvexRates MoreauProx.Characterization RelaxedPRS.StrongCvx

theorem rpl_limit_aux (a b c e : ℝ) (he : 0 ≤ e)
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → a ≤ b + c + s * e) : a ≤ b + c := by
  by_contra hcon
  push_neg at hcon
  set δ := a - b - c with hδ
  have hδpos : 0 < δ := by linarith
  have hpos : 0 < δ / (2 * (e + 1)) := by positivity
  set s := min 1 (δ / (2 * (e + 1))) with hs
  have hs0 : 0 < s := lt_min one_pos hpos
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs2 : s ≤ δ / (2 * (e + 1)) := min_le_right _ _
  have := h s hs0 hs1
  have h3 : s * e ≤ δ / (2 * (e + 1)) * e := mul_le_mul_of_nonneg_right hs2 he
  have h4 : δ / (2 * (e + 1)) * e ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

theorem rpl_prox_subgrad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : IsProperClosedConvex f) (γ : ℝ) (hγ : 0 < γ) (P : H → H)
    (hP : IsProx γ f P) (z : H) : γ⁻¹ • (z - P z) ∈ subgrad f (P z) := by
  obtain ⟨hbot, ⟨y0, hy0⟩, -, hconv⟩ := hf
  set p := P z with hp
  have hpbot := hbot p
  have hptop : f p ≠ ⊤ := by
    intro h
    have h1 := hP z y0
    rw [← hp, h] at h1
    obtain ⟨r, hr⟩ : ∃ r : ℝ, f y0 = r := ⟨(f y0).toReal, (EReal.coe_toReal hy0 (hbot y0)).symm⟩
    rw [hr, ← EReal.coe_add, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _), top_le_iff] at h1
    exact EReal.coe_ne_top _ h1
  refine ⟨hpbot, hptop, fun u => ?_⟩
  by_cases hu : f u = ⊤
  · rw [hu]; exact le_top
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f p = a := ⟨(f p).toReal, (EReal.coe_toReal hptop hpbot).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, f u = b := ⟨(f u).toReal, (EReal.coe_toReal hu (hbot u)).symm⟩
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      a ≤ b + γ⁻¹ * ⟪p - z, u - p⟫_ℝ + s * (‖u - p‖ ^ 2 / (2 * γ)) := by
    intro s hs0 hs1
    have hmem : ((1 - s) • p + s • u, (1 - s) * a + s * b) ∈
        {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} := by
      have := hconv (show (p, a) ∈ {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} by
          simp only [Set.mem_setOf_eq]; rw [ha])
        (show (u, b) ∈ {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} by
          simp only [Set.mem_setOf_eq]; rw [hb]) (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
      simpa using this
    simp only [Set.mem_setOf_eq] at hmem
    have h1 := hP z ((1 - s) • p + s • u)
    rw [← hp, ha] at h1
    have h2 : f ((1 - s) • p + s • u) + (((‖(1 - s) • p + s • u - z‖ ^ 2 / (2 * γ) : ℝ)) : EReal) ≤
        (((1 - s) * a + s * b : ℝ) : EReal) + (((‖(1 - s) • p + s • u - z‖ ^ 2 / (2 * γ) : ℝ)) : EReal) :=
      add_le_add hmem le_rfl
    have h3 := h1.trans h2
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h3
    have hy : (1 - s) • p + s • u - z = (p - z) + s • (u - p) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [hy] at h3
    have hn : ‖(p - z) + s • (u - p)‖ ^ 2 =
        ‖p - z‖ ^ 2 + 2 * s * ⟪p - z, u - p⟫_ℝ + s ^ 2 * ‖u - p‖ ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg hs0.le]
      ring
    rw [hn] at h3
    -- h3 : a + ‖p-z‖^2/(2γ) ≤ (1-s) a + s b + (…)/(2γ)
    have h4 : s * a ≤ s * (b + γ⁻¹ * ⟪p - z, u - p⟫_ℝ + s * (‖u - p‖ ^ 2 / (2 * γ))) := by
      have e1 : (‖p - z‖ ^ 2 + 2 * s * ⟪p - z, u - p⟫_ℝ + s ^ 2 * ‖u - p‖ ^ 2) / (2 * γ) =
          ‖p - z‖ ^ 2 / (2 * γ) + s * (γ⁻¹ * ⟪p - z, u - p⟫_ℝ) +
            s ^ 2 * (‖u - p‖ ^ 2 / (2 * γ)) := by
        field_simp
      rw [e1] at h3
      nlinarith
    exact le_of_mul_le_mul_left h4 hs0
  have := rpl_limit_aux a b (γ⁻¹ * ⟪p - z, u - p⟫_ℝ) (‖u - p‖ ^ 2 / (2 * γ)) (by positivity) key
  have e3 : ⟪u - p, γ⁻¹ • (z - p)⟫_ℝ = -(γ⁻¹ * ⟪p - z, u - p⟫_ℝ) := by
    rw [inner_smul_right]
    have : ⟪p - z, u - p⟫_ℝ = -⟪z - p, u - p⟫_ℝ := by rw [← inner_neg_left, neg_sub]
    rw [this, real_inner_comm]
    ring
  show a + ⟪u - p, γ⁻¹ • (z - P z)⟫_ℝ ≤ b
  rw [← hp, e3]
  linarith

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg) (t : ℝ) (ht : 0 < t) (z : H) :
    RelaxedPRS.StrongCvx.gtG γ Pg z ∈ MoreauProx.Characterization.subgrad g (RelaxedPRS.StrongCvx.xg Pg z) ∧
    RelaxedPRS.StrongCvx.gtF γ Pf Pg z ∈ MoreauProx.Characterization.subgrad f (RelaxedPRS.StrongCvx.xf Pf Pg z) ∧
    RelaxedPRS.StrongCvx.xg Pg z = z - γ • RelaxedPRS.StrongCvx.gtG γ Pg z ∧
    RelaxedPRS.StrongCvx.xf Pf Pg z = RelaxedPRS.StrongCvx.xg Pg z - γ • RelaxedPRS.StrongCvx.gtG γ Pg z - γ • RelaxedPRS.StrongCvx.gtF γ Pf Pg z ∧
    RelaxedPRS.StrongCvx.Tlam Pf Pg t z - z = (2 * t) • (RelaxedPRS.StrongCvx.xf Pf Pg z - RelaxedPRS.StrongCvx.xg Pg z) ∧
    RelaxedPRS.StrongCvx.Tlam Pf Pg t z - z = -(2 * t * γ) • (RelaxedPRS.StrongCvx.gtG γ Pg z + RelaxedPRS.StrongCvx.gtF γ Pf Pg z) := by
  have hγ' : γ ≠ 0 := hγ.ne'
  have e1 : γ • (γ⁻¹ • (z - Pg z)) = z - Pg z := by rw [smul_smul, mul_inv_cancel₀ hγ', one_smul]
  have e2 : γ • (γ⁻¹ • (RelaxedPRS.StrongCvx.refl Pg z - Pf (RelaxedPRS.StrongCvx.refl Pg z))) = RelaxedPRS.StrongCvx.refl Pg z - Pf (RelaxedPRS.StrongCvx.refl Pg z) := by
    rw [smul_smul, mul_inv_cancel₀ hγ', one_smul]
  refine ⟨rpl_prox_subgrad g hg γ hγ Pg hPg z, rpl_prox_subgrad f hf γ hγ Pf hPf (RelaxedPRS.StrongCvx.refl Pg z), ?_, ?_, ?_, ?_⟩
  · simp only [gtG, xg, e1]; abel
  · simp only [gtG, gtF, xg, xf, RelaxedPRS.StrongCvx.refl]
    match_scalars <;> field_simp <;> ring
  · simp only [Tlam, TPRS, xf, xg, RelaxedPRS.StrongCvx.refl]; module
  · simp only [Tlam, TPRS, gtG, gtF, xf, xg, RelaxedPRS.StrongCvx.refl]
    match_scalars <;> field_simp <;> ring
