-- Prove2me | solution 1 for QuadMatIneq.Stabilization.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T18:16:46.383977+00:00
-- url     : https://prove2.me/submissions/f62231e0-2cb8-435f-b350-c9a99c3bc626

import Definitions.Def_QuadMatIneq_Stabilization_QMI
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

private lemma quadratic_comparison (a b c A B C : ℝ) (ha : a < 0) (hc : 0 < c)
    (h : ∀ t : ℝ, a + b * t + c * t ^ 2 = 0 → 0 ≤ A + B * t + C * t ^ 2) :
    0 ≤ A * c - C * a := by
  let d := Real.sqrt (b ^ 2 - 4 * c * a)
  have hd0 : 0 ≤ b ^ 2 - 4 * c * a := by nlinarith [mul_neg_of_pos_of_neg hc ha, sq_nonneg b]
  have hd : d ^ 2 = b ^ 2 - 4 * c * a := Real.sq_sqrt hd0
  have hdpos : 0 ≤ d := Real.sqrt_nonneg _
  have hdb : b < d := by nlinarith [mul_neg_of_pos_of_neg hc ha]
  have hdnb : -b < d := by nlinarith [mul_neg_of_pos_of_neg hc ha]
  let r := (-b + d) / (2 * c)
  let s := (-b - d) / (2 * c)
  have hr : 0 < r := div_pos (by linarith) (by linarith)
  have hs : s < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hdisc : discrim c b a = d * d := by dsimp [discrim]; nlinarith [hd]
  have hr0 : a + b * r + c * r ^ 2 = 0 := by
    have he := (quadratic_eq_zero_iff (ne_of_gt hc) hdisc r).mpr (Or.inl rfl)
    nlinarith
  have hs0 : a + b * s + c * s ^ 2 = 0 := by
    have he := (quadratic_eq_zero_iff (ne_of_gt hc) hdisc s).mpr (Or.inr rfl)
    nlinarith
  have hprod : c * r * s = a := by
    dsimp [r, s]
    field_simp
    nlinarith [hd]
  have hp := h r hr0
  have hq := h s hs0
  have hw : 0 ≤ r * (A + B * s + C * s ^ 2) - s * (A + B * r + C * r ^ 2) := by
    exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hs.le hp).trans
      (mul_nonneg hr.le hq))
  have he : c * (r * (A + B * s + C * s ^ 2) - s * (A + B * r + C * r ^ 2)) =
      (r - s) * (A * c - C * a) := by
    rw [← hprod]
    ring
  have hz := mul_nonneg hc.le hw
  rw [he] at hz
  exact nonneg_of_mul_nonneg_right hz (by linarith)

private def quad {k : Type*} [Fintype k] (X : Matrix k k ℝ) (x : k → ℝ) : ℝ :=
  x ⬝ᵥ (X *ᵥ x)

private lemma quad_expand {k : Type*} [Fintype k] (X : Matrix k k ℝ)
    (x y : k → ℝ) (t : ℝ) :
    quad X (x + t • y) = quad X x + (x ⬝ᵥ (X *ᵥ y) + y ⬝ᵥ (X *ᵥ x)) * t +
      quad X y * t ^ 2 := by
  simp only [quad, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

private lemma ratio_comparison {k : Type*} [Fintype k] (M N : Matrix k k ℝ)
    (h : ∀ x, 0 ≤ quad N x → 0 ≤ quad M x) (x y : k → ℝ)
    (hx : quad N x < 0) (hy : 0 < quad N y) :
    quad M x / quad N x ≤ quad M y / quad N y := by
  have he : 0 ≤ quad M x * quad N y - quad M y * quad N x := by
    apply quadratic_comparison (quad N x)
      (x ⬝ᵥ (N *ᵥ y) + y ⬝ᵥ (N *ᵥ x)) (quad N y)
      (quad M x) (x ⬝ᵥ (M *ᵥ y) + y ⬝ᵥ (M *ᵥ x)) (quad M y) hx hy
    intro t ht
    rw [← quad_expand] at ht
    have hp := h (x + t • y) ht.ge
    simpa only [quad_expand] using hp
  apply (le_div_iff₀ hy).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff_of_neg hx).mpr
  nlinarith

private lemma quad_sub_smul {k : Type*} [Fintype k] (M N : Matrix k k ℝ)
    (a : ℝ) (x : k → ℝ) : quad (M - a • N) x = quad M x - a * quad N x := by
  simp only [quad, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]

theorem solution {k : Type*} [Fintype k] [DecidableEq k]
    (M N : Matrix k k ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian)
    (hpos : ∃ i, 0 < hN.eigenvalues i) :
    (∀ x : k → ℝ, 0 ≤ x ⬝ᵥ (N *ᵥ x) → 0 ≤ x ⬝ᵥ (M *ᵥ x)) ↔
      ∃ a : ℝ, 0 ≤ a ∧ (M - a • N).PosSemidef := by
  constructor
  · intro h
    change ∀ x, 0 ≤ quad N x → 0 ≤ quad M x at h
    obtain ⟨i, hi⟩ := hpos
    have hv : 0 < quad N (hN.eigenvectorBasis i) := by
      simpa only [hN.eigenvalues_eq, RCLike.re_to_real, Pi.star_apply, star_trivial, quad]
        using hi
    let ratios : Set ℝ := {r | ∃ x : k → ℝ, 0 < quad N x ∧ r = quad M x / quad N x}
    have hn : ratios.Nonempty := ⟨_, ⟨hN.eigenvectorBasis i, hv, rfl⟩⟩
    have hlow : ∀ r ∈ ratios, 0 ≤ r := by
      rintro r ⟨x, hx, rfl⟩
      exact div_nonneg (h x hx.le) hx.le
    have hb : BddBelow ratios := ⟨0, hlow⟩
    let a := sInf ratios
    have ha : 0 ≤ a := le_csInf hn hlow
    refine ⟨a, ha, PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_⟩
    · change (M - a • N)ᴴ = M - a • N
      simp only [conjTranspose_sub, conjTranspose_smul, star_trivial, hM.eq, hN.eq]
    · intro x
      change 0 ≤ quad (M - a • N) x
      rw [quad_sub_smul]
      obtain hx | hx | hx := lt_trichotomy (quad N x) 0
      · have hr : quad M x / quad N x ≤ a := by
          apply le_csInf hn
          rintro r ⟨y, hy, rfl⟩
          exact ratio_comparison M N h x y hx hy
        have he := (div_le_iff_of_neg hx).mp hr
        nlinarith
      · simpa only [hx, mul_zero, sub_zero] using h x hx.ge
      · have hr : a ≤ quad M x / quad N x := csInf_le hb ⟨x, hx, rfl⟩
        have he := (le_div_iff₀ hx).mp hr
        nlinarith
  · rintro ⟨a, ha, hp⟩ x hx
    have he := hp.dotProduct_mulVec_nonneg x
    change 0 ≤ quad (M - a • N) x at he
    rw [quad_sub_smul] at he
    change 0 ≤ quad N x at hx
    change 0 ≤ quad M x
    exact (mul_nonneg ha hx).trans (sub_nonneg.mp he)
