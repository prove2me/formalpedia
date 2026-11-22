-- Prove2me | solution 1 for ShiShallow.product_eigenbasis_sum_form_three
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-15T05:04:42.133194+00:00
-- url     : https://prove2.me/submissions/f52985f5-b2da-432e-af1d-b273dfcf7efd

/-
TCON-2D (assembly, step 4 of the spectral soundness bound): the THREE-FOLD PRODUCT FAMILY of an
orthonormal family on `Bits M` is orthonormal and Parseval on the left-nested three-block
register `Bits (M + M + M)`, both stated in EXPLICIT-SUM (Σ-) form.

This is the phrasing bridge of the tower: the platform's product-family theorems are stated in
`EuclideanSpace ℂ (Bits ·)` with `WithLp.toLp 2`, while the eigenbasis producer
(`ShiShallow.exists_sum_form_eigenbasis`) and the final bound
(`ShiShallow.quadratic_form_majority_le_of_eigenbasis`) are stated with plain `Bits w → ℂ` and
explicit `∑ … starRingEnd …` sums.  The translation is `PiLp.inner_apply` plus
`WithLp.ofLp_toLp` / `PiLp.toLp_apply`, exactly as in the accepted proof of
`exists_sum_form_eigenbasis`; no Parseval argument is redone here (the product family's Parseval
identity comes from the accepted card = finrank theorem).

Cited platform theorems (both Proved):
* `ShiShallow.product_family_orthonormal_three`
* `ShiShallow.product_family_parseval_three`

Built against Mathlib at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiTensor_Core
import Theorems.Thm_ShiShallow_product_family_orthonormal_three
import Theorems.Thm_ShiShallow_product_family_parseval_three

set_option autoImplicit false

open ShiShallow ShiTensor

/-- The `EuclideanSpace` inner product as an explicit sum, conjugate on the FIRST argument. -/
private lemma shiSnd_inner_as_sum {w : ℕ} (x y : EuclideanSpace ℂ (Bits w)) :
    inner ℂ x y = ∑ t : Bits w, (starRingEnd ℂ) (WithLp.ofLp x t) * WithLp.ofLp y t := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro t _
  first
    | (rw [RCLike.inner_apply]; exact mul_comm _ _; done)
    | (rw [RCLike.inner_apply']; done)
    | (simp only [RCLike.inner_apply]; exact mul_comm _ _; done)

/-- **The three-fold product family is orthonormal and Parseval, in Σ-form.** -/
theorem solution {M : ℕ} (u : Bits M → (Bits M → ℂ))
    (horth : ∀ i j, (∑ y : Bits M, (starRingEnd ℂ) (u i y) * u j y) = if i = j then 1 else 0) :
    (∀ i j : (Bits M × Bits M) × Bits M,
        (∑ y : Bits (M + M + M),
            (starRingEnd ℂ) (tensor (tensor (u i.1.1) (u i.1.2)) (u i.2) y)
              * tensor (tensor (u j.1.1) (u j.1.2)) (u j.2) y)
          = if i = j then 1 else 0)
      ∧ (∀ z : Bits (M + M + M) → ℂ,
        (∑ i : (Bits M × Bits M) × Bits M,
            ‖∑ y : Bits (M + M + M), (starRingEnd ℂ) (z y)
              * tensor (tensor (u i.1.1) (u i.1.2)) (u i.2) y‖ ^ 2)
          = ∑ y : Bits (M + M + M), ‖z y‖ ^ 2) := by
  classical
  -- the single-copy family, transported into `EuclideanSpace`
  obtain ⟨U, hU⟩ : ∃ U : Bits M → EuclideanSpace ℂ (Bits M),
      U = fun i => WithLp.toLp 2 (u i) := ⟨_, rfl⟩
  have hUo : Orthonormal ℂ U := by
    refine orthonormal_iff_ite.mpr ?_
    intro i j
    rw [shiSnd_inner_as_sum]
    rw [hU]
    simp only [WithLp.ofLp_toLp]
    exact horth i j
  -- the product family, transported into `EuclideanSpace`
  obtain ⟨V, hV⟩ : ∃ V : (Bits M × Bits M) × Bits M → EuclideanSpace ℂ (Bits (M + M + M)),
      V = fun i => WithLp.toLp 2 (tensor (tensor (u i.1.1) (u i.1.2)) (u i.2)) := ⟨_, rfl⟩
  have hVo : Orthonormal ℂ V := by
    have h := product_family_orthonormal_three U U U hUo hUo hUo
    have hfam : (fun i : (Bits M × Bits M) × Bits M =>
        (WithLp.toLp 2 (fun y : Bits (M + M + M) =>
            U i.1.1 (leftBits (leftBits y)) * U i.1.2 (rightBits (leftBits y))
              * U i.2 (rightBits y)) : EuclideanSpace ℂ (Bits (M + M + M)))) = V := by
      rw [hV, hU]
      funext i
      congr 1
      -- `congr 1` can discharge this outright; `all_goals` is a no-op on zero goals,
      -- so neither the `funext` nor the ladder below may be unconditional.
      all_goals funext y
      all_goals first
        | rfl
        | (simp only [PiLp.toLp_apply, tensor]; done)
        | (simp only [PiLp.toLp_apply, tensor]; ring; done)
        | (simp [PiLp.toLp_apply, tensor]; ring; done)
    rw [← hfam]
    exact h
  refine ⟨?_, ?_⟩
  · -- orthonormality, back in Σ-form
    intro i j
    have h := orthonormal_iff_ite.mp hVo i j
    rw [shiSnd_inner_as_sum, hV] at h
    simp only [WithLp.ofLp_toLp] at h
    exact h
  · -- Parseval, back in Σ-form
    intro z
    have h := product_family_parseval_three V hVo (WithLp.toLp 2 z)
    rw [EuclideanSpace.norm_sq_eq] at h
    simp only [shiSnd_inner_as_sum, hV, WithLp.ofLp_toLp, PiLp.toLp_apply] at h
    exact h
