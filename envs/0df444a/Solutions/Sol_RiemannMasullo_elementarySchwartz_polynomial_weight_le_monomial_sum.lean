-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartz_polynomial_weight_le_monomial_sum
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:29:39.089246+00:00
-- url     : https://prove2.me/submissions/70a0b4a8-b62e-4bd7-960b-3857dd148397

-- New supporting theorem for the polynomial generating family in Masullo Appendix D.
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
import Mathlib
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal

theorem solution (p : MvPolynomial (Fin m ⊕ Fin r) ℂ) (f : ElementarySchwartz m n r F)
    (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    ‖MvPolynomial.eval (Sum.elim (fun k => (xt.1 k : ℂ)) (fun k => (a k : ℂ))) p‖ *
      ‖elementaryPartial f β γ xt a b‖ ≤
    ∑ d ∈ p.support, ‖p.coeff d‖ * elementarySchwartzSeminorm
      (fun k => d (Sum.inl k), β, γ, fun k => d (Sum.inr k)) f := by
  classical
  let e := Sum.elim (fun k => (xt.1 k : ℂ)) (fun k => (a k : ℂ))
  let h := elementaryPartial f β γ xt a b
  let idx (d : (Fin m ⊕ Fin r) →₀ ℕ) : ElementarySchwartzIndex m n r :=
    (fun k => d (Sum.inl k), β, γ, fun k => d (Sum.inr k))
  let weight (d : (Fin m ⊕ Fin r) →₀ ℕ) :=
    (∏ k, (xt.1 k:ℂ)^d (Sum.inl k)) * ∏ k, (a k:ℂ)^d (Sum.inr k)
  have hbound (d) : ‖weight d * h‖ ≤ elementarySchwartzSeminorm (idx d) f := by
    have hb : (‖weight d*h‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound f.val (idx d) :=
      le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl))
    exact ENNReal.toReal_mono (f.property.2 (idx d)).ne hb
  have hmono (d : (Fin m ⊕ Fin r) →₀ ℕ) (c : ℂ) :
      MvPolynomial.eval e (MvPolynomial.monomial d c) = c * weight d := by
    rw [MvPolynomial.eval_monomial,d.prod_fintype _ (fun _ => pow_zero _),Fintype.prod_sum_type]
    rfl
  have he : MvPolynomial.eval e p * h = ∑ d ∈ p.support, p.coeff d * (weight d*h) := by
    conv_lhs => rw [p.as_sum,map_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [hmono,mul_assoc]
  change ‖MvPolynomial.eval e p‖ * ‖h‖ ≤ _
  rw [←norm_mul,he]
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun d _ => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound d) (norm_nonneg _))
