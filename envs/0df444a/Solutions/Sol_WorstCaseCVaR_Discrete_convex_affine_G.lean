-- Prove2me | solution 1 for WorstCaseCVaR.Discrete.convex_affine_G
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T03:39:04.637577+00:00
-- url     : https://prove2.me/submissions/92c77235-b4e0-4f99-8180-08bcc58c3932

import Definitions.Def_WorstCaseCVaR_Discrete_Setting

section
set_option autoImplicit false
open WorstCaseCVaR.Discrete
namespace CVaRCodex

/-- Proof of Theorem 2, Zhu & Fukushima (2009), p. 1167: for fixed `x`, `G_β(x, α, π)` is convex
in `α` (for each probability vector `π`) and affine in `π` (for each `α`). -/
theorem convex_affine_G {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ π ∈ stdSimplex ℝ (Fin S), ConvexOn ℝ Set.univ (fun α : ℝ => G f ys β x α π)) ∧
    (∀ α : ℝ, ∃ g : (Fin S → ℝ) →ᵃ[ℝ] ℝ, ∀ π : Fin S → ℝ, G f ys β x α π = g π) := by
  classical
  constructor
  · intro π hπ
    refine ⟨convex_univ,?_⟩
    intro a ha b hb u v hu hv huv
    simp only [smul_eq_mul]
    have hh (k : Fin S) : max (f x (ys k)-(u*a+v*b)) 0 ≤
        u*max (f x (ys k)-a) 0 + v*max (f x (ys k)-b) 0 := by
      apply max_le
      · calc
          _ = u*(f x (ys k)-a) + v*(f x (ys k)-b) := by linear_combination -(f x (ys k))*huv
          _ ≤ _ := add_le_add
            (mul_le_mul_of_nonneg_left (le_max_left _ _) hu)
            (mul_le_mul_of_nonneg_left (le_max_left _ _) hv)
      · exact add_nonneg (mul_nonneg hu (le_max_right _ _))
          (mul_nonneg hv (le_max_right _ _))
    have hs : (∑ k, π k * max (f x (ys k)-(u*a+v*b)) 0) ≤
        u*(∑ k, π k * max (f x (ys k)-a) 0) +
        v*(∑ k, π k * max (f x (ys k)-b) 0) := by
      calc
        _ ≤ ∑ k, π k * (u*max (f x (ys k)-a) 0 + v*max (f x (ys k)-b) 0) :=
          Finset.sum_le_sum (fun k hk ↦ mul_le_mul_of_nonneg_left (hh k) (hπ.1 k))
        _ = _ := by
          simp_rw [mul_add,Finset.sum_add_distrib,← mul_assoc]
          rw [Finset.mul_sum,Finset.mul_sum]
          congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;> ring
    have hc : 0 ≤ (1-β)⁻¹ := inv_nonneg.mpr (by linarith)
    have hf := mul_le_mul_of_nonneg_left hs hc
    dsimp [G]
    nlinarith [hf]
  · intro α
    let L : (Fin S → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun π ↦ (1-β)⁻¹ * ∑ k, π k * max (f x (ys k)-α) 0
        map_add' := by
          intro p q
          simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib,mul_add]
        map_smul' := by
          intro a p
          simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          ring }
    let g : (Fin S → ℝ) →ᵃ[ℝ] ℝ :=
      { toFun := fun π ↦ α + L π
        linear := L
        map_vadd' := by
          intro p v
          change α + L (v+p) = L v + (α + L p)
          rw [L.map_add]
          ring }
    exact ⟨g,fun π ↦ rfl⟩


end CVaRCodex

end


section
set_option autoImplicit false
open WorstCaseCVaR.Discrete
theorem solution {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ π ∈ stdSimplex ℝ (Fin S), ConvexOn ℝ Set.univ (fun α : ℝ => G f ys β x α π)) ∧
    (∀ α : ℝ, ∃ g : (Fin S → ℝ) →ᵃ[ℝ] ℝ, ∀ π : Fin S → ℝ, G f ys β x α π = g π) := by
  exact CVaRCodex.convex_affine_G f ys x β hβ0 hβ1

end

#print axioms solution
