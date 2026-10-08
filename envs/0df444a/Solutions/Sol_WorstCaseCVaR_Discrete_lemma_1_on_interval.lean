-- Prove2me | solution 1 for WorstCaseCVaR.Discrete.lemma_1_on_interval
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T03:52:58.754635+00:00
-- url     : https://prove2.me/submissions/53e4c288-da7b-4392-ba29-e5713b052f0d

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
namespace CVaRCodex

/-- Proof of Theorem 2, Zhu & Fukushima (2009), p. 1167 (Lemma 1 applied on `𝒜 × 𝒫_π`): for every
nonempty closed bounded interval `𝒜 = [a, b]` and every nonempty compact convex set `𝒫_π` of
probability vectors, `G_β(x, ·, ·)` has a saddle point `(α₀, π₀)` on `𝒜 × 𝒫_π`; equivalently,
`max_{π ∈ 𝒫_π} min_{α ∈ 𝒜} G_β(x, α, π) = min_{α ∈ 𝒜} max_{π ∈ 𝒫_π} G_β(x, α, π)` with all extrema
attained. -/
theorem lemma_1_on_interval {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Set (Fin S → ℝ)) (hP : P ⊆ stdSimplex ℝ (Fin S)) (hne : P.Nonempty)
    (hcpt : IsCompact P) (hcvx : Convex ℝ P) (a b : ℝ) (hab : a ≤ b) :
    ∃ α₀ ∈ Set.Icc a b, ∃ π₀ ∈ P, ∀ α ∈ Set.Icc a b, ∀ π ∈ P,
      G f ys β x α₀ π ≤ G f ys β x α₀ π₀ ∧ G f ys β x α₀ π₀ ≤ G f ys β x α π₀ := by
  have hca (π : Fin S → ℝ) : Continuous (fun q : ℝ ↦ G f ys β x q π) := by
    unfold G
    fun_prop
  have hcp (q : ℝ) : Continuous (fun π : Fin S → ℝ ↦ G f ys β x q π) := by
    unfold G
    fun_prop
  have hconv (π : Fin S → ℝ) (hπ : π ∈ P) :
      ConvexOn ℝ (Set.Icc a b) (fun q : ℝ ↦ G f ys β x q π) :=
    ((convex_affine_G f ys x β hβ0 hβ1).1 π (hP hπ)).subset (Set.subset_univ _) (convex_Icc a b)
  have hconc (q : ℝ) : ConcaveOn ℝ P (fun π : Fin S → ℝ ↦ G f ys β x q π) := by
    obtain ⟨g,hg⟩ := (convex_affine_G f ys x β hβ0 hβ1).2 q
    refine ⟨hcvx,?_⟩
    intro p hp r hr u v hu hv huv
    simp_rw [hg]
    rw [Convex.combo_affine_apply huv]
  obtain ⟨q,hq,π,hπ,hs⟩ := Sion.exists_isSaddlePointOn
    (show (Set.Icc a b).Nonempty from ⟨a,le_rfl,hab⟩) (convex_Icc a b) isCompact_Icc
    (fun π hπ ↦ (hca π).lowerSemicontinuous.lowerSemicontinuousOn (Set.Icc a b))
    (fun π hπ ↦ (hconv π hπ).quasiconvexOn)
    hcvx hne hcpt (fun q hq ↦ (hcp q).upperSemicontinuous.upperSemicontinuousOn P)
    (fun q hq ↦ (hconc q).quasiconcaveOn)
  exact ⟨q,hq,π,hπ,fun r hr p hp ↦ ⟨hs q hq p hp,hs r hr π hπ⟩⟩


end CVaRCodex

end


section
set_option autoImplicit false
open WorstCaseCVaR.Discrete
theorem solution {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Set (Fin S → ℝ)) (hP : P ⊆ stdSimplex ℝ (Fin S)) (hne : P.Nonempty)
    (hcpt : IsCompact P) (hcvx : Convex ℝ P) (a b : ℝ) (hab : a ≤ b) :
    ∃ α₀ ∈ Set.Icc a b, ∃ π₀ ∈ P, ∀ α ∈ Set.Icc a b, ∀ π ∈ P,
      G f ys β x α₀ π ≤ G f ys β x α₀ π₀ ∧ G f ys β x α₀ π₀ ≤ G f ys β x α π₀ := by
  exact CVaRCodex.lemma_1_on_interval f ys x β hβ0 hβ1 P hP hne hcpt hcvx a b hab

end

#print axioms solution
