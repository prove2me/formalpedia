-- Prove2me | solution 1 for WorstCaseCVaR.Discrete.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T03:53:22.946987+00:00
-- url     : https://prove2.me/submissions/c3088363-ab50-4c6b-b6d3-cf603aac7463

import Definitions.Def_WorstCaseCVaR_Discrete_Setting

section
set_option autoImplicit false
open WorstCaseCVaR.Discrete
namespace CVaRCodex

lemma threshold_bounds {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ k, -B ≤ f x (ys k) ∧ f x (ys k) ≤ B)
    (π : Fin S → ℝ) (hπ : π ∈ stdSimplex ℝ (Fin S)) :
    (∀ q : ℝ, q ≤ -B → G f ys β x (-B) π ≤ G f ys β x q π) ∧
    (∀ q : ℝ, B ≤ q → G f ys β x B π ≤ G f ys β x q π) ∧
    (∀ q : ℝ, -B ≤ G f ys β x q π) := by
  let c := (1-β)⁻¹
  have hc : 0 < c := inv_pos.mpr (by linarith)
  have he : c*(1-β) = 1 := inv_mul_cancel₀ (by linarith)
  have hcone : 1 ≤ c := by nlinarith [mul_pos hc hβ0]
  have hf (q : ℝ) (hq : q ≤ -B) : G f ys β x q π =
      q+c*((∑ k, π k*f x (ys k))-q) := by
    unfold G
    have hh (k) : max (f x (ys k)-q) 0 = f x (ys k)-q :=
      max_eq_left (sub_nonneg.mpr (hq.trans (hb k).1))
    simp_rw [hh,mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,hπ.2,one_mul]
    dsimp [c]
    ring
  have hz (q : ℝ) (hq : B ≤ q) : G f ys β x q π = q := by
    unfold G
    have hh (k) : max (f x (ys k)-q) 0 = 0 :=
      max_eq_right (sub_nonpos.mpr ((hb k).2.trans hq))
    simp_rw [hh]
    simp
  have hleft : ∀ q : ℝ, q ≤ -B → G f ys β x (-B) π ≤ G f ys β x q π := by
    intro q hq
    rw [hf (-B) le_rfl,hf q hq]
    have hh : (1-c)*(-B-q) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hq)
    nlinarith [hh]
  have hbase (q : ℝ) : q ≤ G f ys β x q π := by
    have hh : 0 ≤ ∑ k, π k*max (f x (ys k)-q) 0 :=
      Finset.sum_nonneg (fun k hk ↦ mul_nonneg (hπ.1 k) (le_max_right _ _))
    have hi := mul_nonneg hc.le hh
    change q ≤ q+c*(∑ k, π k*max (f x (ys k)-q) 0)
    linarith
  refine ⟨hleft,?_,?_⟩
  · intro q hq
    rw [hz B le_rfl,hz q hq]
    exact hq
  · intro q
    by_cases hq : q ≤ -B
    · exact (hbase (-B)).trans (hleft q hq)
    · exact (le_of_lt (lt_of_not_ge hq)).trans (hbase q)

end CVaRCodex

end


section
set_option autoImplicit false
open WorstCaseCVaR.Discrete
namespace CVaRCodex

/-- Proof of Theorem 2, Zhu & Fukushima (2009), p. 1167: there is one nonempty, closed, bounded
interval `𝒜 = [a, b]` such that, for every `π ∈ 𝒫_π`, `G_β(x, ·, π)` attains its minimum over `ℝ`
at a point of `𝒜`; hence `min_{α ∈ ℝ} G_β(x, α, π) = min_{α ∈ 𝒜} G_β(x, α, π)`. -/
theorem reduction_to_interval {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Set (Fin S → ℝ)) (hP : P ⊆ stdSimplex ℝ (Fin S)) :
    ∃ a b : ℝ, a ≤ b ∧ ∀ π ∈ P, ∃ α ∈ Set.Icc a b,
      IsMinOn (fun α' : ℝ => G f ys β x α' π) Set.univ α := by
  classical
  let B := (∑ k : Fin S, |f x (ys k)|) + 1
  have hB : 0 ≤ B := by
    have hh : 0 ≤ ∑ k : Fin S, |f x (ys k)| := Finset.sum_nonneg (fun k hk ↦ abs_nonneg _)
    dsimp [B]
    linarith
  have hb : ∀ k : Fin S, -B ≤ f x (ys k) ∧ f x (ys k) ≤ B := by
    intro k
    apply abs_le.mp
    have hh : |f x (ys k)| ≤ ∑ j : Fin S, |f x (ys j)| :=
      Finset.single_le_sum (fun j hj ↦ abs_nonneg (f x (ys j))) (Finset.mem_univ k)
    dsimp [B]
    linarith
  have hab : -B ≤ B := by linarith
  refine ⟨-B,B,hab,?_⟩
  intro π hπ
  have hc : Continuous (fun q : ℝ ↦ G f ys β x q π) := by
    unfold G
    fun_prop
  obtain ⟨q,hq,hm⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (-B) B).Nonempty from ⟨-B,le_rfl,hab⟩) hc.continuousOn
  have hh := threshold_bounds f ys x β hβ0 hβ1 B hB hb π (hP hπ)
  refine ⟨q,hq,isMinOn_iff.mpr ?_⟩
  intro a ha
  by_cases hlo : a < -B
  · exact (isMinOn_iff.mp hm (-B) ⟨le_rfl,hab⟩).trans (hh.1 a hlo.le)
  · by_cases hhi : B < a
    · exact (isMinOn_iff.mp hm B ⟨hab,le_rfl⟩).trans (hh.2.1 a hhi.le)
    · exact isMinOn_iff.mp hm a ⟨le_of_not_gt hlo,le_of_not_gt hhi⟩


end CVaRCodex

end


section
set_option autoImplicit false
open WorstCaseCVaR.Discrete
namespace CVaRCodex

/-- The min-max inequality used in the proof of Theorem 2, Zhu & Fukushima (2009), p. 1167 (stated
there for Theorem 1's `H_β`): `inf_{α ∈ ℝ} max_{π ∈ 𝒫_π} G_β(x, α, π) ≥ sup_{π ∈ 𝒫_π} min_{α ∈ ℝ}
G_β(x, α, π) = WCVaR_β(x)`, in the equivalent form: for every `α`,
`WCVaR_β(x) ≤ max_{π ∈ 𝒫_π} G_β(x, α, π)`. -/
theorem minmax_inequality {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Set (Fin S → ℝ)) (hP : P ⊆ stdSimplex ℝ (Fin S)) (hne : P.Nonempty) :
    ∀ α : ℝ, wcvar f ys β x P ≤ sSup ((fun π => G f ys β x α π) '' P) := by
  intro α
  have hc : 0 ≤ (1-β)⁻¹ := inv_nonneg.mpr (by linarith)
  have hbound : BddAbove ((fun π ↦ G f ys β x α π) '' P) := by
    refine ⟨α+(1-β)⁻¹*(∑ k, max (f x (ys k)-α) 0),?_⟩
    rintro y ⟨π,hπ,rfl⟩
    have hh : (∑ k, π k*max (f x (ys k)-α) 0) ≤ ∑ k, max (f x (ys k)-α) 0 := by
      apply Finset.sum_le_sum
      intro k hk
      have hp := (mem_Icc_of_mem_stdSimplex (hP hπ) k).2
      simpa using mul_le_mul_of_nonneg_right hp (le_max_right (f x (ys k)-α) 0)
    simpa only [G,add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hh hc) α
  obtain ⟨a,b,hab,hmin⟩ := reduction_to_interval f ys x β hβ0 hβ1 P hP
  apply csSup_le (hne.image _)
  rintro y ⟨π,hπ,rfl⟩
  have hbelow : BddBelow (Set.range (fun q ↦ G f ys β x q π)) := by
    obtain ⟨q,hq,hopt⟩ := hmin π hπ
    simpa only [Set.image_univ] using hopt.bddBelow
  exact (csInf_le hbelow (show G f ys β x α π ∈ Set.range (fun q ↦ G f ys β x q π) from
    ⟨α,rfl⟩)).trans (le_csSup hbound ⟨π,hπ,rfl⟩)


end CVaRCodex

end


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
namespace CVaRCodex

/-- Theorem 2, Zhu & Fukushima (2009), p. 1159: if `𝒫_π` is a compact convex set (of probability
vectors on the scenarios `y_[1], …, y_[S]`, nonempty), then for each `x`
`WCVaR_β(x) = min_{α ∈ ℝ} max_{π ∈ 𝒫_π} G_β(x, α, π)`.
Both extrema on the right are attained: for every `α` the maximum over `𝒫_π` is attained, and
some `α₀` minimizes `α ↦ max_{π ∈ 𝒫_π} G_β(x, α, π)` over `ℝ`, with value `WCVaR_β(x)`. -/
theorem theorem_2 {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Set (Fin S → ℝ)) (hP : P ⊆ stdSimplex ℝ (Fin S)) (hne : P.Nonempty)
    (hcpt : IsCompact P) (hcvx : Convex ℝ P) :
    (∀ α : ℝ, ∃ π₀ ∈ P, IsMaxOn (fun π => G f ys β x α π) P π₀) ∧
    ∃ α₀ : ℝ, IsMinOn (fun α : ℝ => sSup ((fun π => G f ys β x α π) '' P)) Set.univ α₀ ∧
      wcvar f ys β x P = sSup ((fun π => G f ys β x α₀ π) '' P) := by
  have hmax : ∀ α : ℝ, ∃ π₀ ∈ P, IsMaxOn (fun π ↦ G f ys β x α π) P π₀ := by
    intro α
    have hc : Continuous (fun π : Fin S → ℝ ↦ G f ys β x α π) := by
      unfold G
      fun_prop
    exact hcpt.exists_isMaxOn hne hc.continuousOn
  obtain ⟨a,b,hab,hred⟩ := reduction_to_interval f ys x β hβ0 hβ1 P hP
  obtain ⟨q,hq,π,hπ,hs⟩ := lemma_1_on_interval f ys x β hβ0 hβ1 P hP hne hcpt hcvx a b hab
  have hmin : IsMinOn (fun r : ℝ ↦ G f ys β x r π) Set.univ q := by
    obtain ⟨r,hr,hopt⟩ := hred π hπ
    apply isMinOn_iff.mpr
    intro t ht
    exact (hs r hr π hπ).2.trans (isMinOn_iff.mp hopt t ht)
  have hm : IsMaxOn (fun p ↦ G f ys β x q p) P π := by
    apply isMaxOn_iff.mpr
    intro p hp
    exact (hs q hq p hp).1
  have hcv : cvar f ys β x π = G f ys β x q π := by
    have hb : BddBelow (Set.range (fun r ↦ G f ys β x r π)) := by
      simpa only [Set.image_univ] using hmin.bddBelow
    apply le_antisymm (csInf_le hb ⟨q,rfl⟩)
    apply le_csInf (Set.range_nonempty _)
    rintro y ⟨r,rfl⟩
    exact isMinOn_iff.mp hmin r (Set.mem_univ r)
  have hsup : sSup ((fun p ↦ G f ys β x q p) '' P) = G f ys β x q π := by
    refine le_antisymm ?_ (le_csSup hm.bddAbove ⟨π,hπ,rfl⟩)
    apply csSup_le (hne.image _)
    rintro y ⟨p,hp,rfl⟩
    exact isMaxOn_iff.mp hm p hp
  have hcb : BddAbove ((fun p ↦ cvar f ys β x p) '' P) := by
    refine ⟨G f ys β x q π,?_⟩
    rintro y ⟨p,hp,rfl⟩
    obtain ⟨r,hr,hopt⟩ := hred p hp
    have hb : BddBelow (Set.range (fun t ↦ G f ys β x t p)) := by
      simpa only [Set.image_univ] using hopt.bddBelow
    exact (csInf_le hb ⟨q,rfl⟩).trans (isMaxOn_iff.mp hm p hp)
  have heq : wcvar f ys β x P = sSup ((fun p ↦ G f ys β x q p) '' P) := by
    apply le_antisymm (minmax_inequality f ys x β hβ0 hβ1 P hP hne q)
    rw [hsup,← hcv]
    exact le_csSup hcb ⟨π,hπ,rfl⟩
  refine ⟨hmax,q,isMinOn_iff.mpr ?_,heq⟩
  intro r hr
  rw [← heq]
  exact minmax_inequality f ys x β hβ0 hβ1 P hP hne r


end CVaRCodex

end


section
set_option autoImplicit false
open WorstCaseCVaR.Discrete
theorem solution {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Set (Fin S → ℝ)) (hP : P ⊆ stdSimplex ℝ (Fin S)) (hne : P.Nonempty)
    (hcpt : IsCompact P) (hcvx : Convex ℝ P) :
    (∀ α : ℝ, ∃ π₀ ∈ P, IsMaxOn (fun π => G f ys β x α π) P π₀) ∧
    ∃ α₀ : ℝ, IsMinOn (fun α : ℝ => sSup ((fun π => G f ys β x α π) '' P)) Set.univ α₀ ∧
      wcvar f ys β x P = sSup ((fun π => G f ys β x α₀ π) '' P) := by
  exact CVaRCodex.theorem_2 f ys x β hβ0 hβ1 P hP hne hcpt hcvx

end

#print axioms solution
