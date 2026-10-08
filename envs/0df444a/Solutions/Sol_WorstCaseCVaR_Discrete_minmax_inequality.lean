-- Prove2me | solution 1 for WorstCaseCVaR.Discrete.minmax_inequality
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T03:52:35.50664+00:00
-- url     : https://prove2.me/submissions/5fd96f82-acd2-4077-bb5b-2ebb7e88ee57

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
theorem solution {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Set (Fin S → ℝ)) (hP : P ⊆ stdSimplex ℝ (Fin S)) (hne : P.Nonempty) :
    ∀ α : ℝ, wcvar f ys β x P ≤ sSup ((fun π => G f ys β x α π) '' P) := by
  exact CVaRCodex.minmax_inequality f ys x β hβ0 hβ1 P hP hne

end

#print axioms solution
