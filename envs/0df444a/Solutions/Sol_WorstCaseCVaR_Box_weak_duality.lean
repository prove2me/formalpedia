-- Prove2me | solution 1 for WorstCaseCVaR.Box.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T04:53:32.640831+00:00
-- url     : https://prove2.me/submissions/3aa5346d-7d9d-42d7-beaf-3b357673e341

import Definitions.Def_WorstCaseCVaR_Box_DualPair

section
set_option autoImplicit false
open Matrix WorstCaseCVaR.Box
namespace BoxCVaRCodex
lemma weak_pair {S : ℕ} (ηlo ηhi u η : Fin S → ℝ)
    (hη : η ∈ lp22Feasible ηlo ηhi) (d : Dual23 S) (hd : d ∈ lp23Feasible u) :
    u ⬝ᵥ η ≤ lp23Obj ηlo ηhi d := by
  classical
  rcases hη with ⟨hs,hl,hh⟩
  rcases hd with ⟨hu,hξ,hω⟩
  change (∑ k, u k * η k) ≤ (∑ k, ηhi k * d.ξ k) + ∑ k, ηlo k * d.ω k
  have hp (k : Fin S) : u k = d.z + d.ξ k + d.ω k := by
    have h := congrFun hu k
    simpa only [Pi.add_apply] using h.symm
  simp_rw [hp,add_mul,Finset.sum_add_distrib]
  rw [← Finset.mul_sum,hs,mul_zero,zero_add,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have h1 := mul_le_mul_of_nonneg_left (hh k) (hξ k)
  have h2 := mul_le_mul_of_nonpos_left (hl k) (hω k)
  nlinarith

theorem weak_duality {S : ℕ} (ηlo ηhi u : Fin S → ℝ) :
    (∀ η ∈ lp22Feasible ηlo ηhi, ∀ d ∈ lp23Feasible u, u ⬝ᵥ η ≤ lp23Obj ηlo ηhi d) ∧
    ((lp22Feasible ηlo ηhi).Nonempty →
      ∀ d ∈ lp23Feasible u, gammaStar ηlo ηhi u ≤ lp23Obj ηlo ηhi d) := by
  refine ⟨fun η hη d hd => weak_pair ηlo ηhi u η hη d hd,?_⟩
  intro hne d hd
  apply csSup_le (hne.image _)
  rintro y ⟨η,hη,rfl⟩
  exact weak_pair ηlo ηhi u η hη d hd
end BoxCVaRCodex

end


section
set_option autoImplicit false
open Matrix WorstCaseCVaR.Box
theorem solution {S : ℕ} (ηlo ηhi u : Fin S → ℝ) :
    (∀ η ∈ lp22Feasible ηlo ηhi, ∀ d ∈ lp23Feasible u, u ⬝ᵥ η ≤ lp23Obj ηlo ηhi d) ∧
    ((lp22Feasible ηlo ηhi).Nonempty →
      ∀ d ∈ lp23Feasible u, gammaStar ηlo ηhi u ≤ lp23Obj ηlo ηhi d) := BoxCVaRCodex.weak_duality ηlo ηhi u

end

#print axioms solution
