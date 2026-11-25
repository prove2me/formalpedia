-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_der__2d3ff284a7e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:59:35.876648+00:00
-- url     : https://prove2.me/submissions/0afd02d1-23f0-4f96-9a64-35806c5a9d8d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_ddiv_monomial__64d37c5132b7
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_expand_monomial__8cd8bb5d66fe
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_natCast_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hDER : DER K v p) (hD : DVRHyp v p) (r g : ℕ) (M : Fin r →₀ ℕ) (c : ℕ) (hc : 1 ≤ c) :
    ∃ (I : Type) (_ : Fintype I) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ)),
      (∀ s, 0 ≤ v (cf s)) ∧ (∀ s, (absE (κ s) : ℝ) ≤ (absE M : ℝ) / ((p : ℝ) ^ g) + c) ∧
      ∀ η : Fin r →₀ ℕ, cge v c (ddiv M (monomial η (1 : K)) -
        ∑ s, if cls s = (fun a => η a % p ^ g) then
          monomial (ρ' s + p ^ g • (δ s + (divE (p ^ g) η - κ s))) (cf s * bin (κ s) (divE (p ^ g) η))
          else 0) := by
  have hP : 0 < p ^ g := pow_pos hD.prime.pos g
  have H : ∀ ρf : Fin r → Fin (p ^ g), ∃ (n : ℕ) (cf : Fin n → K) (ρ' δ κ : Fin n → (Fin r →₀ ℕ)),
      (∀ t, 0 ≤ v (cf t)) ∧ (∀ t, (absE (κ t) : ℝ) ≤ (absE M : ℝ) / ((p : ℝ) ^ g) + c) ∧
      ∀ (β γ : Fin r →₀ ℕ), ((c : ℕ) : WithTop ℚ) ≤
        v ((ddiv M (monomial ((Finsupp.equivFunOnFinite.symm fun a => ((ρf a : ℕ))) + p ^ g • β) (1 : K)) -
          ∑ t, monomial (ρ' t) (cf t) *
            expand (p ^ g) (monomial (δ t) (1 : K) * ddiv (κ t) (monomial β (1 : K)))).coeff γ) :=
    fun ρf => hDER hD r g _ (fun a => by simp) M c hc
  choose n cf ρ' δ κ hcf hκ happ using H
  refine ⟨Σ ρf : Fin r → Fin (p ^ g), Fin (n ρf), inferInstance, fun s a => (s.1 a : ℕ),
    fun s => cf s.1 s.2, fun s => ρ' s.1 s.2, fun s => δ s.1 s.2, fun s => κ s.1 s.2,
    fun s => hcf s.1 s.2, fun s => hκ s.1 s.2, fun η => ?_⟩
  obtain ⟨ρf, hρf⟩ : ∃ ρf : Fin r → Fin (p ^ g), ∀ a, (ρf a : ℕ) = η a % p ^ g :=
    ⟨fun a => ⟨η a % p ^ g, Nat.mod_lt _ hP⟩, fun a => rfl⟩
  have hη : η = (Finsupp.equivFunOnFinite.symm fun a => ((ρf a : ℕ))) + p ^ g • divE (p ^ g) η := by
    ext a
    have hm := Nat.mod_add_div (η a) (p ^ g)
    simp [divE_apply, hρf]
    all_goals first | exact hm.symm | omega
  have hterm : ∀ t, monomial (ρ' ρf t) (cf ρf t) * expand (p ^ g) (monomial (δ ρf t) (1 : K) *
      ddiv (κ ρf t) (monomial (divE (p ^ g) η) (1 : K))) =
      monomial (ρ' ρf t + p ^ g • (δ ρf t + (divE (p ^ g) η - κ ρf t)))
        (cf ρf t * bin (κ ρf t) (divE (p ^ g) η)) := by
    intro t
    rw [ddiv_monomial', monomial_mul, expand_monomial', monomial_mul, one_mul, one_mul]
  have hsum : (∑ s : (Σ ρf : Fin r → Fin (p ^ g), Fin (n ρf)),
      if (fun a => (s.1 a : ℕ)) = (fun a => η a % p ^ g) then
        monomial (ρ' s.1 s.2 + p ^ g • (δ s.1 s.2 + (divE (p ^ g) η - κ s.1 s.2)))
          (cf s.1 s.2 * bin (κ s.1 s.2) (divE (p ^ g) η)) else 0) =
      ∑ t, monomial (ρ' ρf t) (cf ρf t) * expand (p ^ g) (monomial (δ ρf t) (1 : K) *
        ddiv (κ ρf t) (monomial (divE (p ^ g) η) (1 : K))) := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single ρf]
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [hterm t]
      exact if_pos (funext hρf)
    · intro b _ hb
      refine Finset.sum_eq_zero fun t _ => if_neg ?_
      intro h
      apply hb
      funext a
      apply Fin.ext
      have h2 : ((b a : ℕ)) = η a % p ^ g := congrFun h a
      rw [h2, hρf a]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hpoly : ddiv M (monomial η (1 : K)) - (∑ s : (Σ ρf : Fin r → Fin (p ^ g), Fin (n ρf)),
      if (fun a => (s.1 a : ℕ)) = (fun a => η a % p ^ g) then
        monomial (ρ' s.1 s.2 + p ^ g • (δ s.1 s.2 + (divE (p ^ g) η - κ s.1 s.2)))
          (cf s.1 s.2 * bin (κ s.1 s.2) (divE (p ^ g) η)) else 0) =
      ddiv M (monomial ((Finsupp.equivFunOnFinite.symm fun a => ((ρf a : ℕ))) + p ^ g • divE (p ^ g) η) (1 : K)) -
        ∑ t, monomial (ρ' ρf t) (cf ρf t) * expand (p ^ g) (monomial (δ ρf t) (1 : K) *
          ddiv (κ ρf t) (monomial (divE (p ^ g) η) (1 : K))) := by
    rw [hsum, ← hη]
  intro γ
  have key := happ ρf (divE (p ^ g) η) γ
  rw [← hpoly] at key
  exact (vge_natCast_bound v c _).2 key
end Formalism.MainNotions.PlaneGram
