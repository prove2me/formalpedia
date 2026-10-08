-- Prove2me | solution 1 for WorstCaseCVaR.Mixture.eq_58_59
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T04:20:49.888279+00:00
-- url     : https://prove2.me/submissions/4115335c-2829-429e-a5d4-035c2ad38033

import Definitions.Def_WorstCaseCVaR_Mixture_Setting

section
set_option autoImplicit false
open MeasureTheory
open WorstCaseCVaR.Mixture
namespace MixtureCodex

lemma simplex_average_le {l : ℕ} (v lam : Fin l → ℝ)
    (h : lam ∈ stdSimplex ℝ (Fin l)) (θ : ℝ) (hv : ∀ i, v i ≤ θ) :
    (∑ i, lam i*v i) ≤ θ := by
  calc
    _ ≤ ∑ i, lam i*θ := Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_left (hv i) (h.1 i))
    _ = θ := by rw [← Finset.sum_mul,h.2,one_mul]

lemma simplex_average_maximum {l : ℕ} [NeZero l] (v : Fin l → ℝ) :
    sSup ((fun lam : Fin l → ℝ ↦ ∑ i, lam i*v i) '' stdSimplex ℝ (Fin l)) =
      Finset.univ.sup' Finset.univ_nonempty v := by
  let M := Finset.univ.sup' Finset.univ_nonempty v
  have hm : ∀ i, v i ≤ M := fun i ↦ Finset.le_sup' v (Finset.mem_univ i)
  have hb : BddAbove ((fun lam : Fin l → ℝ ↦ ∑ i, lam i*v i) '' stdSimplex ℝ (Fin l)) := by
    refine ⟨M,?_⟩
    rintro y ⟨lam,hlam,rfl⟩
    exact simplex_average_le v lam hlam M hm
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty v
  have hp : (Pi.single i 1 : Fin l → ℝ) ∈ stdSimplex ℝ (Fin l) := single_mem_stdSimplex ℝ i
  have hs : (∑ j, (Pi.single i 1 : Fin l → ℝ) j*v j) = v i := by simp [Pi.single_apply]
  apply le_antisymm
  · apply csSup_le ((show (stdSimplex ℝ (Fin l)).Nonempty from ⟨Pi.single i 1,hp⟩).image _)
    rintro y ⟨lam,hlam,rfl⟩
    exact simplex_average_le v lam hlam M hm
  · rw [he]
    rw [← hs]
    exact le_csSup hb ⟨Pi.single i 1,hp,rfl⟩

end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory
open WorstCaseCVaR.Mixture
namespace MixtureCodex

theorem eq_58_59 {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    (∀ α θ : ℝ, (∀ lam ∈ stdSimplex ℝ (Fin l), ∑ i, lam i * Fi P f β x i α ≤ θ) ↔
        ∀ i, Fi P f β x i α ≤ θ) ∧
      ∀ α : ℝ, sSup ((fun lam => ∑ i, lam i * Fi P f β x i α) '' stdSimplex ℝ (Fin l)) =
        FL P f β x α := by
  constructor
  · intro α θ
    constructor
    · intro h i
      have hp : (Pi.single i 1 : Fin l → ℝ) ∈ stdSimplex ℝ (Fin l) := single_mem_stdSimplex ℝ i
      simpa [Pi.single_apply] using h (Pi.single i 1) hp
    · intro h lam hlam
      exact simplex_average_le (fun i ↦ Fi P f β x i α) lam hlam θ h
  · intro α
    exact simplex_average_maximum (fun i ↦ Fi P f β x i α)


end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory WorstCaseCVaR.Mixture
theorem solution {l m n : ℕ} [NeZero l] (P : Fin l → Measure (Fin m → ℝ))
    [∀ i, IsProbabilityMeasure (P i)] (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → ℝ)
    (hf : ∀ i, Integrable (f x) (P i)) :
    (∀ α θ : ℝ, (∀ lam ∈ stdSimplex ℝ (Fin l), ∑ i, lam i * Fi P f β x i α ≤ θ) ↔
        ∀ i, Fi P f β x i α ≤ θ) ∧
      ∀ α : ℝ, sSup ((fun lam => ∑ i, lam i * Fi P f β x i α) '' stdSimplex ℝ (Fin l)) =
        FL P f β x α := by
  exact MixtureCodex.eq_58_59 P f β hβ0 hβ1 x hf

end

#print axioms solution
