-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:38:17.7148+00:00
-- url     : https://prove2.me/submissions/0e5620a6-bd20-43ee-94c3-0e7cf9d6a963

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_low_pderiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_low_subst_of_low
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_aeval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries Formalism.FG.SolveVAux
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {σ τ : Type}
private theorem low_mul_lemma {m n : ℕ} {f g : MvPowerSeries τ k} (hf : Low m f) (hg : Low n g) :
    Low (m + n) (f * g) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  first
  | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  | simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  | simp only [Finset.mem_antidiagonal] at hx
  have e : Finsupp.degree x.1 + Finsupp.degree x.2 = Finsupp.degree d := by
    rw [← hx]
    first
    | exact (map_add _ _ _).symm
    | simp [Finsupp.degree, Finsupp.sum_add_index']
  by_cases h1 : Finsupp.degree x.1 < m
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]
private theorem finsupp_apply_le_degree' {ι : Type} (d : ι →₀ ℕ) (i : ι) : d i ≤ d.degree := by
  first
  | exact Finsupp.le_degree i d
  | exact Finsupp.le_degree d i
  | exact Finsupp.le_degree
private theorem pderiv_coe_mvPolynomial (s : σ) (p : MvPolynomial σ k) :
    pderiv k s (p : MvPowerSeries σ k) = ((MvPolynomial.pderiv s p : MvPolynomial σ k) : MvPowerSeries σ k) := by
  ext m
  rw [MvPowerSeries.coeff_pderiv, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe, MvPolynomial.coeff_pderiv]
private theorem Low_finset_sum {N : ℕ} {ι : Type} (S : Finset ι) (F : ι → MvPowerSeries τ k)
    (h : ∀ i ∈ S, Low N (F i)) : Low N (∑ i ∈ S, F i) := by
  intro d hd
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi d hd
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries Formalism.FG.SolveVAux
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {σ τ : Type}
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution [Fintype σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ k) (t : τ) :
    pderiv k t (subst a f) = ∑ s, subst a (pderiv k s f) * pderiv k t (a s) := by
  classical
  have hS : HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have ha1 : ∀ s, Low 1 (a s) := by
    intro s d hd
    have hd0 : d = 0 := Finsupp.ext fun i => by
      have := finsupp_apply_le_degree' d i
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    subst hd0
    simpa using ha s
  have hpoly : ∀ M : ℕ, ∃ p : MvPolynomial σ k, Low M (f - (p : MvPowerSeries σ k)) := by
    intro M
    refine ⟨MvPowerSeries.trunc' k (Finsupp.equivFunOnFinite.symm fun _ => M) f, ?_⟩
    intro m hm
    rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos, sub_self]
    rw [Finsupp.le_def]
    intro s
    have h1 := finsupp_apply_le_degree' m s
    first
    | (change m s ≤ M; omega)
    | (simp; omega)
  ext d
  obtain ⟨p, hp⟩ := hpoly (d.degree + 1 + 1)
  have hf : f = (f - (p : MvPowerSeries σ k)) + (p : MvPowerSeries σ k) := (sub_add_cancel _ _).symm
  generalize f - (p : MvPowerSeries σ k) = g at hp hf
  subst hf
  have hpol := pderiv_aeval a p t
  simp only [map_add, MvPowerSeries.subst_add hS, MvPowerSeries.subst_coe, pderiv_coe_mvPolynomial, add_mul,
    Finset.sum_add_distrib, hpol]
  congr 1
  have h1 : Low (d.degree + 1) (pderiv k t (subst a g)) := low_pderiv (low_subst_of_low ha1 hp) t
  have h2 : Low (d.degree + 1 + 0) (∑ s, subst a (pderiv k s g) * pderiv k t (a s)) :=
    Low_finset_sum _ _ fun s _ => low_mul_lemma (low_subst_of_low ha1 (low_pderiv hp s)) (fun e he => by omega)
  rw [h1 d (by omega), h2 d (by omega)]
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
