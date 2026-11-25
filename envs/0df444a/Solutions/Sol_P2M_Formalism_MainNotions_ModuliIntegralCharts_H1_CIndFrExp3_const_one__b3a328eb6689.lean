-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp3_const_one__b3a328eb6689
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:40:07.221045+00:00
-- url     : https://prove2.me/submissions/22196127-d3dd-46e8-835d-6691c6f9ac95

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BalOf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IsUnitCoeffZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
variable {S : Type} [CommRing S] {d : ℕ}
section Main
variable [Algebra ℚ S]
private theorem constantCoeff_germEvalPair_eq_zero_lemma {τ : Type} (h : MvPolynomial (Fin 2 × Fin d) S) (u v : Fin d → MvPolynomial τ S)
    (hu : ∀ j, constantCoeff (u j) = 0) (hv : ∀ j, constantCoeff (v j) = 0) :
    constantCoeff (ev2 h u v) = constantCoeff h := by
  unfold ev2
  induction h using MvPolynomial.induction_on
  · simp
  · simp only [map_add, *]
  · rename_i p n _
    rcases n with ⟨i, j⟩
    fin_cases i <;> simp [hu, hv]
end Main
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
variable {S : Type} [CommRing S] {d : ℕ}
variable [Algebra ℚ S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
theorem _root_.solution {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ} (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hfF : ∀ i, fF i ∈ Io S (Fin 3 × Fin d))
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hu : IsUnit (coeff 0 P)) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 1 := by
  have hIo : ∀ {σ : Type} (f : MvPolynomial σ S), f ∈ Io S σ → constantCoeff f = 0 := by
    intro σ f hf
    have h2 : Io S σ ≤ RingHom.ker (constantCoeff : MvPolynomial σ S →+* S) := by
      unfold Io idealOfVars
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp
    exact h2 hf
  have hfF0 : ∀ i, constantCoeff (fF i) = 0 := fun i => hIo _ (hfF i)
  have hxs : ∀ (k : Fin 3) (j : Fin d), constantCoeff (xs S d k j) = 0 := by
    intro k j
    simp [xs]
  have hpow : Io S (Fin 3 × Fin d) ^ (m + 1) ≤ Io S (Fin 3 × Fin d) :=
    Ideal.pow_le_self (Nat.succ_ne_zero m)
  have h0 := hIo _ (hpow hph1)
  rw [map_sub, map_mul, constantCoeff_germEvalPair_eq_zero_lemma P fF (xs S d 2) hfF0 (hxs 2),
    constantCoeff_germEvalPair_eq_zero_lemma P (xs S d 0) (xs S d 2) (hxs 0) (hxs 2),
    constantCoeff_germEvalPair_eq_zero_lemma P (xs S d 1) (xs S d 2) (hxs 1) (hxs 2)] at h0
  have hu' : IsUnit (constantCoeff P) := hu
  have hc : constantCoeff P = 1 := by
    have h3 : constantCoeff P * (1 - constantCoeff P) = 0 := by
      rw [mul_sub, mul_one]
      exact h0
    exact (sub_eq_zero.1 ((hu'.mul_right_eq_zero).1 h3)).symm
  rw [pow_one]
  unfold Io idealOfVars
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro e he
  have hne : e ≠ 0 := by
    rintro rfl
    have hc' : coeff 0 P = 1 := hc
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_zero_one, hc', sub_self] at he
    exact he rfl
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (Finsupp.ext hcon)
  exact ⟨i, Set.mem_univ _, hi⟩
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
