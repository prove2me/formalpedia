-- Prove2me | solution 1 for PI.ProdFormulaE.Tr.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:05:47.987566+00:00
-- url     : https://prove2.me/submissions/2a8f4e90-d1b5-46b4-942f-d16b670c893a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_T2SpaceOfIsValuativeTopology

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel Filter Topology
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F]
namespace PI.ProdFormulaE.Tr
theorem _root_.solution {ι : Type} [Finite ι] (P : ι → HeightOneSpectrum (𝓞 F))
    (hP : Function.Injective P) (b : ι → F) (c : F) (hc : c ≠ 0) :
    ∃ x : F, ∀ i, (P i).valuation F (x - b i) ≤ (P i).valuation F c := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F)) b
  have hd' : ∀ i, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = (d : 𝓞 F) • b i :=
    fun i => RingHom.mem_rangeS.1 (hd i)
  choose a ha using hd'
  have hd0 : algebraMap (𝓞 F) F (d : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (nonZeroDivisors.coe_ne_zero d)
  have hw : ∀ i, (P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F) * c) ≠ 0 := fun i =>
    (Valuation.ne_zero_iff _).2 (mul_ne_zero hd0 hc)
  have hn : ∀ i, WithZero.exp (-((WithZero.log ((P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F) * c))).natAbs : ℤ))
      ≤ (P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F) * c) := by
    intro i
    conv_rhs => rw [← WithZero.exp_log (hw i)]
    rw [WithZero.exp_le_exp, Int.natCast_natAbs]
    exact neg_abs_le _
  cases nonempty_fintype ι
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun i => (P i).asIdeal)
    (fun i => (WithZero.log ((P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F) * c))).natAbs)
    (fun i _ => (P i).prime) (fun i _ j _ hij h => hij (hP (HeightOneSpectrum.ext h)))
    (fun i => a i.1)
  refine ⟨algebraMap (𝓞 F) F y / algebraMap (𝓞 F) F (d : 𝓞 F), fun i => ?_⟩
  have h1 := ((P i).intValuation_le_pow_iff_mem _ _).2 (hy i (Finset.mem_univ _))
  have h2 : (P i).valuation F (algebraMap (𝓞 F) F (y - a i)) ≤
      (P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F) * c) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact h1.trans (hn i)
  have h3 : algebraMap (𝓞 F) F (d : 𝓞 F) *
      (algebraMap (𝓞 F) F y / algebraMap (𝓞 F) F (d : 𝓞 F) - b i) = algebraMap (𝓞 F) F (y - a i) := by
    rw [map_sub, ha i, Algebra.smul_def]
    field_simp
  have key : (P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F)) *
      (P i).valuation F (algebraMap (𝓞 F) F y / algebraMap (𝓞 F) F (d : 𝓞 F) - b i) ≤
      (P i).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F)) * (P i).valuation F c := by
    rw [← map_mul, ← map_mul, h3]
    exact h2
  exact (mul_le_mul_iff_right₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hd0))).1 key
end PI.ProdFormulaE.Tr
