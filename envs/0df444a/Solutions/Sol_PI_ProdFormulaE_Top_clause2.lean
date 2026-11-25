-- Prove2me | solution 1 for PI.ProdFormulaE.Top.clause2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:46.098029+00:00
-- url     : https://prove2.me/submissions/3a292b5b-cd21-45f1-87ea-18bc99199288

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ProdFormulaEOf
import Theorems.Thm_PI_ProdFormulaE_Top_fibFin
import Theorems.Thm_PI_ProdFormulaE_Top_fam_over
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_P2M_PI_ProdFormulaE_Base_psiE__E_d316781c1d77
import Theorems.Thm_PI_ProdFormulaE_Frac_den_eq_one_of_norm_le_one
import Theorems.Thm_PI_ProdFormulaE_Frac_finprod_exp
import Theorems.Thm_PI_ProdFormulaE_Frac_norm_sum_sub_sum_le_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField MeasureTheory ValuativeRel Formalism.MainNotions.S.Loc
open PI PI.ProdFormulaE PI.ProdFormulaE.Top
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
namespace PI.ProdFormulaE.Top
theorem _root_.solution (hT : Tr.TrSum) (hI : St.TrInt) (hR : St.ResCharIff) (h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (x : E) :
    (Function.mulSupport fun p => (L p).psiE ((L p).ιE x)).Finite ∧
      ∏ᶠ p, (L p).psiE ((L p).ιE x) =
        Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ))) := by
  classical
  set z := Algebra.trace F E x with hzdef
  choose a ha hn he using fun p => Base.psiE_ιE (L p) h2 x
  have hfun : (fun p => (L p).psiE ((L p).ιE x)) =
      fun p => Complex.exp (2 * Real.pi * Complex.I * ((a p : ℚ) : ℂ)) := funext he
  rw [hfun]
  have hprime : ∀ p : HeightOneSpectrum (𝓞 F), (resChar p).Prime := fun p => (L p).ellPrime.out
  let fib : ℕ → Finset (HeightOneSpectrum (𝓞 F)) := fun q =>
    if hq : q.Prime then (fibFin hR hq).toFinset else ∅
  have hfib : ∀ p q, p ∈ fib q ↔ resChar p = q := by
    intro p q
    by_cases hq : q.Prime
    · simp only [fib, dif_pos hq, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    · simp only [fib, dif_neg hq, Finset.notMem_empty, false_iff]
      rintro rfl
      exact hq (hprime p)

  have hfin : {p | (a p).den ≠ 1}.Finite := by
    obtain ⟨d, hd0, hdint⟩ :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ F |>.mpr (.of_finite ℚ z)).exists_integral_multiple
    have hne : Ideal.span {((d : ℤ) : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hd0
    refine (Ideal.finite_factors hne).subset fun p hp => ?_
    simp only [Set.mem_ofPred_eq] at hp ⊢
    rw [Ideal.dvd_span_singleton]
    by_contra hdp
    apply hp
    haveI := (L p).ellPrime
    have hres : ((resChar p : ℕ) : 𝓞 F) ∈ p.asIdeal := (hR F p (resChar p) (hprime p)).1 rfl
    have hnd : ¬ ((resChar p : ℕ) : ℤ) ∣ d := by
      rintro ⟨k, hk⟩
      apply hdp
      rw [hk, Int.cast_mul]
      exact p.asIdeal.mul_mem_right _ (by exact_mod_cast hres)
    have hd1 : ‖(d : ℚ_[resChar p])‖ = 1 :=
      le_antisymm (Padic.norm_int_le_one d)
        (not_lt.1 fun h => hnd (Padic.norm_intCast_lt_one_iff.1 h))
    have hint : IsIntegral ℤ ((L p).ιF (d • z)) := hdint.map (L p).ιF.toIntAlgHom
    haveI := (L p).qlFin
    have hT1 := hI (resChar p) (L p).Fp ((L p).ιF (d • z)) hint
    have hsm : (L p).ιF (d • z) = algebraMap ℚ_[resChar p] (L p).Fp (d : ℚ_[resChar p]) *
        (L p).ιF z := by
      rw [zsmul_eq_mul, map_mul, map_intCast, map_intCast]
    rw [hsm, ← Algebra.smul_def, map_smul, smul_eq_mul, norm_mul, hd1,
      one_mul] at hT1
    obtain ⟨n, hn'⟩ := ha p
    exact Frac.den_eq_one_of_norm_le_one hn' hT1 (hn p)
  refine Frac.finprod_exp resChar hprime a ha fib hfib hfin _ fun q hq => ?_

  have hfs : Set.Finite {p : HeightOneSpectrum (𝓞 F) | resChar p = q} := fibFin hR hq.out
  haveI : Fintype {p : HeightOneSpectrum (𝓞 F) // resChar p = q} := hfs.fintype
  have hsum := hT F q _ (fam L q) (fam_over hR L q) z
  have htr : Algebra.trace ℚ F z = Algebra.trace ℚ E x := Algebra.trace_trace x
  rw [htr] at hsum
  have hsub : ∑ i ∈ fib q, (a i : ℚ_[q]) =
      ∑ i : {p : HeightOneSpectrum (𝓞 F) // resChar p = q}, (a i.1 : ℚ_[q]) :=
    Finset.sum_subtype _ (fun p => hfib p q) _
  rw [hsub, ← eq_ratCast (algebraMap ℚ ℚ_[q]), ← hsum]
  refine Frac.norm_sum_sub_sum_le_one _ _ _ fun i _ => ?_
  have h1 := (transport_at L q i).choose_spec.2.2 ((L i.1).ιF z) (a i.1)
  exact h1.trans_le (hn i.1)
end PI.ProdFormulaE.Top
