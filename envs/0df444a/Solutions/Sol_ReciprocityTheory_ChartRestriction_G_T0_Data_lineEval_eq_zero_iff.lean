-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.lineEval_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:08.385501+00:00
-- url     : https://prove2.me/submissions/ab1ee985-6b7f-4111-aa7e-32748896acc3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightKerScaledSubstitutionLeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorStructure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightLeTorusHeightSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorHeightBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_lineSection_eq_ratio_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_lineSection_pow_ne_zero
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply


section
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
private theorem sum_support_inr_eq_xDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) :
    ∑ x ∈ s.support, Sum.elim (fun _ => 0) (fun i => s (Sum.inr i)) x = xDeg s := by
  rw [xDeg, Finset.sum_subset (Finset.subset_univ _), Fintype.sum_sum_type]
  · simp
  · intro x _ hx
    cases x with
    | inl p => rfl
    | inr i => simpa using hx
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (n : ℕ) (Q : MvPolynomial (UXVar d.D d.N) K)
    (hQ : XHom n Q) : d.evc c Q = 0 ↔ d.linearSubstitution c Q = 0 := by
  haveI := hd.tower c
  have hw0 := d.lineSection_pow_ne_zero hd c n
  have hfac : d.evc c Q = MvPolynomial.map (algebraMap (Ω c) (A c)) (d.linearSubstitution c Q) *
      MvPolynomial.C (d.w (d.jc c) c ^ n) := by
    rw [Q.as_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s hs => ?_
    simp only [evc, linearSubstitution, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_apply, map_mul,
      MvPolynomial.map_C, Finsupp.prod, map_prod, map_pow]
    rw [← IsScalarTower.algebraMap_apply, mul_assoc]
    congr 1
    rw [← hQ s hs, ← sum_support_inr_eq_xDeg s]
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    cases x with
    | inl p => simp
    | inr i =>
      simp only [Sum.elim_inr, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
      rw [← mul_pow, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [d.lineSection_eq_ratio_smul hd c j, Algebra.smul_def, MvPolynomial.C_mul]
      ring
  rw [hfac]
  constructor
  · intro h
    ext β
    have hb := congrArg (MvPolynomial.coeff β) h
    rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_zero, mul_comm,
      ← Algebra.smul_def] at hb
    rw [MvPolynomial.coeff_zero]
    exact (smul_eq_zero.1 hb).resolve_right hw0
  · intro h
    rw [h, map_zero, zero_mul]
end ReciprocityTheory.ChartRestriction.G.T0.Data
