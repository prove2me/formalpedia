-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.F_degrees
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:39:40.333688+00:00
-- url     : https://prove2.me/submissions/081834f5-bca8-495c-aa2c-491d175a1ff8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_aMM_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sigP_F
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
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
private theorem sigP_monomial {D N : ℕ} (b : Fin (D + 1)) (u : Kˣ) (s : TVar D N →₀ ℕ) (a : K) :
    sigP (K := K) (N := N) b u (monomial s a) = monomial s (a * (u : K) ^ (∑ j, s (b, j))) := by
  show aeval (fun v : TVar D N => if v.1 = b then C (u : K) * X v else X v) (monomial s a) = _
  have e1 : (s.prod fun v e => (if v.1 = b then C (u : K) * X v else X v) ^ e) =
      ∏ v, (if v.1 = b then C (u : K) * X v else X v) ^ s v :=
    Finsupp.prod_fintype _ _ (fun v => pow_zero _)
  have e2 : (s.prod fun v e => (X v : MvPolynomial (TVar D N) K) ^ e) = ∏ v, X v ^ s v :=
    Finsupp.prod_fintype _ _ (fun v => pow_zero _)
  have hfac : ∀ v : TVar D N, (if v.1 = b then C (u : K) * X v else X v) ^ s v =
      C (u : K) ^ (if v.1 = b then s v else 0) * X v ^ s v := by
    intro v
    split_ifs <;> simp [mul_pow]
  have hsum : ∑ v : TVar D N, (if v.1 = b then s v else 0) = ∑ j, s (b, j) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  rw [aeval_monomial, monomial_eq, e1, e2, Finset.prod_congr rfl (fun v _ => hfac v),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, algebraMap_eq, C_mul, C_pow]
  ring
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    (∀ s ∈ F.support, ∑ j, s (0, j) = d.delc c) ∧
      ∀ b : Fin (d.D + 1), b ≠ 0 → ∀ s ∈ F.support, ∑ j, s (b, j) = (d.aMM h c).toNat := by
  have hco : ∀ (b : Fin (d.D + 1)) (u : Kˣ) (s : TVar d.D d.N →₀ ℕ),
      coeff s F * (u : K) ^ (∑ j, s (b, j)) =
        (u : K) ^ (if b = 0 then (d.delc c : ℤ) else d.aMM h c) * coeff s F := by
    intro b u s
    have e := congrArg (coeff s) (sigP_F d hd h c F hF b u)
    rw [coeff_C_mul] at e
    rw [← e]
    conv_rhs => rw [F.as_sum]
    rw [map_sum, coeff_sum]
    simp only [sigP_monomial, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hs
    · rfl
    · rw [mem_support_iff, not_not] at hs
      rw [hs, zero_mul]
  have hdeg : ∀ (b : Fin (d.D + 1)) (s : TVar d.D d.N →₀ ℕ), s ∈ F.support →
      (2 : K) ^ (∑ j, s (b, j)) = (2 : K) ^ (if b = 0 then (d.delc c : ℤ) else d.aMM h c) := by
    intro b s hs
    have h2 := hco b (Units.mk0 2 two_ne_zero) s
    simp only [Units.val_mk0] at h2
    rw [mul_comm] at h2
    exact mul_right_cancel₀ (mem_support_iff.mp hs) h2
  have inj : ∀ m n : ℕ, (2 : K) ^ m = (2 : K) ^ n → m = n := by
    intro m n hmn
    have h' : ((2 ^ m : ℕ) : K) = ((2 ^ n : ℕ) : K) := by
      push_cast
      exact hmn
    exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h')
  refine ⟨fun s hs => ?_, fun b hb s hs => ?_⟩
  · have h0 := hdeg 0 s hs
    rw [if_pos rfl, zpow_natCast] at h0
    exact inj _ _ h0
  · have h1 := hdeg b s hs
    rw [if_neg hb, ← Int.toNat_of_nonneg (aMM_nonneg d hd h c), zpow_natCast] at h1
    exact inj _ _ h1
end ReciprocityTheory.ChartRestriction.G.T0.Data
