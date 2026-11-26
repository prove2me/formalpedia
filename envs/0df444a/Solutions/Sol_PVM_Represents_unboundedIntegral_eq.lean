-- Prove2me | solution 1 for PVM.Represents.unboundedIntegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:12:18.468222+00:00
-- url     : https://prove2.me/submissions/d6d793e7-2c2d-45f4-a7dd-03021c1c7cd5

import Definitions.Def_Spectral_Spectral_Uniqueness
import Definitions.Def_Spectral_Spectral_Intrinsic
import Theorems.Thm_PVM_inner_coordinate_unboundedIntegral_self
import Theorems.Thm_PVM_simpleIntegral_one
import Theorems.Thm_PVM_simpleIntegral_zero
attribute [local simp] PVM.simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero



set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM.Represents
theorem _root_.solution
    {E_pvm : PVM E} {A : E →ₗ.[ℂ] E} (hrep : E_pvm.Represents A)
    (hA : IsSelfAdjoint A) :
    E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A := by
  let coord : ℝ → ℂ := (↑)
  let hcoord : Measurable coord := Complex.continuous_ofReal.measurable
  let B := E_pvm.unboundedIntegral coord hcoord
  rcases hrep with ⟨mu, hmu, hdomain, hmoment⟩
  have hmeasure (x : E) : mu x = E_pvm.scalarMeasure x := by
    apply Measure.ext
    intro S hS
    rw [hmu x S hS, E_pvm.scalarMeasure_apply x S hS]
    rfl
  have hdomains : B.domain = A.domain := by
    ext x
    rw [show x ∈ B.domain ↔
        ∫⁻ t, ‖coord t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x) < ⊤ from
      E_pvm.mem_domain_unboundedIntegral coord hcoord x]
    rw [hdomain x, hmeasure x]
  have hquad (z : E) (hzB : z ∈ B.domain) (hzA : z ∈ A.domain) :
      @inner ℂ E _ (B ⟨z, hzB⟩) z =
        @inner ℂ E _ (A ⟨z, hzA⟩) z := by
    have hdiag : @inner ℂ E _ z (B ⟨z, hzB⟩) =
        @inner ℂ E _ z (A ⟨z, hzA⟩) := by
      calc
        @inner ℂ E _ z (B ⟨z, hzB⟩) =
            ∫ t, coord t ∂(E_pvm.scalarMeasure z) := by
          exact E_pvm.inner_coordinate_unboundedIntegral_self ⟨z, hzB⟩
        _ = ∫ t, coord t ∂(mu z) := by rw [hmeasure z]
        _ = @inner ℂ E _ z (A ⟨z, hzA⟩) := (hmoment ⟨z, hzA⟩).symm
    calc
      @inner ℂ E _ (B ⟨z, hzB⟩) z =
          (starRingEnd ℂ) (@inner ℂ E _ z (B ⟨z, hzB⟩)) :=
        (inner_conj_symm (B ⟨z, hzB⟩) z).symm
      _ = (starRingEnd ℂ) (@inner ℂ E _ z (A ⟨z, hzA⟩)) :=
        congrArg (starRingEnd ℂ) hdiag
      _ = @inner ℂ E _ (A ⟨z, hzA⟩) z :=
        inner_conj_symm (A ⟨z, hzA⟩) z
  have hquad_sub (zB : B.domain) (zA : A.domain)
      (hz : (zB : E) = (zA : E)) :
      @inner ℂ E _ (B zB) (zB : E) =
        @inner ℂ E _ (A zA) (zA : E) := by
    rcases zB with ⟨zB, hzB⟩
    rcases zA with ⟨zA, hzA⟩
    simp only at hz ⊢
    subst zA
    exact hquad zB hzB hzA
  have hpolarization (T : E →ₗ.[ℂ] E) (a b : T.domain) :
      @inner ℂ E _ (T b) (a : E) =
        (@inner ℂ E _ (T (a + b)) ((a + b : T.domain) : E) -
            @inner ℂ E _ (T (a - b)) ((a - b : T.domain) : E) +
              Complex.I * @inner ℂ E _ (T (a + Complex.I • b))
                ((a + Complex.I • b : T.domain) : E) -
            Complex.I * @inner ℂ E _ (T (a - Complex.I • b))
              ((a - Complex.I • b : T.domain) : E)) / 4 := by
    simp only [LinearPMap.map_add, LinearPMap.map_sub, inner_add_left,
      inner_add_right, LinearPMap.map_smul, inner_smul_left, inner_smul_right,
      Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
      mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub,
      sub_sub, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul]
    ring
  apply LinearPMap.ext hdomains
  intro y hyB hyA
  apply hA.dense_domain.eq_of_inner_left ℂ
  intro v hvA
  have hvB : v ∈ B.domain := by rw [hdomains]; exact hvA
  let aB : B.domain := ⟨v, hvB⟩
  let bB : B.domain := ⟨y, hyB⟩
  let aA : A.domain := ⟨v, hvA⟩
  let bA : A.domain := ⟨y, hyA⟩
  rw [hpolarization B aB bB, hpolarization A aA bA]
  rw [hquad_sub (aB + bB) (aA + bA) rfl,
    hquad_sub (aB - bB) (aA - bA) rfl,
    hquad_sub (aB + Complex.I • bB) (aA + Complex.I • bA) rfl,
    hquad_sub (aB - Complex.I • bB) (aA - Complex.I • bA) rfl]
end PVM.Represents
