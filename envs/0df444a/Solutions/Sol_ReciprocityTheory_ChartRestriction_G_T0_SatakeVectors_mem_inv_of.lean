-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.mem_inv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:38:50.401847+00:00
-- url     : https://prove2.me/submissions/73134d97-df09-4858-b2a0-bcc4e9bd1b58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Qdist
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Mathlib.NumberTheory.Height.NumberField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_contId_ne_bot
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



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type*} (G₀ : MvPolynomial κ (𝓞 K)) (h : G₀ ≠ 0) (x : K)
    (hx : ∀ s, ∃ y : 𝓞 K, (y : K) = x * ((G₀.coeff s : 𝓞 K) : K)) :
    x ∈ ((contId G₀ : FractionalIdeal (𝓞 K)⁰ K)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) := by
  have hI : ((contId G₀ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (contId_ne_bot G₀ h)
  rw [FractionalIdeal.mem_inv_iff hI]
  intro y hy
  have hy2 : ∃ y', y' ∈ contId G₀ ∧ algebraMap (𝓞 K) K y' = y := by
    first
      | exact (FractionalIdeal.mem_coeIdeal _).mp hy
      | exact FractionalIdeal.mem_coeIdeal.mp hy
  obtain ⟨y', hy', rfl⟩ := hy2
  rw [FractionalIdeal.mem_one_iff]
  have key : ∃ z : 𝓞 K, (z : K) = x * (y' : K) := by
    clear hy
    unfold contId at hy'
    induction hy' using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨⟨s, _⟩, rfl⟩ := ha
      exact hx s
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨z1, h1⟩ := ha
      obtain ⟨z2, h2⟩ := hb
      refine ⟨z1 + z2, ?_⟩
      first
        | (push_cast; linear_combination h1 + h2)
        | (simp only [map_add]; linear_combination h1 + h2)
        | (simp; linear_combination h1 + h2)
    | smul r a _ ha =>
      obtain ⟨z, hz⟩ := ha
      refine ⟨r * z, ?_⟩
      rw [smul_eq_mul]
      first
        | (push_cast; linear_combination (r : K) * hz)
        | (simp only [map_mul]; linear_combination (algebraMap (𝓞 K) K r) * hz)
        | (simp; linear_combination (r : K) * hz)
  obtain ⟨z, hz⟩ := key
  first
    | exact ⟨z, hz⟩
    | exact ⟨z, by simpa using hz⟩
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
