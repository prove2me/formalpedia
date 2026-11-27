-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_proof_ba6b1899b134
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:05:42.297954+00:00
-- url     : https://prove2.me/submissions/1c1b1c26-1dae-4e96-830e-e782a8c94b3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsConeTrdegFnField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConeTrdegFnField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_trdeg_eq_of_le_of_isAlgebraic_983b32a504c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_mem_fnField_of_mem_adjoin_776b36a2f92d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_coneMap_C_02118dc07c9d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_coneMap_X_ffc52befaca7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_mcMap_X_956b3496ba62
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_coneMap_injective_98f9e82e1c18

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcMap mcIdeal fnField)
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace ConeTrdegFnField
theorem _root_.solution : ConeTrdegFnField.Statement := by
  intro O _ _ Ω _ _ hinj K _ ι _ y hy
  choose c hc using hy
  set F₀ := Algebra.adjoin O (fnField O y : Set Ω)
  have hF : ∀ w ∈ fnField O y, w ∈ F₀ := fun w hw => Algebra.subset_adjoin hw
  have hu : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ F₀ := fun p =>
    hF _ (Subfield.subset_closure (Or.inr ⟨⟨p.1, (p.2, c p.1)⟩, rfl⟩))

  let ρ : MRingOver O ι →ₐ[O] MvPolynomial K F₀ := aeval fun p => C (⟨_, hu p⟩ : F₀) * X p.1
  have hfac : mcMap O y = (ConeTrdegFnField.coneMap (O := O) y c).comp ρ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    rw [ConeTrdegFnField.mcMap_X, AlgHom.comp_apply, aeval_X, map_mul, ConeTrdegFnField.coneMap_C,
      ConeTrdegFnField.coneMap_X, ← mul_assoc, ← map_mul]
    simp only [div_mul_cancel₀ _ (hc p.1)]
  set R := (mcMap O y).range
  have hle : R ≤ (ConeTrdegFnField.coneMap (O := O) y c).range := by
    show (mcMap O y).range ≤ _
    rw [hfac]; exact AlgHom.range_comp_le_range _ _
  have hXR : ∀ p : Σ k, ι k, (C (y p) * X p.1 : MvPolynomial K Ω) ∈ R := fun p =>
    ⟨X p, ConeTrdegFnField.mcMap_X y p⟩

  have halgC : ∀ w ∈ fnField O y, IsAlgebraic R (C w : MvPolynomial K Ω) := by
    intro w hw
    induction hw using Subfield.closure_induction with
    | mem x hx =>
      rcases hx with ⟨r, rfl⟩ | ⟨q, rfl⟩
      · have e : (C (algebraMap O Ω r) : MvPolynomial K Ω) = algebraMap O (MvPolynomial K Ω) r := by
          rw [MvPolynomial.algebraMap_apply]
        rw [e]
        exact isAlgebraic_algebraMap (⟨_, R.algebraMap_mem r⟩ : R)
      · dsimp only
        by_cases h0 : y ⟨q.1, q.2.2⟩ = 0
        · rw [h0, div_zero, map_zero]; exact isAlgebraic_zero
        · refine IsAlgebraic.of_mul (y := C (y ⟨q.1, q.2.2⟩) * X q.1)
            (mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (C_ne_zero.2 h0) (X_ne_zero _)))
            (isAlgebraic_algebraMap (⟨_, hXR ⟨q.1, q.2.2⟩⟩ : R)) ?_
          have e : (C (y ⟨q.1, q.2.2⟩) * X q.1 : MvPolynomial K Ω) * C (y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) =
              C (y ⟨q.1, q.2.1⟩) * X q.1 := by
            rw [mul_comm, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ h0]
          rw [e]
          exact isAlgebraic_algebraMap (⟨_, hXR ⟨q.1, q.2.1⟩⟩ : R)
    | one => rw [map_one]; exact isAlgebraic_one
    | add x z _ _ hx hz => rw [map_add]; exact hx.add hz
    | neg x _ hx => rw [map_neg]; exact hx.neg
    | inv x _ hx =>
      by_cases h0 : x = 0
      · rw [h0, inv_zero, map_zero]; exact isAlgebraic_zero
      · refine IsAlgebraic.of_mul (y := C x) (mem_nonZeroDivisors_of_ne_zero (C_ne_zero.2 h0)) hx ?_
        rw [← map_mul, mul_inv_cancel₀ h0, map_one]; exact isAlgebraic_one
    | mul x z _ _ hx hz => rw [map_mul]; exact hx.mul hz
  have halg : ∀ t ∈ (ConeTrdegFnField.coneMap (O := O) y c).range, IsAlgebraic R t := by
    rintro _ ⟨q, rfl⟩
    change IsAlgebraic R (ConeTrdegFnField.coneMap (O := O) y c q)
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [ConeTrdegFnField.coneMap_C]
      exact halgC a (ConeTrdegFnField.mem_fnField_of_mem_adjoin y a.2)
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p k hp =>
      rw [map_mul, ConeTrdegFnField.coneMap_X]
      exact hp.mul (isAlgebraic_algebraMap (⟨_, hXR ⟨k, c k⟩⟩ : R))
  have hinjP : Function.Injective (algebraMap O (MvPolynomial K Ω)) := by
    rw [IsScalarTower.algebraMap_eq O Ω (MvPolynomial K Ω)]
    exact (C_injective K Ω).comp hinj
  have h1 : Algebra.trdeg O (MRingOver O ι ⧸ mcIdeal O y) = Algebra.trdeg O R :=
    (Ideal.quotientKerEquivRange (mcMap O y)).trdeg_eq
  have h2 : Algebra.trdeg O (ConeTrdegFnField.coneMap (O := O) y c).range = Algebra.trdeg O (MvPolynomial K F₀) :=
    (AlgEquiv.ofInjective (ConeTrdegFnField.coneMap (O := O) y c)
      (ConeTrdegFnField.coneMap_injective y c hc)).trdeg_eq.symm
  have _ : FaithfulSMul O F₀ :=
    (faithfulSMul_iff_algebraMap_injective O F₀).2 fun a b h => hinj (congrArg Subtype.val h)
  have _ : FaithfulSMul F₀ (MvPolynomial K F₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (C_injective K _)
  have h3 : Algebra.trdeg O (MvPolynomial K F₀) = Algebra.trdeg O F₀ + Fintype.card K := by
    rw [← trdeg_add_eq O F₀ (A := MvPolynomial K F₀), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
      Cardinal.mk_fintype]
  rw [h1, ConeTrdegFnField.trdeg_eq_of_le_of_isAlgebraic hinjP hle halg, h2, h3]
end ConeTrdegFnField
end GroundTheory.Heights₂.Heights.NumbersDVR
