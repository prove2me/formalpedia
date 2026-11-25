-- Prove2me | solution 1 for PI.DvRows.degDualBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:34.195813+00:00
-- url     : https://prove2.me/submissions/41ab8644-81ed-4e2d-896e-601a5b49f6ef

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound
import Theorems.Thm_PI_DvRows_vAdd_support_finite
import Theorems.Thm_PI_DvRows_finrank_eq_two_nPl
import Theorems.Thm_PI_DvRows_degL_eq_neg_lcv
import Theorems.Thm_PI_DvRows_lidx_support_finite
import Theorems.Thm_PI_DvRows_lcvFin_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_covolume_exists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
namespace PI.DvRows
theorem _root_.solution (hFG : LamFG) (hCS : GramCS) (hLG : LocalGamma) (hCP : ConjPrime) (hNF : NormFinsum) :
    DegDualBound := by
  intro K _ _ _ _ _ A e n h hS hP hH hC U hU γ hγ
  have hyp : Hyp K A e n h := ⟨hS, hP, hH, hC⟩
  haveI : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  obtain ⟨d, y, hy, hyM, hsp⟩ := covolume_exists K A.V (lamSub A e h U)
  have hfg := hFG K A e n h hyp U hU
  rw [degL_eq_neg_lcv A hP.1 _ hfg y hy hsp]
  obtain ⟨c, hcinv, hc⟩ := hCP K
  set D := (Matrix.of fun i j => h (y i) (y j)).det with hD
  set L := Submodule.span (𝓞 K) (Set.range y) with hL
  have hγw : ∀ w, (γ w : ℝ) = -(vAdd w D : ℝ) - (Formalism.HermitianLatticesTheory.lidx w.asIdeal L (lamSub A e h U) : ℝ) -
      (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ) := by
    intro w
    have := hLG K A e n h hyp U hU d y hy hyM hsp w (γ w) (hγ w) (c w) (hc w).1
    rw [this]; push_cast; ring
  obtain ⟨hD0, hcs⟩ := hCS K A e n h hyp d y hy
  have hfinV := vAdd_support_finite (K := K) D
  have hfinL := lidx_support_finite A hP.1 _ hfg y hy hsp
  set f : HeightOneSpectrum (𝓞 K) → ℝ := fun w =>
    lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal L (lamSub A e h U) : ℝ) with hf
  have hfinf : (Function.support f).Finite :=
    hfinL.subset (fun w hw => by
      simp only [Function.mem_support, hf] at hw ⊢
      intro h0; apply hw; rw [h0]; simp)
  have hfinv : (Function.support fun w => lw K w * (vAdd w D : ℝ)).Finite :=
    hfinV.subset (fun w hw => by
      simp only [Function.mem_support] at hw ⊢
      intro h0; apply hw; rw [h0]; simp)
  have hcf : (Function.support fun w => f (c w)).Finite := by
    refine (hfinf.preimage (hcinv.injective.injOn)).subset (fun w hw => hw)
  have hsym : ∑ᶠ w, lw K w * (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ) = ∑ᶠ w, f w := by
    have h1 : (fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ)) =
        fun w => f (Function.Involutive.toPerm c hcinv w) := by
      funext w
      simp only [hf, Function.Involutive.coe_toPerm]
      congr 1
      unfold lw
      rw [(hc w).2]
    rw [h1]
    exact finsum_comp_equiv (Function.Involutive.toPerm c hcinv)
  have hsplit : ∑ᶠ w, lw K w * (γ w : ℝ) =
      -(∑ᶠ w, lw K w * (vAdd w D : ℝ)) - ∑ᶠ w, f w -
        ∑ᶠ w, lw K w * (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ) := by
    have hlwc : ∀ w, lw K (c w) = lw K w := fun w => by unfold lw; rw [(hc w).2]
    have h1 : (fun w => lw K w * (γ w : ℝ)) = fun w =>
        (-(lw K w * (vAdd w D : ℝ)) + -f w) + -(f (c w)) := by
      funext w
      rw [hγw w]
      simp only [hf]
      rw [hlwc w]; ring
    have hA : (Function.support fun w => -(lw K w * (vAdd w D : ℝ))).Finite :=
      hfinv.subset (fun w hw => by simpa using hw)
    have hB : (Function.support fun w => -f w).Finite :=
      hfinf.subset (fun w hw => by simpa using hw)
    have hC' : (Function.support fun w => -(f (c w))).Finite :=
      hcf.subset (fun w hw => by simpa using hw)
    have hAB : (Function.support fun w => -(lw K w * (vAdd w D : ℝ)) + -f w).Finite :=
      (hA.union hB).subset (Function.support_add _ _)
    rw [h1, finsum_add_distrib hAB hC', finsum_add_distrib hA hB]
    simp only [finsum_neg_distrib]
    have h2 : (∑ᶠ w, f (c w)) = ∑ᶠ w, lw K w * (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ) := by
      congr 1; funext w; simp only [hf]; rw [hlwc w]
    rw [h2]; ring
  rw [hsplit, hsym, hNF K D hD0]
  have hlcv : lcvFin y (lamSub A e h U) = 2 * ∑ᶠ w, f w := lcvFin_eq A y _
  unfold lcv
  rw [hlcv]
  unfold lcvInf
  have hk := finrank_eq_two_nPl (K := K)
  have hnpos : (0 : ℝ) < Formalism.HN.nPl K := by
    unfold Formalism.HN.nPl
    exact_mod_cast Fintype.card_pos
  rw [hk]
  have : Real.log |((Algebra.norm ℚ D : ℚ) : ℝ)| / (2 * (Formalism.HN.nPl K : ℝ)) ≤
      1 / (Formalism.HN.nPl K : ℝ) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re := by
    rw [div_le_iff₀ (by positivity)]
    have := hcs
    field_simp
    nlinarith
  linarith
end PI.DvRows
