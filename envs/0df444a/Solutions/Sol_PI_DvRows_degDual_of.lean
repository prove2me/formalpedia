-- Prove2me | solution 1 for PI.DvRows.degDual_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:35:28.426539+00:00
-- url     : https://prove2.me/submissions/96f30935-ed38-4b89-ac10-0f9ad439c1f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmDual
import Theorems.Thm_PI_DvRows_linInd_left
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_DvRows_degL_eq_neg_lcv
import Theorems.Thm_PI_DvRows_finrank_eq_two_nPl
import Theorems.Thm_PI_DvRows_lcvFin_eq
import Theorems.Thm_PI_DvRows_lidx_support_finite
import Theorems.Thm_PI_DvRows_vAdd_support_finite
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
theorem _root_.solution (hFG : LamFG) (hAd : Adapted) (hAI : ArchIdentity) (hLP : LocalPairing)
    (hCP : ConjPrime) (hNF : NormFinsum) : DegDual := by
  intro K _ _ _ _ _ A e n h hS hP hH hC U hU
  have hyp : Hyp K A e n h := ⟨hS, hP, hH, hC⟩
  obtain ⟨k, d, u, z, y, hlin, hspz, hspu, hzM, hy, hyM, hspy, hMfg, hSfg, hspM, hspS⟩ :=
    hAd K A e n h hyp U hU
  have hfg := hFG K A e n h hyp U hU
  have hu : LinearIndependent K u := linInd_left u z hlin
  set M := cutE A e A.L with hM
  set S := cutE A e A.L ⊓ U.restrictScalars (𝓞 K) with hS'
  set Λ := lamSub A e h U with hΛ
  rw [degL_eq_neg_lcv A hP.1 S hSfg u hu hspS, degL_eq_neg_lcv A hP.1 M hMfg _ hlin hspM,
    degL_eq_neg_lcv A hP.1 Λ hfg y hy hspy]
  have hyU : ∀ i, ∀ x ∈ U, h (y i) x = 0 := fun i => (hyM i).2.1
  have hye : ∀ i, y i ∈ LinearMap.range e := fun i => (hyM i).1
  have harch := hAI K A e n h hyp U hU k d u z y hlin hspz hspu hy hye hyU
  obtain ⟨c, hcinv, hc⟩ := hCP K
  have hlwc : ∀ w, lw K (c w) = lw K w := fun w => by unfold lw; rw [(hc w).2]
  set D := (Matrix.of fun i j => h (y i) (z j)).det with hD
  set zf := Fin.append u z with hzf
  set Ly := Submodule.span (𝓞 K) (Set.range y)
  set Lz := Submodule.span (𝓞 K) (Set.range zf)
  set Lu := Submodule.span (𝓞 K) (Set.range u)
  have hloc : ∀ w, (vAdd w D : ℝ) + (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal Ly Λ : ℝ) +
      (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lz M : ℝ) - (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lu S : ℝ) = 0 := by
    intro w
    have := hLP K A e n h hyp U hU k d u z y hlin hspz hspu hzM hy hyM hspy w (c w) (hc w).1
    exact_mod_cast this

  have fV := vAdd_support_finite (K := K) D
  have fY := lidx_support_finite A hP.1 Λ hfg y hy hspy
  have fZ := lidx_support_finite A hP.1 M hMfg zf hlin hspM
  have fU := lidx_support_finite A hP.1 S hSfg u hu hspS
  set a : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (vAdd w D : ℝ)
  set gy : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Ly Λ : ℝ)
  set gz : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lz M : ℝ)
  set gu : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lu S : ℝ)
  have sub : ∀ {x : HeightOneSpectrum (𝓞 K) → ℤ}, (Function.support x).Finite →
      (Function.support fun w => lw K w * (x w : ℝ)).Finite := fun hx =>
    hx.subset (fun w hw => by
      simp only [Function.mem_support] at hw ⊢
      intro h0; apply hw; rw [h0]; simp)
  have fa : (Function.support a).Finite := sub fV
  have fgy : (Function.support gy).Finite := sub fY
  have fgz : (Function.support gz).Finite := sub fZ
  have fgu : (Function.support gu).Finite := sub fU
  have fgyc : (Function.support fun w => gy (c w)).Finite :=
    (fgy.preimage (hcinv.injective.injOn)).subset (fun w hw => hw)
  have hsum0 : (∑ᶠ w, (a w + gy (c w) + gz w - gu w)) = 0 := by
    have : (fun w => a w + gy (c w) + gz w - gu w) = fun _ => (0 : ℝ) := by
      funext w
      simp only [a, gy, gz, gu]
      rw [hlwc w]
      have := hloc w
      linear_combination lw K w * this
    rw [this, finsum_zero]
  have hsym : (∑ᶠ w, gy (c w)) = ∑ᶠ w, gy w := by
    have : (fun w => gy (c w)) = fun w => gy (Function.Involutive.toPerm c hcinv w) := by
      funext w; simp
    rw [this]
    exact finsum_comp_equiv (Function.Involutive.toPerm c hcinv)
  have hsplit : (∑ᶠ w, (a w + gy (c w) + gz w - gu w)) =
      (∑ᶠ w, a w) + (∑ᶠ w, gy (c w)) + (∑ᶠ w, gz w) - ∑ᶠ w, gu w := by
    rw [finsum_sub_distrib ((fa.union fgyc).union fgz |>.subset ?_) fgu,
      finsum_add_distrib ((fa.union fgyc).subset (Function.support_add _ _)) fgz,
      finsum_add_distrib fa fgyc]
    intro w hw
    simp only [Function.mem_support] at hw
    by_contra hn
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    apply hw
    rw [hn.1.1, hn.1.2, hn.2]; ring
  rw [hsplit, hsym] at hsum0

  have hnorm : Real.log |((Algebra.norm ℚ D : ℚ) : ℝ)| / (Module.finrank ℚ K : ℝ) = ∑ᶠ w, a w := by
    by_cases hD0 : D = 0
    · simp only [a]
      rw [hD0]
      simp [vAdd]
    · exact (hNF K D hD0).symm
  unfold lcv lcvInf
  rw [lcvFin_eq A u, lcvFin_eq A zf, lcvFin_eq A y]
  have hk := finrank_eq_two_nPl (K := K)
  have hnpos : (0 : ℝ) < Formalism.HN.nPl K := by
    unfold Formalism.HN.nPl
    exact_mod_cast Fintype.card_pos
  rw [hk] at hnorm
  have e1 : (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v zf).det.re -
      (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re =
      2 * (∑ᶠ w, a w) - (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re := by
    rw [← hnorm, ← harch]
    field_simp
    ring
  change -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re + 2 * ∑ᶠ w, gu w) -
      -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v zf).det.re + 2 * ∑ᶠ w, gz w) =
      -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re + 2 * ∑ᶠ w, gy w)
  linarith
end PI.DvRows
