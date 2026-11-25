-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_add_head_1a96cf9f98d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:15:26.679424+00:00
-- url     : https://prove2.me/submissions/233278a6-c3bb-44a8-a625-20d7aad526c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairCocycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_cons_793b6e89e838
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimStrictDrop_proof_15777780f510
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleMul_proof_5282581d8898
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialIdealCorresp_proof_bd738eb41ba7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialIdealMultiHomog_proof_41306882bd1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialQuotDim_proof_5536281ab8d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SupSpanMultiHomog_proof_861d53cbe2c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommute_proof_79421367f623
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_lt_natCast_of_add_one_le_0fd376134ce8


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
universe u
variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (h3 : IntNumAddFirst.Statement.{0}) {ϖ : O} (hϖ : Irreducible ϖ)
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) {W : Ideal (MRing ι O)} (hW : ratDiv P f g W ≠ 0)
    (u v : K → ℤ) (l : List (K → ℤ)) (hl : l.length + 1 = d) :
    vNumL W ((u + v) :: l) = vNumL W (u :: l) + vNumL W (v :: l) := by
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime
  have hmh : ∀ (h : MRing ι O) (e : K → ℕ), IsMultiHomog h e → divCycle P h W ≠ 0 →
      IsMultiHomogIdeal W ∧ W ∈ (P ⊔ Ideal.span {h}).minimalPrimes := by
    intro h e he hW'
    unfold divCycle at hW'
    split_ifs at hW' with hW''
    · exact ⟨MinimalPrimeMultiHomog.proof O K ι _ W
        (SupSpanMultiHomog.proof O K ι P h e hPmh he) hW''.1, hW''.1⟩
    · exact absurd rfl hW'
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
  have hWdata : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
    by_cases hWf : divCycle P f W = 0
    · have hWg : divCycle P g W ≠ 0 := by
        intro hWg; apply hW; simp [ratDiv, hWf, hWg]
      obtain ⟨hm, hmin⟩ := hmh g bg hbg hWg
      exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
    · obtain ⟨hm, hmin⟩ := hmh f bf hbf hWf
      exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
  obtain ⟨hWm, hWp, hPW⟩ := hWdata
  have := hWp
  have hlt : P < W := lt_of_le_of_ne hPW (fun e => hϖP (e ▸ hϖW))
  have hdrop := DimStrictDrop.proof (MRing ι O) P W hlt
  rw [hP.dim] at hdrop
  have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.proof O ϖ hϖ K ι W hϖW]
    have e : d + 1 + Fintype.card K = l.length + 2 + Fintype.card K := by omega
    rw [e] at hdrop
    exact lt_natCast_of_add_one_le hdrop
  have key := h3 (IsLocalRing.ResidueField O) K ι l.length (specialIdeal W)
    (SpecialIdealCorresp.proof O ϖ hϖ K ι P W hWp hϖW).1 (SpecialIdealMultiHomog.proof O K ι W hWm)
    hdim u v l.get
  rw [vNumL_cons, vNumL_cons, vNumL_cons]
  exact key
end GroundTheory.Heights₂.Heights.NumbersDVR
