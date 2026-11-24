-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommute_proof_79421367f623
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:41.281798+00:00
-- url     : https://prove2.me/submissions/8ae25fb9-7b92-427a-a9ed-c1ca92478dbd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_support_finite_6a5043317abf
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
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace VerticalDivisorsCommute
theorem _root_.solution (h1 : CutByEffectiveDivisor.Statement.{u})
    (h2 : Representative.Statement.{u}) (h3 : IntNumAddFirst.Statement.{u})
    (h4 : DivCycleFiniteSupport.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : SpecialQuotDim.Statement.{u})
    (h8 : SpecialIdealCorresp.Statement.{u}) (h9 : SpecialIdealMultiHomog.Statement.{u})
    (h10 : DimStrictDrop.Statement.{u}) : VerticalDivisorsCommute.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b b' f g f' g' hD hD' L
  obtain ⟨c', c'', hc', hc'', hb'⟩ := hD'.degrees
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime

  have hmh : ∀ (h : MRing ι O) (e : K → ℕ), IsMultiHomog h e → ∀ W, divCycle P h W ≠ 0 →
      IsMultiHomogIdeal W ∧ W ∈ (P ⊔ Ideal.span {h}).minimalPrimes ∧ IsRelevant W := by
    intro h e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨h5 O K ι _ W (h6 O K ι P h e hPmh he) hW'.1, hW'.1, hW'.2⟩
    · exact absurd rfl hW
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hTfin : {H : Ideal (MRing ι O) | (divCycle P f' H ≠ 0 ∨ divCycle P g' H ≠ 0) ∧
      (C ϖ : MRing ι O) ∉ H}.Finite :=
    ((h4 O K ι P f').union (h4 O K ι P g')).subset fun H hH => hH.1
  obtain ⟨f₁, g₁, hV₁, hrat, hT₁⟩ := h2 O ϖ hϖ K ι P b f g hP.multiProj hD hTfin.toFinset (by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    obtain ⟨hne, hϖH⟩ := hH
    rcases hne with hne | hne
    · obtain ⟨hm, hmin, hrel⟩ := hmh f' c' hc' H hne
      exact ⟨⟨hmin.1.1, hm, hrel⟩, le_sup_left.trans hmin.1.2, hϖH, f', hD'.num_not_mem, hmin⟩
    · obtain ⟨hm, hmin, hrel⟩ := hmh g' c'' hc'' H hne
      exact ⟨⟨hmin.1.1, hm, hrel⟩, le_sup_left.trans hmin.1.2, hϖH, g', hD'.den_not_mem, hmin⟩)
  have e1 := h1 O ϖ hϖ K ι P d hP b f₁ g₁ hV₁ c' f' hc' hD'.num_not_mem
    (fun H hH hϖH => hT₁ H (by rw [Set.Finite.mem_toFinset]; exact ⟨Or.inl hH, hϖH⟩)) L
  have e2 := h1 O ϖ hϖ K ι P d hP b f₁ g₁ hV₁ c'' g' hc'' hD'.den_not_mem
    (fun H hH hϖH => hT₁ H (by rw [Set.Finite.mem_toFinset]; exact ⟨Or.inr hH, hϖH⟩)) L
  rw [hrat] at e1 e2

  have hadd : ∀ W, ratDiv P f g W ≠ 0 →
      vNum W (Matrix.vecCons b' L) = vNum W (Matrix.vecCons (fun k => (c' k : ℤ)) L) -
        vNum W (Matrix.vecCons (fun k => (c'' k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    have hWdata : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · have hWg : divCycle P g W ≠ 0 := by
          intro hWg; apply hW; simp [ratDiv, hWf, hWg]
        obtain ⟨hm, hmin, -⟩ := hmh g bg hbg W hWg
        exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
      · obtain ⟨hm, hmin, -⟩ := hmh f bf hbf W hWf
        exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
    obtain ⟨hWm, hWp, hPW⟩ := hWdata
    have := hWp
    have hlt : P < W := lt_of_le_of_ne hPW (fun e => hϖP (e ▸ hϖW))
    have hdrop := h10 (MRing ι O) P W hlt
    rw [hP.dim] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [h7 O ϖ hϖ K ι W hϖW]
      have e : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K := by omega
      rw [e] at hdrop
      exact lt_natCast_of_add_one_le hdrop
    have key := h3 (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (h8 O ϖ hϖ K ι P W hWp hϖW).1 (h9 O K ι W hWm) hdim b' (fun k => (c'' k : ℤ)) L
    have hsum : b' + (fun k => (c'' k : ℤ)) = fun k => (c' k : ℤ) := by
      rw [← hb']; funext k; simp
    rw [hsum] at key
    unfold vNum
    rw [key]; ring
  have hZfin := ratDiv_support_finite h4 P f g
  calc cycEval (fun G => vNum G (Matrix.vecCons b' L)) (ratDiv P f g)
      = cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c' k : ℤ)) L)) (ratDiv P f g) -
          cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c'' k : ℤ)) L)) (ratDiv P f g) := by
        unfold cycEval
        rw [← finsum_sub_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
          (hZfin.subset (Function.support_mul_subset_left _ _))]
        refine finsum_congr fun W => ?_
        by_cases hW : ratDiv P f g W = 0
        · simp [hW]
        · beta_reduce
          rw [hadd W hW, mul_sub]
    _ = _ := by rw [e1, e2]
    _ = cycEval (fun G => vNum G (Matrix.vecCons b L)) (ratDiv P f' g') := by
        unfold cycEval
        rw [← finsum_sub_distrib ((h4 O K ι P f').subset (Function.support_mul_subset_left _ _))
          ((h4 O K ι P g').subset (Function.support_mul_subset_left _ _))]
        refine finsum_congr fun W => ?_
        rw [← sub_mul]
        change ratDiv P f' g' W * _ = ratDiv P f' g' W * _
        by_cases hW : ratDiv P f' g' W = 0
        · simp [hW]
        · beta_reduce
          rw [if_pos (hD'.vertical W hW)]
end VerticalDivisorsCommute
end GroundTheory.Heights₂.Heights.NumbersDVR
