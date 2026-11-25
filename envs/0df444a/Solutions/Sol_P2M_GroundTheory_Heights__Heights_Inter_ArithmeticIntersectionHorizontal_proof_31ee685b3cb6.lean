-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_proof_31ee685b3cb6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:10:11.977224+00:00
-- url     : https://prove2.me/submissions/b9e64172-fc2d-4c47-a068-5a8d48479ed4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalImageZ
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_isHorizontal_imageZ_419052dac111
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_dim_eq_a8c8db789c89
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_mem_minimalPrimes_6f9a6b133d70
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_isMultiHomog_rename_9fe74e305f65

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open ArithmeticIntersectionHorizontal
namespace GroundTheory.Heights₂.Heights.Inter
namespace ArithmeticIntersectionHorizontal
theorem _root_.solution (hDiv : DivSuppArithStatement) (hIm : ImageArithStatement)
    (hP0 : GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.Statement) : ArithmeticIntersectionHorizontal.Statement := by
  intro I hI n hn K _ ι _ K' _ ι' _ κ v P' L L' s α W' hv hP' hP hL hLL' hs hsP hW' hh
  classical

  let A : HermLine ι := HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) (fun k => (α k : ℤ))
  let A' : HermLine ι' :=
    HermLine.ofMetrics (fun k => maxMetric ℂ (ι' k)) (fun k => ((Function.extend κ α 0 : K' → ℕ) k : ℤ))
  have hsec : IsSectionOn (imageZ v P') A s := ⟨α, fun _ => rfl, hs, hsP⟩
  have hsec' : IsSectionOn P' A' (rename v s) :=
    ⟨Function.extend κ α 0, fun _ => rfl, isMultiHomog_rename hv hs, fun h => hsP (Ideal.mem_comap.mpr h)⟩
  have hW'n : IsArithVar W' n := (hDiv K' ι' P' n A' (rename v s) W' hP' hsec' hW').1 hh
  have hhQ : IsHorizontal (imageZ v W') := isHorizontal_imageZ hh
  obtain ⟨d, hdn, hQd⟩ := hIm K ι K' ι' κ v W' n hP.1 hv hW'n
  rcases hdn.lt_or_eq with hlt | heq
  ·
    right
    refine ⟨fun hm => ?_, hP0 I hI K ι K' ι' κ v W' d n L L' hv hW'n hQd hlt hL hLL'⟩
    have := dim_eq hQd ((hDiv K ι (imageZ v P') n A s _ hP hsec hm).1 hhQ)
    omega
  ·
    left
    rw [heq] at hQd
    have hle := hW'.1.1.2
    have hm : imageZ v W' ∈ divSupp (imageZ v P') s := by
      refine ⟨mem_minimalPrimes hQd ?_ fun M hM hMr hMh => (hDiv K ι (imageZ v P') n A s M hP hsec ⟨hM, hMr⟩).1 hMh,
        hQd.2.1.2.2⟩
      refine sup_le (Ideal.comap_mono (le_sup_left.trans hle)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_comap.mpr (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact ⟨hm, fun G' J' hJ' => hn K ι K' ι' κ v W' G' J' L L' hv hW'n hQd hJ' hL hLL'⟩
end ArithmeticIntersectionHorizontal
end GroundTheory.Heights₂.Heights.Inter
