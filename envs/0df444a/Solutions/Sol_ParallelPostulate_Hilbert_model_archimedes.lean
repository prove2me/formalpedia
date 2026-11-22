-- Prove2me | solution 1 for ParallelPostulate.Hilbert.model_archimedes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:17:20.89437+00:00
-- url     : https://prove2.me/submissions/84bae827-e0fc-41b6-a1e4-d074caf5f509

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate
public import Theorems.Thm_ParallelPostulate_Hilbert_archimedes_of_length
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_ne
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_sq_add_sq_pos


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Hilbert
open Pairs HyperbolicPlane
namespace ParallelPostulate.Hilbert
theorem _root_.solution (κ : ℝ) (hκ : κ ≤ 0) : (model κ hκ).Archimedes := by
  rcases hκ.lt_or_eq with h | rfl
  · have hk : 0 < √(-κ) := Real.sqrt_pos.mpr (neg_pos.mpr h)
    apply archimedes_of_length hκ (kleinDist κ)
    · intro P Q R S hP hQ hR hS
      exact apart_eq_iff_kleinDist_eq h hP hQ hR hS
    · intro A B C hA hC hABC
      exact (kleinDist_add_of_between h hA hC hABC).2
    · intro P Q hP hQ hPQ
      exact kleinDist_pos h hP hQ hPQ
    · intro P hP
      rw [kleinDist_eq_arsinh h hP hP, apart_self]
      simp
    · intro O D hO hOD d hd
      have hsinh : 0 < Real.sinh (√(-κ) * d) := Real.sinh_pos_iff.mpr (mul_pos hk hd)
      obtain ⟨t, ht, hX, hap⟩ := exists_onRay_apart h hO hOD
        (α := Real.sinh (√(-κ) * d) ^ 2 / (-κ)) (div_pos (by positivity) (neg_pos.mpr h))
      refine ⟨t, ht, hX, ?_⟩
      have e : -κ * (Real.sinh (√(-κ) * d) ^ 2 / (-κ)) = Real.sinh (√(-κ) * d) ^ 2 := by
        field_simp [h.ne]
      rw [kleinDist_eq_arsinh h hO hX, hap, e, Real.sqrt_sq hsinh.le, Real.arsinh_sinh]
      field_simp
  · apply archimedes_of_length hκ (fun P Q => √(apart 0 P Q))
    · intro P Q R S _ _ _ _
      exact (Real.sqrt_inj (apart_zero_nonneg _ _) (apart_zero_nonneg _ _)).symm
    · intro A B C _ _ hABC
      exact euclid_sqrt_apart_add hABC
    · intro P Q hP hQ hPQ
      exact Real.sqrt_pos.mpr (apart_pos hP hQ hPQ)
    · intro P _
      simp [apart_self]
    · intro O D _ hOD d hd
      have hV : 0 < (D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2 := by
        have hne : ((D.1 - O.1, D.2 - O.2) : ℝ × ℝ) ≠ (0, 0) := by
          intro e
          apply hOD
          have h1 := congrArg Prod.fst e
          have h2 := congrArg Prod.snd e
          simp only [] at h1 h2
          exact Prod.ext (by linarith) (by linarith)
        exact sq_add_sq_pos hne
      have hsV := Real.sqrt_pos.mpr hV
      refine ⟨d / √((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2), div_pos hd hsV, mem_plane_zero _, ?_⟩
      have e : apart 0 O ((Dim.mk O D).pt (d / √((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)))
          = (d / √((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)) ^ 2
            * ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2) := by
        rw [apart_zero_bound]
        simp only [Dim.pt]
        ring
      change √(apart 0 O _) = d
      rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_pos hd hsV).le]
      field_simp
end ParallelPostulate.Hilbert
