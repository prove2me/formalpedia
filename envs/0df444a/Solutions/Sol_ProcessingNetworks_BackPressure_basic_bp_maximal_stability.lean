-- Prove2me | solution 1 for ProcessingNetworks.BackPressure.basic_bp_maximal_stability
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:33:36.322517+00:00
-- url     : https://prove2.me/submissions/bdd21867-82ea-44be-9b74-b8d5edd7d8d7

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope
import Definitions.Def_ProcessingNetworks_BackPressure_RegularPoint
import Definitions.Def_ProcessingNetworks_BackPressure_FluidModelSolution

open MeasureTheory Filter

namespace ProcessingNetworks.BackPressure.BasicBPCE

open ProcessingNetworks.BackPressure

noncomputable def dat : SPNPlanningData 2 2 2 :=
  { B := !![1, 1; 0, 0], Γ := !![2, 0; -1, 0], m := fun _ => 1, hm := fun _ => one_pos,
    A := 1, b := fun _ => 1, hb := fun _ => one_pos }

theorem R_eq : dat.R = !![-1, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [SPNPlanningData.R, dat]

theorem p_eq (β z : Fin 2 → ℝ) : p dat β z = z 0 * (-β 0 + β 1) + z 1 * β 0 := by
  simp [p, R_eq, dotProduct, Fin.sum_univ_two, Matrix.mulVec]

theorem hleon : IsLeontiefNetwork dat := by
  refine ⟨fun j => ?_, ⟨![1, 2], fun j => by fin_cases j <;> norm_num, fun i => ?_⟩⟩
  · fin_cases j
    · refine ⟨1, by simp [R_eq], fun i hi => ?_⟩
      fin_cases i
      · simp [R_eq] at hi; linarith
      · rfl
    · refine ⟨0, by simp [R_eq], fun i hi => ?_⟩
      fin_cases i
      · rfl
      · simp [R_eq] at hi
  · fin_cases i <;> simp [R_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

theorem hopt : IsOptimalSPPValue dat 0 0 := by
  refine ⟨⟨0, by simp, fun _ => le_refl _, fun k => by simp [dat]⟩, fun γ ⟨x, _, hx, hA⟩ => ?_⟩
  have := hA 0
  simp [dat, Matrix.one_mulVec] at this
  linarith [hx 0]

noncomputable def N : Finset (Fin 2 → ℝ) := {![0, 0], ![1, 0], ![0, 1], ![1, 1]}

theorem ext2 {a b : Fin 2 → ℝ} (h0 : a 0 = b 0) (h1 : a 1 = b 1) : a = b := by
  funext i; fin_cases i; exact h0; exact h1

theorem hN (β : Fin 2 → ℝ) :
    β ∈ N ↔ (∀ j, β j = 0 ∨ β j = 1) ∧ ∀ k, ∑ j, dat.A k j * β j ≤ 1 := by
  constructor
  · intro h
    simp only [N, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl <;>
    · refine ⟨fun j => by fin_cases j <;> simp, fun k => ?_⟩
      fin_cases k <;> simp [dat, Fin.sum_univ_two, Matrix.one_apply]
  · rintro ⟨h01, -⟩
    simp only [N, Finset.mem_insert, Finset.mem_singleton]
    rcases h01 0 with a | a <;> rcases h01 1 with b | b
    · left; exact ext2 (by simp [a]) (by simp [b])
    · right; right; left; exact ext2 (by simp [a]) (by simp [b])
    · right; left; exact ext2 (by simp [a]) (by simp [b])
    · right; right; right; exact ext2 (by simp [a]) (by simp [b])

noncomputable def Zraw (x : ℕ) (_ : ℝ) (_ : ℝ) : Fin 2 → ℕ := ![0, x]

noncomputable def Yraw (β : Fin 2 → ℝ) (_ : ℕ) (u : ℝ) (_ : ℝ) : ℝ :=
  if β = 0 then max u 0 else 0

noncomputable def Yh (β : Fin 2 → ℝ) (t : ℝ) : ℝ := if β = 0 then max t 0 else 0

theorem zero_mem : (0 : Fin 2 → ℝ) ∈ N := by
  simp only [N, Finset.mem_insert]; left; exact ext2 (by simp) (by simp)

end ProcessingNetworks.BackPressure.BasicBPCE

open ProcessingNetworks.BackPressure in
theorem solution : ¬ (∀ {Xstate : Type} [Countable Xstate] {Ω : Type} [MeasureSpace Ω] {I J K : ℕ}
    (dat : SPNPlanningData I J K) (hleontief : IsLeontiefNetwork dat)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (hb1 : ∀ k : Fin K, dat.b k = 1)
    (hA01 : ∀ j : Fin J, ∃! k : Fin K, dat.A k j = 1 ∧ ∀ k' : Fin K, k' ≠ k → dat.A k' j = 0)
    (lam : Fin I → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (γstar : ℝ) (hopt : IsOptimalSPPValue dat lam γstar) (hsub : γstar < 1)
    (N : Finset (Fin J → ℝ))
    (hN : ∀ β : Fin J → ℝ, β ∈ N ↔ (∀ j, β j = 0 ∨ β j = 1) ∧ ∀ k, ∑ j, dat.A k j * β j ≤ 1)
    (Nraw : Xstate → ℝ → Ω → Fin J → ℕ) (Zraw : Xstate → ℝ → Ω → Fin I → ℕ)
    (Traw : Xstate → ℝ → Ω → Fin J → ℝ) (Yraw : (Fin J → ℝ) → Xstate → ℝ → Ω → ℝ)
    (vhat : Fin J → Xstate → ℝ → Ω → ℝ) (uhat : Fin I → Xstate → ℝ → Ω → ℝ)
    (size : Xstate → ℝ) (size_nonneg : ∀ x, 0 ≤ size x)
    (hTY : ∀ x ω t j, Traw x t ω j = ∑ β ∈ N, β j * Yraw β x t ω)
    (hYmono : ∀ β ∈ N, ∀ x ω, Monotone (Yraw β x · ω))
    (hYsum : ∀ x ω t, 0 ≤ t → ∑ β ∈ N, Yraw β x t ω = t)
    (hBP : ∀ β ∈ N, ∀ βstar ∈ N, ∀ (x : Xstate) (ω : Ω) (u1 u2 : ℝ), 0 ≤ u1 → u1 ≤ u2 →
      (∀ u ∈ Set.Icc u1 u2,
        p dat β (fun i => (Zraw x u ω i : ℝ)) < p dat βstar (fun i => (Zraw x u ω i : ℝ))) →
      (∀ u ∈ Set.Icc u1 u2,
        BPFeasible dat (Nraw x u ω) (Zraw x u ω) β → BPFeasible dat (Nraw x u ω) (Zraw x u ω) βstar) →
      Yraw β x u2 ω - Yraw β x u1 ω ≤ (⨆ j, vhat j x u1 ω) + (⨅ i, uhat i x u1 ω))
    (ω : Ω) (x : ℕ → Xstate) (hsize : Tendsto (fun n => size (x n)) atTop atTop)
    (hres_v : ∀ (j : Fin J) (s : ℝ), 0 < s →
      Tendsto (fun n => (size (x n))⁻¹ * vhat j (x n) (size (x n) * s) ω) atTop (nhds 0))
    (hres_u : ∀ (i : Fin I) (s : ℝ), 0 < s →
      Tendsto (fun n => (size (x n))⁻¹ * uhat i (x n) (size (x n) * s) ω) atTop (nhds 0))
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) (Yh : (Fin J → ℝ) → ℝ → ℝ)
    (hsol : IsFluidModelSolution dat lam Dh Fh Th Zh)
    (hZconv :
      UOCConverges (fun n t i => (size (x n))⁻¹ * (Zraw (x n) (size (x n) * t) ω i : ℝ)) Zh)
    (hTconv :
      UOCConverges (fun n t j => (size (x n))⁻¹ * Traw (x n) (size (x n) * t) ω j) Th)
    (hYconv : ∀ β ∈ N,
      UOCConvergesR (fun n t => (size (x n))⁻¹ * Yraw β (x n) (size (x n) * t) ω) (Yh β)),
    IsRelaxedBPFluidSolution dat lam Dh Fh Th Zh ∧ RelaxedBPFluidStable dat lam) := by
  intro h
  open BasicBPCE in
  have hsol : IsFluidModelSolution dat 0 (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun _ => ![0, 1]) := by
    refine ⟨fun t _ i => by simp, fun t _ i => by fin_cases i <;> simp, fun t _ i => by simp,
      fun t _ j => by simp, ⟨rfl, fun _ _ _ => le_refl _⟩, fun s t _ hst k => ?_⟩
    simp [dat]; linarith
  open BasicBPCE in
  have key := h (Xstate := ℕ) (Ω := ℝ) dat hleon
    (fun k j => by fin_cases k <;> fin_cases j <;> simp [dat])
    (fun j => ⟨j, by simp [dat]⟩) (fun _ => rfl)
    (fun j => ⟨j, ⟨by simp [dat], fun k' hk' => by simp [dat, Matrix.one_apply, hk']⟩,
      fun k hk => by
        by_contra hne
        have := hk.2 j (Ne.symm hne)
        simp [dat] at this⟩)
    0 (fun _ => le_refl _) 0 hopt one_pos N hN
    (fun _ _ _ => 0) Zraw (fun _ _ _ => 0) Yraw (fun _ _ _ _ => 0) (fun _ _ _ _ => 0)
    (fun n => (n : ℝ)) (fun n => Nat.cast_nonneg n)
    (fun x ω t j => by
      refine (Finset.sum_eq_zero fun β _ => ?_).symm
      unfold Yraw; split_ifs with hβ
      · rw [hβ]; simp
      · simp)
    (fun β _ x ω a b hab => by
      unfold Yraw; split_ifs
      · exact max_le_max hab le_rfl
      · exact le_rfl)
    (fun x ω t ht => by
      unfold Yraw
      rw [Finset.sum_ite_eq' N 0 (fun β => max t 0), if_pos zero_mem, max_eq_left ht])
    (fun β _ βstar hβs x ω u1 u2 hu1 hu12 hlt hfeas => by
      by_cases hβ : β = 0
      · exfalso
        subst hβ
        have h1 := hlt u1 ⟨le_rfl, hu12⟩
        rw [p_eq, p_eq] at h1
        simp [Zraw] at h1
        have hfe : BPFeasible dat (0 : Fin 2 → ℕ) (Zraw x u1 ω) 0 :=
          ⟨⟨fun j => le_refl (0 : ℝ), fun k => by simp [dat]⟩, fun i => by
            simp [serviceInitiation]; fin_cases i <;> simp [Zraw]⟩
        have hs := (hfeas u1 ⟨le_rfl, hu12⟩ hfe).2 0
        have hpos : 0 < βstar 0 := by
          rcases ((hN βstar).mp hβs).1 0 with h0 | h0
          · rw [h0] at h1; simp at h1
          · rw [h0]; exact one_pos
        have hu0 : serviceInitiation 0 βstar 0 = 1 := by
          simp [serviceInitiation, hpos]
        have hu1 : 0 ≤ serviceInitiation 0 βstar 1 := by
          unfold serviceInitiation; split_ifs <;> norm_num
        simp [dat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Zraw, hu0] at hs
        linarith
      · simp [Yraw, hβ])
    0 (fun n : ℕ => n + 1)
    (by
      simp only [Nat.cast_add, Nat.cast_one]
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    (fun j s _ => by simp only [mul_zero]; exact tendsto_const_nhds)
    (fun i s _ => by simp only [mul_zero]; exact tendsto_const_nhds)
    _ _ _ _ Yh hsol
    (fun Tb _ ε hε => ⟨0, fun n _ t _ i => by
      fin_cases i
      · simp [Zraw, hε]
      · have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
        simp [Zraw, hn, hε]⟩)
    (fun Tb _ ε hε => ⟨0, fun n _ t _ j => by simp [hε]⟩)
    (fun β _ Tb _ ε hε => ⟨0, fun n _ t ht => by
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      unfold Yraw Yh
      beta_reduce
      split_ifs
      · rw [max_eq_left (mul_nonneg (Nat.cast_nonneg _) ht.1), max_eq_left ht.1, ← mul_assoc, inv_mul_cancel₀ hn,
          one_mul, sub_self, abs_zero]; exact hε
      · simp [hε]⟩)
  have hz := key.1.2 1 one_pos
    ⟨differentiableAt_const _, differentiableAt_const _, differentiableAt_const _,
      differentiableAt_const _⟩ 0 (hasDerivAt_const _ _)
  have hα : (![1, 0] : Fin 2 → ℝ) ∈ AllocationPolytope BasicBPCE.dat :=
    ⟨fun j => by fin_cases j <;> simp, fun k => by
      fin_cases k <;> simp [BasicBPCE.dat, Matrix.one_mulVec]⟩
  have := hz.2 _ hα
  rw [BasicBPCE.p_eq, BasicBPCE.p_eq] at this
  norm_num at this


