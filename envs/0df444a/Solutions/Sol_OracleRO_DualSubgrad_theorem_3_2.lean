-- Prove2me | solution 2 for OracleRO.DualSubgrad.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:20.361753+00:00
-- url     : https://prove2.me/submissions/efb80b73-ec10-427e-81f9-ac2897d40416

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_OracleRO_DualSubgrad_Problem
import Definitions.Def_OracleRO_DualSubgrad_Algorithm1
import Theorems.Thm_OracleRO_DualSubgrad_convexity_step
import Theorems.Thm_OracleRO_DualSubgrad_eq_6
import Theorems.Thm_OracleRO_DualSubgrad_lemma_1

-- carved verbatim out of submission c349ef76-d53f-46f4-94ae-6dedae90e637, lines 304-402

section
set_option autoImplicit false

open OracleRO.DualSubgrad in
theorem p72856194_iter_mem
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O) (t : ℕ) :
    alg1X gradU P O G D ε u0 x0 t ∈ Dom := by
  cases t with
  | zero => simpa [alg1X, alg1State] using hx0
  | succ k =>
    simp only [alg1X, alg1State]
    set u' : Fin m → EuclideanSpace ℝ (Fin d) := fun i =>
      P ((alg1State gradU P O (alg1Eta G D ε) u0 x0 k).1 i + alg1Eta G D ε •
        gradU i (alg1State gradU P O (alg1Eta G D ε) u0 x0 k).2
          ((alg1State gradU P O (alg1Eta G D ε) u0 x0 k).1 i)) with hu'
    have hU : ∀ i, u' i ∈ U := fun i => (hP _).1
    rcases h : O u' with _ | x
    · simpa using hx0
    · simpa using ((hO u' hU).1 x h).1

open OracleRO.DualSubgrad in
theorem p72856194_U_mem {m n d : ℕ} (U : Set (EuclideanSpace ℝ (Fin d)))
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto U P) (t : ℕ) (ht : 1 ≤ t) (i : Fin m) :
    alg1U gradU P O G D ε u0 x0 t i ∈ U := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [alg1U, alg1State]
  exact (hP _).1

open OracleRO.DualSubgrad in
theorem solution
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hDom : Convex ℝ Dom) (hU : Convex ℝ U) (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hconv : ∀ i, ∀ u ∈ U, ConvexOn ℝ Dom (fun x => f i x u))
    (hconc : ∀ i, ∀ x ∈ Dom, ConcaveOn ℝ U (f i x))
    (hgrad : ∀ i, ∀ x ∈ Dom, ∀ u ∈ U, HasGradientAt (f i x) (gradU i x u) u)
    (hgradG : ∀ i, ∀ x ∈ Dom, ∀ u ∈ U, ‖gradU i x u‖ ≤ G)
    (hdiam : ∀ u ∈ U, ∀ v ∈ U, ‖u - v‖ ≤ D)
    (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (hu0 : ∀ i, u0 i ∈ U) (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O) :
    (alg1Output gradU P O G D ε u0 x0 = none → ¬ RobustFeasible Dom U f) ∧
    (∀ xbar, alg1Output gradU P O G D ε u0 x0 = some xbar →
      IsApproxSolution Dom U f (2 * ε) xbar) ∧
    alg1Calls gradU P O G D ε u0 x0 ≤ ⌈G ^ 2 * D ^ 2 / ε ^ 2⌉₊ := by
  have hTnat : 0 < alg1T G D ε := by
    have : 0 < G ^ 2 * D ^ 2 / ε ^ 2 := by positivity
    unfold alg1T
    exact Nat.ceil_pos.mpr this
  refine ⟨?_, ?_, ?_⟩
  · -- infeasibility branch
    intro hnone hfeas
    unfold alg1Output at hnone
    split_ifs at hnone with h
    obtain ⟨t, ht, hOt⟩ := h
    have hmem : ∀ i, alg1U gradU P O G D ε u0 x0 t i ∈ U := fun i =>
      p72856194_U_mem U gradU P O ε D G u0 x0 hP t (Finset.mem_Icc.mp ht).1 i
    obtain ⟨x, hx, hall⟩ := hfeas
    exact (hO _ hmem).2 hOt ⟨x, hx, fun i => hall i _ (hmem i)⟩
  · -- approximate solution branch
    intro xbar hout
    set T := alg1T G D ε with hTdef
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hTnat
    have hxbar : xbar = (1 / (T : ℝ)) •
        ∑ t ∈ Finset.Icc 1 T, alg1X gradU P O G D ε u0 x0 t := by
      unfold alg1Output at hout
      split_ifs at hout
      exact (Option.some.inj hout).symm
    have hXmem : ∀ t, alg1X gradU P O G D ε u0 x0 t ∈ Dom := fun t =>
      p72856194_iter_mem Dom U f gradU P O ε D G u0 x0 hP hx0 hO t
    refine ⟨?_, ?_⟩
    · rw [hxbar, Finset.smul_sum]
      refine hDom.sum_mem (fun _ _ => by positivity) ?_ (fun t _ => hXmem t)
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp only [Nat.add_sub_cancel]
      field_simp
    · intro i u hu
      have h1 := OracleRO.DualSubgrad.convexity_step Dom U f gradU P O ε D G u0 x0 hDom hP hconv hε hD hG hx0 hO
        xbar hout i u hu
      have h2 := OracleRO.DualSubgrad.eq_6 Dom U f gradU P O ε D G u0 x0 hP hε hD hG hO xbar hout i
      have h3 := OracleRO.DualSubgrad.lemma_1 U P
        (fun t => f i (alg1X gradU P O G D ε u0 x0 t))
        (fun t => gradU i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i))
        (fun t => alg1U gradU P O G D ε u0 x0 t i) T D G hU hP hTnat hD hG hdiam
        (fun t _ => hconc i _ (hXmem t))
        (fun t ht => hgrad i _ (hXmem t) _
          (p72856194_U_mem U gradU P O ε D G u0 x0 hP t (Finset.mem_Icc.mp ht).1 i))
        (fun t ht => hgradG i _ (hXmem t) _
          (p72856194_U_mem U gradU P O ε D G u0 x0 hP t (Finset.mem_Icc.mp ht).1 i))
        (p72856194_U_mem U gradU P O ε D G u0 x0 hP 1 le_rfl i)
        (by
          intro t ht
          simp only [alg1U, alg1X, alg1State, alg1Eta, hTdef])
        u hu
      -- G D √T ≤ ε T
      have hsq : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
      have hTge : G ^ 2 * D ^ 2 / ε ^ 2 ≤ (T : ℝ) := Nat.le_ceil _
      have hGD : G * D ≤ ε * Real.sqrt T := by
        have hle : (G * D) ^ 2 ≤ (ε * Real.sqrt T) ^ 2 := by
          rw [mul_pow ε, Real.sq_sqrt hTpos.le]
          rw [div_le_iff₀ (by positivity)] at hTge
          nlinarith
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hle
      have hreg : G * D * Real.sqrt T ≤ ε * T := by
        have := mul_le_mul_of_nonneg_right hGD hsq.le
        rw [mul_assoc ε, Real.mul_self_sqrt hTpos.le] at this
        exact this
      set S1 := ∑ t ∈ Finset.Icc 1 T, f i (alg1X gradU P O G D ε u0 x0 t) u
      set S2 := ∑ t ∈ Finset.Icc 1 T,
        f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i)
      have h2' : S2 ≤ ε * T := by
        rw [one_div, inv_mul_le_iff₀ hTpos] at h2; linarith
      have h1' : f i xbar u * T ≤ S1 := by
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hTpos] at h1; exact h1
      have : f i xbar u * T ≤ 2 * ε * T := by linarith
      exact le_of_mul_le_mul_right this hTpos
  · -- call count
    show alg1Calls gradU P O G D ε u0 x0 ≤ alg1T G D ε
    unfold alg1Calls
    split_ifs with h
    · exact (Nat.find_spec h).2.1
    · exact le_rfl

end
