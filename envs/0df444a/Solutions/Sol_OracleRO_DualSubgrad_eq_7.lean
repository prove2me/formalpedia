-- Prove2me | solution 1 for OracleRO.DualSubgrad.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:53:46.36698+00:00
-- url     : https://prove2.me/submissions/92cce856-0d46-4763-97f3-09a8a3af3ce2

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_OracleRO_DualSubgrad_Problem
import Definitions.Def_OracleRO_DualSubgrad_Algorithm1



namespace OracleRO.DualSubgrad

open Set

lemma h19_proj_le {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))} (hPc : Convex ℝ U)
    {y z u : EuclideanSpace ℝ (Fin d)} (hzP : z ∈ U)
    (hmin : ∀ w ∈ U, ‖z - y‖ ≤ ‖w - y‖)
    (hu : u ∈ U) : ‖z - u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
  have key : 0 ≤ inner ℝ (z - y) (u - z) := by
    by_contra hneg
    push_neg at hneg
    set c := inner ℝ (z - y) (u - z) with hcdef
    have hne : u - z ≠ 0 := by
      intro h; rw [h, inner_zero_right] at hcdef; linarith
    set q := ‖u - z‖ ^ 2 with hqdef
    have hq : 0 < q := by positivity
    set s := min 1 (-c / q) with hsdef
    have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) hq)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hsq : s * q ≤ -c := by
      have := min_le_right 1 (-c / q)
      rw [← hsdef] at this
      calc s * q ≤ (-c / q) * q := mul_le_mul_of_nonneg_right this hq.le
        _ = -c := by field_simp
    have hw : z + s • (u - z) ∈ U := hPc.add_smul_sub_mem hzP hu ⟨hs0.le, hs1⟩
    have h1 := hmin _ hw
    have h2 : ‖z - y‖ ^ 2 ≤ ‖z + s • (u - z) - y‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e : z + s • (u - z) - y = (z - y) + s • (u - z) := by abel
    rw [e, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0,
      mul_pow, ← hcdef, ← hqdef] at h2
    nlinarith
  have e : y - u = (y - z) + (z - u) := by abel
  rw [e, norm_add_sq_real]
  have : inner ℝ (y - z) (z - u) = inner ℝ (z - y) (u - z) := by
    rw [← inner_neg_neg, neg_sub, neg_sub]
  rw [this]
  nlinarith [norm_nonneg (y - z)]

lemma h19_grad_ineq {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hc : ConcaveOn ℝ U h)
    {g v u : EuclideanSpace ℝ (Fin d)} (hv : v ∈ U) (hu : u ∈ U)
    (hg : HasGradientAt h g v) :
    h u - h v ≤ inner ℝ g (u - v) := by
  have hl : HasDerivAt (fun s : ℝ => v + s • (u - v)) (u - v) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (u - v)).const_add v
  have hf : HasFDerivAt h (InnerProductSpace.toDual ℝ _ g).toContinuousLinearMap v := hg
  have hder : HasDerivAt (fun s : ℝ => h (v + s • (u - v))) (inner ℝ g (u - v)) 0 := by
    have hf' : HasFDerivAt h (InnerProductSpace.toDual ℝ _ g).toContinuousLinearMap
        (v + (0:ℝ) • (u - v)) := by simpa using hf
    have := hf'.comp_hasDerivAt (0:ℝ) hl
    have e : (InnerProductSpace.toDual ℝ _ g).toContinuousLinearMap (u - v) = inner ℝ g (u - v) := by
      simp [InnerProductSpace.toDual_apply_apply]
    rw [e] at this
    exact this
  have hs := hder.tendsto_slope_zero_right
  simp only [zero_add, smul_eq_mul, zero_smul, add_zero] at hs
  have hle : ∀ t ∈ Set.Ioo (0:ℝ) 1, h u - h v ≤ t⁻¹ * (h (v + t • (u - v)) - h v) := by
    intro t ht
    have hconv := hc.2 hv hu (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)
      ht.1.le (by ring)
    have e : (1 - t) • v + t • u = v + t • (u - v) := by module
    rw [e, smul_eq_mul, smul_eq_mul] at hconv
    rw [le_inv_mul_iff₀ ht.1]
    linarith
  exact ge_of_tendsto hs (by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    exact hle t ht)

lemma h19_regret {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))} (hU : Convex ℝ U)
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (η G D : ℝ) (hη : 0 < η)
    (a g : ℕ → EuclideanSpace ℝ (Fin d)) (φ ψ : ℕ → ℝ)
    (haU : ∀ t, a t ∈ U) (hstep : ∀ t, a (t + 1) = P (a t + η • g t))
    (hg : ∀ t, ‖g t‖ ≤ G) (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ U)
    (hin : ∀ t, φ t - ψ t ≤ inner ℝ (g t) (u - a t))
    (hdiam : ‖a 1 - u‖ ≤ D) (T : ℕ) :
    2 * η * ∑ t ∈ Finset.Icc 1 T, (φ t - ψ t) ≤ D ^ 2 + T * (η ^ 2 * G ^ 2) := by
  have step : ∀ t, 2 * η * (φ t - ψ t) ≤ ‖a t - u‖ ^ 2 - ‖a (t + 1) - u‖ ^ 2 + η ^ 2 * G ^ 2 := by
    intro t
    have hproj := h19_proj_le hU (y := a t + η • g t) (z := a (t + 1)) (by rw [hstep t]; exact (hP _).1)
      (by
        intro w hw
        rw [hstep t, norm_sub_rev, norm_sub_rev w]
        exact (hP _).2 w hw) hu
    have ex : a t + η • g t - u = (a t - u) + η • g t := by abel
    rw [ex, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hη, mul_pow, real_inner_comm] at hproj
    have hg2 : ‖g t‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hg t) 2
    have hi := hin t
    have hi' : inner ℝ (g t) (a t - u) = - inner ℝ (g t) (u - a t) := by
      rw [← inner_neg_right, neg_sub]
    rw [hi'] at hproj
    have := mul_le_mul_of_nonneg_left hi hη.le
    nlinarith [sq_nonneg η, mul_le_mul_of_nonneg_left hg2 (sq_nonneg η)]
  have key : ∀ T : ℕ, 2 * η * ∑ t ∈ Finset.Icc 1 T, (φ t - ψ t) ≤
      ‖a 1 - u‖ ^ 2 - ‖a (T + 1) - u‖ ^ 2 + T * (η ^ 2 * G ^ 2) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_Icc_succ_top (by omega), mul_add]
      have := step (T + 1)
      push_cast
      nlinarith
  have h1 := key T
  have h2 : ‖a 1 - u‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdiam 2
  nlinarith [sq_nonneg ‖a (T + 1) - u‖]

lemma h19_alg_props {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n)))
    (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε : ℝ) (η : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hu0 : ∀ i, u0 i ∈ U) (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O) :
    ∀ t, (∀ i, (alg1State gradU P O η u0 x0 t).1 i ∈ U) ∧ (alg1State gradU P O η u0 x0 t).2 ∈ Dom := by
  intro t
  induction t with
  | zero => exact ⟨hu0, hx0⟩
  | succ t ih =>
    have hu' : ∀ i, (alg1State gradU P O η u0 x0 (t + 1)).1 i ∈ U := by
      intro i
      simp only [alg1State]
      exact (hP _).1
    refine ⟨hu', ?_⟩
    simp only [alg1State]
    cases hOo : O (fun i => P ((alg1State gradU P O η u0 x0 t).1 i + η •
        gradU i (alg1State gradU P O η u0 x0 t).2 ((alg1State gradU P O η u0 x0 t).1 i))) with
    | none => simpa using hx0
    | some x =>
      have := (hO _ (fun i => (hP _).1)).1 x hOo
      simpa using this.1

lemma h19_core {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hU : Convex ℝ U) (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hconc : ∀ i, ∀ x ∈ Dom, ConcaveOn ℝ U (f i x))
    (hgrad : ∀ i, ∀ x ∈ Dom, ∀ u ∈ U, HasGradientAt (f i x) (gradU i x u) u)
    (hgradG : ∀ i, ∀ x ∈ Dom, ∀ u ∈ U, ‖gradU i x u‖ ≤ G)
    (hdiam : ∀ u ∈ U, ∀ v ∈ U, ‖u - v‖ ≤ D)
    (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (hu0 : ∀ i, u0 i ∈ U) (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O) :
    ∀ i, ∀ u ∈ U,
      (1 / (alg1T G D ε : ℝ)) * ∑ t ∈ Finset.Icc 1 (alg1T G D ε),
          f i (alg1X gradU P O G D ε u0 x0 t) u
        - (1 / (alg1T G D ε : ℝ)) * ∑ t ∈ Finset.Icc 1 (alg1T G D ε),
          f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i)
        ≤ G * D / Real.sqrt (alg1T G D ε) ∧
      G * D / Real.sqrt (alg1T G D ε) ≤ ε := by
  intro i u hu
  set T := alg1T G D ε with hT
  have hTpos : (0 : ℝ) < T := by
    rw [hT, alg1T]
    exact_mod_cast Nat.ceil_pos.2 (by positivity)
  have hTge : G ^ 2 * D ^ 2 / ε ^ 2 ≤ (T : ℝ) := Nat.le_ceil _
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hsq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hTpos.le
  have hη : 0 < alg1Eta G D ε := by
    rw [alg1Eta]; positivity
  have hprops := h19_alg_props Dom U f gradU P O ε (alg1Eta G D ε) u0 x0 hP hu0 hx0 hO
  have hreg := h19_regret hU hP (alg1Eta G D ε) G D hη
    (fun t => alg1U gradU P O G D ε u0 x0 t i)
    (fun t => gradU i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i))
    (fun t => f i (alg1X gradU P O G D ε u0 x0 t) u)
    (fun t => f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i))
    (fun t => (hprops t).1 i)
    (fun t => rfl)
    (fun t => hgradG i _ ((hprops t).2) _ ((hprops t).1 i))
    u hu
    (fun t => h19_grad_ineq _ (hconc i _ (hprops t).2) ((hprops t).1 i) hu
      (hgrad i _ (hprops t).2 _ ((hprops t).1 i)))
    (hdiam _ ((hprops 1).1 i) _ hu) T
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hTe : (T : ℝ) = Real.sqrt T * Real.sqrt T := hsq.symm
  have hηe : alg1Eta G D ε = D / (G * Real.sqrt T) := rfl
  have hbound : (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, (f i (alg1X gradU P O G D ε u0 x0 t) u -
      f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i)) ≤
      G * D / Real.sqrt T := by
    set S := ∑ t ∈ Finset.Icc 1 T, (f i (alg1X gradU P O G D ε u0 x0 t) u -
      f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i)) with hS
    rw [hηe] at hreg
    have h3 : S ≤ G * D * Real.sqrt T := by
      have hpos : 0 < D / (G * Real.sqrt T) := by positivity
      have : 2 * (D / (G * Real.sqrt T)) * S ≤ 2 * (D / (G * Real.sqrt T)) * (G * D * Real.sqrt T) := by
        refine hreg.trans (le_of_eq ?_)
        have aux : ∀ s : ℝ, 0 < s → (T : ℝ) = s * s →
            D ^ 2 + (T : ℝ) * ((D / (G * s)) ^ 2 * G ^ 2) = 2 * (D / (G * s)) * (G * D * s) := by
          intro s hs hTs
          rw [hTs]
          field_simp
          ring
        exact aux _ hsT hTe
      exact le_of_mul_le_mul_left this (by positivity)
    rw [one_div, inv_mul_eq_div, div_le_div_iff₀ hTpos hsT]
    have h5 := mul_le_mul_of_nonneg_right h3 hsT.le
    have h6 : G * D * Real.sqrt T * Real.sqrt T = G * D * T := by rw [mul_assoc _ (Real.sqrt T), hsq]
    linarith
  refine ⟨hbound, ?_⟩
  rw [div_le_iff₀ hsT]
  have h4 : G * D / ε ≤ Real.sqrt T := by
    apply Real.le_sqrt_of_sq_le
    calc (G * D / ε) ^ 2 = G ^ 2 * D ^ 2 / ε ^ 2 := by ring
      _ ≤ (T : ℝ) := hTge
  rw [div_le_iff₀ hε] at h4
  nlinarith

end OracleRO.DualSubgrad

open OracleRO.DualSubgrad


theorem solution
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hU : Convex ℝ U) (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hconc : ∀ i, ∀ x ∈ Dom, ConcaveOn ℝ U (f i x))
    (hgrad : ∀ i, ∀ x ∈ Dom, ∀ u ∈ U, HasGradientAt (f i x) (gradU i x u) u)
    (hgradG : ∀ i, ∀ x ∈ Dom, ∀ u ∈ U, ‖gradU i x u‖ ≤ G)
    (hdiam : ∀ u ∈ U, ∀ v ∈ U, ‖u - v‖ ≤ D)
    (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (hu0 : ∀ i, u0 i ∈ U) (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O) :
    ∀ i, ∀ u ∈ U,
      (1 / (alg1T G D ε : ℝ)) * ∑ t ∈ Finset.Icc 1 (alg1T G D ε),
          f i (alg1X gradU P O G D ε u0 x0 t) u
        - (1 / (alg1T G D ε : ℝ)) * ∑ t ∈ Finset.Icc 1 (alg1T G D ε),
          f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i)
        ≤ G * D / Real.sqrt (alg1T G D ε) ∧
      G * D / Real.sqrt (alg1T G D ε) ≤ ε := by
  exact h19_core Dom U f gradU P O ε D G u0 x0 hU hP hconc hgrad hgradG hdiam hε hD hG hu0 hx0 hO
