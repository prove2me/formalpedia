-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_proof_dadec741dbcb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:55.940042+00:00
-- url     : https://prove2.me/submissions/647adda0-d4b7-4170-80a4-a5a807305692

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormMinimalFactorPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermMinimalPolynomialDivides
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreCentredEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormRemainder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormMinimalFactorPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_coeff_analyticAt_b57ea1c05d56
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_C_mem_8979057cbcb7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_X_mem_db6226df2a96
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_eval__eq_zero_of_dvd_aea6d61b0052
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_cleared_eq_23e1a1101028
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_linear_apply_eq_sum_2971557c4b0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormMinimalFactorPoints_roots_near_centred_36b26e525c3f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimitiveFormMinimalFactorPoints
open Topology Filter Polynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimitiveFormMinimalFactorPoints
theorem _root_.solution (hMin : GermMinimalPolynomialDivides.Statement) (hCen : FiniteFibreCentredEquation.Statement)
    (hRem : PrimitiveFormRemainder.Statement) : PrimitiveFormMinimalFactorPoints.Statement := by
  classical
  intro σ _ Y w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδne hp hsep hrel
  obtain ⟨n, b, hb, hmX, hdiv⟩ := hMin σ Y w d A hX hirr hiso hinj ℓ (ℓ.analyticAt w)
  choose nW cW hcW hcW0 hWX using fun i : σ =>
    hCen σ Y w d A hX hiso (fun z => z i) ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  obtain ⟨V, K, f, hVo, hwV, hf, hXV⟩ := hX
  choose M R hR hRz using fun k : Fin K => hRem σ w d A ℓ N δ q nW cW (f k) hδ hq hcW hcW0 (hf k w hwV)
  set ev : (Fin d → ℂ) → ((Fin d → ℂ) → ℂ) →+* ℂ := fun y => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y with hev
  have hevC : ∀ y (g : (Fin d → ℂ) → ℂ), ev y g = g y := fun _ _ => rfl
  set e : σ → σ → ℂ := fun i j => if i = j then 1 else 0 with he

  set Q : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i => ∑ j, C (q i j) * X ^ (j : ℕ) with hQdef
  have hQ : ∀ i, Q i ∈ liftsRing (anSub (A w)).subtype := fun i =>
    Subring.sum_mem _ fun j _ => Subring.mul_mem _ (C_mem (hq i j)) (Subring.pow_mem _ (X_mem _) _)
  have hQe : ∀ i y t, (Q i).eval₂ (ev y) t = ∑ j, q i j y * t ^ (j : ℕ) := by
    intro i y t; simp [hQdef, eval₂_finsetSum, hevC]
  have hproj : ∀ r : Fin d, AnalyticAt ℂ (fun y : Fin d → ℂ => y r) (A w) := fun r =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) r).analyticAt _
  set Ep : Polynomial ((Fin d → ℂ) → ℂ) := X ^ N + ∑ j, C (a j) * X ^ (j : ℕ) with hEp
  set EA : Fin d → Polynomial ((Fin d → ℂ) → ℂ) := fun r =>
    ∑ i, C (fun _ => A (e i) r) * Q i - C (fun y => δ y * y r) with hEA
  set El : Polynomial ((Fin d → ℂ) → ℂ) := ∑ i, C (fun _ => ℓ (e i)) * Q i - C δ * X with hEl
  set EW : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i =>
    Q i ^ nW i + ∑ j, C (fun y => cW i j y * δ y ^ (nW i - j)) * Q i ^ (j : ℕ) with hEW
  have hEpc : Ep ∈ liftsRing (anSub (A w)).subtype :=
    Subring.add_mem _ (Subring.pow_mem _ (X_mem _) _)
      (Subring.sum_mem _ fun j _ => Subring.mul_mem _ (C_mem (ha j)) (Subring.pow_mem _ (X_mem _) _))
  have hEAc : ∀ r, EA r ∈ liftsRing (anSub (A w)).subtype := fun r =>
    Subring.sub_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (C_mem analyticAt_const) (hQ i))
      (C_mem (hδ.mul (hproj r)))
  have hElc : El ∈ liftsRing (anSub (A w)).subtype :=
    Subring.sub_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (C_mem analyticAt_const) (hQ i))
      (Subring.mul_mem _ (C_mem hδ) (X_mem _))
  have hEWc : ∀ i, EW i ∈ liftsRing (anSub (A w)).subtype := fun i =>
    Subring.add_mem _ (Subring.pow_mem _ (hQ i) _) (Subring.sum_mem _ fun j _ =>
      Subring.mul_mem _ (C_mem ((hcW i j).mul (hδ.pow _))) (Subring.pow_mem _ (hQ i) _))

  have hEpe : ∀ y t, Ep.eval₂ (ev y) t = t ^ N + ∑ j, a j y * t ^ (j : ℕ) := by
    intro y t; simp [hEp, eval₂_finsetSum, hevC]
  have hEAe : ∀ r y t, (EA r).eval₂ (ev y) t = ∑ i, A (e i) r * ∑ j, q i j y * t ^ (j : ℕ) - δ y * y r := by
    intro r y t; simp [hEA, eval₂_finsetSum, hevC, hQe]
  have hEle : ∀ y t, El.eval₂ (ev y) t = ∑ i, ℓ (e i) * ∑ j, q i j y * t ^ (j : ℕ) - δ y * t := by
    intro y t; simp [hEl, eval₂_finsetSum, hevC, hQe]
  have hEWe : ∀ i y t, (EW i).eval₂ (ev y) t = (∑ j, q i j y * t ^ (j : ℕ)) ^ nW i +
      ∑ j : Fin (nW i), cW i j y * δ y ^ (nW i - j) * (∑ j, q i j y * t ^ (j : ℕ)) ^ (j : ℕ) := by
    intro i y t; simp [hEW, eval₂_finsetSum, hevC, hQe, eval₂_pow]
  have hAsum : ∀ (v : σ → ℂ) r, A v r = ∑ i, v i * A (e i) r := by
    intro v r; rw [linear_apply_eq_sum A v]; simp [Finset.sum_apply, he]
  have hlsum : ∀ v : σ → ℂ, ℓ v = ∑ i, v i * ℓ (e i) := by
    intro v; rw [linear_apply_eq_sum ℓ v]; simp [he]

  have hrelA : ∀ᶠ z in 𝓝 w, z ∈ Y → ∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ) := by
    filter_upwards [eventually_all.2 hrel] with z hz hzX i using hz i hzX
  have hWA : ∀ᶠ z in 𝓝 w, z ∈ Y → ∀ i, z i ^ nW i + ∑ j, cW i j (A z) * z i ^ (j : ℕ) = 0 := by
    filter_upwards [eventually_all.2 hWX] with z hz hzX i using hz i hzX
  have dEp := hdiv Ep (coeff_analyticAt hEpc) (by
    filter_upwards [hp] with z hz hzX; rw [hEpe]; exact hz hzX)
  have dEA := fun r => hdiv (EA r) (coeff_analyticAt (hEAc r)) (by
    filter_upwards [hrelA] with z hz hzX
    rw [hEAe, Finset.sum_congr rfl fun i _ => by rw [← hz hzX i], hAsum z r, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring)
  have dEl := hdiv El (coeff_analyticAt hElc) (by
    filter_upwards [hrelA] with z hz hzX
    rw [hEle, Finset.sum_congr rfl fun i _ => by rw [← hz hzX i]]
    rw [hlsum z, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring)
  have dEW := fun i => hdiv (EW i) (coeff_analyticAt (hEWc i)) (by
    filter_upwards [hrelA, hWA] with z hz hzW hzX
    rw [hEWe, ← hz hzX i, cleared_eq, hzW hzX i, mul_zero])
  have dR := fun k => hdiv (R k) (hR k) (by
    filter_upwards [hRz k, hrelA, hWA, hVo.mem_nhds hwV] with z h1 hz hzW hzV hzX
    have hz0 : z ∈ {z | z ∈ V ∧ ∀ i, f i z = 0} := by rw [← hXV]; exact ⟨hzX, hzV⟩
    rw [← h1 (hzW hzX) (hz hzX), hz0.2 k, mul_zero])
  refine ⟨n, b, hb, hmX, ?_, ?_⟩
  · filter_upwards [hsep, dEp] with y hs hd hδy
    refine (hs hδy).of_dvd ?_
    simpa [hEp, Polynomial.map_add, Polynomial.map_sum, hevC] using hd
  intro U hU
  have hO : ∀ᶠ z in 𝓝 w, z ∈ U ∧ z ∈ V ∧ ∀ k, (∀ i, z i ^ nW i + ∑ j, cW i j (A z) * z i ^ (j : ℕ) = 0) →
      (∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      δ (A z) ^ M k * f k z = (R k).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z) :=
    by filter_upwards [hU, hVo.mem_nhds hwV, eventually_all.2 hRz] with z h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hO
  have hnear := fun i => roots_near_centred (cW i) (A w) (w i) (fun j => (hcW i j).continuousAt) (hcW0 i) hε
  filter_upwards [eventually_all.2 hnear, eventually_all.2 dEA, dEl, eventually_all.2 dEW,
    eventually_all.2 dR] with y hny hAy hly hWy hRy hδy τ hτ
  set φ : σ → ℂ := fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y with hφ
  have hQφ : ∀ i, ∑ j, q i j y * τ ^ (j : ℕ) = δ y * φ i := fun i => by
    rw [hφ]; field_simp
  have hAφ : A φ = y := by
    funext r
    have h0 := eval₂_eq_zero_of_dvd (hAy r) hτ
    rw [hEAe, sub_eq_zero] at h0
    rw [hAsum φ r]
    apply mul_left_cancel₀ hδy
    rw [← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hQφ i]; ring
  have hlφ : ℓ φ = τ := by
    have h0 := eval₂_eq_zero_of_dvd hly hτ
    rw [hEle, sub_eq_zero] at h0
    rw [hlsum φ]
    apply mul_left_cancel₀ hδy
    rw [← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hQφ i]; ring
  have hWφ : ∀ i, φ i ^ nW i + ∑ j, cW i j y * φ i ^ (j : ℕ) = 0 := by
    intro i
    have h0 := eval₂_eq_zero_of_dvd (hWy i) hτ
    rw [hEWe, hQφ i, cleared_eq] at h0
    exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hδy)
  have hdist : dist φ w < ε := by
    rw [dist_pi_lt_iff hε]
    intro i
    rw [dist_eq_norm]
    exact hny i (φ i) (hWφ i)
  obtain ⟨hφU, hφV, hφR⟩ := hball hdist
  have hfk : ∀ k, f k φ = 0 := by
    intro k
    have h1 := hφR k (by rw [hAφ]; exact hWφ) (by intro i; rw [hAφ, hlφ, hQφ i])
    rw [hAφ, hlφ, eval₂_eq_zero_of_dvd (hRy k) hτ] at h1
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hδy)
  have hφX : φ ∈ Y ∩ V := by rw [hXV]; exact ⟨hφV, hfk⟩
  exact ⟨⟨hφX.1, hφU⟩, hAφ, hlφ⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimitiveFormMinimalFactorPoints
