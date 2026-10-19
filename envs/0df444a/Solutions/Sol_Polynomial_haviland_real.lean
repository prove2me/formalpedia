-- Prove2me | solution 1 for Polynomial.haviland_real
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T22:24:49.200972+00:00
-- url     : https://prove2.me/submissions/7191be24-60e0-4c7b-a68b-fe5d06d3feec

import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open MeasureTheory Set Filter Topology
open scoped ENNReal CompactlySupported
set_option autoImplicit false

private theorem extend_positive (K : Set ℝ) (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ p : Polynomial ℝ, (∀ x ∈ K, 0 ≤ p.eval (x : ℝ)) → 0 ≤ L p) :
    ∃ Λ : C_c(K, ℝ) →ₚ[ℝ] ℝ,
      ∀ (p : Polynomial ℝ) (f : C_c(K, ℝ)),
        (∀ x : K, f x ≤ p.eval (x : ℝ)) → Λ f ≤ L p := by
  let E := Polynomial ℝ × C_c(K, ℝ)
  let s : PointedCone ℝ E := {
    carrier := {y | ∀ x : K, 0 ≤ y.1.eval (x : ℝ) + y.2 x}
    zero_mem' := by simp
    add_mem' := by
      intro a b ha hb x
      change 0 ≤ (a.1+b.1).eval (x:ℝ) + (a.2+b.2) x
      simp only [Polynomial.eval_add, CompactlySupportedContinuousMap.add_apply]
      linarith [ha x,hb x]
    smul_mem' := by
      intro c y hy x
      change 0 ≤ ((c:ℝ) • y.1).eval (x:ℝ) + ((c:ℝ) • y.2) x
      simp only [Polynomial.eval_smul, CompactlySupportedContinuousMap.smul_apply]
      change 0 ≤ (c:ℝ) * y.1.eval (x:ℝ) + (c:ℝ) * y.2 x
      simpa only [mul_add] using mul_nonneg c.property (hy x) }
  let D := LinearMap.ker (LinearMap.snd ℝ (Polynomial ℝ) C_c(K, ℝ))
  let F : E →ₗ.[ℝ] ℝ := (L.comp (LinearMap.fst ℝ (Polynomial ℝ) C_c(K, ℝ))).toPMap D
  have hF : ∀ y : F.domain, (y : E) ∈ s → 0 ≤ F y := by
    rintro ⟨⟨p,f⟩,hy⟩ h
    have hf : f = 0 := hy
    apply hL p
    intro x hx
    simpa [hf] using h ⟨x,hx⟩
  have hd : ∀ y : E, ∃ z : F.domain, (z : E) + y ∈ s := by
    rintro ⟨p,f⟩
    let b := ‖f.toBoundedContinuousFunction‖
    refine ⟨⟨(Polynomial.C b - p, 0), by rfl⟩, ?_⟩
    intro x
    have hb : |f x| ≤ b := f.toBoundedContinuousFunction.norm_coe_le_norm x
    change 0 ≤ (Polynomial.C b - p + p).eval (x:ℝ) + (0+f) x
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_C, zero_add]
    linarith [neg_abs_le (f x)]
  obtain ⟨G,hG,hpos⟩ := riesz_extension s F hF hd
  have hp (p : Polynomial ℝ) : G (p,0) = L p := hG ⟨(p,0),by rfl⟩
  let Λ : C_c(K, ℝ) →ₚ[ℝ] ℝ := {
    toLinearMap := G.comp (LinearMap.inr ℝ (Polynomial ℝ) C_c(K, ℝ))
    monotone' := by
      intro f g hfg
      have h := hpos (0,g-f) (by intro x; simpa using sub_nonneg.mpr (hfg x))
      change G (0,f) ≤ G (0,g)
      have hh : G (0,g-f) = G (0,g) - G (0,f) := by
        rw [show ((0:Polynomial ℝ),g-f) = (0,g) - (0,f) from
          Prod.ext (by change (0:Polynomial ℝ) = 0-0; simp) rfl, map_sub]
      linarith }
  refine ⟨Λ, fun p f hpf => ?_⟩
  have h := hpos (p,-f) (by intro x; simpa using sub_nonneg.mpr (hpf x))
  have he : G (p,-f) = L p - Λ f := by
    rw [show (p,-f) = (p,0) - (0,f) by simp, map_sub, hp]
    rfl
  linarith

private theorem cutoffs (K : Set ℝ) (hK : IsClosed K) :
    ∃ η : ℕ → C_c(K,ℝ),
      (∀ n x, η n x ∈ Icc 0 1) ∧
      (∀ (n : ℕ) (x : K), |(x : ℝ)| ≤ n → η n x = 1) := by
  let := hK.locallyCompactSpace
  have hcomp (n : ℕ) : IsCompact ((Subtype.val : K → ℝ) ⁻¹' Icc (-(n:ℝ)) n) :=
    hK.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage isCompact_Icc
  have hc (n : ℕ) := exists_continuousMap_one_of_isCompact_subset_isOpen (hcomp n)
    isOpen_univ (subset_univ _)
  choose f hf hcompact _ hbound using hc
  refine ⟨fun n => ⟨f n,hcompact n⟩, hbound, ?_⟩
  intro n x hx
  exact hf n (abs_le.mp hx)

private def cut_mul {K : Set ℝ} (η : C_c(K,ℝ)) (f : C(K,ℝ)) : C_c(K,ℝ) :=
  ⟨η.toContinuousMap * f, η.hasCompactSupport.mul_right⟩

private theorem cutoff_tendsto {K : Set ℝ} (η : ℕ → C_c(K,ℝ))
    (hη : ∀ (n : ℕ) (x : K), |(x : ℝ)| ≤ n → η n x = 1) (x : K) :
    Tendsto (fun n => η (n+1) x) atTop (𝓝 1) := by
  obtain ⟨N,hN⟩ := exists_nat_ge |(x:ℝ)|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (hη (n+1) x (hN.trans (by exact_mod_cast Nat.le_succ_of_le hn))).symm

private theorem integrable_eval {K : Set ℝ} [LocallyCompactSpace K]
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (Λ : C_c(K,ℝ) →ₚ[ℝ] ℝ)
    (hΛ : ∀ (p : Polynomial ℝ) (f : C_c(K,ℝ)),
      (∀ x : K, f x ≤ p.eval (x : ℝ)) → Λ f ≤ L p)
    (η : ℕ → C_c(K,ℝ)) (hb : ∀ n x, η n x ∈ Icc 0 1)
    (he : ∀ (n : ℕ) (x : K), |(x:ℝ)| ≤ n → η n x = 1) (p : Polynomial ℝ) :
    Integrable (fun x : K => p.eval (x : ℝ)) (RealRMK.rieszMeasure Λ) := by
  let μ := RealRMK.rieszMeasure Λ
  let f : C(K,ℝ) := ⟨fun x => |p.eval (x : ℝ)|, p.continuous.comp continuous_subtype_val |>.abs⟩
  let F (n : ℕ) := cut_mul (η (n+1)) f
  have hF (n : ℕ) (x : K) : 0 ≤ F n x := mul_nonneg (hb _ _).1 (abs_nonneg _)
  have hlim (x : K) : Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    simpa [F,cut_mul] using (cutoff_tendsto η he x).mul_const (f x)
  have hbound (n : ℕ) : ∫⁻ x, ENNReal.ofReal (F n x) ∂μ ≤
      ENNReal.ofReal (L (1 + p^2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (F n).integrable (ae_of_all _ (hF n)),
      RealRMK.integral_rieszMeasure]
    apply ENNReal.ofReal_le_ofReal
    apply hΛ (1+p^2) (F n)
    intro x
    change η (n+1) x * |p.eval (x : ℝ)| ≤ (1+p^2).eval (x:ℝ)
    apply (mul_le_of_le_one_left (abs_nonneg _) (hb (n+1) x).2).trans
    simp only [Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_pow]
    nlinarith [sq_nonneg (|p.eval (x : ℝ)| - 1),sq_abs (p.eval (x : ℝ))]
  have hfatou : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal (L (1+p^2)) := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ := by
        congr 1; funext x; exact ((ENNReal.continuous_ofReal.tendsto _).comp (hlim x)).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop :=
        lintegral_liminf_le (fun n => (F n).continuous.measurable.ennreal_ofReal)
      _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hbound)
  have hi : Integrable (fun x : K => |p.eval (x : ℝ)|) μ :=
    ⟨f.continuous.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => abs_nonneg _))).mpr
        (hfatou.trans_lt ENNReal.ofReal_lt_top)⟩
  exact (integrable_norm_iff (p.continuous.comp continuous_subtype_val).aestronglyMeasurable).mp hi

private theorem cutoff_error (n : ℕ) (x t a : ℝ) (ha : a ∈ Icc 0 1)
    (he : |x| ≤ (n:ℝ)+1 → a=1) :
    |t-a*t| ≤ ((n:ℝ)+1)⁻¹ * ((1+x^2)*(1+t^2)) := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  rw [inv_mul_eq_div, le_div_iff₀ hn]
  by_cases hx : |x| ≤ (n:ℝ)+1
  · simp only [he hx, one_mul, sub_self, abs_zero, zero_mul]
    positivity
  · have habs : |t-a*t| ≤ |t| := by
      calc
        _ = |1-a| * |t| := by rw [← abs_mul]; congr 1; ring
        _ ≤ 1 * |t| := mul_le_mul_of_nonneg_right (by
          rw [abs_of_nonneg (by linarith [ha.2])]; linarith [ha.1]) (abs_nonneg _)
        _ = _ := one_mul _
    have ht : |t| ≤ 1+t^2 := by
      nlinarith [sq_nonneg (|t|-1),sq_abs t]
    have hxx : (n:ℝ)+1 ≤ 1+x^2 := by
      have hx' : (n:ℝ)+1 ≤ |x| := (not_le.mp hx).le
      have hh := mul_self_le_mul_self hn.le hx'
      nlinarith [sq_abs x, sq_nonneg (n:ℝ), (show 0 ≤ (n:ℝ) by positivity)]
    calc
      _ ≤ (1+t^2) * ((n:ℝ)+1) := mul_le_mul_of_nonneg_right (habs.trans ht) hn.le
      _ ≤ (1+t^2) * (1+x^2) := mul_le_mul_of_nonneg_left hxx (by positivity)
      _ = _ := mul_comm _ _

private theorem integral_eval {K : Set ℝ} [LocallyCompactSpace K]
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (Λ : C_c(K,ℝ) →ₚ[ℝ] ℝ)
    (hΛ : ∀ (p : Polynomial ℝ) (f : C_c(K,ℝ)),
      (∀ x : K, f x ≤ p.eval (x:ℝ)) → Λ f ≤ L p)
    (η : ℕ → C_c(K,ℝ)) (hb : ∀ n x, η n x ∈ Icc 0 1)
    (he : ∀ (n : ℕ) (x : K), |(x:ℝ)| ≤ n → η n x = 1) (p : Polynomial ℝ) :
    ∫ x : K, p.eval (x:ℝ) ∂(RealRMK.rieszMeasure Λ) = L p := by
  let μ := RealRMK.rieszMeasure Λ
  let f : C(K,ℝ) := ⟨fun x => p.eval (x:ℝ),p.continuous.comp continuous_subtype_val⟩
  let F (n : ℕ) := cut_mul (η (n+1)) f
  let q : Polynomial ℝ := (1+Polynomial.X^2)*(1+p^2)
  have herr (n : ℕ) (x : K) : |p.eval (x:ℝ) - F n x| ≤
      ((n:ℝ)+1)⁻¹ * q.eval (x:ℝ) := by
    simpa [F,cut_mul,f,q,Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_mul]
      using cutoff_error n (x:ℝ) (p.eval (x:ℝ)) (η (n+1) x) (hb _ _)
        (by simpa only [Nat.cast_add,Nat.cast_one] using he (n+1) x)
  have hupper (n : ℕ) : Λ (F n) ≤ L p + ((n:ℝ)+1)⁻¹ * L q := by
    have h := hΛ (p + ((n:ℝ)+1)⁻¹ • q) (F n) (fun x => by
      have h := (abs_le.mp (herr n x)).1
      simpa only [Polynomial.eval_add,Polynomial.eval_smul,smul_eq_mul] using (by linarith :
        F n x ≤ p.eval (x:ℝ) + ((n:ℝ)+1)⁻¹ * q.eval (x:ℝ)))
    simpa using h
  have hlower (n : ℕ) : L p - ((n:ℝ)+1)⁻¹ * L q ≤ Λ (F n) := by
    have h := hΛ (-p + ((n:ℝ)+1)⁻¹ • q) (-F n) (fun x => by
      have h := (abs_le.mp (herr n x)).2
      simpa only [Polynomial.eval_add,Polynomial.eval_neg,Polynomial.eval_smul,smul_eq_mul,
        CompactlySupportedContinuousMap.neg_apply] using (by linarith :
        -F n x ≤ -p.eval (x:ℝ) + ((n:ℝ)+1)⁻¹ * q.eval (x:ℝ)))
    simp only [map_add,map_neg,map_smul,smul_eq_mul] at h
    linarith
  have ht : Tendsto (fun n:ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n:ℕ => ((n:ℝ)+1)⁻¹ * L q) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp ht).mul_const (L q)
  have hlo : Tendsto (fun n:ℕ => L p - ((n:ℝ)+1)⁻¹ * L q) atTop (𝓝 (L p)) := by
    simpa using tendsto_const_nhds.sub hc
  have hhi : Tendsto (fun n:ℕ => L p + ((n:ℝ)+1)⁻¹ * L q) atTop (𝓝 (L p)) := by
    simpa using tendsto_const_nhds.add hc
  have hseq : Tendsto (fun n => Λ (F n)) atTop (𝓝 (L p)) := hlo.squeeze hhi hlower hupper
  have hi := integrable_eval L Λ hΛ η hb he p
  have hd : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x : K, p.eval (x:ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x : K => |p.eval (x:ℝ)|)
      (fun n => (F n).continuous.aestronglyMeasurable) hi.norm
    · intro n
      apply ae_of_all
      intro x
      change |η (n+1) x * p.eval (x:ℝ)| ≤ _
      rw [abs_mul,abs_of_nonneg (hb _ _).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hb _ _).2
    · apply ae_of_all
      intro x
      simpa [F,cut_mul,f] using (cutoff_tendsto η he x).mul_const (p.eval (x:ℝ))
  dsimp only [μ] at hd
  simp only [RealRMK.integral_rieszMeasure] at hd
  exact tendsto_nhds_unique hd hseq

theorem solution (K : Set ℝ) (hK : IsClosed K)
    (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ p : Polynomial ℝ, (∀ x ∈ K, 0 ≤ p.eval x) → 0 ≤ L p) :
    ∃ μ : Measure ℝ, μ Kᶜ = 0 ∧
      ∀ p : Polynomial ℝ, Integrable (fun x : ℝ => p.eval x) μ ∧
        ∫ x, p.eval x ∂μ = L p := by
  let := hK.locallyCompactSpace
  obtain ⟨Λ,hΛ⟩ := extend_positive K L hL
  obtain ⟨η,hb,he⟩ := cutoffs K hK
  let ν := RealRMK.rieszMeasure Λ
  refine ⟨ν.map Subtype.val, ?_, fun p => ⟨?_,?_⟩⟩
  · rw [Measure.map_apply measurable_subtype_coe hK.measurableSet.compl]
    simp
  · exact (integrable_map_measure (p.continuous.aestronglyMeasurable)
      measurable_subtype_coe.aemeasurable).mpr (integrable_eval L Λ hΛ η hb he p)
  · rw [integral_map measurable_subtype_coe.aemeasurable p.continuous.aestronglyMeasurable]
    exact integral_eval L Λ hΛ η hb he p
