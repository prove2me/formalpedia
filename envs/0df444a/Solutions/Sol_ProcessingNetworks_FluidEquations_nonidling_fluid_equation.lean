-- Prove2me | solution 1 for ProcessingNetworks.FluidEquations.nonidling_fluid_equation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T21:46:06.981807+00:00
-- url     : https://prove2.me/submissions/e171747f-c959-46aa-ad1c-a031ececc4e1

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FluidEquations_PolicyRelations



namespace ProcessingNetworks.FluidEquations

open MeasureTheory Filter ProcessingNetworks.Stability

lemma fe_uoc_sum {d : ℕ} {f : ℕ → ℝ → Fin d → ℝ} {g : ℝ → Fin d → ℝ}
    (h : UOCConverges f g) (S : Finset (Fin d)) :
    ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∃ Nb : ℕ, ∀ n ≥ Nb, ∀ t ∈ Set.Icc (0:ℝ) T,
      |∑ i ∈ S, f n t i - ∑ i ∈ S, g t i| < ε := by
  intro T hT ε hε
  obtain ⟨Nb, hN⟩ := h T hT (ε / (S.card + 1)) (by positivity)
  refine ⟨Nb, fun n hn t ht => ?_⟩
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i ∈ S, |f n t i - g t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ε / (S.card + 1) := Finset.sum_le_sum (fun i _ => (hN n hn t ht i).le)
    _ < ε := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

lemma fe_uoc_sum_tendsto {d : ℕ} {f : ℕ → ℝ → Fin d → ℝ} {g : ℝ → Fin d → ℝ}
    (h : UOCConverges f g) (S : Finset (Fin d)) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n => ∑ i ∈ S, f n t i) atTop (nhds (∑ i ∈ S, g t i)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Nb, hN⟩ := fe_uoc_sum h S t ht ε hε
  exact ⟨Nb, fun n hn => by rw [Real.dist_eq]; exact hN n hn t ⟨ht, le_rfl⟩⟩

lemma fe_deriv_of_affine (G : ℝ → ℝ) (a c t b : ℝ) (hat : a < t) (htc : t < c)
    (h : ∀ u1 u2, a < u1 → u1 ≤ u2 → u2 < c → G u2 - G u1 = (u2 - u1) * b) :
    HasDerivAt G b t := by
  have h0 : HasDerivAt (fun s => G t + (s - t) * b) b t := by
    have := (((hasDerivAt_id t).sub_const t).mul_const b).const_add (G t)
    simpa using this
  apply h0.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hat htc] with s hs
  rcases le_total s t with hst | hst
  · have := h s t hs.1 hst htc; linarith
  · have := h t s hat hst hs.2; linarith

lemma fe_lim_bounds {A B e : ℕ → ℝ} {a b' L : ℝ} (hA : Tendsto A atTop (nhds a))
    (hB : Tendsto B atTop (nhds b')) (he : Tendsto e atTop (nhds 0))
    (hev : ∀ᶠ n in atTop, L - e n ≤ A n - B n ∧ A n - B n ≤ L) : a - b' = L := by
  have hAB : Tendsto (fun n => A n - B n) atTop (nhds (a - b')) := hA.sub hB
  apply le_antisymm
  · exact le_of_tendsto hAB (hev.mono fun n h => h.2)
  · have hL : Tendsto (fun n => L - e n) atTop (nhds (L - 0)) := tendsto_const_nhds.sub he
    have := le_of_tendsto_of_tendsto hL hAB (hev.mono fun n h => h.1)
    simpa using this

/-- Local positivity window: from continuity and positivity of the limit sum we get an interval
on which, eventually, the unscaled sum exceeds any given level. -/
lemma fe_window {d : ℕ} (S : Finset (Fin d)) (Zh : ℝ → Fin d → ℝ) (hZcont : Continuous Zh)
    (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ S, Zh t i) :
    ∃ a c δ : ℝ, 0 < a ∧ a < t ∧ t < c ∧ 0 < δ ∧
      ∀ u, a < u → u < c → δ < ∑ i ∈ S, Zh u i := by
  have hcont : Continuous fun u => ∑ i ∈ S, Zh u i :=
    continuous_finsetSum _ (fun i _ => (continuous_apply i).comp hZcont)
  have hev : ∀ᶠ u in nhds t, (∑ i ∈ S, Zh t i) / 2 < ∑ i ∈ S, Zh u i :=
    hcont.continuousAt.eventually (lt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨t - min ε t / 2, t + min ε t / 2, (∑ i ∈ S, Zh t i) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · have := min_le_right ε t; linarith
  · have : 0 < min ε t := lt_min hε ht; linarith
  · have : 0 < min ε t := lt_min hε ht; linarith
  · linarith
  · intro u h1 h2
    apply hball
    rw [Real.dist_eq, abs_lt]
    have := min_le_left ε t
    constructor <;> linarith

/-- Generic: eventually the scaled sum stays above `δ/2` on `[0,c]`, so the unscaled sum exceeds
`size * δ / 2`. -/
lemma fe_unscaled_big {d : ℕ} (S : Finset (Fin d)) (Zx : ℕ → ℝ → Fin d → ℝ) (s : ℕ → ℝ)
    (Zh : ℝ → Fin d → ℝ)
    (hZ : UOCConverges (fun n t i => (s n)⁻¹ * Zx n (s n * t) i) Zh)
    (hs : Tendsto s atTop atTop) (a c δ L : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hwin : ∀ u, a < u → u < c → δ < ∑ i ∈ S, Zh u i) :
    ∀ᶠ n in atTop, 0 < s n ∧ ∀ u1 u2, a < u1 → u1 ≤ u2 → u2 < c → ∀ w ∈ Set.Icc (s n * u1) (s n * u2),
      L < ∑ i ∈ S, Zx n w i := by
  have hc : 0 ≤ c ∨ c < 0 := le_or_gt 0 c
  rcases hc with hc | hc
  swap
  · filter_upwards [hs.eventually_ge_atTop 1] with n hn
    refine ⟨by linarith, fun u1 u2 h1 h12 h2 => ?_⟩
    exfalso; linarith
  obtain ⟨Nb, hN⟩ := fe_uoc_sum hZ S c hc (δ / 2) (by linarith)
  filter_upwards [hs.eventually_ge_atTop (2 * |L| / δ + 1), eventually_ge_atTop Nb]
    with n hn hnb
  have hspos : 0 < s n := by
    have : 0 ≤ 2 * |L| / δ := by positivity
    linarith
  refine ⟨hspos, fun u1 u2 h1 _ h2 w hw => ?_⟩
  have hu1 : u1 ≤ w / s n := by rw [le_div_iff₀ hspos]; linarith [hw.1]
  have hu2 : w / s n ≤ u2 := by rw [div_le_iff₀ hspos]; linarith [hw.2]
  have hb := hN n hnb (w / s n) ⟨by linarith, by linarith⟩
  have hsw : s n * (w / s n) = w := mul_div_cancel₀ w hspos.ne'
  simp only [hsw] at hb
  have hz := hwin (w / s n) (by linarith) (by linarith)
  rw [← Finset.mul_sum] at hb
  have hlow : δ / 2 < (s n)⁻¹ * ∑ i ∈ S, Zx n w i := by
    rw [abs_lt] at hb; linarith [hb.1]
  have h3 : s n * (δ / 2) < ∑ i ∈ S, Zx n w i := by
    have := mul_lt_mul_of_pos_left hlow hspos
    rwa [← mul_assoc, mul_inv_cancel₀ hspos.ne', one_mul] at this
  have h4 : |L| < s n * (δ / 2) := by
    have h5 : (2 * |L| / δ + 1) * (δ / 2) = |L| + δ / 2 := by field_simp
    nlinarith
  linarith [le_abs_self L]

theorem nonidling_core
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) (hni : NonIdling dat fam)
    (Th Zh : ℝ → Fin I → ℝ) (ω : Ω) (x : ℕ → Xstate) (hZcont : Continuous Zh)
    (hsize : Tendsto (fun n => Mrep.size (x n)) atTop atTop)
    (hT : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * fam.T (x n) (Mrep.size (x n) * t) ω i) Th)
    (hZ : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.Zx (x n) (Mrep.size (x n) * t) ω i : ℝ)) Zh)
    (k : Fin K) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ poolBuffers dat k, Zh t i) :
    HasDerivAt (fun s => ∑ i ∈ poolBuffers dat k, Th s i) (dat.b k) t := by
  set S := poolBuffers dat k with hS
  obtain ⟨a, c, δ, ha, hat, htc, hδ, hwin⟩ := fe_window S Zh hZcont t ht hz
  apply fe_deriv_of_affine _ a c t _ hat htc
  intro u1 u2 h1 h12 h2
  have hbig := fe_unscaled_big S (fun n w i => (fam.Zx (x n) w ω i : ℝ))
    (fun n => Mrep.size (x n)) Zh hZ hsize a c δ (dat.b k) ha hδ hwin
  refine fe_lim_bounds (fe_uoc_sum_tendsto hT S u2 (by linarith))
    (fe_uoc_sum_tendsto hT S u1 (by linarith)) (e := fun _ => 0) tendsto_const_nhds ?_
  filter_upwards [hbig] with n ⟨hspos, hn⟩
  have hcond : ∀ w ∈ Set.Icc (Mrep.size (x n) * u1) (Mrep.size (x n) * u2),
      dat.b k ≤ ∑ i ∈ S, (fam.Zx (x n) w ω i : ℝ) :=
    fun w hw => (hn u1 u2 h1 h12 h2 w hw).le
  have key := hni (x n) ω _ _ k (by have := mul_pos hspos (by linarith : (0:ℝ) < u1); linarith)
    (mul_le_mul_of_nonneg_left h12 hspos.le) hcond
  have eq : ∑ i ∈ S, (Mrep.size (x n))⁻¹ * fam.T (x n) (Mrep.size (x n) * u2) ω i -
      ∑ i ∈ S, (Mrep.size (x n))⁻¹ * fam.T (x n) (Mrep.size (x n) * u1) ω i =
      (u2 - u1) * dat.b k := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub, ← Finset.sum_sub_distrib, key]
    field_simp
  rw [eq]
  constructor <;> simp

theorem nonidling_main
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) (hni : NonIdling dat fam)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hfl : FluidLimitPath fam Dh Fh Th Zh)
    (k : Fin K) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ poolBuffers dat k, Zh t i) :
    HasDerivAt (fun s => ∑ i ∈ poolBuffers dat k, Th s i) (dat.b k) t := by
  obtain ⟨_, _, _, hZc, ω, x, hs, _, _, hT, hZ⟩ := hfl
  exact nonidling_core dat fam hni Th Zh ω x hZc hs hT hZ k t ht hz

end ProcessingNetworks.FluidEquations

open ProcessingNetworks.FluidEquations
open MeasureTheory Filter ProcessingNetworks.Stability

theorem solution
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ) (hni : NonIdling dat fam)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hfl : FluidLimitPath fam Dh Fh Th Zh)
    (k : Fin K) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ poolBuffers dat k, Zh t i) :
    HasDerivAt (fun s => ∑ i ∈ poolBuffers dat k, Th s i) (dat.b k) t := by
  exact nonidling_main dat fam hni Dh Fh Th Zh hfl k t ht hz
