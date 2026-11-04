-- Prove2me | solution 1 for UnknownLoads.Coxian.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T20:45:43.891127+00:00
-- url     : https://prove2.me/submissions/d7a2ff48-b320-4453-b8d0-1df8bec296a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UnknownLoads_Coxian_NicePaths
import Theorems.Thm_UnknownLoads_Coxian_proposition_16
import Theorems.Thm_UnknownLoads_Coxian_proposition_17
import Theorems.Thm_UnknownLoads_Coxian_proposition_18
import Theorems.Thm_UnknownLoads_Coxian_fluid_u_limits
open MeasureTheory Filter Topology

namespace UnknownLoads.Coxian.T3aux
open UnknownLoads.Coxian

lemma qOf_le_one {r : ℕ} {s : Profile r → ℝ} (hs : InS s) (i : ℕ) : qOf s i ≤ 1 := by
  unfold qOf
  have : 0 ≤ ∑ ν ∈ lowProfiles r i, s ν := Finset.sum_nonneg (fun ν _ => (hs.1 ν).1)
  linarith

lemma qOf_nonneg {r : ℕ} {s : Profile r → ℝ} (hs : InS s) (i : ℕ) : 0 ≤ qOf s i := by
  unfold qOf
  have := sum_le_hasSum (lowProfiles r i) (fun ν _ => (hs.1 ν).1) hs.2
  linarith

lemma lowProfiles_mono (r : ℕ) {i j : ℕ} (hij : i ≤ j) : lowProfiles r i ⊆ lowProfiles r j := by
  intro ν hν
  simp only [lowProfiles, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hν ⊢
  exact ⟨fun m => lt_of_lt_of_le (hν.1 m) hij, lt_of_lt_of_le hν.2 hij⟩

lemma qOf_anti {r : ℕ} {s : Profile r → ℝ} (hs : InS s) {i j : ℕ} (hij : i ≤ j) :
    qOf s j ≤ qOf s i := by
  unfold qOf
  have := Finset.sum_le_sum_of_subset_of_nonneg (lowProfiles_mono r hij)
    (f := s) (fun ν _ _ => (hs.1 ν).1)
  linarith

lemma qOf_zero {r : ℕ} (s : Profile r → ℝ) : qOf s 0 = 1 := by
  simp [qOf, lowProfiles]

lemma qOf_eq_zero_of_ge {r : ℕ} {s : Profile r → ℝ} (hs : InS s) {M i : ℕ} (hM : qOf s M = 0)
    (hi : M ≤ i) : qOf s i = 0 :=
  le_antisymm (hM ▸ qOf_anti hs hi) (qOf_nonneg hs i)

lemma sum_Icc_shift (g : ℕ → ℝ) (a b : ℕ) :
    ∑ i ∈ Finset.Icc (a + 1) (a + b), g i = ∑ i ∈ Finset.range b, g (a + 1 + i) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ← ih, show a + (b + 1) = (a + b) + 1 by ring,
      Finset.sum_Icc_succ_top (by omega)]
    congr 1
    congr 1
    ring

lemma summable_q {r : ℕ} {s : Profile r → ℝ} (hs : InS s) {M : ℕ} (hM : qOf s M = 0) (k : ℕ) :
    Summable (fun i => qOf s (k + i)) := by
  apply summable_of_ne_finset_zero (s := Finset.range M)
  intro i hi
  simp only [Finset.mem_range, not_lt] at hi
  exact qOf_eq_zero_of_ge hs hM (by omega)

lemma mass_decomp (P : Params) {s : Profile P.r → ℝ} (hs : InS s) {M : ℕ} (hM : qOf s M = 0) :
    uMass s = xMass P s + yMass P s + zMass P s := by
  set L := ellStar P
  set D := P.Δ
  have hsum : Summable (fun i => qOf s (i + 1)) := by
    have := summable_q hs hM 1
    simpa [add_comm] using this
  rw [uMass, ← hsum.sum_add_tsum_nat_add (L + D), Finset.sum_range_add, xMass, yMass, zMass]
  have e1 : ∑ i ∈ Finset.Icc 1 L, qOf s i = ∑ x ∈ Finset.range L, qOf s (x + 1) := by
    have := sum_Icc_shift (qOf s) 0 L
    simp only [zero_add] at this
    rw [this]
    simp [add_comm]
  have e2 : ∑ i ∈ Finset.Icc (L + 1) (L + D), qOf s i =
      ∑ x ∈ Finset.range D, qOf s (L + x + 1) := by
    rw [sum_Icc_shift]
    congr 1; ext x; congr 1; ring
  have e3 : ∑' i, qOf s (L + D + 1 + i) = ∑' i, qOf s (i + (L + D) + 1) := by
    congr 1; ext i; congr 1; ring
  rw [e1, e2, e3]

lemma xMass_le (P : Params) {s : Profile P.r → ℝ} (hs : InS s) : xMass P s ≤ ellStar P := by
  unfold xMass
  calc ∑ i ∈ Finset.Icc 1 (ellStar P), qOf s i ≤ ∑ i ∈ Finset.Icc 1 (ellStar P), (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => qOf_le_one hs i)
    _ = ellStar P := by simp

lemma one_sub_q_le (P : Params) {s : Profile P.r → ℝ} (hs : InS s) {i : ℕ} (hi1 : 1 ≤ i)
    (hi : i ≤ ellStar P) : 1 - qOf s i ≤ ellStar P - xMass P s := by
  have h : (ellStar P : ℝ) - xMass P s = ∑ j ∈ Finset.Icc 1 (ellStar P), (1 - qOf s j) := by
    unfold xMass; simp [Finset.sum_sub_distrib]
  rw [h]
  exact Finset.single_le_sum (f := fun j => 1 - qOf s j)
    (fun j _ => by have := qOf_le_one hs j; linarith) (Finset.mem_Icc.2 ⟨hi1, hi⟩)

lemma xMass_nonneg (P : Params) {s : Profile P.r → ℝ} (hs : InS s) : 0 ≤ xMass P s := by
  unfold xMass; exact Finset.sum_nonneg (fun i _ => qOf_nonneg hs i)

lemma yMass_nonneg (P : Params) {s : Profile P.r → ℝ} (hs : InS s) : 0 ≤ yMass P s := by
  unfold yMass; exact Finset.sum_nonneg (fun i _ => qOf_nonneg hs i)

lemma zMass_nonneg (P : Params) {s : Profile P.r → ℝ} (hs : InS s) : 0 ≤ zMass P s := by
  unfold zMass; exact tsum_nonneg (fun i => qOf_nonneg hs _)

lemma tail_ennreal (P : Params) {s : Profile P.r → ℝ} (hs : InS s) {M : ℕ} (hM : qOf s M = 0) :
    (∑' i : ℕ, if ((ellStar P : ℕ) : ℤ) + (P.Δ : ℤ) < (i : ℤ)
        then ENNReal.ofReal (qOf s i) else 0) = ENNReal.ofReal (zMass P s) := by
  set g : ℕ → ENNReal := fun i => if ((ellStar P : ℕ) : ℤ) + (P.Δ : ℤ) < (i : ℤ)
        then ENNReal.ofReal (qOf s i) else 0 with hg
  have hsplit := Summable.sum_add_tsum_nat_add' (f := g) (k := ellStar P + P.Δ + 1)
    ENNReal.summable
  rw [zMass, ENNReal.ofReal_tsum_of_nonneg (fun i => qOf_nonneg hs _) (summable_q hs hM _),
    ← hsplit]
  have h1 : ∑ i ∈ Finset.range (ellStar P + P.Δ + 1), g i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only [hg]
    rw [if_neg (by omega)]
  rw [h1, zero_add]
  congr 1; ext i
  simp only [hg]
  rw [if_pos (by push_cast; omega)]
  congr 2; ring

end UnknownLoads.Coxian.T3aux

namespace UnknownLoads.Coxian.T3aux
open UnknownLoads.Coxian

lemma p_nonneg (P : Params) (m : Fin P.r) : 0 ≤ P.p m := by
  by_cases h : m.val + 1 = P.r
  · rw [P.p_last m h]
  · exact (P.p_mem m h).1.le

lemma p_lt_one (P : Params) (m : Fin P.r) : P.p m < 1 := by
  by_cases h : m.val + 1 = P.r
  · rw [P.p_last m h]; norm_num
  · exact (P.p_mem m h).2

lemma rho_nonneg (P : Params) : 0 ≤ rho P := by
  unfold rho meanService
  apply mul_nonneg P.lam_nonneg
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  apply mul_nonneg
  · linarith [p_lt_one P i]
  · exact Finset.prod_nonneg (fun j _ => p_nonneg P j)
  · exact Finset.sum_nonneg (fun k _ => (one_div_pos.2 (P.μ_pos k)).le)

lemma eta_pos (P : Params) : 0 < eta P := by
  unfold eta
  obtain ⟨m, _, hm⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin P.r)))
    ⟨⟨0, P.r_pos⟩, Finset.mem_univ _⟩ (fun m : Fin P.r => (1 - P.p m) * P.μ m)
  rw [hm]
  exact mul_pos (by linarith [p_lt_one P m]) (P.μ_pos m)

lemma Delta_pos (P : Params) : (0 : ℝ) < P.Δ := by
  have := P.Δ_pos; exact_mod_cast (by omega : 0 < P.Δ)

lemma floorDelta_rho (P : Params) : floorDelta P.Δ (rho P) = ((ellStar P : ℕ) : ℤ) := by
  unfold ellStar
  rw [Int.toNat_of_nonneg]
  unfold floorDelta
  apply mul_nonneg (by positivity)
  exact Int.floor_nonneg.2 (div_nonneg (rho_nonneg P) (Delta_pos P).le)

lemma ell_le_rho (P : Params) : (ellStar P : ℝ) ≤ rho P := by
  have h := floorDelta_rho P
  have hD := Delta_pos P
  have : ((floorDelta P.Δ (rho P) : ℤ) : ℝ) = (ellStar P : ℝ) := by rw [h]; simp
  rw [← this]; unfold floorDelta; push_cast
  have := Int.floor_le (rho P / P.Δ)
  calc (P.Δ : ℝ) * ⌊rho P / P.Δ⌋ ≤ P.Δ * (rho P / P.Δ) := by gcongr
    _ = rho P := by field_simp

lemma rho_lt_ell_add (P : Params) : rho P < (ellStar P : ℝ) + P.Δ := by
  have h := floorDelta_rho P
  have hD := Delta_pos P
  have : ((floorDelta P.Δ (rho P) : ℤ) : ℝ) = (ellStar P : ℝ) := by rw [h]; simp
  rw [← this]; unfold floorDelta; push_cast
  have := Int.lt_floor_add_one (rho P / P.Δ)
  calc rho P = P.Δ * (rho P / P.Δ) := by field_simp
    _ < P.Δ * (⌊rho P / P.Δ⌋ + 1) := by gcongr
    _ = _ := by ring

lemma ell_ne_rho (P : Params) (hρ : ∀ i : ℕ, rho P ≠ (i : ℝ) * (P.Δ : ℝ)) :
    (ellStar P : ℝ) ≠ rho P := by
  have h := floorDelta_rho P
  have hk : 0 ≤ ⌊rho P / P.Δ⌋ := Int.floor_nonneg.2 (div_nonneg (rho_nonneg P) (Delta_pos P).le)
  have := hρ (⌊rho P / P.Δ⌋).toNat
  intro heq
  apply this
  have h3 : ((floorDelta P.Δ (rho P) : ℤ) : ℝ) = (ellStar P : ℝ) := by rw [h]; simp
  have h2 : rho P = (P.Δ : ℝ) * ((⌊rho P / P.Δ⌋ : ℤ) : ℝ) := by
    have h4 := h3.trans heq
    unfold floorDelta at h4; push_cast at h4; linarith
  have e : (((⌊rho P / P.Δ⌋).toNat : ℕ) : ℝ) = ((⌊rho P / P.Δ⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk
  rw [e]
  nth_rewrite 1 [h2]
  ring

lemma floorDelta_eq_of_mem (P : Params) {v : ℝ} (h1 : (ellStar P : ℝ) ≤ v)
    (h2 : v < (ellStar P : ℝ) + P.Δ) : floorDelta P.Δ v = ((ellStar P : ℕ) : ℤ) := by
  have h := floorDelta_rho P
  have hD := Delta_pos P
  have hE : ((floorDelta P.Δ (rho P) : ℤ) : ℝ) = (ellStar P : ℝ) := by rw [h]; simp
  rw [← h]
  unfold floorDelta at hE ⊢
  congr 1
  set k := ⌊rho P / P.Δ⌋
  push_cast at hE
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hD]; nlinarith
  · rw [div_lt_iff₀ hD]; nlinarith

/-- Gronwall-type bound for an absolutely continuous function with `f' ≤ -η f` a.e. -/
lemma gronwall_ac {f : ℝ → ℝ} {a b η : ℝ} (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Icc a b → deriv f τ ≤ -η * f τ) :
    f b ≤ f a * Real.exp (-η * (b - a)) := by
  set e : ℝ → ℝ := fun τ => Real.exp (η * τ) with he
  have hec : AbsolutelyContinuousOnInterval e a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    apply ContDiff.contDiffOn
    exact Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hw := hf.mul hec
  have hint := hw.integral_deriv_eq_sub
  have hle : ∫ x in a..b, deriv (f * e) x ≤ ∫ x in a..b, (0 : ℝ) := by
    apply intervalIntegral.integral_mono_ae_restrict hab hw.intervalIntegrable_deriv
      intervalIntegrable_const
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hd, hf.ae_differentiableAt] with τ h1 h2 hτ
    have hτ' : τ ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hτ
    have hde : HasDerivAt e (Real.exp (η * τ) * η) τ := by
      have := ((hasDerivAt_id τ).const_mul η).exp
      simpa [he, mul_comm] using this
    have hD : HasDerivAt (f * e) (deriv f τ * e τ + f τ * (Real.exp (η * τ) * η)) τ :=
      (h2 hτ').hasDerivAt.mul hde
    rw [hD.deriv]
    have hep : 0 < e τ := Real.exp_pos _
    have := h1 hτ
    have : deriv f τ * Real.exp (η * τ) ≤ -η * f τ * Real.exp (η * τ) :=
      mul_le_mul_of_nonneg_right this hep.le
    nlinarith
  rw [hint, intervalIntegral.integral_zero] at hle
  simp only [Pi.mul_apply, he] at hle
  have hpos : 0 < Real.exp (η * b) := Real.exp_pos _
  have key : f b ≤ f a * Real.exp (η * a) / Real.exp (η * b) := by
    rw [le_div_iff₀ hpos]; linarith
  calc f b ≤ f a * Real.exp (η * a) / Real.exp (η * b) := key
    _ = f a * Real.exp (-η * (b - a)) := by
      rw [mul_div_assoc, ← Real.exp_sub]; congr 2; ring

/-- Lower bound from an a.e. lower bound on the derivative. -/
lemma ftc_lower {f : ℝ → ℝ} {a b κ : ℝ} (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Ioo a b → κ ≤ deriv f τ) :
    κ * (b - a) ≤ f b - f a := by
  rw [← hf.integral_deriv_eq_sub]
  have := intervalIntegral.integral_mono_ae_restrict (f := fun _ => κ) (μ := volume) hab
    intervalIntegrable_const hf.intervalIntegrable_deriv (by
      rw [Filter.EventuallyLE, Measure.restrict_congr_set Ioo_ae_eq_Icc.symm,
        ae_restrict_iff' measurableSet_Ioo]
      exact hd)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

end UnknownLoads.Coxian.T3aux

namespace UnknownLoads.Coxian.T3aux
open UnknownLoads.Coxian

lemma sub_core {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}
    (sys : System P Ω μP) (T : ℝ) (BT : ℕ) (ω : Ω) (hω : IsNicePath sys T BT ω)
    (ε t0 t1 σ c : ℝ) (hε : 0 < ε) (ht0 : 1 ≤ t0) (ht01 : t0 ≤ t1)
    (hσ : σ = t1 + ((ellStar P : ℝ) + 1) / (eta P * ε)) (hσT : σ ≤ T)
    (hdiff : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ (fluidU P sys.sLim) t)
    (hu : ∀ t ≥ t0, (ellStar P : ℝ) + 3 * ε < fluidU P sys.sLim t ∧
        -(eta P * ε) < deriv (fluidU P sys.sLim) t)
    (hc : c = fluidU P sys.sLim t0)
    (hz1 : c * Real.exp (-(eta P) * (t1 - t0)) ≤ ε / (2 * ((P.Δ : ℝ) + 1)))
    (h17 : TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) => uMass (sys.s n ω t)) (fluidU P sys.sLim)
      atTop (Set.Icc 0 T))
    (N : ℕ)
    (hgood : ∀ n ≥ N, ∀ t ∈ Set.Icc (0:ℝ) T, InS (sys.s n ω t) ∧ qOf (sys.s n ω t) (BT + 1) = 0)
    (hℓ : ∀ n ≥ N, ∀ t ∈ Set.Icc t0 T, (sys.ℓ n ω t : ℤ) = floorDelta P.Δ (rho P))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (hφN : ∀ k, N ≤ φ k) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ x z : ℝ → ℝ,
      TendstoUniformlyOn (fun k t => xMass P (sys.s (φ (ψ k)) ω t)) x atTop (Set.Icc 0 T) ∧
      TendstoUniformlyOn (fun k t => zMass P (sys.s (φ (ψ k)) ω t)) z atTop (Set.Icc 0 T) ∧
      (∀ t ∈ Set.Icc σ T, x t = ellStar P) ∧
      (∀ t ∈ Set.Icc σ T, z t * Real.exp (eta P * (t - σ)) ≤ c) := by
  obtain ⟨ψ, hψ, g, hg⟩ := hω.2.1.2.2.2.1 φ hφ
  have hφ' : StrictMono (fun k => φ (ψ k)) := hφ.comp hψ
  have hφ'N : ∀ k, N ≤ φ (ψ k) := fun k => hφN (ψ k)
  set η := eta P with hηdef
  have hη : 0 < η := eta_pos P
  have hηε : 0 < η * ε := mul_pos hη hε
  set ℓ : ℝ := (ellStar P : ℝ) with hℓdef
  have hℓ0 : 0 ≤ ℓ := Nat.cast_nonneg _
  have hD := Delta_pos P
  have hgap : 0 < (ℓ + 1) / (η * ε) := div_pos (by linarith) hηε
  have ht1σ : t1 < σ := by rw [hσ]; linarith
  have ht0T : t0 < T := by linarith
  have hT0 : (0:ℝ) ≤ T := by linarith
  obtain ⟨x, y, z, hx, hy, hz, hxac, hyac, hzac, hi, hii⟩ :=
    proposition_18 sys T BT ω hω (fun k => φ (ψ k)) hφ' g hg t0 T (by linarith) ht0T le_rfl
      (fun k t ht => hℓ _ (hφ'N k) t ht)
  set u := fluidU P sys.sLim with hudef
  -- pointwise facts on [0, T]
  have hfacts : ∀ t ∈ Set.Icc (0:ℝ) T, x t + y t + z t = u t ∧ 0 ≤ x t ∧ x t ≤ ℓ ∧
      0 ≤ y t ∧ 0 ≤ z t := by
    intro t ht
    have hxt := hx.tendsto_at ht
    have hyt := hy.tendsto_at ht
    have hzt := hz.tendsto_at ht
    have hut := (h17.tendsto_at ht).comp hφ'.tendsto_atTop
    have hgk := fun k => hgood _ (hφ'N k) t ht
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply tendsto_nhds_unique ((hxt.add hyt).add hzt)
      refine hut.congr (fun k => ?_)
      simp only [Function.comp]
      exact mass_decomp P (hgk k).1 (hgk k).2
    · exact ge_of_tendsto' hxt (fun k => xMass_nonneg P (hgk k).1)
    · exact le_of_tendsto' hxt (fun k => xMass_le P (hgk k).1)
    · exact ge_of_tendsto' hyt (fun k => yMass_nonneg P (hgk k).1)
    · exact ge_of_tendsto' hzt (fun k => zMass_nonneg P (hgk k).1)
  have hsub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → Set.uIcc a b ⊆ Set.uIcc 0 T := by
    intro a b h1 h2 h3
    rw [Set.uIcc_of_le h2, Set.uIcc_of_le hT0]
    exact Set.Icc_subset_Icc h1 h3
  -- (28)
  have hzb : ∀ t ∈ Set.Icc t0 T, z t ≤ z t0 * Real.exp (-η * (t - t0)) := by
    intro t ht
    apply gronwall_ac ht.1 (hzac.mono (hsub t0 t (by linarith) ht.1 ht.2))
    filter_upwards [hii] with τ h hτ
    exact h ⟨hτ.1, hτ.2.trans ht.2⟩
  have ht0mem : t0 ∈ Set.Icc (0:ℝ) T := ⟨by linarith, ht0T.le⟩
  have hzt0c : z t0 ≤ c := by
    obtain ⟨h1, h2, _, h4, _⟩ := hfacts t0 ht0mem
    rw [hc]; linarith
  have hzt0 : 0 ≤ z t0 := (hfacts t0 ht0mem).2.2.2.2
  have hzc : ∀ t ∈ Set.Icc t0 T, z t ≤ c * Real.exp (-η * (t - t0)) := by
    intro t ht
    exact (hzb t ht).trans (mul_le_mul_of_nonneg_right hzt0c (Real.exp_pos _).le)
  have hzsmall : ∀ t ∈ Set.Icc t1 T, z t ≤ ε / (2 * ((P.Δ : ℝ) + 1)) := by
    intro t ht
    have h1 := hzc t ⟨ht01.trans ht.1, ht.2⟩
    have hc0 : 0 ≤ c := hzt0.trans hzt0c
    have h2 : Real.exp (-η * (t - t0)) ≤ Real.exp (-(eta P) * (t1 - t0)) := by
      apply Real.exp_le_exp.2
      have : t1 - t0 ≤ t - t0 := by linarith [ht.1]
      nlinarith
    calc z t ≤ c * Real.exp (-η * (t - t0)) := h1
      _ ≤ c * Real.exp (-(eta P) * (t1 - t0)) := mul_le_mul_of_nonneg_left h2 hc0
      _ ≤ _ := hz1
  -- derivative of x where x < ℓ
  have hD' : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Ioo t1 T → x τ < ℓ → η * ε ≤ deriv x τ := by
    set Bad : Set ℝ := {τ | τ ∈ Set.Ioo t1 T ∧ x τ < ℓ ∧ ¬ (η * ε ≤ deriv x τ)} with hBad
    have hnull : volume Bad = 0 := by
      apply measure_null_of_locally_null Bad
      intro τ0 h0
      obtain ⟨V, hV, hVae⟩ := hi τ0 ⟨by linarith [h0.1.1], h0.1.2⟩ h0.2.1
      refine ⟨Bad ∩ V, inter_mem_nhdsWithin Bad hV, ?_⟩
      have hQ : ∀ᵐ τ ∂(volume : Measure ℝ),
          (τ ∈ V → deriv y τ ≤ -(eta P) * (y τ - (P.Δ : ℝ) * z τ)) ∧
          (τ ∈ Set.uIcc 0 T → DifferentiableAt ℝ x τ) ∧
          (τ ∈ Set.uIcc 0 T → DifferentiableAt ℝ y τ) ∧
          (τ ∈ Set.uIcc 0 T → DifferentiableAt ℝ z τ) ∧
          (τ ∈ Set.Icc t0 T → deriv z τ ≤ -(eta P) * z τ) := by
        filter_upwards [hVae, hxac.ae_differentiableAt, hyac.ae_differentiableAt,
          hzac.ae_differentiableAt, hii] with τ h1 h2 h3 h4 h5 using ⟨h1, h2, h3, h4, h5⟩
      apply measure_mono_null _ (ae_iff.1 hQ)
      intro τ hτ hq
      obtain ⟨⟨⟨hτ1, hτ2⟩, hxτ, hbad⟩, hτV⟩ := hτ
      obtain ⟨q1, q2, q3, q4, q5⟩ := hq
      apply hbad
      have hτ0 : 0 < τ := by linarith
      have hτu : τ ∈ Set.uIcc 0 T := by rw [Set.uIcc_of_le hT0]; exact ⟨hτ0.le, hτ2.le⟩
      have hxd := q2 hτu
      have hyd := q3 hτu
      have hzd := q4 hτu
      have hud := hdiff τ hτ0
      have heq : x =ᶠ[𝓝 τ] fun t => u t - y t - z t := by
        filter_upwards [Ioo_mem_nhds hτ0 hτ2] with t ht
        obtain ⟨e1, _⟩ := hfacts t ⟨ht.1.le, ht.2.le⟩
        linarith
      have hder : deriv x τ = deriv u τ - deriv y τ - deriv z τ := by
        rw [heq.deriv_eq, deriv_fun_sub (hud.fun_sub hyd) hzd, deriv_fun_sub hud hyd]
      have hyτ := q1 hτV
      have hzτ := q5 ⟨by linarith, hτ2.le⟩
      obtain ⟨e1, _, _, _, hz0⟩ := hfacts τ ⟨hτ0.le, hτ2.le⟩
      have hzs := hzsmall τ ⟨hτ1.le, hτ2.le⟩
      have hzs' : z τ * (2 * ((P.Δ : ℝ) + 1)) ≤ ε := by
        rwa [le_div_iff₀ (by positivity)] at hzs
      obtain ⟨hu1, hu2⟩ := hu τ (by linarith)
      have hA : 5 / 2 * ε ≤ y τ - (P.Δ : ℝ) * z τ := by nlinarith
      have hB := mul_le_mul_of_nonneg_left hA hη.le
      have hC : 0 ≤ η * z τ := mul_nonneg hη.le hz0
      rw [hder]
      simp only [← hηdef] at hyτ hzτ hu2
      nlinarith
    rw [ae_iff]
    apply measure_mono_null _ hnull
    intro τ hτ
    simp only [Set.mem_setOf_eq, _root_.not_imp] at hτ
    exact ⟨hτ.1, hτ.2.1, hτ.2.2⟩
  have hxcont : ContinuousOn x (Set.Icc 0 T) := by
    have := hxac.continuousOn; rwa [Set.uIcc_of_le hT0] at this
  have hftc : ∀ a b : ℝ, t1 ≤ a → a ≤ b → b ≤ T → (∀ τ ∈ Set.Ioo a b, x τ < ℓ) →
      η * ε * (b - a) ≤ x b - x a := by
    intro a b ha hab hb hlt
    apply ftc_lower hab (hxac.mono (hsub a b (by linarith) hab hb))
    filter_upwards [hD'] with τ h hτ
    exact h ⟨lt_of_le_of_lt ha hτ.1, lt_of_lt_of_le hτ.2 hb⟩ (hlt τ hτ)
  -- (29)
  have hxreach : ∀ t ∈ Set.Icc σ T, x t = ℓ := by
    intro t ht
    have htm : t ∈ Set.Icc (0:ℝ) T := ⟨by linarith [ht.1], ht.2⟩
    by_contra hne
    have hlt : x t < ℓ := lt_of_le_of_ne (hfacts t htm).2.2.1 hne
    set S : Set ℝ := Set.Icc t1 t ∩ x ⁻¹' Set.Ici ℓ with hS
    have ht1t : t1 ≤ t := by linarith [ht.1]
    by_cases hSne : S.Nonempty
    · have hSc : IsClosed S :=
        ContinuousOn.preimage_isClosed_of_isClosed
          (hxcont.mono (Set.Icc_subset_Icc (by linarith) ht.2)) isClosed_Icc isClosed_Ici
      have hSb : BddAbove S := ⟨t, fun τ hτ => hτ.1.2⟩
      have ha := hSc.csSup_mem hSne hSb
      set a := sSup S
      have hlt' : ∀ τ ∈ Set.Ioo a t, x τ < ℓ := by
        intro τ hτ
        by_contra h
        have : τ ∈ S := ⟨⟨by linarith [ha.1.1, hτ.1], hτ.2.le⟩, not_lt.1 h⟩
        linarith [le_csSup hSb this, hτ.1]
      have := hftc a t ha.1.1 ha.1.2 ht.2 hlt'
      have hxa : ℓ ≤ x a := ha.2
      have : 0 ≤ η * ε * (t - a) := mul_nonneg hηε.le (by linarith [ha.1.2])
      linarith
    · have hall : ∀ τ ∈ Set.Ioo t1 t, x τ < ℓ := by
        intro τ hτ
        by_contra h
        exact hSne ⟨τ, ⟨hτ.1.le, hτ.2.le⟩, not_lt.1 h⟩
      have h1 := hftc t1 t le_rfl ht1t ht.2 hall
      have hx1 : 0 ≤ x t1 := (hfacts t1 ⟨by linarith, by linarith [ht.2]⟩).2.1
      have h2 : (ℓ + 1) / (η * ε) ≤ t - t1 := by rw [hσ] at ht; linarith [ht.1]
      have h3 : η * ε * ((ℓ + 1) / (η * ε)) = ℓ + 1 := by field_simp
      have h4 := mul_le_mul_of_nonneg_left h2 hηε.le
      linarith
  refine ⟨ψ, hψ, x, z, hx, hz, hxreach, ?_⟩
  intro t ht
  have h1 := hzc t ⟨by linarith [ht.1], ht.2⟩
  have hc0 : 0 ≤ c := hzt0.trans hzt0c
  calc z t * Real.exp (η * (t - σ)) ≤ c * Real.exp (-η * (t - t0)) * Real.exp (η * (t - σ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = c * Real.exp (-η * (σ - t0)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ c * 1 := by
        apply mul_le_mul_of_nonneg_left _ hc0
        rw [Real.exp_le_one_iff]
        nlinarith
    _ = c := mul_one c

end UnknownLoads.Coxian.T3aux
open UnknownLoads.Coxian UnknownLoads.Coxian.T3aux

theorem solution {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}
    (sys : System P Ω μP) (hρ : ∀ i : ℕ, rho P ≠ (i : ℝ) * (P.Δ : ℝ)) :
    ∃ σ η c : ℝ, 0 < σ ∧ 0 < η ∧ 0 < c ∧ ∀ T : ℝ, ∀ᵐ ω ∂μP,
      TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) => (sys.ℓ n ω t : ℝ))
          (fun _ => ((floorDelta P.Δ (rho P) : ℤ) : ℝ)) atTop (Set.Icc σ T) ∧
      (∀ i : ℕ, (i : ℤ) ≤ floorDelta P.Δ (rho P) →
          TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) => sys.q n ω t i) (fun _ => (1 : ℝ)) atTop
            (Set.Icc σ T)) ∧
      Filter.limsup (fun n : ℕ => ⨆ t ∈ Set.Icc σ T,
          (∑' i : ℕ, if floorDelta P.Δ (rho P) + (P.Δ : ℤ) < (i : ℤ)
              then ENNReal.ofReal (sys.q n ω t i) else 0) *
            ENNReal.ofReal (Real.exp (η * (t - σ)))) atTop ≤ ENNReal.ofReal c := by
  obtain ⟨hdiff, hlim, hdlim⟩ := fluid_u_limits sys.sLim sys.sLim_mem
  set u := fluidU P sys.sLim with hudef
  set ρ := rho P with hρdef
  set ℓ : ℝ := (ellStar P : ℝ) with hℓdef
  have hℓ0 : 0 ≤ ℓ := Nat.cast_nonneg _
  have hD := Delta_pos P
  have hℓρ : ℓ < ρ := lt_of_le_of_ne (ell_le_rho P) (ell_ne_rho P hρ)
  have hρℓ : ρ < ℓ + P.Δ := rho_lt_ell_add P
  set ε := min (ρ - ℓ) (ℓ + P.Δ - ρ) / 4 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]; apply div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hε1 : 4 * ε ≤ ρ - ℓ := by rw [hεdef]; linarith [min_le_left (ρ - ℓ) (ℓ + P.Δ - ρ)]
  have hε2 : 4 * ε ≤ ℓ + P.Δ - ρ := by
    rw [hεdef]; linarith [min_le_right (ρ - ℓ) (ℓ + P.Δ - ρ)]
  set η := eta P with hηdef
  have hη : 0 < η := eta_pos P
  have hηε : 0 < η * ε := mul_pos hη hε
  obtain ⟨A1, hA1⟩ := Metric.tendsto_atTop.1 hlim ε hε
  obtain ⟨A2, hA2⟩ := Metric.tendsto_atTop.1 hdlim (η * ε) hηε
  set t0 := max (max A1 A2) 1 with ht0def
  have ht0 : 1 ≤ t0 := le_max_right _ _
  have hu : ∀ t ≥ t0, ℓ + 3 * ε < u t ∧ -(η * ε) < deriv u t ∧ u t < ℓ + P.Δ - 3 * ε := by
    intro t ht
    have h1 := hA1 t (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht)
    have h2 := hA2 t (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht)
    rw [Real.dist_eq] at h1 h2
    rw [sub_zero] at h2
    have := abs_lt.1 h1
    have := abs_lt.1 h2
    refine ⟨by linarith, by linarith, by linarith⟩
  set c := u t0 with hcdef
  have hc0 : 0 < c := by linarith [(hu t0 le_rfl).1]
  set K := 2 * ((P.Δ : ℝ) + 1) * c / ε with hKdef
  have hK : 0 < K := by positivity
  set L := max 0 (Real.log K / η) with hLdef
  set t1 := t0 + L with ht1def
  have hL0 : 0 ≤ L := le_max_left _ _
  have ht01 : t0 ≤ t1 := by linarith
  set σ := t1 + (ℓ + 1) / (η * ε) with hσdef
  have ht0σ : t0 < σ := by
    have : 0 < (ℓ + 1) / (η * ε) := div_pos (by linarith) hηε
    rw [hσdef]; linarith
  have hσpos : 0 < σ := by linarith
  have hz1 : c * Real.exp (-(eta P) * (t1 - t0)) ≤ ε / (2 * ((P.Δ : ℝ) + 1)) := by
    have hLK : Real.log K ≤ η * L := by
      have := le_max_right 0 (Real.log K / η)
      rw [← hLdef, div_le_iff₀ hη] at this; linarith
    have h1 : Real.exp (-(eta P) * (t1 - t0)) ≤ K⁻¹ := by
      rw [← Real.exp_log hK, ← Real.exp_neg]
      apply Real.exp_le_exp.2
      rw [← hηdef]
      have : t1 - t0 = L := by rw [ht1def]; ring
      rw [this]; linarith
    calc c * Real.exp (-(eta P) * (t1 - t0)) ≤ c * K⁻¹ := mul_le_mul_of_nonneg_left h1 hc0.le
      _ = ε / (2 * ((P.Δ : ℝ) + 1)) := by rw [hKdef]; field_simp
  refine ⟨σ, η, c, hσpos, hη, hc0, fun T => ?_⟩
  by_cases hTσ : T < σ
  · have hE : Set.Icc σ T = ∅ := Set.Icc_eq_empty (not_le.2 hTσ)
    refine Filter.Eventually.of_forall (fun ω => ?_)
    refine ⟨by rw [hE]; exact tendstoUniformlyOn_empty,
      fun i _ => by rw [hE]; exact tendstoUniformlyOn_empty, ?_⟩
    simp [hE]
  push Not at hTσ
  have hT : 0 < T := by linarith
  obtain ⟨BT, _, h16⟩ := proposition_16 sys T hT
  filter_upwards [h16] with ω hω
  have h17 := proposition_17 sys T BT ω hω
  obtain ⟨nT, hnT⟩ := hω.2.2.1
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 h17) ε hε)
  set N := max (max N0 nT) 1 with hNdef
  have hN1 : ∀ n ≥ N, 1 ≤ n := fun n hn => le_trans (le_max_right _ _) hn
  have hNT : ∀ n ≥ N, nT ≤ n := fun n hn =>
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hN0' : ∀ n ≥ N, N0 ≤ n := fun n hn =>
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hgood : ∀ n ≥ N, ∀ t ∈ Set.Icc (0:ℝ) T,
      InS (sys.s n ω t) ∧ qOf (sys.s n ω t) (BT + 1) = 0 := by
    intro n hn t ht
    exact ⟨(hω.1 n (hN1 n hn)).1 t ht.1, (hnT n (hNT n hn) t ht).1⟩
  have hℓeq : ∀ n ≥ N, ∀ t ∈ Set.Icc t0 T,
      (sys.ℓ n ω t : ℤ) = floorDelta P.Δ (rho P) := by
    intro n hn t ht
    have htm : t ∈ Set.Icc (0:ℝ) T := ⟨by linarith [ht.1], ht.2⟩
    rw [(hω.1 n (hN1 n hn)).2.2.2.2.2 t htm.1, floorDelta_rho]
    have h1 := hN0 n (hN0' n hn) t htm
    rw [Real.dist_eq] at h1
    have := abs_lt.1 h1
    have hut := hu t ht.1
    apply floorDelta_eq_of_mem P <;> linarith
  have hsub := sub_core sys T BT ω hω ε t0 t1 σ c hε ht0 ht01 rfl hTσ hdiff
    (fun t ht => ⟨(hu t ht).1, (hu t ht).2.1⟩) rfl hz1 h17 N hgood hℓeq
  have hσsub : Set.Icc σ T ⊆ Set.Icc (0:ℝ) T := Set.Icc_subset_Icc (by linarith) le_rfl
  have hσsub0 : ∀ t ∈ Set.Icc σ T, t0 ≤ t := fun t ht => by linarith [ht.1, ht0σ]
  refine ⟨?_, ?_, ?_⟩
  · -- (8a)
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [eventually_ge_atTop N] with n hn t ht
    have := hℓeq n hn t ⟨hσsub0 t ht, ht.2⟩
    rw [← this]
    simp [hδ]
  · -- (8b)
    intro i hi
    have hi' : i ≤ ellStar P := by rw [floorDelta_rho] at hi; exact_mod_cast hi
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · rw [Metric.tendstoUniformlyOn_iff]
      intro δ hδ
      refine Filter.Eventually.of_forall (fun n t _ => ?_)
      simp [System.q, qOf_zero, hδ]
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop (hcon.and_eventually (eventually_ge_atTop N))
    obtain ⟨ψ, _, x, z, hx, _, hxℓ, _⟩ := hsub φ hφ (fun k => (hP k).2)
    obtain ⟨K0, hK0⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hx δ hδ)
    have h0 := (hP (ψ K0)).1
    push Not at h0
    obtain ⟨t, ht, hge⟩ := h0
    have htm := hσsub ht
    have h1 := hK0 K0 le_rfl t htm
    rw [hxℓ t ht] at h1
    have hgk := hgood (φ (ψ K0)) (hP _).2 t htm
    have h2 := one_sub_q_le P hgk.1 hi1 hi'
    have h3 := qOf_le_one hgk.1 i
    simp only [System.q] at hge
    rw [Real.dist_eq] at h1 hge
    rw [abs_of_nonneg (by linarith)] at hge
    have := le_abs_self ((ellStar P : ℝ) - xMass P (sys.s (φ (ψ K0)) ω t))
    linarith
  · -- (8c)
    set E := Real.exp (η * (T - σ)) with hEdef
    have hEpos : 0 < E := Real.exp_pos _
    have key : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ t ∈ Set.Icc σ T,
        zMass P (sys.s n ω t) * Real.exp (η * (t - σ)) ≤ c + δ := by
      intro δ hδ
      by_contra hcon
      rw [not_eventually] at hcon
      obtain ⟨φ, hφ, hP⟩ :=
        extraction_of_frequently_atTop (hcon.and_eventually (eventually_ge_atTop N))
      obtain ⟨ψ, _, x, z, _, hz, _, hzc⟩ := hsub φ hφ (fun k => (hP k).2)
      obtain ⟨K0, hK0⟩ := eventually_atTop.1
        (Metric.tendstoUniformlyOn_iff.1 hz (δ / E) (div_pos hδ hEpos))
      have h0 := (hP (ψ K0)).1
      push Not at h0
      obtain ⟨t, ht, hge⟩ := h0
      have htm := hσsub ht
      have h1 := hK0 K0 le_rfl t htm
      rw [Real.dist_eq] at h1
      have h1' := (abs_lt.1 h1).1
      have he : Real.exp (η * (t - σ)) ≤ E := by
        apply Real.exp_le_exp.2
        have := ht.2
        nlinarith
      have hep : 0 < Real.exp (η * (t - σ)) := Real.exp_pos _
      have h2 := hzc t ht
      have h3 : zMass P (sys.s (φ (ψ K0)) ω t) ≤ z t + δ / E := by linarith
      have h4 := mul_le_mul_of_nonneg_right h3 hep.le
      have h5 : δ / E * Real.exp (η * (t - σ)) ≤ δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hEpos]
        exact mul_le_mul_of_nonneg_left he hδ.le
      nlinarith
    apply ENNReal.le_of_forall_pos_le_add
    intro δ hδ _
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add hc0.le δ.coe_nonneg]
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [key δ (NNReal.coe_pos.2 hδ), eventually_ge_atTop N] with n hn hnN
    apply iSup₂_le
    intro t ht
    have hgk := hgood n hnN t (hσsub ht)
    rw [floorDelta_rho]
    have htail : (∑' i : ℕ, if ((ellStar P : ℕ) : ℤ) + (P.Δ : ℤ) < (i : ℤ)
        then ENNReal.ofReal (sys.q n ω t i) else 0) = ENNReal.ofReal (zMass P (sys.s n ω t)) :=
      tail_ennreal P hgk.1 hgk.2
    rw [htail, ← ENNReal.ofReal_mul (zMass_nonneg P hgk.1)]
    exact ENNReal.ofReal_le_ofReal (hn t ht)
