-- Prove2me | solution 1 for SpeedFactory.BreakEven.eq_18
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:31:01.850759+00:00
-- url     : https://prove2.me/submissions/e5eda659-cb15-44b0-a855-a279fd05d7ef

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model
import Definitions.Def_SpeedFactory_BreakEven_Dynamics

open MeasureTheory ProbabilityTheory Filter Topology Set
open SpeedFactory.BreakEven


namespace SFAux

noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

lemma phi_eq (x : ℝ) :
    stdNormalPDF x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [stdNormalPDF, gaussianPDFReal_def]

lemma phi_pos (x : ℝ) : 0 < stdNormalPDF x := gaussianPDFReal_pos _ _ _ one_ne_zero

lemma phi_neg (x : ℝ) : stdNormalPDF (-x) = stdNormalPDF x := by
  rw [phi_eq, phi_eq]; ring_nf

lemma phi_hasDerivAt (x : ℝ) : HasDerivAt stdNormalPDF (-x * stdNormalPDF x) x := by
  have h : HasDerivAt (fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2))
      ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-x ^ 2 / 2) * (-(2 * x ^ 1 * 1) / 2))) x := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.exp
    exact (((hasDerivAt_id x).pow 2).neg).div_const 2
  have hf : stdNormalPDF = fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) :=
    funext phi_eq
  rw [hf]
  convert h using 1
  ring

lemma phi_continuous : Continuous stdNormalPDF := by
  have hf : stdNormalPDF = fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) :=
    funext phi_eq
  rw [hf]; fun_prop

lemma integrable_phi : Integrable stdNormalPDF := integrable_gaussianPDFReal 0 1

lemma Phi_eq_integral (x : ℝ) : Phi x = ∫ t in Iic x, stdNormalPDF t := by
  rw [Phi, cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal]
  · rfl
  · exact setIntegral_nonneg measurableSet_Iic (fun t _ => (phi_pos t).le)

lemma Phi_hasDerivAt (x : ℝ) : HasDerivAt Phi (stdNormalPDF x) x := by
  have h : ∀ y, Phi y = Phi 0 + ∫ t in (0:ℝ)..y, stdNormalPDF t := by
    intro y
    rw [Phi_eq_integral, Phi_eq_integral,
      ← intervalIntegral.integral_Iic_sub_Iic integrable_phi.integrableOn integrable_phi.integrableOn]
    ring
  have : Phi = fun y => Phi 0 + ∫ t in (0:ℝ)..y, stdNormalPDF t := funext h
  rw [this]
  exact ((phi_continuous.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _

lemma Phi_continuous : Continuous Phi :=
  continuous_iff_continuousAt.mpr fun x => (Phi_hasDerivAt x).continuousAt

lemma Phi_strictMono : StrictMono Phi :=
  strictMono_of_hasDerivAt_pos Phi_hasDerivAt phi_pos

lemma Phi_atTop : Tendsto Phi atTop (𝓝 1) := tendsto_cdf_atTop _
lemma Phi_atBot : Tendsto Phi atBot (𝓝 0) := tendsto_cdf_atBot _

lemma Phi_neg (x : ℝ) : Phi (-x) = 1 - Phi x := by
  have hd : ∀ y, HasDerivAt (fun y => Phi y + Phi (-y)) 0 y := by
    intro y
    have h1 := Phi_hasDerivAt y
    have h2 := (Phi_hasDerivAt (-y)).comp y (hasDerivAt_neg y)
    have h3 := h1.add h2
    rw [phi_neg, show stdNormalPDF y + stdNormalPDF y * -1 = 0 by ring] at h3
    exact h3
  have hconst : ∀ y, Phi y + Phi (-y) = Phi 0 + Phi (-0) := fun y =>
    is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv) y 0
  have hlim : Tendsto (fun y => Phi y + Phi (-y)) atTop (𝓝 (1 + 0)) :=
    Phi_atTop.add (Phi_atBot.comp tendsto_neg_atTop_atBot)
  have hlim2 : Tendsto (fun y => Phi y + Phi (-y)) atTop (𝓝 (Phi 0 + Phi (-0))) := by
    simp_rw [hconst]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hlim hlim2
  have := hconst x
  linarith

lemma Phi_quantile {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : Phi (stdNormalQuantile r) = r := by
  set S := {z : ℝ | cdf (gaussianReal 0 1) z ≤ r} with hS
  have hne : S.Nonempty := by
    have := (Phi_atBot.eventually (gt_mem_nhds hr0)).exists
    obtain ⟨z, hz⟩ := this
    exact ⟨z, le_of_lt hz⟩
  obtain ⟨Z, hZ⟩ := (eventually_atTop.mp (Phi_atTop.eventually (lt_mem_nhds hr1)))
  have hbdd : BddAbove S := by
    refine ⟨Z, fun z hz => ?_⟩
    by_contra h
    have := hZ z (le_of_lt (lt_of_not_ge h))
    exact absurd hz (not_le.mpr this)
  have hclosed : IsClosed S := isClosed_le Phi_continuous continuous_const
  have hmem : sSup S ∈ S := hclosed.csSup_mem hne hbdd
  have hq : stdNormalQuantile r = sSup S := rfl
  rw [hq]
  apply le_antisymm hmem
  have hgt : ∀ y > sSup S, r < Phi y := by
    intro y hy
    by_contra h
    exact absurd (le_csSup hbdd (show y ∈ S from le_of_not_gt h)) (not_le.mpr hy)
  have ht : Tendsto Phi (𝓝[>] (sSup S)) (𝓝 (Phi (sSup S))) :=
    (Phi_continuous.tendsto _).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun y hy => (hgt y hy).le)


/-- The standard normal first-order loss function `L(c) = E[(c + Z)⁺] = φ(c) + cΦ(c)`. -/
noncomputable def Lf (c : ℝ) : ℝ := stdNormalPDF c + c * Phi c

lemma Lf_hasDerivAt (c : ℝ) : HasDerivAt Lf (Phi c) c := by
  have h := (phi_hasDerivAt c).add ((hasDerivAt_id c).mul (Phi_hasDerivAt c))
  exact h.congr_deriv (by simp)

lemma phi_tendsto_atTop : Tendsto stdNormalPDF atTop (𝓝 0) := by
  have hf : stdNormalPDF = fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) :=
    funext phi_eq
  rw [hf]
  have h1 : Tendsto (fun y : ℝ => -y ^ 2 / 2) atTop atBot := by
    have := (tendsto_pow_atTop (α := ℝ) two_ne_zero)
    exact (tendsto_neg_atTop_atBot.comp this).atBot_div_const (by norm_num)
  have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  simpa using h2

lemma integrable_mul_phi : Integrable (fun z => z * stdNormalPDF z) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := 1/2) (by norm_num)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  refine h.congr (ae_of_all _ fun z => ?_)
  simp only [phi_eq]
  ring_nf

lemma integral_Ioi_phi (a : ℝ) : ∫ z in Ioi a, stdNormalPDF z = 1 - Phi a := by
  have h := integral_add_compl (measurableSet_Iic (a := a)) integrable_phi
  rw [compl_Iic, ← Phi_eq_integral] at h
  have h1 : ∫ z, stdNormalPDF z = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero
  linarith

lemma integral_Ioi_mul_phi (a : ℝ) : ∫ z in Ioi a, z * stdNormalPDF z = stdNormalPDF a := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun z => -stdNormalPDF z)
    (f' := fun z => z * stdNormalPDF z) (a := a) (m := 0)
    (phi_continuous.neg.continuousWithinAt)
    (fun x _ => by
      exact (phi_hasDerivAt x).neg.congr_deriv (by ring))
    integrable_mul_phi.integrableOn
    (by simpa using phi_tendsto_atTop.neg)
  rw [h]; ring

lemma integral_posPart_std (c : ℝ) :
    ∫ z, max (c + z) 0 ∂(gaussianReal 0 1) = Lf c := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpt : ∀ z, gaussianPDFReal 0 1 z • max (c + z) 0
      = (Ioi (-c)).indicator (fun z => c * stdNormalPDF z + z * stdNormalPDF z) z := by
    intro z
    by_cases hz : -c < z
    · rw [indicator_of_mem (show z ∈ Ioi (-c) from hz), max_eq_left (by linarith), smul_eq_mul]
      simp only [stdNormalPDF]; ring
    · rw [indicator_of_notMem (show z ∉ Ioi (-c) from hz), max_eq_right (by linarith)]
      simp
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Ioi,
    integral_add (integrable_phi.const_mul c).integrableOn integrable_mul_phi.integrableOn,
    integral_const_mul, integral_Ioi_phi, integral_Ioi_mul_phi, Phi_neg, phi_neg, Lf]
  ring

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integrable_of_hasLaw {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : NNReal}
    (hX : HasLaw X (gaussianReal m v) P) : Integrable X P := by
  have h1 : Integrable id (gaussianReal m v) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)
  rw [← hX.map_eq] at h1
  exact (integrable_map_measure aestronglyMeasurable_id hX.aemeasurable).mp h1

lemma integral_of_hasLaw {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : NNReal}
    (hX : HasLaw X (gaussianReal m v) P) : ∫ ω, X ω ∂P = m := by
  rw [show (fun ω => X ω) = X from rfl, hX.integral_eq, integral_id_gaussianReal]

lemma integral_max_sub {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : NNReal}
    (hX : HasLaw X (gaussianReal m v) P) (hv : v ≠ 0) (a : ℝ) :
    ∫ ω, max (X ω - a) 0 ∂P = Real.sqrt v * Lf ((m - a) / Real.sqrt v) := by
  set s := Real.sqrt v with hs
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (fun h => hv (NNReal.coe_eq_zero.mp h.symm))
  have hs0 : 0 < s := Real.sqrt_pos.mpr hv'
  have hZ := gaussianReal_div_const (gaussianReal_sub_const hX m) s
  have hZ' : HasLaw (fun ω => (X ω - m) / s) (gaussianReal 0 1) P := by
    convert hZ using 2
    · simp
    · ext; simp [hs, Real.sq_sqrt hv'.le, hv'.ne']
  have hpt : ∀ ω, max (X ω - a) 0 = s * max ((m - a) / s + (X ω - m) / s) 0 := by
    intro ω
    rw [show s * max ((m - a) / s + (X ω - m) / s) 0
        = max (s * ((m - a) / s + (X ω - m) / s)) (s * 0) from mul_max_of_nonneg _ _ hs0.le,
      mul_zero]
    congr 1
    field_simp
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  have := hZ'.integral_comp (f := fun z => max ((m - a) / s + z) 0)
    (by fun_prop)
  simp only [Function.comp_def] at this
  rw [this, integral_posPart_std]

lemma integrable_max_sub {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : NNReal}
    (hX : HasLaw X (gaussianReal m v) P) (a : ℝ) [IsFiniteMeasure P] :
    Integrable (fun ω => max (X ω - a) 0) P :=
  ((integrable_of_hasLaw hX).sub (integrable_const a)).pos_part

/-- Newsvendor function `N(c) = (A + B) L(c) − B c = E[A (c+Z)⁺ + B (c+Z)⁻]`. -/
noncomputable def NV (A B c : ℝ) : ℝ := (A + B) * Lf c - B * c

lemma NV_hasDerivAt (A B c : ℝ) : HasDerivAt (NV A B) ((A + B) * Phi c - B) c := by
  have := ((Lf_hasDerivAt c).const_mul (A + B)).sub ((hasDerivAt_id c).const_mul B)
  exact this.congr_deriv (by simp)

lemma NV_min {A B c0 : ℝ} (hA : 0 < A) (hB : 0 < B) (hc0 : Phi c0 = B / (A + B)) :
    NV A B c0 = (A + B) * stdNormalPDF c0 ∧ ∀ c, c ≠ c0 → NV A B c0 < NV A B c := by
  have hAB : 0 < A + B := by linarith
  refine ⟨?_, ?_⟩
  · simp only [NV, Lf]
    rw [hc0]; field_simp; ring
  · intro c hc
    have hcont : Continuous (NV A B) :=
      continuous_iff_continuousAt.mpr fun x => (NV_hasDerivAt A B x).continuousAt
    have hd : ∀ ξ, (A + B) * Phi ξ - B = (A + B) * (Phi ξ - Phi c0) := by
      intro ξ; rw [hc0]; field_simp
    rcases lt_or_gt_of_ne hc with h | h
    · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (NV A B) _ h hcont.continuousOn
        (fun x _ => NV_hasDerivAt A B x)
      rw [hd, eq_div_iff (by linarith)] at hslope
      have h1 : Phi ξ - Phi c0 < 0 := by linarith [Phi_strictMono hξ.2]
      have h2 : (A + B) * (Phi ξ - Phi c0) < 0 := mul_neg_of_pos_of_neg hAB h1
      nlinarith
    · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (NV A B) _ h hcont.continuousOn
        (fun x _ => NV_hasDerivAt A B x)
      rw [hd, eq_div_iff (by linarith)] at hslope
      have h1 : 0 < Phi ξ - Phi c0 := by linarith [Phi_strictMono hξ.1]
      have h2 : 0 < (A + B) * (Phi ξ - Phi c0) := mul_pos hAB h1
      nlinarith

end SFAux



namespace SFAux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma hasLaw_const {P : Measure Ω} [IsProbabilityMeasure P] (c : ℝ) :
    HasLaw (fun _ : Ω => c) (gaussianReal c 0) P where
  aemeasurable := aemeasurable_const
  map_eq := by rw [gaussianReal_zero_var, Measure.map_const]; simp

lemma hasLaw_lin {P : Measure Ω} [IsProbabilityMeasure P] {e : ℕ → Ω → ℝ} {μ σ2 : ℝ}
    (hσ2 : 0 ≤ σ2) (hind : iIndepFun e P)
    (hlaw : ∀ t, HasLaw (e t) (gaussianReal μ σ2.toNNReal) P)
    (a : ℕ → ℝ) (c : ℝ) (S : Finset ℕ) :
    HasLaw (fun ω => c + ∑ j ∈ S, a j * e j ω)
      (gaussianReal (c + μ * ∑ j ∈ S, a j) (σ2 * ∑ j ∈ S, a j ^ 2).toNNReal) P := by
  induction S using Finset.induction_on with
  | empty => simpa using hasLaw_const (P := P) c
  | insert j S hj ih =>
    have hmeas : ∀ i, AEMeasurable (fun ω => a i * e i ω) P :=
      fun i => (hlaw i).aemeasurable.const_mul _
    have hind' : iIndepFun (fun i ω => a i * e i ω) P :=
      hind.comp (fun i x => a i * x) (fun i => measurable_const.mul measurable_id)
    have hI : IndepFun (∑ i ∈ S, fun ω => a i * e i ω) (fun ω => a j * e j ω) P :=
      hind'.indepFun_finsetSum_of_notMem₀ hmeas hj
    have hI2 : IndepFun (fun ω => c + ∑ i ∈ S, a i * e i ω) (fun ω => a j * e j ω) P := by
      have := hI.comp (φ := fun x => c + x) (ψ := id) (measurable_const.add measurable_id)
        measurable_id
      convert this using 1 <;> funext ω <;> simp [Finset.sum_apply]
    have hj' := gaussianReal_const_mul (hlaw j) (a j)
    have hsum := gaussianReal_add_gaussianReal_of_indepFun hI2 ih.map_eq hj'.map_eq
    refine ⟨?_, ?_⟩
    · exact aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun i _ => hmeas i)
    · have hfun : (fun ω => c + ∑ i ∈ insert j S, a i * e i ω)
          = (fun ω => c + ∑ i ∈ S, a i * e i ω) + (fun ω => a j * e j ω) := by
        funext ω; simp [Finset.sum_insert hj]; ring
      rw [hfun, hsum]
      have hS : 0 ≤ ∑ i ∈ S, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      congr 1
      · rw [Finset.sum_insert hj]; ring
      · ext
        simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, Finset.sum_insert hj]
        rw [Real.coe_toNNReal _ (mul_nonneg hσ2 hS), Real.coe_toNNReal _ hσ2,
          Real.coe_toNNReal _ (mul_nonneg hσ2 (add_nonneg (sq_nonneg _) hS))]
        ring

lemma lrAvg_of_tendsto {c : ℕ → ℝ} {l : ℝ} (h : Tendsto c atTop (𝓝 l)) : lrAvg c = l := by
  unfold lrAvg
  apply Tendsto.liminf_eq
  have h1 : Tendsto (fun k => c (k + 1)) atTop (𝓝 l) := h.comp (tendsto_add_atTop_nat 1)
  have h2 := h1.cesaro
  convert h2 using 2 with n
  rw [div_eq_inv_mul]
  congr 1
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma lrAvg_const (c : ℝ) : lrAvg (fun _ => c) = c := lrAvg_of_tendsto tendsto_const_nhds

end SFAux



namespace SFAux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma invCost_eq (M : Model) (x : ℝ) :
    invCost M x = (M.h + M.b) * max (x - 0) 0 - M.b * x := by
  unfold invCost
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith), sub_zero, max_eq_right h]; ring
  · rw [max_eq_left h, max_eq_right (by linarith), sub_zero, max_eq_left h]; ring

lemma integrable_invCost (M : Model) {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    {m : ℝ} {v : NNReal} (hX : HasLaw X (gaussianReal m v) P) :
    Integrable (fun ω => invCost M (X ω)) P := by
  simp_rw [invCost_eq]
  exact ((integrable_max_sub hX 0).const_mul _).sub ((integrable_of_hasLaw hX).const_mul _)

lemma integral_invCost (M : Model) {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    {m : ℝ} {v : NNReal} (hX : HasLaw X (gaussianReal m v) P) (hv : v ≠ 0) :
    ∫ ω, invCost M (X ω) ∂P = Real.sqrt v * NV M.h M.b (m / Real.sqrt v) := by
  simp_rw [invCost_eq]
  rw [integral_sub ((integrable_max_sub hX 0).const_mul _) ((integrable_of_hasLaw hX).const_mul _),
    integral_const_mul, integral_const_mul, integral_max_sub hX hv, integral_of_hasLaw hX]
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.2 (fun h => hv (NNReal.coe_eq_zero.mp h.symm))
  have hs0 : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv'
  unfold NV
  rw [sub_zero]
  field_simp

lemma capCost_eq (M : Model) (k q : ℝ) :
    capCost M k q = M.u * k + M.u * M.m * max (q - k) 0 := rfl

lemma integrable_capCost (M : Model) {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    {m : ℝ} {v : NNReal} (hX : HasLaw X (gaussianReal m v) P) (k : ℝ) :
    Integrable (fun ω => capCost M k (X ω)) P := by
  simp_rw [capCost_eq]
  exact (integrable_const _).add ((integrable_max_sub hX k).const_mul _)

lemma integral_capCost (M : Model) {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    {m : ℝ} {v : NNReal} (hX : HasLaw X (gaussianReal m v) P) (hv : v ≠ 0) (k : ℝ) :
    ∫ ω, capCost M k (X ω) ∂P
      = M.u * k + M.u * M.m * (Real.sqrt v * Lf ((m - k) / Real.sqrt v)) := by
  simp_rw [capCost_eq]
  rw [integral_add (integrable_const _) ((integrable_max_sub hX k).const_mul _),
    integral_const, integral_const_mul, integral_max_sub hX hv]
  simp

/-! ### TBS dynamics -/

omit [MeasurableSpace Ω] in
lemma invTBS_succ (M : Model) (γ α iStar i0 : ℝ) (d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    invTBS M γ α iStar i0 d (t + 1) ω
      = α * invTBS M γ α iStar i0 d t ω + (1 - α) * iStar + M.μ - d (t + 1) ω := by
  simp only [invTBS]; ring

omit [MeasurableSpace Ω] in
lemma invTBS_closed (M : Model) (γ α iStar i0 : ℝ) (d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    invTBS M γ α iStar i0 d t ω = iStar + α ^ t * (i0 - iStar)
      + ∑ j ∈ Finset.range t, α ^ (t - 1 - j) * (M.μ - d (j + 1) ω) := by
  induction t with
  | zero => simp [invTBS]
  | succ t ih =>
    rw [invTBS_succ, ih, Finset.sum_range_succ]
    have hs : ∑ j ∈ Finset.range t, α ^ (t + 1 - 1 - j) * (M.μ - d (j + 1) ω)
        = α * ∑ j ∈ Finset.range t, α ^ (t - 1 - j) * (M.μ - d (j + 1) ω) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < t := Finset.mem_range.mp hj
      have : t + 1 - 1 - j = (t - 1 - j) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [hs]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, pow_succ]
    ring

lemma iIndep_shift {P : Measure Ω} {d : ℕ → Ω → ℝ} (h : iIndepFun d P) :
    iIndepFun (fun j => d (j + 1)) P :=
  h.precomp (g := fun j => j + 1) (fun a b hab => by simpa using hab)

lemma hasLaw_invTBS (M : Model) (hM : M.Standing) {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ → Ω → ℝ} (hd : IIDNormalDemand M P d) (γ α iStar i0 : ℝ) (t : ℕ) :
    HasLaw (invTBS M γ α iStar i0 d t)
      (gaussianReal (iStar + α ^ t * (i0 - iStar))
        (M.σ ^ 2 * ∑ j ∈ Finset.range t, (α ^ 2) ^ j).toNNReal) P := by
  have h := hasLaw_lin (e := fun j => d (j + 1)) (sq_nonneg M.σ) (iIndep_shift hd.1)
    (fun j => hd.2 (j + 1)) (fun j => -α ^ (t - 1 - j))
    (iStar + α ^ t * (i0 - iStar) + M.μ * ∑ j ∈ Finset.range t, α ^ (t - 1 - j))
    (Finset.range t)
  have hfun : invTBS M γ α iStar i0 d t = fun ω =>
      (iStar + α ^ t * (i0 - iStar) + M.μ * ∑ j ∈ Finset.range t, α ^ (t - 1 - j))
        + ∑ j ∈ Finset.range t, -α ^ (t - 1 - j) * d (j + 1) ω := by
    funext ω
    have e : ∑ j ∈ Finset.range t, α ^ (t - 1 - j) * (M.μ - d (j + 1) ω)
        = ∑ j ∈ Finset.range t, M.μ * α ^ (t - 1 - j)
          + ∑ j ∈ Finset.range t, -α ^ (t - 1 - j) * d (j + 1) ω := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _; ring
    rw [invTBS_closed, e, Finset.mul_sum]; ring
  rw [hfun]
  convert h using 2
  · simp [Finset.sum_neg_distrib]
  · congr 2
    have := Finset.sum_range_reflect (fun j => (α ^ 2) ^ j) t
    rw [← this]
    apply Finset.sum_congr rfl
    intro j _
    rw [neg_sq, ← pow_mul, ← pow_mul, mul_comm]

end SFAux



namespace SFAux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma NV_continuous (A B : ℝ) : Continuous (NV A B) :=
  continuous_iff_continuousAt.mpr fun x => (NV_hasDerivAt A B x).continuousAt

lemma Lf_continuous : Continuous Lf :=
  continuous_iff_continuousAt.mpr fun x => (Lf_hasDerivAt x).continuousAt

lemma integral_invCost' (M : Model) {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    {m w : ℝ} (hX : HasLaw X (gaussianReal m w.toNNReal) P) (hw : 0 < w) :
    ∫ ω, invCost M (X ω) ∂P = Real.sqrt w * NV M.h M.b (m / Real.sqrt w) := by
  rw [integral_invCost M hX (by simpa using hw), Real.coe_toNNReal _ hw.le]

lemma integral_capCost' (M : Model) {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    {m w : ℝ} (hX : HasLaw X (gaussianReal m w.toNNReal) P) (hw : 0 < w) (k : ℝ) :
    ∫ ω, capCost M k (X ω) ∂P
      = M.u * k + M.u * M.m * (Real.sqrt w * Lf ((m - k) / Real.sqrt w)) := by
  rw [integral_capCost M hX (by simpa using hw), Real.coe_toNNReal _ hw.le]

/-- Geometric partial sums. -/
noncomputable def Vg (α : ℝ) (t : ℕ) : ℝ := ∑ j ∈ Finset.range t, (α ^ 2) ^ j

lemma Vg_ge_one (α : ℝ) {t : ℕ} (ht : 1 ≤ t) : 1 ≤ Vg α t := by
  unfold Vg
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  have : 0 ≤ ∑ j ∈ Finset.range n, (α ^ 2) ^ (j + 1) :=
    Finset.sum_nonneg fun j _ => pow_nonneg (sq_nonneg _) _
  linarith

lemma Vg_tendsto {α : ℝ} (hα : α ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (Vg α) atTop (𝓝 (1 - α ^ 2)⁻¹) := by
  have h1 : α ^ 2 < 1 := by
    obtain ⟨a, b⟩ := hα; nlinarith
  exact (hasSum_geometric_of_lt_one (sq_nonneg α) h1).tendsto_sum_nat

lemma pow_tendsto_zero {α : ℝ} (hα : α ∈ Ioo (-1 : ℝ) 1) :
    Tendsto (fun t : ℕ => α ^ t) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_lt.mpr hα)

lemma sigmaI_eq (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Ioo (-1 : ℝ) 1) :
    Real.sqrt (M.σ ^ 2 * (1 - α ^ 2)⁻¹) = sigmaI M α := by
  have hσ : 0 ≤ M.σ := hM.2.1.le
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hσ, Real.sqrt_inv, sigmaI, div_eq_mul_inv]

lemma sigmaQ_eq (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Ioo (-1 : ℝ) 1) :
    Real.sqrt ((α - 1) ^ 2 * (M.σ ^ 2 * (1 - α ^ 2)⁻¹)) = sigmaQ M α := by
  have hσ : 0 ≤ M.σ := hM.2.1.le
  obtain ⟨a1, a2⟩ := hα
  have e : (α - 1) ^ 2 * (M.σ ^ 2 * (1 - α ^ 2)⁻¹) = M.σ ^ 2 * ((1 - α) / (1 + α)) := by
    have h1 : (1 + α) ≠ 0 := by linarith
    have h2 : (1 - α ^ 2) ≠ 0 := by nlinarith
    field_simp
    ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hσ, sigmaQ]

lemma sigmaI_pos (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Ioo (-1 : ℝ) 1) :
    0 < sigmaI M α := by
  obtain ⟨a1, a2⟩ := hα
  unfold sigmaI
  apply div_pos hM.2.1
  apply Real.sqrt_pos.mpr; nlinarith

lemma sigmaQ_pos (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Ioo (-1 : ℝ) 1) :
    0 < sigmaQ M α := by
  obtain ⟨a1, a2⟩ := hα
  unfold sigmaQ
  apply mul_pos hM.2.1
  apply Real.sqrt_pos.mpr
  apply div_pos <;> linarith

lemma hasLaw_qTBS (M : Model) (hM : M.Standing) {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ → Ω → ℝ} (hd : IIDNormalDemand M P d) (γ α iStar i0 : ℝ) (t : ℕ) :
    HasLaw (qTBS M γ α iStar i0 d t)
      (gaussianReal (M.μ * γ + (α - 1) * (α ^ t * (i0 - iStar)))
        ((α - 1) ^ 2 * (M.σ ^ 2 * Vg α t)).toNNReal) P := by
  have h := gaussianReal_add_const (gaussianReal_const_mul
    (hasLaw_invTBS M hM hd γ α iStar i0 t) (α - 1)) (M.μ * γ + (1 - α) * iStar)
  have hfun : qTBS M γ α iStar i0 d t
      = fun ω => (α - 1) * invTBS M γ α iStar i0 d t ω + (M.μ * γ + (1 - α) * iStar) := by
    funext ω; simp only [qTBS]; ring
  rw [hfun]
  convert h using 2
  · ring
  · ext
    have hV : 0 ≤ M.σ ^ 2 * Vg α t :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => pow_nonneg (sq_nonneg _) _)
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    simp only [Vg] at hV ⊢
    rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) hV), Real.coe_toNNReal _ hV]

/-- The limit of the expected inventory cost. -/
lemma tendsto_invCost (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Ioo (-1 : ℝ) 1)
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ → Ω → ℝ} (hd : IIDNormalDemand M P d)
    (γ iStar i0 : ℝ) :
    Tendsto (fun t => ∫ ω, invCost M (invTBS M γ α iStar i0 d t ω) ∂P) atTop
      (𝓝 (sigmaI M α * NV M.h M.b (iStar / sigmaI M α))) := by
  have hσ2 : 0 < M.σ ^ 2 := pow_pos hM.2.1 2
  have heq : ∀ᶠ t in atTop, Real.sqrt (M.σ ^ 2 * Vg α t)
        * NV M.h M.b ((iStar + α ^ t * (i0 - iStar)) / Real.sqrt (M.σ ^ 2 * Vg α t))
      = ∫ ω, invCost M (invTBS M γ α iStar i0 d t ω) ∂P := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact (integral_invCost' M (hasLaw_invTBS M hM hd γ α iStar i0 t)
      (mul_pos hσ2 (lt_of_lt_of_le one_pos (Vg_ge_one α ht)))).symm
  refine Tendsto.congr' heq ?_
  have hs : Tendsto (fun t => Real.sqrt (M.σ ^ 2 * Vg α t)) atTop (𝓝 (sigmaI M α)) := by
    rw [← sigmaI_eq M hM hα]
    exact ((Vg_tendsto hα).const_mul _).sqrt
  have hm : Tendsto (fun t : ℕ => iStar + α ^ t * (i0 - iStar)) atTop (𝓝 iStar) := by
    simpa using tendsto_const_nhds.add ((pow_tendsto_zero hα).mul_const (i0 - iStar))
  exact hs.mul ((NV_continuous _ _).continuousAt.tendsto.comp
    (hm.div hs (sigmaI_pos M hM hα).ne'))

lemma tendsto_capCost (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Ioo (-1 : ℝ) 1)
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ → Ω → ℝ} (hd : IIDNormalDemand M P d)
    (γ iStar k i0 : ℝ) :
    Tendsto (fun t => ∫ ω, capCost M k (qTBS M γ α iStar i0 d t ω) ∂P) atTop
      (𝓝 (M.u * k + M.u * M.m * (sigmaQ M α * Lf ((M.μ * γ - k) / sigmaQ M α)))) := by
  have hσ2 : 0 < M.σ ^ 2 := pow_pos hM.2.1 2
  have hα1 : 0 < (α - 1) ^ 2 := by
    have : α - 1 ≠ 0 := by linarith [hα.2]
    positivity
  have heq : ∀ᶠ t in atTop, M.u * k + M.u * M.m * (Real.sqrt ((α - 1) ^ 2 * (M.σ ^ 2 * Vg α t))
        * Lf ((M.μ * γ + (α - 1) * (α ^ t * (i0 - iStar)) - k)
          / Real.sqrt ((α - 1) ^ 2 * (M.σ ^ 2 * Vg α t))))
      = ∫ ω, capCost M k (qTBS M γ α iStar i0 d t ω) ∂P := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact (integral_capCost' M (hasLaw_qTBS M hM hd γ α iStar i0 t)
      (mul_pos hα1 (mul_pos hσ2 (lt_of_lt_of_le one_pos (Vg_ge_one α ht)))) k).symm
  refine Tendsto.congr' heq ?_
  have hs : Tendsto (fun t => Real.sqrt ((α - 1) ^ 2 * (M.σ ^ 2 * Vg α t))) atTop
      (𝓝 (sigmaQ M α)) := by
    rw [← sigmaQ_eq M hM hα]
    exact (((Vg_tendsto hα).const_mul _).const_mul _).sqrt
  have hm : Tendsto (fun t : ℕ => M.μ * γ + (α - 1) * (α ^ t * (i0 - iStar)) - k) atTop
      (𝓝 (M.μ * γ - k)) := by
    simpa using ((tendsto_const_nhds.add
      (((pow_tendsto_zero hα).mul_const (i0 - iStar)).const_mul (α - 1))).sub_const k)
  exact tendsto_const_nhds.add (tendsto_const_nhds.mul (hs.mul
    (Lf_continuous.continuousAt.tendsto.comp (hm.div hs (sigmaQ_pos M hM hα).ne'))))

end SFAux



namespace SFAux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma sum_split_top (N : ℕ) (hN : 2 ≤ N) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range (N - 1), f j = ∑ j ∈ Finset.range (N - 2), f j + f (N - 2) := by
  rw [show N - 1 = (N - 2) + 1 by omega, Finset.sum_range_succ]

lemma sum_split_bot (N : ℕ) (hN : 2 ≤ N) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range (N - 1), f j = f 0 + ∑ j ∈ Finset.range (N - 2), f (j + 1) := by
  rw [show N - 1 = (N - 2) + 1 by omega, Finset.sum_range_succ', add_comm]

section OUT
variable (M : Model) (iStar i0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ) (d : ℕ → Ω → ℝ) (ω : Ω)

omit [MeasurableSpace Ω] in
lemma out_fst_succ (t : ℕ) :
    (outState M iStar i0 pipe0 d ω (t + 1)).1 = (outState M iStar i0 pipe0 d ω t).1
      - d (t + 1) ω + (outState M iStar i0 pipe0 d ω t).2 (M.L - 2) := rfl

omit [MeasurableSpace Ω] in
lemma out_snd_zero (t : ℕ) :
    (outState M iStar i0 pipe0 d ω (t + 1)).2 0 = qOUT M iStar i0 pipe0 d t ω := rfl

omit [MeasurableSpace Ω] in
lemma out_snd_succ (t j : ℕ) :
    (outState M iStar i0 pipe0 d ω (t + 1)).2 (j + 1) = (outState M iStar i0 pipe0 d ω t).2 j :=
  rfl

omit [MeasurableSpace Ω] in
lemma qOUT_eq (t : ℕ) : qOUT M iStar i0 pipe0 d t ω = iStar + M.L * M.μ
    - ((outState M iStar i0 pipe0 d ω t).1
      + ∑ j ∈ Finset.range (M.L - 1), (outState M iStar i0 pipe0 d ω t).2 j) := rfl

omit [MeasurableSpace Ω] in
/-- Inventory position after demand: `IP_{t+1} = i⋆ + Lμ − d_{t+1}`. -/
lemma out_IP (hL : 2 ≤ M.L) (t : ℕ) :
    (outState M iStar i0 pipe0 d ω (t + 1)).1
      + ∑ j ∈ Finset.range (M.L - 1), (outState M iStar i0 pipe0 d ω (t + 1)).2 j
      = iStar + M.L * M.μ - d (t + 1) ω := by
  rw [sum_split_bot M.L hL, out_snd_zero]
  simp only [out_snd_succ]
  rw [out_fst_succ, qOUT_eq, sum_split_top M.L hL]
  ring

omit [MeasurableSpace Ω] in
lemma qOUT_succ (hL : 2 ≤ M.L) (t : ℕ) : qOUT M iStar i0 pipe0 d (t + 1) ω = d (t + 1) ω := by
  rw [qOUT_eq, out_IP M iStar i0 pipe0 d ω hL]; ring

omit [MeasurableSpace Ω] in
lemma out_pipe (t j : ℕ) (hj : j < t) :
    (outState M iStar i0 pipe0 d ω t).2 j = qOUT M iStar i0 pipe0 d (t - 1 - j) ω := by
  induction t generalizing j with
  | zero => omega
  | succ t ih =>
    cases j with
    | zero => rw [out_snd_zero]; congr 1
    | succ j =>
      rw [out_snd_succ, ih j (by omega)]
      congr 1; omega

omit [MeasurableSpace Ω] in
lemma invOUT_closed (hL : 2 ≤ M.L) (t : ℕ) (ht : M.L ≤ t) :
    invOUT M iStar i0 pipe0 d t ω = iStar + M.L * M.μ
      - ∑ j ∈ Finset.range M.L, d (t - j) ω := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hIP := out_IP M iStar i0 pipe0 d ω hL t'
  have hpipe : ∑ j ∈ Finset.range (M.L - 1), (outState M iStar i0 pipe0 d ω (t' + 1)).2 j
      = ∑ j ∈ Finset.range (M.L - 1), d (t' + 1 - (j + 1)) ω := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [out_pipe M iStar i0 pipe0 d ω (t' + 1) j (by omega)]
    obtain ⟨r, hr⟩ : ∃ r, t' + 1 - 1 - j = r + 1 := ⟨t' - j - 1, by omega⟩
    rw [hr, qOUT_succ M iStar i0 pipe0 d ω hL]
    congr 1; omega
  have hsum : ∑ j ∈ Finset.range M.L, d (t' + 1 - j) ω
      = ∑ j ∈ Finset.range (M.L - 1), d (t' + 1 - (j + 1)) ω + d (t' + 1) ω := by
    rw [show M.L = (M.L - 1) + 1 by omega, Finset.sum_range_succ']
    simp
  unfold invOUT
  rw [hsum, ← hpipe]
  linarith

lemma hasLaw_invOUT (hM : M.Standing) {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IIDNormalDemand M P d) (t : ℕ) (ht : M.L ≤ t) :
    HasLaw (invOUT M iStar i0 pipe0 d t) (gaussianReal iStar (M.σ ^ 2 * M.L).toNNReal) P := by
  have hL := hM.2.2.2.2.2.2.2
  have h := hasLaw_lin (e := fun j => d (j + 1)) (sq_nonneg M.σ) (iIndep_shift hd.1)
    (fun j => hd.2 (j + 1)) (fun _ => -1) (iStar + M.L * M.μ) (Finset.Ico (t - M.L) t)
  have hre : ∀ ω, ∑ j ∈ Finset.range M.L, d (t - j) ω
      = ∑ k ∈ Finset.Ico (t - M.L) t, d (k + 1) ω := by
    intro ω
    apply Finset.sum_nbij' (fun j => t - 1 - j) (fun k => t - 1 - k)
    · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Ico]; omega
    · intro k hk; simp only [Finset.mem_Ico] at hk; simp only [Finset.mem_range]; omega
    · intro j hj; simp only [Finset.mem_range] at hj; omega
    · intro k hk; simp only [Finset.mem_Ico] at hk; omega
    · intro j hj; simp only [Finset.mem_range] at hj; congr 1; omega
  have hfun : invOUT M iStar i0 pipe0 d t
      = fun ω => (iStar + M.L * M.μ) + ∑ k ∈ Finset.Ico (t - M.L) t, (fun _ => (-1 : ℝ)) k
          * (fun j => d (j + 1)) k ω := by
    funext ω
    rw [invOUT_closed M iStar i0 pipe0 d ω hL t ht, hre]
    simp [Finset.sum_neg_distrib]; ring
  rw [hfun]
  have hcard : ((Finset.Ico (t - M.L) t).card : ℝ) = M.L := by
    rw [Nat.card_Ico]; push_cast [show t - (t - M.L) = M.L by omega]; rfl
  convert h using 2
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
    rw [hcard]; ring
  · simp only [neg_sq, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard]

end OUT

lemma sigmaIS_eq (M : Model) (hM : M.Standing) :
    Real.sqrt (M.σ ^ 2 * M.L) = sigmaIS M := by
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM.2.1.le, sigmaIS]

lemma sigmaIS_pos (M : Model) (hM : M.Standing) : 0 < sigmaIS M := by
  unfold sigmaIS
  apply mul_pos hM.2.1
  apply Real.sqrt_pos.mpr
  have := hM.2.2.2.2.2.2.2
  have : (2 : ℝ) ≤ M.L := by exact_mod_cast this
  linarith

lemma lrCostOUT_eq (M : Model) (hM : M.Standing) {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ → Ω → ℝ} (hd : IIDNormalDemand M P d) (iStar i0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ) :
    lrCostOUT M iStar i0 pipe0 P d
      = sigmaIS M * NV M.h M.b (iStar / sigmaIS M) + M.p * M.μ := by
  have hL := hM.2.2.2.2.2.2.2
  apply lrAvg_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop M.L] with t ht
  have hX := hasLaw_invOUT M iStar i0 pipe0 d hM hd t ht
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hq : (fun ω => qOUT M iStar i0 pipe0 d (t' + 1) ω) = d (t' + 1) := by
    funext ω; exact qOUT_succ M iStar i0 pipe0 d ω hL t'
  have hdi : Integrable (d (t' + 1)) P := integrable_of_hasLaw (hd.2 (t' + 1))
  have e1 : ∫ ω, (invCost M (invOUT M iStar i0 pipe0 d (t' + 1) ω)
        + M.p * qOUT M iStar i0 pipe0 d (t' + 1) ω) ∂P
      = ∫ ω, invCost M (invOUT M iStar i0 pipe0 d (t' + 1) ω) ∂P
        + ∫ ω, M.p * d (t' + 1) ω ∂P := by
    rw [← integral_add (integrable_invCost M hX) (hdi.const_mul _)]
    congr 1; funext ω; rw [qOUT_succ M iStar i0 pipe0 d ω hL t']
  have hσL : 0 < M.σ ^ 2 * M.L := by
    apply mul_pos (pow_pos hM.2.1 2)
    have : (2 : ℝ) ≤ M.L := by exact_mod_cast hL
    linarith
  rw [e1, integral_invCost' M hX hσL, integral_const_mul, integral_of_hasLaw (hd.2 (t' + 1)),
    sigmaIS_eq M hM]

end SFAux



namespace SFAux

lemma Phi_zi (M : Model) (hM : M.Standing) : Phi (zi M) = M.b / (M.h + M.b) := by
  obtain ⟨_, _, hh, hb, _⟩ := hM
  unfold zi
  rw [Phi_quantile (div_pos hb (by linarith)) ((div_lt_one (by linarith)).mpr (by linarith)),
    add_comm]

lemma Phi_neg_zq (M : Model) (hM : M.Standing) : Phi (-zq M) = 1 / ((M.m - 1) + 1) := by
  obtain ⟨_, _, _, _, _, hm, _⟩ := hM
  have hm0 : 0 < M.m := by linarith
  unfold zq
  rw [Phi_neg, Phi_quantile (div_pos (by linarith) hm0) ((div_lt_one hm0).mpr (by linarith)),
    sub_add_cancel, eq_div_iff hm0.ne', sub_mul, div_mul_cancel₀ _ hm0.ne']
  ring

variable {Ω : Type*} [MeasurableSpace Ω]

theorem prop1 (M : Model) (hM : M.Standing) {γ α : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Ioo (-1 : ℝ) 1)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d) (i0 : ℝ) :
    let Ci := sigmaI M α * (M.h + M.b) * stdNormalPDF (zi M)
    let Cq := M.u * M.μ * γ + M.u * M.m * sigmaQ M α * stdNormalPDF (zq M)
    let Cp := M.p * (1 - γ) * M.μ
    let C13 := sigmaI M α * (M.h + M.b) * stdNormalPDF (zi M)
      + sigmaQ M α * M.u * M.m * stdNormalPDF (zq M) + ((M.u - M.p) * γ + M.p) * M.μ
    let iOpt := sigmaI M α * zi M
    let kOpt := M.μ * γ + sigmaQ M α * zq M
    -- (10)
    (IsLeast (Set.range fun s : ℝ => lrInvCostTBS M γ α s i0 P d) Ci ∧
      lrInvCostTBS M γ α iOpt i0 P d = Ci ∧
      ∀ s : ℝ, lrInvCostTBS M γ α s i0 P d = Ci → s = iOpt) ∧
    -- (11)
    (∀ s : ℝ, IsLeast (Set.range fun k : ℝ => lrCapCostTBS M γ α s k i0 P d) Cq ∧
      lrCapCostTBS M γ α s kOpt i0 P d = Cq ∧
      ∀ k : ℝ, lrCapCostTBS M γ α s k i0 P d = Cq → k = kOpt) ∧
    -- (12)
    lrAvg (fun _ => M.p * (M.μ * (1 - γ))) = Cp ∧
    -- (13)
    (IsLeast (Set.range fun x : ℝ × ℝ => lrCostTBS M γ α x.1 x.2 i0 P d) C13 ∧
      lrCostTBS M γ α iOpt kOpt i0 P d = C13 ∧
      ∀ x : ℝ × ℝ, lrCostTBS M γ α x.1 x.2 i0 P d = C13 → x = (iOpt, kOpt)) ∧
    C13 = Ci + Cq + Cp ∧
    0 ≤ Ci ∧ 0 ≤ Cq ∧ 0 ≤ Cp ∧ 0 ≤ C13 := by
  intro Ci Cq Cp C13 iOpt kOpt
  have hM' := hM
  obtain ⟨hμ, hσ, hh, hb, hu, hm, hp, _⟩ := hM'
  have hσI := sigmaI_pos M hM hα
  have hσQ := sigmaQ_pos M hM hα
  -- the reduced cost functions
  set fI : ℝ → ℝ := fun s => (sigmaI M α) * NV M.h M.b (s / (sigmaI M α)) with hfI
  set fC : ℝ → ℝ := fun k => M.u * M.μ * γ + M.u * (sigmaQ M α) * NV (M.m - 1) 1 ((M.μ * γ - k) / (sigmaQ M α))
    with hfC
  have hI : ∀ s, lrInvCostTBS M γ α s i0 P d = fI s := fun s =>
    lrAvg_of_tendsto (tendsto_invCost M hM hα hd γ s i0)
  have hCapLim : ∀ k, M.u * k + M.u * M.m * ((sigmaQ M α) * Lf ((M.μ * γ - k) / (sigmaQ M α))) = fC k := by
    intro k
    simp only [hfC, NV]
    have e : k = M.μ * γ - (sigmaQ M α) * ((M.μ * γ - k) / (sigmaQ M α)) := by field_simp; ring
    set c := (M.μ * γ - k) / (sigmaQ M α)
    rw [e]; ring
  have hC : ∀ s k, lrCapCostTBS M γ α s k i0 P d = fC k := fun s k => by
    rw [← hCapLim]; exact lrAvg_of_tendsto (tendsto_capCost M hM hα hd γ s k i0)
  have hT : ∀ s k, lrCostTBS M γ α s k i0 P d = fI s + M.p * (M.μ * (1 - γ)) + fC k := by
    intro s k
    apply lrAvg_of_tendsto
    have hper : ∀ t, periodCostTBS M γ α s k i0 P d t
        = ∫ ω, invCost M (invTBS M γ α s i0 d t ω) ∂P + M.p * (M.μ * (1 - γ))
          + ∫ ω, capCost M k (qTBS M γ α s i0 d t ω) ∂P := by
      intro t
      unfold periodCostTBS
      have h1 := integrable_invCost M (hasLaw_invTBS M hM hd γ α s i0 t)
      have h3 := integrable_capCost M (hasLaw_qTBS M hM hd γ α s i0 t) k
      have e1 : ∫ ω, (invCost M (invTBS M γ α s i0 d t ω) + M.p * (M.μ * (1 - γ))
            + capCost M k (qTBS M γ α s i0 d t ω)) ∂P
          = ∫ ω, (invCost M (invTBS M γ α s i0 d t ω) + M.p * (M.μ * (1 - γ))) ∂P
            + ∫ ω, capCost M k (qTBS M γ α s i0 d t ω) ∂P :=
        integral_add (h1.add (integrable_const _)) h3
      have e2 : ∫ ω, (invCost M (invTBS M γ α s i0 d t ω) + M.p * (M.μ * (1 - γ))) ∂P
          = ∫ ω, invCost M (invTBS M γ α s i0 d t ω) ∂P + ∫ _ω, M.p * (M.μ * (1 - γ)) ∂P :=
        integral_add h1 (integrable_const _)
      rw [e1, e2]
      simp
    rw [show periodCostTBS M γ α s k i0 P d = _ from funext hper, ← hCapLim]
    exact ((tendsto_invCost M hM hα hd γ s i0).add tendsto_const_nhds).add
      (tendsto_capCost M hM hα hd γ s k i0)
  -- minimization facts
  have hNVi := NV_min hh hb (Phi_zi M hM)
  have hNVq := NV_min (show 0 < M.m - 1 by linarith) one_pos (Phi_neg_zq M hM)
  have hImin : fI iOpt = Ci ∧ ∀ s, s ≠ iOpt → Ci < fI s := by
    have hiOpt : iOpt / (sigmaI M α) = zi M := by simp only [iOpt]; field_simp
    refine ⟨?_, ?_⟩
    · simp only [hfI]; rw [hiOpt, hNVi.1]; simp only [Ci]; ring
    · intro s hs
      have hne : s / (sigmaI M α) ≠ zi M := by
        intro h; apply hs; simp only [iOpt]; rw [← h]; field_simp
      have := hNVi.2 _ hne
      simp only [hfI]
      have e : Ci = (sigmaI M α) * NV M.h M.b (zi M) := by rw [hNVi.1]; simp only [Ci]; ring
      rw [e]; exact mul_lt_mul_of_pos_left this hσI
  have hCmin : fC kOpt = Cq ∧ ∀ k, k ≠ kOpt → Cq < fC k := by
    have hkOpt : (M.μ * γ - kOpt) / (sigmaQ M α) = -zq M := by simp only [kOpt]; field_simp; ring
    have e : Cq = M.u * M.μ * γ + M.u * (sigmaQ M α) * NV (M.m - 1) 1 (-zq M) := by
      rw [hNVq.1, phi_neg]; simp only [Cq]; ring
    refine ⟨?_, ?_⟩
    · simp only [hfC]; rw [hkOpt, e]
    · intro k hk
      have hne : (M.μ * γ - k) / (sigmaQ M α) ≠ -zq M := by
        intro h; apply hk; simp only [kOpt]
        have : M.μ * γ - k = -zq M * (sigmaQ M α) := by rw [← h]; field_simp
        linarith
      have := hNVq.2 _ hne
      simp only [hfC]
      rw [e]
      have := mul_lt_mul_of_pos_left this (mul_pos hu hσQ)
      linarith
  have hCp : M.p * (M.μ * (1 - γ)) = Cp := by simp only [Cp]; ring
  have h13 : C13 = Ci + Cq + Cp := by simp only [C13, Ci, Cq, Cp]; ring
  refine ⟨⟨⟨⟨iOpt, by simp only [hI]; exact hImin.1⟩, ?_⟩, by rw [hI]; exact hImin.1, ?_⟩,
    fun s => ⟨⟨⟨kOpt, by simp only [hC]; exact hCmin.1⟩, ?_⟩, by rw [hC]; exact hCmin.1, ?_⟩,
    by rw [lrAvg_const, hCp], ⟨⟨⟨(iOpt, kOpt), ?_⟩, ?_⟩, ?_, ?_⟩, h13, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    simp only [hI]
    by_cases hs : s = iOpt
    · rw [hs, hImin.1]
    · exact (hImin.2 s hs).le
  · intro s hs
    by_contra hne
    rw [hI] at hs
    exact absurd hs (hImin.2 s hne).ne'
  · rintro _ ⟨k, rfl⟩
    simp only [hC]
    by_cases hk : k = kOpt
    · rw [hk, hCmin.1]
    · exact (hCmin.2 k hk).le
  · intro k hk
    by_contra hne
    rw [hC] at hk
    exact absurd hk (hCmin.2 k hne).ne'
  · simp only [hT, hImin.1, hCmin.1, hCp, h13]; ring
  · rintro _ ⟨⟨s, k⟩, rfl⟩
    simp only [hT, h13, hCp]
    have h1 : Ci ≤ fI s := by
      by_cases hs : s = iOpt
      · rw [hs, hImin.1]
      · exact (hImin.2 s hs).le
    have h2 : Cq ≤ fC k := by
      by_cases hk : k = kOpt
      · rw [hk, hCmin.1]
      · exact (hCmin.2 k hk).le
    linarith
  · rw [hT, hImin.1, hCmin.1, hCp, h13]; ring
  · rintro ⟨s, k⟩ hx
    simp only [hT, h13, hCp] at hx
    have h1 : Ci ≤ fI s := by
      by_cases hs : s = iOpt
      · rw [hs, hImin.1]
      · exact (hImin.2 s hs).le
    have h2 : Cq ≤ fC k := by
      by_cases hk : k = kOpt
      · rw [hk, hCmin.1]
      · exact (hCmin.2 k hk).le
    have hs : s = iOpt := by
      by_contra hs; have := hImin.2 s hs; linarith
    have hk : k = kOpt := by
      by_contra hk; have := hCmin.2 k hk; linarith
    rw [hs, hk]
  · simp only [Ci]
    exact mul_nonneg (mul_nonneg hσI.le (by linarith)) (phi_pos _).le
  · simp only [Cq]
    have : 0 ≤ M.u * M.μ * γ := mul_nonneg (mul_nonneg hu.le hμ.le) hγ.1
    have : 0 ≤ M.u * M.m * (sigmaQ M α) * stdNormalPDF (zq M) :=
      mul_nonneg (mul_nonneg (mul_nonneg hu.le (by linarith)) hσQ.le) (phi_pos _).le
    linarith
  · simp only [Cp]
    exact mul_nonneg (mul_nonneg hp (by linarith [hγ.2])) hμ.le
  · rw [h13]
    have : 0 ≤ Ci := mul_nonneg (mul_nonneg hσI.le (by linarith)) (phi_pos _).le
    have : 0 ≤ Cq := by
      have : 0 ≤ M.u * M.μ * γ := mul_nonneg (mul_nonneg hu.le hμ.le) hγ.1
      have : 0 ≤ M.u * M.m * (sigmaQ M α) * stdNormalPDF (zq M) :=
        mul_nonneg (mul_nonneg (mul_nonneg hu.le (by linarith)) hσQ.le) (phi_pos _).le
      simp only [Cq]; linarith
    have : 0 ≤ Cp := mul_nonneg (mul_nonneg hp (by linarith [hγ.2])) hμ.le
    linarith

end SFAux



namespace SFAux

theorem eq18 (M : Model) (hM : M.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d) (i0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ) :
    let Cs := sigmaIS M * (M.h + M.b) * stdNormalPDF (zi M) + M.p * M.μ
    IsLeast (Set.range fun s : ℝ => lrCostOUT M s i0 pipe0 P d) Cs ∧
    lrCostOUT M (sigmaIS M * zi M) i0 pipe0 P d = Cs ∧
    (∀ s : ℝ, lrCostOUT M s i0 pipe0 P d = Cs → s = sigmaIS M * zi M) ∧
    ∀ (iStar : ℝ) (t : ℕ), M.L ≤ t →
      variance (invOUT M iStar i0 pipe0 d t) P = M.L * M.σ ^ 2 := by
  intro Cs
  have hS := sigmaIS_pos M hM
  have hNVi := NV_min hM.2.2.1 hM.2.2.2.1 (Phi_zi M hM)
  have hC : ∀ s, lrCostOUT M s i0 pipe0 P d
      = sigmaIS M * NV M.h M.b (s / sigmaIS M) + M.p * M.μ :=
    fun s => lrCostOUT_eq M hM hd s i0 pipe0
  have hopt : sigmaIS M * zi M / sigmaIS M = zi M := by field_simp
  have hval : sigmaIS M * NV M.h M.b (zi M) + M.p * M.μ = Cs := by
    rw [hNVi.1]; simp only [Cs]; ring
  have hlt : ∀ s, s ≠ sigmaIS M * zi M → Cs < lrCostOUT M s i0 pipe0 P d := by
    intro s hs
    have hne : s / sigmaIS M ≠ zi M := by
      intro h; apply hs; rw [← h]; field_simp
    rw [hC, ← hval]
    have := mul_lt_mul_of_pos_left (hNVi.2 _ hne) hS
    linarith
  have hat : lrCostOUT M (sigmaIS M * zi M) i0 pipe0 P d = Cs := by rw [hC, hopt, hval]
  refine ⟨⟨⟨_, hat⟩, ?_⟩, hat, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    by_cases hs : s = sigmaIS M * zi M
    · show Cs ≤ lrCostOUT M s i0 pipe0 P d
      rw [hs, hat]
    · exact (hlt s hs).le
  · intro s hs
    by_contra hne
    exact absurd hs (hlt s hne).ne'
  · intro iStar t ht
    have hX := hasLaw_invOUT M iStar i0 pipe0 d hM hd t ht
    rw [hX.variance_eq, variance_id_gaussianReal,
      Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))]
    ring

end SFAux

theorem solution (M : Model) (hM : M.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d) (i0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ) :
    let Cs := sigmaIS M * (M.h + M.b) * stdNormalPDF (zi M) + M.p * M.μ
    IsLeast (Set.range fun s : ℝ => lrCostOUT M s i0 pipe0 P d) Cs ∧
    lrCostOUT M (sigmaIS M * zi M) i0 pipe0 P d = Cs ∧
    (∀ s : ℝ, lrCostOUT M s i0 pipe0 P d = Cs → s = sigmaIS M * zi M) ∧
    ∀ (iStar : ℝ) (t : ℕ), M.L ≤ t →
      variance (invOUT M iStar i0 pipe0 d t) P = M.L * M.σ ^ 2 :=
  SFAux.eq18 M hM P d hd i0 pipe0
