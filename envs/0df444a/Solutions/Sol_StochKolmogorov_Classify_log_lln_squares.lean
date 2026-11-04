-- Prove2me | solution 1 for StochKolmogorov.Classify.log_lln_squares
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T13:51:16.527965+00:00
-- url     : https://prove2.me/submissions/8a322cbf-3237-45a1-a4b0-959d55cea3d9

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Theorems.Thm_EthierKurtz_brownian_ito_integral_and_formula
import Theorems.Thm_EthierKurtz_brownian_ito_integral_locality_and_continuity

/-! Child `StochKolmogorov.Classify.log_lln_squares` (Hening-Nguyen arXiv:1704.06984v1, proof of Lemma 5.4 /
Theorem 5.2, p. 28): strong law of large numbers for `ln Xᵢ` along the times `m²`. Proof: Itô's formula for
`ln Xₖ` (smoothly floored), localized and de-localized by path continuity; gated L² bound for the martingale
part; Borel–Cantelli along `m²`. Uses the Proved platform theorems
`EthierKurtz.brownian_ito_integral_and_formula` and `EthierKurtz.brownian_ito_integral_locality_and_continuity`. -/

set_option autoImplicit false


section Part0
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators ContDiff

namespace StochKolmogorov.Classify.HL

open StochKolmogorov.Classify EthierKurtz

/-- Smooth floor at level `a/4`, equal to the identity on `[a/2, ∞)`. -/
noncomputable def psi (a y : ℝ) : ℝ :=
  Real.smoothTransition (4 * y / a - 1) * y +
    (1 - Real.smoothTransition (4 * y / a - 1)) * (a / 4)

lemma psi_contDiff (a : ℝ) : ContDiff ℝ ∞ (psi a) := by
  unfold psi
  have h1 : ContDiff ℝ ∞ (fun y : ℝ => Real.smoothTransition (4 * y / a - 1)) :=
    Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_id).div_const a).sub contDiff_const)
  exact (h1.mul contDiff_id).add ((contDiff_const.sub h1).mul contDiff_const)

lemma psi_eq {a y : ℝ} (ha : 0 < a) (hy : a / 2 ≤ y) : psi a y = y := by
  unfold psi
  have h : 1 ≤ 4 * y / a - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ ha]; linarith
  rw [Real.smoothTransition.one_of_one_le h]; ring

lemma psi_ge {a : ℝ} (ha : 0 < a) (y : ℝ) : a / 4 ≤ psi a y := by
  unfold psi
  set s := Real.smoothTransition (4 * y / a - 1)
  have hs0 : 0 ≤ s := Real.smoothTransition.nonneg _
  by_cases hy : a / 4 ≤ y
  · have : 0 ≤ s * (y - a / 4) := mul_nonneg hs0 (by linarith)
    nlinarith
  · have h : 4 * y / a - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_iff₀ ha]; linarith
    have : s = 0 := Real.smoothTransition.zero_of_nonpos h
    rw [this]; linarith

lemma psi_pos {a : ℝ} (ha : 0 < a) (y : ℝ) : 0 < psi a y :=
  lt_of_lt_of_le (by linarith) (psi_ge ha y)

/-- `log ∘ psi a`. -/
noncomputable def logPsi (a y : ℝ) : ℝ := Real.log (psi a y)

lemma logPsi_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (logPsi a) :=
  (psi_contDiff a).log (fun y => (psi_pos ha y).ne')

lemma logPsi_eq {a y : ℝ} (ha : 0 < a) (hy : a / 2 ≤ y) : logPsi a y = Real.log y := by
  unfold logPsi; rw [psi_eq ha hy]

lemma logPsi_eventuallyEq {a y : ℝ} (ha : 0 < a) (hy : a / 2 < y) :
    logPsi a =ᶠ[𝓝 y] Real.log := by
  filter_upwards [Ioi_mem_nhds hy] with z hz using logPsi_eq ha (le_of_lt hz)

lemma deriv_logPsi {a y : ℝ} (ha : 0 < a) (hy : a / 2 < y) : deriv (logPsi a) y = y⁻¹ := by
  rw [(logPsi_eventuallyEq ha hy).deriv_eq, Real.deriv_log]

lemma deriv_deriv_logPsi {a y : ℝ} (ha : 0 < a) (hy : a / 2 < y) :
    deriv (deriv (logPsi a)) y = -(y ^ 2)⁻¹ := by
  have h : deriv (logPsi a) =ᶠ[𝓝 y] fun z => z⁻¹ := by
    filter_upwards [Ioi_mem_nhds hy] with z hz using deriv_logPsi ha hz
  rw [h.deriv_eq, deriv_inv]

/-- Fréchet derivative of `v ↦ G (v k)`. -/
lemma hasFDerivAt_coord {n : ℕ} (G : ℝ → ℝ) (hG : Differentiable ℝ G) (k : Fin n)
    (v : SDEState n) :
    HasFDerivAt (fun w : SDEState n => G (w k))
      (deriv G (v k) • (EuclideanSpace.proj k : SDEState n →L[ℝ] ℝ)) v := by
  have h : HasFDerivAt (fun w : SDEState n => G (w k)) _ v :=
    ((hG (v k)).hasDerivAt.hasFDerivAt).comp v
      (EuclideanSpace.proj k : SDEState n →L[ℝ] ℝ).hasFDerivAt
  refine h.congr_fderiv ?_
  ext w; simp [mul_comm]

lemma fderiv_coord {n : ℕ} (G : ℝ → ℝ) (hG : Differentiable ℝ G) (k : Fin n) :
    fderiv ℝ (fun w : SDEState n => G (w k)) =
      fun v => deriv G (v k) • (EuclideanSpace.proj k : SDEState n →L[ℝ] ℝ) := by
  funext v; exact (hasFDerivAt_coord G hG k v).fderiv

lemma fderiv_coord_apply {n : ℕ} (G : ℝ → ℝ) (hG : Differentiable ℝ G) (k : Fin n)
    (v w : SDEState n) :
    fderiv ℝ (fun w : SDEState n => G (w k)) v w = deriv G (v k) * w k := by
  rw [fderiv_coord G hG k]; simp

lemma fderiv_fderiv_coord_apply {n : ℕ} (G : ℝ → ℝ) (hG : Differentiable ℝ G)
    (hG' : Differentiable ℝ (deriv G)) (k : Fin n) (v w w' : SDEState n) :
    fderiv ℝ (fderiv ℝ (fun w : SDEState n => G (w k))) v w w' =
      deriv (deriv G) (v k) * w k * w' k := by
  rw [fderiv_coord G hG k]
  have h := (hasFDerivAt_coord (deriv G) hG' k v).smul_const
    (EuclideanSpace.proj k : SDEState n →L[ℝ] ℝ)
  rw [h.fderiv]; simp [mul_comm, mul_left_comm]

/-- The test function of C1: `f_{a,k}(v) = log (psi a (v k))`. -/
noncomputable def fLog {n : ℕ} (a : ℝ) (k : Fin n) (v : SDEState n) : ℝ := logPsi a (v k)

lemma logPsi_diff {a : ℝ} (ha : 0 < a) : Differentiable ℝ (logPsi a) :=
  (logPsi_contDiff ha).differentiable (by simp)

lemma logPsi_diff' {a : ℝ} (ha : 0 < a) : Differentiable ℝ (deriv (logPsi a)) :=
  ((logPsi_contDiff ha).iterate_deriv 1).differentiable (by simp)

lemma fLog_contDiff {n : ℕ} {a : ℝ} (ha : 0 < a) (k : Fin n) : ContDiff ℝ 2 (fLog (n := n) a k) := by
  unfold fLog
  exact ((logPsi_contDiff ha).of_le (by first | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | simp | norm_cast | decide)).comp
    (EuclideanSpace.proj k : SDEState n →L[ℝ] ℝ).contDiff

lemma fderiv_fLog_single {n : ℕ} {a : ℝ} (ha : 0 < a) (k i : Fin n) (v : SDEState n) :
    fderiv ℝ (fLog a k) v (EuclideanSpace.single i 1) =
      if i = k then deriv (logPsi a) (v k) else 0 := by
  unfold fLog
  rw [fderiv_coord_apply _ (logPsi_diff ha) k]
  by_cases h : i = k
  · subst h; simp
  · simp [EuclideanSpace.single_apply, Ne.symm h, h]

lemma fderiv2_fLog_single {n : ℕ} {a : ℝ} (ha : 0 < a) (k i i' : Fin n) (v : SDEState n) :
    fderiv ℝ (fderiv ℝ (fLog a k)) v (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) =
      if i = k ∧ i' = k then deriv (deriv (logPsi a)) (v k) else 0 := by
  unfold fLog
  rw [fderiv_fderiv_coord_apply _ (logPsi_diff ha) (logPsi_diff' ha) k]
  by_cases h : i = k
  · by_cases h' : i' = k
    · subst h; subst h'; simp
    · subst h; simp [EuclideanSpace.single_apply, Ne.symm h', h']
  · simp [EuclideanSpace.single_apply, Ne.symm h, h]

lemma continuous_fderiv_fLog {n : ℕ} {a : ℝ} (ha : 0 < a) (k : Fin n) :
    Continuous (fderiv ℝ (fLog (n := n) a k)) :=
  (fLog_contDiff ha k).continuous_fderiv (by norm_num)

end StochKolmogorov.Classify.HL

end Part0


section Part1
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.HL

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma hasBrownianItoIntegral_zero (P : Measure Ω) (F : ℝ≥0 → MeasurableSpace Ω)
    (W : ℝ≥0 → Ω → ℝ) :
    HasBrownianItoIntegral P F W (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨fun t ω => by simp, fun t => ⟨fun _ _ _ => 0, fun _ _ _ => measurable_const,
    fun _ => ⟨0, by simp⟩, ?_, ?_⟩⟩
  · intro ε hε
    have h0 : ∀ (i : ℕ) (u : ℝ) (ω : Ω), itoStepValue t i (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) u ω = 0 := fun i u ω =>
      Finset.sum_eq_zero fun k _ => by split_ifs <;> rfl
    simp [h0, hε.ne']
  · intro ε hε; simp [itoStepSum, hε.ne']

lemma continuous_posPart : Continuous (posPart (n := n)) := by
  unfold posPart
  first
  | fun_prop
  | exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).max
        continuous_const)

lemma posPart_mem (y : SDEState n) : posPart y ∈ orthant n := by
  intro i; simp [posPart]

lemma cont_comp_posPart {φ : SDEState n → ℝ} (h : ContinuousOn φ (orthant n)) :
    Continuous fun y => φ (posPart y) :=
  h.comp_continuous continuous_posPart posPart_mem

lemma posPart_eq_of_mem {y : SDEState n} (hy : y ∈ orthant n) : posPart y = y := by
  ext i; simp [posPart, max_eq_left (hy i)]

/-- Noise integrand of `ln Xₖ`: `gₖ(X⁺) Γⱼₖ`. -/
noncomputable def gInt (C : Coeffs n) (Y : ℝ≥0 → Ω → SDEState n) (k j : Fin n) :
    ℝ≥0 → Ω → ℝ :=
  fun s ω => C.g k (posPart (Y s ω)) * C.Γ j k

/-- Drift of `ln Xₖ`: `hₖ(y⁺) = fₖ(y⁺) − σₖₖ gₖ(y⁺)²/2`. -/
noncomputable def hInt (C : Coeffs n) (k : Fin n) (y : SDEState n) : ℝ :=
  C.f k (posPart y) - C.sig k k * C.g k (posPart y) ^ 2 / 2

lemma sig_self (C : Coeffs n) (k : Fin n) : C.sig k k = ∑ j, C.Γ j k * C.Γ j k := by
  simp [Coeffs.sig, Matrix.mul_apply]

lemma diffusion_apply (C : Coeffs n) (s : ℝ≥0) (y : SDEState n) (i j : Fin n) :
    diffusion C (s, y) (i, j) = y i * C.g i (posPart y) * C.Γ j i := by
  simp [diffusion]

lemma drift_apply (C : Coeffs n) (s : ℝ≥0) (y : SDEState n) (i : Fin n) :
    drift C (s, y) i = y i * C.f i (posPart y) := by
  simp [drift]

lemma le_t_of_dyadic (t : ℝ≥0) (N i : ℕ) (hi : i ≤ 2 ^ N) :
    (i : ℝ≥0) * t / 2 ^ N ≤ t := by
  rw [div_le_iff₀ (pow_pos (by norm_num) N)]
  calc (i : ℝ≥0) * t ≤ (2 ^ N : ℝ≥0) * t := by
        gcongr; exact_mod_cast hi
    _ = t * 2 ^ N := mul_comm _ _

lemma toNNReal_le_of_mem {t : ℝ≥0} {u : ℝ} (hu : u ∈ Set.uIcc (0 : ℝ) t.val) :
    u.toNNReal ≤ t := by
  rw [Set.uIcc_of_le t.2] at hu
  exact Real.toNNReal_le_iff_le_coe.mpr hu.2

set_option maxHeartbeats 1000000 in
/-- C1: Itô's formula for `ln Xₖ` on `{∀ s ≤ t, a ≤ Xₖ(s)}`. -/
theorem log_ito (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (hcont : ∀ i, ContinuousOn (C.f i) (orthant n) ∧ ContinuousOn (C.g i) (orthant n))
    (x : SDEState n) (hx : x ∈ orthant n) (k : Fin n) (L : Fin n → ℝ≥0 → Ω → ℝ)
    (hL : ∀ j, HasBrownianItoIntegral P (completedBrownianPast P B (fun _ => x))
        (fun s ω => B s ω j) (gInt C (X x) k j) (L j))
    (a : ℝ) (ha : 0 < a) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, (∀ s ≤ t, a ≤ X x s ω k) →
      Real.log (X x t ω k) = Real.log (x k) + (∑ j, L j t ω) +
        ∫ u in (0 : ℝ)..t.val, hInt C k (X x u.toNNReal ω) := by
  obtain ⟨hP, hB, hsol⟩ := hX
  obtain ⟨hXm, hXc, hXa, hX0, J, -, -, hJ, -, hXeq⟩ := hsol x hx
  obtain ⟨ito1, ito2, ito3⟩ := brownian_ito_integral_and_formula hB x
  obtain ⟨loc1, -, -, -⟩ := brownian_ito_integral_locality_and_continuity hB x
  have hfc : ∀ i, Continuous fun y : SDEState n => C.f i (posPart y) :=
    fun i => cont_comp_posPart (hcont i).1
  have hgc : ∀ i, Continuous fun y : SDEState n => C.g i (posPart y) :=
    fun i => cont_comp_posPart (hcont i).2
  -- coefficient processes
  set H : Fin n → Fin n → ℝ≥0 → Ω → ℝ := fun i j s ω => diffusion C (s, X x s ω) (i, j)
    with hHdef
  set b : Fin n → ℝ≥0 → Ω → ℝ := fun i s ω => drift C (s, X x s ω) i with hbdef
  have hHφ : ∀ i j, Continuous fun y : SDEState n => y i * C.g i (posPart y) * C.Γ j i :=
    fun i j => (((PiLp.continuous_apply 2 _ i).mul (hgc i)).mul continuous_const)
  have hbφ : ∀ i, Continuous fun y : SDEState n => y i * C.f i (posPart y) :=
    fun i => ((PiLp.continuous_apply 2 _ i).mul (hfc i))
  have hHeq : ∀ i j s ω, H i j s ω = X x s ω i * C.g i (posPart (X x s ω)) * C.Γ j i :=
    fun i j s ω => diffusion_apply C s _ i j
  have hbeq : ∀ i s ω, b i s ω = X x s ω i * C.f i (posPart (X x s ω)) :=
    fun i s ω => drift_apply C s _ i
  have hHm : ∀ i j s, Measurable[completedBrownianPast P B (fun _ => x) s] (H i j s) := by
    intro i j s
    have : H i j s = (fun y : SDEState n => y i * C.g i (posPart y) * C.Γ j i) ∘ X x s := by
      funext ω; exact hHeq i j s ω
    rw [this]; exact (hHφ i j).measurable.comp (hXa s)
  have hHc : ∀ i j ω, Continuous fun s => H i j s ω := by
    intro i j ω
    have : (fun s => H i j s ω) =
        (fun y : SDEState n => y i * C.g i (posPart y) * C.Γ j i) ∘ (fun s => X x s ω) := by
      funext s; exact hHeq i j s ω
    rw [this]; exact (hHφ i j).comp (hXc ω)
  have hbm : ∀ i s, Measurable[completedBrownianPast P B (fun _ => x) s] (b i s) := by
    intro i s
    have : b i s = (fun y : SDEState n => y i * C.f i (posPart y)) ∘ X x s := by
      funext ω; exact hbeq i s ω
    rw [this]; exact (hbφ i).measurable.comp (hXa s)
  have hbc : ∀ i ω, Continuous fun s => b i s ω := by
    intro i ω
    have : (fun s => b i s ω) = (fun y : SDEState n => y i * C.f i (posPart y)) ∘
        (fun s => X x s ω) := by
      funext s; exact hbeq i s ω
    rw [this]; exact (hbφ i).comp (hXc ω)
  -- the integrands of the Itô formula's martingale terms
  set f := fLog (n := n) a k with hfdef
  have hDc : Continuous (fderiv ℝ f) := continuous_fderiv_fLog ha k
  set Ki : Fin n → Fin n → ℝ≥0 → Ω → ℝ :=
    fun i j s ω => fderiv ℝ f (X x s ω) (EuclideanSpace.single i 1) * H i j s ω with hKidef
  have hKim : ∀ i j s, Measurable[completedBrownianPast P B (fun _ => x) s] (Ki i j s) := by
    intro i j s
    have hφ : Continuous fun y : SDEState n => fderiv ℝ f y (EuclideanSpace.single i 1) :=
      hDc.clm_apply continuous_const
    exact (hφ.measurable.comp (hXa s)).mul (hHm i j s)
  have hKic : ∀ i j ω, Continuous fun s => Ki i j s ω := by
    intro i j ω
    have hφ : Continuous fun y : SDEState n => fderiv ℝ f y (EuclideanSpace.single i 1) :=
      hDc.clm_apply continuous_const
    exact (hφ.comp (hXc ω)).mul (hHc i j ω)
  choose K hK using fun i j => ito1 j (Ki i j) (hKim i j) (hKic i j)
  have hform := @ito3 (by infer_instance) n (X x) hXm hXc hXa H (fun i j s ω => J s ω (i, j)) b
    hHm hHc hJ hbm hbc hXeq f (fLog_contDiff ha k) K hK t
  -- the martingale terms with `i ≠ k` vanish
  have hKz : ∀ i, i ≠ k → ∀ j, ∀ᵐ ω ∂P, K i j t ω = 0 := by
    intro i hi j
    have hb0 : ∀ s ω, |Ki i j s ω| ≤ 0 := by
      intro s ω; simp [hKidef, hfdef, fderiv_fLog_single ha, hi]
    obtain ⟨hm, hle, -⟩ := @ito2 hP j (Ki i j) (K i j) (hKim i j) (hKic i j) 0 hb0 (hK i j) t
    have hint : ∫ ω, K i j t ω ^ 2 ∂P = 0 :=
      le_antisymm (by simpa using hle) (integral_nonneg fun ω => sq_nonneg _)
    have := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (K i j t ω))
      hm.integrable_sq).mp hint
    filter_upwards [this] with ω hω
    simpa using hω
  -- the `i = k` terms are the Itô integrals `L j` on the event
  set E : Set Ω := {ω | ∀ s ≤ t, a ≤ X x s ω k} with hEdef
  have hloc : ∀ j, ∀ᵐ ω ∂P, ω ∈ E → K k j t ω = L j t ω := by
    intro j
    have hgm : ∀ s, Measurable[completedBrownianPast P B (fun _ => x) s] (gInt C (X x) k j s) :=
      fun s => ((hgc k).measurable.comp (hXa s)).mul measurable_const
    have hgcs : ∀ ω, Continuous fun s => gInt C (X x) k j s ω :=
      fun ω => ((hgc k).comp (hXc ω)).mul continuous_const
    refine loc1 j (Ki k j) (gInt C (X x) k j) (K k j) (L j) (hKim k j) (hKic k j) hgm hgcs
      (hK k j) (hL j) t E ?_
    intro ω hω N i hi
    have hs := hω _ (le_t_of_dyadic t N i hi)
    have hy : a / 2 < X x ((i : ℝ≥0) * t / 2 ^ N) ω k := by linarith
    have hy0 : X x ((i : ℝ≥0) * t / 2 ^ N) ω k ≠ 0 := by linarith
    simp only [hKidef, hfdef, fderiv_fLog_single ha, ite_true, if_true, hHeq, gInt]
    rw [deriv_logPsi ha hy]
    field_simp
  have hX0' : ∀ᵐ ω ∂P, X x 0 ω = x := hX0
  filter_upwards [hform, hX0', ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
      (show ∀ᵐ ω ∂P, i ≠ k → K i j t ω = 0 from by
        by_cases hi : i = k
        · exact Eventually.of_forall fun _ h => absurd hi h
        · filter_upwards [hKz i hi j] with ω h _ using h),
    ae_all_iff.mpr hloc] with ω hf h0 hz hl hE
  have hω : ω ∈ E := hE
  -- pathwise facts on the event
  have hpos : ∀ u ∈ Set.uIcc (0 : ℝ) t.val, a / 2 < X x u.toNNReal ω k :=
    fun u hu => by have := hE _ (toNNReal_le_of_mem hu); linarith
  have hcu : ∀ φ : SDEState n → ℝ, Continuous φ → Continuous fun u : ℝ => φ (X x u.toNNReal ω) :=
    fun φ hφ => hφ.comp ((hXc ω).comp continuous_real_toNNReal)
  -- left side and initial value
  have hlt : f (X x t ω) = Real.log (X x t ω k) := by
    simp only [hfdef, fLog]; exact logPsi_eq ha (by have := hE t le_rfl; linarith)
  have hl0 : f (X x 0 ω) = Real.log (x k) := by
    simp only [hfdef, fLog, h0]
    exact logPsi_eq ha (by have := hE 0 (by simp); rw [h0] at this; linarith)
  -- martingale part
  have hmart : (∑ i, ∑ j, K i j t ω) = ∑ j, L j t ω := by
    rw [Finset.sum_eq_single k (fun i _ hi => Finset.sum_eq_zero fun j _ => hz i j hi)
      (fun h => absurd (Finset.mem_univ k) h)]
    exact Finset.sum_congr rfl fun j _ => hl j hω
  -- drift part
  have hdrift : (∑ i, ∫ u in (0 : ℝ)..t.val,
      fderiv ℝ f (X x u.toNNReal ω) (EuclideanSpace.single i 1) * b i u.toNNReal ω) =
      ∫ u in (0 : ℝ)..t.val, C.f k (posPart (X x u.toNNReal ω)) := by
    rw [Finset.sum_eq_single k (fun i _ hi => by
        simp [hfdef, fderiv_fLog_single ha, hi]) (fun h => absurd (Finset.mem_univ k) h)]
    refine intervalIntegral.integral_congr fun u hu => ?_
    have h1 := hpos u hu
    have h2 : X x u.toNNReal ω k ≠ 0 := by linarith
    simp only [hfdef, fderiv_fLog_single ha, if_pos rfl, ite_true, if_true, hbeq, deriv_logPsi ha h1]
    field_simp
  -- second-order part
  have hsec : (1 / 2 : ℝ) * ∑ i, ∑ i', ∑ j, ∫ u in (0 : ℝ)..t.val,
      fderiv ℝ (fderiv ℝ f) (X x u.toNNReal ω) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i' 1) * H i j u.toNNReal ω * H i' j u.toNNReal ω =
      ∫ u in (0 : ℝ)..t.val, -(C.sig k k * C.g k (posPart (X x u.toNNReal ω)) ^ 2 / 2) := by
    rw [Finset.sum_eq_single k (fun i _ hi => Finset.sum_eq_zero fun i' _ =>
        Finset.sum_eq_zero fun j _ => by simp [hfdef, fderiv2_fLog_single ha, hi])
      (fun h => absurd (Finset.mem_univ k) h)]
    rw [Finset.sum_eq_single k (fun i' _ hi' => Finset.sum_eq_zero fun j _ => by
        simp [hfdef, fderiv2_fLog_single ha, hi'])
      (fun h => absurd (Finset.mem_univ k) h)]
    have hj : ∀ j, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ (fderiv ℝ f) (X x u.toNNReal ω) (EuclideanSpace.single k 1)
          (EuclideanSpace.single k 1) * H k j u.toNNReal ω * H k j u.toNNReal ω =
        ∫ u in (0 : ℝ)..t.val, -(C.g k (posPart (X x u.toNNReal ω)) ^ 2 * (C.Γ j k * C.Γ j k)) := by
      intro j
      refine intervalIntegral.integral_congr fun u hu => ?_
      have h1 := hpos u hu
      have h2 : X x u.toNNReal ω k ≠ 0 := by linarith
      simp only [hfdef, fderiv2_fLog_single ha, and_self, if_pos rfl, ite_true, if_true, hHeq,
        deriv_deriv_logPsi ha h1]
      field_simp
      try ring
    rw [Finset.sum_congr rfl fun j _ => hj j]
    rw [← intervalIntegral.integral_finsetSum (fun j _ =>
      (hcu (fun y => -(C.g k (posPart y) ^ 2 * (C.Γ j k * C.Γ j k)))
        ((((hgc k).pow 2).mul continuous_const).neg)).intervalIntegrable _ _)]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [sig_self, Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring
  rw [← hlt, hf, hl0, hmart, hdrift, hsec]
  have hI1 : IntervalIntegrable (fun u : ℝ => C.f k (posPart (X x u.toNNReal ω))) volume 0 t.val :=
    (hcu _ (hfc k)).intervalIntegrable _ _
  have hI2 : IntervalIntegrable
      (fun u : ℝ => -(C.sig k k * C.g k (posPart (X x u.toNNReal ω)) ^ 2 / 2)) volume 0 t.val :=
    (hcu _ ((continuous_const.mul ((hgc k).pow 2)).div_const 2).neg).intervalIntegrable _ _
  rw [add_assoc, ← intervalIntegral.integral_add hI1 hI2]
  congr 2

end StochKolmogorov.Classify.HL

end Part1


section Part2
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.HL

open StochKolmogorov.Classify EthierKurtz

/-- Measurability of `ω ↦ ∫₀ˢ H(u) du` for `H` continuous in time and `m`-measurable up to `s`
(Carathéodory). -/
lemma measurable_integral_of_adapted {Ω : Type*} [m : MeasurableSpace Ω] {H : ℝ≥0 → Ω → ℝ}
    (s : ℝ≥0) (hm : ∀ u, u ≤ s → Measurable (H u)) (hc : ∀ ω, Continuous fun u => H u ω) :
    Measurable (fun ω => ∫ u in (0 : ℝ)..s.val, H u.toNNReal ω) := by
  set H' : ℝ → Ω → ℝ := fun u ω => H (min u.toNNReal s) ω with hH'
  have hH'c : ∀ ω, Continuous fun u => H' u ω :=
    fun ω => (hc ω).comp (continuous_real_toNNReal.min continuous_const)
  have hH'm : ∀ u, Measurable (H' u) := fun u => hm _ (min_le_right _ _)
  have hj : Measurable (Function.uncurry H') :=
    measurable_uncurry_of_continuous_of_measurable hH'c hH'm
  have hj' : StronglyMeasurable (Function.uncurry fun (ω : Ω) (u : ℝ) => H' u ω) :=
    (hj.comp measurable_swap).stronglyMeasurable
  have hint := hj'.integral_prod_right (ν := volume.restrict (Set.Ioc (0 : ℝ) s.val))
  have heq : (fun ω => ∫ u in (0 : ℝ)..s.val, H u.toNNReal ω) =
      fun ω => ∫ u, H' u ω ∂(volume.restrict (Set.Ioc (0 : ℝ) s.val)) := by
    funext ω
    rw [intervalIntegral.integral_of_le s.2]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    simp only [hH']
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hu.2)]
  rw [heq]; exact hint.measurable

/-- The gate `ρ(y) = 1 − min 1 (max 0 y)`. -/
noncomputable def rho (y : ℝ) : ℝ := 1 - min 1 (max 0 y)

lemma rho_nonneg (y : ℝ) : 0 ≤ rho y := by
  unfold rho; have := min_le_left (1 : ℝ) (max 0 y); linarith

lemma rho_le_one (y : ℝ) : rho y ≤ 1 := by
  unfold rho; have := le_min (zero_le_one' ℝ) (le_max_left 0 y); linarith

lemma rho_of_le {y : ℝ} (hy : y ≤ 0) : rho y = 1 := by
  unfold rho; rw [max_eq_left hy, min_eq_right zero_le_one]; ring

lemma rho_of_ge {y : ℝ} (hy : 1 ≤ y) : rho y = 0 := by
  unfold rho; rw [max_eq_right (by linarith), min_eq_left hy]; ring

lemma continuous_rho : Continuous rho := by
  unfold rho; fun_prop

lemma rho_sq_le_one (y : ℝ) : rho y ^ 2 ≤ 1 := by
  have h0 := rho_nonneg y; have h1 := rho_le_one y; nlinarith

/-- Pathwise gate bound: `∫₀ᵗ φ ρ(∫₀ᵘφ − A)² ≤ A + 1` for continuous `φ ≥ 0`. -/
lemma gate_bound (φ : ℝ → ℝ) (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u) {A : ℝ} (hA : 0 ≤ A)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t, φ u * rho ((∫ v in (0 : ℝ)..u, φ v) - A) ^ 2 ≤ A + 1 := by
  set Q : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, φ v with hQ
  have hQc : Continuous Q := intervalIntegral.continuous_primitive
    (fun a b => hφc.intervalIntegrable a b) 0
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => φ u * rho (Q u - A) ^ 2) volume a b :=
    fun a b => (hφc.mul ((continuous_rho.comp (hQc.sub continuous_const)).pow 2)).intervalIntegrable a b
  have hle : ∀ b, 0 ≤ b → ∫ u in (0 : ℝ)..b, φ u * rho (Q u - A) ^ 2 ≤ Q b := by
    intro b hb
    refine intervalIntegral.integral_mono_on hb (hint 0 b) (hφc.intervalIntegrable 0 b) ?_
    intro u _
    have := rho_sq_le_one (Q u - A)
    have := hφ0 u
    nlinarith
  have hQmono : ∀ a b, a ≤ b → Q a ≤ Q b := by
    intro a b hab
    have : Q b = Q a + ∫ v in a..b, φ v := by
      simp only [hQ]
      rw [intervalIntegral.integral_add_adjacent_intervals (hφc.intervalIntegrable _ _)
        (hφc.intervalIntegrable _ _)]
    rw [this]
    have : 0 ≤ ∫ v in a..b, φ v := intervalIntegral.integral_nonneg hab (fun u _ => hφ0 u)
    linarith
  by_cases hT : Q t ≤ A + 1
  · exact (hle t ht).trans hT
  · replace hT := not_le.mp hT
    have hQ0 : Q 0 = 0 := by simp [hQ]
    obtain ⟨τ, hτ, hQτ⟩ : ∃ τ ∈ Set.Icc 0 t, Q τ = A + 1 :=
      intermediate_value_Icc ht hQc.continuousOn ⟨by rw [hQ0]; linarith, hT.le⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 τ) (hint τ t)]
    have h2 : ∫ u in τ..t, φ u * rho (Q u - A) ^ 2 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro u hu
        rw [Set.uIcc_of_le hτ.2] at hu
        have : 1 ≤ Q u - A := by have := hQmono τ u hu.1; linarith
        simp only [rho_of_ge this]; ring
    rw [h2, add_zero]
    exact (hle τ hτ.1).trans hQτ.le

/-- `∫ Φ ≤ c` for `0 ≤ Φ ≤ c` pointwise on a probability space (also if `Φ` is not integrable). -/
lemma integral_le_of_le_const {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Φ : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ ω, Φ ω ≤ c) :
    ∫ ω, Φ ω ∂P ≤ c := by
  by_cases hi : Integrable Φ P
  · calc ∫ ω, Φ ω ∂P ≤ ∫ _ω, c ∂P := integral_mono hi (integrable_const c) h
      _ = c := by simp
  · rw [integral_undef hi]; exact hc

section main

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma completedBrownianPast_mono' (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) {s t : ℝ≥0} (hst : s ≤ t) :
    completedBrownianPast P W ξ s ≤ completedBrownianPast P W ξ t := by
  unfold completedBrownianPast
  refine sup_le_sup_right (sup_le_sup_right ?_ _) _
  refine iSup_le fun r => ?_
  have hr : r.val ≤ t := r.2.trans hst
  exact le_iSup (fun q : Set.Iic t => MeasurableSpace.comap (W q.val) inferInstance) ⟨r.val, hr⟩

/-- C3: gated Chebyshev bound for the Itô integral of an unbounded continuous adapted `g·c`. -/
theorem gated_tail {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) (g : ℝ≥0 → Ω → ℝ)
    (hgm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (g s))
    (hgc : ∀ ω, Continuous fun s => g s ω) (c : ℝ) (L : ℝ≥0 → Ω → ℝ)
    (hL : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (fun s ω => g s ω * c) L)
    (t : ℝ≥0) {A : ℝ} (hA : 0 ≤ A) {lam : ℝ} (hlam : 0 < lam) :
    P {ω | lam < |L t ω| ∧ ∫ u in (0 : ℝ)..t.val, g u.toNNReal ω ^ 2 ≤ A} ≤
      ENNReal.ofReal (c ^ 2 * (A + 1) / lam ^ 2) := by
  obtain ⟨ito1, ito2, -⟩ := brownian_ito_integral_and_formula hW x₀
  obtain ⟨loc1, loc2, -, -⟩ := brownian_ito_integral_locality_and_continuity hW x₀
  set F := completedBrownianPast P W (fun _ => x₀) with hF
  have hFmono : ∀ {u s : ℝ≥0}, u ≤ s → F u ≤ F s := fun hus =>
    completedBrownianPast_mono' P W _ hus
  -- clamp, primitive, gate
  let cl : ℕ → ℝ → ℝ := fun M y => max (-(M : ℝ)) (min (M : ℝ) y)
  have hclc : ∀ M, Continuous (cl M) := fun M =>
    continuous_const.max (continuous_const.min continuous_id)
  have hclb : ∀ (M : ℕ) (y : ℝ), |cl M y| ≤ M := by
    intro M y
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hcl_eq : ∀ (M : ℕ) (y : ℝ), |y| ≤ M → cl M y = y := by
    intro M y hy
    obtain ⟨h1, h2⟩ := abs_le.mp hy
    simp only [cl]; rw [min_eq_right h2, max_eq_right h1]
  let gM : ℕ → ℝ≥0 → Ω → ℝ := fun M s ω => cl M (g s ω)
  let Q : ℕ → ℝ≥0 → Ω → ℝ := fun M s ω => ∫ u in (0 : ℝ)..s.val, gM M u.toNNReal ω ^ 2
  let G : ℕ → ℝ≥0 → Ω → ℝ := fun M s ω => gM M s ω * c * rho (Q M s ω - A)
  have hgMc : ∀ M ω, Continuous fun s => gM M s ω := fun M ω => (hclc M).comp (hgc ω)
  have hgMm : ∀ M s, Measurable[F s] (gM M s) := fun M s => (hclc M).measurable.comp (hgm s)
  have hQc : ∀ M ω, Continuous fun s : ℝ≥0 => Q M s ω := fun M ω =>
    (intervalIntegral.continuous_primitive (fun a b =>
      (((hgMc M ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable a b) 0).comp
      NNReal.continuous_coe
  have hQm : ∀ M s, Measurable[F s] (Q M s) := fun M s =>
    @measurable_integral_of_adapted Ω (F s) (fun u ω => gM M u ω ^ 2) s
      (fun u hu => ((hgMm M u).pow_const 2).mono (hFmono hu) le_rfl) (fun ω => (hgMc M ω).pow 2)
  have hGc : ∀ M ω, Continuous fun s => G M s ω := fun M ω =>
    ((hgMc M ω).mul continuous_const).mul (continuous_rho.comp ((hQc M ω).sub continuous_const))
  have hGm : ∀ M s, Measurable[F s] (G M s) := fun M s =>
    ((hgMm M s).mul_const c).mul (continuous_rho.measurable.comp ((hQm M s).sub_const A))
  have hGb : ∀ M s ω, |G M s ω| ≤ M * |c| := by
    intro M s ω
    have h1 := hclb M (g s ω)
    have h2 := rho_nonneg (Q M s ω - A)
    have h3 := rho_le_one (Q M s ω - A)
    have : |G M s ω| = |cl M (g s ω)| * |c| * rho (Q M s ω - A) := by
      simp only [G, gM, abs_mul, abs_of_nonneg h2]
    rw [this]
    calc |cl M (g s ω)| * |c| * rho (Q M s ω - A) ≤ M * |c| * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg c)) h3 h2
            (mul_nonneg (Nat.cast_nonneg M) (abs_nonneg c))
      _ = M * |c| := mul_one _
  choose LG hLG using fun M => ito1 j (G M) (hGm M) (hGc M)
  -- L² bound for the gated integral
  have hL2 : ∀ M, ∫ ω, LG M t ω ^ 2 ∂P ≤ c ^ 2 * (A + 1) := by
    intro M
    have h := loc2 j (G M) (LG M) (fun _ _ => 0) (fun _ _ => 0) (hGm M) (hGc M) (M * |c|)
      (hGb M) (hLG M) (fun _ => measurable_const) (fun _ => continuous_const)
      (fun _ _ => by rw [abs_zero]; exact mul_nonneg (Nat.cast_nonneg M) (abs_nonneg c))
      (hasBrownianItoIntegral_zero _ _ _) t
    simp only [sub_zero] at h
    refine h.trans (integral_le_of_le_const (mul_nonneg (sq_nonneg c) (by linarith)) fun ω => ?_)
    have hφc : Continuous fun u : ℝ => gM M u.toNNReal ω ^ 2 :=
      ((hgMc M ω).comp continuous_real_toNNReal).pow 2
    have hb := gate_bound (fun u : ℝ => gM M u.toNNReal ω ^ 2) hφc (fun u => sq_nonneg _) hA t.2
    calc ∫ u in (0 : ℝ)..t.val, G M u.toNNReal ω ^ 2
        = c ^ 2 * ∫ u in (0 : ℝ)..t.val, gM M u.toNNReal ω ^ 2 *
            rho ((∫ v in (0 : ℝ)..u, gM M v.toNNReal ω ^ 2) - A) ^ 2 := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun u hu => ?_
          rw [Set.uIcc_of_le t.2] at hu
          have hu' : (u.toNNReal).val = u := Real.coe_toNNReal u hu.1
          simp only [G, Q]
          rw [hu']
          ring
      _ ≤ c ^ 2 * (A + 1) := mul_le_mul_of_nonneg_left hb (sq_nonneg c)
  -- Chebyshev for the gated integral
  have hcheb : ∀ M, P {ω | lam < |LG M t ω|} ≤ ENNReal.ofReal (c ^ 2 * (A + 1) / lam ^ 2) := by
    intro M
    obtain ⟨hmem, -, -⟩ := ito2 j (G M) (LG M) (hGm M) (hGc M) (M * |c|) (hGb M) (hLG M) t
    have hint := hmem.integrable_sq
    have h := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall fun ω => sq_nonneg (LG M t ω)) hint (lam ^ 2)
    have hsub : {ω | lam < |LG M t ω|} ⊆ {ω | lam ^ 2 ≤ LG M t ω ^ 2} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have : lam ^ 2 ≤ |LG M t ω| ^ 2 := pow_le_pow_left₀ hlam.le hω.le 2
      rwa [sq_abs] at this
    have hlam2 : 0 < lam ^ 2 := by positivity
    have hreal : P.real {ω | lam ^ 2 ≤ LG M t ω ^ 2} ≤ c ^ 2 * (A + 1) / lam ^ 2 := by
      rw [le_div_iff₀ hlam2]; linarith [h, hL2 M]
    calc P {ω | lam < |LG M t ω|} ≤ P {ω | lam ^ 2 ≤ LG M t ω ^ 2} := measure_mono hsub
      _ = ENNReal.ofReal (P.real {ω | lam ^ 2 ≤ LG M t ω ^ 2}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  -- locality on `{|g| ≤ M on [0,t]} ∩ {∫₀ᵗ g² ≤ A}` and `M → ∞`
  set S : Set Ω := {ω | lam < |L t ω| ∧ ∫ u in (0 : ℝ)..t.val, g u.toNNReal ω ^ 2 ≤ A} with hS
  set SM : ℕ → Set Ω := fun M => S ∩ {ω | ∀ s ≤ t, |g s ω| ≤ M} with hSMdef
  have hSM : ∀ M, P (SM M) ≤ ENNReal.ofReal (c ^ 2 * (A + 1) / lam ^ 2) := by
    intro M
    have hloc := loc1 j (G M) (fun s ω => g s ω * c) (LG M) L (hGm M) (hGc M)
      (fun s => (hgm s).mul_const c) (fun ω => (hgc ω).mul continuous_const) (hLG M) hL t (SM M)
      (by
        intro ω hω N i hi
        have hs := le_t_of_dyadic t N i hi
        have hgs : ∀ s', s' ≤ t → gM M s' ω = g s' ω := fun s' hs' => hcl_eq M _ (hω.2 s' hs')
        have hQs : Q M ((i : ℝ≥0) * t / 2 ^ N) ω ≤ A := by
          have heq : Q M ((i : ℝ≥0) * t / 2 ^ N) ω =
              ∫ u in (0 : ℝ)..((i : ℝ≥0) * t / 2 ^ N : ℝ≥0).val, g u.toNNReal ω ^ 2 := by
            refine intervalIntegral.integral_congr fun u hu => ?_
            show gM M u.toNNReal ω ^ 2 = g u.toNNReal ω ^ 2
            rw [hgs _ ((toNNReal_le_of_mem hu).trans hs)]
          rw [heq]
          refine le_trans ?_ hω.1.2
          refine intervalIntegral.integral_mono_interval le_rfl
            ((i : ℝ≥0) * t / 2 ^ N : ℝ≥0).2 (by exact_mod_cast hs)
            (Eventually.of_forall fun u => sq_nonneg _)
            ((((hgc ω).comp continuous_real_toNNReal).pow 2).intervalIntegrable _ _)
        simp only [G]
        rw [hgs _ hs, rho_of_le (by linarith), mul_one])
    refine le_trans (measure_mono_ae ?_) (hcheb M)
    filter_upwards [hloc] with ω hω hmem
    have h1 := hω hmem
    show lam < |LG M t ω|
    rw [h1]; exact hmem.1.1
  have hmono : Monotone SM := by
    intro M M' h ω hω
    exact ⟨hω.1, fun s hs => (hω.2 s hs).trans (by exact_mod_cast h)⟩
  have hU : ⋃ M, SM M = S := by
    ext ω; simp only [Set.mem_iUnion]; constructor
    · rintro ⟨M, h⟩; exact h.1
    · intro h
      obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
        (hgc ω).continuousOn
      obtain ⟨M, hM⟩ := exists_nat_ge B0
      refine ⟨M, h, fun s hs => ?_⟩
      have := hB0 s ⟨by positivity, hs⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans hM
  rw [← hU]
  exact le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hSM

end main

end StochKolmogorov.Classify.HL

end Part2


section Part3
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.HL

open StochKolmogorov.Classify EthierKurtz

section C4

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma sq_bound_arith {c K ε T : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) (hT : 1 ≤ T) :
    c ^ 2 * (K * T + 1) / (ε * T) ^ 2 ≤ c ^ 2 * (K + 1) / (ε ^ 2 * T) := by
  have hT0 : 0 < T := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h : c ^ 2 * (K + 1) * (ε * T) ^ 2 - c ^ 2 * (K * T + 1) * (ε ^ 2 * T) =
      c ^ 2 * ε ^ 2 * T * (T - 1) := by ring
  have h2 : 0 ≤ c ^ 2 * ε ^ 2 * T * (T - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg c) (sq_nonneg ε)) hT0.le) (by linarith)
  linarith

/-- C4: the martingale SLLN along squares under a linear bound on the quadratic variation. -/
theorem lln_sq {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) (g : ℝ≥0 → Ω → ℝ)
    (hgm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (g s))
    (hgc : ∀ ω, Continuous fun s => g s ω) (c : ℝ) (L : ℝ≥0 → Ω → ℝ)
    (hL : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (fun s ω => g s ω * c) L) (K : ℝ) :
    ∀ᵐ ω ∂P, (∀ᶠ t : ℝ in atTop, ∫ u in (0 : ℝ)..t, g u.toNNReal ω ^ 2 ≤ K * t) →
      Tendsto (fun m : ℕ => L ((m ^ 2 : ℕ) : ℝ≥0) ω / ((m ^ 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  let T : ℕ → ℝ := fun m => (((m + 1) ^ 2 : ℕ) : ℝ)
  have hT1 : ∀ m, 1 ≤ T m := fun m => by
    simp only [T]; exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos m)
  let ε : ℕ → ℝ := fun q => 1 / ((q : ℝ) + 1)
  have hε : ∀ q, 0 < ε q := fun q => by positivity
  let S : ℕ → ℕ → Set Ω := fun q m =>
    {ω | ε q * T m < |L (((m + 1) ^ 2 : ℕ) : ℝ≥0) ω| ∧
      ∫ u in (0 : ℝ)..T m, g u.toNNReal ω ^ 2 ≤ K' * T m}
  have hS : ∀ q m, P (S q m) ≤ ENNReal.ofReal (c ^ 2 * (K' + 1) / (ε q ^ 2) * (1 / T m)) := by
    intro q m
    have h := gated_tail hW x₀ j g hgm hgc c L hL (((m + 1) ^ 2 : ℕ) : ℝ≥0)
      (A := K' * T m) (mul_nonneg hK'0 (by linarith [hT1 m])) (lam := ε q * T m)
      (mul_pos (hε q) (by linarith [hT1 m]))
    have hv : ((((m + 1) ^ 2 : ℕ) : ℝ≥0)).val = T m := NNReal.coe_natCast _
    rw [hv] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have := sq_bound_arith (c := c) hK'0 (hε q) (hT1 m)
    calc c ^ 2 * (K' * T m + 1) / (ε q * T m) ^ 2 ≤ c ^ 2 * (K' + 1) / (ε q ^ 2 * T m) := this
      _ = c ^ 2 * (K' + 1) / (ε q ^ 2) * (1 / T m) := by
        field_simp
  have hsumT : Summable fun m : ℕ => 1 / T m := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine h.congr fun m => ?_
    simp [T]
  have hBC : ∀ q, ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∉ S q m := by
    intro q
    refine ae_eventually_notMem ?_
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (hS q))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg
      (div_nonneg (mul_nonneg (sq_nonneg c) (by linarith)) (sq_nonneg _))
      (by have := hT1 m; positivity)) (hsumT.mul_left _)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_all_iff.mpr hBC] with ω hω hK
  refine (tendsto_add_atTop_iff_nat 1).mp ?_
  have hTt : Tendsto T atTop atTop := by
    have h1 : Tendsto (fun m : ℕ => (m + 1) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp (tendsto_add_atTop_nat 1)
    exact tendsto_natCast_atTop_atTop.comp h1
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt he
  filter_upwards [hω q, hTt.eventually hK] with m h1 h2
  have hTm := hT1 m
  have hTpos : 0 < T m := by linarith
  have hint : ∫ u in (0 : ℝ)..T m, g u.toNNReal ω ^ 2 ≤ K' * T m :=
    h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hTpos.le)
  have hle : |L (((m + 1) ^ 2 : ℕ) : ℝ≥0) ω| ≤ ε q * T m := by
    by_contra hc
    exact h1 ⟨not_le.mp hc, hint⟩
  have hTm' : (((m + 1) ^ 2 : ℕ) : ℝ) = T m := rfl
  rw [Real.dist_eq, sub_zero, hTm', abs_div, abs_of_pos hTpos, div_lt_iff₀ hTpos]
  calc |L (((m + 1) ^ 2 : ℕ) : ℝ≥0) ω| ≤ ε q * T m := hle
    _ < e * T m := mul_lt_mul_of_pos_right hq hTpos

end C4

end StochKolmogorov.Classify.HL

end Part3


section Part4
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.HL

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- C2: the log-Itô identity at a fixed time, a.s., when the path stays in the open orthant. -/
theorem log_rep (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (hcont : ∀ i, ContinuousOn (C.f i) (orthant n) ∧ ContinuousOn (C.g i) (orthant n))
    (x : SDEState n) (hx : x ∈ orthant n)
    (hstay : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ openOrthant n) (k : Fin n) (L : Fin n → ℝ≥0 → Ω → ℝ)
    (hL : ∀ j, HasBrownianItoIntegral P (completedBrownianPast P B (fun _ => x))
        (fun s ω => B s ω j) (gInt C (X x) k j) (L j)) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Real.log (X x t ω k) = Real.log (x k) + (∑ j, L j t ω) +
        ∫ u in (0 : ℝ)..t.val, hInt C k (X x u.toNNReal ω) := by
  have hR : ∀ R : ℕ, ∀ᵐ ω ∂P, (∀ s ≤ t, 1 / ((R : ℝ) + 1) ≤ X x s ω k) →
      Real.log (X x t ω k) = Real.log (x k) + (∑ j, L j t ω) +
        ∫ u in (0 : ℝ)..t.val, hInt C k (X x u.toNNReal ω) :=
    fun R => log_ito P C B X hX hcont x hx k L hL _ (by positivity) t
  have hXc : ∀ ω, Continuous fun s => X x s ω := (hX.2.2 x hx).2.1
  filter_upwards [ae_all_iff.mpr hR, hstay] with ω hω hs
  obtain ⟨s0, hs0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_isMinOn
    ⟨0, ⟨le_rfl, by positivity⟩⟩ ((PiLp.continuous_apply 2 _ k).comp (hXc ω)).continuousOn
  have hpos : 0 < X x s0 ω k := hs s0 k
  obtain ⟨R, hR⟩ := exists_nat_one_div_lt hpos
  refine hω R fun s hst => hR.le.trans ?_
  exact isMinOn_iff.mp hmin s ⟨by positivity, hst⟩

/-- C5 = the NEW child `log_lln_squares`: the strong law for `ln Xᵢ` along squares. -/
theorem log_lln_squares (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (hcont : ∀ i, ContinuousOn (C.f i) (orthant n) ∧ ContinuousOn (C.g i) (orthant n))
    (x : SDEState n) (hx : x ∈ openOrthant n)
    (hstay : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ openOrthant n) :
    (∃ K : ℝ, ∀ᵐ ω ∂P, ∀ i, ∀ᶠ t : ℝ in atTop,
      ∫ u in (0 : ℝ)..t, C.g i (X x u.toNNReal ω) ^ 2 ≤ K * t) →
    ∀ᵐ ω ∂P, ∀ i, Tendsto (fun m : ℕ =>
      Real.log (X x ((m ^ 2 : ℕ) : ℝ≥0) ω i) / ((m ^ 2 : ℕ) : ℝ)
      - ((m ^ 2 : ℕ) : ℝ)⁻¹ * ∫ u in (0 : ℝ)..((m ^ 2 : ℕ) : ℝ),
          (C.f i (X x u.toNNReal ω) - C.sig i i * C.g i (X x u.toNNReal ω) ^ 2 / 2))
        atTop (𝓝 0) := by
  rintro ⟨K, hK⟩
  have hx' : x ∈ orthant n := fun i => (hx i).le
  haveI := hX.1
  obtain ⟨hXm, hXc, hXa, -⟩ := hX.2.2 x hx'
  obtain ⟨ito1, -, -⟩ := brownian_ito_integral_and_formula hX.2.1 x
  have hgc : ∀ k, Continuous fun y : SDEState n => C.g k (posPart y) :=
    fun k => cont_comp_posPart (hcont k).2
  have hgm : ∀ k j s, Measurable[completedBrownianPast P B (fun _ => x) s]
      (gInt C (X x) k j s) :=
    fun k j s => ((hgc k).measurable.comp (hXa s)).mul measurable_const
  have hgcs : ∀ k j ω, Continuous fun s => gInt C (X x) k j s ω :=
    fun k j ω => ((hgc k).comp (hXc ω)).mul continuous_const
  choose L hL using fun k j => ito1 j (gInt C (X x) k j) (hgm k j) (hgcs k j)
  have hrep : ∀ k (m : ℕ), ∀ᵐ ω ∂P, Real.log (X x ((m ^ 2 : ℕ) : ℝ≥0) ω k) =
      Real.log (x k) + (∑ j, L k j ((m ^ 2 : ℕ) : ℝ≥0) ω) +
        ∫ u in (0 : ℝ)..((m ^ 2 : ℕ) : ℝ≥0).val, hInt C k (X x u.toNNReal ω) :=
    fun k m => log_rep P C B X hX hcont x hx' hstay k (L k) (hL k) _
  have hlln : ∀ k j, ∀ᵐ ω ∂P, (∀ᶠ t : ℝ in atTop,
      ∫ u in (0 : ℝ)..t, C.g k (posPart (X x u.toNNReal ω)) ^ 2 ≤ K * t) →
      Tendsto (fun m : ℕ => L k j ((m ^ 2 : ℕ) : ℝ≥0) ω / ((m ^ 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    fun k j => lln_sq hX.2.1 x j (fun s ω => C.g k (posPart (X x s ω)))
      (fun s => (hgc k).measurable.comp (hXa s)) (fun ω => (hgc k).comp (hXc ω)) (C.Γ j k)
      (L k j) (hL k j) K
  filter_upwards [hK, hstay, ae_all_iff.mpr fun k => ae_all_iff.mpr fun m => hrep k m,
    ae_all_iff.mpr fun k => ae_all_iff.mpr fun j => hlln k j] with ω hKω hs hr hl
  intro k
  have hpp : ∀ u, posPart (X x u ω) = X x u ω := fun u => posPart_eq_of_mem fun i => (hs u i).le
  have hKk : ∀ᶠ t : ℝ in atTop,
      ∫ u in (0 : ℝ)..t, C.g k (posPart (X x u.toNNReal ω)) ^ 2 ≤ K * t := by
    simpa only [hpp] using hKω k
  have hLk := fun j => hl k j hKk
  have hT : Tendsto (fun m : ℕ => ((m ^ 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_pow_atTop two_ne_zero)
  have hlim : Tendsto (fun m : ℕ => Real.log (x k) / ((m ^ 2 : ℕ) : ℝ) +
      ∑ j, L k j ((m ^ 2 : ℕ) : ℝ≥0) ω / ((m ^ 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h1 := (tendsto_const_nhds (x := Real.log (x k))).div_atTop hT
    have h2 := tendsto_finset_sum Finset.univ fun j _ => hLk j
    simpa using h1.add h2
  refine hlim.congr' (Eventually.of_forall fun m => ?_)
  have hI : ∫ u in (0 : ℝ)..((m ^ 2 : ℕ) : ℝ≥0).val, hInt C k (X x u.toNNReal ω) =
      ∫ u in (0 : ℝ)..((m ^ 2 : ℕ) : ℝ),
        (C.f k (X x u.toNNReal ω) - C.sig k k * C.g k (X x u.toNNReal ω) ^ 2 / 2) := by
    have hv : ((m ^ 2 : ℕ) : ℝ≥0).val = ((m ^ 2 : ℕ) : ℝ) := NNReal.coe_natCast _
    rw [hv]; simp only [hInt, hpp]
  simp only
  rw [hr k m, hI, ← Finset.sum_div]
  ring

end StochKolmogorov.Classify.HL

end Part4


open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

open StochKolmogorov.Classify EthierKurtz in
theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : StochKolmogorov.Classify.Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (hcont : ∀ i, ContinuousOn (C.f i) (orthant n) ∧ ContinuousOn (C.g i) (orthant n))
    (x : SDEState n) (hx : x ∈ openOrthant n)
    (hstay : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ openOrthant n) :
    (∃ K : ℝ, ∀ᵐ ω ∂P, ∀ i, ∀ᶠ t : ℝ in atTop,
      ∫ u in (0 : ℝ)..t, C.g i (X x u.toNNReal ω) ^ 2 ≤ K * t) →
    ∀ᵐ ω ∂P, ∀ i, Tendsto (fun m : ℕ =>
      Real.log (X x ((m ^ 2 : ℕ) : ℝ≥0) ω i) / ((m ^ 2 : ℕ) : ℝ)
      - ((m ^ 2 : ℕ) : ℝ)⁻¹ * ∫ u in (0 : ℝ)..((m ^ 2 : ℕ) : ℝ),
          (C.f i (X x u.toNNReal ω) - C.sig i i * C.g i (X x u.toNNReal ω) ^ 2 / 2))
        atTop (𝓝 0) := by
  exact StochKolmogorov.Classify.HL.log_lln_squares P C B X hX hcont x hx hstay
