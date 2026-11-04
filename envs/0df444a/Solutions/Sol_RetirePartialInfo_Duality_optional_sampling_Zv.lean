-- Prove2me | solution 1 for RetirePartialInfo.Duality.optional_sampling_Zv
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T06:47:25.542206+00:00
-- url     : https://prove2.me/submissions/f5a56d32-4a48-4662-b089-113025ffd864

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_RetirePartialInfo_Duality_Primal

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
open RetirePartialInfo.Duality

namespace RetirePIos

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_tau (p : Params) (st : Setting Ω) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ) :
    Measurable τ := by
  refine measurable_of_Iic fun t => ?_
  have h := (hτ.1 t)
  have : τ ⁻¹' Iic t = {ω | (τ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} := by
    ext ω; simp only [mem_preimage, mem_Iic, mem_setOf_eq, WithTop.coe_le_coe]
  rw [this]
  exact (FS p st).le t _ h

lemma tau_le_Tn (p : Params) (st : Setting Ω) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ)
    (ω : Ω) : τ ω ≤ p.Tn := by
  have h1 : (τ ω : ℝ) ≤ p.T := (hτ.2 ω).trans p.T1_le_T
  rw [← NNReal.coe_le_coe, Params.Tn, Real.coe_toNNReal _ p.T_pos.le]; exact h1

/-- Mesh of the `n`-th dyadic grid of `[0, T]`. -/
noncomputable def δ (p : Params) (n : ℕ) : ℝ≥0 := p.Tn / 2 ^ n

lemma δ_pos (p : Params) (n : ℕ) : 0 < δ p n := by
  unfold δ
  exact div_pos (Real.toNNReal_pos.2 p.T_pos) (pow_pos two_pos n)

/-- The dyadic approximation from above of a stopping time. -/
noncomputable def τd (p : Params) (τ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  (⌈τ ω / δ p n⌉₊ : ℝ≥0) * δ p n

lemma le_τd (p : Params) (τ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) : τ ω ≤ τd p τ n ω := by
  unfold τd
  have := Nat.le_ceil (τ ω / δ p n)
  rwa [div_le_iff₀ (δ_pos p n)] at this

lemma τd_lt (p : Params) (τ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) : τd p τ n ω < τ ω + δ p n := by
  unfold τd
  have := Nat.ceil_lt_add_one (zero_le (a := τ ω / δ p n))
  have h2 := mul_lt_mul_of_pos_right this (δ_pos p n)
  rwa [add_mul, div_mul_cancel₀ _ (δ_pos p n).ne', one_mul] at h2

lemma τd_le_Tn (p : Params) (st : Setting Ω) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ)
    (n : ℕ) (ω : Ω) : τd p τ n ω ≤ p.Tn := by
  unfold τd
  have hk : ⌈τ ω / δ p n⌉₊ ≤ 2 ^ n := by
    rw [Nat.ceil_le, div_le_iff₀ (δ_pos p n)]
    unfold δ
    push_cast
    rw [mul_div_cancel₀ _ (pow_ne_zero n two_ne_zero)]
    exact tau_le_Tn p st τ hτ ω
  calc (⌈τ ω / δ p n⌉₊ : ℝ≥0) * δ p n ≤ (2 ^ n : ℕ) * δ p n := by gcongr
    _ = p.Tn := by unfold δ; push_cast; rw [mul_div_cancel₀ _ (pow_ne_zero n two_ne_zero)]

lemma τd_le_iff (p : Params) (τ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) (t : ℝ≥0) :
    τd p τ n ω ≤ t ↔ τ ω ≤ (⌊t / δ p n⌋₊ : ℝ≥0) * δ p n := by
  unfold τd
  rw [← le_div_iff₀ (δ_pos p n), ← div_le_iff₀ (δ_pos p n)]
  constructor
  · intro h
    have h1 : ⌈τ ω / δ p n⌉₊ ≤ ⌊t / δ p n⌋₊ := Nat.le_floor h
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  · intro h
    have h1 : ⌈τ ω / δ p n⌉₊ ≤ ⌊t / δ p n⌋₊ := Nat.ceil_le.2 h
    exact (by exact_mod_cast h1 : (⌈τ ω / δ p n⌉₊ : ℝ≥0) ≤ ⌊t / δ p n⌋₊).trans
      (Nat.floor_le (zero_le (a := t / δ p n)))

lemma isStoppingTime_τd (p : Params) (st : Setting Ω) (τ : Ω → ℝ≥0)
    (hτ : IsRetirementTime p st τ) (n : ℕ) :
    IsStoppingTime (FS p st) (fun ω => (τd p τ n ω : WithTop ℝ≥0)) := by
  intro t
  set s : ℝ≥0 := (⌊t / δ p n⌋₊ : ℝ≥0) * δ p n
  have hst : s ≤ t := by
    have := Nat.floor_le (zero_le (a := t / δ p n))
    rwa [← le_div_iff₀ (δ_pos p n)]
  have hset : {ω | (τd p τ n ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
      {ω | (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_setOf_eq, WithTop.coe_le_coe]
    exact τd_le_iff p τ n ω t
  rw [hset]
  exact (FS p st).mono hst _ (hτ.1 s)

lemma tendsto_τd (p : Params) (τ : Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun n => τd p τ n ω) atTop (𝓝 (τ ω)) := by
  have hδ : Tendsto (fun n => δ p n) atTop (𝓝 0) := by
    unfold δ
    have : Tendsto (fun n : ℕ => ((2 : ℝ≥0) ^ n)⁻¹) atTop (𝓝 0) :=
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0)⁻¹) (by norm_num)).congr
        (fun n => by rw [inv_pow])
    simpa [div_eq_mul_inv] using this.const_mul p.Tn
  have hup : Tendsto (fun n => τ ω + δ p n) atTop (𝓝 (τ ω)) := by
    simpa using tendsto_const_nhds.add hδ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => le_τd p τ n ω) (fun n => (τd_lt p τ n ω).le)

lemma countable_range_τd (p : Params) (τ : Ω → ℝ≥0) (n : ℕ) :
    (Set.range (fun ω => (τd p τ n ω : WithTop ℝ≥0))).Countable := by
  refine (Set.countable_range (fun k : ℕ => (((k : ℝ≥0) * δ p n : ℝ≥0) : WithTop ℝ≥0))).mono ?_
  rintro _ ⟨ω, rfl⟩
  exact ⟨⌈τ ω / δ p n⌉₊, rfl⟩

lemma measurable_τd (p : Params) (st : Setting Ω) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ)
    (n : ℕ) : Measurable (τd p τ n) := by
  refine measurable_of_Iic fun t => ?_
  have : τd p τ n ⁻¹' Iic t = τ ⁻¹' Iic ((⌊t / δ p n⌋₊ : ℝ≥0) * δ p n) := by
    ext ω; simp only [mem_preimage, mem_Iic]; exact τd_le_iff p τ n ω t
  rw [this]
  exact measurable_tau p st τ hτ measurableSet_Iic

lemma measurable_Zv_at (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ)
    (hZv : IsZVersion p st Iθ Zv) (σ : Ω → ℝ≥0) (hσ : Measurable σ) (hσT : ∀ ω, σ ω ≤ p.Tn) :
    Measurable (fun ω => Zv (σ ω) ω) := by
  have hu : Measurable (Function.uncurry fun (t : ℝ≥0) (ω : Ω) => Zv (min t p.Tn) ω) := by
    refine measurable_uncurry_of_continuous_of_measurable (m := ‹MeasurableSpace Ω›)
      (u := fun (t : ℝ≥0) (ω : Ω) => Zv (min t p.Tn) ω) ?_ ?_
    · intro ω
      exact (hZv.2.2.1 ω).comp_continuous (continuous_id.min continuous_const)
        (fun t => show min t p.Tn ≤ p.Tn from min_le_right _ _)
    · intro t
      exact (hZv.2.1 _).mono ((FS p st).le _) le_rfl
  have heq : (fun ω => Zv (σ ω) ω) =
      fun ω => (Function.uncurry fun (t : ℝ≥0) (ω : Ω) => Zv (min t p.Tn) ω) (σ ω, ω) := by
    funext ω; simp [Function.uncurry, min_eq_left (hσT ω)]
  rw [heq]
  exact hu.comp (hσ.prodMk measurable_id)

lemma measurable_ZT (p : Params) (st : Setting Ω) (Iθ : ℝ≥0 → Ω → ℝ)
    (hIto : IsItoIntegral p st (θ p st) Iθ) : Measurable (Z p st Iθ p.Tn) := by
  have h1 : Measurable (fun ω => ∫ s in Icc (0 : ℝ) p.Tn, θ p st s.toNNReal ω ^ 2) := by
    have h : Measurable (fun q : Ω × ℝ => θ p st q.2.toNNReal q.1 ^ 2) := by
      have hμ : Measurable (fun q : Ω × ℝ => st.μ q.2.toNNReal q.1) :=
        st.measurable_μ.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
      unfold θ
      fun_prop
    exact (h.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Icc (0 : ℝ) p.Tn))).measurable
  have h2 : Measurable (Iθ p.Tn) := (hIto.2.2.1 p.Tn).mono (st.𝓕.le p.Tn) le_rfl
  unfold Z
  fun_prop

/-- The discrete identity `E[Z_T g(τ_n)] = E[𝒵_{τ_n} g(τ_n)]` and `𝒵_{τ_n} = E[Z_T | F_{τ_n}]`. -/
lemma discrete_os (p : Params) (st : Setting Ω) (Iθ Zv : ℝ≥0 → Ω → ℝ) (hst : st.Standing p)
    (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ) (n : ℕ) :
    (fun ω => Zv (τd p τ n ω) ω) =ᵐ[st.P]
      st.P[Z p st Iθ p.Tn | (isStoppingTime_τd p st τ hτ n).measurableSpace] := by
  have hP : IsProbabilityMeasure st.P := hst.1
  set F := FS p st
  have hmart := martingale_condExp (Z p st Iθ p.Tn) F st.P
  have hτn := isStoppingTime_τd p st τ hτ n
  have hle : ∀ ω, (τd p τ n ω : WithTop ℝ≥0) ≤ (p.Tn : WithTop ℝ≥0) := fun ω =>
    WithTop.coe_le_coe.2 (τd_le_Tn p st τ hτ n ω)
  have hSV := hmart.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτn hle
    (countable_range_τd p τ n)
  have hGle : hτn.measurableSpace ≤ F p.Tn := hτn.measurableSpace_le_of_le_const hle
  have hcc := condExp_condExp_of_le (μ := st.P) (f := Z p st Iθ p.Tn) hGle (F.le p.Tn)
  have hall : ∀ᵐ ω ∂st.P, ∀ k : ℕ, (((k : ℝ≥0) * δ p n : ℝ≥0) : ℝ) ≤ p.T →
      Zv ((k : ℝ≥0) * δ p n) ω = st.P[Z p st Iθ p.Tn | F ((k : ℝ≥0) * δ p n)] ω := by
    rw [ae_all_iff]
    intro k
    by_cases hk : (((k : ℝ≥0) * δ p n : ℝ≥0) : ℝ) ≤ p.T
    · filter_upwards [hZv.1 _ hk] with ω hω
      intro _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hk
  filter_upwards [hall, hSV, hcc] with ω hω h1 h2
  rw [← h2, ← h1]
  show Zv (τd p τ n ω) ω = st.P[Z p st Iθ p.Tn | F (τd p τ n ω)] ω
  have hT : ((τd p τ n ω : ℝ≥0) : ℝ) ≤ p.T := by
    have := τd_le_Tn p st τ hτ n ω
    rw [← NNReal.coe_le_coe, Params.Tn, Real.coe_toNNReal _ p.T_pos.le] at this
    exact this
  exact hω ⌈τ ω / δ p n⌉₊ hT

end RetirePIos

open RetirePIos in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ)
    (h21 : Assumption21 p st Iθ) (hZv : IsZVersion p st Iθ Zv)
    (τ : Ω → ℝ≥0) (hτ : IsRetirementTime p st τ) (g : ℝ → ℝ) (hg : Continuous g) :
    Integrable (fun ω => Zv (τ ω) ω) st.P ∧
      ∫ ω, Z p st Iθ p.Tn ω * g (τ ω) ∂st.P = ∫ ω, Zv (τ ω) ω * g (τ ω) ∂st.P := by
  have hP : IsProbabilityMeasure st.P := hst.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
    (s := Icc (0 : ℝ) p.T)
  have hTn : ∀ t : ℝ≥0, t ≤ p.Tn → (t : ℝ) ∈ Icc (0 : ℝ) p.T := fun t ht => ⟨t.2, by
    have := NNReal.coe_le_coe.2 ht
    rwa [Params.Tn, Real.coe_toNNReal _ p.T_pos.le] at this⟩
  have hgn : ∀ n ω, ‖g (τd p τ n ω)‖ ≤ C := fun n ω => hC _ (hTn _ (τd_le_Tn p st τ hτ n ω))
  have hg0 : ∀ ω, ‖g (τ ω)‖ ≤ C := fun ω => hC _ (hTn _ (tau_le_Tn p st τ hτ ω))
  have hτm := measurable_tau p st τ hτ
  have hτdm := measurable_τd p st τ hτ
  set X : Ω → ℝ := fun ω => Zv (τ ω) ω with hXdef
  set Xn : ℕ → Ω → ℝ := fun n ω => Zv (τd p τ n ω) ω with hXndef
  have hXm : Measurable X := measurable_Zv_at p st Iθ Zv hZv τ hτm (tau_le_Tn p st τ hτ)
  have hZint : Integrable (Z p st Iθ p.Tn) st.P := by
    simpa only [min_self] using h21.2.integrable p.Tn
  have hZm := measurable_ZT p st Iθ hIto
  have hGle : ∀ n, (isStoppingTime_τd p st τ hτ n).measurableSpace ≤ ‹MeasurableSpace Ω› :=
    fun n => (isStoppingTime_τd p st τ hτ n).measurableSpace_le
  have hdos := discrete_os p st Iθ Zv hst hIto h21 hZv τ hτ
  have hUI : UniformIntegrable Xn 1 st.P :=
    (hZint.uniformIntegrable_condExp hGle).ae_eq fun n => (hdos n).symm
  have htends : ∀ ω, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω)) := by
    intro ω
    have hc := (hZv.2.2.1 ω).continuousWithinAt (show τ ω ∈ Iic p.Tn from tau_le_Tn p st τ hτ ω)
    have ht : Tendsto (fun n => τd p τ n ω) atTop (𝓝[Iic p.Tn] (τ ω)) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_τd p τ ω,
        Eventually.of_forall fun n => τd_le_Tn p st τ hτ n ω⟩
    exact hc.tendsto.comp ht
  have hXint : Integrable X st.P := hUI.integrable_of_ae_tendsto (Eventually.of_forall htends)
  refine ⟨hXint, ?_⟩
  have hgτn : ∀ n, Tendsto (fun k => g (τd p τ k n)) atTop (𝓝 (g (τ n))) := fun ω =>
    (hg.tendsto _).comp (NNReal.tendsto_coe.2 (tendsto_τd p τ ω))
  -- the discrete identities
  have hXnint : ∀ n, Integrable (Xn n) st.P := fun n => integrable_condExp.congr (hdos n).symm
  have hdisc : ∀ n, ∫ ω, Z p st Iθ p.Tn ω * g (τd p τ n ω) ∂st.P =
      ∫ ω, Xn n ω * g (τd p τ n ω) ∂st.P := by
    intro n
    have hτn := isStoppingTime_τd p st τ hτ n
    have hmτ : Measurable[hτn.measurableSpace] (τd p τ n) := by
      refine measurable_of_Iic fun t => ?_
      have : τd p τ n ⁻¹' Iic t = {ω | (τd p τ n ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} := by
        ext ω; simp only [mem_preimage, mem_Iic, mem_setOf_eq, WithTop.coe_le_coe]
      rw [this]; exact hτn.measurableSet_le' t
    have hgm : StronglyMeasurable[hτn.measurableSpace] (fun ω => g (τd p τ n ω)) :=
      (hg.measurable.comp (measurable_coe_nnreal_real.comp hmτ)).stronglyMeasurable
    have hint1 : Integrable (fun ω => Z p st Iθ p.Tn ω * g (τd p τ n ω)) st.P :=
      hZint.mul_bdd (c := C) (hg.measurable.comp (measurable_coe_nnreal_real.comp
        (hτdm n))).aestronglyMeasurable (Eventually.of_forall (hgn n))
    have hpull := condExp_mul_of_stronglyMeasurable_right (m := hτn.measurableSpace) (μ := st.P)
      (f := Z p st Iθ p.Tn) hgm hint1 hZint
    rw [← integral_condExp (hGle n) (f := fun ω => Z p st Iθ p.Tn ω * g (τd p τ n ω))]
    refine integral_congr_ae ?_
    filter_upwards [hpull, hdos n] with ω h1 h2
    rw [show (fun ω => Z p st Iθ p.Tn ω * g (τd p τ n ω)) =
      Z p st Iθ p.Tn * fun ω => g (τd p τ n ω) from rfl, h1]
    simp only [Pi.mul_apply, hXndef, h2]
  -- limit of the left side
  have hL : Tendsto (fun n => ∫ ω, Z p st Iθ p.Tn ω * g (τd p τ n ω) ∂st.P) atTop
      (𝓝 (∫ ω, Z p st Iθ p.Tn ω * g (τ ω) ∂st.P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => C * ‖Z p st Iθ p.Tn ω‖)
      (fun n => (hZm.mul (hg.measurable.comp (measurable_coe_nnreal_real.comp
        (hτdm n)))).aestronglyMeasurable) (hZint.norm.const_mul C) ?_ ?_
    · intro n
      refine Eventually.of_forall fun ω => ?_
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hgn n ω) (norm_nonneg _)
    · exact Eventually.of_forall fun ω => tendsto_const_nhds.mul (hgτn ω)
  -- limit of the right side
  have hR : Tendsto (fun n => ∫ ω, Xn n ω * g (τd p τ n ω) ∂st.P) atTop
      (𝓝 (∫ ω, X ω * g (τ ω) ∂st.P)) := by
    have hL1 := tendsto_Lp_finite_of_tendsto_ae (p := 1) le_rfl ENNReal.one_ne_top hUI.1
      (memLp_one_iff_integrable.2 hXint) hUI.2.1 (Eventually.of_forall htends)
    have h1 : Tendsto (fun n => ENNReal.ofReal C * eLpNorm (Xn n - X) 1 st.P) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hL1 (Or.inr ENNReal.ofReal_ne_top)
    have h2 : Tendsto (fun n => ∫⁻ ω, ‖X ω‖ₑ * ‖g (τd p τ n ω) - g (τ ω)‖ₑ ∂st.P) atTop
        (𝓝 0) := by
      have := tendsto_lintegral_of_dominated_convergence (μ := st.P)
        (F := fun n ω => ‖X ω‖ₑ * ‖g (τd p τ n ω) - g (τ ω)‖ₑ) (f := fun _ => 0)
        (fun ω => ‖X ω‖ₑ * ENNReal.ofReal (2 * C)) ?_ ?_ ?_ ?_
      · simpa using this
      · intro n
        exact hXm.enorm.mul ((hg.measurable.comp (measurable_coe_nnreal_real.comp (hτdm n))).sub
          (hg.measurable.comp (measurable_coe_nnreal_real.comp hτm))).enorm
      · intro n
        refine Eventually.of_forall fun ω => ?_
        show ‖X ω‖ₑ * ‖g (τd p τ n ω) - g (τ ω)‖ₑ ≤ ‖X ω‖ₑ * ENNReal.ofReal (2 * C)
        gcongr
        rw [← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖g (τd p τ n ω) - g (τ ω)‖ ≤ ‖g (τd p τ n ω)‖ + ‖g (τ ω)‖ := norm_sub_le _ _
          _ ≤ C + C := add_le_add (hgn n ω) (hg0 ω)
          _ = 2 * C := by ring
      · rw [lintegral_mul_const _ hXm.enorm]
        exact ENNReal.mul_ne_top hXint.2.ne ENNReal.ofReal_ne_top
      · refine Eventually.of_forall fun ω => ?_
        have : Tendsto (fun n => ‖g (τd p τ n ω) - g (τ ω)‖ₑ) atTop (𝓝 0) := by
          have h := ((hgτn ω).sub_const (g (τ ω)))
          rw [sub_self] at h
          have h' := (continuous_enorm.tendsto (0 : ℝ)).comp h
          simpa [Function.comp_def] using h'
        simpa using ENNReal.Tendsto.const_mul this (Or.inr enorm_ne_top)
    refine tendsto_integral_of_L1 (fun ω => X ω * g (τ ω)) (hXm.mul (hg.measurable.comp
      (measurable_coe_nnreal_real.comp hτm))).aestronglyMeasurable
      (Eventually.of_forall fun n => (hXnint n).mul_bdd (c := C)
        (hg.measurable.comp (measurable_coe_nnreal_real.comp (hτdm n))).aestronglyMeasurable
        (Eventually.of_forall (hgn n))) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using h1.add h2) (fun n => bot_le) (fun n => ?_)
    rw [eLpNorm_one_eq_lintegral_enorm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_add_left' ?_]
    · refine lintegral_mono fun ω => ?_
      have heq : Xn n ω * g (τd p τ n ω) - X ω * g (τ ω) =
          (Xn n ω - X ω) * g (τd p τ n ω) + X ω * (g (τd p τ n ω) - g (τ ω)) := by ring
      rw [heq]
      refine (enorm_add_le _ _).trans ?_
      rw [enorm_mul, enorm_mul, mul_comm (‖Xn n ω - X ω‖ₑ)]
      gcongr
      · rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (hgn n ω)
      · simp
    · exact (((hXnint n).aemeasurable.sub hXm.aemeasurable).enorm.const_mul _)
  have hfun : (fun n => ∫ ω, Z p st Iθ p.Tn ω * g (τd p τ n ω) ∂st.P) =
      fun n => ∫ ω, Xn n ω * g (τd p τ n ω) ∂st.P := funext hdisc
  rw [hfun] at hL
  exact tendsto_nhds_unique hL hR
