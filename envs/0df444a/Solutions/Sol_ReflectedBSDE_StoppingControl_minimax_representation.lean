-- Prove2me | solution 1 for ReflectedBSDE.StoppingControl.minimax_representation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:02:22.514466+00:00
-- url     : https://prove2.me/submissions/1e452e3c-0995-44db-b671-20a8eaf698b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ReflectedBSDE_StoppingControl_comparison
import Theorems.Thm_ReflectedBSDE_StoppingControl_affine_representation
import Theorems.Thm_ReflectedBSDE_StoppingControl_optimal_control_exists
import Theorems.Thm_ReflectedBSDE_StoppingControl_payoff_integrable
import Theorems.Thm_ReflectedBSDE_StoppingControl_stopping_lower_bound
import Theorems.Thm_ReflectedBSDE_StoppingControl_inner_essInf_exists

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace RBSDE2Red

open ReflectedBSDE.StoppingControl

/-! ### Generic measurability helpers (an arbitrary measurable space on `Ω`) -/

section Gen

variable {Ω : Type*} [MeasurableSpace Ω]

lemma toNN_min {r : ℝ} {i : ℝ≥0} (hr : r ≤ i) : min r.toNNReal i = r.toNNReal :=
  min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hr)

lemma meas_time (i : ℝ≥0) : Measurable fun p : Set.Iic i × Ω => (p.1 : ℝ≥0) :=
  measurable_subtype_coe.comp measurable_fst

lemma G2 {β : Type*} [MeasurableSpace β] (i : ℝ≥0) {u : ℝ≥0 → Ω → β}
    (hu : Measurable fun p : Set.Iic i × Ω => u p.1 p.2) :
    Measurable fun p : ℝ × Ω => u (min p.1.toNNReal i) p.2 := by
  have hφ : Measurable fun p : ℝ × Ω =>
      ((⟨min p.1.toNNReal i, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Set.Iic i), p.2) :=
    ((measurable_fst.real_toNNReal.min measurable_const).subtype_mk).prodMk measurable_snd
  exact hu.comp hφ

lemma G2b {β : Type*} [MeasurableSpace β] (i : ℝ≥0) {u : ℝ≥0 → Ω → β}
    (hu : Measurable fun p : Set.Iic i × Ω => u p.1 p.2) (ω : Ω) :
    Measurable fun r : ℝ => u (min r.toNNReal i) ω :=
  (G2 i hu).comp measurable_prodMk_right

lemma G4 (i : ℝ≥0) {u : ℝ≥0 → Ω → ℝ}
    (hu : Measurable fun p : Set.Iic i × Ω => u p.1 p.2) :
    StronglyMeasurable fun ω => ∫ r in Set.Icc (0 : ℝ) i, u r.toNNReal ω := by
  have h3 := (G2 i hu).stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Set.Icc (0 : ℝ) i))
  convert h3 using 1
  funext ω
  exact setIntegral_congr_fun measurableSet_Icc fun r hr => by simp [toNN_min hr.2]

lemma G5 (i : ℝ≥0) {u : ℝ≥0 → Ω → ℝ≥0∞}
    (hu : Measurable fun p : Set.Iic i × Ω => u p.1 p.2) :
    Measurable fun ω => ∫⁻ r in Set.Icc (0 : ℝ) i, u (min r.toNNReal i) ω :=
  (G2 i hu).lintegral_prod_left'

lemma G6 (i : ℝ≥0) {u : ℝ≥0 → Ω → ℝ}
    (hu : Measurable fun p : Set.Iic i × Ω => u p.1 p.2) (ω : Ω) :
    AEStronglyMeasurable (fun r : ℝ => u r.toNNReal ω) (volume.restrict (Set.Icc (0 : ℝ) i)) := by
  refine (G2b i hu ω).aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  simp [toNN_min hr.2]

lemma meas_dot {X : Type*} [MeasurableSpace X] {d : ℕ} {g : X → Fin d → ℝ} (hg : Measurable g)
    (z : Fin d → ℝ) : Measurable fun x => dot (g x) z := by
  unfold dot
  exact Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp hg).mul_const _

lemma conj_meas {X : Type*} [MeasurableSpace X] {d : ℕ} (F : X → ℝ → (Fin d → ℝ) → ℝ)
    (β : X → ℝ) (γ : X → Fin d → ℝ) (τ : X → ℝ≥0) (T : ℝ≥0) (hτ : Measurable τ)
    (hF : ∀ y z, Measurable fun x => F x y z) (hβ : Measurable β) (hγ : Measurable γ)
    (hcont : ∀ x, τ x ≤ T → Continuous fun p : ℝ × (Fin d → ℝ) => F x p.1 p.2) :
    Measurable fun x => if τ x ≤ T then
      (⨆ (y : ℝ) (z : Fin d → ℝ), ((F x y z - β x * y - dot (γ x) z : ℝ) : EReal)) else 0 := by
  set D := TopologicalSpace.denseSeq (ℝ × (Fin d → ℝ))
  have key : ∀ x, τ x ≤ T →
      (⨆ (y : ℝ) (z : Fin d → ℝ), ((F x y z - β x * y - dot (γ x) z : ℝ) : EReal)) =
        ⨆ n : ℕ, ((F x (D n).1 (D n).2 - β x * (D n).1 - dot (γ x) (D n).2 : ℝ) : EReal) := by
    intro x hx
    set g : ℝ × (Fin d → ℝ) → ℝ := fun p => F x p.1 p.2 - β x * p.1 - dot (γ x) p.2 with hg_def
    have hg : Continuous g := by
      refine ((hcont x hx).sub (continuous_const.mul continuous_fst)).sub ?_
      unfold dot
      exact continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp
        continuous_snd)
    apply le_antisymm
    · refine iSup₂_le fun y z => ?_
      have := (TopologicalSpace.denseRange_denseSeq (ℝ × (Fin d → ℝ))).induction_on
        (p := fun p => ((g p : ℝ) : EReal) ≤ ⨆ n : ℕ, ((g (D n) : ℝ) : EReal)) (y, z)
        (isClosed_le (continuous_coe_real_ereal.comp hg) continuous_const)
        (fun n => le_iSup (fun n : ℕ => ((g (D n) : ℝ) : EReal)) n)
      exact this
    · exact iSup_le fun n => le_iSup₂_of_le (D n).1 (D n).2 le_rfl
  have heq : (fun x => if τ x ≤ T then
      (⨆ (y : ℝ) (z : Fin d → ℝ), ((F x y z - β x * y - dot (γ x) z : ℝ) : EReal)) else 0) =
      fun x => if τ x ≤ T then
        (⨆ n : ℕ, ((F x (D n).1 (D n).2 - β x * (D n).1 - dot (γ x) (D n).2 : ℝ) : EReal))
        else 0 := by
    funext x
    split_ifs with hx
    · exact key x hx
    · rfl
  rw [heq]
  refine Measurable.ite (measurableSet_le hτ measurable_const) ?_ measurable_const
  refine Measurable.iSup fun n => ?_
  exact (((hF _ _).sub (hβ.mul_const _)).sub (meas_dot hγ _)).coe_real_ereal

lemma sq_sum_meas {X : Type*} [MeasurableSpace X] {d : ℕ} {g : X → Fin d → ℝ}
    (hg : Measurable g) : Measurable fun x => ∑ j, g x j ^ 2 :=
  Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp hg).pow_const 2

omit [MeasurableSpace Ω] in
lemma G7 {m m0 : MeasurableSpace Ω} (hm : m ≤ m0) (μ : Measure[m0] Ω) (i : ℝ≥0)
    (u : ℝ≥0 → Ω → ℝ≥0∞)
    (hu : Measurable[Subtype.instMeasurableSpace.prod m] fun p : Set.Iic i × Ω => u p.1 p.2)
    (hfin : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) i, u r.toNNReal ω) ∂μ < ⊤) :
    ∀ᵐ ω ∂μ, ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) i)), u r.toNNReal ω < ⊤ := by
  have hint_eq : ∀ ω, ∫⁻ r in Set.Icc (0 : ℝ) i, u r.toNNReal ω =
      ∫⁻ r in Set.Icc (0 : ℝ) i, u (min r.toNNReal i) ω := fun ω =>
    setLIntegral_congr_fun measurableSet_Icc fun r hr => by simp [toNN_min hr.2]
  have hG : Measurable[m0] fun ω => ∫⁻ r in Set.Icc (0 : ℝ) i, u (min r.toNNReal i) ω :=
    (@G5 Ω m i u hu).mono hm le_rfl
  have hfin' : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) i, u (min r.toNNReal i) ω) ∂μ ≠ ⊤ := by
    simp_rw [← hint_eq]; exact hfin.ne
  filter_upwards [ae_lt_top hG hfin'] with ω hω
  have := ae_lt_top (@G2b Ω m _ _ i u hu ω) hω.ne
  filter_upwards [this, ae_restrict_mem measurableSet_Icc] with r hr hr'
  rwa [toNN_min hr'.2] at hr

end Gen

lemma measurable_EReal_abs : Measurable EReal.abs := by
  have : EReal.abs = fun x => if x = ⊤ ∨ x = ⊥ then ⊤ else ENNReal.ofReal |x.toReal| := by
    funext x
    induction x <;> simp [EReal.abs_def]
  rw [this]
  exact Measurable.ite ((measurableSet_singleton _).union (measurableSet_singleton _))
    measurable_const (ENNReal.measurable_ofReal.comp measurable_ereal_toReal.abs)

lemma enorm_toReal_le (x : EReal) : ‖x.toReal‖ₑ ≤ EReal.abs x := by
  induction x
  · simp
  · simp [EReal.abs_def, Real.enorm_eq_ofReal_abs]
  · simp

lemma abs_coord_le {d : ℕ} (γ : Fin d → ℝ) (j : Fin d) : |γ j| ≤ eucNorm γ :=
  Real.abs_le_sqrt (Finset.single_le_sum (fun k _ => sq_nonneg (γ k)) (Finset.mem_univ j))

lemma abs_dot_le {d : ℕ} (γ z : Fin d → ℝ) (C : ℝ) (hC : eucNorm γ ≤ C) :
    |dot γ z| ≤ C * ∑ j, |z j| := by
  unfold dot
  calc |∑ j, γ j * z j| ≤ ∑ j, |γ j * z j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, C * |z j| := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right ((abs_coord_le γ j).trans hC) (abs_nonneg _)
    _ = C * ∑ j, |z j| := by rw [Finset.mul_sum]

lemma ennsq (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ 2 ≤ (b + b) ^ 2 := by gcongr
      _ = 4 * b ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := by gcongr; exact le_add_self
  · calc (a + b) ^ 2 ≤ (a + a) ^ 2 := by gcongr
      _ = 4 * a ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := by gcongr; exact le_self_add

lemma split_Icc (h : ℝ → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hint : IntegrableOn h (Set.Icc a c)) :
    ∫ x in Set.Icc a c, h x = (∫ x in Set.Icc a b, h x) + ∫ x in Set.Icc b c, h x := by
  have hU : Set.Icc a c = Set.Icc a b ∪ Set.Ioc b c := (Set.Icc_union_Ioc_eq_Icc hab hbc).symm
  rw [hU, setIntegral_union (Set.disjoint_left.mpr fun x hx1 hx2 => absurd hx1.2
      (not_le.mpr hx2.1)) measurableSet_Ioc
      (hint.mono_set (Set.Icc_subset_Icc_right hbc))
      (hint.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left hab)))]
  rw [integral_Icc_eq_integral_Ioc (μ := (volume : Measure ℝ)) (f := h) (x := b) (y := c)]

/-! ### Objects attached to a control -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-- `F(t, β_t, γ_t)` on `[0, T]`, `0` afterwards. -/
noncomputable def eps (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (c : Control Ω d) :
    ℝ≥0 → Ω → EReal :=
  fun t ω => if t ≤ T then conj f ω t (c.1 t ω) (c.2 t ω) else 0

noncomputable def del (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (c : Control Ω d) :
    ℝ≥0 → Ω → ℝ :=
  fun t ω => (eps T f c t ω).toReal

noncomputable def ftil (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (c : Control Ω d) :
    ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ :=
  fun t ω y z => del T f c t ω + c.1 t ω * y + dot (c.2 t ω) z

lemma eps_prog {𝓕 : Filtration ℝ≥0 mΩ} (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (c : Control Ω d)
    (hfprog : ∀ y z, IsStronglyProgressive 𝓕 (fun t ω => f t ω y z))
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (hc1 : IsStronglyProgressive 𝓕 c.1) (hc2 : IsStronglyProgressive 𝓕 c.2) (i : ℝ≥0) :
    Measurable[Subtype.instMeasurableSpace.prod (𝓕 i)]
      (fun p : Set.Iic i × Ω => eps T f c p.1 p.2) := by
  exact @conj_meas (Set.Iic i × Ω) (Subtype.instMeasurableSpace.prod (𝓕 i)) d
    (fun p y z => f p.1 p.2 y z) (fun p => c.1 p.1 p.2) (fun p => c.2 p.1 p.2)
    (fun p => (p.1 : ℝ≥0)) T (@meas_time Ω (𝓕 i) i)
    (fun y z => (hfprog y z i).measurable) (hc1 i).measurable (hc2 i).measurable
    (fun p hp => continuousOn_univ.mp ((hconc p.2 p.1 hp).continuousOn isOpen_univ))

lemma del_L2F {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} (T : ℝ≥0)
    (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (c : Control Ω d)
    (hfprog : ∀ y z, IsStronglyProgressive 𝓕 (fun t ω => f t ω y z))
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (hc : c ∈ admissible 𝓕 P T f) : Peng1990.SMP.L2F 𝓕 P T (del T f c) := by
  obtain ⟨hc1, hc2, -, hint⟩ := hc
  refine ⟨fun i => (measurable_ereal_toReal.comp (eps_prog T f c hfprog hconc hc1 hc2 i)).stronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hint
  refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
  have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hs.2
  simp only [del, eps, if_pos hsT]
  gcongr
  exact enorm_toReal_le _

lemma ftil_standing {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} [IsProbabilityMeasure P]
    (T : ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (c : Control Ω d) (hdata : StandingData 𝓕 P T ξ f S)
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (hc : c ∈ admissible 𝓕 P T f) : StandingData 𝓕 P T ξ (ftil T f c) S := by
  have hfprog : ∀ y z, IsStronglyProgressive 𝓕 (fun t ω => f t ω y z) :=
    fun y z => (hdata.coeff_mem y z).1
  have hδ := del_L2F T f c hfprog hconc hc
  obtain ⟨hc1, hc2, ⟨C, hC⟩, -⟩ := hc
  refine ⟨hdata.terminal, fun y z => ?_, hdata.obstacle_cont, hdata.obstacle_prog,
    hdata.obstacle_sq, hdata.obstacle_le_terminal⟩
  refine ⟨fun i => ((hδ.1 i).add ((hc1 i).mul_const y)).add
    (@meas_dot _ (Subtype.instMeasurableSpace.prod (𝓕 i)) _ _ (hc2 i).measurable z).stronglyMeasurable, ?_⟩
  set M : ℝ≥0∞ := ENNReal.ofReal (C * |y| + C * ∑ j, |z j|) with hM
  have hpt : ∀ ω, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖ftil T f c s.toNNReal ω y z‖ₑ ^ 2 ≤ 4 * (‖del T f c s.toNNReal ω‖ₑ ^ 2 + M ^ 2) := by
    intro ω s hs
    have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hs.2
    have hb := hC _ hsT ω
    have hβ : |c.1 s.toNNReal ω| ≤ C := by
      have := Real.sqrt_nonneg (∑ j, c.2 s.toNNReal ω j ^ 2)
      unfold eucNorm at hb; linarith
    have hγ : eucNorm (c.2 s.toNNReal ω) ≤ C := by
      have := abs_nonneg (c.1 s.toNNReal ω); linarith
    have hlin : ‖c.1 s.toNNReal ω * y + dot (c.2 s.toNNReal ω) z‖ₑ ≤ M := by
      rw [Real.enorm_eq_ofReal_abs, hM]
      apply ENNReal.ofReal_le_ofReal
      calc |c.1 s.toNNReal ω * y + dot (c.2 s.toNNReal ω) z|
          ≤ |c.1 s.toNNReal ω * y| + |dot (c.2 s.toNNReal ω) z| := abs_add_le _ _
        _ ≤ C * |y| + C * ∑ j, |z j| := by
          gcongr
          · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hβ (abs_nonneg _)
          · exact abs_dot_le _ _ C hγ
    have h1 : ‖ftil T f c s.toNNReal ω y z‖ₑ ≤ ‖del T f c s.toNNReal ω‖ₑ + M := by
      unfold ftil
      rw [add_assoc]
      exact (enorm_add_le _ _).trans (add_le_add le_rfl hlin)
    calc ‖ftil T f c s.toNNReal ω y z‖ₑ ^ 2 ≤ (‖del T f c s.toNNReal ω‖ₑ + M) ^ 2 := by gcongr
      _ ≤ 4 * (‖del T f c s.toNNReal ω‖ₑ ^ 2 + M ^ 2) := ennsq _ _
  have hinner : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ‖ftil T f c s.toNNReal ω y z‖ₑ ^ 2 ≤
      4 * ((∫⁻ s in Set.Icc (0 : ℝ) T, ‖del T f c s.toNNReal ω‖ₑ ^ 2) +
        M ^ 2 * volume (Set.Icc (0 : ℝ) T)) := by
    intro ω
    calc ∫⁻ s in Set.Icc (0 : ℝ) T, ‖ftil T f c s.toNNReal ω y z‖ₑ ^ 2
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, 4 * (‖del T f c s.toNNReal ω‖ₑ ^ 2 + M ^ 2) :=
          setLIntegral_mono' measurableSet_Icc (hpt ω)
      _ = _ := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_right _ measurable_const,
            setLIntegral_const]
  have hvol : volume (Set.Icc (0 : ℝ) T) < ⊤ := measure_Icc_lt_top
  calc ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ‖ftil T f c s.toNNReal ω y z‖ₑ ^ 2) ∂P
      ≤ ∫⁻ ω, 4 * ((∫⁻ s in Set.Icc (0 : ℝ) T, ‖del T f c s.toNNReal ω‖ₑ ^ 2) +
        M ^ 2 * volume (Set.Icc (0 : ℝ) T)) ∂P := lintegral_mono hinner
    _ = 4 * ((∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ‖del T f c s.toNNReal ω‖ₑ ^ 2) ∂P) +
        M ^ 2 * volume (Set.Icc (0 : ℝ) T)) := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_right _ measurable_const,
            lintegral_const, measure_univ, mul_one]
    _ < ⊤ := by
          refine ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.mpr ⟨hδ.2, ?_⟩)
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hvol

lemma sol_congr {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {T : ℝ≥0}
    {B : ℝ≥0 → Ω → Fin d → ℝ} {ξ : Ω → ℝ} {g g' : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ}
    {S Y : ℝ≥0 → Ω → ℝ} {Z : ℝ≥0 → Ω → Fin d → ℝ} {K : ℝ≥0 → Ω → ℝ}
    (hgg : ∀ t ≤ T, ∀ ω y z, g t ω y z = g' t ω y z)
    (h : IsRBSDESolution 𝓕 P T B ξ g S Y Z K) : IsRBSDESolution 𝓕 P T B ξ g' S Y Z K := by
  obtain ⟨J, hJ, heq⟩ := h.eqn
  refine { h with eqn := ⟨J, hJ, fun t ht => (heq t ht).mono fun ω hω => ?_⟩ }
  have hE : Set.EqOn (fun s : ℝ => g s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω))
      (fun s : ℝ => g' s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω)) (Set.Icc (t : ℝ) T) :=
    fun s hs => hgg _ (Real.toNNReal_le_iff_le_coe.mpr hs.2) _ _ _
  refine ⟨hω.1.congr_fun hE measurableSet_Icc, ?_⟩
  rw [hω.2, setIntegral_congr_fun measurableSet_Icc hE]

omit mΩ in
lemma ftil_eq (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (c : Control Ω d) :
    ∀ t ≤ T, ∀ ω y z, affineCoeff f c t ω y z = ftil T f c t ω y z := by
  intro t ht ω y z
  simp [affineCoeff, ftil, del, eps, ht]

lemma conj_lt_top_ae {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} (T : ℝ≥0)
    (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (c : Control Ω d)
    (hfprog : ∀ y z, IsStronglyProgressive 𝓕 (fun t ω => f t ω y z))
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (hc : c ∈ admissible 𝓕 P T f) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      conj f ω s.toNNReal (c.1 s.toNNReal ω) (c.2 s.toNNReal ω) < ⊤ := by
  obtain ⟨hc1, hc2, -, hint⟩ := hc
  have hH : Measurable[Subtype.instMeasurableSpace.prod (𝓕 T)]
      (fun p : Set.Iic T × Ω => EReal.abs (eps T f c p.1 p.2) ^ 2) :=
    (measurable_EReal_abs.comp (eps_prog T f c hfprog hconc hc1 hc2 T)).pow_const 2
  have hE : ∀ ω, ∫⁻ r in Set.Icc (0 : ℝ) T, EReal.abs (eps T f c r.toNNReal ω) ^ 2 =
      ∫⁻ r in Set.Icc (0 : ℝ) T,
        EReal.abs (conj f ω r.toNNReal (c.1 r.toNNReal ω) (c.2 r.toNNReal ω)) ^ 2 := by
    intro ω
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hrT : r.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hr.2
    simp only [eps, if_pos hrT]
  have hfin : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, EReal.abs (eps T f c r.toNNReal ω) ^ 2) ∂P
      < ⊤ := by simp_rw [hE]; exact hint
  have := G7 (𝓕.le T) P T (fun t ω => EReal.abs (eps T f c t ω) ^ 2) hH hfin
  filter_upwards [this] with ω hω
  filter_upwards [hω, ae_restrict_mem measurableSet_Icc] with r hr hr'
  have hrT : r.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hr'.2
  simp only [eps, if_pos hrT] at hr
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  rw [htop] at hr
  simp at hr

lemma f_le_ftil {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} (T : ℝ≥0)
    (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (c : Control Ω d)
    (hfprog : ∀ y z, IsStronglyProgressive 𝓕 (fun t ω => f t ω y z))
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (hc : c ∈ admissible 𝓕 P T f) :
    ∀ (y : ℝ) (z : Fin d → ℝ), ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      f s.toNNReal ω y z ≤ ftil T f c s.toNNReal ω y z := by
  intro y z
  filter_upwards [conj_lt_top_ae T f c hfprog hconc hc] with ω hω
  filter_upwards [hω, ae_restrict_mem measurableSet_Icc] with s hs hs'
  have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hs'.2
  simp only [ftil, del, eps, if_pos hsT]
  set x := conj f ω s.toNNReal (c.1 s.toNNReal ω) (c.2 s.toNNReal ω) with hx
  have hge : ((f s.toNNReal ω y z - c.1 s.toNNReal ω * y - dot (c.2 s.toNNReal ω) z : ℝ) : EReal)
      ≤ x := by
    rw [hx]; unfold conj
    exact le_iSup₂_of_le (f := fun (y : ℝ) (z : Fin d → ℝ) =>
      ((f s.toNNReal ω y z - c.1 s.toNNReal ω * y - dot (c.2 s.toNNReal ω) z : ℝ) : EReal))
      y z le_rfl
  have hbot : x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hge
  have hx' : x = ((x.toReal : ℝ) : EReal) := (EReal.coe_toReal hs.ne hbot).symm
  rw [hx'] at hge
  have := EReal.coe_le_coe_iff.mp hge
  linarith

lemma Gamma_meas {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {T : ℝ≥0}
    {B : ℝ≥0 → Ω → Fin d → ℝ} (β : ℝ≥0 → Ω → ℝ) (γ : ℝ≥0 → Ω → Fin d → ℝ)
    (J : Fin d → ℝ≥0 → Ω → ℝ)
    (hβ : IsStronglyProgressive 𝓕 β) (hγ : IsStronglyProgressive 𝓕 γ)
    (hJ : IsContItoIntegral 𝓕 P T B γ J) (t : ℝ≥0) :
    StronglyMeasurable[𝓕 t] (linGamma β γ J 0 t) := by
  unfold linGamma
  have h1 : StronglyMeasurable[𝓕 t] fun ω => ∫ r in Set.Icc (0 : ℝ) t, β r.toNNReal ω :=
    @G4 Ω (𝓕 t) t β (hβ t).measurable
  have hsq : Measurable[Subtype.instMeasurableSpace.prod (𝓕 t)]
      (fun p : Set.Iic t × Ω => ∑ j, γ p.1 p.2 j ^ 2) :=
    Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp (hγ t).measurable).pow_const 2
  have h2 : StronglyMeasurable[𝓕 t] fun ω => ∫ r in Set.Icc (0 : ℝ) t, ∑ j, γ r.toNNReal ω j ^ 2 :=
    @G4 Ω (𝓕 t) t (fun s ω => ∑ j, γ s ω j ^ 2) hsq
  have h3 : StronglyMeasurable[𝓕 t] fun ω => ∑ j, (J j t ω - J j 0 ω) := by
    refine Finset.stronglyMeasurable_fun_sum (f := fun j ω => J j t ω - J j 0 ω) _ fun j _ => ?_
    exact ((hJ j).1.2.1 t).sub (((hJ j).1.2.1 0).mono (𝓕.mono (zero_le (a := t))))
  have h4 : StronglyMeasurable[𝓕 t] fun ω => (∫ r in Set.Icc (0 : ℝ) t, β r.toNNReal ω) +
      ∑ j, (J j t ω - J j 0 ω) - 1 / 2 * ∫ r in Set.Icc (0 : ℝ) t, ∑ j, γ r.toNNReal ω j ^ 2 :=
    (StronglyMeasurable.add h1 h3).sub (h2.const_mul _)
  have h5 := (Real.continuous_exp.comp_stronglyMeasurable h4)
  simpa [NNReal.coe_zero] using h5

lemma sec_int {𝓕 : Filtration ℝ≥0 mΩ} {T : ℝ≥0} (u : ℝ≥0 → Ω → ℝ)
    (hu : IsStronglyProgressive 𝓕 u) (C : ℝ) (hC : ∀ t ≤ T, ∀ ω, |u t ω| ≤ C) (ω : Ω) :
    IntegrableOn (fun r : ℝ => u r.toNNReal ω) (Set.Icc (0 : ℝ) T) := by
  refine IntegrableOn.of_bound measure_Icc_lt_top
    (@G6 Ω (𝓕 T) T u (hu T).measurable ω) C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact hC _ (Real.toNNReal_le_iff_le_coe.mpr hr.2) ω

omit mΩ in
lemma Gamma_split (β : ℝ≥0 → Ω → ℝ) (γ : ℝ≥0 → Ω → Fin d → ℝ) (J : Fin d → ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (ω : Ω)
    (hβi : IntegrableOn (fun r : ℝ => β r.toNNReal ω) (Set.Icc (0 : ℝ) T))
    (hγi : IntegrableOn (fun r : ℝ => ∑ j, γ r.toNNReal ω j ^ 2) (Set.Icc (0 : ℝ) T))
    {t s : ℝ≥0} (hts : t ≤ s) (hs : s ≤ T) :
    linGamma β γ J 0 s ω = linGamma β γ J 0 t ω * linGamma β γ J t s ω := by
  unfold linGamma
  rw [← Real.exp_add]
  congr 1
  have hsub : Set.Icc ((0 : ℝ≥0) : ℝ) s ⊆ Set.Icc (0 : ℝ) T :=
    Set.Icc_subset_Icc (by simp) (by exact_mod_cast hs)
  rw [split_Icc _ (b := t) (by simp) (by exact_mod_cast hts)
      (hβi.mono_set hsub),
    split_Icc _ (b := t) (by simp) (by exact_mod_cast hts)
      (hγi.mono_set hsub)]
  have : ∑ j, (J j s ω - J j 0 ω) = ∑ j, (J j t ω - J j 0 ω) + ∑ j, (J j s ω - J j t ω) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]; ring

lemma esssup_unique {Ω : Type*} {m' : MeasurableSpace Ω} [m0 : MeasurableSpace Ω] {μ : Measure Ω}
    {𝒳 : Set (Ω → ℝ)} {g1 g2 : Ω → ℝ} (h1 : IsEssSup μ m' 𝒳 g1) (h2 : IsEssSup μ m' 𝒳 g2) :
    g1 =ᵐ[μ] g2 :=
  (h1.2.2 g2 h2.1 h2.2.1).antisymm (h2.2.2 g1 h1.1 h1.2.1)

lemma esssup_scale {Ω : Type*} {m' : MeasurableSpace Ω} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} {V : Set (Ω → ℝ≥0)} (A Φ : (Ω → ℝ≥0) → Ω → ℝ) {G y : Ω → ℝ}
    (hGpos : ∀ ω, 0 < G ω) (hGm : StronglyMeasurable[m'] G) (hym : StronglyMeasurable[m'] y)
    (hAΦ : ∀ v ∈ V, A v =ᵐ[μ] fun ω => G ω * Φ v ω)
    (h : IsEssSup μ m' {X | ∃ v ∈ V, X = A v} (fun ω => G ω * y ω)) :
    IsEssSup μ m' {X | ∃ v ∈ V, X = Φ v} y := by
  refine ⟨hym, ?_, ?_⟩
  · rintro X ⟨v, hv, rfl⟩
    filter_upwards [h.2.1 _ ⟨v, hv, rfl⟩, hAΦ v hv] with ω h1 h2
    rw [h2] at h1
    exact le_of_mul_le_mul_left h1 (hGpos ω)
  · intro g' hg' hle
    have h2 := h.2.2 (fun ω => G ω * g' ω) (hGm.mul hg') (by
      rintro X ⟨v, hv, rfl⟩
      filter_upwards [hle _ ⟨v, hv, rfl⟩, hAΦ v hv] with ω h1 h2
      rw [h2]; exact mul_le_mul_of_nonneg_left h1 (hGpos ω).le)
    filter_upwards [h2] with ω h
    exact le_of_mul_le_mul_left h (hGpos ω)

omit mΩ in
lemma payoff_eq (T : ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (S : ℝ≥0 → Ω → ℝ) (c : Control Ω d) (J : Fin d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (v : Ω → ℝ≥0) (hv : ∀ ω, t ≤ v ω ∧ v ω ≤ T)
    (hsplit : ∀ ω, ∀ s : ℝ≥0, t ≤ s → s ≤ T →
      linGamma c.1 c.2 J 0 s ω = linGamma c.1 c.2 J 0 t ω * linGamma c.1 c.2 J t s ω) :
    affinePayoff T ξ S (del T f c) c.1 c.2 J t v =
      fun ω => linGamma c.1 c.2 J 0 t ω * payoff T ξ f S c J t v ω := by
  funext ω
  unfold affinePayoff payoff
  have hint : ∫ s in Set.Icc (t : ℝ) (v ω), linGamma c.1 c.2 J 0 s.toNNReal ω *
        del T f c s.toNNReal ω =
      linGamma c.1 c.2 J 0 t ω * ∫ s in Set.Icc (t : ℝ) (v ω), linGamma c.1 c.2 J t s.toNNReal ω *
        (conj f ω s.toNNReal (c.1 s.toNNReal ω) (c.2 s.toNNReal ω)).toReal := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    have hs0 : 0 ≤ s := le_trans t.2 hs.1
    have h1 : t ≤ s.toNNReal := (Real.le_toNNReal_iff_coe_le hs0).mpr hs.1
    have h2 : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr
      (hs.2.trans (by exact_mod_cast (hv ω).2))
    simp only [del, eps, if_pos h2]
    rw [hsplit ω _ h1 h2]; ring
  rw [hint, hsplit ω (v ω) (hv ω).1 (hv ω).2]; ring

end RBSDE2Red

open RBSDE2Red ReflectedBSDE.StoppingControl

theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : Peng1990.SMP.IsStdBrownian P B)
    (T : ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : StandingData (augFiltration hB) P T ξ f S)
    (hLip : ∃ K : ℝ, IsLipschitzCoeff P T f K)
    (hS2 : InS2 (augFiltration hB) P T S)
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (hsol : IsRBSDESolution (augFiltration hB) P T B ξ f S Y Z K)
    (J : Control Ω d → Fin d → ℝ≥0 → Ω → ℝ)
    (hJ : ∀ c ∈ admissible (augFiltration hB) P T f,
      IsContItoIntegral (augFiltration hB) P T B c.2 (J c))
    (Yc : Control Ω d → ℝ≥0 → Ω → ℝ) (Zc : Control Ω d → ℝ≥0 → Ω → Fin d → ℝ)
    (Kc : Control Ω d → ℝ≥0 → Ω → ℝ)
    (hYc : ∀ c ∈ admissible (augFiltration hB) P T f,
      IsRBSDESolution (augFiltration hB) P T B ξ (affineCoeff f c) S (Yc c) (Zc c) (Kc c)) :
    ∀ t ≤ T,
      (∀ c ∈ admissible (augFiltration hB) P T f,
        IsEssSup P (augFiltration hB t)
          {X | ∃ v ∈ stoppingTimesFrom (augFiltration hB) T t,
            X = P[payoff T ξ f S c (J c) t v | augFiltration hB t]}
          (Yc c t)) ∧
      MultiperiodRisk.Bellman.IsEssInf P (augFiltration hB t)
        ((fun c => Yc c t) '' admissible (augFiltration hB) P T f) (Y t) ∧
      MultiperiodRisk.Bellman.IsEssInf P (augFiltration hB t)
        {X | ∃ c ∈ admissible (augFiltration hB) P T f,
          IsEssSup P (augFiltration hB t)
            {X' | ∃ v ∈ stoppingTimesFrom (augFiltration hB) T t,
              X' = P[payoff T ξ f S c (J c) t v | augFiltration hB t]} X}
        (Y t) ∧
      (∀ v ∈ stoppingTimesFrom (augFiltration hB) T t, ∃ X : Ω → ℝ,
        MultiperiodRisk.Bellman.IsEssInf P (augFiltration hB t)
          {X' | ∃ c ∈ admissible (augFiltration hB) P T f,
            X' = P[payoff T ξ f S c (J c) t v | augFiltration hB t]} X) ∧
      IsEssSup P (augFiltration hB t)
        {X | ∃ v ∈ stoppingTimesFrom (augFiltration hB) T t,
          MultiperiodRisk.Bellman.IsEssInf P (augFiltration hB t)
            {X' | ∃ c ∈ admissible (augFiltration hB) P T f,
              X' = P[payoff T ξ f S c (J c) t v | augFiltration hB t]} X}
        (Y t) := by
  intro t ht
  have hfprog : ∀ y z, IsStronglyProgressive (augFiltration hB) (fun t ω => f t ω y z) :=
    fun y z => (hdata.coeff_mem y z).1
  -- per-control consequences
  have hsol' : ∀ c ∈ admissible (augFiltration hB) P T f,
      IsRBSDESolution (augFiltration hB) P T B ξ (ftil T f c) S (Yc c) (Zc c) (Kc c) :=
    fun c hc => sol_congr (ftil_eq T f c) (hYc c hc)
  have hcomp : ∀ c ∈ admissible (augFiltration hB) P T f,
      ∀ᵐ ω ∂P, ∀ s ≤ T, Y s ω ≤ Yc c s ω := fun c hc =>
    comparison hB T ξ ξ f (ftil T f c) S S hdata (ftil_standing T ξ f S c hdata hconc hc)
      (Or.inl hLip) (ae_of_all _ fun _ => le_rfl) (f_le_ftil T f c hfprog hconc hc)
      (ae_of_all _ fun _ _ _ => le_rfl) Y Z K hsol (Yc c) (Zc c) (Kc c) (hsol' c hc)
  have item1 : ∀ c ∈ admissible (augFiltration hB) P T f,
      IsEssSup P (augFiltration hB t)
        {X | ∃ v ∈ stoppingTimesFrom (augFiltration hB) T t,
          X = P[payoff T ξ f S c (J c) t v | augFiltration hB t]} (Yc c t) := by
    intro c hc
    have hc' := hc
    obtain ⟨hc1, hc2, ⟨C, hC⟩, -⟩ := hc'
    have hrep := affine_representation hB T ξ S (del T f c) c.1 c.2
      (del_L2F T f c hfprog hconc hc) hc1 hc2 ⟨C, ae_of_all _ fun ω s hs => hC s hs ω⟩
      (ftil_standing T ξ f S c hdata hconc hc) hS2 (J c) (hJ c hc) (Yc c) (Zc c) (Kc c)
      (hsol' c hc) t ht
    have hβi : ∀ ω, IntegrableOn (fun r : ℝ => c.1 r.toNNReal ω) (Set.Icc (0 : ℝ) T) :=
      sec_int c.1 hc1 C (fun s hs ω => by
        have := hC s hs ω
        have := Real.sqrt_nonneg (∑ j, c.2 s ω j ^ 2)
        unfold eucNorm at *; linarith)
    have hsqprog : IsStronglyProgressive (augFiltration hB) (fun s ω => ∑ j, c.2 s ω j ^ 2) :=
      fun i => (@sq_sum_meas _ (Subtype.instMeasurableSpace.prod (augFiltration hB i)) _ _
        (hc2 i).measurable).stronglyMeasurable
    have hγi : ∀ ω, IntegrableOn (fun r : ℝ => ∑ j, c.2 r.toNNReal ω j ^ 2)
        (Set.Icc (0 : ℝ) T) :=
      sec_int (fun s ω => ∑ j, c.2 s ω j ^ 2) hsqprog (C ^ 2) (fun s hs ω => by
        have h0 : 0 ≤ ∑ j, c.2 s ω j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
        have h1 := hC s hs ω
        have h2 : eucNorm (c.2 s ω) ≤ C := by have := abs_nonneg (c.1 s ω); linarith
        rw [abs_of_nonneg h0, ← Real.sq_sqrt h0]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2)
    have hsplit : ∀ ω, ∀ s : ℝ≥0, t ≤ s → s ≤ T →
        linGamma c.1 c.2 (J c) 0 s ω = linGamma c.1 c.2 (J c) 0 t ω *
          linGamma c.1 c.2 (J c) t s ω :=
      fun ω s h1 h2 => Gamma_split c.1 c.2 (J c) T ω (hβi ω) (hγi ω) h1 h2
    have hG := Gamma_meas c.1 c.2 (J c) hc1 hc2 (hJ c hc) t
    refine esssup_scale
      (fun v => P[affinePayoff T ξ S (del T f c) c.1 c.2 (J c) t v | augFiltration hB t])
      (fun v => P[payoff T ξ f S c (J c) t v | augFiltration hB t])
      (fun ω => by unfold linGamma; exact Real.exp_pos _) hG
      ((hsol' c hc).progY.stronglyAdapted t) ?_ hrep
    intro v hv
    have hvb : ∀ ω, t ≤ v ω ∧ v ω ≤ T := hv.2
    obtain ⟨hi1, hi2⟩ := payoff_integrable hB T ξ f S hdata hLip hS2 hconc J hJ t ht c hc v hv
    show P[affinePayoff T ξ S (del T f c) c.1 c.2 (J c) t v | augFiltration hB t] =ᵐ[P] _
    rw [payoff_eq T ξ f S c (J c) t v hvb hsplit]
    exact condExp_mul_of_stronglyMeasurable_left hG hi2 hi1
  obtain ⟨cs, hcs, -, huniq⟩ := optimal_control_exists hB T ξ f S hdata hLip hconc Y Z K hsol
  have hYcs : Yc cs t =ᵐ[P] Y t :=
    (huniq _ _ _ (hYc cs hcs)).1.mono fun ω h => (h t ht).1.symm
  have hYm : StronglyMeasurable[augFiltration hB t] (Y t) := hsol.progY.stronglyAdapted t
  have hle : ∀ c ∈ admissible (augFiltration hB) P T f, Y t ≤ᵐ[P] Yc c t :=
    fun c hc => (hcomp c hc).mono fun ω h => h t ht
  obtain ⟨v0, hv0, hlow⟩ :=
    stopping_lower_bound hB T ξ f S hdata hLip hS2 hconc Y Z K hsol J hJ t ht
  refine ⟨item1, ?_, ?_,
    fun v hv => inner_essInf_exists hB T ξ f S hdata hLip hS2 hconc J hJ t ht v hv, ?_⟩
  · refine ⟨hYm, ?_, ?_⟩
    · rintro h ⟨c, hc, rfl⟩
      exact hle c hc
    · intro g' _ hlb
      exact (hlb _ ⟨cs, hcs, rfl⟩).trans hYcs.le
  · refine ⟨hYm, ?_, ?_⟩
    · rintro X ⟨c, hc, hX⟩
      exact (hle c hc).trans (esssup_unique (item1 c hc) hX).le
    · intro g' _ hlb
      exact (hlb _ ⟨cs, hcs, item1 cs hcs⟩).trans hYcs.le
  · refine ⟨hYm, ?_, ?_⟩
    · rintro X ⟨v, hv, hX⟩
      have h1 : X ≤ᵐ[P] P[payoff T ξ f S cs (J cs) t v | augFiltration hB t] :=
        hX.2.1 _ ⟨cs, hcs, rfl⟩
      have h2 : P[payoff T ξ f S cs (J cs) t v | augFiltration hB t] ≤ᵐ[P] Yc cs t :=
        (item1 cs hcs).2.1 _ ⟨v, hv, rfl⟩
      exact (h1.trans h2).trans hYcs.le
    · intro g' _ hub
      obtain ⟨X0, hX0⟩ := inner_essInf_exists hB T ξ f S hdata hLip hS2 hconc J hJ t ht v0 hv0
      have hYX : Y t ≤ᵐ[P] X0 := hX0.2.2 (Y t) hYm (by
        rintro X' ⟨c, hc, rfl⟩
        exact hlow c hc)
      exact hYX.trans (hub X0 ⟨v0, hv0, hX0⟩)
