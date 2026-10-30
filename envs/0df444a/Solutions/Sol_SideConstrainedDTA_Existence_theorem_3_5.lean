-- Prove2me | solution 1 for SideConstrainedDTA.Existence.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:44:27.703056+00:00
-- url     : https://prove2.me/submissions/dc349af4-53f3-4a81-aa5b-e3bee43d7824

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting
import Theorems.Thm_SideConstrainedDTA_Existence_theorem_3_3
import Theorems.Thm_SideConstrainedDTA_Existence_theorem_3_4
import Theorems.Thm_SideConstrainedDTA_Existence_lam_weak_seq_compact

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence.Sol35

open SideConstrainedDTA.Existence

open Classical in
noncomputable def toL2 (μ : Measure ℝ) (f : ℝ → ℝ) : Lp ℝ 2 μ :=
  if hf : MemLp f 2 μ then hf.toLp f else 0

lemma coe_toL2 {μ : Measure ℝ} {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    (toL2 μ f : ℝ → ℝ) =ᵐ[μ] f := by
  unfold toL2; rw [dif_pos hf]; exact hf.coeFn_toLp

lemma inner_toL2 {μ : Measure ℝ} {f : ℝ → ℝ} (hf : MemLp f 2 μ) (w : Lp ℝ 2 μ) :
    inner ℝ (toL2 μ f) w = ∫ t, f t * (w : ℝ → ℝ) t ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coe_toL2 hf] with t ht
  rw [ht]; simp [mul_comm]

noncomputable def emb {W : Type*} (μ : Measure ℝ) {d : ℕ} (e : W ≃ Fin d) (h : W → ℝ → ℝ) :
    PiLp 2 (fun _ : Fin d => Lp ℝ 2 μ) :=
  WithLp.toLp 2 (fun k => toL2 μ (h (e.symm k)))

variable {I W E : Type*} [Fintype W] [DecidableEq I]

lemma lam_bd (N : Model I W E) {h : W → ℝ → ℝ} (hh : Lam N h) (p : W) :
    ∀ᵐ t ∂(volume.restrict (Icc N.t0 N.tf)), 0 ≤ h p t ∧ h p t ≤ N.B p := by
  have h1 := ae_restrict_of_ae (μ := volume) (s := Icc N.t0 N.tf) (hh.2.1 p)
  filter_upwards [h1, ae_restrict_mem measurableSet_Icc] with t ht htI
  exact (ht.1 htI)

lemma lam_mem (N : Model I W E) {h : W → ℝ → ℝ} (hh : Lam N h) (p : W) :
    MemLp (h p) 2 (volume.restrict (Icc N.t0 N.tf)) :=
  MemLp.of_bound (hh.1 p).aestronglyMeasurable (N.B p) (by
    filter_upwards [lam_bd N hh p] with t ht
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [ht.1, ht.2])

lemma pair_congr (N : Model I W E) {g g' : W → ℝ → ℝ} (h : W → ℝ → ℝ)
    (hg : ∀ p, g p =ᵐ[volume.restrict (Icc N.t0 N.tf)] g' p) : pair N g h = pair N g' h := by
  unfold pair
  refine Finset.sum_congr rfl fun p _ => integral_congr_ae ?_
  filter_upwards [hg p] with t ht
  rw [ht]

lemma inner_emb (N : Model I W E) {d : ℕ} (e : W ≃ Fin d) {h : W → ℝ → ℝ}
    (hh : ∀ p, MemLp (h p) 2 (volume.restrict (Icc N.t0 N.tf)))
    (G : PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Icc N.t0 N.tf)))) :
    inner ℝ (emb (volume.restrict (Icc N.t0 N.tf)) e h) G =
      pair N (fun p t => (G.ofLp (e p) : ℝ → ℝ) t) h := by
  rw [PiLp.inner_apply]
  simp only [emb, PiLp.toLp_apply]
  unfold pair
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_toL2 (hh _)]
  simp only [Equiv.apply_symm_apply, mul_comm]

end SideConstrainedDTA.Existence.Sol35

open SideConstrainedDTA.Existence SideConstrainedDTA.Existence.Sol35

theorem solution {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]
    (N : Model I W E) (hN : N.Basic) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ)
    (hΦ : ∀ h, Lam N h → ∀ p, AEStronglyMeasurable (Φ h p) (volume.restrict (Icc N.t0 N.tf)))
    (h1 : A1 N Φ) (h2 : A2 N) (h3 : A3 N) (h4 : A4 N Φ) :
    ∃ h, IsDTCEq N Φ h := by
  classical
  set μ : Measure ℝ := volume.restrict (Icc N.t0 N.tf) with hμ
  set d := Fintype.card W
  set e : W ≃ Fin d := Fintype.equivFin W
  have memΦ : ∀ h, Lam N h → ∀ p, MemLp (Φ h p) 2 μ := by
    intro h hh p
    obtain ⟨K, hK⟩ := h1 h hh p
    refine MemLp.of_bound (hΦ h hh p) K ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs]; exact hK t ht
  let C : Set (PiLp 2 (fun _ : Fin d => Lp ℝ 2 μ)) := {x | ∃ h, Lam N h ∧ emb μ e h = x}
  let A : PiLp 2 (fun _ : Fin d => Lp ℝ 2 μ) → PiLp 2 (fun _ : Fin d => Lp ℝ 2 μ) :=
    fun x => if hx : ∃ h, Lam N h ∧ emb μ e h = x then emb μ e (Φ hx.choose) else 0
  have hA_eq : ∀ x (hx : ∃ h, Lam N h ∧ emb μ e h = x), A x = emb μ e (Φ hx.choose) :=
    fun x hx => dif_pos hx
  -- nonempty
  have hne : C.Nonempty := by
    obtain ⟨h, hh⟩ := h3
    exact ⟨emb μ e h, h, hh, rfl⟩
  -- convex
  have hconv : Convex ℝ C := by
    rintro x ⟨g1, hg1, rfl⟩ y ⟨g2, hg2, rfl⟩ a b ha hb hab
    have hm1 := lam_mem N hg1
    have hm2 := lam_mem N hg2
    have hmc : ∀ p, MemLp (fun t => a * g1 p t + b * g2 p t) 2 μ := fun p =>
      ((hm1 p).const_mul a).add ((hm2 p).const_mul b)
    refine ⟨fun p t => a * g1 p t + b * g2 p t, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro p
      exact ((hg1.1 p).const_mul a).add ((hg2.1 p).const_mul b)
    · intro p
      filter_upwards [hg1.2.1 p, hg2.2.1 p] with t ht1 ht2
      refine ⟨fun hti => ?_, fun hti => ?_⟩
      · obtain ⟨a1, a2⟩ := ht1.1 hti
        obtain ⟨b1, b2⟩ := ht2.1 hti
        refine ⟨by positivity, ?_⟩
        have e1 : a * g1 p t ≤ a * N.B p := mul_le_mul_of_nonneg_left a2 ha
        have e2 : b * g2 p t ≤ b * N.B p := mul_le_mul_of_nonneg_left b2 hb
        have : a * N.B p + b * N.B p = N.B p := by rw [← add_mul, hab, one_mul]
        linarith
      · simp [ht1.2 hti, ht2.2 hti]
    · intro i
      have hI1 : ∀ p, Integrable (g1 p) μ := fun p => (hm1 p).integrable one_le_two
      have hI2 : ∀ p, Integrable (g2 p) μ := fun p => (hm2 p).integrable one_le_two
      have : ∀ p, ∫ t, a * g1 p t + b * g2 p t ∂μ =
          a * ∫ t, g1 p t ∂μ + b * ∫ t, g2 p t ∂μ := by
        intro p
        rw [integral_add ((hI1 p).const_mul a) ((hI2 p).const_mul b)]
        simp only [integral_const_mul]
      calc ∑ p ∈ Finset.univ.filter (fun p => N.com p = i), ∫ t, a * g1 p t + b * g2 p t ∂μ
          = ∑ p ∈ Finset.univ.filter (fun p => N.com p = i),
              (a * ∫ t, g1 p t ∂μ + b * ∫ t, g2 p t ∂μ) := Finset.sum_congr rfl fun p _ => this p
        _ = a * N.Q i + b * N.Q i := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hg1.2.2 i, hg2.2.2 i]
        _ = N.Q i := by rw [← add_mul, hab, one_mul]
    · refine PiLp.ext fun k => ?_
      simp only [emb, PiLp.toLp_apply, PiLp.add_apply, PiLp.smul_apply]
      refine Lp.ext ?_
      filter_upwards [coe_toL2 (hmc (e.symm k)), Lp.coeFn_add (a • toL2 μ (g1 (e.symm k)))
        (b • toL2 μ (g2 (e.symm k))), Lp.coeFn_smul a (toL2 μ (g1 (e.symm k))),
        Lp.coeFn_smul b (toL2 μ (g2 (e.symm k))), coe_toL2 (hm1 (e.symm k)),
        coe_toL2 (hm2 (e.symm k))] with t q1 q2 q3 q4 q5 q6
      rw [q1, q2, Pi.add_apply, q3, q4, Pi.smul_apply, Pi.smul_apply, q5, q6]
      simp
  -- closed
  have hclosed : IsClosed C := by
    refine isSeqClosed_iff_isClosed.1 fun xs x hxs hlim => ?_
    choose hs hhs hEs using hxs
    obtain ⟨φ, hφ, hstar, hL, hweak⟩ := lam_weak_seq_compact N hs hhs
    refine ⟨hstar, hL, ?_⟩
    refine ext_inner_right ℝ fun G => ?_
    have t1 : Tendsto (fun n => inner ℝ (xs (φ n)) G) atTop (𝓝 (inner ℝ x G)) :=
      (hlim.comp hφ.tendsto_atTop).inner tendsto_const_nhds
    have t2 : Tendsto (fun n => inner ℝ (xs (φ n)) G) atTop
        (𝓝 (inner ℝ (emb μ e hstar) G)) := by
      rw [inner_emb N e (lam_mem N hL)]
      have := hweak (fun p t => (G.ofLp (e p) : ℝ → ℝ) t) (fun p => Lp.memLp _)
      refine this.congr fun n => ?_
      rw [← hEs (φ n), inner_emb N e (lam_mem N (hhs (φ n)))]
    exact tendsto_nhds_unique t2 t1
  -- bounded
  have hbdd : Bornology.IsBounded C := by
    have hK : ∀ h, Lam N h → ∀ p, ‖toL2 μ (h p)‖ ≤
        (measureUnivNNReal μ : ℝ) ^ ((2:ENNReal).toReal)⁻¹ * |N.B p| := by
      intro h hh p
      refine Lp.norm_le_of_ae_bound (abs_nonneg _) ?_
      filter_upwards [coe_toL2 (lam_mem N hh p), lam_bd N hh p] with t q1 q2
      rw [q1, Real.norm_eq_abs]
      exact abs_le_abs q2.2 (by linarith [q2.1, q2.2])
    refine isBounded_iff_forall_norm_le.2 ⟨Real.sqrt (∑ k : Fin d,
      ((measureUnivNNReal μ : ℝ) ^ ((2:ENNReal).toReal)⁻¹ * |N.B (e.symm k)|) ^ 2), ?_⟩
    rintro x ⟨h, hh, rfl⟩
    refine Real.le_sqrt_of_sq_le ?_
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum fun k _ => ?_
    simp only [emb, PiLp.toLp_apply]
    exact pow_le_pow_left₀ (norm_nonneg _) (hK h hh _) 2
  -- weak-strong continuity
  have hAc : ∀ (xs : ℕ → PiLp 2 (fun _ : Fin d => Lp ℝ 2 μ))
      (x₀ : PiLp 2 (fun _ : Fin d => Lp ℝ 2 μ)), (∀ n, xs n ∈ C) → x₀ ∈ C →
      (∀ g, Tendsto (fun n => inner ℝ (xs n) g) atTop (𝓝 (inner ℝ x₀ g))) →
      Tendsto (fun n => A (xs n)) atTop (𝓝 (A x₀)) := by
    intro xs x₀ hxs hx₀ hw
    have hc : WeakConvSeq N (fun n => (hxs n).choose) hx₀.choose := by
      refine ⟨fun n => (hxs n).choose_spec.1, hx₀.choose_spec.1, fun g hg => ?_⟩
      have key : ∀ (h : W → ℝ → ℝ), Lam N h →
          inner ℝ (emb μ e h) (emb μ e g) = pair N g h := by
        intro h hh
        rw [inner_emb N e (lam_mem N hh)]
        refine pair_congr N h fun p => ?_
        simp only [emb, PiLp.toLp_apply, Equiv.symm_apply_apply]
        exact coe_toL2 (hg p)
      have := hw (emb μ e g)
      rw [← hx₀.choose_spec.2, key _ hx₀.choose_spec.1] at this
      refine this.congr fun n => ?_
      rw [← (hxs n).choose_spec.2, key _ (hxs n).choose_spec.1]
    have hfun : (fun n => A (xs n)) = fun n => emb μ e (Φ (hxs n).choose) :=
      funext fun n => hA_eq _ (hxs n)
    rw [hfun, hA_eq _ hx₀]
    refine ((PiLp.continuous_toLp 2 _).tendsto _).comp (tendsto_pi_nhds.2 fun k => ?_)
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have h4' := h4 _ _ hc (e.symm k)
    refine h4'.congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    exact ((coe_toL2 (memΦ _ (hxs n).choose_spec.1 _)).sub
      (coe_toL2 (memΦ _ hx₀.choose_spec.1 _))).symm
  obtain ⟨x, hx, hvi⟩ := theorem_3_4 N.t0 N.tf d C A hne hclosed hconv hbdd hAc
  have hL0 := hx.choose_spec.1
  have hE0 := hx.choose_spec.2
  refine ⟨hx.choose, (theorem_3_3 N hN Φ hΦ h1 hx.choose hL0).2 fun h hh => ?_⟩
  have hv := hvi (emb μ e h) ⟨h, hh, rfl⟩
  rw [hA_eq x hx, inner_emb N e (memΦ _ hL0)] at hv
  convert hv using 1
  unfold pair
  refine Finset.sum_congr rfl fun p _ => integral_congr_ae ?_
  have hcomp : (emb μ e h - x).ofLp (e p) = toL2 μ (h p) - toL2 μ (hx.choose p) := by
    conv_lhs => rw [← hE0]
    simp [emb, PiLp.sub_apply]
  beta_reduce
  rw [hcomp]
  filter_upwards [Lp.coeFn_sub (toL2 μ (h p)) (toL2 μ (hx.choose p)),
    coe_toL2 (lam_mem N hh p), coe_toL2 (lam_mem N hL0 p)] with t q1 q2 q3
  rw [q1, Pi.sub_apply, q2, q3, mul_comm]
