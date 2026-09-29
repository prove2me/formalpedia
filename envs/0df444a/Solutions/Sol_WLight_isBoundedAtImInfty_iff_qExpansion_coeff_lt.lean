-- Prove2me | solution 1 for WLight.isBoundedAtImInfty_iff_qExpansion_coeff_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4f38c1be-3103-5e50-acf7-40a1d3011d5d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt

set_option autoImplicit false

noncomputable section

p2m_open "Complex Real UpperHalfPlane Function Filter Polynomial Real.Polynomial"
open scoped Topology Manifold MatrixGroups ModularForm

namespace WLightBdd

section CuspCriterion

variable {N : ℕ}

lemma isBoundedAtImInfty_discriminant : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).boundedAtFilter

lemma isBoundedAtImInfty_discPow (n : ℕ) :
    IsBoundedAtImInfty (⇑CuspForm.discriminant ^ n : ℍ → ℂ) := by
  induction n with
  | zero => exact pow_zero (⇑CuspForm.discriminant : ℍ → ℂ) ▸ Filter.const_boundedAtFilter _ (1 : ℂ)
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul isBoundedAtImInfty_discriminant

lemma IsBoundedAtImInfty.mul_discPow_mono {f : ℍ → ℂ} {m m' : ℕ} (hm : m ≤ m')
    (h : IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)) :
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m') := by
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  rw [hshape]
  exact h.mul (isBoundedAtImInfty_discPow (m' - m))

def discPowForm (m : ℕ) : ModularForm 𝒮ℒ (12 * m) :=
  ModularForm.mcast (by ring) ((CuspForm.toModularFormₗ CuspForm.discriminant).pow m)

lemma discPowForm_coe (m : ℕ) : ⇑(discPowForm m) = ⇑CuspForm.discriminant ^ m := by
  funext z
  simp [discPowForm, ModularForm.coe_mcast, ModularForm.coe_pow,
    CuspForm.toModularFormₗ_apply]

lemma periodic_one_fn (c : ℝ) : Function.Periodic ((1 : ℍ → ℂ) ∘ ofComplex) c := fun _ => rfl

lemma periodic_discPow_comp_ofComplex (k : ℕ) (N : ℕ) :
    Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) N := by
  have h1 : Function.Periodic (⇑CuspForm.discriminant ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL
  have hk : Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) 1 := by
    induction k with
    | zero => exact periodic_one_fn 1
    | succ k ih =>
      intro x
      have hx := (ih.mul h1) x
      simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply] at hx ⊢
      rw [pow_succ, pow_succ]
      exact hx
  simpa using hk.nat_mul N

lemma mdiff_discPow (k : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑CuspForm.discriminant ^ k : ℍ → ℂ) := by
  rw [← discPowForm_coe]
  exact (discPowForm k).holo'

lemma mdiff_mul_discPow {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (m : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) :=
  hf.mul (mdiff_discPow m)

lemma analyticAt_cuspFunction_zero_of [NeZero N] {g : ℍ → ℂ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Function.Periodic (g ∘ ofComplex) N) (hbd : IsBoundedAtImInfty g) :
    AnalyticAt ℂ (cuspFunction N g) 0 :=
  analyticAt_cuspFunction_zero
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hper hhol hbd

lemma qExpansion_one_discPowForm (k : ℕ) :
    qExpansion 1 (discPowForm k) = (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [discPowForm, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hco : (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ) =
      ModularForm.discriminant := by
    funext z
    rw [CuspForm.toModularFormₗ_apply]
    exact congrFun CuspForm.coe_discriminant z
  rw [hco]

lemma qExpansion_one_discPow (k : ℕ) :
    qExpansion 1 (⇑CuspForm.discriminant ^ k : ℍ → ℂ) =
      (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [← discPowForm_coe]
  exact qExpansion_one_discPowForm k

lemma coeff_pow_eq_zero_of_lt {D : PowerSeries ℂ} (hD0 : D.coeff 0 = 0) {k n : ℕ}
    (hn : n < k) : (D ^ k).coeff n = 0 := by
  have hX : (PowerSeries.X : PowerSeries ℂ) ∣ D :=
    PowerSeries.X_dvd_iff.mpr (by rwa [← PowerSeries.coeff_zero_eq_constantCoeff])
  exact PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hX k) n hn

lemma discriminant_qExpansion_coeff_zero :
    (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

lemma qParam_one_eq_pow {N : ℕ} (hN : N ≠ 0) (τ : ℂ) :
    Function.Periodic.qParam 1 τ = Function.Periodic.qParam N τ ^ N := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

theorem qExpansion_coeff_width (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperN : Function.Periodic (f ∘ ofComplex) N := by
    simpa using hper.nat_mul N
  let f' : C(ℍ, ℂ) := ⟨f, hhol.continuous⟩
  have hfan : AnalyticAt ℂ (cuspFunction N f') 0 :=
    analyticAt_cuspFunction_zero hN' hperN hhol hbd
  set c : ℕ → ℂ := fun n ↦ if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 with hc
  have hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam N τ ^ m) (f' τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hhol hbd τ
    have hinj : Function.Injective fun m : ℕ ↦ N * m := fun a b h ↦ by
      simpa [Nat.mul_right_inj hN] using h
    refine (hinj.hasSum_iff (f := fun m ↦ c m • Function.Periodic.qParam N τ ^ m) ?_).mp ?_
    · intro x hx
      have : ¬ N ∣ x := fun ⟨k, hk⟩ ↦ hx ⟨k, hk.symm⟩
      simp [hc, this]
    · refine h1.congr_fun fun m ↦ ?_
      simp only [Function.comp_apply, hc, Nat.dvd_mul_right, if_true,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN), qParam_one_eq_pow hN, ← pow_mul]
  exact (qExpansion_coeff_unique f' hN' hfan hf n).symm

theorem isZeroAtImInfty_iff_qExpansion_coeff_zero_eq_zero {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hfbdd : IsBoundedAtImInfty f) :
    IsZeroAtImInfty f ↔ (qExpansion h f).coeff 0 = 0 := by
  have hanal := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  rw [qExpansion_coeff_zero hh hanal hfper]
  refine ⟨fun hf ↦ hf.valueAtInfty_eq_zero, fun hv ↦ ?_⟩
  rw [IsZeroAtImInfty, ZeroAtFilter, ← hv, ← cuspFunction_apply_zero hh hanal hfper]
  exact (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)).congr
    (fun τ ↦ eq_cuspFunction τ hh.ne' hfper)

open Asymptotics in

theorem isBigO_qParam_pow_of_qExpansion_coeff_eq_zero {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hfbdd : IsBoundedAtImInfty f)
    {k : ℕ} (hcoeff : ∀ n ≤ k, (qExpansion h f).coeff n = 0) :
    f =O[atImInfty] fun τ ↦ (Periodic.qParam h τ) ^ (k + 1) := by
  have hanal := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  have hideriv : ∀ i < k + 1, iteratedDeriv i (cuspFunction h f) 0 = 0 := by
    intro i hi
    have hci := hcoeff i (Nat.lt_succ_iff.mp hi)
    rw [qExpansion_coeff] at hci
    have hfac : ((i.factorial : ℂ))⁻¹ ≠ 0 :=
      inv_ne_zero (Nat.cast_ne_zero.mpr i.factorial_ne_zero)
    exact (mul_eq_zero.mp hci).resolve_left hfac
  have hord : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (cuspFunction h f) 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanal).mpr hideriv
  obtain ⟨g, hgan, hfac⟩ := (natCast_le_analyticOrderAt hanal).mp hord
  have hOcf : (cuspFunction h f) =O[𝓝 0] fun q : ℂ ↦ q ^ (k + 1) := by
    have hg1 : g =O[𝓝 (0 : ℂ)] (fun _ : ℂ ↦ (1 : ℂ)) := hgan.continuousAt.isBigO_one ℂ
    refine ((isBigO_refl (fun q : ℂ ↦ q ^ (k + 1)) (𝓝 0)).mul hg1).congr' ?_
      (.of_forall fun q ↦ mul_one _)
    filter_upwards [hfac] with q hq
    rw [hq, sub_zero, smul_eq_mul]
  refine (hOcf.comp_tendsto (qParam_tendsto_atImInfty hh)).congr' ?_ (.of_forall fun τ ↦ rfl)
  exact .of_forall fun τ ↦ eq_cuspFunction τ hh.ne' hfper

open Asymptotics ModularForm in

theorem qParam_pow_isBigO_discPow {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    (fun τ : ℍ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * k)) =O[atImInfty]
      (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ k) := by
  refine .trans (IsBigO.of_bound 1 (.of_forall fun τ ↦ le_of_eq ?_)) (exp_isBigO_discriminant.pow k)
  rw [one_mul, norm_pow, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le,
    pow_mul, Function.Periodic.norm_qParam, ← Real.exp_nat_mul, UpperHalfPlane.coe_im]
  congr 2
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp

open Asymptotics ModularForm in

theorem isZeroAtImInfty_mul_disc_of_coeff_le {N : ℕ} (hN : N ≠ 0) {F : ℍ → ℂ} {M : ℕ}
    (hM : 1 ≤ M)
    (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F * ⇑CuspForm.discriminant ^ M))
    (hfper : Periodic ((F * ⇑CuspForm.discriminant ^ M) ∘ ofComplex) N)
    (hfbd : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ M))
    (hcoeff : ∀ n ≤ N * (M - 1), (qExpansion N (F * ⇑CuspForm.discriminant ^ M)).coeff n = 0) :
    IsZeroAtImInfty (F * ⇑CuspForm.discriminant) := by
  set G : ℍ → ℂ := F * ⇑CuspForm.discriminant ^ M with hGdef
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hGO : G =O[atImInfty]
      fun τ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * (M - 1) + 1) :=
    isBigO_qParam_pow_of_qExpansion_coeff_eq_zero hN' hfper hfhol hfbd hcoeff
  have hqO : (fun τ : ℍ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * (M - 1) + 1))
      =O[atImInfty]
        (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ (M - 1) *
          Periodic.qParam (N : ℝ) (τ : ℂ)) :=
    ((qParam_pow_isBigO_discPow hN (M - 1)).mul
        (isBigO_refl (fun τ : ℍ ↦ Periodic.qParam (N : ℝ) (τ : ℂ)) atImInfty)).congr_left
      (fun τ ↦ (pow_succ _ _).symm)
  have hGO' : G =O[atImInfty]
      (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ (M - 1) *
        Periodic.qParam (N : ℝ) (τ : ℂ)) := hGO.trans hqO
  have hfdeq : ∀ τ : ℍ, (F * ⇑CuspForm.discriminant) τ
      = G τ / (ModularForm.discriminant τ) ^ (M - 1) := fun τ ↦ by
    have hΔ := ModularForm.discriminant_ne_zero τ
    simp only [hGdef, Pi.mul_apply, Pi.pow_apply, CuspForm.coe_discriminant]
    rw [eq_div_iff (pow_ne_zero _ hΔ), mul_assoc, ← pow_succ', Nat.sub_add_cancel hM]
  have hfneq : (fun τ : ℍ ↦ ‖G τ / ((ModularForm.discriminant τ : ℂ) ^ (M - 1) *
        Periodic.qParam (N : ℝ) (τ : ℂ))‖)
      = (fun τ ↦ ‖(F * ⇑CuspForm.discriminant) τ / Periodic.qParam (N : ℝ) (τ : ℂ)‖) :=
    funext fun τ ↦ by rw [hfdeq, div_div]
  have hbnd : IsBoundedUnder (· ≤ ·) atImInfty
      (fun τ : ℍ ↦ ‖(F * ⇑CuspForm.discriminant) τ / Periodic.qParam (N : ℝ) (τ : ℂ)‖) :=
    hfneq ▸ div_isBoundedUnder_of_isBigO hGO'
  have hq_ne : ∀ τ : ℍ, Periodic.qParam (N : ℝ) (τ : ℂ) ≠ 0 := fun τ ↦
    Complex.exp_ne_zero _
  have hFDO : (F * ⇑CuspForm.discriminant) =O[atImInfty]
      (fun τ : ℍ ↦ Periodic.qParam (N : ℝ) (τ : ℂ)) :=
    (isBigO_iff_div_isBoundedUnder (.of_forall fun τ h ↦ absurd h (hq_ne τ))).mpr hbnd
  exact hFDO.trans_tendsto (qParam_tendsto_atImInfty hN')

open ModularForm in
set_option maxHeartbeats 1600000 in

lemma qExpansion_discPow_coeff_eq_zero_of_lt [NeZero N] (k : ℕ) {j : ℕ} (hj : j < N * k) :
    (qExpansion N (⇑CuspForm.discriminant ^ k : ℍ → ℂ)).coeff j = 0 := by
  have hper : Function.Periodic
      ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) (1 : ℂ) := by
    have h := periodic_discPow_comp_ofComplex k 1
    simpa only [Nat.cast_one] using h
  rw [qExpansion_coeff_width _ (NeZero.ne N) hper
    (mdiff_discPow k) (isBoundedAtImInfty_discPow k), qExpansion_one_discPow]
  split_ifs with hN
  · exact coeff_pow_eq_zero_of_lt discriminant_qExpansion_coeff_zero
      (Nat.div_lt_of_lt_mul (Nat.mul_comm N k ▸ hj))
  · rfl

open Asymptotics ModularForm in

theorem isBoundedAtImInfty_of_coeff_lt {N : ℕ} (hN : N ≠ 0) {F : ℍ → ℂ} {M : ℕ}
    (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F * ⇑CuspForm.discriminant ^ M))
    (hfper : Periodic ((F * ⇑CuspForm.discriminant ^ M) ∘ ofComplex) N)
    (hfbd : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ M))
    (hcoeff : ∀ n < N * M, (qExpansion N (F * ⇑CuspForm.discriminant ^ M)).coeff n = 0) :
    IsBoundedAtImInfty F := by
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0
    simpa using hfbd
  set G : ℍ → ℂ := F * ⇑CuspForm.discriminant ^ M with hGdef
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNM : N * M - 1 + 1 = N * M := Nat.sub_add_cancel (Nat.mul_pos (Nat.pos_of_ne_zero hN) hMpos)
  have hGO : G =O[atImInfty] fun τ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * M - 1 + 1) :=
    isBigO_qParam_pow_of_qExpansion_coeff_eq_zero hN' hfper hfhol hfbd fun n hn => hcoeff n (by omega)
  rw [hNM] at hGO
  have hGO' : G =O[atImInfty] (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ M) :=
    hGO.trans (qParam_pow_isBigO_discPow hN M)
  have hfdeq : ∀ τ : ℍ, F τ = G τ / (ModularForm.discriminant τ) ^ M := fun τ ↦ by
    have hΔ := ModularForm.discriminant_ne_zero τ
    simp only [hGdef, Pi.mul_apply, Pi.pow_apply, CuspForm.coe_discriminant]
    rw [eq_div_iff (pow_ne_zero _ hΔ)]
  have hbnd : IsBoundedUnder (· ≤ ·) atImInfty (fun τ : ℍ ↦ ‖G τ / (ModularForm.discriminant τ : ℂ) ^ M‖) :=
    div_isBoundedUnder_of_isBigO hGO'
  have hfun : (fun τ : ℍ ↦ ‖F τ‖) = fun τ : ℍ ↦ ‖G τ / (ModularForm.discriminant τ : ℂ) ^ M‖ :=
    funext fun τ => by rw [hfdeq τ]
  have hbnd' : IsBoundedUnder (· ≤ ·) atImInfty (fun τ : ℍ ↦ ‖F τ‖) := by
    rw [hfun]; exact hbnd
  change F =O[atImInfty] (1 : ℍ → ℝ)
  exact (isBigO_one_iff ℝ).mpr hbnd'

open ModularForm in

theorem qExpansion_coeff_eq_zero_of_isBoundedAtImInfty [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ ofComplex) N)
    (hFbd : IsBoundedAtImInfty F) :
    ∀ n < N * M, (qExpansion N (F * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
  intro n hn
  rw [qExpansion_mul (analyticAt_cuspFunction_zero_of hFhol hFper hFbd)
      (analyticAt_cuspFunction_zero_of (mdiff_discPow M)
        (periodic_discPow_comp_ofComplex M N) (isBoundedAtImInfty_discPow M)),
    PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ⟨i, j⟩ hij ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rw [qExpansion_discPow_coeff_eq_zero_of_lt M (show j < N * M by omega), mul_zero]

end CuspCriterion

end WLightBdd

end

open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

open WLightBdd in
theorem solution (N : ℕ) [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) N)
    (hFbd : IsBoundedAtImInfty (F * ModularForm.discriminant ^ M)) :
    IsBoundedAtImInfty F ↔
      ∀ n < N * M,
        (UpperHalfPlane.qExpansion N (F * ModularForm.discriminant ^ M)).coeff n = 0 := by
  rw [show (ModularForm.discriminant : ℍ → ℂ) = ⇑CuspForm.discriminant from
    CuspForm.coe_discriminant.symm]
  have hFbd' : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ M) := by
    rwa [show (⇑CuspForm.discriminant : ℍ → ℂ) = ModularForm.discriminant from
      CuspForm.coe_discriminant]
  exact ⟨qExpansion_coeff_eq_zero_of_isBoundedAtImInfty hFhol hFper,
    isBoundedAtImInfty_of_coeff_lt (NeZero.ne N) (mdiff_mul_discPow hFhol M)
      (hFper.mul (periodic_discPow_comp_ofComplex M N)) hFbd'⟩

end S_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt
end P2MW
export P2MW.S_WLight_isBoundedAtImInfty_iff_qExpansion_coeff_lt (solution)
