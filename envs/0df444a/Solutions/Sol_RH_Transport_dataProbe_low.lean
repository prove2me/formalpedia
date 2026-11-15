-- Prove2me | solution 1 for RH.Transport.dataProbe_low
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T04:05:30.822403+00:00
-- url     : https://prove2.me/submissions/49a1866e-90c2-48e6-be5d-cfe88a03171c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024
import Definitions.Def_Transport_DataProbe
import Theorems.Thm_RH_Transport_PhysicalHigh_actual_ray_normalizer_inverse
import Theorems.Thm_OAI_SevenEighths_ProbePhysical_transport_original_ray_compensatedPhysicalProbe_low_loss
set_option autoImplicit false
open RH RH.Transport
open scoped Classical BigOperators ContDiff
open Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeFinalAssembly
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
noncomputable section

namespace RH.Transport.DataProbeLow

/-! Arithmetic of the tuned exponents. -/

theorem tuned_total_pos : 0 < TunedCandidate.ell := by
  norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]

theorem tuned_total_le : TunedCandidate.ell ≤ 1/5 := by
  norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]

theorem tuned_width_sum : TunedCandidate.lx + TunedCandidate.ly = 1 - TunedCandidate.ell := by
  simp only [TunedCandidate.lx, TunedCandidate.ly, TunedCandidate.lxAt, TunedCandidate.lyAt]
  ring

theorem tuned_xy_lt : TunedCandidate.lx < TunedCandidate.ly := by
  have hb : (0:ℝ) < TunedCandidate.b := by norm_num [TunedCandidate.b]
  simp only [TunedCandidate.lx, TunedCandidate.ly, TunedCandidate.lxAt, TunedCandidate.lyAt]
  linarith

theorem tuned_source_growth :
    TunedCandidate.ell < 2*TunedCandidate.lx-TunedCandidate.ly := by
  norm_num [TunedCandidate.lx, TunedCandidate.ly, TunedCandidate.lxAt, TunedCandidate.lyAt,
    TunedCandidate.b, TunedCandidate.ell, Geometry.ell, TunedCandidate.p]

theorem tuned_low_power :
    TunedCandidate.lx/2+(TunedCandidate.ly-TunedCandidate.lx)/12 =
      TunedCandidate.signal TunedCandidate.B := by
  simp only [TunedCandidate.signal, TunedCandidate.signalAt, TunedCandidate.B,
    TunedCandidate.boundaryAt, TunedCandidate.lx, TunedCandidate.ly, TunedCandidate.lxAt,
    TunedCandidate.lyAt, TunedCandidate.hAt]
  ring

lemma isBigO_rpow_of_eventual_norm_bound (f : ℝ→ℂ) (r : ℝ)
    (h : ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,‖f Z‖≤C*Z^r) :
    f=O[atTop](fun Z : ℝ=>Z^r) := by
  obtain ⟨C,hC,hb⟩ := h
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with Z hb hZ
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hZ r)] using hb

/-- The normalized probe at the tuned exponents: the raw probe and the inverse
normalizer each receive half of the loss. -/
theorem tunedNormalizedProbe_low {K : ℕ}
    (M : Ideal HeckeFamily.O) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell)
    (hsum : ∑j,ell j=TunedCandidate.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,PhysicalLow.tunedNormalizedProbe M H S hmax ell a b W W0 W1 η
      =O[atTop](fun Z : ℝ=>Z^(TunedCandidate.signal TunedCandidate.B+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin K) : Function.support (WC j)⊆Set.Icc a b := by
    intro y hy
    apply Set.Ioo_subset_Icc_self (hsupp j _)
    intro hz
    exact hy (by dsimp [WC];rw [hz];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hW1' : Function.support W1⊆Set.Icc a1 (max b1 (a1+1)) := by
    intro y hy
    exact ⟨(hW1 hy).1,(hW1 hy).2.trans (le_max_left _ _)⟩
  have hab1 : a1 < max b1 (a1+1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨Cn,hCn,hnorm⟩ := RH.Transport.PhysicalHigh.actual_ray_normalizer_inverse M H hH S hS
    a b ha hab TunedCandidate.ell ell hell hsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 (loss/2) (by positivity)
  intro η
  obtain ⟨Cp,hCp,hprobe⟩ :=
    OAI.SevenEighths.ProbePhysical.transport_original_ray_compensatedPhysicalProbe_low_loss
      TunedCandidate.ell TunedCandidate.lx TunedCandidate.ly tuned_total_pos.le tuned_total_le
      tuned_width_sum tuned_xy_lt tuned_source_growth S hS hmax ell (fun j=>(hell j).le) hinj
      hsum.le (RayQuotient.identityClass M H) a b B (loss/2) ha hab (by positivity) WC hWC hWCB
      W0 W1 a0 b0 a1 (max b1 (a1+1))
      (SchwartzMap.seminorm ℝ 0 0 W0) (SchwartzMap.seminorm ℝ 0 0 W1)
      ha0 ha1 hab1 (by positivity) (by positivity) hW0 hW1' (W0.smooth (⊤ : ℕ∞))
      (W1.smooth (⊤ : ℕ∞))
      (SchwartzMap.norm_le_seminorm ℝ W0) (SchwartzMap.norm_le_seminorm ℝ W1) η
  rw [tuned_low_power] at hprobe
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Cp*Cn,by positivity,?_⟩
  filter_upwards [hprobe,hnorm,eventually_gt_atTop (0:ℝ)] with Z hp hn hZ
  dsimp only at hn
  dsimp only [PhysicalLow.tunedNormalizedProbe]
  rw [div_eq_mul_inv,norm_mul]
  calc
    _≤(Cp*Z^(TunedCandidate.signal TunedCandidate.B+loss/2))*(Cn*Z^(loss/2)) :=
      mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    _=(Cp*Cn)*Z^(TunedCandidate.signal TunedCandidate.B+loss) := by
      rw [mul_mul_mul_comm,←Real.rpow_add hZ]
      congr 2
      ring

end RH.Transport.DataProbeLow

theorem solution {Δ : ℝ} {seed : Parameters.HighData Δ} (F : SourceData seed)
    {Kmin : ℕ} {allowance : ℝ} (D : PhysicalHigh.TunedData Kmin allowance)
    (loss : ℝ) (hloss : 0<loss) (η : Character) :
    dataProbe F D η=O[atTop](fun Z : ℝ=>Z^(TunedCandidate.signal TunedCandidate.B+loss)) := by
  exact RH.Transport.DataProbeLow.tunedNormalizedProbe_low F.modulus ⊤ le_top
    F.S F.exclusions F.maximal 1 2 1 loss (by norm_num) (by norm_num) hloss
    D.ell D.slots_pos D.slots_injective D.slots_sum (fun _=>F.w)
    (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero) F.W F.W 1 2 1 2
    (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero η
