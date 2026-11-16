-- Prove2me | solution 1 for RH.Transport.PhysicalHigh.data_chosen_moments
-- status  : ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T04:26:20.209282+00:00
-- url     : https://prove2.me/submissions/2859e510-4de7-42e4-9d20-6e6372e09316

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Definitions.Def_Transport_PhysicalHigh_MomentBound
import Definitions.Def_Transport_PhysicalHigh_PositiveFineSourceInput
import Theorems.Thm_RH_Transport_PhysicalHigh_actual_plain_inputs
import Theorems.Thm_RH_Transport_PhysicalHigh_actual_source_moments_from_inputs
set_option autoImplicit false

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeHighRowFamily

lemma rawMoment_mono_constant {data : RowData} {W : ℝ→ℂ} {c κ C D : ℝ}
    (h : RawMoment data W c κ C) (hCD : C≤D) : RawMoment data W c κ D := by
  intro H X hH hX hsize rows hrows
  apply (h H X hH hX hsize rows hrows).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD (by linarith)) (by positivity)

lemma moments_mono_constant {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    {F : Fiber M H Label Slot U a ε tstar T allowance i}
    {Δ c κ C D height εm : ℝ} (hU : 0≤U) (h : Moments F Δ c κ C height εm) (hCD : C≤D) :
    Moments F Δ c κ D height εm := by
  constructor
  · intro n hn s hs t ht
    exact ⟨rawMoment_mono_constant (h.inverse_raw n hn s hs t ht).1 hCD,
      rawMoment_mono_constant (h.inverse_raw n hn s hs t ht).2 hCD⟩
  · intro selected hsel hcap1 hcap2 n hn s hs t ht
    exact (h.inverse_marked selected hsel hcap1 hcap2 n hn s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))
  · intro selected hsel hcap j k hj s hs t ht
    exact (h.plain_marked selected hsel hcap j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))
  · intro j k hj s hs t ht
    exact (h.plain_unmarked j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))

lemma sourceMomentsAt_mono_constant (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (Δ c κ C D height εm : ℝ) (hZ : 0≤Z) (hCD : C≤D)
    (h : SourceMomentsAt M H hH S hS η rows ell W Z d a ε τ dmax b slotMesh binWidth i z Δ c κ C height εm) :
    SourceMomentsAt M H hH S hS η rows ell W Z d a ε τ dmax b slotMesh binWidth i z Δ c κ D height εm := by
  intro q B hrows hdata hrev hslots hwidth hprof hupp hext hmesh hbin hfam bin j J K hne
  exact moments_mono_constant (Real.rpow_nonneg hZ _)
    (h q B hrows hdata hrev hslots hwidth hprof hupp hext hmesh hbin hfam bin j J K hne) hCD

end SevenEighths.ProbeFinalAssembly

end

end OAI
end


open RH RH.Transport RH.Transport.PhysicalHigh
open scoped Classical
open Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbeFinalAssembly ProbeHighRowFamily HeckeInverseAmplification
open Parameters
noncomputable section

namespace RH.Transport.PhysicalHigh.DataMoments

/-- A polynomial in the height `Z^(2τ)` of degree `J` is absorbed by `Z^t`
as soon as `2τ(1+J) ≤ t`. -/
lemma polynomial_height_absorption (C Z τ J t : ℝ)
    (hC : 0≤C) (hZ : 1≤Z) (hτ : 0≤τ) (hJ : 0≤J) (hbudget : 2*τ*(1+J)≤t) :
    C*(1+Z^(2*τ))^J≤(C*2^J)*Z^t := by
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hscale : 1≤Z^(2*τ) := Real.one_le_rpow hZ (by positivity)
  calc
    _≤C*(2*Z^(2*τ))^J := by gcongr;linarith
    _=(C*2^J)*Z^(2*τ*J) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hZp.le _),←Real.rpow_mul hZp.le]
      ring
    _≤(C*2^J)*Z^t := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

/-- Chosen-height moment production: the height exponent is chosen only after
the moment degree `J` is known. -/
theorem actual_chosen_moments {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (N : ℕ) (ell : Fin N → ℝ) (hell : ∀ j, 0 < ell j)
    (hinj : Function.Injective ell)
    (t rmin ellMin allowance : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (P : DetectorScales t N rmin ellMin allowance)
    (hfine : ∀ j, ell j ≤ plainMesh t / 200)
    (cB kB cH kH : ℝ) (hcB : 0 < cB) (hkB : 0 < kB)
    (hcH : 0 < cH) (hkH : 0 < kH)
    (hbeta : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta ≤ 7 / 8) :
    ∃ τ : ℝ, 0 < τ ∧ τ < (1 / 200 : ℝ) / 2 ∧
      4 * τ < (1 / 200 : ℝ) * P.cost ∧ τ < t ∧
      2 * τ ≤ t ∧ τ * (2 + 4 * P.eps) < t ∧
      ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        1 < Z ∧ ∀ rows : Finset FreeRow,
        (∀ u ∈ rows, Z ^ (1 / 100 : ℝ) ≤ rowNorm u) →
        ∀ d : ℝ, (1 / 200 : ℝ) ≤ d →
        ∀ a dmax slotMesh binWidth : ℝ, ∀ i : ℕ, ∀ z : ℂ,
        z.re = 17 / 50 → |z.im| ≤ Z ^ (2 * τ) →
        SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows ell
          (fun _ y => (F.w y : ℂ)) Z d a P.ε τ dmax 2 slotMesh binWidth i z 0
          (if 2 * a - 1 ≤ 5 / 6 then cB else cH)
          (if 2 * a - 1 ≤ 5 / 6 then kB else kH)
          (C * Z ^ t) (Z ^ (2 * τ)) t := by
  obtain ⟨J, hmoment⟩ := RH.Transport.PhysicalHigh.actual_source_moments_from_inputs F N ell
    hell hinj P.ε t P.epsilon_small ht ht1 hfine cB kB cH kH hcB hkB hcH hkH
    (RH.Transport.PhysicalHigh.actual_plain_inputs F N t ht hbeta hceiling)
  obtain ⟨τ, hτ, hτd, hτc, hτt, hτJ, hτeps⟩ :=
    P.height_choice (J : ℝ) (Nat.cast_nonneg J)
  have hτ2 : 2 * τ ≤ t := by nlinarith [Nat.cast_nonneg (α := ℝ) J]
  refine ⟨τ, hτ, hτd, hτc, hτt, hτ2, hτeps, ?_⟩
  intro η
  obtain ⟨C, hC, hb⟩ := hmoment η
  refine ⟨C * 2 ^ (J : ℝ), by positivity, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with Z hb hZ
  refine ⟨hb.1, ?_⟩
  intro rows hrows d hd a dmax slotMesh binWidth i z hz hzh
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hconstant : C * (1 + Z ^ (2 * τ)) ^ J ≤
      (C * 2 ^ (J : ℝ)) * Z ^ t := by
    simpa only [Real.rpow_natCast] using
      polynomial_height_absorption C Z τ (J : ℝ) t hC.le hZ hτ.le
        (Nat.cast_nonneg J) hτJ
  have hraw := hb.2 (Z ^ (2 * τ)) (Real.rpow_nonneg hZ0 _) rows hrows d hd
    a τ dmax slotMesh binWidth i z hz hzh
  exact sourceMomentsAt_mono_constant F.modulus ⊤ le_top F.S F.exclusions.prime η
    rows ell (fun _ y => (F.w y : ℂ)) Z d a P.ε τ dmax 2 slotMesh binWidth i z 0
    _ _ (C * (1 + Z ^ (2 * τ)) ^ J) ((C * 2 ^ (J : ℝ)) * Z ^ t)
    (Z ^ (2 * τ)) t hZ0 hconstant hraw

end RH.Transport.PhysicalHigh.DataMoments

theorem solution {Δ : ℝ} {seed : Parameters.HighData Δ} (F : SourceData seed)
    {Kmin : ℕ} {allowance : ℝ} (D : TunedData Kmin allowance)
    (counts : CountParameters F.modulus ⊤ reservedLoss)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta≤7/8) :
    ∃τ : ℝ,0<τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200:ℝ)*D.P.cost ∧
      τ<reservedLoss ∧ 2*τ≤reservedLoss ∧ τ*(2+4*D.P.eps)<reservedLoss ∧
      ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
        1<Z ∧ TunedSourceMomentBound F D counts η Z τ (C*Z^reservedLoss) (Z^(2*τ)) := by
  exact RH.Transport.PhysicalHigh.DataMoments.actual_chosen_moments F D.K D.ell D.slots_pos
    D.slots_injective reservedLoss D.rmin D.ellMin allowance (by norm_num [reservedLoss]) (by norm_num [reservedLoss])
    D.P D.slots_fine counts.cB counts.kB counts.cH counts.kH
    counts.cB_pos counts.kB_pos counts.cH_pos counts.kH_pos hbeta hceiling
