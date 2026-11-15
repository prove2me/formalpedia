-- Prove2me | solution 1 for RH.Transport.PhysicalHigh.exists_tuned_data
-- status  : ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T03:41:06.174916+00:00
-- url     : https://prove2.me/submissions/d30b2017-fe47-4838-9faf-021f17a84acb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Definitions.Def_Transport_PhysicalHigh_TunedData
import Theorems.Thm_RH_Transport_PhysicalHigh_fine_even_slot_count
import Theorems.Thm_RH_Transport_PhysicalHigh_distinct_slots_for_size
import Theorems.Thm_RH_Transport_PhysicalHigh_exists_detector_scales_after_slots

set_option autoImplicit false

/-! The first sections are the mesh positivity lemmas of OpenAI's family-003 development
(openai/math, Apache-2.0), as carried in the accepted platform proof of
`OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction.certified_floor`. The last
section is LW56e2, `Transport/PhysicalHigh/EnergyMesh.lean` and `TunedData.lean`. -/

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstSecondLossParameters
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstSecondLossParameters

lemma depth_covers (Mcap σ:ℝ)(hσ:0<σ):Mcap<(depth Mcap σ:ℝ)*σ/2 := by
  have hh:=Nat.le_ceil (2*Mcap/σ)
  have hn:2*Mcap≤(⌈2*Mcap/σ⌉₊:ℝ)*σ:=(div_le_iff₀ hσ).mp hh
  simp only [depth,Nat.cast_add,Nat.cast_one]
  nlinarith

end SevenEighths.CenteredMomentFirstSecondLossParameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SuccessorPaidParameters
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentSuccessorPaidParameters
open CenteredMomentFirstSecondLossParameters

lemma mesh_cost (kappa reserve : ℝ) (hk : 0≤kappa) (hr : 0≤ reserve) :
    kappa*(reserve/(kappa+1))≤ reserve := by
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0<kappa+1)).mpr
  nlinarith

end SevenEighths.CenteredMomentSuccessorPaidParameters

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.WidthSchedule
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyWidthSchedule
open CenteredMomentSuccessorPaidParameters CenteredMomentFirstSecondLossParameters

theorem bounds (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
    0<amplification ε ∧ amplification ε≤1 ∧ amplification ε≤ε/16000 ∧
    0< reserve M B ε ∧ 0< mesh M B κ ε ∧ mesh M B κ ε≤ reserve M B ε ∧
    κ*mesh M B κ ε≤ reserve M B ε ∧
    20*reserve M B ε≤amplification ε/2 ∧
    M<width M B ε (count M ε) ∧
    loss M B ε (count M ε)≤ε/1000 :=by
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  have hs1:amplification ε≤1:=min_le_left _ _
  have hse:amplification ε≤ε/16000:=min_le_right _ _
  have hn:0≤(count M ε:ℝ):=Nat.cast_nonneg _
  have hL:0<scale M B ε:=by unfold scale;positivity
  have hr:0< reserve M B ε:=lt_min (by positivity) (by positivity)
  have hrs:reserve M B ε≤amplification ε/100:=min_le_left _ _
  have hre:reserve M B ε≤ε/(1000000*scale M B ε):=min_le_right _ _
  have hp:reserve M B ε*(1000000*scale M B ε)≤ε:=
    (le_div_iff₀ (by positivity)).mp hre
  have hnL:(count M ε:ℝ)≤ scale M B ε:=by unfold scale;linarith
  have h1L:1≤ scale M B ε:=by unfold scale;linarith
  have hnR:(count M ε:ℝ)*reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right hnL hr.le
    nlinarith
  have hR:reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right h1L hr.le
    nlinarith
  have hm:0< mesh M B κ ε:=by unfold mesh;positivity
  have hmr:mesh M B κ ε≤ reserve M B ε:=by
    unfold mesh
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hkm:κ*mesh M B κ ε≤ reserve M B ε:=mesh_cost κ _ hκ hr.le
  have hw:M<width M B ε (count M ε):=by
    have hd:=depth_covers M (amplification ε) hs
    change M<(count M ε:ℝ)*amplification ε/2 at hd
    unfold width
    linarith
  refine ⟨hs,hs1,hse,hr,hm,hmr,hkm,by linarith,hw,?_⟩
  unfold loss
  linarith

lemma width_zero (M B ε:ℝ):width M B ε 0=reserve M B ε/16:=by simp [width]
lemma loss_zero (M B ε:ℝ):loss M B ε 0=reserve M B ε:=by simp [loss]

end SevenEighths.CenteredMomentEnergyWidthSchedule

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.Profiles
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentEnergyProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalSource
open CenteredMomentScaleSupremum

lemma lower_pos (a b:ℝ)(ha:0<a)(n:ℕ):0<lower a b n:=by
  induction n with
  | zero=>exact ha
  | succ n ih=>exact div_pos ih (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

end SevenEighths.CenteredMomentEnergyProfiles

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Energy.WidthRanges
namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyProfiles CenteredMomentEnergyWidthSchedule

lemma range_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤ range M B L n:=by
  induction n with
  | zero=>exact zero_le_one.trans (le_max_left _ _)
  | succ n ih=>simp only [range,step];positivity

lemma sourceCap_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤ sourceCap M B L n:=by
  have hr:=range_nonneg M B L hM hB n
  unfold sourceCap
  positivity

end SevenEighths.CenteredMomentEnergyWidthRanges

end

end OAI
end

section
namespace RH.Transport.PhysicalHigh
noncomputable section
open scoped BigOperators
open OAI OAI.SevenEighths
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges

lemma plainMesh_pos {εm:ℝ}(hεm:0<εm):0<plainMesh εm:=by
  exact (bounds 2 (finalSourceCap 2 0 1 (εm/4)) (3/4) (εm/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by norm_num) (by positivity)).2.2.2.2.1

lemma reservedLoss_pos : 0 < reservedLoss := by norm_num
lemma reservedLoss_le_one : reservedLoss ≤ 1 := by norm_num
lemma conductorCap_pos : 0 < conductorCap := by
  norm_num [conductorCap, TunedCandidate.h, TunedCandidate.hAt, TunedCandidate.ell,
    Geometry.ell, TunedCandidate.p, TunedCandidate.b, TunedCandidate.zeta]

theorem exists_tuned_data_src (Kmin : ℕ) (allowance : ℝ) (ha : 0 < allowance) :
    Nonempty (TunedData Kmin allowance) := by
  have htotal : 0 < TunedCandidate.ell := by
    norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]
  let cap := min (reservedLoss / 200) (plainMesh reservedLoss / 200)
  have hcap : 0 < cap := lt_min (by norm_num) (div_pos (plainMesh_pos reservedLoss_pos) (by norm_num))
  obtain ⟨K, hKmin, hK, hEven, hcapK⟩ := fine_even_slot_count cap hcap Kmin
  let ell := Classical.choose (distinct_slots_for_size TunedCandidate.ell htotal K hK)
  have hell := Classical.choose_spec (distinct_slots_for_size TunedCandidate.ell htotal K hK)
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  let ellMin := TunedCandidate.ell / (2 * K)
  let rmin := ellMin / conductorCap
  have hmin : 0 < ellMin := div_pos htotal (by positivity)
  have hr : 0 < rmin := div_pos hmin conductorCap_pos
  obtain ⟨P⟩ := exists_detector_scales_after_slots reservedLoss rmin ellMin allowance K
    reservedLoss_pos reservedLoss_le_one hr hmin ha
  refine ⟨{
    K := K, K_large := hKmin, K_pos := hK, K_even := hEven
    ell := ell, ellMin := ellMin, rmin := rmin
    ellMin_eq := rfl, rmin_eq := rfl, ellMin_pos := hmin, rmin_pos := hr
    slots_injective := hell.1, slots_sum := hell.2.1
    slots_pos := fun j => hmin.trans_le (hell.2.2 j).1
    slots_lower := fun j => (hell.2.2 j).1
    slots_upper := ?_, slots_fine := ?_, P := P }⟩
  · intro j
    have hb := ((hell.2.2 j).2.le.trans hcapK).trans (min_le_left _ _)
    change ell j ≤ reservedLoss / 200 at hb
    convert hb using 1 <;> ring
  · intro j
    exact ((hell.2.2 j).2.le.trans hcapK).trans (min_le_right _ _)

end
end RH.Transport.PhysicalHigh
end

open RH RH.Transport RH.Transport.PhysicalHigh
open scoped BigOperators
noncomputable section
theorem solution (Kmin : ℕ) (allowance : ℝ) (ha : 0 < allowance) :
    Nonempty (TunedData Kmin allowance) :=
  RH.Transport.PhysicalHigh.exists_tuned_data_src Kmin allowance ha
