-- Prove2me | solution 1 for TwoStageRnQ.classical_ship_le_lot
-- status  : ACCEPTED   (prove)
-- author  : @beatlesmania
-- created : 2026-11-17T00:27:16.367555+00:00
-- url     : https://prove2.me/submissions/b13918d3-13d6-4185-b4a5-6e664bc54510

import Definitions.Def_TwoStageRnQ_Model
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_TwoStageRnQ_Model

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

lemma ncard_Ioc_int (a b : ℤ) : (Set.Ioc a b).ncard = (b - a).toNat := by
  rw [← Finset.coe_Ioc, Set.ncard_coe_finset, Int.card_Ioc]

lemma jumpCount_le_toNat {f : ℝ → ℤ} {T : ℝ} (φ : ℝ → ℤ) (a b : ℤ)
    (hmem : ∀ t, t ∈ Set.Ioc 0 T → (∀ s < t, f s < f t) → a < φ t ∧ φ t ≤ b)
    (hφ : ∀ t₁ t₂, t₁ ∈ Set.Ioc 0 T → t₂ ∈ Set.Ioc 0 T → f t₁ < f t₂ → φ t₁ < φ t₂) :
    jumpCount f T ≤ (b - a).toNat := by
  unfold jumpCount
  rw [← ncard_Ioc_int a b]
  refine Set.ncard_le_ncard_of_injOn φ (fun t ht => ?_) (fun t₁ h₁ t₂ h₂ heq => ?_)
    (Set.finite_Ioc a b)
  · exact hmem t ht.1 ht.2
  · rcases lt_trichotomy t₁ t₂ with h | h | h
    · exact absurd heq (ne_of_lt (hφ t₁ t₂ h₁.1 h₂.1 (h₂.2 t₁ h)))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hφ t₂ t₁ h₂.1 h₁.1 (h₁.2 t₂ h)))

lemma jumpCount_le_real {f : ℝ → ℤ} {T : ℝ} (φ : ℝ → ℤ) (a b : ℤ) (hab : a ≤ b)
    (hmem : ∀ t, t ∈ Set.Ioc 0 T → (∀ s < t, f s < f t) → a < φ t ∧ φ t ≤ b)
    (hφ : ∀ t₁ t₂, t₁ ∈ Set.Ioc 0 T → t₂ ∈ Set.Ioc 0 T → f t₁ < f t₂ → φ t₁ < φ t₂) :
    (jumpCount f T : ℝ) ≤ ((b - a : ℤ) : ℝ) := by
  have h := jumpCount_le_toNat φ a b hmem hφ
  have h' : ((jumpCount f T : ℕ) : ℤ) ≤ b - a := by
    have := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
    omega
  exact_mod_cast h'

lemma jumpCount_mul_le {g : ℝ → ℤ} (hg : Monotone g) (q : ℤ) (hq : 0 < q) {T : ℝ} (hT : 0 ≤ T) :
    (jumpCount (fun t => q * g t) T : ℝ) ≤ ((g T - g 0 : ℤ) : ℝ) := by
  refine jumpCount_le_real g (g 0) (g T) (hg hT) (fun t ht hj => ?_) (fun t₁ t₂ _ _ h => ?_)
  · refine ⟨?_, hg ht.2⟩
    have := hj 0 ht.1
    exact lt_of_mul_lt_mul_left this hq.le
  · exact lt_of_mul_lt_mul_left h hq.le

lemma jumpCount_lot_le {f : ℝ → ℤ} (hf : Monotone f) (q : ℤ) (hq : 0 < q)
    (hdvd : ∀ s t, s ≤ t → q ∣ f t - f s) {T : ℝ} (hT : 0 ≤ T) :
    (jumpCount f T : ℝ) ≤ ((f T - f 0 : ℤ) : ℝ) / (q : ℝ) := by
  have hdiv : ∀ t, 0 ≤ t → (f t - f 0) = q * ((f t - f 0) / q) := fun t ht =>
    (Int.mul_ediv_cancel' (hdvd 0 t ht)).symm
  have hb : 0 ≤ (f T - f 0) / q := Int.ediv_nonneg (sub_nonneg.mpr (hf hT)) hq.le
  have key := jumpCount_le_real (f := f) (T := T) (fun t => (f t - f 0) / q) 0 ((f T - f 0) / q) hb
    (fun t ht hj => ?_) (fun t₁ t₂ h₁ h₂ h => ?_)
  · rw [sub_zero] at key
    rw [Int.cast_div (hdvd 0 T hT) (by exact_mod_cast hq.ne')] at key
    exact key
  · have h0 : f 0 < f t := hj 0 ht.1
    have e := hdiv t ht.1.le
    refine ⟨?_, Int.ediv_le_ediv hq (by linarith [hf ht.2])⟩
    by_contra hneg
    rw [not_lt] at hneg
    have : q * ((f t - f 0) / q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq.le hneg
    linarith
  · have e₁ := hdiv t₁ h₁.1.le
    have e₂ := hdiv t₂ h₂.1.le
    by_contra hneg
    rw [not_lt] at hneg
    have : q * ((f t₂ - f 0) / q) ≤ q * ((f t₁ - f 0) / q) := mul_le_mul_of_nonneg_left hneg hq.le
    linarith

lemma longRunCost_mono {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (cI : ℝ → Ω → ℝ)
    {Z Z' : ℝ → Ω → ℝ} (h : ∀ T, 0 ≤ T → ∀ ω, Z T ω ≤ Z' T ω) :
    longRunCost ν cI Z ≤ longRunCost ν cI Z' := by
  unfold longRunCost
  refine Filter.limsup_le_limsup ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  gcongr with ω
  exact h T hT ω

end TwoStageRnQ

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

section ClassicalMono

variable {P : Params} (S : DemandSpace P) (c : ClassicalControls)

lemma Classical'.reqCount_mono (ω : S.Ω) : Monotone (fun t => Classical'.reqCount S c t ω) := by
  intro s t hst
  unfold Classical'.reqCount
  apply Int.floor_mono
  have hQ : (0 : ℝ) < ((c.1.2.2.1 : ℕ) : ℝ) := by exact_mod_cast c.1.2.2.1.pos
  have := S.N_mono ω hst
  gcongr

lemma Classical'.ordCount_mono (ω : S.Ω) : Monotone (fun t => Classical'.ordCount S c t ω) := by
  intro s t hst
  unfold Classical'.ordCount
  apply Int.floor_mono
  have hQ : (0 : ℝ) < ((c.1.2.2.1 : ℕ) : ℝ) := by exact_mod_cast c.1.2.2.1.pos
  have hn : (0 : ℝ) < ((c.1.2.2.2.1 : ℕ) : ℝ) := by exact_mod_cast c.1.2.2.2.1.pos
  have := S.N_mono ω hst
  have h' : ((S.N s ω : ℤ) : ℝ) ≤ ((S.N t ω : ℤ) : ℝ) := by exact_mod_cast this
  gcongr

lemma Classical'.matchCount_mono (ω : S.Ω) :
    Monotone (fun t => Classical'.matchCount S c t ω) := by
  intro s t hst
  unfold Classical'.matchCount Classical'.recvCount
  have h1 := Classical'.reqCount_mono S c ω hst
  have h2 := Classical'.ordCount_mono S c ω (by linarith : s - P.L2 ≤ t - P.L2)
  have hn : (0 : ℤ) ≤ ((c.1.2.2.2.1 : ℕ) : ℤ) := by positivity
  exact min_le_min h1 (mul_le_mul_of_nonneg_left h2 hn)

end ClassicalMono

theorem classical_ship_le_lot_pf (P : Params) (S : DemandSpace P) (c : ClassicalControls) :
    classicalShipCost P S c ≤ classicalLotCost P S c := by
  unfold classicalShipCost classicalLotCost
  refine longRunCost_mono _ _ (fun T hT ω => ?_)
  have hQ : (0 : ℤ) < ((c.1.2.2.1 : ℕ) : ℤ) := by exact_mod_cast c.1.2.2.1.pos
  have hn : (0 : ℤ) < ((c.1.2.2.2.1 : ℕ) : ℤ) := by exact_mod_cast c.1.2.2.2.1.pos
  have j1 : (jumpCount (fun t => Classical'.U1 S c t ω) T : ℝ)
      ≤ ((Classical'.matchCount S c T ω - Classical'.matchCount S c 0 ω : ℤ) : ℝ) :=
    jumpCount_mul_le (g := fun t => Classical'.matchCount S c t ω)
      (Classical'.matchCount_mono S c ω) _ hQ hT
  have j2 : (jumpCount (fun t => Classical'.U2 S c t ω) T : ℝ)
      ≤ ((Classical'.ordCount S c T ω - Classical'.ordCount S c 0 ω : ℤ) : ℝ) :=
    jumpCount_mul_le (g := fun t => Classical'.ordCount S c t ω)
      (Classical'.ordCount_mono S c ω) _ (mul_pos hn hQ) hT
  have k1 := P.K1_nonneg
  have k2 := P.K2_nonneg
  have := mul_le_mul_of_nonneg_left j1 k1
  have := mul_le_mul_of_nonneg_left j2 k2
  linarith

theorem cost_order_pf (P : Params) : OPTsh P ≤ OPTlot P := by
  unfold OPTlot
  refine le_iInf fun S => le_iInf fun π => le_iInf fun q => le_iInf fun hq => le_iInf fun hadm => ?_
  have hq1 : (0 : ℤ) < ((q.1 : ℕ) : ℤ) := by exact_mod_cast q.1.pos
  have hq2 : (0 : ℤ) < ((q.2 : ℕ) : ℤ) := by exact_mod_cast q.2.pos
  have hZ : ∀ T, 0 ≤ T → ∀ ω, π.shipSetup T ω ≤ π.lotSetup q T ω := by
    intro T hT ω
    unfold ShipmentPolicy.shipSetup ShipmentPolicy.lotSetup
    have j1 := jumpCount_lot_le (f := fun t => π.U1 t ω) (π.U1_mono ω) _ hq1
      (fun s t hst => (hq ω s t hst).1) hT
    have j2 := jumpCount_lot_le (f := fun t => π.U2 t ω) (π.U2_mono ω) _ hq2
      (fun s t hst => (hq ω s t hst).2) hT
    have k1 := P.K1_nonneg
    have k2 := P.K2_nonneg
    have := mul_le_mul_of_nonneg_left j1 k1
    have := mul_le_mul_of_nonneg_left j2 k2
    push_cast at *
    linarith
  have hadm' : π.Admissible π.shipSetup :=
    { hadm with
      finite_horizon := fun T hT => lt_of_le_of_lt (by
          gcongr with ω
          exact hZ T hT ω) (hadm.finite_horizon T hT) }
  calc OPTsh P ≤ π.shipCost := iInf_le_of_le S (iInf_le_of_le π (iInf_le_of_le hadm' le_rfl))
    _ ≤ π.lotCost q := longRunCost_mono _ _ hZ

end TwoStageRnQ

namespace TwoStageRnQ

theorem _root_.solution (P : Params) (S : DemandSpace P) (c : ClassicalControls) :
    classicalShipCost P S c ≤ classicalLotCost P S c :=
  classical_ship_le_lot_pf P S c

end TwoStageRnQ
