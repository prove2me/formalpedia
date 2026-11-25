-- Prove2me | solution 1 for UpperTheory.beS_constantCoeff_eq_zero_and_wtGe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:45.172343+00:00
-- url     : https://prove2.me/submissions/06698109-5b5b-4eee-9517-b46db856aec9

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_ColDefs
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_BeSConstantCoeffEqZeroAndWtGe
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_one_le_norm_two
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_smul_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_smul_wt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_single
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_monoWtGe_rad
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemmaS
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_substitution_weight_bound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_sum
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_add
import Theorems.Thm_Formalism_G_LogP_hX0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped BigOperators
open Formalism.DworkPowerSeriesWeights Formalism.IncomingBounds UpperTheory.G2
private theorem pos_add_mul {Lt : Type} {i : ℕ} {pos : Lt → ℕ → Lt} (hp : IsPos i pos) (z : Lt) (a k : ℕ) :
    pos z (a + i * k) = pos z a := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, ← hp.add, hp.period, ih]
private theorem pos_congr {Lt : Type} {i : ℕ} {pos : Lt → ℕ → Lt} (hp : IsPos i pos) (z : Lt) {a b : ℕ}
    (h : a ≡ b [MOD 2 * i]) : pos z a = pos z b := by
  have h' : a % i = b % i := Nat.ModEq.of_mul_left 2 h
  rw [← Nat.mod_add_div a i, ← Nat.mod_add_div b i, pos_add_mul hp, pos_add_mul hp, h']
private theorem radii_sum_ge_one_opposite_parity {Lt : Type} {l i : ℕ} [NeZero i] (hl : (1 : ℝ) ≤ l) {pos : Lt → ℕ → Lt} (hp : IsPos i pos)
    {sig : Lt → ℝ} (hs : IsRadii l pos sig) (r : Lt) (s s' : ZMod (2 * i)) (a b : ℕ) (hab : b ≤ a)
    (hpar : s.val % 2 ≠ s'.val % 2) (h : s + (a : ZMod (2 * i)) = s' + (b : ZMod (2 * i))) :
    1 ≤ (l : ℝ) ^ a * sig (pos r s.val) + (l : ℝ) ^ b * sig (pos r s'.val) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hab
  have h1 : ((s.val + e : ℕ) : ZMod (2 * i)) = ((s'.val : ℕ) : ZMod (2 * i)) := by
    push_cast at h ⊢
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination h
  have h2 : s.val + e ≡ s'.val [MOD 2 * i] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
  have h3 : (s.val + e) % 2 = s'.val % 2 := Nat.ModEq.of_mul_right i h2
  have he : Odd e := Nat.odd_iff.mpr (by omega)
  have h4 := hs.2 (pos r s.val) e he
  rw [hp.add, pos_congr hp r h2] at h4
  have h5 : (1 : ℝ) ≤ (l : ℝ) ^ b := one_le_pow₀ hl
  calc (1 : ℝ) = 1 * 1 := (one_mul _).symm
    _ ≤ (l : ℝ) ^ b * ((l : ℝ) ^ e * sig (pos r s.val) + sig (pos r s'.val)) :=
        mul_le_mul h5 h4 zero_le_one (by linarith)
    _ = _ := by ring
end

set_option autoImplicit false
open scoped BigOperators
open Formalism.DworkPowerSeriesWeights Formalism.IncomingBounds UpperTheory.G2
namespace UpperTheory
theorem _root_.solution :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l i : ℕ) [NeZero i], l.Prime → Odd l → ‖(l : K)‖ < 1 →
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ (2 * i) - 1) →
    ∀ (Lt β : Type) [Fintype Lt] [Fintype β] [DecidableEq Lt] [DecidableEq β] (pos : Lt → ℕ → Lt), IsPos i pos →
    ∀ sig : Lt → ℝ, IsRadii l pos sig → ∀ (R : Finset Lt) (sg : Lt → K) (be : Lt → MvPowerSeries (ZMod (2 * i)) K),
    (∀ r ∈ R, sg r = 1 ∨ sg r = -1) → (∀ r ∈ R, BHyp l (2 * i) K0 ζ (be r)) →
    MvPowerSeries.constantCoeff (beS (β := β) i pos R sg be) = 0 ∧
      WtGe ‖(l : K)‖ (fun v : Lt × β => rho l + sig v.1) (1 / ((l : ℝ) - 1)) (beS (β := β) i pos R sg be) := by
  intro K _ _ _ l i _ hl hodd hpi K0 hK0 ζ hζ Lt β _ _ _ _ pos hp sig hs R sg be hsg hbe
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.one_le
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have h1 : ‖(l : K)‖ ≤ 1 := hpi.le
  have hi : 2 ≤ 2 * i := by have := NeZero.pos i; omega
  have hX0 : ∀ (r : Lt) (b : β) (s : ZMod (2 * i)),
      MvPowerSeries.constantCoeff (MvPowerSeries.X (pos r s.val, b) : MvPowerSeries (Lt × β) K) = 0 :=
    fun r b s => MvPowerSeries.constantCoeff_X _
  have hXw : ∀ v : Lt × β, WtGe ‖(l : K)‖ (fun v : Lt × β => rho l + sig v.1) (rho l + sig v.1)
      (MvPowerSeries.X v : MvPowerSeries (Lt × β) K) := by
    intro v n
    rw [monoWtGe_iff, MvPowerSeries.coeff_X]
    split_ifs with h
    · subst h
      rw [asmR_dot_single]
      simp
    · simpa using Real.rpow_nonneg h0.le _
  unfold beS
  constructor
  · rw [map_sum]
    refine Finset.sum_eq_zero fun r hr => asmOne_smul_const _ ?_
    have hbe0 : MvPowerSeries.constantCoeff (be r) = 0 := by
      by_contra h
      have h' : MvPowerSeries.coeff 0 (be r) ≠ 0 := by
        rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      have := ((hbe r hr).2.2.1 0 h').1
      simp [degE] at this
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (hX0 r b)) (hX0 r b) hbe0
  · refine wtGe_sum h0 _ _ fun r hr => ?_
    obtain ⟨hS1, hS2⟩ := lemmaS K l (2 * i) hl hodd hi (even_two_mul i) hpi K0 hK0 ζ hζ (be r) (hbe r hr)
    have hbeR : WtGe ‖(l : K)‖ (fun s : ZMod (2 * i) => rho l + sig (pos r s.val)) (1 / ((l : ℝ) - 1)) (be r) := by
      intro n
      by_cases hb : IsBiPower l n
      · obtain ⟨s, s', α, γ, hs0, hs', _, hsum, rfl⟩ := hb
        have hq : 1 ≤ (l : ℝ) ^ α * sig (pos r s.val) + (l : ℝ) ^ γ * sig (pos r s'.val) := by
          rcases le_total γ α with h | h
          · exact radii_sum_ge_one_opposite_parity hl1 hp hs r s s' α γ h (by omega) hsum
          · rw [add_comm]
            exact radii_sum_ge_one_opposite_parity hl1 hp hs r s' s γ α h (by omega) hsum.symm
        have hn := hS1 (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ γ))
        rw [monoWtGe_iff] at hn ⊢
        refine le_trans hn (Real.rpow_le_rpow_of_exponent_ge h0 h1 ?_)
        simp only [dot_add, asmR_dot_single, Nat.cast_pow]
        linarith
      · exact asmR_monoWtGe_rad h0 h1 (fun s => le_add_of_nonneg_right (hs.1 _)) (hS2 n hb)
    have hsg1 : ‖sg r / 2‖ ≤ 1 := by
      have hs1 : ‖sg r‖ = 1 := by rcases hsg r hr with h | h <;> simp [h]
      have h2 := asmOne_one_le_norm_two (K := K) hodd hpi
      rw [norm_div, hs1]
      exact (div_le_one (lt_of_lt_of_le one_pos h2)).mpr h2
    refine asmOne_smul_wt hsg1 (wtGe_sum h0 _ _ fun b _ => ?_)
    exact substitution_weight_bound K ‖(l : K)‖ h0 hpi (ZMod (2 * i)) (Lt × β) _ _ _ _ (be r) (hX0 r b)
      (fun s => hXw (pos r s.val, b)) hbeR
end UpperTheory
