-- Prove2me | solution 1 for P2M_BandParity_odd_subgroup_congruence__298617d94255
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:00:11.049086+00:00
-- url     : https://prove2.me/submissions/0c732435-e474-4e8a-88cd-70a5fcccc1ea

module
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_OddSubgroup
public import Theorems.Thm_BandParity_uSign_eq
public import Theorems.Thm_P2M_BandParity_cosetBandSum_eq__5f1f29a5d302
public import Theorems.Thm_BandParity_card_coset
public import Theorems.Thm_BandParity_sum_uSign
public import Theorems.Thm_BandParity_odd_card_powKer
public import Theorems.Thm_BandParity_card_filter_pow
public import Theorems.Thm_BandParity_sum_sign_mul_modEq


set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {N : ℕ} [NeZero N]
variable (hN : Odd N) (hN3 : 3 ≤ N)
include hN hN3
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hH
namespace BandParity
theorem _root_.solution (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e ≡
      (Nat.card H : ℤ) - 2 * oddCount (coset H x) - 2 * oddCount ((coset H x).image (· ^ e))
      [ZMOD 4] := by
  rw [cosetBandSum_eq' hN hN3 hH x he he0]
  have hm := sum_sign_mul_modEq (coset H x) uSign (fun u => uSign (u ^ e))
    (fun u _ => uSign_eq u) (fun u _ => uSign_eq _)
  have h1 := sum_uSign (coset H x)
  have h2 : ∑ u ∈ coset H x, uSign (u ^ e) =
      ((coset H x).card : ℤ) - 2 * ((powKer H e).card * oddCount ((coset H x).image (· ^ e))) := by
    have : ∀ u : (ZMod N)ˣ, uSign (u ^ e) =
        1 - 2 * (if Odd ((u ^ e : (ZMod N)ˣ) : ZMod N).val then 1 else 0) := by
      intro u; unfold uSign
      rcases Nat.even_or_odd ((u ^ e : (ZMod N)ˣ) : ZMod N).val with h | h
      · rw [h.neg_one_pow]; split_ifs with hh
        · exact absurd hh (Nat.not_odd_iff_even.2 h)
        · ring
      · rw [h.neg_one_pow]; split_ifs; ring
    have hcf := card_filter_pow (H := H) x e (fun y : (ZMod N)ˣ => Odd (y : ZMod N).val)
    rw [Finset.sum_congr rfl (fun u _ => this u), Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_boole, oddCount]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcf]; push_cast; ring
  rw [h1, h2, card_coset] at hm
  refine hm.trans ?_
  obtain ⟨c, hc⟩ := odd_card_powKer hH e
  rw [hc]
  exact Int.modEq_iff_dvd.2 ⟨c * oddCount ((coset H x).image (· ^ e)), by push_cast; ring⟩
end BandParity
