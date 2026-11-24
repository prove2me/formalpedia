-- Prove2me | solution 1 for TaoFivePrimes.eta0VaughanBilinearSum_eq_centredPairSum
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-21T08:51:49.192196+00:00
-- url     : https://prove2.me/submissions/d0908cc4-16d7-403a-9e0a-d51dc9f48f9c

/-
The platform bilinear sum is the centred pair sum: reindexing and coefficient
identity for the Type II part of Tao's Lemma 4.11. The retained declarations
preserve their original statements and proofs; the file is a reduction-free
adaptation of the public bridge `theorem51TypeII_eq_norm_eta0VaughanBilinearSum`
to the value equality behind it.
-/
import Definitions.Def_TaoFivePrimes_TypeIIChunkInterfaces
set_option autoImplicit false
set_option maxRecDepth 10000
namespace TaoFivePrimes
open scoped BigOperators ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open ArithmeticFunction
@[simp] theorem arithmeticRestrictGT_apply (B n : ℕ)
    (f : ArithmeticFunction ℝ) :
    arithmeticRestrictGT B f n = if B < n then f n else 0 := rfl
theorem truncated_vonMangoldt_divisor_sum_eq_zero_of_le
    (V w : ℕ) (hw : w ≤ V) :
    (arithmeticRestrictGT V ArithmeticFunction.vonMangoldt *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) w = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  rcases Nat.mem_divisors.mp hd with ⟨hdvd, hwne⟩
  have hdle : d ≤ V := by
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hwne) hdvd).trans hw
  simp [arithmeticRestrictGT, Nat.not_lt.mpr hdle]
theorem vaughanTypeIICoefficient_eq_zero_of_le
    (V w : ℕ) (hw : w ≤ V) :
    vaughanTypeIICoefficient V w = 0 := by
  change (arithmeticRestrictGT V ArithmeticFunction.vonMangoldt *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) w -
        (if V < w then (1 / 2 : ℝ) * Real.log w else 0) = 0
  rw [truncated_vonMangoldt_divisor_sum_eq_zero_of_le V w hw,
    if_neg (Nat.not_lt.mpr hw)]
  ring
theorem eta0_eq_zero_of_one_le {y : ℝ} (hy : 1 ≤ y) : eta0 y = 0 := by
  unfold eta0
  rw [if_pos (by linarith)]
  have hlog : Real.log 2 ≤ Real.log (2 * y) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hcut : Real.log 2 - |Real.log (2 * y)| ≤ 0 :=
    sub_nonpos.mpr (hlog.trans (le_abs_self (Real.log (2 * y))))
  rw [max_eq_left hcut, mul_zero]
lemma theorem51Centered_eq_vaughanCoefficient
    (V : ℝ) (hV : 0 ≤ V) (w : ℕ) (hw : V < w) :
    theorem51Centered V w = vaughanTypeIICoefficient ⌊V⌋₊ w := by
  have hw' : ⌊V⌋₊ < w := (Nat.floor_lt hV).2 hw
  change _ = (arithmeticRestrictGT ⌊V⌋₊ ArithmeticFunction.vonMangoldt *
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) w -
      (if ⌊V⌋₊ < w then (1 / 2 : ℝ) * Real.log w else 0)
  rw [if_pos hw', ArithmeticFunction.coe_mul_zeta_apply]
  unfold theorem51Centered
  rw [Finset.sum_filter]
  simp only [arithmeticRestrictGT_apply, Nat.floor_lt hV]
  ring_nf
noncomputable def publicTypeIITerm (x alpha U V : ℝ) (d w : ℕ) : ℂ :=
  if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
    (ArithmeticFunction.moebius d : ℂ) * (theorem51Centered V w : ℂ) *
      expCircle (alpha * d * w) * (eta0 ((d : ℝ) * w / x) : ℂ)
  else 0
lemma publicTypeIITerm_support
    (x alpha U V : ℝ) (hx : 0 < x) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (d w : ℕ) (hne : publicTypeIITerm x alpha U V d w ≠ 0) :
    d ∈ Finset.Ioc 0 ⌊x⌋₊ ∧ w ∈ Finset.Ioc 0 ⌊x⌋₊ ∧ d * w ≤ ⌊x⌋₊ := by
  have hguard : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 := by
    by_contra h
    exact hne (by unfold publicTypeIITerm; rw [if_neg h])
  have hdpos : 0 < d := by exact_mod_cast (hU.trans_lt hguard.1)
  have hwpos : 0 < w := by exact_mod_cast (hV.trans_lt hguard.2.1)
  have hp : (d : ℝ) * w < x := by
    by_contra h
    have heta : eta0 ((d : ℝ) * w / x) = 0 :=
      eta0_eq_zero_of_one_le ((le_div_iff₀ hx).2 (by simpa using le_of_not_gt h))
    exact hne (by simp [publicTypeIITerm, hguard, heta])
  have hpNat : d * w ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx.le).2 (by exact_mod_cast hp.le)
  have hdle : d ≤ d * w := by nlinarith
  have hwle : w ≤ d * w := by nlinarith
  exact ⟨Finset.mem_Ioc.mpr ⟨hdpos, hdle.trans hpNat⟩,
    Finset.mem_Ioc.mpr ⟨hwpos, hwle.trans hpNat⟩, hpNat⟩
lemma publicTypeIITerm_eq_local
    (x alpha U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (d w : ℕ) :
    publicTypeIITerm x alpha U V d w =
      (((arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) d) *
        vaughanTypeIICoefficient ⌊V⌋₊ w : ℝ) : ℂ) *
        eta0VaughanTest x alpha (d * w) := by
  by_cases hd : U < (d : ℝ)
  · have hd' : ⌊U⌋₊ < d := (Nat.floor_lt hU).2 hd
    by_cases hw : V < (w : ℝ)
    · by_cases hdo : d.Coprime 2
      · by_cases hwo : w.Coprime 2
        · have hp : (d * w).Coprime 2 := Nat.coprime_mul_iff_left.mpr ⟨hdo, hwo⟩
          unfold publicTypeIITerm eta0VaughanTest
          rw [if_pos ⟨hd, hw, hdo, hwo⟩, if_pos hp,
            arithmeticRestrictGT_apply, if_pos hd',
            theorem51Centered_eq_vaughanCoefficient V hV w hw]
          simp only [ArithmeticFunction.intCoe_apply]
          push_cast
          ring_nf
        · have hp : ¬(d * w).Coprime 2 := fun h => hwo (Nat.coprime_mul_iff_left.mp h).2
          simp [publicTypeIITerm, hwo, eta0VaughanTest, hp]
      · have hp : ¬(d * w).Coprime 2 := fun h => hdo (Nat.coprime_mul_iff_left.mp h).1
        simp [publicTypeIITerm, hdo, eta0VaughanTest, hp]
    · have hw' : w ≤ ⌊V⌋₊ := Nat.le_of_not_gt (by simpa only [Nat.floor_lt hV] using hw)
      simp [publicTypeIITerm, hw, vaughanTypeIICoefficient_eq_zero_of_le _ _ hw']
  · have hd' : ¬⌊U⌋₊ < d := by simpa only [Nat.floor_lt hU] using hd
    simp [publicTypeIITerm, hd, arithmeticRestrictGT_apply, hd']
theorem bilinear_eq_centredPairSum
    (x alpha U V : ℝ) (hx : 0 < x) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    eta0VaughanBilinearSum x alpha U V =
      ∑' d : ℕ, ∑' w : ℕ, publicTypeIITerm x alpha U V d w := by
  have hs := publicTypeIITerm_support x alpha U V hx hU hV
  have hfinite : (∑' d : ℕ, ∑' w : ℕ, publicTypeIITerm x alpha U V d w) =
      ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ w ∈ Finset.Ioc 0 ⌊x⌋₊,
        publicTypeIITerm x alpha U V d w := by
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) (fun d hd => by
      have hz : ∀ w, publicTypeIITerm x alpha U V d w = 0 := by
        intro w
        by_contra h
        exact hd (hs d w h).1
      simp only [hz, tsum_zero])]
    apply Finset.sum_congr rfl
    intro d hd
    exact tsum_eq_sum (fun w hw => by
      by_contra h
      exact hw (hs d w h).2.1)
  let F : ℕ × ℕ → ℂ := fun p =>
    if p.1 * p.2 ≤ ⌊x⌋₊ then
      (((arithmeticRestrictGT ⌊U⌋₊ (μ : ArithmeticFunction ℝ) p.1) *
        vaughanTypeIICoefficient ⌊V⌋₊ p.2 : ℝ) : ℂ) *
        eta0VaughanTest x alpha (p.1 * p.2)
    else 0
  have hprod : (∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).product (Finset.Ioc 0 ⌊x⌋₊), F p) =
      ∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ w ∈ Finset.Ioc 0 ⌊x⌋₊, F (d, w) :=
    Finset.sum_product (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc 0 ⌊x⌋₊) F
  have hbool : (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ w ∈ Finset.Ioc 0 ⌊x⌋₊,
        publicTypeIITerm x alpha U V d w) =
      ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).product (Finset.Ioc 0 ⌊x⌋₊), F p := by
    rw [hprod]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro w hw
    dsimp only [F]
    by_cases hp : d * w ≤ ⌊x⌋₊
    · rw [if_pos hp]
      exact publicTypeIITerm_eq_local x alpha U V hU hV d w
    · rw [if_neg hp]
      by_contra h
      exact hp (hs d w h).2.2
  rw [hfinite, hbool]
  unfold eta0VaughanBilinearSum
  rw [Finset.sum_filter]
end TaoFivePrimes
open TaoFivePrimes
theorem solution (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    TaoFivePrimes.eta0VaughanBilinearSum x alpha U V =
      ∑' d : ℕ, ∑' w : ℕ,
        (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
            (((TaoFivePrimes.theorem51Centered V w : ℝ)) : ℂ) *
            TaoFivePrimes.expCircle (alpha * d * w) *
            ((TaoFivePrimes.eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
        else 0) := by
  have hmain : TaoFivePrimes.eta0VaughanBilinearSum x alpha U V =
      ∑' d : ℕ, ∑' w : ℕ, publicTypeIITerm x alpha U V d w :=
    bilinear_eq_centredPairSum x alpha U V (by linarith) (by linarith) (by linarith)
  have hterm : ∀ d w : ℕ, publicTypeIITerm x alpha U V d w =
      (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          (((TaoFivePrimes.theorem51Centered V w : ℝ)) : ℂ) *
          TaoFivePrimes.expCircle (alpha * d * w) *
          ((TaoFivePrimes.eta0 ((d : ℝ) * (w : ℝ) / x) : ℝ) : ℂ)
      else 0) := by
    intro d w
    unfold publicTypeIITerm
    by_cases h : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
    · rw [if_pos h]
    · rw [if_neg h]
  rw [hmain]
  exact tsum_congr (fun d => tsum_congr (fun w => hterm d w))
#print axioms solution
