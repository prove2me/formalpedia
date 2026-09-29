-- Prove2me | solution 1 for TarchaBraids.thm_3_15_half_twists_far_commute_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T07:17:39.488946+00:00
-- url     : https://prove2.me/submissions/ea820150-b92b-48d9-8ad6-aaaeaa61fae3

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
namespace TarchaBraids
open BraidsLinksMCG
noncomputable section
lemma mul_mem_unit_interval {a b : ℝ}
    (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hb1 : -1 ≤ b) (hb2 : b ≤ 1) :
    -1 ≤ a * b ∧ a * b ≤ 1 := by
  have ha : |a| ≤ 1 := abs_le.mpr ⟨ha1, ha2⟩
  have hb : |b| ≤ 1 := abs_le.mpr ⟨hb1, hb2⟩
  have habs : |a * b| ≤ 1 := by
    rw [abs_mul]
    calc
      |a| * |b| ≤ 1 * 1 := mul_le_mul ha hb (abs_nonneg b) (by norm_num)
      _ = 1 := by norm_num
  exact abs_le.mp habs
lemma twistPoint_far_ne {n : ℕ} (i j : Fin (n - 1))
    (si sj ti tj : ℝ) (hsi1 : -1 ≤ si) (hsi2 : si ≤ 1)
    (hsj1 : -1 ≤ sj) (hsj2 : sj ≤ 1)
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    twistPoint ((i : ℕ) + 3 / 2) si ti ≠
      twistPoint ((j : ℕ) + 3 / 2) sj tj := by
  intro h
  have hci1 := Real.neg_one_le_cos (Real.pi * ti)
  have hci2 := Real.cos_le_one (Real.pi * ti)
  have hcj1 := Real.neg_one_le_cos (Real.pi * tj)
  have hcj2 := Real.cos_le_one (Real.pi * tj)
  have hpi := mul_mem_unit_interval hsi1 hsi2 hci1 hci2
  have hpj := mul_mem_unit_interval hsj1 hsj2 hcj1 hcj2
  have hpi1 : -1 ≤ si * Real.cos (Real.pi * ti) := hpi.1
  have hpi2 : si * Real.cos (Real.pi * ti) ≤ 1 := hpi.2
  have hpj1 : -1 ≤ sj * Real.cos (Real.pi * tj) := hpj.1
  have hpj2 : sj * Real.cos (Real.pi * tj) ≤ 1 := hpj.2
  have hre :
      ((i : ℕ) : ℝ) + 3 / 2 + si * Real.cos (Real.pi * ti) / 2 =
        ((j : ℕ) : ℝ) + 3 / 2 + sj * Real.cos (Real.pi * tj) / 2 := by
    simpa using congrArg Complex.re h
  have hijR : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) + 1 := by
    nlinarith
  have hjiR : ((j : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) + 1 := by
    nlinarith
  have hijN : (i : ℕ) ≤ (j : ℕ) + 1 := by
    exact_mod_cast hijR
  have hjiN : (j : ℕ) ≤ (i : ℕ) + 1 := by
    exact_mod_cast hjiR
  have hcases :
      (i : ℕ) = (j : ℕ) ∨
      (i : ℕ) = (j : ℕ) + 1 ∨
      (j : ℕ) = (i : ℕ) + 1 := by
    omega
  rcases hcases with heq | hsucc | hpred
  · have hz : (i : ℤ) - (j : ℤ) = 0 := by
      have h' : (i : ℤ) = (j : ℤ) := by exact_mod_cast heq
      omega
    rw [hz] at hij
    norm_num at hij
  · have hz : (i : ℤ) - (j : ℤ) = 1 := by
      have h' : (i : ℤ) = (j : ℤ) + 1 := by exact_mod_cast hsucc
      omega
    rw [hz] at hij
    norm_num at hij
  · have hz : (i : ℤ) - (j : ℤ) = -1 := by
      have h' : (j : ℤ) = (i : ℤ) + 1 := by exact_mod_cast hpred
      omega
    rw [hz] at hij
    norm_num at hij
def doubleTwistFun (n : ℕ) (i j : Fin (n - 1)) (s t : ℝ) (k : Fin n) : ℂ :=
  if (k : ℕ) = (i : ℕ) then
    twistPoint ((i : ℕ) + 3 / 2) (-1) s
  else if (k : ℕ) = (i : ℕ) + 1 then
    twistPoint ((i : ℕ) + 3 / 2) 1 s
  else
    halfTwistFun n j t k
lemma doubleTwistFun_of_eq {n : ℕ} {i j : Fin (n - 1)} {k : Fin n}
    (s t : ℝ) (h : (k : ℕ) = (i : ℕ)) :
    doubleTwistFun n i j s t k = twistPoint ((i : ℕ) + 3 / 2) (-1) s := by
  simp [doubleTwistFun, h]
lemma doubleTwistFun_of_eq_succ {n : ℕ} {i j : Fin (n - 1)} {k : Fin n}
    (s t : ℝ) (h1 : (k : ℕ) ≠ (i : ℕ)) (h2 : (k : ℕ) = (i : ℕ) + 1) :
    doubleTwistFun n i j s t k = twistPoint ((i : ℕ) + 3 / 2) 1 s := by
  simp [doubleTwistFun, h1, h2]
lemma doubleTwistFun_of_outside {n : ℕ} {i j : Fin (n - 1)} {k : Fin n}
    (s t : ℝ) (h1 : (k : ℕ) ≠ (i : ℕ)) (h2 : (k : ℕ) ≠ (i : ℕ) + 1) :
    doubleTwistFun n i j s t k = halfTwistFun n j t k := by
  simp [doubleTwistFun, h1, h2]
lemma doubleTwist_inside_ne_outside {n : ℕ} (i j : Fin (n - 1))
    (s t sign : ℝ) (hsign : sign = -1 ∨ sign = 1)
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs)
    (l : Fin n) (hli : (l : ℕ) ≠ (i : ℕ))
    (hlis : (l : ℕ) ≠ (i : ℕ) + 1) :
    twistPoint ((i : ℕ) + 3 / 2) sign s ≠ halfTwistFun n j t l := by
  rcases hsign with rfl | rfl
  · by_cases hlj : (l : ℕ) = (j : ℕ)
    · rw [halfTwistFun_of_eq t hlj]
      exact twistPoint_far_ne i j (-1) (-1) s t (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hij
    · by_cases hljs : (l : ℕ) = (j : ℕ) + 1
      · rw [halfTwistFun_of_eq_succ t hlj hljs]
        exact twistPoint_far_ne i j (-1) 1 s t (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) hij
      · rw [halfTwistFun_of_fixed t hlj hljs]
        exact twistPoint_ne_fixed (-1) s (by norm_num) (by norm_num) hli hlis
  · by_cases hlj : (l : ℕ) = (j : ℕ)
    · rw [halfTwistFun_of_eq t hlj]
      exact twistPoint_far_ne i j 1 (-1) s t (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hij
    · by_cases hljs : (l : ℕ) = (j : ℕ) + 1
      · rw [halfTwistFun_of_eq_succ t hlj hljs]
        exact twistPoint_far_ne i j 1 1 s t (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) hij
      · rw [halfTwistFun_of_fixed t hlj hljs]
        exact twistPoint_ne_fixed 1 s (by norm_num) (by norm_num) hli hlis
lemma doubleTwistFun_injective (n : ℕ) (i j : Fin (n - 1)) (s t : ℝ)
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    Function.Injective (doubleTwistFun n i j s t) := by
  intro k l hkl
  by_cases hk1 : (k : ℕ) = (i : ℕ)
  · by_cases hl1 : (l : ℕ) = (i : ℕ)
    · exact Fin.ext (hk1.trans hl1.symm)
    · by_cases hl2 : (l : ℕ) = (i : ℕ) + 1
      · rw [doubleTwistFun_of_eq s t hk1,
          doubleTwistFun_of_eq_succ s t hl1 hl2] at hkl
        exact absurd hkl (twistPoint_ne_twistPoint _ _)
      · rw [doubleTwistFun_of_eq s t hk1,
          doubleTwistFun_of_outside s t hl1 hl2] at hkl
        exact absurd hkl
          (doubleTwist_inside_ne_outside i j s t (-1) (Or.inl rfl) hij l hl1 hl2)
  · by_cases hk2 : (k : ℕ) = (i : ℕ) + 1
    · by_cases hl1 : (l : ℕ) = (i : ℕ)
      · rw [doubleTwistFun_of_eq_succ s t hk1 hk2,
          doubleTwistFun_of_eq s t hl1] at hkl
        exact absurd hkl.symm (twistPoint_ne_twistPoint _ _)
      · by_cases hl2 : (l : ℕ) = (i : ℕ) + 1
        · exact Fin.ext (hk2.trans hl2.symm)
        · rw [doubleTwistFun_of_eq_succ s t hk1 hk2,
            doubleTwistFun_of_outside s t hl1 hl2] at hkl
          exact absurd hkl
            (doubleTwist_inside_ne_outside i j s t 1 (Or.inr rfl) hij l hl1 hl2)
    · by_cases hl1 : (l : ℕ) = (i : ℕ)
      · rw [doubleTwistFun_of_outside s t hk1 hk2,
          doubleTwistFun_of_eq s t hl1] at hkl
        exact absurd hkl.symm
          (doubleTwist_inside_ne_outside i j s t (-1) (Or.inl rfl) hij k hk1 hk2)
      · by_cases hl2 : (l : ℕ) = (i : ℕ) + 1
        · rw [doubleTwistFun_of_outside s t hk1 hk2,
            doubleTwistFun_of_eq_succ s t hl1 hl2] at hkl
          exact absurd hkl.symm
            (doubleTwist_inside_ne_outside i j s t 1 (Or.inr rfl) hij k hk1 hk2)
        · rw [doubleTwistFun_of_outside s t hk1 hk2,
            doubleTwistFun_of_outside s t hl1 hl2] at hkl
          exact halfTwistFun_injective n j t hkl
def doubleTwistConfig (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) (s t : ℝ) : OrderedConfig n :=
  ⟨doubleTwistFun n i j s t, doubleTwistFun_injective n i j s t hij⟩
lemma continuous_doubleTwistConfig (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    Continuous (fun x : ℝ × ℝ => doubleTwistConfig n i j hij x.1 x.2) := by
  apply Continuous.subtype_mk
  refine continuous_pi fun k => ?_
  change Continuous (fun x : ℝ × ℝ => doubleTwistFun n i j x.1 x.2 k)
  simp only [doubleTwistFun, halfTwistFun, twistPoint]
  split_ifs
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · exact continuous_const
lemma far_nat_ne_00 {n : ℕ} (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) : (i : ℕ) ≠ (j : ℕ) := by
  intro h
  have h' : (i : ℤ) = (j : ℤ) := by exact_mod_cast h
  have hz : (i : ℤ) - (j : ℤ) = 0 := by omega
  rw [hz] at hij
  norm_num at hij
lemma far_nat_ne_01 {n : ℕ} (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) : (i : ℕ) ≠ (j : ℕ) + 1 := by
  intro h
  have h' : (i : ℤ) = (j : ℤ) + 1 := by exact_mod_cast h
  have hz : (i : ℤ) - (j : ℤ) = 1 := by omega
  rw [hz] at hij
  norm_num at hij
lemma far_nat_ne_10 {n : ℕ} (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) : (i : ℕ) + 1 ≠ (j : ℕ) := by
  intro h
  have h' : (i : ℤ) + 1 = (j : ℤ) := by exact_mod_cast h
  have hz : (i : ℤ) - (j : ℤ) = -1 := by omega
  rw [hz] at hij
  norm_num at hij
lemma far_nat_ne_11 {n : ℕ} (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) : (i : ℕ) + 1 ≠ (j : ℕ) + 1 := by
  intro h
  have h' : (i : ℕ) = (j : ℕ) := by omega
  exact far_nat_ne_00 i j hij h'
lemma far_swap_j_preserves_i_outside {n : ℕ} (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) (k : Fin n)
    (hk0 : (k : ℕ) ≠ (i : ℕ)) (hk1 : (k : ℕ) ≠ (i : ℕ) + 1) :
    (((Equiv.swap (strandIdx j) (strandIdxSucc j)) k : Fin n) : ℕ) ≠ (i : ℕ) ∧
      (((Equiv.swap (strandIdx j) (strandIdxSucc j)) k : Fin n) : ℕ) ≠ (i : ℕ) + 1 := by
  by_cases hkj0 : (k : ℕ) = (j : ℕ)
  · have hk : k = strandIdx j := Fin.ext (by simpa [strandIdx] using hkj0)
    subst k
    rw [Equiv.swap_apply_left]
    constructor
    · simpa [strandIdxSucc] using (far_nat_ne_01 i j hij).symm
    · simpa [strandIdxSucc] using (far_nat_ne_11 i j hij).symm
  · by_cases hkj1 : (k : ℕ) = (j : ℕ) + 1
    · have hk : k = strandIdxSucc j := Fin.ext (by simpa [strandIdxSucc] using hkj1)
      subst k
      rw [Equiv.swap_apply_right]
      constructor
      · simpa [strandIdx] using (far_nat_ne_00 i j hij).symm
      · simpa [strandIdx] using (far_nat_ne_10 i j hij).symm
    · have hk0' : k ≠ strandIdx j := by
        intro hk
        exact hkj0 (by simpa [strandIdx] using congrArg Fin.val hk)
      have hk1' : k ≠ strandIdxSucc j := by
        intro hk
        exact hkj1 (by simpa [strandIdxSucc] using congrArg Fin.val hk)
      rw [Equiv.swap_apply_of_ne_of_ne hk0' hk1']
      exact ⟨hk0, hk1⟩
lemma doubleTwistConfig_zero_right (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) (s : ℝ) :
    doubleTwistConfig n i j hij s 0 = halfTwistConfig n i s := by
  apply Subtype.ext
  funext k
  by_cases hk0 : (k : ℕ) = (i : ℕ)
  · rw [show (doubleTwistConfig n i j hij s 0).1 k = doubleTwistFun n i j s 0 k from rfl,
      doubleTwistFun_of_eq s 0 hk0,
      show (halfTwistConfig n i s).1 k = halfTwistFun n i s k from rfl,
      halfTwistFun_of_eq s hk0]
  · by_cases hk1 : (k : ℕ) = (i : ℕ) + 1
    · rw [show (doubleTwistConfig n i j hij s 0).1 k = doubleTwistFun n i j s 0 k from rfl,
        doubleTwistFun_of_eq_succ s 0 hk0 hk1,
        show (halfTwistConfig n i s).1 k = halfTwistFun n i s k from rfl,
        halfTwistFun_of_eq_succ s hk0 hk1]
    · rw [show (doubleTwistConfig n i j hij s 0).1 k = doubleTwistFun n i j s 0 k from rfl,
        doubleTwistFun_of_outside s 0 hk0 hk1,
        show (halfTwistConfig n i s).1 k = halfTwistFun n i s k from rfl,
        halfTwistFun_of_fixed s hk0 hk1]
      have hz := congrArg (fun q : OrderedConfig n => q.1 k) (halfTwistConfig_zero n j)
      simpa [halfTwistConfig, baseOrdered] using hz
lemma doubleTwistConfig_zero_left (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) (t : ℝ) :
    doubleTwistConfig n i j hij 0 t = halfTwistConfig n j t := by
  apply Subtype.ext
  funext k
  by_cases hk0 : (k : ℕ) = (i : ℕ)
  · have hkj0 : (k : ℕ) ≠ (j : ℕ) := by
      rw [hk0]
      exact far_nat_ne_00 i j hij
    have hkj1 : (k : ℕ) ≠ (j : ℕ) + 1 := by
      rw [hk0]
      exact far_nat_ne_01 i j hij
    rw [show (doubleTwistConfig n i j hij 0 t).1 k = doubleTwistFun n i j 0 t k from rfl,
      doubleTwistFun_of_eq 0 t hk0,
      show (halfTwistConfig n j t).1 k = halfTwistFun n j t k from rfl,
      halfTwistFun_of_fixed t hkj0 hkj1]
    simp only [twistPoint, Real.cos_zero, Real.sin_zero, mul_zero]
    push_cast
    rw [hk0]
    ring
  · by_cases hk1 : (k : ℕ) = (i : ℕ) + 1
    · have hkj0 : (k : ℕ) ≠ (j : ℕ) := by
        rw [hk1]
        exact far_nat_ne_10 i j hij
      have hkj1 : (k : ℕ) ≠ (j : ℕ) + 1 := by
        rw [hk1]
        exact far_nat_ne_11 i j hij
      rw [show (doubleTwistConfig n i j hij 0 t).1 k = doubleTwistFun n i j 0 t k from rfl,
        doubleTwistFun_of_eq_succ 0 t hk0 hk1,
        show (halfTwistConfig n j t).1 k = halfTwistFun n j t k from rfl,
        halfTwistFun_of_fixed t hkj0 hkj1]
      simp only [twistPoint, Real.cos_zero, Real.sin_zero, mul_zero]
      push_cast
      rw [hk1]
      push_cast
      ring
    · rw [show (doubleTwistConfig n i j hij 0 t).1 k = doubleTwistFun n i j 0 t k from rfl,
        doubleTwistFun_of_outside 0 t hk0 hk1]
      rfl
lemma doubleTwistConfig_j_endpoint (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) (s : ℝ) :
    (doubleTwistConfig n i j hij s 0).1 =
      (doubleTwistConfig n i j hij s 1).1 ∘
        (Equiv.swap (strandIdx j) (strandIdxSucc j)) := by
  funext k
  by_cases hk0 : (k : ℕ) = (i : ℕ)
  · have hki : k = strandIdx i := Fin.ext (by simpa [strandIdx] using hk0)
    have hij0 : strandIdx i ≠ strandIdx j := by
      intro h
      exact far_nat_ne_00 i j hij (by simpa [strandIdx] using congrArg Fin.val h)
    have hij1 : strandIdx i ≠ strandIdxSucc j := by
      intro h
      exact far_nat_ne_01 i j hij (by simpa [strandIdx, strandIdxSucc] using congrArg Fin.val h)
    have hswap : Equiv.swap (strandIdx j) (strandIdxSucc j) k = k := by
      rw [hki, Equiv.swap_apply_of_ne_of_ne hij0 hij1]
    rw [Function.comp_apply, hswap]
    change doubleTwistFun n i j s 0 k = doubleTwistFun n i j s 1 k
    rw [doubleTwistFun_of_eq s 0 hk0, doubleTwistFun_of_eq s 1 hk0]
  · by_cases hk1 : (k : ℕ) = (i : ℕ) + 1
    · have hki : k = strandIdxSucc i := Fin.ext (by simpa [strandIdxSucc] using hk1)
      have hij0 : strandIdxSucc i ≠ strandIdx j := by
        intro h
        exact far_nat_ne_10 i j hij (by simpa [strandIdxSucc, strandIdx] using congrArg Fin.val h)
      have hij1 : strandIdxSucc i ≠ strandIdxSucc j := by
        intro h
        exact far_nat_ne_11 i j hij (by simpa [strandIdxSucc] using congrArg Fin.val h)
      have hswap : Equiv.swap (strandIdx j) (strandIdxSucc j) k = k := by
        rw [hki, Equiv.swap_apply_of_ne_of_ne hij0 hij1]
      rw [Function.comp_apply, hswap]
      change doubleTwistFun n i j s 0 k = doubleTwistFun n i j s 1 k
      rw [doubleTwistFun_of_eq_succ s 0 hk0 hk1,
        doubleTwistFun_of_eq_succ s 1 hk0 hk1]
    · have hout := far_swap_j_preserves_i_outside i j hij k hk0 hk1
      rw [Function.comp_apply]
      change doubleTwistFun n i j s 0 k =
        doubleTwistFun n i j s 1 (Equiv.swap (strandIdx j) (strandIdxSucc j) k)
      rw [doubleTwistFun_of_outside s 0 hk0 hk1,
        doubleTwistFun_of_outside s 1 hout.1 hout.2]
      have hz := congrArg (fun q : OrderedConfig n => q.1 k) (halfTwistConfig_zero n j)
      have ho := congrFun (halfTwistConfig_one n j) k
      have hz' : halfTwistFun n j 0 k = (baseOrdered n).1 k := by
        simpa [halfTwistConfig] using hz
      have ho' : (baseOrdered n).1 k =
          halfTwistFun n j 1 (Equiv.swap (strandIdx j) (strandIdxSucc j) k) := by
        simpa [halfTwistConfig, Function.comp_apply] using ho
      exact hz'.trans ho'
lemma doubleTwistConfig_i_endpoint (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) (t : ℝ) :
    (doubleTwistConfig n i j hij 0 t).1 =
      (doubleTwistConfig n i j hij 1 t).1 ∘
        (Equiv.swap (strandIdx i) (strandIdxSucc i)) := by
  funext k
  by_cases hk0 : (k : ℕ) = (i : ℕ)
  · have hk : k = strandIdx i := Fin.ext (by simpa [strandIdx] using hk0)
    subst k
    rw [Function.comp_apply, Equiv.swap_apply_left]
    change doubleTwistFun n i j 0 t (strandIdx i) =
      doubleTwistFun n i j 1 t (strandIdxSucc i)
    rw [doubleTwistFun_of_eq 0 t (by simp [strandIdx]),
      doubleTwistFun_of_eq_succ 1 t (by simp [strandIdxSucc]) (by simp [strandIdxSucc])]
    simp [twistPoint] <;> ring
  · by_cases hk1 : (k : ℕ) = (i : ℕ) + 1
    · have hk : k = strandIdxSucc i := Fin.ext (by simpa [strandIdxSucc] using hk1)
      subst k
      rw [Function.comp_apply, Equiv.swap_apply_right]
      change doubleTwistFun n i j 0 t (strandIdxSucc i) =
        doubleTwistFun n i j 1 t (strandIdx i)
      rw [doubleTwistFun_of_eq_succ 0 t (by simp [strandIdxSucc]) (by simp [strandIdxSucc]),
        doubleTwistFun_of_eq 1 t (by simp [strandIdx])]
      simp [twistPoint] <;> ring
    · have hk0' : k ≠ strandIdx i := by
        intro h
        exact hk0 (by simpa [strandIdx] using congrArg Fin.val h)
      have hk1' : k ≠ strandIdxSucc i := by
        intro h
        exact hk1 (by simpa [strandIdxSucc] using congrArg Fin.val h)
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hk0' hk1']
      change doubleTwistFun n i j 0 t k = doubleTwistFun n i j 1 t k
      rw [doubleTwistFun_of_outside 0 t hk0 hk1,
        doubleTwistFun_of_outside 1 t hk0 hk1]
lemma configProj_double_j_endpoint (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) (s : ℝ) :
    configProj n (doubleTwistConfig n i j hij s 0) =
      configProj n (doubleTwistConfig n i j hij s 1) := by
  have h : configProj n (doubleTwistConfig n i j hij s 1) =
      configProj n (doubleTwistConfig n i j hij s 0) :=
    Quotient.sound ⟨Equiv.swap (strandIdx j) (strandIdxSucc j),
      doubleTwistConfig_j_endpoint n i j hij s⟩
  exact h.symm
lemma configProj_double_i_endpoint (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) (t : ℝ) :
    configProj n (doubleTwistConfig n i j hij 0 t) =
      configProj n (doubleTwistConfig n i j hij 1 t) := by
  have h : configProj n (doubleTwistConfig n i j hij 1 t) =
      configProj n (doubleTwistConfig n i j hij 0 t) :=
    Quotient.sound ⟨Equiv.swap (strandIdx i) (strandIdxSucc i),
      doubleTwistConfig_i_endpoint n i j hij t⟩
  exact h.symm
open unitInterval
lemma configProj_halfTwist_zero (n : ℕ) (i : Fin (n - 1)) :
    configProj n (halfTwistConfig n i 0) = baseUnordered n := by
  rw [halfTwistConfig_zero]
  rfl
lemma configProj_halfTwist_one (n : ℕ) (i : Fin (n - 1)) :
    configProj n (halfTwistConfig n i 1) = baseUnordered n := by
  exact (halfTwistLoop n i).target
lemma configProj_double_zero_zero (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    configProj n (doubleTwistConfig n i j hij 0 0) = baseUnordered n := by
  rw [doubleTwistConfig_zero_right, configProj_halfTwist_zero]
lemma configProj_double_one_one (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    configProj n (doubleTwistConfig n i j hij 1 1) = baseUnordered n := by
  rw [← configProj_double_j_endpoint n i j hij 1]
  rw [doubleTwistConfig_zero_right, configProj_halfTwist_one]
def farCommMap (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) (z : I × I) : UnorderedConfig n :=
  if (z.2 : ℝ) ≤ 1 / 2 then
    configProj n <| doubleTwistConfig n i j hij
      (2 * (z.1 : ℝ) * (z.2 : ℝ))
      (2 * (1 - (z.1 : ℝ)) * (z.2 : ℝ))
  else
    configProj n <| doubleTwistConfig n i j hij
      ((1 - (z.1 : ℝ)) * (2 * (z.2 : ℝ) - 1) + (z.1 : ℝ))
      ((1 - (z.1 : ℝ)) + (z.1 : ℝ) * (2 * (z.2 : ℝ) - 1))
lemma continuous_farCommMap (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    Continuous (farCommMap n i j hij) := by
  unfold farCommMap
  apply continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
  · have hlow : Continuous (fun z : I × I =>
        (2 * (z.1 : ℝ) * (z.2 : ℝ),
          2 * (1 - (z.1 : ℝ)) * (z.2 : ℝ))) := by
      fun_prop
    exact ((configProj n).continuous.comp
      ((continuous_doubleTwistConfig n i j hij).comp hlow)).continuousOn
  · have hhigh : Continuous (fun z : I × I =>
        ((1 - (z.1 : ℝ)) * (2 * (z.2 : ℝ) - 1) + (z.1 : ℝ),
          (1 - (z.1 : ℝ)) + (z.1 : ℝ) * (2 * (z.2 : ℝ) - 1))) := by
      fun_prop
    exact ((configProj n).continuous.comp
      ((continuous_doubleTwistConfig n i j hij).comp hhigh)).continuousOn
  · intro z hz
    have hz' : (z.2 : ℝ) = 1 / 2 := by
      simpa [Function.comp_apply] using hz
    apply congrArg (configProj n)
    congr 1 <;> rw [hz'] <;> ring
def farCommHomotopy (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    Path.Homotopy
      ((halfTwistLoop n j).trans (halfTwistLoop n i))
      ((halfTwistLoop n i).trans (halfTwistLoop n j)) where
  toFun := farCommMap n i j hij
  continuous_toFun := continuous_farCommMap n i j hij
  map_zero_left x := by
    change farCommMap n i j hij (0, x) =
      ((halfTwistLoop n j).trans (halfTwistLoop n i)) x
    simp only [Path.trans_apply]
    unfold farCommMap
    split_ifs with hx
    · simp [halfTwistLoop]
      rw [doubleTwistConfig_zero_left]
    · simp [halfTwistLoop]
      rw [← configProj_double_j_endpoint n i j hij (2 * (x : ℝ) - 1)]
      rw [doubleTwistConfig_zero_right]
  map_one_left x := by
    change farCommMap n i j hij (1, x) =
      ((halfTwistLoop n i).trans (halfTwistLoop n j)) x
    simp only [Path.trans_apply]
    unfold farCommMap
    split_ifs with hx
    · simp [halfTwistLoop]
      rw [doubleTwistConfig_zero_right]
    · simp [halfTwistLoop]
      rw [← configProj_double_i_endpoint n i j hij (2 * (x : ℝ) - 1)]
      rw [doubleTwistConfig_zero_left]
  prop' u x hx := by
    rcases hx with hx | hx
    · rw [hx]
      change farCommMap n i j hij (u, 0) =
        ((halfTwistLoop n j).trans (halfTwistLoop n i)) 0
      rw [Path.source]
      unfold farCommMap
      norm_num
      exact configProj_double_zero_zero n i j hij
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      change farCommMap n i j hij (u, 1) =
        ((halfTwistLoop n j).trans (halfTwistLoop n i)) 1
      rw [Path.target]
      unfold farCommMap
      norm_num
      convert configProj_double_one_one n i j hij using 1 <;> ring
theorem halfTwistBraid_far_commute (n : ℕ) (i j : Fin (n - 1))
    (hij : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    halfTwistBraid n i * halfTwistBraid n j =
      halfTwistBraid n j * halfTwistBraid n i := by
  rw [FundamentalGroup.mul_def, FundamentalGroup.mul_def]
  change Path.Homotopic.Quotient.mk
      ((halfTwistLoop n j).trans (halfTwistLoop n i)) =
    Path.Homotopic.Quotient.mk
      ((halfTwistLoop n i).trans (halfTwistLoop n j))
  exact (Path.Homotopic.Quotient.eq).2 ⟨farCommHomotopy n i j hij⟩
end
end TarchaBraids
open BraidsLinksMCG TarchaBraids
theorem solution (n : ℕ) : ∀ i j : Fin (n - 1), 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs → halfTwistBraid n i * halfTwistBraid n j = halfTwistBraid n j * halfTwistBraid n i := by
  intro i j hij
  exact halfTwistBraid_far_commute n i j hij
