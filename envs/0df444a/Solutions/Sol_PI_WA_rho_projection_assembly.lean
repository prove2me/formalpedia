-- Prove2me | solution 1 for PI.WA.rho_projection_assembly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:57.987082+00:00
-- url     : https://prove2.me/submissions/5e8d224b-5cf6-4341-aa7a-92a5f959a578

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeakApproxDVR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_RhoProjectionAssembly
import Theorems.Thm_PI_WADVR_Sm_sum
import Theorems.Thm_PI_WADVR_Sm_add
import Theorems.Thm_PI_WADVR_Sm_mono
import Theorems.Thm_PI_WADVR_Sm_mul
import Theorems.Thm_PI_WADVR_Sm_neg
import Theorems.Thm_PI_WADVR_big_one_add_pow
import Theorems.Thm_PI_WADVR_exists_sm_target
import Theorems.Thm_PI_WADVR_sm_exists
import Theorems.Thm_PI_WADVR_sm_of_density
import Theorems.Thm_PI_WADVR_small_one_add_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WA
open PI.WADVR
namespace PI.WA
theorem _root_.solution : Assembly := by
  intro E _ ι _ W Q _ _ _ _ _ _ iw p hp0 hpu hden ϖ hϖ hz x N
  classical
  choose z hz0 hzi hzj using hz
  choose n hn using fun i => exists_sm_target (hϖ i) (hp0 i) N
  set K : ℕ := ∑ i, n i with hK
  have hnK : ∀ i, n i ≤ K := fun i =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  choose y c hy using fun i => hden i (x i) K
  have hyS : ∀ i, PI.WADVR.Sm (Q i) (ϖ i) K (iw i (y i) - x i) := fun i =>
    sm_of_density (hϖ i) (hpu i) (hy i)
  choose k hk using fun i j => sm_exists (hϖ j) (iw j (y i))
  set B : ℕ := ∑ i, ∑ j, (-(k i j)).toNat with hB
  have hkB : ∀ i j, -(k i j) ≤ (B : ℤ) := by
    intro i j
    have h1 : (-(k i j)).toNat ≤ ∑ j', (-(k i j')).toNat :=
      Finset.single_le_sum (f := fun j' => (-(k i j')).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have h2 : ∑ j', (-(k i j')).toNat ≤ B :=
      Finset.single_le_sum (f := fun i' => ∑ j', (-(k i' j')).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h3 := Int.self_le_toNat (-(k i j))
    have h4 : ((-(k i j)).toNat : ℤ) ≤ B := by exact_mod_cast h1.trans h2
    linarith
  set r : ℕ := 1 + K + B with hr
  have hr1 : 1 ≤ r := by omega
  have hrk : ∀ i j, (K : ℤ) ≤ (r : ℤ) + k i j := by
    intro i j
    have := hkB i j
    push_cast [hr]
    linarith
  let e : ι → E := fun i => z i ^ r * (1 + z i ^ r)⁻¹
  refine ⟨∑ i, e i * y i, fun j => ?_⟩
  have he : ∀ i, iw j (e i) = iw j (z i) ^ r * (1 + iw j (z i) ^ r)⁻¹ := by
    intro i; simp [e, map_mul, map_pow, map_inv₀, map_add, map_one]

  have hT : ∀ i, PI.WADVR.Sm (Q j) (ϖ j) K
      ((iw j (e i) - if i = j then 1 else 0) * iw j (y i)) := by
    intro i
    by_cases hij : i = j
    · subst hij
      obtain ⟨hne, hsm⟩ := big_one_add_pow (hϖ i) ((map_ne_zero (iw i)).mpr (hz0 i)) (hzi i) hr1
      have hid : iw i (e i) - (if i = i then 1 else 0) = -(1 + iw i (z i) ^ r)⁻¹ := by
        rw [if_pos rfl, he]
        calc iw i (z i) ^ r * (1 + iw i (z i) ^ r)⁻¹ - 1
            = (iw i (z i) ^ r - (1 + iw i (z i) ^ r)) * (1 + iw i (z i) ^ r)⁻¹ := by
              rw [sub_mul, mul_inv_cancel₀ hne]
          _ = -(1 + iw i (z i) ^ r)⁻¹ := by ring
      rw [hid]
      exact (hsm.neg.mul (hϖ i) (hk i i)).mono (hϖ i) (hrk i i)
    · rw [if_neg hij, sub_zero, he]
      obtain ⟨_, hsm⟩ := small_one_add_pow (hϖ j) (hzj i j (Ne.symm hij)) hr1
      exact (hsm.mul (hϖ j) (hk i j)).mono (hϖ j) (hrk i j)
  have hsum : iw j (∑ i, e i * y i) - x j =
      (∑ i, (iw j (e i) - if i = j then 1 else 0) * iw j (y i)) + (iw j (y j) - x j) := by
    rw [map_sum]
    simp only [map_mul, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have htot : PI.WADVR.Sm (Q j) (ϖ j) K (iw j (∑ i, e i * y i) - x j) := by
    rw [hsum]
    exact (PI.WADVR.Sm.sum _ _ _ fun i _ => hT i).add (hyS j)
  obtain ⟨c', hc'⟩ := hn j _ (htot.mono (hϖ j) (by exact_mod_cast hnK j))
  exact ⟨c', by rw [← hc']; ring⟩
end PI.WA
