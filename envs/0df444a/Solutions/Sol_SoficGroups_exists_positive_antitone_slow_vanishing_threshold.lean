-- Prove2me | solution 1 for SoficGroups.exists_positive_antitone_slow_vanishing_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/cd77a7b9-b1ed-4d42-86de-b3d81b8b61bf

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    (e : ℕ → ℝ) (he_nonneg : ∀ n, 0 ≤ e n)
    (he : Tendsto e atTop (nhds 0)) :
    ∃ eta : ℕ → ℝ,
      (∀ n, 0 < eta n) ∧ Antitone eta ∧
      Tendsto eta atTop (nhds 0) ∧
      Tendsto (fun n => e n / eta n) atTop (nhds 0) := by
  have hrange : BddAbove (Set.range e) := he.bddAbove_range
  have htail_bdd (n : ℕ) : BddAbove (e '' Set.Ici n) := by
    apply hrange.mono
    rintro y ⟨k, hk, rfl⟩
    exact ⟨k, rfl⟩
  have htail_ne (n : ℕ) : (e '' Set.Ici n).Nonempty := by
    refine ⟨e n, ?_⟩
    exact ⟨n, Set.mem_Ici.mpr (le_refl n), rfl⟩
  let d : ℕ → ℝ := fun n => sSup (e '' Set.Ici n)
  have hd_dom (n : ℕ) : e n ≤ d n := by
    dsimp [d]
    apply le_csSup (htail_bdd n)
    exact ⟨n, Set.mem_Ici.mpr (le_refl n), rfl⟩
  have hd_nonneg (n : ℕ) : 0 ≤ d n :=
    (he_nonneg n).trans (hd_dom n)
  have hd_antitone : Antitone d := by
    intro a b hab
    change sSup (e '' Set.Ici b) ≤ sSup (e '' Set.Ici a)
    apply csSup_le_csSup (htail_bdd a) (htail_ne b)
    rintro y ⟨k, hk, rfl⟩
    exact ⟨k, Set.mem_Ici.mpr (hab.trans (Set.mem_Ici.mp hk)), rfl⟩
  have hd_zero : Tendsto d atTop (nhds 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall fun n => lt_of_lt_of_le ha (hd_nonneg n)
    · intro a ha
      have hev : ∀ᶠ k in atTop, e k < a / 2 :=
        he.eventually (gt_mem_nhds (half_pos ha))
      obtain ⟨N, hN⟩ := eventually_atTop.mp hev
      filter_upwards [eventually_ge_atTop N] with n hn
      have hle : d n ≤ a / 2 := by
        dsimp [d]
        apply csSup_le (htail_ne n)
        rintro y ⟨k, hk, rfl⟩
        exact (hN k (hn.trans (Set.mem_Ici.mp hk))).le
      exact hle.trans_lt (half_lt_self ha)
  let q : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hq_pos (n : ℕ) : 0 < q n := by
    dsimp [q]
    positivity
  have hq_antitone : Antitone q := by
    intro a b hab
    dsimp [q]
    apply one_div_le_one_div_of_le (by positivity)
    have hab_real : (a : ℝ) ≤ b := by
      exact_mod_cast hab
    exact add_le_add hab_real (le_refl 1)
  have hq_zero : Tendsto q atTop (nhds 0) := by
    dsimp [q]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let eta : ℕ → ℝ := fun n => Real.sqrt (d n + q n)
  have heta_pos (n : ℕ) : 0 < eta n := by
    dsimp [eta]
    apply Real.sqrt_pos.2
    exact lt_of_lt_of_le (hq_pos n) (le_add_of_nonneg_left (hd_nonneg n))
  have heta_antitone : Antitone eta := by
    intro a b hab
    dsimp [eta]
    exact Real.sqrt_le_sqrt (add_le_add (hd_antitone hab) (hq_antitone hab))
  have hsum_zero : Tendsto (fun n => d n + q n) atTop (nhds 0) := by
    simpa using hd_zero.add hq_zero
  have heta_zero : Tendsto eta atTop (nhds 0) := by
    simpa only [eta, Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsum_zero
  have hratio_bound (n : ℕ) : e n / eta n ≤ eta n := by
    apply (div_le_iff₀ (heta_pos n)).2
    calc
      e n ≤ d n := hd_dom n
      _ ≤ d n + q n := le_add_of_nonneg_right (hq_pos n).le
      _ = eta n * eta n := by
        dsimp [eta]
        nlinarith [Real.sq_sqrt (add_nonneg (hd_nonneg n) (hq_pos n).le)]
  refine ⟨eta, heta_pos, heta_antitone, heta_zero, ?_⟩
  exact squeeze_zero (fun n => div_nonneg (he_nonneg n) (heta_pos n).le)
    hratio_bound heta_zero
end SoficGroups
