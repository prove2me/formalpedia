-- Prove2me | solution 1 for SensitivityPoA.Holder.lemma_10_d
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T08:55:36.994427+00:00
-- url     : https://prove2.me/submissions/0864e094-7390-4c67-bfc6-7b6f5890271c

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting
import Theorems.Thm_KellyStochasticNetworks_wardrop_equilibrium_exists
import Theorems.Thm_SensitivityPoA_Holder_lemma_10_a
import Theorems.Thm_SensitivityPoA_Holder_lemma_10_c
import Theorems.Thm_SensitivityPoA_Holder_lemma_1_c

set_option autoImplicit false

open KellyStochasticNetworks
open SensitivityPoA.Holder

namespace PoAH

lemma basic_of_standing (N : Network) (hN : N.Standing) : N.Basic :=
  ⟨hN.1, hN.2.1, hN.2.2.1, fun k => lt_of_lt_of_le (by norm_num) (hN.2.2.2.2 k)⟩

lemma lf_nonneg (N : Network) (hN : N.Basic) (x : Fin N.R → ℝ) (hx : ∀ r, 0 ≤ x r)
    (j : Fin N.J) : 0 ≤ linkFlow N.A x j := by
  unfold linkFlow
  refine Finset.sum_nonneg (fun r _ => ?_)
  rcases hN.1 j r with h | h <;> rw [h] <;> [simp; simpa using hx r]

lemma lf_le (N : Network) (hN : N.Basic) (x : Fin N.R → ℝ) (hx : ∀ r, 0 ≤ x r) (j : Fin N.J) :
    linkFlow N.A x j ≤ ∑ r, x r := by
  unfold linkFlow
  refine Finset.sum_le_sum (fun r _ => ?_)
  rcases hN.1 j r with h | h <;> rw [h] <;> simp [hx r]

lemma sum_flow (N : Network) {Γ : Game N} {x : Fin N.R → ℝ} (hx : IsFlow Γ x) :
    ∑ r, x r = totalDemand Γ.d := by
  unfold totalDemand
  rw [← Finset.sum_fiberwise Finset.univ N.s x]
  exact Finset.sum_congr rfl (fun k _ => hx.2 k)

lemma lf_le_T (N : Network) (hN : N.Basic) {Γ : Game N} {x : Fin N.R → ℝ} (hx : IsFlow Γ x)
    (j : Fin N.J) : linkFlow N.A x j ≤ totalDemand Γ.d :=
  (lf_le N hN x hx.1 j).trans (sum_flow N hx).le

lemma cost_nonneg (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (f : Fin N.R → ℝ) (hf : IsFlow Γ f) : 0 ≤ cost Γ f := by
  unfold cost
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (lf_nonneg N hN f hf.1 j)
    ((hΓ.1 j).2.2 _ (lf_nonneg N hN f hf.1 j)))

lemma T_nonneg {N : Network} (Γ : Game N) (hΓ : Γ.IsGeneralized) : 0 ≤ totalDemand Γ.d :=
  Finset.sum_nonneg (fun k _ => hΓ.2 k)

/-- WE existence for a generalized game. -/
lemma we_exists (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized) :
    ∃ f, IsWE Γ f := by
  set D : Fin N.J → ℝ → ℝ := fun j x => Γ.τ j (max x 0) with hDdef
  have hDc : ∀ j, Continuous (D j) := by
    intro j
    have h1 : Continuous (fun x : ℝ => max x 0) := continuous_id.max continuous_const
    exact (hΓ.1 j).1.comp_continuous h1 (fun x => le_max_right x 0)
  have hDm : ∀ j, Monotone (D j) := by
    intro j a b hab
    exact (hΓ.1 j).2.1 (le_max_right a 0 : (0:ℝ) ≤ max a 0) (le_max_right b 0)
      (max_le_max hab le_rfl)
  have hserved : ∀ σ, ∃ r, N.s r = σ := by
    intro σ
    obtain ⟨r, hr⟩ := Finset.card_pos.mp (hN.2.2.2 σ)
    exact ⟨r, (Finset.mem_filter.mp hr).2⟩
  obtain ⟨x, hx⟩ := wardrop_equilibrium_exists N.A N.s D Γ.d hN.1 hDc hDm hΓ.2 hserved
  refine ⟨x, hx.1, ?_⟩
  intro r r' hs hpos
  have hlf : ∀ j, D j (linkFlow N.A x j) = Γ.τ j (linkFlow N.A x j) := by
    intro j
    simp only [hDdef]
    rw [max_eq_left (lf_nonneg N hN x hx.1.1 j)]
  have := hx.2 r r' hs hpos
  simpa only [hlf] using this

/-- a generic bound on the gap of suprema -/
lemma sSup_gap (S1 S2 : Set ℝ) (h1 : S1.Nonempty) (h2 : S2.Nonempty) (B : ℝ)
    (h : ∀ a ∈ S1, ∀ b ∈ S2, |a - b| ≤ B) : |sSup S1 - sSup S2| ≤ B := by
  obtain ⟨a0, ha0⟩ := h1
  obtain ⟨b0, hb0⟩ := h2
  have bd1 : BddAbove S1 := ⟨b0 + B, fun a ha => by
    have := (abs_le.mp (h a ha b0 hb0)).2; linarith⟩
  have bd2 : BddAbove S2 := ⟨a0 + B, fun b hb => by
    have := (abs_le.mp (h a0 ha0 b hb)).1; linarith⟩
  rw [abs_le]
  constructor
  · have : sSup S2 - B ≤ sSup S1 := by
      have : sSup S2 ≤ sSup S1 + B := by
        refine csSup_le ⟨b0, hb0⟩ (fun b hb => ?_)
        have := (abs_le.mp (h a0 ha0 b hb)).1
        have := le_csSup bd1 ha0
        linarith
      linarith
    linarith
  · have : sSup S1 ≤ sSup S2 + B := by
      refine csSup_le ⟨a0, ha0⟩ (fun a ha => ?_)
      have := (abs_le.mp (h a ha b0 hb0)).2
      have := le_csSup bd2 hb0
      linarith
    linarith

lemma dist_nonneg {N : Network} (Γ1 Γ2 : Game N) : 0 ≤ gameDist Γ1 Γ2 :=
  le_trans (norm_nonneg _) (le_max_left _ _)

lemma dist_bound (N : Network) (Γ1 Γ2 : Game N) (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N)
    (j : Fin N.J) (y : ℝ) (hy0 : 0 ≤ y)
    (hyT : y ≤ min (totalDemand Γ1.d) (totalDemand Γ2.d)) :
    |Γ1.τ j y - Γ2.τ j y| ≤ gameDist Γ1 Γ2 := by
  set m := min (totalDemand Γ1.d) (totalDemand Γ2.d)
  have hbdd : ∀ j : Fin N.J, ∃ C : ℝ, ∀ y ∈ Set.Icc (0:ℝ) m, |Γ1.τ j y - Γ2.τ j y| ≤ C := by
    intro j
    have hc : ContinuousOn (fun y => |Γ1.τ j y - Γ2.τ j y|) (Set.Icc (0:ℝ) m) := by
      refine (ContinuousOn.abs (ContinuousOn.sub ?_ ?_))
      · exact (h1.1.1 j).1.mono Set.Icc_subset_Ici_self
      · exact (h2.1.1 j).1.mono Set.Icc_subset_Ici_self
    obtain ⟨C, hC⟩ := (isCompact_Icc.bddAbove_image hc)
    exact ⟨C, fun y hy => hC ⟨y, hy, rfl⟩⟩
  choose C hC using hbdd
  unfold gameDist
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (le_max_left _ _)
  refine le_csSup ⟨∑ j, |C j|, ?_⟩ ⟨(j, y), ⟨Set.mem_univ _, ⟨hy0, hyT⟩⟩, rfl⟩
  rintro _ ⟨⟨i, z⟩, ⟨_, hz⟩, rfl⟩
  calc |Γ1.τ i z - Γ2.τ i z| ≤ C i := hC i z hz
    _ ≤ |C i| := le_abs_self _
    _ ≤ ∑ j, |C j| := Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)

lemma dist_demand {N : Network} (Γ1 Γ2 : Game N) (k : Fin N.Sd) :
    |Γ1.d k - Γ2.d k| ≤ gameDist Γ1 Γ2 := by
  unfold gameDist
  refine le_trans ?_ (le_max_left _ _)
  have := norm_le_pi_norm (Γ1.d - Γ2.d) k
  simpa [Real.norm_eq_abs] using this

lemma dist_end {N : Network} (Γ1 Γ2 : Game N) (j : Fin N.J) :
    |Γ1.τ j (totalDemand Γ1.d) - Γ2.τ j (totalDemand Γ2.d)| ≤ gameDist Γ1 Γ2 := by
  unfold gameDist
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (le_max_right _ _)
  have := norm_le_pi_norm (fun j => Γ1.τ j (totalDemand Γ1.d) - Γ2.τ j (totalDemand Γ2.d)) j
  simpa [Real.norm_eq_abs] using this

/-- upper bound on the distance from componentwise bounds -/
lemma dist_le {N : Network} (Γ1 Γ2 : Game N) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ k, |Γ1.d k - Γ2.d k| ≤ B)
    (hτ : ∀ j y, 0 ≤ y → y ≤ min (totalDemand Γ1.d) (totalDemand Γ2.d) →
      |Γ1.τ j y - Γ2.τ j y| ≤ B)
    (hend : ∀ j, |Γ1.τ j (totalDemand Γ1.d) - Γ2.τ j (totalDemand Γ2.d)| ≤ B) :
    gameDist Γ1 Γ2 ≤ B := by
  unfold gameDist
  refine max_le ?_ (max_le ?_ ?_)
  · refine (pi_norm_le_iff_of_nonneg hB).2 (fun k => ?_)
    simpa [Real.norm_eq_abs] using hd k
  · refine Real.sSup_le ?_ hB
    rintro _ ⟨⟨i, z⟩, ⟨_, hz⟩, rfl⟩
    exact hτ i z hz.1 hz.2
  · refine (pi_norm_le_iff_of_nonneg hB).2 (fun k => ?_)
    simpa [Real.norm_eq_abs] using hend k

lemma flow_exists (N : Network) (hN : N.Basic) (Γ : Game N) (hd : ∀ k, 0 ≤ Γ.d k) :
    ∃ g, IsFlow Γ g := by
  have hex : ∀ k : Fin N.Sd, ∃ r0, N.s r0 = k := fun k => by
    obtain ⟨r, hr⟩ := Finset.card_pos.mp (hN.2.2.2 k)
    exact ⟨r, (Finset.mem_filter.mp hr).2⟩
  choose rs hrs using hex
  refine ⟨fun r => if r = rs (N.s r) then Γ.d (N.s r) else 0, fun r => ?_, fun σ => ?_⟩
  · show 0 ≤ (if r = rs (N.s r) then Γ.d (N.s r) else 0)
    split_ifs
    · exact hd _
    · exact le_rfl
  · have : ∀ r ∈ Finset.univ.filter (fun r => N.s r = σ),
        (if r = rs (N.s r) then Γ.d (N.s r) else 0) = if r = rs σ then Γ.d σ else 0 := by
      intro r hr
      have hrk : N.s r = σ := (Finset.mem_filter.mp hr).2
      rw [hrk]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    simp [hrs σ]

/-- every flow puts at least `T/J` on some arc -/
lemma exists_big_arc (N : Network) (hN : N.Basic) {Γ : Game N} {f : Fin N.R → ℝ}
    (hf : IsFlow Γ f) (hJ : 0 < N.J) :
    ∃ j, totalDemand Γ.d / N.J ≤ linkFlow N.A f j := by
  by_contra hcon
  push Not at hcon
  have hsum : totalDemand Γ.d ≤ ∑ j, linkFlow N.A f j := by
    rw [← sum_flow N hf]
    unfold linkFlow
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun r _ => ?_)
    obtain ⟨j0, hj0⟩ := hN.2.1 r
    have hnn : ∀ j, 0 ≤ N.A j r * f r := fun j => by
      rcases hN.1 j r with h | h <;> rw [h] <;> simp [hf.1 r]
    calc f r = N.A j0 r * f r := by rw [hj0]; ring
      _ ≤ ∑ j, N.A j r * f r :=
        Finset.single_le_sum (f := fun j => N.A j r * f r) (fun j _ => hnn j) (Finset.mem_univ j0)
  have : ∑ j, linkFlow N.A f j < ∑ _j : Fin N.J, totalDemand Γ.d / N.J := by
    have : (Finset.univ : Finset (Fin N.J)).Nonempty := ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
    exact Finset.sum_lt_sum_of_nonempty this (fun j _ => hcon j)
  simp at this
  have hJr : (0:ℝ) < N.J := by exact_mod_cast hJ
  rw [mul_div_cancel₀ _ hJr.ne'] at this
  linarith

lemma J_pos (N : Network) (hN : N.Basic) : 0 < N.J := by
  have hR : 0 < N.R := by
    have := hN.2.2.2 ⟨0, hN.2.2.1⟩
    have h2 := Finset.card_le_univ (Finset.univ.filter fun r => N.s r = ⟨0, hN.2.2.1⟩)
    simp at h2
    omega
  obtain ⟨j, _⟩ := hN.2.1 ⟨0, hR⟩
  exact Nat.pos_of_ne_zero (fun h => by have := j.2; omega)

/-- a uniform lower bound for the cost of every flow -/
lemma cost_ge (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (f : Fin N.R → ℝ) (hf : IsFlow Γ f) (c : ℝ) (hc : ∀ j, c ≤ Γ.τ j (totalDemand Γ.d / N.J)) :
    totalDemand Γ.d / N.J * c ≤ cost Γ f := by
  have hJ := J_pos N hN
  have hJr : (0:ℝ) < N.J := by exact_mod_cast hJ
  obtain ⟨j, hj⟩ := exists_big_arc N hN hf hJ
  have hT0 : 0 ≤ totalDemand Γ.d / N.J := div_nonneg (T_nonneg Γ hΓ) hJr.le
  have hnn : ∀ i, 0 ≤ linkFlow N.A f i * Γ.τ i (linkFlow N.A f i) := fun i =>
    mul_nonneg (lf_nonneg N hN f hf.1 i) ((hΓ.1 i).2.2 _ (lf_nonneg N hN f hf.1 i))
  have h1 : linkFlow N.A f j * Γ.τ j (linkFlow N.A f j) ≤ cost Γ f :=
    Finset.single_le_sum (f := fun i => linkFlow N.A f i * Γ.τ i (linkFlow N.A f i))
      (fun i _ => hnn i) (Finset.mem_univ j)
  have hmono : Γ.τ j (totalDemand Γ.d / N.J) ≤ Γ.τ j (linkFlow N.A f j) :=
    (hΓ.1 j).2.1 hT0 (lf_nonneg N hN f hf.1 j) hj
  have hτ0 : 0 ≤ Γ.τ j (totalDemand Γ.d / N.J) := (hΓ.1 j).2.2 _ hT0
  rcases le_or_gt c 0 with hc0 | hc0
  · nlinarith
  · have := hc j
    calc totalDemand Γ.d / N.J * c ≤ linkFlow N.A f j * Γ.τ j (linkFlow N.A f j) := by
          apply mul_le_mul hj (this.trans hmono) hc0.le (lf_nonneg N hN f hf.1 j)
      _ ≤ cost Γ f := h1

lemma so_ge (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (c : ℝ) (hc : ∀ j, c ≤ Γ.τ j (totalDemand Γ.d / N.J)) :
    totalDemand Γ.d / N.J * c ≤ SOCost Γ := by
  obtain ⟨g, hg⟩ := flow_exists N hN Γ hΓ.2
  exact le_csInf ⟨_, g, hg, rfl⟩ (by rintro _ ⟨f, hf, rfl⟩; exact cost_ge N hN Γ hΓ f hf c hc)

lemma so_pos (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ ∈ gameSpace N) :
    0 < SOCost Γ := by
  have hJ := J_pos N hN
  have hJr : (0:ℝ) < N.J := by exact_mod_cast hJ
  have hT := hΓ.2.1
  set x := totalDemand Γ.d / N.J
  have hx0 : 0 < x := div_pos hT hJr
  have hxT : x ≤ totalDemand Γ.d := div_le_self hT.le (by exact_mod_cast hJ)
  have hne : (Finset.univ : Finset (Fin N.J)).Nonempty := ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
  obtain ⟨j0, _, hj0⟩ := Finset.exists_min_image Finset.univ (fun j => Γ.τ j x) hne
  have hpos : 0 < Γ.τ j0 x := hΓ.2.2 j0 x hx0 hxT
  have := so_ge N hN Γ hΓ.1 (Γ.τ j0 x) (fun j => hj0 j (Finset.mem_univ j))
  exact lt_of_lt_of_le (mul_pos hx0 hpos) this

lemma so_le (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized) (f : Fin N.R → ℝ)
    (hf : IsFlow Γ f) : SOCost Γ ≤ cost Γ f :=
  csInf_le ⟨0, by rintro _ ⟨g, hg, rfl⟩; exact cost_nonneg N hN Γ hΓ g hg⟩ ⟨f, hf, rfl⟩

lemma we_nonneg (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized) :
    0 ≤ WECost Γ := by
  obtain ⟨f, hf⟩ := we_exists N hN Γ hΓ
  unfold WECost
  apply Real.sSup_nonneg
  rintro _ ⟨g, hg, rfl⟩
  exact cost_nonneg N hN Γ hΓ g hg.1

/-- any upper bound on the cost of all flows bounds the WE cost -/
lemma we_le (N : Network) (Γ : Game N) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ f, IsFlow Γ f → cost Γ f ≤ B) : WECost Γ ≤ B := by
  unfold WECost
  refine Real.sSup_le ?_ hB0
  rintro _ ⟨g, hg, rfl⟩
  exact hB g hg.1

lemma cost_le (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (f : Fin N.R → ℝ) (hf : IsFlow Γ f) (P : ℝ)
    (hP : ∀ j, Γ.τ j (totalDemand Γ.d) ≤ P) :
    cost Γ f ≤ N.J * totalDemand Γ.d * P := by
  unfold cost
  have hT0 := T_nonneg Γ hΓ
  have : ∀ j, linkFlow N.A f j * Γ.τ j (linkFlow N.A f j) ≤ totalDemand Γ.d * P := by
    intro j
    have h0 := lf_nonneg N hN f hf.1 j
    have h1 := lf_le_T N hN hf j
    have h2 : Γ.τ j (linkFlow N.A f j) ≤ Γ.τ j (totalDemand Γ.d) :=
      (hΓ.1 j).2.1 h0 hT0 h1
    have h3 := (hΓ.1 j).2.2 _ h0
    exact mul_le_mul h1 (h2.trans (hP j)) h3 hT0
  calc ∑ j, linkFlow N.A f j * Γ.τ j (linkFlow N.A f j) ≤ ∑ _j : Fin N.J, totalDemand Γ.d * P :=
        Finset.sum_le_sum (fun j _ => this j)
    _ = N.J * totalDemand Γ.d * P := by simp; ring

end PoAH

namespace PoAH

lemma cost_close (N : Network) (hN : N.Basic) (Γ1 Γ2 : Game N)
    (D : ℝ) (hD : ∀ j y, 0 ≤ y → y ≤ totalDemand Γ1.d → |Γ1.τ j y - Γ2.τ j y| ≤ D)
    (f : Fin N.R → ℝ) (hf : IsFlow Γ1 f) :
    |cost Γ1 f - cost Γ2 f| ≤ (N.J : ℝ) * totalDemand Γ1.d * D := by
  set T := totalDemand Γ1.d with hT
  have hyf : ∀ j, 0 ≤ linkFlow N.A f j ∧ linkFlow N.A f j ≤ T := fun j =>
    ⟨lf_nonneg N hN f hf.1 j, lf_le_T N hN hf j⟩
  unfold cost
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ j : Fin N.J, |linkFlow N.A f j * Γ1.τ j (linkFlow N.A f j) -
      linkFlow N.A f j * Γ2.τ j (linkFlow N.A f j)| ≤ T * D := by
    intro j
    have h1 := hD j _ (hyf j).1 (hyf j).2
    rw [← mul_sub, abs_mul, abs_of_nonneg (hyf j).1]
    exact mul_le_mul (hyf j).2 h1 (abs_nonneg _) (le_trans (hyf j).1 (hyf j).2)
  calc ∑ j, |linkFlow N.A f j * Γ1.τ j (linkFlow N.A f j) -
        linkFlow N.A f j * Γ2.τ j (linkFlow N.A f j)|
      ≤ ∑ j : Fin N.J, T * D := Finset.sum_le_sum (fun j _ => hterm j)
    _ = (N.J : ℝ) * T * D := by simp; ring

lemma approx_mono {N : Network} (Γ : Game N) (ε ε' : ℝ) (h : ε ≤ ε') (f : Fin N.R → ℝ)
    (hf : IsApproxWE Γ ε f) : IsApproxWE Γ ε' f :=
  ⟨hf.1, fun g hg => (hf.2 g hg).trans h⟩

/-- passing to the limit `δ → 0⁺` in a bound valid for all `ε0 + δ` -/
lemma limit_bound (x a b ε0 : ℝ) (hε0 : 0 ≤ ε0)
    (h : ∀ δ > 0, x ≤ a * Real.sqrt (b * (ε0 + δ)) + (ε0 + δ)) :
    x ≤ a * Real.sqrt (b * ε0) + ε0 := by
  have hc : Continuous (fun δ : ℝ => a * Real.sqrt (b * (ε0 + δ)) + (ε0 + δ)) := by
    fun_prop
  have ht : Filter.Tendsto (fun δ : ℝ => a * Real.sqrt (b * (ε0 + δ)) + (ε0 + δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (a * Real.sqrt (b * (ε0 + 0)) + (ε0 + 0))) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  simp only [add_zero] at ht
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall (fun δ hδ => h δ hδ))

end PoAH


open KellyStochasticNetworks
open SensitivityPoA.Holder

namespace PoAH

lemma we_pair_close (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hd : Γ1.d = Γ2.d)
    (M : ℝ) (hM0 : 0 < M) (hM : ∀ j, LipOnIcc (Γ1.τ j) (totalDemand Γ1.d) M)
    (f g : Fin N.R → ℝ) (hf : IsWE Γ1 f) (hg : IsWE Γ2 g) :
    |cost Γ1 f - cost Γ2 g| ≤
      (N.J : ℝ) * Real.sqrt (M * ((N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2))
        * totalDemand Γ1.d + (N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2
        + (N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2 := by
  have hB := basic_of_standing N hN
  set T := totalDemand Γ1.d
  set D := gameDist Γ1 Γ2
  have hT0 : 0 ≤ T := T_nonneg Γ1 h1.1
  have hD0 : 0 ≤ D := dist_nonneg Γ1 Γ2
  have hε0 : 0 ≤ (N.J : ℝ) * T * D := by positivity
  have happ := (lemma_10_c N hN Γ1 Γ2 h1 h2 hd f g hf hg).2
  -- cost of g in Γ1 vs cost of f in Γ1
  have hA : |cost Γ1 g - cost Γ1 f| ≤
      (N.J : ℝ) * Real.sqrt (M * ((N.J : ℝ) * T * D)) * T + (N.J : ℝ) * T * D := by
    have key : ∀ δ > 0, |cost Γ1 g - cost Γ1 f| ≤
        ((N.J : ℝ) * T) * Real.sqrt (M * ((N.J : ℝ) * T * D + δ)) + ((N.J : ℝ) * T * D + δ) := by
      intro δ hδ
      have hε : 0 < (N.J : ℝ) * T * D + δ := by linarith
      have hg' := approx_mono Γ1 _ _ (by linarith : (N.J : ℝ) * T * D ≤ (N.J : ℝ) * T * D + δ) g happ
      have := (lemma_1_c N hB Γ1 h1.1 _ hε g f hg' hf M hM0 hM).2.2
      calc |cost Γ1 g - cost Γ1 f| ≤ (N.J : ℝ) * Real.sqrt (M * ((N.J : ℝ) * T * D + δ)) * T
            + ((N.J : ℝ) * T * D + δ) := this
        _ = _ := by ring
    have := limit_bound _ _ _ _ hε0 key
    calc |cost Γ1 g - cost Γ1 f| ≤ ((N.J : ℝ) * T) * Real.sqrt (M * ((N.J : ℝ) * T * D))
          + (N.J : ℝ) * T * D := this
      _ = _ := by ring
  have hT2 : totalDemand Γ2.d = T := by simp only [T, hd]
  have hC : |cost Γ1 g - cost Γ2 g| ≤ (N.J : ℝ) * T * D := by
    refine cost_close N hB Γ1 Γ2 D (fun j y hy0 hyT => ?_) g ⟨hg.1.1, fun σ => by rw [hg.1.2 σ, hd]⟩
    exact dist_bound N Γ1 Γ2 h1 h2 j y hy0 (by rw [hT2]; exact le_min hyT hyT)
  have : |cost Γ1 f - cost Γ2 g| ≤ |cost Γ1 g - cost Γ1 f| + |cost Γ1 g - cost Γ2 g| := by
    rw [abs_sub_comm (cost Γ1 g) (cost Γ1 f)]
    exact abs_sub_le _ _ _
  linarith

theorem l10d (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hd : Γ1.d = Γ2.d)
    (M : ℝ) (hM0 : 0 < M) (hM : ∀ j, LipOnIcc (Γ1.τ j) (totalDemand Γ1.d) M) :
    |WECost Γ1 - WECost Γ2|
        ≤ (Real.sqrt (M * N.J * totalDemand Γ1.d) + 2) * N.J * totalDemand Γ1.d
          * max (Real.sqrt (gameDist Γ1 Γ2)) (gameDist Γ1 Γ2) ∧
    (gameDist Γ1 Γ2 ≤ SOCost Γ1 / (2 * N.J * totalDemand Γ1.d) →
      |PoA Γ1 - PoA Γ2|
        ≤ 2 * (PoA Γ1 + Real.sqrt (M * N.J * totalDemand Γ1.d) + 2) / SOCost Γ1
            * (N.J * totalDemand Γ1.d)
          * max (Real.sqrt (gameDist Γ1 Γ2)) (gameDist Γ1 Γ2)) := by
  have hB := basic_of_standing N hN
  set T := totalDemand Γ1.d with hTdef
  set D := gameDist Γ1 Γ2 with hDdef
  have hT0 : 0 < T := h1.2.1
  have hD0 : 0 ≤ D := dist_nonneg Γ1 Γ2
  have hJ : (0:ℝ) < N.J := by exact_mod_cast J_pos N hB
  set X := max (Real.sqrt D) D with hX
  have hsD : Real.sqrt D ≤ X := le_max_left _ _
  have hDX : D ≤ X := le_max_right _ _
  have hsq : Real.sqrt (M * ((N.J : ℝ) * T * D)) = Real.sqrt (M * N.J * T) * Real.sqrt D := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  have hWE : |WECost Γ1 - WECost Γ2| ≤
      (Real.sqrt (M * N.J * T) + 2) * N.J * T * X := by
    obtain ⟨f0, hf0⟩ := we_exists N hB Γ1 h1.1
    obtain ⟨g0, hg0⟩ := we_exists N hB Γ2 h2.1
    unfold WECost
    refine sSup_gap (cost Γ1 '' {f | IsWE Γ1 f}) (cost Γ2 '' {f | IsWE Γ2 f})
      ⟨_, f0, hf0, rfl⟩ ⟨_, g0, hg0, rfl⟩ _ ?_
    rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
    refine (we_pair_close N hN Γ1 Γ2 h1 h2 hd M hM0 hM f g hf hg).trans ?_
    rw [hsq]
    have hs0 : 0 ≤ Real.sqrt (M * N.J * T) := Real.sqrt_nonneg _
    have e1 : (N.J : ℝ) * (Real.sqrt (M * N.J * T) * Real.sqrt D) * T
        ≤ (N.J : ℝ) * (Real.sqrt (M * N.J * T) * X) * T := by gcongr
    have e2 : (N.J : ℝ) * T * D ≤ (N.J : ℝ) * T * X := by gcongr
    nlinarith
  refine ⟨hWE, fun hsmall => ?_⟩
  -- PoA part
  have hS1 : 0 < SOCost Γ1 := so_pos N hB Γ1 h1
  have hSO : |SOCost Γ1 - SOCost Γ2| ≤ (N.J : ℝ) * T * D := lemma_10_a N hN Γ1 Γ2 h1 h2 hd
  have hW1 : 0 ≤ WECost Γ1 := we_nonneg N hB Γ1 h1.1
  have hJT : 0 < (N.J : ℝ) * T := mul_pos hJ hT0
  have hJTD : (N.J : ℝ) * T * D ≤ SOCost Γ1 / 2 := by
    have := hsmall
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hS2 : SOCost Γ1 / 2 ≤ SOCost Γ2 := by
    have := (abs_le.mp hSO).2; linarith
  have hS2p : 0 < SOCost Γ2 := by linarith
  set S1 := SOCost Γ1
  set S2 := SOCost Γ2
  set W1 := WECost Γ1
  set W2 := WECost Γ2
  set K := (Real.sqrt (M * N.J * T) + 2) * N.J * T
  have hPoA1 : PoA Γ1 = W1 / S1 := rfl
  have hPoA2 : PoA Γ2 = W2 / S2 := rfl
  rw [hPoA1, hPoA2]
  have hdiff : W1 / S1 - W2 / S2 = (W1 * (S2 - S1) + S1 * (W1 - W2)) / (S1 * S2) := by
    field_simp; ring
  rw [hdiff, abs_div, abs_of_pos (mul_pos hS1 hS2p)]
  have hnum : |W1 * (S2 - S1) + S1 * (W1 - W2)| ≤ W1 * ((N.J : ℝ) * T * X) + S1 * (K * X) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hW1, abs_of_pos hS1, abs_sub_comm S2 S1]
    have : (N.J : ℝ) * T * D ≤ (N.J : ℝ) * T * X := by gcongr
    gcongr
    · linarith
  rw [div_le_iff₀ (mul_pos hS1 hS2p)]
  have hX0 : 0 ≤ X := le_trans hD0 hDX
  have hK0 : 0 ≤ K := by positivity
  -- target: num ≤ 2 (W1/S1 + √ + 2)/S1 * (J T) * X * (S1 S2)
  have hgoal : W1 * ((N.J : ℝ) * T * X) + S1 * (K * X) ≤
      2 * (W1 / S1 + Real.sqrt (M * N.J * T) + 2) / S1 * (N.J * T) * X * (S1 * S2) := by
    have e : 2 * (W1 / S1 + Real.sqrt (M * N.J * T) + 2) / S1 * (N.J * T) * X * (S1 * S2)
        = 2 * S2 / S1 * (W1 * ((N.J : ℝ) * T * X) + S1 * (K * X)) := by
      simp only [K]; field_simp; ring
    rw [e]
    have h2 : 1 ≤ 2 * S2 / S1 := by rw [le_div_iff₀ hS1]; linarith
    have hn : 0 ≤ W1 * ((N.J : ℝ) * T * X) + S1 * (K * X) := by positivity
    nlinarith
  linarith

end PoAH

open KellyStochasticNetworks
open SensitivityPoA.Holder

theorem solution (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hd : Γ1.d = Γ2.d)
    (M : ℝ) (hM0 : 0 < M) (hM : ∀ j, LipOnIcc (Γ1.τ j) (totalDemand Γ1.d) M) :
    |WECost Γ1 - WECost Γ2|
        ≤ (Real.sqrt (M * N.J * totalDemand Γ1.d) + 2) * N.J * totalDemand Γ1.d
          * max (Real.sqrt (gameDist Γ1 Γ2)) (gameDist Γ1 Γ2) ∧
    (gameDist Γ1 Γ2 ≤ SOCost Γ1 / (2 * N.J * totalDemand Γ1.d) →
      |PoA Γ1 - PoA Γ2|
        ≤ 2 * (PoA Γ1 + Real.sqrt (M * N.J * totalDemand Γ1.d) + 2) / SOCost Γ1
            * (N.J * totalDemand Γ1.d)
          * max (Real.sqrt (gameDist Γ1 Γ2)) (gameDist Γ1 Γ2)) :=
  PoAH.l10d N hN Γ1 Γ2 h1 h2 hd M hM0 hM
