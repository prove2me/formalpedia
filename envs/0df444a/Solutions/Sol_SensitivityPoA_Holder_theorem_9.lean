-- Prove2me | solution 1 for SensitivityPoA.Holder.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T09:16:49.136474+00:00
-- url     : https://prove2.me/submissions/5fd7d3e1-29ae-4b28-8e6a-6306ab6656e6

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting
import Theorems.Thm_KellyStochasticNetworks_wardrop_equilibrium_exists
import Theorems.Thm_SensitivityPoA_Holder_lemma_10_d
import Theorems.Thm_SensitivityPoA_Holder_lemma_11_c

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

lemma le_pimax {N : Network} (Γ1 : Game N) (T : ℝ) (j : Fin N.J) :
    Γ1.τ j T ≤ ⨆ i, Γ1.τ i T :=
  le_ciSup (Finite.bddAbove_range (fun i => Γ1.τ i T)) j

end PoAH


open KellyStochasticNetworks
open SensitivityPoA.Holder

namespace PoAH

/-- the game with the costs of `Γ` frozen beyond `T(d)` and demand `e` -/
noncomputable def capGame {N : Network} (Γ : Game N) (e : Fin N.Sd → ℝ) : Game N :=
  ⟨fun j x => Γ.τ j (min x (totalDemand Γ.d)), e⟩

lemma M_nonneg {N : Network} (Γ : Game N) (hT : 0 < totalDemand Γ.d) (M : ℝ)
    (j : Fin N.J) (hM : LipOnIcc (Γ.τ j) (totalDemand Γ.d) M) : 0 ≤ M := by
  have := hM 0 ⟨le_rfl, hT.le⟩ (totalDemand Γ.d) ⟨hT.le, le_rfl⟩
  have h0 := abs_nonneg (Γ.τ j 0 - Γ.τ j (totalDemand Γ.d))
  rw [show (0:ℝ) - totalDemand Γ.d = -totalDemand Γ.d by ring, abs_neg, abs_of_pos hT] at this
  by_contra hc; push Not at hc
  nlinarith

lemma cap_lip {N : Network} (Γ : Game N) (hT : 0 < totalDemand Γ.d) (M M1 : ℝ) (hMM : M ≤ M1)
    (hM : ∀ j, LipOnIcc (Γ.τ j) (totalDemand Γ.d) M) (e : Fin N.Sd → ℝ) (S : ℝ) (j : Fin N.J) :
    LipOnIcc ((capGame Γ e).τ j) S M1 := by
  intro x hx y hy
  have hM0 := M_nonneg Γ hT M j (hM j)
  show |Γ.τ j (min x (totalDemand Γ.d)) - Γ.τ j (min y (totalDemand Γ.d))| ≤ M1 * |x - y|
  have h := hM j (min x (totalDemand Γ.d)) ⟨le_min hx.1 hT.le, min_le_right _ _⟩
    (min y (totalDemand Γ.d)) ⟨le_min hy.1 hT.le, min_le_right _ _⟩
  have h2 : |min x (totalDemand Γ.d) - min y (totalDemand Γ.d)| ≤ |x - y| := by
    have := abs_min_sub_min_le_max x (totalDemand Γ.d) y (totalDemand Γ.d)
    simpa using this
  calc _ ≤ M * |min x (totalDemand Γ.d) - min y (totalDemand Γ.d)| := h
    _ ≤ M * |x - y| := mul_le_mul_of_nonneg_left h2 hM0
    _ ≤ M1 * |x - y| := mul_le_mul_of_nonneg_right hMM (abs_nonneg _)

lemma cap_space {N : Network} (Γ : Game N) (hΓ : Γ ∈ gameSpace N) (e : Fin N.Sd → ℝ)
    (he : ∀ k, 0 ≤ e k) (hTe : 0 < totalDemand e) : capGame Γ e ∈ gameSpace N := by
  have hT := hΓ.2.1
  refine ⟨⟨fun j => ⟨?_, ?_, ?_⟩, he⟩, hTe, fun j x hx _ => ?_⟩
  · exact (hΓ.1.1 j).1.comp (continuous_id.min continuous_const).continuousOn
      (fun x (hx : 0 ≤ x) => show 0 ≤ min x (totalDemand Γ.d) from le_min hx hT.le)
  · intro a ha b hb hab
    exact (hΓ.1.1 j).2.1 (show 0 ≤ min a (totalDemand Γ.d) from le_min ha hT.le)
      (show 0 ≤ min b (totalDemand Γ.d) from le_min hb hT.le) (min_le_min_right _ hab)
  · intro x hx; exact (hΓ.1.1 j).2.2 _ (le_min hx hT.le)
  · exact hΓ.2.2 j _ (lt_min hx hT) (min_le_right _ _)

/-- freezing the costs beyond `T(d)` does not change the PoA -/
lemma poa_cap (N : Network) (hN : N.Basic) (Γ : Game N) :
    PoA (capGame Γ Γ.d) = PoA Γ := by
  have hlf : ∀ f, IsFlow Γ f → ∀ j,
      (capGame Γ Γ.d).τ j (linkFlow N.A f j) = Γ.τ j (linkFlow N.A f j) := by
    intro f hf j
    show Γ.τ j (min _ _) = _
    rw [min_eq_left (lf_le_T N hN hf j)]
  have hflow : ∀ f, IsFlow (capGame Γ Γ.d) f ↔ IsFlow Γ f := fun f => Iff.rfl
  have hcost : ∀ f, IsFlow Γ f → cost (capGame Γ Γ.d) f = cost Γ f := by
    intro f hf; unfold cost; exact Finset.sum_congr rfl (fun j _ => by rw [hlf f hf j])
  have hwe : ∀ f, IsWE (capGame Γ Γ.d) f ↔ IsWE Γ f := by
    intro f
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun r r' hs hp => ?_⟩
      have := h2 r r' hs hp
      simpa only [hlf f h1] using this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun r r' hs hp => ?_⟩
      have := h2 r r' hs hp
      show ∑ j, (capGame Γ Γ.d).τ j (linkFlow N.A f j) * N.A j r ≤
        ∑ j, (capGame Γ Γ.d).τ j (linkFlow N.A f j) * N.A j r'
      simpa only [hlf f h1] using this
  have hSO : SOCost (capGame Γ Γ.d) = SOCost Γ := by
    unfold SOCost
    congr 1
    ext c; constructor
    · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, (hcost f hf).symm⟩
    · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, hcost f hf⟩
  have hWE : WECost (capGame Γ Γ.d) = WECost Γ := by
    unfold WECost
    congr 1
    ext c; constructor
    · rintro ⟨f, hf, rfl⟩
      have hf' := (hwe f).1 hf
      exact ⟨f, hf', (hcost f hf'.1).symm⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, (hwe f).2 hf, hcost f hf.1⟩
  unfold PoA; rw [hSO, hWE]

lemma T_sub_le {N : Network} (e1 e2 : Fin N.Sd → ℝ) (D : ℝ) (h : ∀ k, |e1 k - e2 k| ≤ D) :
    |totalDemand e1 - totalDemand e2| ≤ N.Sd * D := by
  unfold totalDemand; rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |e1 k - e2 k| ≤ ∑ _k : Fin N.Sd, D := Finset.sum_le_sum (fun k _ => h k)
    _ = N.Sd * D := by simp

/-- distance between the auxiliary game `Γ'' = (τ̂, d')` and `Γ' = (σ, d')` -/
lemma dist_cap_right (N : Network) (Γ Γ' : Game N) (hΓ : Γ ∈ gameSpace N) (hΓ' : Γ' ∈ gameSpace N) :
    gameDist (capGame Γ Γ'.d) Γ' ≤ gameDist Γ Γ' := by
  set D := gameDist Γ Γ'
  set T := totalDemand Γ.d
  have hT := hΓ.2.1
  have claim : ∀ j y, 0 ≤ y → y ≤ totalDemand Γ'.d → |Γ.τ j (min y T) - Γ'.τ j y| ≤ D := by
    intro j y hy0 hyT
    rcases le_or_gt y T with h | h
    · rw [min_eq_left h]; exact dist_bound N Γ Γ' hΓ hΓ' j y hy0 (le_min h hyT)
    · rw [min_eq_right h.le]
      have a1 := dist_bound N Γ Γ' hΓ hΓ' j T hT.le (le_min le_rfl (by linarith))
      have a2 := dist_end Γ Γ' j
      have m1 : Γ'.τ j T ≤ Γ'.τ j y := (hΓ'.1.1 j).2.1 (Set.mem_Ici.mpr hT.le)
        (Set.mem_Ici.mpr hy0) h.le
      have m2 : Γ'.τ j y ≤ Γ'.τ j (totalDemand Γ'.d) := (hΓ'.1.1 j).2.1 (Set.mem_Ici.mpr hy0)
        (Set.mem_Ici.mpr (by linarith)) hyT
      rw [abs_le] at a1 a2 ⊢
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  refine dist_le _ _ D (dist_nonneg Γ Γ') (fun k => by show |Γ'.d k - Γ'.d k| ≤ D; simp; exact dist_nonneg Γ Γ') ?_ ?_
  · intro j y hy0 hyT
    exact claim j y hy0 (le_trans hyT (min_le_left _ _))
  · intro j
    exact claim j _ (T_nonneg Γ' hΓ'.1) le_rfl

/-- distance between two capped games along the cost slice -/
lemma dist_cap_cap (N : Network) (Γ : Game N) (hT : 0 < totalDemand Γ.d) (M M1 : ℝ)
    (hMM : M ≤ M1) (hM1 : 1 ≤ M1) (hM : ∀ j, LipOnIcc (Γ.τ j) (totalDemand Γ.d) M)
    (e1 e2 : Fin N.Sd → ℝ) (he1 : ∀ k, 0 ≤ e1 k) (he2 : ∀ k, 0 ≤ e2 k) (hSd : 1 ≤ (N.Sd : ℝ))
    (D : ℝ) (hD : ∀ k, |e1 k - e2 k| ≤ D) (hD0 : 0 ≤ D) :
    gameDist (capGame Γ e1) (capGame Γ e2) ≤ M1 * N.Sd * D := by
  have hB : D ≤ M1 * N.Sd * D := by
    have : 1 ≤ M1 * N.Sd := by nlinarith
    nlinarith
  refine dist_le _ _ _ (le_trans hD0 hB) (fun k => (hD k).trans hB) (fun j y _ _ => by
    rw [show (capGame Γ e1).τ = (capGame Γ e2).τ from rfl, sub_self, abs_zero]; linarith) ?_
  intro j
  have h1 : 0 ≤ totalDemand e1 := Finset.sum_nonneg (fun k _ => he1 k)
  have h2 : 0 ≤ totalDemand e2 := Finset.sum_nonneg (fun k _ => he2 k)
  have := cap_lip Γ hT M M1 hMM hM e1 (max (totalDemand e1) (totalDemand e2)) j
    (totalDemand e1) ⟨h1, le_max_left _ _⟩ (totalDemand e2) ⟨h2, le_max_right _ _⟩
  have hTT := T_sub_le e1 e2 D hD
  calc |(capGame Γ e1).τ j (totalDemand (capGame Γ e1).d) -
        (capGame Γ e2).τ j (totalDemand (capGame Γ e2).d)|
      = |(capGame Γ e1).τ j (totalDemand e1) - (capGame Γ e1).τ j (totalDemand e2)| := rfl
    _ ≤ M1 * |totalDemand e1 - totalDemand e2| := this
    _ ≤ M1 * (N.Sd * D) := mul_le_mul_of_nonneg_left hTT (by linarith)
    _ = M1 * N.Sd * D := by ring

end PoAH


open KellyStochasticNetworks
open SensitivityPoA.Holder

namespace PoAH

lemma cap_bounds (N : Network) (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (e : Fin N.Sd → ℝ) (he : ∀ k, 0 ≤ e k)
    (hT1 : totalDemand Γ.d / 2 ≤ totalDemand e) (hT2 : totalDemand e ≤ 3 * totalDemand Γ.d / 2)
    (c0 : ℝ) (hc0 : ∀ j, c0 ≤ Γ.τ j (totalDemand Γ.d / (2 * N.J))) (hc0p : 0 < c0) :
    capGame Γ e ∈ gameSpace N ∧
    totalDemand Γ.d / (2 * N.J) * c0 ≤ SOCost (capGame Γ e) ∧
    WECost (capGame Γ e) ≤ N.J * (3 * totalDemand Γ.d / 2) * (⨆ j, Γ.τ j (totalDemand Γ.d)) ∧
    0 ≤ (⨆ j, (capGame Γ e).τ j (totalDemand (capGame Γ e).d)) ∧
    (⨆ j, (capGame Γ e).τ j (totalDemand (capGame Γ e).d)) ≤ (⨆ j, Γ.τ j (totalDemand Γ.d)) := by
  have hB := basic_of_standing N hN
  set T := totalDemand Γ.d with hTdef
  have hT : 0 < T := hΓ.2.1
  have hJn := J_pos N hB
  have hJ : (0:ℝ) < N.J := by exact_mod_cast hJn
  have hJ1 : (1:ℝ) ≤ N.J := by exact_mod_cast hJn
  have hTe : 0 < totalDemand e := by linarith
  have hG := cap_space Γ hΓ e he hTe
  set P := ⨆ j, Γ.τ j T
  have hPj : ∀ j, Γ.τ j T ≤ P := fun j => le_pimax Γ T j
  have hP0 : 0 ≤ P := le_trans ((hΓ.1.1 ⟨0, hJn⟩).2.2 T hT.le) (hPj _)
  have hGT : ∀ j, (capGame Γ e).τ j (totalDemand e) ≤ P := by
    intro j
    show Γ.τ j (min (totalDemand e) T) ≤ P
    exact ((hΓ.1.1 j).2.1 (Set.mem_Ici.mpr (le_min hTe.le hT.le)) (Set.mem_Ici.mpr hT.le)
      (min_le_right _ _)).trans (hPj j)
  refine ⟨hG, ?_, ?_, ?_, ?_⟩
  · have hx : T / (2 * N.J) ≤ min (totalDemand e / N.J) T := by
      refine le_min ?_ ?_
      · rw [div_le_div_iff₀ (by positivity) hJ]; nlinarith
      · rw [div_le_iff₀ (by positivity)]; nlinarith
    have hc : ∀ j, c0 ≤ (capGame Γ e).τ j (totalDemand (capGame Γ e).d / N.J) := by
      intro j
      show c0 ≤ Γ.τ j (min (totalDemand e / N.J) T)
      exact (hc0 j).trans ((hΓ.1.1 j).2.1 (Set.mem_Ici.mpr (by positivity))
        (Set.mem_Ici.mpr (le_trans (by positivity) hx)) hx)
    have := so_ge N hB (capGame Γ e) hG.1 c0 hc
    have h2 : T / (2 * N.J) * c0 ≤ totalDemand e / N.J * c0 := by
      apply mul_le_mul_of_nonneg_right _ hc0p.le
      rw [div_le_div_iff₀ (by positivity) hJ]; nlinarith
    exact h2.trans this
  · refine we_le N _ _ (by positivity) (fun f hf => ?_)
    refine (cost_le N hB _ hG.1 f hf P hGT).trans ?_
    show (N.J : ℝ) * totalDemand e * P ≤ _
    gcongr
  · exact le_ciSup_of_le (Finite.bddAbove_range _) ⟨0, hJn⟩
      ((hG.1.1 _).2.2 _ (T_nonneg _ hG.1))
  · haveI : Nonempty (Fin N.J) := ⟨⟨0, hJn⟩⟩
    exact ciSup_le hGT

lemma sqrt_bound (D : ℝ) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) : D ≤ Real.sqrt D := by
  rw [show D = Real.sqrt D * Real.sqrt D from (Real.mul_self_sqrt hD0).symm]
  have h0 := Real.sqrt_nonneg D
  have h1 : Real.sqrt D ≤ 1 := by rw [Real.sqrt_le_one]; exact hD1
  have : Real.sqrt D * Real.sqrt D ≤ Real.sqrt D * 1 := mul_le_mul_of_nonneg_left h1 h0
  rw [Real.mul_self_sqrt hD0] at this ⊢
  linarith

end PoAH


open KellyStochasticNetworks
open SensitivityPoA.Holder

namespace PoAH


lemma partI (N : Network) (hN : N.Standing) (Γ Γ' : Game N) (hΓ : Γ ∈ gameSpace N)
    (hΓ' : Γ' ∈ gameSpace N) (M M1 : ℝ) (hMM : M ≤ M1) (hM10 : 0 < M1)
    (hM : ∀ j, LipOnIcc (Γ.τ j) (totalDemand Γ.d) M)
    (s0 T3 ρ0 D : ℝ) (hs0 : 0 < s0) (hS : s0 ≤ SOCost (capGame Γ Γ'.d))
    (hpa : 0 ≤ PoA (capGame Γ Γ'.d)) (hpb : PoA (capGame Γ Γ'.d) ≤ ρ0)
    (hTd2 : totalDemand Γ'.d ≤ T3) (hD0 : 0 ≤ D) (hD1 : D ≤ 1)
    (hDist : gameDist (capGame Γ Γ'.d) Γ' ≤ D) (hcond : D * (2 * N.J * T3) ≤ s0) :
    |PoA (capGame Γ Γ'.d) - PoA Γ'| ≤
      2 * (ρ0 + Real.sqrt (M1 * N.J * T3) + 2) / s0 * (N.J * T3) * Real.sqrt D := by
  have hB := basic_of_standing N hN
  have hJ : (0:ℝ) < N.J := by exact_mod_cast J_pos N hB
  have hT := hΓ.2.1
  have hTd0 : 0 < totalDemand Γ'.d := hΓ'.2.1
  set G := capGame Γ Γ'.d
  have hG : G ∈ gameSpace N := cap_space Γ hΓ Γ'.d hΓ'.1.2 hTd0
  have hD10 := dist_nonneg G Γ'
  have hlip : ∀ j, LipOnIcc (G.τ j) (totalDemand G.d) M1 :=
    fun j => cap_lip Γ hT M M1 hMM hM Γ'.d _ j
  have hGT : totalDemand G.d = totalDemand Γ'.d := rfl
  have hSG : 0 < SOCost G := lt_of_lt_of_le hs0 hS
  have hcond' : gameDist G Γ' ≤ SOCost G / (2 * N.J * totalDemand G.d) := by
    rw [hGT, le_div_iff₀ (mul_pos (mul_pos two_pos hJ) hTd0)]
    have h1 : 2 * (N.J : ℝ) * totalDemand Γ'.d ≤ 2 * N.J * T3 := by
      have := mul_le_mul_of_nonneg_left hTd2 (mul_pos two_pos hJ).le; linarith
    have h2 : gameDist G Γ' * (2 * N.J * totalDemand Γ'.d) ≤ D * (2 * N.J * T3) :=
      mul_le_mul hDist h1 (mul_pos (mul_pos two_pos hJ) hTd0).le hD0
    linarith
  have h10 := (lemma_10_d N hN G Γ' hG hΓ' rfl M1 hM10 hlip).2 hcond'
  have hT30 : 0 ≤ T3 := le_trans hTd0.le hTd2
  have hcoef : 2 * (PoA G + Real.sqrt (M1 * N.J * totalDemand G.d) + 2) / SOCost G
      * (N.J * totalDemand G.d) ≤ 2 * (ρ0 + Real.sqrt (M1 * N.J * T3) + 2) / s0 * (N.J * T3) := by
    rw [hGT]
    have : Real.sqrt (M1 * N.J * totalDemand Γ'.d) ≤ Real.sqrt (M1 * N.J * T3) :=
      Real.sqrt_le_sqrt (by gcongr)
    have : 0 ≤ ρ0 := hpa.trans hpb
    gcongr
  have hmax : max (Real.sqrt (gameDist G Γ')) (gameDist G Γ') ≤ Real.sqrt D := by
    have h1 : Real.sqrt (gameDist G Γ') ≤ Real.sqrt D := Real.sqrt_le_sqrt hDist
    have h2 : gameDist G Γ' ≤ Real.sqrt (gameDist G Γ') :=
      sqrt_bound _ hD10 (le_trans hDist hD1)
    exact max_le h1 (h2.trans h1)
  have hκ : 0 ≤ 2 * (ρ0 + Real.sqrt (M1 * N.J * T3) + 2) / s0 * (N.J * T3) := by
    have : 0 ≤ ρ0 := hpa.trans hpb
    positivity
  refine h10.trans ?_
  calc _ ≤ 2 * (ρ0 + Real.sqrt (M1 * N.J * T3) + 2) / s0 * (N.J * T3)
        * max (Real.sqrt (gameDist G Γ')) (gameDist G Γ') :=
        mul_le_mul_of_nonneg_right hcoef (le_trans (Real.sqrt_nonneg _) (le_max_left _ _))
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax hκ

lemma partII (N : Network) (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (M M1 : ℝ) (hMM : M ≤ M1) (hM1 : 1 ≤ M1)
    (hM : ∀ j, LipOnIcc (Γ.τ j) (totalDemand Γ.d) M)
    (s0 T3 ρ0 a0 b0 P D : ℝ) (hs0 : 0 < s0) (hPdef : P = ⨆ j, Γ.τ j (totalDemand Γ.d))
    (ha0 : a0 = 2 * (N.J * N.Sd * P + N.J * T3 * M1 * N.Sd))
    (hb0 : b0 = 2 * ((Real.sqrt (M1 * N.J * T3) + 2) * N.J * T3 + N.J * N.Sd * P) * Real.sqrt M1)
    (f1 f2 : Fin N.Sd → ℝ) (hG1 : capGame Γ f1 ∈ gameSpace N) (hG2 : capGame Γ f2 ∈ gameSpace N)
    (hf1 : ∀ k, 0 ≤ f1 k) (hf2 : ∀ k, 0 ≤ f2 k)
    (hS1 : s0 ≤ SOCost (capGame Γ f1))
    (hpa : 0 ≤ PoA (capGame Γ f1)) (hpb : PoA (capGame Γ f1) ≤ ρ0)
    (hP10 : 0 ≤ ⨆ j, (capGame Γ f1).τ j (totalDemand (capGame Γ f1).d))
    (hP1 : (⨆ j, (capGame Γ f1).τ j (totalDemand (capGame Γ f1).d)) ≤ P)
    (ha1 : 0 < totalDemand f1) (ha2 : totalDemand f1 ≤ T3)
    (h12 : totalDemand f2 ≤ totalDemand f1) (hfD : ∀ k, |f1 k - f2 k| ≤ D)
    (hD0 : 0 ≤ D) (hD1 : D ≤ 1)
    (hc3 : M1 * N.Sd * D * N.Sd < totalDemand f1) (hc5 : M1 * N.Sd * D * (2 * a0) ≤ s0) :
    |PoA (capGame Γ f1) - PoA (capGame Γ f2)| ≤
      (2 * ρ0 * a0 + 2 * b0) / s0 * (N.Sd * Real.sqrt M1 + Real.sqrt M1 * N.Sd * (M1 * N.Sd))
        * Real.sqrt D := by
  have hB := basic_of_standing N hN
  have hJ : (0:ℝ) < N.J := by exact_mod_cast J_pos N hB
  have hSd : (1:ℝ) ≤ N.Sd := by exact_mod_cast hB.2.2.1
  have hSd0 : (0:ℝ) < N.Sd := by linarith
  have hT := hΓ.2.1
  have hM10 : 0 < M1 := by linarith
  set G1 := capGame Γ f1
  set G2 := capGame Γ f2
  have hD2 := dist_cap_cap N Γ hT M M1 hMM hM1 hM f1 f2 hf1 hf2 hSd D hfD hD0
  set D2 := gameDist G1 G2
  have hD20 : 0 ≤ D2 := dist_nonneg G1 G2
  have hlip : ∀ j, LipOnIcc (G1.τ j) (totalDemand G1.d) M1 :=
    fun j => cap_lip Γ hT M M1 hMM hM f1 _ j
  set P1 := ⨆ j, G1.τ j (totalDemand G1.d)
  have hT1 : totalDemand G1.d = totalDemand f1 := rfl
  have hP0 : 0 ≤ P := hP10.trans hP1
  have hT30 : 0 ≤ T3 := ha1.le.trans ha2
  have hνs : 0 < 2 * (N.J * N.Sd * P1 + N.J * totalDemand G1.d * M1 * N.Sd) := by
    rw [hT1]; positivity
  have hνs2 : 2 * (N.J * N.Sd * P1 + N.J * totalDemand G1.d * M1 * N.Sd) ≤ a0 := by
    rw [hT1, ha0]; gcongr
  have hlt2 : D2 < totalDemand G1.d / N.Sd := by
    rw [hT1, lt_div_iff₀ hSd0]
    have := mul_le_mul_of_nonneg_right hD2 hSd0.le
    linarith
  have hsm2 : D2 ≤ SOCost G1 / (2 * (2 * (N.J * N.Sd * P1
      + N.J * totalDemand G1.d * M1 * N.Sd))) := by
    rw [le_div_iff₀ (by positivity)]
    have : D2 * (2 * (2 * (N.J * N.Sd * P1 + N.J * totalDemand G1.d * M1 * N.Sd)))
        ≤ M1 * N.Sd * D * (2 * a0) :=
      mul_le_mul hD2 (by linarith) (by positivity) (by positivity)
    linarith
  have h11 := lemma_11_c N hN G1 G2 hG1 hG2 rfl h12 M1 hM1 hlip hlt2 hsm2
  have hνt : 2 * ((Real.sqrt (M1 * N.J * totalDemand G1.d) + 2) * N.J * totalDemand G1.d
      + N.J * N.Sd * P1) * Real.sqrt M1 ≤ b0 := by
    rw [hT1, hb0]
    have : Real.sqrt (M1 * N.J * totalDemand f1) ≤ Real.sqrt (M1 * N.J * T3) :=
      Real.sqrt_le_sqrt (by gcongr)
    gcongr
  have hνp : (2 * PoA G1 * (2 * (N.J * N.Sd * P1 + N.J * totalDemand G1.d * M1 * N.Sd))
      + 2 * (2 * ((Real.sqrt (M1 * N.J * totalDemand G1.d) + 2) * N.J * totalDemand G1.d
      + N.J * N.Sd * P1) * Real.sqrt M1)) / SOCost G1 ≤ (2 * ρ0 * a0 + 2 * b0) / s0 := by
    have : 0 ≤ totalDemand G1.d := by rw [hT1]; exact ha1.le
    have : 0 ≤ ρ0 := hpa.trans hpb
    have : 0 ≤ 2 * ρ0 * a0 + 2 * b0 := by
      have : 0 ≤ a0 := by rw [ha0]; positivity
      have : 0 ≤ b0 := by rw [hb0]; positivity
      positivity
    gcongr
  have hsM := Real.sqrt_nonneg M1
  have hsDD := Real.sqrt_nonneg D
  have hX : max (Real.sqrt (N.Sd * D2)) (Real.sqrt M1 * (N.Sd * D2)) ≤
      (N.Sd * Real.sqrt M1 + Real.sqrt M1 * N.Sd * (M1 * N.Sd)) * Real.sqrt D := by
    have q1 : Real.sqrt (N.Sd * D2) ≤ N.Sd * Real.sqrt M1 * Real.sqrt D := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have : (N.Sd * Real.sqrt M1 * Real.sqrt D) ^ 2 = N.Sd * (M1 * N.Sd * D) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hM10.le, Real.sq_sqrt hD0]; ring
      rw [this]; exact mul_le_mul_of_nonneg_left hD2 hSd0.le
    have q2 : Real.sqrt M1 * (N.Sd * D2) ≤ Real.sqrt M1 * N.Sd * (M1 * N.Sd) * Real.sqrt D := by
      have hh : D2 ≤ M1 * N.Sd * Real.sqrt D :=
        hD2.trans (mul_le_mul_of_nonneg_left (sqrt_bound D hD0 hD1) (by positivity))
      have : N.Sd * D2 ≤ N.Sd * (M1 * N.Sd * Real.sqrt D) :=
        mul_le_mul_of_nonneg_left hh hSd0.le
      calc Real.sqrt M1 * (N.Sd * D2) ≤ Real.sqrt M1 * (N.Sd * (M1 * N.Sd * Real.sqrt D)) :=
            mul_le_mul_of_nonneg_left this hsM
        _ = _ := by ring
    have hq1 : 0 ≤ N.Sd * Real.sqrt M1 * Real.sqrt D := by positivity
    have hq2 : 0 ≤ Real.sqrt M1 * N.Sd * (M1 * N.Sd) * Real.sqrt D := by positivity
    rw [add_mul]
    exact max_le (by linarith) (by linarith)
  refine h11.trans ?_
  have hX0 : 0 ≤ max (Real.sqrt (N.Sd * D2)) (Real.sqrt M1 * (N.Sd * D2)) :=
    le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hν0 : 0 ≤ (2 * ρ0 * a0 + 2 * b0) / s0 := by
    have : 0 ≤ ρ0 := hpa.trans hpb
    have : 0 ≤ a0 := by rw [ha0]; positivity
    have : 0 ≤ b0 := by rw [hb0]; positivity
    positivity
  calc _ ≤ (2 * ρ0 * a0 + 2 * b0) / s0 * max (Real.sqrt (N.Sd * D2)) (Real.sqrt M1 * (N.Sd * D2)) :=
        mul_le_mul_of_nonneg_right hνp hX0
    _ ≤ (2 * ρ0 * a0 + 2 * b0) / s0 *
        ((N.Sd * Real.sqrt M1 + Real.sqrt M1 * N.Sd * (M1 * N.Sd)) * Real.sqrt D) :=
        mul_le_mul_of_nonneg_left hX hν0
    _ = _ := by ring

theorem t9 (N : Network) (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (M : ℝ) (hM : ∀ j, LipOnIcc (Γ.τ j) (totalDemand Γ.d) M) :
    ∃ ε > 0, ∃ κ > 0, ∀ Γ' ∈ gameSpace N, gameDist Γ Γ' < ε →
      |PoA Γ - PoA Γ'| ≤ κ * Real.sqrt (gameDist Γ Γ') := by
  have hB := basic_of_standing N hN
  have hT : 0 < totalDemand Γ.d := hΓ.2.1
  have hJn := J_pos N hB
  have hJ : (0:ℝ) < N.J := by exact_mod_cast hJn
  have hJ1 : (1:ℝ) ≤ N.J := by exact_mod_cast hJn
  have hSd : (1:ℝ) ≤ N.Sd := by exact_mod_cast hB.2.2.1
  have hSd0 : (0:ℝ) < N.Sd := by linarith
  obtain ⟨T, hTdef⟩ : ∃ T, T = totalDemand Γ.d := ⟨_, rfl⟩
  rw [← hTdef] at hT
  obtain ⟨M1, hM1def⟩ : ∃ M1, M1 = max M 1 := ⟨_, rfl⟩
  have hMM : M ≤ M1 := hM1def ▸ le_max_left _ _
  have hM1 : 1 ≤ M1 := hM1def ▸ le_max_right _ _
  have hM10 : 0 < M1 := by linarith
  obtain ⟨P, hPdef⟩ : ∃ P, P = ⨆ j, Γ.τ j (totalDemand Γ.d) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := hPdef ▸ le_trans ((hΓ.1.1 ⟨0, hJn⟩).2.2 _ (hTdef ▸ hT.le)) (le_pimax Γ _ _)
  have hne : (Finset.univ : Finset (Fin N.J)).Nonempty := ⟨⟨0, hJn⟩, Finset.mem_univ _⟩
  obtain ⟨j0, _, hj0⟩ := Finset.exists_min_image Finset.univ
    (fun j => Γ.τ j (totalDemand Γ.d / (2 * N.J))) hne
  obtain ⟨c0, hc0def⟩ : ∃ c0, c0 = Γ.τ j0 (totalDemand Γ.d / (2 * N.J)) := ⟨_, rfl⟩
  have hc0p : 0 < c0 := by
    rw [hc0def]
    refine hΓ.2.2 j0 _ (by rw [← hTdef]; positivity) ?_
    rw [div_le_iff₀ (by positivity)]
    have := hΓ.2.1
    nlinarith
  have hc0 : ∀ j, c0 ≤ Γ.τ j (totalDemand Γ.d / (2 * N.J)) :=
    fun j => hc0def ▸ hj0 j (Finset.mem_univ j)
  obtain ⟨s0, hs0def⟩ : ∃ s0, s0 = T / (2 * N.J) * c0 := ⟨_, rfl⟩
  have hs0 : 0 < s0 := by rw [hs0def]; positivity
  obtain ⟨T3, hT3def⟩ : ∃ T3, T3 = 3 * T / 2 := ⟨_, rfl⟩
  have hT3 : 0 < T3 := by rw [hT3def]; positivity
  obtain ⟨ρ0, hρ0def⟩ : ∃ ρ0, ρ0 = N.J * T3 * P / s0 := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ0 := by rw [hρ0def]; positivity
  obtain ⟨a0, ha0def⟩ : ∃ a0, a0 = 2 * (N.J * N.Sd * P + N.J * T3 * M1 * N.Sd) := ⟨_, rfl⟩
  have ha0 : 0 < a0 := by rw [ha0def]; positivity
  obtain ⟨b0, hb0def⟩ : ∃ b0,
      b0 = 2 * ((Real.sqrt (M1 * N.J * T3) + 2) * N.J * T3 + N.J * N.Sd * P) * Real.sqrt M1 :=
    ⟨_, rfl⟩
  have hb0 : 0 ≤ b0 := by rw [hb0def]; positivity
  obtain ⟨κ1, hκ1def⟩ : ∃ κ1, κ1 = 2 * (ρ0 + Real.sqrt (M1 * N.J * T3) + 2) / s0 * (N.J * T3) :=
    ⟨_, rfl⟩
  have hκ1 : 0 ≤ κ1 := by rw [hκ1def]; positivity
  obtain ⟨κ2, hκ2def⟩ : ∃ κ2, κ2 = (2 * ρ0 * a0 + 2 * b0) / s0 *
      (N.Sd * Real.sqrt M1 + Real.sqrt M1 * N.Sd * (M1 * N.Sd)) := ⟨_, rfl⟩
  have hκ2 : 0 ≤ κ2 := by rw [hκ2def]; positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = min (min 1 (T / (2 * N.Sd))) (min (T / (2 * (M1 * N.Sd * N.Sd)))
    (min (s0 / (3 * N.J * T)) (s0 / (2 * a0 * (M1 * N.Sd))))) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  refine ⟨ε, hε, κ1 + κ2 + 1, by positivity, ?_⟩
  intro Γ' hΓ' hlt
  obtain ⟨D, hDdef⟩ : ∃ D, D = gameDist Γ Γ' := ⟨_, rfl⟩
  rw [← hDdef] at hlt ⊢
  have hD0 : 0 ≤ D := hDdef ▸ dist_nonneg Γ Γ'
  rw [hεdef] at hlt
  have e1 : D < 1 := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : D < T / (2 * N.Sd) := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_right _ _))
  have e3 : D < T / (2 * (M1 * N.Sd * N.Sd)) :=
    lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : D < s0 / (3 * N.J * T) :=
    lt_of_lt_of_le hlt ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e5 : D < s0 / (2 * a0 * (M1 * N.Sd)) :=
    lt_of_lt_of_le hlt ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  clear hlt
  have hdk : ∀ k, |Γ.d k - Γ'.d k| ≤ D := fun k => hDdef ▸ dist_demand Γ Γ' k
  have hdk' : ∀ k, |Γ'.d k - Γ.d k| ≤ D := fun k => by rw [abs_sub_comm]; exact hdk k
  have hTT := T_sub_le Γ.d Γ'.d D hdk
  rw [← hTdef] at hTT
  have hSdD : N.Sd * D < T / 2 := by
    rw [lt_div_iff₀ (by positivity)] at e2; linarith
  have hTd1 : T / 2 ≤ totalDemand Γ'.d := by
    have := (abs_le.mp hTT).2; linarith
  have hTd2 : totalDemand Γ'.d ≤ T3 := by
    have := (abs_le.mp hTT).1; rw [hT3def]; linarith
  have hTd0 : 0 < totalDemand Γ'.d := hΓ'.2.1
  have hTa1 : totalDemand Γ.d / 2 ≤ totalDemand Γ.d := by linarith
  have hTa2 : totalDemand Γ.d ≤ 3 * totalDemand Γ.d / 2 := by linarith
  -- bounds
  have poa_bd : ∀ G : Game N, G ∈ gameSpace N → s0 ≤ SOCost G → WECost G ≤ N.J * T3 * P →
      0 ≤ PoA G ∧ PoA G ≤ ρ0 := by
    intro G hG hS hW
    have hS0 : 0 < SOCost G := lt_of_lt_of_le hs0 hS
    have hW0 := we_nonneg N hB G hG.1
    refine ⟨div_nonneg hW0 hS0.le, ?_⟩
    show WECost G / SOCost G ≤ ρ0
    rw [hρ0def]
    calc WECost G / SOCost G ≤ N.J * T3 * P / SOCost G := by gcongr
      _ ≤ N.J * T3 * P / s0 := by gcongr
  have cb : ∀ e : Fin N.Sd → ℝ, (∀ k, 0 ≤ e k) → T / 2 ≤ totalDemand e → totalDemand e ≤ T3 →
      capGame Γ e ∈ gameSpace N ∧ s0 ≤ SOCost (capGame Γ e) ∧
      (0 ≤ PoA (capGame Γ e) ∧ PoA (capGame Γ e) ≤ ρ0) ∧
      0 ≤ (⨆ j, (capGame Γ e).τ j (totalDemand (capGame Γ e).d)) ∧
      (⨆ j, (capGame Γ e).τ j (totalDemand (capGame Γ e).d)) ≤ P := by
    intro e he h1 h2
    obtain ⟨g1, g2, g3, g4, g5⟩ := cap_bounds N hN Γ hΓ e he (hTdef ▸ h1)
      (by rw [← hTdef]; rw [hT3def] at h2; exact h2) c0 hc0 hc0p
    rw [← hTdef, ← hs0def] at g2
    rw [← hPdef] at g3
    rw [← hTdef, ← hT3def] at g3
    rw [← hPdef] at g5
    exact ⟨g1, g2, poa_bd _ g1 g2 g3, g4, g5⟩
  obtain ⟨hG'', hS'', hp'', -, -⟩ := cb Γ'.d hΓ'.1.2 hTd1 hTd2
  -- part I
  have pI := partI N hN Γ Γ' hΓ hΓ' M M1 hMM hM10 hM s0 T3 ρ0 D hs0 hS'' hp''.1 hp''.2 hTd2
    hD0 e1.le (hDdef ▸ dist_cap_right N Γ Γ' hΓ hΓ') (by
      rw [lt_div_iff₀ (by positivity)] at e4
      have : (2 : ℝ) * N.J * T3 = 3 * N.J * T := by rw [hT3def]; ring
      rw [this]; linarith)
  rw [← hκ1def] at pI
  -- part II
  have hc5 : M1 * N.Sd * D * (2 * a0) ≤ s0 := by
    rw [lt_div_iff₀ (by positivity)] at e5; linarith
  have hc3' : M1 * N.Sd * D * N.Sd < T / 2 := by
    rw [lt_div_iff₀ (by positivity)] at e3; linarith
  have pII : |PoA (capGame Γ Γ.d) - PoA (capGame Γ Γ'.d)| ≤ κ2 * Real.sqrt D := by
    have hTa1' : T / 2 ≤ totalDemand Γ.d := by rw [← hTdef]; linarith
    have hTa2' : totalDemand Γ.d ≤ T3 := by rw [← hTdef, hT3def]; linarith
    obtain ⟨hGa, hSa, hpa, hPa0, hPa⟩ := cb Γ.d hΓ.1.2 hTa1' hTa2'
    obtain ⟨hGd, hSd', hpd, hPd0, hPd⟩ := cb Γ'.d hΓ'.1.2 hTd1 hTd2
    rw [hκ2def]
    rcases le_total (totalDemand Γ'.d) (totalDemand Γ.d) with h | h
    · exact partII N hN Γ hΓ M M1 hMM hM1 hM s0 T3 ρ0 a0 b0 P D hs0 hPdef ha0def hb0def
        Γ.d Γ'.d hGa hGd hΓ.1.2 hΓ'.1.2 hSa hpa.1 hpa.2 hPa0 hPa (by rw [← hTdef]; exact hT)
        hTa2' h hdk hD0 e1.le (by rw [← hTdef]; linarith) hc5
    · rw [abs_sub_comm]
      exact partII N hN Γ hΓ M M1 hMM hM1 hM s0 T3 ρ0 a0 b0 P D hs0 hPdef ha0def hb0def
        Γ'.d Γ.d hGd hGa hΓ'.1.2 hΓ.1.2 hSd' hpd.1 hpd.2 hPd0 hPd hTd0
        hTd2 h hdk' hD0 e1.le (by linarith) hc5
  rw [← poa_cap N hB Γ]
  have := abs_sub_le (PoA (capGame Γ Γ.d)) (PoA (capGame Γ Γ'.d)) (PoA Γ')
  have := Real.sqrt_nonneg D
  calc _ ≤ κ2 * Real.sqrt D + κ1 * Real.sqrt D := by linarith
    _ ≤ (κ1 + κ2 + 1) * Real.sqrt D := by nlinarith

end PoAH

open KellyStochasticNetworks
open SensitivityPoA.Holder

theorem solution (N : Network) (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (M : ℝ) (hM : ∀ j, LipOnIcc (Γ.τ j) (totalDemand Γ.d) M) :
    ∃ ε > 0, ∃ κ > 0, ∀ Γ' ∈ gameSpace N, gameDist Γ Γ' < ε →
      |PoA Γ - PoA Γ'| ≤ κ * Real.sqrt (gameDist Γ Γ') :=
  PoAH.t9 N hN Γ hΓ M hM
