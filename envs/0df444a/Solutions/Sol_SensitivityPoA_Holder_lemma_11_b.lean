-- Prove2me | solution 1 for SensitivityPoA.Holder.lemma_11_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T08:59:07.78384+00:00
-- url     : https://prove2.me/submissions/0e93aac8-80d4-4298-9c6d-e43c65d9ef32

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting
import Theorems.Thm_KellyStochasticNetworks_wardrop_equilibrium_exists

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

/-- the per-pair scaling factor used to shrink a flow of demand `v` to demand `w` -/
noncomputable def scal {Sd : ℕ} (v w : Fin Sd → ℝ) (k : Fin Sd) : ℝ :=
  if v k = 0 then 0 else w k / v k

lemma scal_nonneg {Sd : ℕ} (v w : Fin Sd → ℝ) (hv : ∀ k, 0 ≤ v k) (hw : ∀ k, 0 ≤ w k)
    (k : Fin Sd) : 0 ≤ scal v w k := by
  unfold scal; split_ifs
  · exact le_rfl
  · exact div_nonneg (hw k) (hv k)

lemma scal_le_one {Sd : ℕ} (v w : Fin Sd → ℝ) (hv : ∀ k, 0 ≤ v k) (hwv : ∀ k, w k ≤ v k)
    (k : Fin Sd) : scal v w k ≤ 1 := by
  unfold scal; split_ifs with h
  · exact zero_le_one
  · exact div_le_one_of_le₀ (hwv k) (hv k)

lemma lf_mono (N : Network) (hN : N.Basic) (x y : Fin N.R → ℝ) (hxy : ∀ r, x r ≤ y r)
    (j : Fin N.J) : linkFlow N.A x j ≤ linkFlow N.A y j := by
  unfold linkFlow
  refine Finset.sum_le_sum (fun r _ => ?_)
  rcases hN.1 j r with h | h <;> rw [h] <;> simp [hxy r]

/-- shrink a flow of demand `v` into a flow of demand `w ≤ v`, pathwise below it -/
lemma shrink_flow (N : Network) (Γv Γw : Game N) (hv : ∀ k, 0 ≤ Γv.d k) (hw : ∀ k, 0 ≤ Γw.d k)
    (hwv : ∀ k, Γw.d k ≤ Γv.d k) (f : Fin N.R → ℝ) (hf : IsFlow Γv f) :
    IsFlow Γw (fun r => scal Γv.d Γw.d (N.s r) * f r) ∧
      ∀ r, scal Γv.d Γw.d (N.s r) * f r ≤ f r := by
  refine ⟨⟨fun r => mul_nonneg (scal_nonneg _ _ hv hw _) (hf.1 r), fun σ => ?_⟩, fun r => ?_⟩
  · have : ∀ r ∈ Finset.univ.filter (fun r => N.s r = σ),
        scal Γv.d Γw.d (N.s r) * f r = scal Γv.d Γw.d σ * f r := by
      intro r hr; rw [(Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hf.2 σ]
    unfold scal; split_ifs with h
    · have := hwv σ; have := hw σ; rw [h] at *; linarith
    · field_simp
  · have h1 := scal_le_one _ _ hv hwv (N.s r)
    have h2 := hf.1 r
    nlinarith

/-- the extension used to enlarge a flow of demand `w` into a flow of demand `v ≥ w` -/
lemma extend_flow (N : Network) (hN : N.Basic) (Γv Γw : Game N)
    (hwv : ∀ k, Γw.d k ≤ Γv.d k) (h : Fin N.R → ℝ) (hh : IsFlow Γw h) :
    ∃ l : Fin N.R → ℝ, (∀ r, 0 ≤ l r) ∧ ∑ r, l r = totalDemand Γv.d - totalDemand Γw.d ∧
      IsFlow Γv (fun r => h r + l r) := by
  obtain ⟨l, hl⟩ := flow_exists N hN ⟨Γv.τ, fun k => Γv.d k - Γw.d k⟩
    (fun k => by have := hwv k; simp; linarith)
  refine ⟨l, hl.1, ?_, ⟨fun r => add_nonneg (hh.1 r) (hl.1 r), fun σ => ?_⟩⟩
  · rw [sum_flow N hl]; unfold totalDemand; rw [← Finset.sum_sub_distrib]
  · rw [Finset.sum_add_distrib, hh.2 σ, hl.2 σ]; ring

lemma lf_add (N : Network) (x y : Fin N.R → ℝ) (j : Fin N.J) :
    linkFlow N.A (fun r => x r + y r) j = linkFlow N.A x j + linkFlow N.A y j := by
  unfold linkFlow; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun r _ => by ring)

/-- SO cost comparison along a cost slice, between demand `v` and a smaller demand `w`. -/
lemma so_slice (N : Network) (hN : N.Basic) (Γv Γw : Game N) (hτ : Γw.τ = Γv.τ)
    (hgv : Γv.IsGeneralized) (hgw : Γw.IsGeneralized) (hwv : ∀ k, Γw.d k ≤ Γv.d k)
    (T M P D : ℝ) (hTv : totalDemand Γv.d ≤ T) (hM0 : 0 ≤ M)
    (hM : ∀ j, LipOnIcc (Γv.τ j) T M) (hP : ∀ j, Γv.τ j T ≤ P)
    (hD : ∀ k, Γv.d k - Γw.d k ≤ D) :
    |SOCost Γv - SOCost Γw| ≤ ((N.J : ℝ) * N.Sd * P + N.J * T * M * N.Sd) * D := by
  have hJ : (0:ℝ) < N.J := by exact_mod_cast J_pos N hN
  have hSd : (0:ℝ) < N.Sd := by exact_mod_cast hN.2.2.1
  have hD0 : 0 ≤ D := le_trans (by linarith [hwv ⟨0, hN.2.2.1⟩]) (hD ⟨0, hN.2.2.1⟩)
  have hT0 : 0 ≤ T := le_trans (T_nonneg Γv hgv) hTv
  have hP0 : 0 ≤ P := le_trans ((hgv.1 ⟨0, J_pos N hN⟩).2.2 T hT0) (hP _)
  rw [abs_le]
  constructor
  · -- SOCost Γw ≤ SOCost Γv
    obtain ⟨g0, hg0⟩ := flow_exists N hN Γv hgv.2
    have : SOCost Γw ≤ SOCost Γv := by
      refine le_csInf ⟨_, g0, hg0, rfl⟩ ?_
      rintro _ ⟨f, hf, rfl⟩
      obtain ⟨hf', hle⟩ := shrink_flow N Γv Γw hgv.2 hgw.2 hwv f hf
      refine (so_le N hN Γw hgw _ hf').trans ?_
      unfold cost
      refine Finset.sum_le_sum (fun j _ => ?_)
      have a0 := lf_nonneg N hN _ hf'.1 j
      have a1 := lf_mono N hN _ _ hle j
      rw [hτ]
      have b1 := (hgv.1 j).2.1 a0 (le_trans a0 a1) a1
      have b0 := (hgv.1 j).2.2 _ a0
      exact mul_le_mul a1 b1 b0 (le_trans a0 a1)
    have : 0 ≤ ((N.J : ℝ) * N.Sd * P + N.J * T * M * N.Sd) * D := by positivity
    linarith
  · -- SOCost Γv ≤ SOCost Γw + E
    obtain ⟨g0, hg0⟩ := flow_exists N hN Γw hgw.2
    have key : SOCost Γv - ((N.J : ℝ) * N.Sd * P + N.J * T * M * N.Sd) * D ≤ SOCost Γw := by
      refine le_csInf ⟨_, g0, hg0, rfl⟩ ?_
      rintro _ ⟨h, hh, rfl⟩
      obtain ⟨l, hl0, hlsum, hfl⟩ := extend_flow N hN Γv Γw hwv h hh
      have hlD : ∑ r, l r ≤ N.Sd * D := by
        rw [hlsum]; unfold totalDemand; rw [← Finset.sum_sub_distrib]
        calc ∑ k, (Γv.d k - Γw.d k) ≤ ∑ _k : Fin N.Sd, D := Finset.sum_le_sum (fun k _ => hD k)
          _ = N.Sd * D := by simp
      have hlj : ∀ j, linkFlow N.A l j ≤ N.Sd * D := fun j => (lf_le N hN l hl0 j).trans hlD
      have hsumh : ∑ j, linkFlow N.A h j ≤ N.J * T := by
        calc ∑ j, linkFlow N.A h j ≤ ∑ _j : Fin N.J, T := Finset.sum_le_sum (fun j _ =>
              (lf_le_T N hN hh j).trans (by
                unfold totalDemand; exact le_trans (Finset.sum_le_sum (fun k _ => hwv k)) hTv))
          _ = N.J * T := by simp
      have hcv := so_le N hN Γv hgv _ hfl
      have hterm : ∀ j, linkFlow N.A (fun r => h r + l r) j * Γv.τ j (linkFlow N.A (fun r => h r + l r) j)
          ≤ linkFlow N.A h j * Γw.τ j (linkFlow N.A h j) +
            (linkFlow N.A h j * (M * (N.Sd * D)) + N.Sd * D * P) := by
        intro j
        rw [lf_add, hτ]
        have a0 := lf_nonneg N hN h hh.1 j
        have b0 := lf_nonneg N hN l hl0 j
        have hsum := lf_le_T N hN hfl j
        rw [lf_add] at hsum
        have hle1 : linkFlow N.A h j + linkFlow N.A l j ≤ T := hsum.trans hTv
        have lip := hM j _ ⟨by linarith, hle1⟩ _ ⟨a0, by linarith⟩
        have lip' : Γv.τ j (linkFlow N.A h j + linkFlow N.A l j) - Γv.τ j (linkFlow N.A h j)
            ≤ M * (N.Sd * D) := by
          have := (abs_le.mp lip).2
          rw [show linkFlow N.A h j + linkFlow N.A l j - linkFlow N.A h j = linkFlow N.A l j by ring,
            abs_of_nonneg b0] at this
          nlinarith [hlj j]
        have hτT : Γv.τ j (linkFlow N.A h j + linkFlow N.A l j) ≤ P :=
          ((hgv.1 j).2.1 (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr hT0) hle1).trans (hP j)
        have hτ0 := (hgv.1 j).2.2 _ (by linarith : 0 ≤ linkFlow N.A h j + linkFlow N.A l j)
        have e1 : linkFlow N.A h j * Γv.τ j (linkFlow N.A h j + linkFlow N.A l j) ≤
            linkFlow N.A h j * (Γv.τ j (linkFlow N.A h j) + M * (N.Sd * D)) :=
          mul_le_mul_of_nonneg_left (by linarith) a0
        have e2 : linkFlow N.A l j * Γv.τ j (linkFlow N.A h j + linkFlow N.A l j) ≤ N.Sd * D * P :=
          mul_le_mul (hlj j) hτT hτ0 (by positivity)
        nlinarith
      have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
      have e3 : ∑ j, linkFlow N.A h j * (M * (N.Sd * D)) ≤ N.J * T * (M * (N.Sd * D)) := by
        rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hsumh (by positivity)
      have e4 : ∑ _j : Fin N.J, (N.Sd : ℝ) * D * P = N.J * (N.Sd * D * P) := by simp
      unfold cost at hcv ⊢
      nlinarith
    linarith

end PoAH


open KellyStochasticNetworks
open SensitivityPoA.Holder

namespace PoAH

/-- the auxiliary game `Γ̂ = (π, min(w, w'))` -/
noncomputable def hatGame {N : Network} (Γ1 Γ2 : Game N) : Game N :=
  ⟨Γ1.τ, fun k => min (Γ1.d k) (Γ2.d k)⟩

lemma hat_gen {N : Network} (Γ1 Γ2 : Game N) (h1 : Γ1.IsGeneralized) (h2 : Γ2.IsGeneralized) :
    (hatGame Γ1 Γ2).IsGeneralized :=
  ⟨h1.1, fun k => le_min (h1.2 k) (h2.2 k)⟩

lemma hat_d1 {N : Network} (Γ1 Γ2 : Game N) (k : Fin N.Sd) :
    Γ1.d k - (hatGame Γ1 Γ2).d k ≤ gameDist Γ1 Γ2 := by
  have := dist_demand Γ1 Γ2 k
  show Γ1.d k - min (Γ1.d k) (Γ2.d k) ≤ _
  rcases le_total (Γ1.d k) (Γ2.d k) with h | h
  · rw [min_eq_left h]; linarith [dist_nonneg Γ1 Γ2]
  · rw [min_eq_right h]; exact le_trans (le_abs_self _) this

lemma hat_d2 {N : Network} (Γ1 Γ2 : Game N) (k : Fin N.Sd) :
    Γ2.d k - (hatGame Γ1 Γ2).d k ≤ gameDist Γ1 Γ2 := by
  have := dist_demand Γ1 Γ2 k
  show Γ2.d k - min (Γ1.d k) (Γ2.d k) ≤ _
  rcases le_total (Γ1.d k) (Γ2.d k) with h | h
  · rw [min_eq_left h]; rw [abs_sub_comm] at this; exact le_trans (le_abs_self _) this
  · rw [min_eq_right h]; linarith [dist_nonneg Γ1 Γ2]

lemma le_pimax {N : Network} (Γ1 : Game N) (T : ℝ) (j : Fin N.J) :
    Γ1.τ j T ≤ ⨆ i, Γ1.τ i T :=
  le_ciSup (Finite.bddAbove_range (fun i => Γ1.τ i T)) j

theorem l11b (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hτ : Γ2.τ = Γ1.τ)
    (hT : totalDemand Γ2.d ≤ totalDemand Γ1.d)
    (M : ℝ) (hM1 : 1 ≤ M) (hM : ∀ j, LipOnIcc (Γ1.τ j) (totalDemand Γ1.d) M) :
    |SOCost Γ1 - SOCost Γ2| ≤ 2 * (N.J * N.Sd * (⨆ j, Γ1.τ j (totalDemand Γ1.d))
        + N.J * totalDemand Γ1.d * M * N.Sd) * gameDist Γ1 Γ2 := by
  have hB := basic_of_standing N hN
  set T := totalDemand Γ1.d
  set P := ⨆ j, Γ1.τ j T
  set D := gameDist Γ1 Γ2
  have hG := hat_gen Γ1 Γ2 h1.1 h2.1
  have a := so_slice N hB Γ1 (hatGame Γ1 Γ2) rfl h1.1 hG (fun k => min_le_left _ _) T M P D
    le_rfl (by linarith) hM (fun j => le_pimax Γ1 T j) (hat_d1 Γ1 Γ2)
  have b := so_slice N hB Γ2 (hatGame Γ1 Γ2) (by rw [hτ]; rfl) h2.1 hG (fun k => min_le_right _ _)
    T M P D hT (by linarith) (by rw [hτ]; exact hM) (fun j => by rw [hτ]; exact le_pimax Γ1 T j)
    (hat_d2 Γ1 Γ2)
  have : |SOCost Γ1 - SOCost Γ2| ≤ |SOCost Γ1 - SOCost (hatGame Γ1 Γ2)| +
      |SOCost Γ2 - SOCost (hatGame Γ1 Γ2)| := by
    rw [abs_sub_comm (SOCost Γ2)]; exact abs_sub_le _ _ _
  linarith

end PoAH

open KellyStochasticNetworks
open SensitivityPoA.Holder

theorem solution (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hτ : Γ2.τ = Γ1.τ)
    (hT : totalDemand Γ2.d ≤ totalDemand Γ1.d)
    (M : ℝ) (hM1 : 1 ≤ M) (hM : ∀ j, LipOnIcc (Γ1.τ j) (totalDemand Γ1.d) M) :
    let T : ℝ := totalDemand Γ1.d
    let D : ℝ := gameDist Γ1 Γ2
    let πmax : ℝ := ⨆ j, Γ1.τ j T
    let νtil : ℝ := 2 * ((Real.sqrt (M * N.J * T) + 2) * N.J * T + N.J * N.Sd * πmax) * Real.sqrt M
    let νstar : ℝ := 2 * (N.J * N.Sd * πmax + N.J * T * M * N.Sd)
    let X : ℝ := max (Real.sqrt (N.Sd * D)) (Real.sqrt M * (N.Sd * D))
    D < T / N.Sd → |SOCost Γ1 - SOCost Γ2| ≤ νstar * D := by
  intro T D πmax νtil νstar X _
  exact PoAH.l11b N hN Γ1 Γ2 h1 h2 hτ hT M hM1 hM
