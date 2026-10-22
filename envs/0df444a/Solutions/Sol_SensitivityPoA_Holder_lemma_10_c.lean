-- Prove2me | solution 1 for SensitivityPoA.Holder.lemma_10_c
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:33:14.680063+00:00
-- url     : https://prove2.me/submissions/448d4e92-10e8-475e-88e5-b98a005ba775

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

set_option autoImplicit false
open KellyStochasticNetworks
open SensitivityPoA.Holder

section
variable {N : Network}

lemma poa_path_decomp (Γ : Game N) (f x y : Fin N.R → ℝ) :
    ∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A x j - linkFlow N.A y j) =
      ∑ r, pathCost Γ f r * (x r - y r) := by
  unfold pathCost linkFlow
  have : ∀ j, Γ.τ j (∑ r, N.A j r * f r) * ((∑ r, N.A j r * x r) - ∑ r, N.A j r * y r) =
      ∑ r, Γ.τ j (∑ r, N.A j r * f r) * N.A j r * (x r - y r) := by
    intro j
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  simp only [this]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun r _ => by rw [Finset.sum_mul])

lemma poa_cost_eq (Γ : Game N) (f : Fin N.R → ℝ) :
    cost Γ f = ∑ r, f r * pathCost Γ f r := by
  have := poa_path_decomp Γ f f (fun _ => 0)
  simp only [sub_zero] at this
  unfold cost
  have h2 : ∑ j, linkFlow N.A f j * Γ.τ j (linkFlow N.A f j) =
      ∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A f j - linkFlow N.A (fun _ => (0:ℝ)) j) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [linkFlow]; ring
  rw [h2, this]
  exact Finset.sum_congr rfl (fun r _ => by ring)

end



lemma poa_basic_of_standing (N : Network) (hN : N.Standing) : N.Basic :=
  ⟨hN.1, hN.2.1, hN.2.2.1, fun k => lt_of_lt_of_le (by norm_num) (hN.2.2.2.2 k)⟩

lemma poa_lf_nonneg (N : Network) (hN : N.Basic) (x : Fin N.R → ℝ) (hx : ∀ r, 0 ≤ x r) (j : Fin N.J) :
    0 ≤ linkFlow N.A x j := by
  unfold linkFlow
  refine Finset.sum_nonneg (fun r _ => ?_)
  rcases hN.1 j r with h | h <;> rw [h] <;> [simp; simpa using hx r]


lemma poa_lf_le (N : Network) (hN : N.Basic) (x : Fin N.R → ℝ) (hx : ∀ r, 0 ≤ x r) (j : Fin N.J) :
    linkFlow N.A x j ≤ ∑ r, x r := by
  unfold linkFlow
  refine Finset.sum_le_sum (fun r _ => ?_)
  rcases hN.1 j r with h | h <;> rw [h] <;> simp [hx r]

lemma poa_sum_flow (N : Network) {Γ : Game N} {x : Fin N.R → ℝ} (hx : IsFlow Γ x) :
    ∑ r, x r = totalDemand Γ.d := by
  unfold totalDemand
  rw [← Finset.sum_fiberwise Finset.univ N.s x]
  exact Finset.sum_congr rfl (fun k _ => hx.2 k)

lemma poa_wardrop_ineq (N : Network) (hN : N.Basic) (Γ : Game N) (ftil g : Fin N.R → ℝ)
    (hftil : IsWE Γ ftil) (hg : IsFlow Γ g) :
    0 ≤ ∑ j, Γ.τ j (linkFlow N.A ftil j) * (linkFlow N.A g j - linkFlow N.A ftil j) := by
  obtain ⟨⟨hgnn, hgsum⟩, hwe⟩ := hftil
  obtain ⟨hfnn, hfsum⟩ := hg
  rw [poa_path_decomp]
  rw [← Finset.sum_fiberwise Finset.univ N.s]
  refine Finset.sum_nonneg (fun k _ => ?_)
  have hne : (Finset.univ.filter (fun r => N.s r = k)).Nonempty :=
    Finset.card_pos.mp (hN.2.2.2 k)
  obtain ⟨r0, hr0, hmin⟩ := Finset.exists_min_image _ (pathCost Γ ftil) hne
  have hr0k : N.s r0 = k := (Finset.mem_filter.mp hr0).2
  have hA : ∀ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r * ftil r =
      pathCost Γ ftil r0 * ftil r := by
    intro r hr
    have hrk : N.s r = k := (Finset.mem_filter.mp hr).2
    rcases (hgnn r).eq_or_lt with h0 | h0
    · rw [← h0]; ring
    · have h1 := hwe r r0 (by rw [hrk, hr0k]) h0
      have h2 := hmin r hr
      have : pathCost Γ ftil r = pathCost Γ ftil r0 := le_antisymm (by simpa [pathCost] using h1) h2
      rw [this]
  have hB : ∀ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r0 * g r ≤
      pathCost Γ ftil r * g r := fun r hr =>
    mul_le_mul_of_nonneg_right (hmin r hr) (hfnn r)
  have hs1 := hfsum k
  have hs2 := hgsum k
  have e1 : ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r * (g r - ftil r) =
      ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r * g r -
        ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r * ftil r := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [e1, Finset.sum_congr rfl hA, ← Finset.mul_sum, hs2]
  have := Finset.sum_le_sum hB
  rw [← Finset.mul_sum, hs1] at this
  linarith

lemma poa_dist_bound (N : Network) (Γ1 Γ2 : Game N) (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N)
    (hd : Γ1.d = Γ2.d) (j : Fin N.J) (y : ℝ) (hy0 : 0 ≤ y) (hyT : y ≤ totalDemand Γ1.d) :
    |Γ1.τ j y - Γ2.τ j y| ≤ gameDist Γ1 Γ2 := by
  have hT : totalDemand Γ2.d = totalDemand Γ1.d := by rw [hd]
  have hmin : min (totalDemand Γ1.d) (totalDemand Γ2.d) = totalDemand Γ1.d := by rw [hT]; simp
  have hbdd : ∀ j : Fin N.J, ∃ C : ℝ, ∀ y ∈ Set.Icc (0:ℝ) (totalDemand Γ1.d), |Γ1.τ j y - Γ2.τ j y| ≤ C := by
    intro j
    have hc : ContinuousOn (fun y => |Γ1.τ j y - Γ2.τ j y|) (Set.Icc (0:ℝ) (totalDemand Γ1.d)) := by
      refine (ContinuousOn.abs (ContinuousOn.sub ?_ ?_))
      · exact (h1.1.1 j).1.mono Set.Icc_subset_Ici_self
      · exact (h2.1.1 j).1.mono Set.Icc_subset_Ici_self
    obtain ⟨C, hC⟩ := (isCompact_Icc.bddAbove_image hc)
    exact ⟨C, fun y hy => hC ⟨y, hy, rfl⟩⟩
  choose C hC using hbdd
  unfold gameDist
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (le_max_left _ _)
  refine le_csSup ⟨∑ j, |C j|, ?_⟩ ⟨(j, y), ⟨Set.mem_univ _, by rw [hmin]; exact ⟨hy0, hyT⟩⟩, rfl⟩
  rintro _ ⟨⟨i, z⟩, ⟨_, hz⟩, rfl⟩
  rw [hmin] at hz
  calc |Γ1.τ i z - Γ2.τ i z| ≤ C i := hC i z hz
    _ ≤ |C i| := le_abs_self _
    _ ≤ ∑ j, |C j| := Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

lemma poa_approx_of_close (N : Network) (hN : N.Basic) (Γ1 Γ2 : Game N) (hd : Γ1.d = Γ2.d)
    (D : ℝ)
    (hD : ∀ j y, 0 ≤ y → y ≤ totalDemand Γ1.d → |Γ1.τ j y - Γ2.τ j y| ≤ D)
    (ftil : Fin N.R → ℝ) (hWE : IsWE Γ1 ftil) :
    IsApproxWE Γ2 ((N.J : ℝ) * totalDemand Γ1.d * D) ftil := by
  have hfl1 : IsFlow Γ1 ftil := ⟨hWE.1.1, hWE.1.2⟩
  have hflow : ∀ g, IsFlow Γ2 g → IsFlow Γ1 g := by
    intro g hg
    refine ⟨hg.1, fun σ => ?_⟩
    rw [hg.2 σ, hd]
  refine ⟨⟨hWE.1.1, fun σ => by rw [hWE.1.2 σ, hd]⟩, fun g hg => ?_⟩
  have hg1 := hflow g hg
  have hA := poa_wardrop_ineq N hN Γ1 ftil g hWE hg1
  set T := totalDemand Γ1.d with hT
  have hyt : ∀ j, 0 ≤ linkFlow N.A ftil j ∧ linkFlow N.A ftil j ≤ T := fun j =>
    ⟨poa_lf_nonneg N hN ftil hWE.1.1 j, 
      (poa_lf_le N hN ftil hWE.1.1 j).trans (poa_sum_flow N hfl1).le⟩
  have hyg : ∀ j, 0 ≤ linkFlow N.A g j ∧ linkFlow N.A g j ≤ T := fun j =>
    ⟨poa_lf_nonneg N hN g hg1.1 j, 
      (poa_lf_le N hN g hg1.1 j).trans (poa_sum_flow N hg1).le⟩
  have hb : ∀ j, Γ2.τ j (linkFlow N.A ftil j) * (linkFlow N.A ftil j - linkFlow N.A g j) ≤
      Γ1.τ j (linkFlow N.A ftil j) * (linkFlow N.A ftil j - linkFlow N.A g j) + D * T := by
    intro j
    have h1 := hD j _ (hyt j).1 (hyt j).2
    have hD0 : 0 ≤ D := le_trans (abs_nonneg _) h1
    have h2 : |linkFlow N.A ftil j - linkFlow N.A g j| ≤ T := by
      rw [abs_le]; constructor <;> linarith [hyt j, hyg j]
    have h3 : |(Γ2.τ j (linkFlow N.A ftil j) - Γ1.τ j (linkFlow N.A ftil j)) *
        (linkFlow N.A ftil j - linkFlow N.A g j)| ≤ D * T := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul h1 h2 (abs_nonneg _) hD0
    have h4 := (abs_le.mp h3).2
    nlinarith [h4]
  calc ∑ j, Γ2.τ j (linkFlow N.A ftil j) * (linkFlow N.A ftil j - linkFlow N.A g j)
      ≤ ∑ j, (Γ1.τ j (linkFlow N.A ftil j) * (linkFlow N.A ftil j - linkFlow N.A g j) + D * T) :=
        Finset.sum_le_sum (fun j _ => hb j)
    _ = (∑ j, Γ1.τ j (linkFlow N.A ftil j) * (linkFlow N.A ftil j - linkFlow N.A g j)) + N.J * (D * T) := by
        rw [Finset.sum_add_distrib]; simp
    _ ≤ (N.J : ℝ) * T * D := by
        have : ∑ j, Γ1.τ j (linkFlow N.A ftil j) * (linkFlow N.A ftil j - linkFlow N.A g j) =
            -∑ j, Γ1.τ j (linkFlow N.A ftil j) * (linkFlow N.A g j - linkFlow N.A ftil j) := by
          rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [this]; nlinarith

theorem solution (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hd : Γ1.d = Γ2.d)
    (ftil gtil : Fin N.R → ℝ) (hftil : IsWE Γ1 ftil) (hgtil : IsWE Γ2 gtil) :
    IsApproxWE Γ2 ((N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2) ftil ∧
    IsApproxWE Γ1 ((N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2) gtil := by
  have hB := poa_basic_of_standing N hN
  refine ⟨poa_approx_of_close N hB Γ1 Γ2 hd _ (fun j y hy0 hyT =>
    poa_dist_bound N Γ1 Γ2 h1 h2 hd j y hy0 hyT) ftil hftil, ?_⟩
  have := poa_approx_of_close N hB Γ2 Γ1 hd.symm (gameDist Γ1 Γ2) (fun j y hy0 hyT => by
    rw [abs_sub_comm]
    exact poa_dist_bound N Γ1 Γ2 h1 h2 hd j y hy0 (by rw [hd]; exact hyT)) gtil hgtil
  rw [← hd] at this
  exact this
