-- Prove2me | solution 1 for SensitivityPoA.Holder.lemma_10_b
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:36:03.613167+00:00
-- url     : https://prove2.me/submissions/8872a19e-7d20-4d92-83cd-3726e90fa298

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

lemma poa_mono_int (h : ℝ → ℝ) (hc : ContinuousOn h (Set.Ici 0)) (hm : MonotoneOn h (Set.Ici 0))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    h a * (b - a) ≤ ∫ u in a..b, h u ∧ ∫ u in a..b, h u ≤ h b * (b - a) := by
  have hint : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → IntervalIntegrable h MeasureTheory.volume x y := by
    intro x y hx hy
    refine ContinuousOn.intervalIntegrable (hc.mono ?_)
    intro z hz
    rw [Set.mem_uIcc] at hz
    simp only [Set.mem_Ici]
    rcases hz with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have key : ∀ x y : ℝ, 0 ≤ x → x ≤ y → h x * (y - x) ≤ ∫ u in x..y, h u ∧ ∫ u in x..y, h u ≤ h y * (y - x) := by
    intro x y hx hxy
    have hy : 0 ≤ y := hx.trans hxy
    constructor
    · have := intervalIntegral.integral_mono_on hxy (intervalIntegrable_const (c := h x))
        (hint x y hx hy) (fun u hu => hm (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (hx.trans hu.1)) hu.1)
      simpa [mul_comm] using this
    · have := intervalIntegral.integral_mono_on hxy (hint x y hx hy)
        (intervalIntegrable_const (c := h y)) (fun u hu => hm (Set.mem_Ici.mpr (hx.trans hu.1)) (Set.mem_Ici.mpr hy) hu.2)
      simpa [mul_comm] using this
  rcases le_total a b with hab | hab
  · exact key a b ha hab
  · obtain ⟨k1, k2⟩ := key b a hb hab
    rw [intervalIntegral.integral_symm]
    constructor <;> nlinarith


lemma poa_int_ii (N : Network) (Γ : Game N) (hΓ : Γ.IsGeneralized) (y : ℝ) (hy : 0 ≤ y) (j : Fin N.J) :
    IntervalIntegrable (Γ.τ j) MeasureTheory.volume 0 y := by
  refine ContinuousOn.intervalIntegrable (((hΓ.1 j).1).mono ?_)
  intro z hz
  rw [Set.mem_uIcc] at hz
  simp only [Set.mem_Ici]
  rcases hz with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith

lemma poa_pot_lower (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (x y : Fin N.R → ℝ) (hx : ∀ r, 0 ≤ x r) (hy : ∀ r, 0 ≤ y r) :
    ∑ j, Γ.τ j (linkFlow N.A y j) * (linkFlow N.A x j - linkFlow N.A y j) ≤ potential Γ x - potential Γ y := by
  have hpot : ∀ j, (∫ u in (0:ℝ)..(linkFlow N.A x j), Γ.τ j u) - (∫ u in (0:ℝ)..(linkFlow N.A y j), Γ.τ j u) =
      ∫ u in (linkFlow N.A y j)..(linkFlow N.A x j), Γ.τ j u := by
    intro j
    rw [intervalIntegral.integral_interval_sub_left
      (poa_int_ii N Γ hΓ _ (poa_lf_nonneg N hN x hx j) j) (poa_int_ii N Γ hΓ _ (poa_lf_nonneg N hN y hy j) j)]
  unfold potential wardropObjective
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [hpot j]
  exact (poa_mono_int _ (hΓ.1 j).1 (hΓ.1 j).2.1 _ _ (poa_lf_nonneg N hN y hy j) (poa_lf_nonneg N hN x hx j)).1

lemma poa_pot_min (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (ftil g : Fin N.R → ℝ) (hWE : IsWE Γ ftil) (hg : IsFlow Γ g) :
    potential Γ ftil ≤ potential Γ g := by
  have h1 := poa_wardrop_ineq N hN Γ ftil g hWE hg
  have h2 := poa_pot_lower N hN Γ hΓ g ftil hg.1 hWE.1.1
  linarith

lemma poa_pot_close (N : Network) (hN : N.Basic) (Γ1 Γ2 : Game N) (h1 : Γ1.IsGeneralized) (h2 : Γ2.IsGeneralized)
    (D : ℝ) (hD : ∀ j y, 0 ≤ y → y ≤ totalDemand Γ1.d → |Γ1.τ j y - Γ2.τ j y| ≤ D)
    (f : Fin N.R → ℝ) (hf : IsFlow Γ1 f) :
    |potential Γ1 f - potential Γ2 f| ≤ (N.J : ℝ) * totalDemand Γ1.d * D := by
  set T := totalDemand Γ1.d with hT
  have hyf : ∀ j, 0 ≤ linkFlow N.A f j ∧ linkFlow N.A f j ≤ T := fun j =>
    ⟨poa_lf_nonneg N hN f hf.1 j, (poa_lf_le N hN f hf.1 j).trans (poa_sum_flow N hf).le⟩
  unfold potential wardropObjective
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ j : Fin N.J, |(∫ u in (0:ℝ)..(linkFlow N.A f j), Γ1.τ j u) -
      (∫ u in (0:ℝ)..(linkFlow N.A f j), Γ2.τ j u)| ≤ T * D := by
    intro j
    rw [← intervalIntegral.integral_sub (poa_int_ii N Γ1 h1 _ (hyf j).1 j) (poa_int_ii N Γ2 h2 _ (hyf j).1 j)]
    have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD j 0 le_rfl (by
      rw [hT]; exact le_trans (hyf j).1 (hyf j).2))
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := linkFlow N.A f j)
      (f := fun u => Γ1.τ j u - Γ2.τ j u) (C := D) (fun x hx => by
        rw [Set.uIoc_of_le (hyf j).1] at hx
        simpa using hD j x hx.1.le (hx.2.trans (hyf j).2))
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    rw [sub_zero, abs_of_nonneg (hyf j).1]
    nlinarith [(hyf j).2]
  calc ∑ j, |(∫ u in (0:ℝ)..(linkFlow N.A f j), Γ1.τ j u) - (∫ u in (0:ℝ)..(linkFlow N.A f j), Γ2.τ j u)|
      ≤ ∑ j : Fin N.J, T * D := Finset.sum_le_sum (fun j _ => hterm j)
    _ = (N.J : ℝ) * T * D := by simp; ring

theorem solution (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hd : Γ1.d = Γ2.d)
    (ftil gtil : Fin N.R → ℝ) (hftil : IsWE Γ1 ftil) (hgtil : IsWE Γ2 gtil) :
    (∀ f, IsFlow Γ1 f →
      |potential Γ1 f - potential Γ2 f| ≤ (N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2) ∧
    |potential Γ1 ftil - potential Γ2 gtil| ≤ (N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2 ∧
    (0 ≤ potential Γ1 gtil - potential Γ1 ftil ∧
      potential Γ1 gtil - potential Γ1 ftil ≤ 2 * (N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2) ∧
    (0 ≤ potential Γ2 ftil - potential Γ2 gtil ∧
      potential Γ2 ftil - potential Γ2 gtil ≤ 2 * (N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2) := by
  have hB := poa_basic_of_standing N hN
  set K := (N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2 with hK
  have hD : ∀ j y, 0 ≤ y → y ≤ totalDemand Γ1.d → |Γ1.τ j y - Γ2.τ j y| ≤ gameDist Γ1 Γ2 :=
    fun j y hy0 hyT => poa_dist_bound N Γ1 Γ2 h1 h2 hd j y hy0 hyT
  have hfl1t : IsFlow Γ1 ftil := ⟨hftil.1.1, hftil.1.2⟩
  have hfl2g : IsFlow Γ2 gtil := ⟨hgtil.1.1, hgtil.1.2⟩
  have hfl1g : IsFlow Γ1 gtil := ⟨hgtil.1.1, fun σ => by rw [hgtil.1.2 σ, hd]⟩
  have hfl2t : IsFlow Γ2 ftil := ⟨hftil.1.1, fun σ => by rw [hftil.1.2 σ, hd]⟩
  have c1 : ∀ f, IsFlow Γ1 f → |potential Γ1 f - potential Γ2 f| ≤ K :=
    fun f hf => poa_pot_close N hB Γ1 Γ2 h1.1 h2.1 _ hD f hf
  have c1' : ∀ f, IsFlow Γ1 f → |potential Γ2 f - potential Γ1 f| ≤ K := by
    intro f hf; rw [abs_sub_comm]; exact c1 f hf
  have m1 := poa_pot_min N hB Γ1 h1.1 ftil gtil hftil hfl1g
  have m2 := poa_pot_min N hB Γ2 h2.1 gtil ftil hgtil hfl2t
  have a1 := abs_le.mp (c1 gtil hfl1g)
  have a2 := abs_le.mp (c1 ftil hfl1t)
  refine ⟨c1, ?_, ⟨by linarith, by linarith [a1.2, a1.1, a2.1, a2.2]⟩, ⟨by linarith, by linarith [a1.2, a1.1, a2.1, a2.2]⟩⟩
  rw [abs_le]
  constructor <;> linarith [a1.2, a1.1, a2.1, a2.2]
