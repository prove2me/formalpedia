-- Prove2me | solution 1 for SystemicDiv.SellOff.proposition_4_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:41:20.753328+00:00
-- url     : https://prove2.me/submissions/37fa44ba-5bdb-42d2-b90b-c55b06fef003

import Mathlib
import Definitions.Def_SystemicDiv_SellOff_Model
import Theorems.Thm_SystemicDiv_SellOff_lemma_A_1



namespace SysDivComb

open Finset

theorem pot_double {N : ℕ} (a : Fin N → Fin N → ℝ) (hs : ∀ m j, a m j = a j m) :
    2 * ∑ m, (a m m + ∑ j ∈ univ.filter (· < m), a m j) =
      ∑ m, a m m + ∑ m, ∑ j, a m j := by
  have h1 : ∀ m, ∑ j ∈ univ.filter (· < m), a m j = ∑ j, if j < m then a m j else 0 := by
    intro m; rw [Finset.sum_filter]
  have h2 : ∀ m, ∑ j, a m j =
      (∑ j, if j < m then a m j else 0) + a m m + ∑ j, if m < j then a m j else 0 := by
    intro m
    have : ∀ j, a m j = (if j < m then a m j else 0) + (if j = m then a m j else 0) +
        (if m < j then a m j else 0) := by
      intro j
      rcases lt_trichotomy j m with h | h | h
      · simp [h, h.ne, not_lt.2 h.le]
      · subst h; simp
      · simp [h, h.ne', not_lt.2 h.le]
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    simp
  have h3 : ∑ m, ∑ j, (if m < j then a m j else 0) =
      ∑ m, ∑ j, (if j < m then a m j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun j _ => ?_))
    split_ifs <;> simp [hs]
  have hR : ∑ m, ∑ j, a m j = ∑ m, (∑ j, if j < m then a m j else 0) + ∑ m, a m m +
      ∑ m, ∑ j, (if m < j then a m j else 0) := by
    rw [Finset.sum_congr rfl (fun m _ => h2 m), Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_congr rfl (fun m _ => h1 m), hR, h3]
  ring

end SysDivComb

namespace SysDivComb
open Finset

theorem pot_diff {N : ℕ} (a a' : Fin N → Fin N → ℝ) (hs : ∀ m j, a m j = a j m)
    (hs' : ∀ m j, a' m j = a' j m) (i : Fin N) (he : ∀ m j, m ≠ i → j ≠ i → a m j = a' m j) :
    ∑ m, (a m m + ∑ j ∈ univ.filter (· < m), a m j) -
      ∑ m, (a' m m + ∑ j ∈ univ.filter (· < m), a' m j) = ∑ j, a i j - ∑ j, a' i j := by
  have h1 := pot_double a hs
  have h2 := pot_double a' hs'
  have hd : ∀ m, m ≠ i → ∑ j, a m j - ∑ j, a' m j = a m i - a' m i := by
    intro m hm
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · intro j _ hj; rw [he m j hm hj, sub_self]
    · simp
  have hD : ∑ m, a m m - ∑ m, a' m m = a i i - a' i i := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · intro m _ hm; rw [he m m hm hm, sub_self]
    · simp
  have hT : ∑ m, ∑ j, a m j - ∑ m, ∑ j, a' m j =
      (∑ j, a i j - ∑ j, a' i j) + ∑ m, (a m i - a' m i) - (a i i - a' i i) := by
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [← Finset.add_sum_erase _ (fun m => a m i - a' m i) (Finset.mem_univ i)]
    rw [Finset.sum_congr rfl (fun m hm => hd m (Finset.ne_of_mem_erase hm))]
    ring
  have hsym : ∑ m, (a m i - a' m i) = ∑ j, a i j - ∑ j, a' i j := by
    rw [← Finset.sum_sub_distrib]; simp [hs _ i, hs' _ i]
  linarith

end SysDivComb

open MeasureTheory

namespace SysDivAn
open SystemicDiv.SellOff

theorem sold_eq (b : Bank) (hb : b.Standing) :
    sold b = fun R => b.levM * b.w * max (-(R + b.ell)) 0 := by
  funext R; exact (lemma_A_1 b hb R).2

theorem sold_abs_le (b : Bank) (hb : b.Standing) (R : ℝ) :
    |sold b R| ≤ |b.levM * b.w| * (|R| + |b.ell|) := by
  rw [sold_eq b hb, abs_mul]
  gcongr
  rw [abs_of_nonneg (le_max_right _ _)]
  apply max_le
  · have := neg_abs_le R; have := neg_abs_le b.ell; linarith
  · positivity

theorem portRet_abs_le {K : ℕ} (p : Fin K → ℝ) (hp : p ∈ stdSimplex ℝ (Fin K)) (z : Shock K) :
    |portRet p z| ≤ ‖z‖ := by
  unfold portRet
  calc |∑ k, p k * z k| ≤ ∑ k, |p k * z k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, p k * ‖z‖ := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [abs_mul, abs_of_nonneg (hp.1 k)]
        exact mul_le_mul_of_nonneg_left (by simpa using PiLp.norm_apply_le z k) (hp.1 k)
    _ = ‖z‖ := by rw [← Finset.sum_mul, hp.2, one_mul]

theorem coef_abs_le {K : ℕ} (γ : Fin K → ℝ) (p q : Fin K → ℝ) (hp : p ∈ stdSimplex ℝ (Fin K))
    (hq : q ∈ stdSimplex ℝ (Fin K)) : |∑ k, p k * γ k * q k| ≤ ∑ k, |γ k| := by
  have hp1 : ∀ k, p k ≤ 1 := fun k => by
    have := Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ k); rw [hp.2] at this; exact this
  have hq1 : ∀ k, q k ≤ 1 := fun k => by
    have := Finset.single_le_sum (fun j _ => hq.1 j) (Finset.mem_univ k); rw [hq.2] at this; exact this
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [abs_mul, abs_mul, abs_of_nonneg (hp.1 k), abs_of_nonneg (hq.1 k)]
  have := abs_nonneg (γ k)
  calc p k * |γ k| * q k ≤ 1 * |γ k| * 1 := by
        have := hp.1 k; have := hq.1 k; have := hp1 k; have := hq1 k
        gcongr
    _ = |γ k| := by ring

/-- The integrand of `M`. -/
noncomputable def Fm {K : ℕ} (γ : Fin K → ℝ) (b b' : Bank) (p q : Fin K → ℝ) (z : Shock K) : ℝ :=
  (∑ k, p k * γ k * q k) * sold b (portRet p z) * sold b' (portRet q z)

theorem Fm_cont (K : ℕ) (γ : Fin K → ℝ) (b b' : Bank) (hb : b.Standing) (hb' : b'.Standing) :
    Continuous (fun x : (Fin K → ℝ) × (Fin K → ℝ) × Shock K => Fm γ b b' x.1 x.2.1 x.2.2) := by
  unfold Fm portRet
  rw [sold_eq b hb, sold_eq b' hb']
  fun_prop

noncomputable def bnd {K : ℕ} (γ : Fin K → ℝ) (b b' : Bank) (z : Shock K) : ℝ :=
  (∑ k, |γ k|) * (|b.levM * b.w| * |b'.levM * b'.w|) *
    (2 * ‖z‖ ^ 2 + 2 * (|b.ell| + |b'.ell|) ^ 2)

theorem Fm_bound {K : ℕ} (γ : Fin K → ℝ) (b b' : Bank) (hb : b.Standing) (hb' : b'.Standing)
    (p q : Fin K → ℝ) (hp : p ∈ stdSimplex ℝ (Fin K)) (hq : q ∈ stdSimplex ℝ (Fin K))
    (z : Shock K) : ‖Fm γ b b' p q z‖ ≤ bnd γ b b' z := by
  unfold Fm bnd
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have h1 := coef_abs_le γ p q hp hq
  have h2 := sold_abs_le b hb (portRet p z)
  have h3 := sold_abs_le b' hb' (portRet q z)
  have h4 := portRet_abs_le p hp z
  have h5 := portRet_abs_le q hq z
  have e1 : |sold b (portRet p z)| ≤ |b.levM * b.w| * (‖z‖ + (|b.ell| + |b'.ell|)) :=
    h2.trans (by gcongr; linarith [abs_nonneg b'.ell])
  have e2 : |sold b' (portRet q z)| ≤ |b'.levM * b'.w| * (‖z‖ + (|b.ell| + |b'.ell|)) :=
    h3.trans (by gcongr; linarith [abs_nonneg b.ell])
  have hz : (‖z‖ + (|b.ell| + |b'.ell|)) ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * (|b.ell| + |b'.ell|) ^ 2 := by
    nlinarith [sq_nonneg (‖z‖ - (|b.ell| + |b'.ell|))]
  have hΓ : 0 ≤ ∑ k, |γ k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  calc |∑ k, p k * γ k * q k| * |sold b (portRet p z)| * |sold b' (portRet q z)|
      ≤ (∑ k, |γ k|) * (|b.levM * b.w| * (‖z‖ + (|b.ell| + |b'.ell|))) *
          (|b'.levM * b'.w| * (‖z‖ + (|b.ell| + |b'.ell|))) := by
        gcongr
    _ = (∑ k, |γ k|) * (|b.levM * b.w| * |b'.levM * b'.w|) * (‖z‖ + (|b.ell| + |b'.ell|)) ^ 2 := by
        ring
    _ ≤ _ := by gcongr

theorem bnd_integrable {K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (γ : Fin K → ℝ) (b b' : Bank) : Integrable (bnd γ b b') μ := by
  unfold bnd
  refine Integrable.const_mul ?_ _
  exact ((hM2.const_mul 2).add (integrable_const _))

theorem Fm_integrable {K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (γ : Fin K → ℝ) (b b' : Bank) (hb : b.Standing) (hb' : b'.Standing)
    (p q : Fin K → ℝ) (hp : p ∈ stdSimplex ℝ (Fin K)) (hq : q ∈ stdSimplex ℝ (Fin K)) :
    Integrable (Fm γ b b' p q) μ := by
  refine Integrable.mono' (bnd_integrable μ hM2 γ b b') ?_ (Filter.Eventually.of_forall
    (Fm_bound γ b b' hb hb' p q hp hq))
  have : Continuous (Fm γ b b' p q) :=
    (Fm_cont K γ b b' hb hb').comp (by fun_prop : Continuous fun z : Shock K => (p, q, z))
  exact this.aestronglyMeasurable


theorem S_eq_M {K : ℕ} (μ : Measure (Shock K)) (γ : Fin K → ℝ) (b : Bank) (p : Fin K → ℝ) :
    S μ γ b p = M μ γ b b p p := by
  unfold S M
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only; ring

theorem M_symm {K : ℕ} (μ : Measure (Shock K)) (γ : Fin K → ℝ) (b b' : Bank)
    (p q : Fin K → ℝ) : M μ γ b b' p q = M μ γ b' b q p := by
  unfold M
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  have : ∑ k, p k * γ k * q k = ∑ k, q k * γ k * p k :=
    Finset.sum_congr rfl (fun k _ => by ring)
  simp only [this]; ring

theorem EC_eq {N K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (γ : Fin K → ℝ) (π : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K)) (i : Fin N) :
    EC μ B γ π i = ∑ j, M μ γ (B i) (B j) (π i) (π j) := by
  unfold EC M
  rw [← integral_finsetSum]
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [cost, ret]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  · intro j _
    exact Fm_integrable μ hM2 γ (B i) (B j) (hB i) (hB j) (π i) (π j) (hπ i) (hπ j)

theorem Pot_eq {N K : ℕ} (μ : Measure (Shock K)) (B : Fin N → Bank)
    (γ : Fin K → ℝ) (π : Fin N → Fin K → ℝ) :
    Pot μ B γ π = ∑ m, (M μ γ (B m) (B m) (π m) (π m) +
      ∑ j ∈ Finset.univ.filter (· < m), M μ γ (B m) (B j) (π m) (π j)) := by
  unfold Pot
  simp only [S_eq_M]

theorem pot_ident {N K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (γ : Fin K → ℝ) (π π' : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K))
    (hπ' : ∀ j, π' j ∈ stdSimplex ℝ (Fin K)) (i : Fin N) (he : ∀ j, j ≠ i → π j = π' j) :
    EC μ B γ π i - EC μ B γ π' i = Pot μ B γ π - Pot μ B γ π' := by
  rw [EC_eq μ hM2 B hB γ π hπ, EC_eq μ hM2 B hB γ π' hπ', Pot_eq, Pot_eq]
  symm
  apply SysDivComb.pot_diff (fun m j => M μ γ (B m) (B j) (π m) (π j))
    (fun m j => M μ γ (B m) (B j) (π' m) (π' j))
  · intro m j; exact M_symm μ γ _ _ _ _
  · intro m j; exact M_symm μ γ _ _ _ _
  · intro m j hm hj; simp only [he m hm, he j hj]

theorem M_contOn {N K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (γ : Fin K → ℝ) (m j : Fin N) :
    ContinuousOn (fun π : Fin N → Fin K → ℝ => M μ γ (B m) (B j) (π m) (π j))
      (Admissible N K) := by
  have hmem : ∀ π ∈ Admissible N K, ∀ j, π j ∈ stdSimplex ℝ (Fin K) := fun π hπ j =>
    (Set.mem_univ_pi.1 hπ) j
  refine continuousOn_of_dominated (bound := bnd γ (B m) (B j)) ?_ ?_
    (bnd_integrable μ hM2 γ _ _) ?_
  · intro π hπ
    exact (Fm_integrable μ hM2 γ (B m) (B j) (hB m) (hB j) (π m) (π j) (hmem π hπ m)
      (hmem π hπ j)).aestronglyMeasurable
  · intro π hπ
    exact Filter.Eventually.of_forall (Fm_bound γ (B m) (B j) (hB m) (hB j) (π m) (π j)
      (hmem π hπ m) (hmem π hπ j))
  · refine Filter.Eventually.of_forall (fun z => ?_)
    exact ((Fm_cont K γ (B m) (B j) (hB m) (hB j)).comp
      (by fun_prop : Continuous fun π : Fin N → Fin K → ℝ => (π m, π j, z))).continuousOn

theorem Pot_contOn {N K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (γ : Fin K → ℝ) : ContinuousOn (Pot μ B γ) (Admissible N K) := by
  have : Pot μ B γ = fun π => ∑ m, (M μ γ (B m) (B m) (π m) (π m) +
      ∑ j ∈ Finset.univ.filter (· < m), M μ γ (B m) (B j) (π m) (π j)) := by
    funext π; exact Pot_eq μ B γ π
  rw [this]
  refine continuousOn_finsetSum _ (fun m _ => ?_)
  refine (M_contOn μ hM2 B hB γ m m).add (continuousOn_finsetSum _ (fun j _ => ?_))
  exact M_contOn μ hM2 B hB γ m j

end SysDivAn



open MeasureTheory

namespace SysDivQ
open SystemicDiv.SellOff SysDivAn

/-- Bank `m`'s liquidated holding of asset `k`: `π_{m,k} x_m`. -/
noncomputable def u {N K : ℕ} (B : Fin N → Bank) (π : Fin N → Fin K → ℝ) (m : Fin N) (k : Fin K)
    (z : Shock K) : ℝ := π m k * sold (B m) (portRet (π m) z)

noncomputable def Q {N K : ℕ} (γ : Fin K → ℝ) (B : Fin N → Bank) (π : Fin N → Fin K → ℝ)
    (z : Shock K) : ℝ :=
  (1 / 2) * ∑ k, γ k * (∑ m, u B π m k z ^ 2 + (∑ m, u B π m k z) ^ 2)

theorem u_cont {N K : ℕ} (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (π : Fin N → Fin K → ℝ) (m : Fin N) (k : Fin K) : Continuous (u B π m k) := by
  unfold u portRet
  rw [sold_eq (B m) (hB m)]
  fun_prop

/-- uniform constants -/
noncomputable def cA {N : ℕ} (B : Fin N → Bank) : ℝ := ∑ m, |(B m).levM * (B m).w|
noncomputable def cL {N : ℕ} (B : Fin N → Bank) : ℝ := ∑ m, |(B m).ell|

theorem cA_nonneg {N : ℕ} (B : Fin N → Bank) : 0 ≤ cA B :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)
theorem cL_nonneg {N : ℕ} (B : Fin N → Bank) : 0 ≤ cL B :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)
theorem le_cA {N : ℕ} (B : Fin N → Bank) (m : Fin N) : |(B m).levM * (B m).w| ≤ cA B :=
  Finset.single_le_sum (f := fun m => |(B m).levM * (B m).w|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ m)
theorem le_cL {N : ℕ} (B : Fin N → Bank) (m : Fin N) : |(B m).ell| ≤ cL B :=
  Finset.single_le_sum (f := fun m => |(B m).ell|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ m)

theorem simplex_le_one {K : ℕ} (p : Fin K → ℝ) (hp : p ∈ stdSimplex ℝ (Fin K)) (k : Fin K) :
    p k ≤ 1 := by
  have := Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ k); rw [hp.2] at this
  exact this

theorem sold_abs_le' {N K : ℕ} (B : Fin N → Bank) (hB : ∀ i, (B i).Standing) (m : Fin N)
    (p : Fin K → ℝ) (hp : p ∈ stdSimplex ℝ (Fin K)) (z : Shock K) :
    |sold (B m) (portRet p z)| ≤ cA B * (‖z‖ + cL B) := by
  refine (sold_abs_le (B m) (hB m) _).trans ?_
  have := portRet_abs_le p hp z
  have := le_cA B m; have := le_cL B m
  have : 0 ≤ ‖z‖ := norm_nonneg _
  have := cA_nonneg B
  gcongr

theorem u_abs_le {N K : ℕ} (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (π : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K)) (m : Fin N) (k : Fin K)
    (z : Shock K) : |u B π m k z| ≤ cA B * (‖z‖ + cL B) := by
  unfold u
  rw [abs_mul, abs_of_nonneg ((hπ m).1 k)]
  have h1 := simplex_le_one _ (hπ m) k
  have h2 := sold_abs_le' B hB m (π m) (hπ m) z
  have h3 : 0 ≤ cA B * (‖z‖ + cL B) := mul_nonneg (cA_nonneg B) (by
    have := cL_nonneg B; positivity)
  calc π m k * |sold (B m) (portRet (π m) z)| ≤ 1 * (cA B * (‖z‖ + cL B)) := by
        gcongr
    _ = _ := one_mul _

/-- a function bounded by `C (‖z‖ + L)^2`, continuous, is integrable -/
theorem int_of_bound {K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (f : Shock K → ℝ) (hf : Continuous f) (C L : ℝ) (hL : 0 ≤ L)
    (h : ∀ z, |f z| ≤ C * (‖z‖ + L) ^ 2) : Integrable f μ := by
  refine Integrable.mono' (g := fun z => |C| * (2 * ‖z‖ ^ 2 + 2 * L ^ 2))
    (((hM2.const_mul 2).add (integrable_const _)).const_mul _) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs]
  refine (h z).trans ?_
  have h1 : (‖z‖ + L) ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * L ^ 2 := by nlinarith [sq_nonneg (‖z‖ - L)]
  calc C * (‖z‖ + L) ^ 2 ≤ |C| * (‖z‖ + L) ^ 2 := by gcongr; exact le_abs_self C
    _ ≤ _ := by gcongr

theorem sq_int {K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (L : ℝ) (hL : 0 ≤ L) : Integrable (fun z : Shock K => (‖z‖ + L) ^ 2) μ :=
  int_of_bound μ hM2 _ (by fun_prop) 1 L hL (fun z => by
    rw [abs_of_nonneg (sq_nonneg _), one_mul])

theorem Q_cont {N K : ℕ} (γ : Fin K → ℝ) (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (π : Fin N → Fin K → ℝ) : Continuous (Q γ B π) := by
  unfold Q
  have := u_cont B hB π
  fun_prop

theorem Q_abs_le {N K : ℕ} (γ : Fin K → ℝ) (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (π : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K)) (z : Shock K) :
    |Q γ B π z| ≤ ((∑ k, |γ k|) * (N + N ^ 2) * cA B ^ 2) * (‖z‖ + cL B) ^ 2 := by
  set G := cA B * (‖z‖ + cL B)
  have hG : 0 ≤ G := mul_nonneg (cA_nonneg B) (by have := cL_nonneg B; positivity)
  have hu := u_abs_le B hB π hπ
  have hk : ∀ k, |∑ m, u B π m k z ^ 2 + (∑ m, u B π m k z) ^ 2| ≤ (N + N ^ 2) * G ^ 2 := by
    intro k
    have e1 : |∑ m, u B π m k z ^ 2| ≤ N * G ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ m, |u B π m k z ^ 2| ≤ ∑ _m : Fin N, G ^ 2 := by
            refine Finset.sum_le_sum (fun m _ => ?_)
            rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hu m k z) 2
        _ = N * G ^ 2 := by simp
    have e2 : |(∑ m, u B π m k z) ^ 2| ≤ N ^ 2 * G ^ 2 := by
      rw [abs_pow]
      have : |∑ m, u B π m k z| ≤ N * G := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ m, |u B π m k z| ≤ ∑ _m : Fin N, G := Finset.sum_le_sum (fun m _ => hu m k z)
          _ = N * G := by simp
      calc |∑ m, u B π m k z| ^ 2 ≤ (N * G) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = _ := by ring
    calc _ ≤ |∑ m, u B π m k z ^ 2| + |(∑ m, u B π m k z) ^ 2| := abs_add_le _ _
      _ ≤ N * G ^ 2 + N ^ 2 * G ^ 2 := add_le_add e1 e2
      _ = _ := by ring
  unfold Q
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  have hsum : |∑ k, γ k * (∑ m, u B π m k z ^ 2 + (∑ m, u B π m k z) ^ 2)| ≤
      (∑ k, |γ k|) * ((N + N ^ 2) * G ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hk k) (abs_nonneg _)
  have hpos : 0 ≤ (∑ k, |γ k|) * ((N + N ^ 2) * G ^ 2) :=
    mul_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)
  calc 1 / 2 * |∑ k, γ k * (∑ m, u B π m k z ^ 2 + (∑ m, u B π m k z) ^ 2)|
      ≤ 1 * ((∑ k, |γ k|) * ((N + N ^ 2) * G ^ 2)) := by
        nlinarith [abs_nonneg (∑ k, γ k * (∑ m, u B π m k z ^ 2 + (∑ m, u B π m k z) ^ 2))]
    _ = _ := by simp only [G]; ring

theorem Q_int {N K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (γ : Fin K → ℝ) (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (π : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K)) : Integrable (Q γ B π) μ :=
  int_of_bound μ hM2 _ (Q_cont γ B hB π) _ _ (cL_nonneg B) (Q_abs_le γ B hB π hπ)

theorem Fm_eq_u {N K : ℕ} (γ : Fin K → ℝ) (B : Fin N → Bank) (π : Fin N → Fin K → ℝ)
    (m j : Fin N) (z : Shock K) :
    Fm γ (B m) (B j) (π m) (π j) z = ∑ k, γ k * (u B π m k z * u B π j k z) := by
  unfold Fm u
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem two_Q {N K : ℕ} (γ : Fin K → ℝ) (B : Fin N → Bank) (π : Fin N → Fin K → ℝ)
    (z : Shock K) :
    ∑ m, Fm γ (B m) (B m) (π m) (π m) z + ∑ m, ∑ j, Fm γ (B m) (B j) (π m) (π j) z =
      2 * Q γ B π z := by
  simp only [Fm_eq_u, Q]
  have h1 : ∀ m, ∑ k, γ k * (u B π m k z * u B π m k z) = ∑ k, γ k * u B π m k z ^ 2 := by
    intro m; refine Finset.sum_congr rfl (fun k _ => by ring)
  have h2 : ∑ m, ∑ j, ∑ k, γ k * (u B π m k z * u B π j k z) =
      ∑ k, γ k * (∑ m, u B π m k z) ^ 2 := by
    calc ∑ m, ∑ j, ∑ k, γ k * (u B π m k z * u B π j k z)
        = ∑ m, ∑ k, ∑ j, γ k * (u B π m k z * u B π j k z) :=
          Finset.sum_congr rfl (fun m _ => Finset.sum_comm)
      _ = ∑ k, ∑ m, ∑ j, γ k * (u B π m k z * u B π j k z) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun m _ => h1 m), h2, Finset.sum_comm]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  ring

theorem Pot_Q {N K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (γ : Fin K → ℝ) (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (π : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K)) :
    Pot μ B γ π = ∫ z, Q γ B π z ∂μ := by
  have hd := SysDivComb.pot_double (fun m j => M μ γ (B m) (B j) (π m) (π j))
    (fun m j => M_symm μ γ _ _ _ _)
  rw [← Pot_eq] at hd
  have hi : ∀ m j, Integrable (Fm γ (B m) (B j) (π m) (π j)) μ := fun m j =>
    Fm_integrable μ hM2 γ (B m) (B j) (hB m) (hB j) (π m) (π j) (hπ m) (hπ j)
  have h2 : ∑ m, M μ γ (B m) (B m) (π m) (π m) + ∑ m, ∑ j, M μ γ (B m) (B j) (π m) (π j) =
      ∫ z, 2 * Q γ B π z ∂μ := by
    have hM : ∀ m j, M μ γ (B m) (B j) (π m) (π j) = ∫ z, Fm γ (B m) (B j) (π m) (π j) z ∂μ :=
      fun _ _ => rfl
    simp only [hM]
    rw [← integral_finsetSum _ (fun m _ => hi m m)]
    rw [Finset.sum_congr rfl (fun m _ => (integral_finsetSum _ (fun j _ => hi m j)).symm)]
    rw [← integral_finsetSum _ (fun m _ => integrable_finset_sum _ (fun j _ => hi m j))]
    rw [← integral_add (integrable_finset_sum _ (fun m _ => hi m m))
      (integrable_finset_sum _ (fun m _ => integrable_finset_sum _ (fun j _ => hi m j)))]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Finset.sum_apply]
    exact two_Q γ B π z
  rw [integral_const_mul] at h2
  linarith

end SysDivQ


open MeasureTheory

namespace SysDivQ
open SystemicDiv.SellOff SysDivAn

/-- the segment of profiles `π + t (π' - π)` -/
def seg {N K : ℕ} (π π' : Fin N → Fin K → ℝ) (t : ℝ) : Fin N → Fin K → ℝ :=
  fun m k => π m k + t * (π' m k - π m k)

theorem seg_mem {N K : ℕ} (π π' : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K))
    (hπ' : ∀ j, π' j ∈ stdSimplex ℝ (Fin K)) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (j : Fin N) :
    seg π π' t j ∈ stdSimplex ℝ (Fin K) := by
  have ha : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
  have hb : (0:ℝ) ≤ t := ht.1
  have h := (convex_stdSimplex ℝ (Fin K)) (hπ j) (hπ' j) ha hb (by ring)
  convert h using 1
  funext k; simp [seg]; ring

theorem sold_lip (b : Bank) (hb : b.Standing) (R R' : ℝ) :
    |sold b R - sold b R'| ≤ |b.levM * b.w| * |R - R'| := by
  rw [sold_eq b hb]
  simp only
  rw [← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (abs_max_sub_max_le_abs (-(R + b.ell)) (-(R' + b.ell)) (0:ℝ)).trans (le_of_eq ?_)
  rw [show -(R + b.ell) - -(R' + b.ell) = -(R - R') by ring, abs_neg]

theorem portRet_sub_le {K : ℕ} (p q : Fin K → ℝ) (hp : p ∈ stdSimplex ℝ (Fin K))
    (hq : q ∈ stdSimplex ℝ (Fin K)) (t : ℝ) (ht : 0 ≤ t) (z : Shock K) :
    |portRet (fun k => p k + t * (q k - p k)) z - portRet p z| ≤ t * (K * ‖z‖) := by
  unfold portRet
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |(p k + t * (q k - p k)) * z k - p k * z k| ≤ ∑ _k : Fin K, t * ‖z‖ := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [show (p k + t * (q k - p k)) * z k - p k * z k = t * ((q k - p k) * z k) by ring,
          abs_mul, abs_of_nonneg ht, abs_mul]
        have h1 : |q k - p k| ≤ 1 := by
          rw [abs_le]
          have := hp.1 k; have := hq.1 k
          have := simplex_le_one p hp k; have := simplex_le_one q hq k
          constructor <;> linarith
        have h2 : |z k| ≤ ‖z‖ := by simpa using PiLp.norm_apply_le z k
        have := abs_nonneg (z k)
        gcongr
        calc |q k - p k| * |z k| ≤ 1 * ‖z‖ := by gcongr
          _ = ‖z‖ := one_mul _
    _ = t * (K * ‖z‖) := by simp; ring

theorem delta_le {N K : ℕ} (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (π π' : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K))
    (hπ' : ∀ j, π' j ∈ stdSimplex ℝ (Fin K)) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (m : Fin N) (k : Fin K) (z : Shock K) :
    |u B (seg π π' t) m k z - u B π m k z| ≤ t * (cA B * (K + 1) * (‖z‖ + cL B)) := by
  have hs := seg_mem π π' hπ hπ' t ht
  unfold u
  have e : seg π π' t m k * sold (B m) (portRet (seg π π' t m) z) -
      π m k * sold (B m) (portRet (π m) z) =
      (seg π π' t m k - π m k) * sold (B m) (portRet (seg π π' t m) z) +
        π m k * (sold (B m) (portRet (seg π π' t m) z) - sold (B m) (portRet (π m) z)) := by ring
  rw [e]
  have h1 : |seg π π' t m k - π m k| ≤ t := by
    simp only [seg]
    rw [show π m k + t * (π' m k - π m k) - π m k = t * (π' m k - π m k) by ring, abs_mul,
      abs_of_nonneg ht.1]
    have : |π' m k - π m k| ≤ 1 := by
      rw [abs_le]
      have := (hπ m).1 k; have := (hπ' m).1 k
      have := simplex_le_one _ (hπ m) k; have := simplex_le_one _ (hπ' m) k
      constructor <;> linarith
    nlinarith [ht.1]
  have h2 := sold_abs_le' B hB m _ (hs m) z
  have h3 : |sold (B m) (portRet (seg π π' t m) z) - sold (B m) (portRet (π m) z)| ≤
      cA B * (t * (K * ‖z‖)) := by
    refine (sold_lip (B m) (hB m) _ _).trans ?_
    have := le_cA B m
    have := portRet_sub_le (π m) (π' m) (hπ m) (hπ' m) t ht.1 z
    have hp : |portRet (seg π π' t m) z - portRet (π m) z| ≤ t * (K * ‖z‖) := this
    have := cA_nonneg B
    gcongr
  have h4 : |π m k| ≤ 1 := by
    rw [abs_of_nonneg ((hπ m).1 k)]; exact simplex_le_one _ (hπ m) k
  have hA := cA_nonneg B
  have hL := cL_nonneg B
  have hz := norm_nonneg z
  have ht0 := ht.1
  calc |(seg π π' t m k - π m k) * sold (B m) (portRet (seg π π' t m) z) +
        π m k * (sold (B m) (portRet (seg π π' t m) z) - sold (B m) (portRet (π m) z))|
      ≤ |seg π π' t m k - π m k| * |sold (B m) (portRet (seg π π' t m) z)| +
        |π m k| * |sold (B m) (portRet (seg π π' t m) z) - sold (B m) (portRet (π m) z)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ t * (cA B * (‖z‖ + cL B)) + 1 * (cA B * (t * (K * ‖z‖))) := by
        gcongr
    _ ≤ t * (cA B * (K + 1) * (‖z‖ + cL B)) := by
        have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
        have : t * (cA B * (‖z‖ + cL B)) + 1 * (cA B * (t * (K * ‖z‖))) =
            t * cA B * (‖z‖ + cL B + K * ‖z‖) := by ring
        rw [this]
        have : ‖z‖ + cL B + K * ‖z‖ ≤ (K + 1) * (‖z‖ + cL B) := by nlinarith
        calc t * cA B * (‖z‖ + cL B + K * ‖z‖) ≤ t * cA B * ((K + 1) * (‖z‖ + cL B)) := by
              gcongr
          _ = _ := by ring

end SysDivQ


open MeasureTheory

namespace SysDivQ
open SystemicDiv.SellOff SysDivAn

theorem upd_identity {N : ℕ} (a b : Fin N → ℝ) :
    (∑ m, b m ^ 2 + (∑ m, b m) ^ 2) - (∑ m, a m ^ 2 + (∑ m, a m) ^ 2) -
      ∑ i, ((∑ m, (if m = i then b m else a m) ^ 2 + (∑ m, (if m = i then b m else a m)) ^ 2) -
        (∑ m, a m ^ 2 + (∑ m, a m) ^ 2)) =
      (∑ m, (b m - a m)) ^ 2 - ∑ m, (b m - a m) ^ 2 := by
  have hc1 : ∀ i, ∑ m, (if m = i then b m else a m) ^ 2 = ∑ m, a m ^ 2 + (b i ^ 2 - a i ^ 2) := by
    intro i
    have : ∀ m, (if m = i then b m else a m) ^ 2 =
        a m ^ 2 + (if m = i then b m ^ 2 - a m ^ 2 else 0) := by
      intro m; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun m _ => this m), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  have hc2 : ∀ i, ∑ m, (if m = i then b m else a m) = ∑ m, a m + (b i - a i) := by
    intro i
    have : ∀ m, (if m = i then b m else a m) = a m + (if m = i then b m - a m else 0) := by
      intro m; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun m _ => this m), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  simp only [hc1, hc2]
  have h3 : ∀ i, (∑ m, a m ^ 2 + (b i ^ 2 - a i ^ 2) + (∑ m, a m + (b i - a i)) ^ 2 -
      (∑ m, a m ^ 2 + (∑ m, a m) ^ 2)) =
      (b i ^ 2 - a i ^ 2) + 2 * (∑ m, a m) * (b i - a i) + (b i - a i) ^ 2 := by
    intro i; ring
  rw [Finset.sum_congr rfl (fun i _ => h3 i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hb : ∑ m, b m = ∑ m, a m + ∑ m, (b m - a m) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hb]
  ring

theorem u_update {N K : ℕ} (B : Fin N → Bank) (π π2 : Fin N → Fin K → ℝ) (i : Fin N)
    (m : Fin N) (k : Fin K) (z : Shock K) :
    u B (Function.update π i (π2 i)) m k z = if m = i then u B π2 m k z else u B π m k z := by
  unfold u
  by_cases h : m = i
  · subst h; simp
  · simp [h, Function.update_of_ne h]

theorem Q_ineq {N K : ℕ} (γ : Fin K → ℝ) (hγ : ∀ k, 0 ≤ γ k) (B : Fin N → Bank)
    (π π2 : Fin N → Fin K → ℝ) (z : Shock K) :
    -(1 / 2 * ∑ k, γ k * ∑ m, (u B π2 m k z - u B π m k z) ^ 2) ≤
      Q γ B π2 z - Q γ B π z - ∑ i, (Q γ B (Function.update π i (π2 i)) z - Q γ B π z) := by
  have key : Q γ B π2 z - Q γ B π z - ∑ i, (Q γ B (Function.update π i (π2 i)) z - Q γ B π z) =
      1 / 2 * ∑ k, γ k * ((∑ m, (u B π2 m k z - u B π m k z)) ^ 2 -
        ∑ m, (u B π2 m k z - u B π m k z) ^ 2) := by
    simp only [← upd_identity]
    unfold Q
    simp only [u_update]
    simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i k => 1 / 2 * (γ k * (∑ m, (if m = i then u B π2 m k z else u B π m k z) ^ 2 +
        (∑ m, if m = i then u B π2 m k z else u B π m k z) ^ 2)) -
          1 / 2 * (γ k * (∑ m, u B π m k z ^ 2 + (∑ m, u B π m k z) ^ 2)))]
    rw [← Finset.sum_sub_distrib]
  rw [key]
  have : ∀ k, γ k * (-(∑ m, (u B π2 m k z - u B π m k z) ^ 2)) ≤
      γ k * ((∑ m, (u B π2 m k z - u B π m k z)) ^ 2 - ∑ m, (u B π2 m k z - u B π m k z) ^ 2) := by
    intro k
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (∑ m, (u B π2 m k z - u B π m k z))])
      (hγ k)
  have h2 := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => this k)
  simp only [mul_neg, Finset.sum_neg_distrib] at h2
  linarith

end SysDivQ


open MeasureTheory

namespace SysDivQ
open SystemicDiv.SellOff SysDivAn

theorem update_mem {N K : ℕ} (π : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K))
    (i : Fin N) (q : Fin K → ℝ) (hq : q ∈ stdSimplex ℝ (Fin K)) (j : Fin N) :
    Function.update π i q j ∈ stdSimplex ℝ (Fin K) := by
  by_cases hj : j = i
  · subst hj; simpa using hq
  · rw [Function.update_of_ne hj]; exact hπ j

theorem delta_sq_sum_le {N K : ℕ} (γ : Fin K → ℝ) (hγ : ∀ k, 0 ≤ γ k) (B : Fin N → Bank)
    (hB : ∀ i, (B i).Standing)
    (π π' : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K))
    (hπ' : ∀ j, π' j ∈ stdSimplex ℝ (Fin K)) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (z : Shock K) :
    ∑ k, γ k * ∑ m, (u B (seg π π' t) m k z - u B π m k z) ^ 2 ≤
      t ^ 2 * (((∑ k, γ k) * N * (cA B * (K + 1)) ^ 2) * (‖z‖ + cL B) ^ 2) := by
  have hΔ : ∀ m k, (u B (seg π π' t) m k z - u B π m k z) ^ 2 ≤
      t ^ 2 * ((cA B * (K + 1)) ^ 2 * (‖z‖ + cL B) ^ 2) := by
    intro m k
    have h := delta_le B hB π π' hπ hπ' t ht m k z
    have h0 : 0 ≤ t * (cA B * (K + 1) * (‖z‖ + cL B)) := le_trans (abs_nonneg _) h
    calc (u B (seg π π' t) m k z - u B π m k z) ^ 2
        = |u B (seg π π' t) m k z - u B π m k z| ^ 2 := (sq_abs _).symm
      _ ≤ (t * (cA B * (K + 1) * (‖z‖ + cL B))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = _ := by ring
  calc ∑ k, γ k * ∑ m, (u B (seg π π' t) m k z - u B π m k z) ^ 2
      ≤ ∑ k, γ k * ∑ _m : Fin N, t ^ 2 * ((cA B * (K + 1)) ^ 2 * (‖z‖ + cL B) ^ 2) := by
        refine Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun m _ => hΔ m k)) (hγ k))
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => by ring)

theorem approx_add {N K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (γ : Fin K → ℝ) (hγ : ∀ k, 0 ≤ γ k) (B : Fin N → Bank)
    (hB : ∀ i, (B i).Standing)
    (π π' : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K))
    (hπ' : ∀ j, π' j ∈ stdSimplex ℝ (Fin K)) :
    ∃ C, ∀ t ∈ Set.Icc (0:ℝ) 1, -(C * t ^ 2) ≤
      Pot μ B γ (seg π π' t) - Pot μ B γ π -
        ∑ i, (Pot μ B γ (Function.update π i (seg π π' t i)) - Pot μ B γ π) := by
  set D := (∑ k, γ k) * N * (cA B * (K + 1)) ^ 2
  refine ⟨1 / 2 * D * ∫ z, (‖z‖ + cL B) ^ 2 ∂μ, fun t ht => ?_⟩
  have hs := seg_mem π π' hπ hπ' t ht
  have hu : ∀ i, ∀ j, Function.update π i (seg π π' t i) j ∈ stdSimplex ℝ (Fin K) :=
    fun i => update_mem π hπ i _ (hs i)
  rw [Pot_Q μ hM2 γ B hB _ hs, Pot_Q μ hM2 γ B hB _ hπ]
  simp only [Pot_Q μ hM2 γ B hB _ (hu _)]
  have iQ := fun π (h : ∀ j, π j ∈ stdSimplex ℝ (Fin K)) => Q_int μ hM2 γ B hB π h
  rw [← integral_sub (iQ _ hs) (iQ _ hπ)]
  simp only [← integral_sub (iQ _ (hu _)) (iQ _ hπ)]
  have hi : ∀ i, Integrable (fun a => Q γ B (Function.update π i (seg π π' t i)) a - Q γ B π a) μ :=
    fun i => (iQ _ (hu i)).sub (iQ _ hπ)
  have h0 : Integrable (fun a => Q γ B (seg π π' t) a - Q γ B π a) μ := (iQ _ hs).sub (iQ _ hπ)
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  rw [← integral_sub h0 (integrable_finset_sum _ (fun i _ => hi i))]
  have hW := sq_int μ hM2 (cL B) (cL_nonneg B)
  have : -((1 / 2 * D * ∫ z, (‖z‖ + cL B) ^ 2 ∂μ) * t ^ 2) =
      ∫ z, -(1 / 2 * (t ^ 2 * (D * (‖z‖ + cL B) ^ 2))) ∂μ := by
    rw [integral_neg, integral_const_mul, integral_const_mul, integral_const_mul]; ring
  rw [this]
  refine integral_mono (((hW.const_mul D).const_mul _).const_mul _).neg
    (h0.sub (integrable_finset_sum _ (fun i _ => hi i))) (fun z => ?_)
  simp only [Finset.sum_apply]
  refine le_trans ?_ (Q_ineq γ hγ B π (seg π π' t) z)
  have := delta_sq_sum_le γ hγ B hB π π' hπ hπ' t ht z
  linarith

end SysDivQ


open MeasureTheory

namespace SysDivQ
open SystemicDiv.SellOff SysDivAn

theorem cvx_trick (H : ℝ → ℝ) (hH : ConvexOn ℝ (Set.Icc (0:ℝ) 1) H) (C : ℝ)
    (h : ∀ t ∈ Set.Ioc (0:ℝ) 1, H 0 - C * t ^ 2 ≤ H t) : H 0 ≤ H 1 := by
  by_contra hlt
  push_neg at hlt
  set d := H 0 - H 1 with hd
  have dpos : 0 < d := by linarith
  have key : ∀ t ∈ Set.Ioc (0:ℝ) 1, d ≤ C * t := by
    intro t ht
    have h1 := hH.2 (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 by simp) (show (1:ℝ) ∈ Set.Icc (0:ℝ) 1 by simp)
      (show (0:ℝ) ≤ 1 - t by linarith [ht.2]) ht.1.le (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one] at h1
    have h2 := h t ht
    have : t * d ≤ t * (C * t) := by nlinarith
    exact le_of_mul_le_mul_left this ht.1
  set t := min 1 (d / (2 * (|C| + 1))) with htdef
  have hC : 0 < 2 * (|C| + 1) := by positivity
  have ht0 : 0 < t := lt_min one_pos (div_pos dpos hC)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ d / (2 * (|C| + 1)) := min_le_right _ _
  have h3 := key t ⟨ht0, ht1⟩
  have h4 : C * t ≤ |C| * t := mul_le_mul_of_nonneg_right (le_abs_self C) ht0.le
  have h5 : |C| * t ≤ |C| * (d / (2 * (|C| + 1))) := mul_le_mul_of_nonneg_left ht2 (abs_nonneg C)
  have h6 : |C| * (d / (2 * (|C| + 1))) < d := by
    rw [mul_div_assoc', div_lt_iff₀ hC]; nlinarith [abs_nonneg C]
  linarith

theorem seg_zero {N K : ℕ} (π π' : Fin N → Fin K → ℝ) : seg π π' 0 = π := by
  funext m k; simp [seg]

theorem seg_one {N K : ℕ} (π π' : Fin N → Fin K → ℝ) : seg π π' 1 = π' := by
  funext m k; simp [seg]

theorem seg_mem_adm {N K : ℕ} (π π' : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K))
    (hπ' : ∀ j, π' j ∈ stdSimplex ℝ (Fin K)) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    seg π π' t ∈ Admissible N K :=
  Set.mem_univ_pi.2 (seg_mem π π' hπ hπ' t ht)

theorem seg_convex {N K : ℕ} (μ : Measure (Shock K)) (B : Fin N → Bank) (γ : Fin K → ℝ)
    (hconv : ConvexOn ℝ (Admissible N K) (Pot μ B γ))
    (π π' : Fin N → Fin K → ℝ) (hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K))
    (hπ' : ∀ j, π' j ∈ stdSimplex ℝ (Fin K)) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun t => Pot μ B γ (seg π π' t)) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have e : seg π π' (a • x + b • y) = a • seg π π' x + b • seg π π' y := by
    funext m k
    simp only [seg, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
    have : b = 1 - a := by linarith
    subst this; ring
  simp only
  rw [e]
  exact hconv.2 (seg_mem_adm π π' hπ hπ' x hx) (seg_mem_adm π π' hπ hπ' y hy) ha hb hab

theorem nash_min {N K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (γ : Fin K → ℝ) (hγ : ∀ k, 0 ≤ γ k) (B : Fin N → Bank)
    (hB : ∀ i, (B i).Standing) (hconv : ConvexOn ℝ (Admissible N K) (Pot μ B γ))
    (π : Fin N → Fin K → ℝ) (hN : IsNash μ B γ π) (π' : Fin N → Fin K → ℝ)
    (hπ' : π' ∈ Admissible N K) : Pot μ B γ π ≤ Pot μ B γ π' := by
  have hπ : ∀ j, π j ∈ stdSimplex ℝ (Fin K) := fun j => (Set.mem_univ_pi.1 hN.1) j
  have hπ'' : ∀ j, π' j ∈ stdSimplex ℝ (Fin K) := fun j => (Set.mem_univ_pi.1 hπ') j
  obtain ⟨C, hC⟩ := approx_add μ hM2 γ hγ B hB π π' hπ hπ''
  have := cvx_trick (fun t => Pot μ B γ (seg π π' t)) (seg_convex μ B γ hconv π π' hπ hπ'') C
    (fun t ht => by
      have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have h1 := hC t ht'
      have hs := seg_mem π π' hπ hπ'' t ht'
      have h2 : 0 ≤ ∑ i, (Pot μ B γ (Function.update π i (seg π π' t i)) - Pot μ B γ π) := by
        refine Finset.sum_nonneg (fun i _ => ?_)
        have hid := pot_ident μ hM2 B hB γ (Function.update π i (seg π π' t i)) π
          (update_mem π hπ i _ (hs i)) hπ i (fun j hj => Function.update_of_ne hj _ _)
        have := hN.2 i (seg π π' t i) (hs i)
        linarith
      simp only [seg_zero]
      linarith)
  simpa [seg_zero, seg_one] using this

end SysDivQ


open MeasureTheory

namespace SysDivQ
open SystemicDiv.SellOff SysDivAn

theorem sum_ite_sq {N : ℕ} (a : Fin N → ℝ) (i : Fin N) (x : ℝ) :
    ∑ m, (if m = i then x else a m) ^ 2 = ∑ m, a m ^ 2 + (x ^ 2 - a i ^ 2) := by
  have : ∀ m, (if m = i then x else a m) ^ 2 = a m ^ 2 + (if m = i then x ^ 2 - a m ^ 2 else 0) := by
    intro m; split_ifs with h <;> [subst h; skip] <;> ring
  rw [Finset.sum_congr rfl (fun m _ => this m), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem sum_ite_lin {N : ℕ} (a : Fin N → ℝ) (i : Fin N) (x : ℝ) :
    ∑ m, (if m = i then x else a m) = ∑ m, a m + (x - a i) := by
  have : ∀ m, (if m = i then x else a m) = a m + (if m = i then x - a m else 0) := by
    intro m; split_ifs with h <;> [subst h; skip] <;> ring
  rw [Finset.sum_congr rfl (fun m _ => this m), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- `Q` after a unilateral change of bank `i`. -/
theorem Q_upd {N K : ℕ} (γ : Fin K → ℝ) (B : Fin N → Bank) (π π2 : Fin N → Fin K → ℝ)
    (i : Fin N) (z : Shock K) :
    Q γ B (Function.update π i (π2 i)) z - Q γ B π z =
      1 / 2 * ∑ k, γ k * ((u B π2 i k z ^ 2 - u B π i k z ^ 2) +
        2 * (∑ m, u B π m k z) * (u B π2 i k z - u B π i k z) +
          (u B π2 i k z - u B π i k z) ^ 2) := by
  unfold Q
  have h1 : ∀ k, ∑ m, u B (Function.update π i (π2 i)) m k z ^ 2 =
      ∑ m, u B π m k z ^ 2 + (u B π2 i k z ^ 2 - u B π i k z ^ 2) := by
    intro k
    have : ∀ m, u B (Function.update π i (π2 i)) m k z =
        if m = i then u B π2 i k z else u B π m k z := by
      intro m; rw [u_update]; split_ifs with h <;> [subst h; skip] <;> rfl
    simp only [this]; exact sum_ite_sq _ i _
  have h2 : ∀ k, ∑ m, u B (Function.update π i (π2 i)) m k z =
      ∑ m, u B π m k z + (u B π2 i k z - u B π i k z) := by
    intro k
    have : ∀ m, u B (Function.update π i (π2 i)) m k z =
        if m = i then u B π2 i k z else u B π m k z := by
      intro m; rw [u_update]; split_ifs with h <;> [subst h; skip] <;> rfl
    simp only [this]; exact sum_ite_lin _ i _
  simp only [h1, h2]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => by ring)

/-- `S` as an integral of a sum of squares. -/
noncomputable def Sint {K : ℕ} (γ : Fin K → ℝ) (b : Bank) (p : Fin K → ℝ) (z : Shock K) : ℝ :=
  ∑ k, γ k * (p k * sold b (portRet p z)) ^ 2

theorem S_eq_Sint {K : ℕ} (μ : Measure (Shock K)) (γ : Fin K → ℝ) (b : Bank) (p : Fin K → ℝ) :
    S μ γ b p = ∫ z, Sint γ b p z ∂μ := by
  unfold S Sint
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem Sint_int {K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (γ : Fin K → ℝ) (b : Bank) (hb : b.Standing) (p : Fin K → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin K)) : Integrable (Sint γ b p) μ := by
  have : Sint γ b p = Fm γ b b p p := by
    funext z; unfold Sint Fm; rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [this]; exact Fm_integrable μ hM2 γ b b hb hb p p hp hp

end SysDivQ


open MeasureTheory

namespace SysDivQ
open SystemicDiv.SellOff SysDivAn

theorem same_ell_bound {N K : ℕ} (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (γ : Fin K → ℝ) (hγ : ∀ k, 0 ≤ γ k) (B : Fin N → Bank)
    (hB : ∀ i, (B i).Standing) (ℓ : ℝ) (hℓ : ∀ i, (B i).ell = ℓ)
    (s : Fin K → ℝ) (hs : s ∈ stdSimplex ℝ (Fin K))
    (hmin : ∀ i, IsMinOn (S μ γ (B i)) (stdSimplex ℝ (Fin K)) s)
    (π' : Fin N → Fin K → ℝ) (hπ' : ∀ j, π' j ∈ stdSimplex ℝ (Fin K)) (i : Fin N) :
    ∃ C0, ∀ t ∈ Set.Icc (0:ℝ) 1, -(C0 * t ^ 2) ≤
      Pot μ B γ (Function.update (fun _ => s) i (seg (fun _ => s) π' t i)) -
        Pot μ B γ (fun _ => s) := by
  set sb : Fin N → Fin K → ℝ := fun _ => s with hsb
  have hsb' : ∀ j, sb j ∈ stdSimplex ℝ (Fin K) := fun _ => hs
  set c : Fin N → ℝ := fun m => (B m).levM * (B m).w with hc
  have cpos : ∀ m, 0 < c m := fun m => mul_pos (hB m).2.2.2 (hB m).1
  set Ct := ∑ m, c m
  set y : Shock K → ℝ := fun z => max (-(portRet s z + ℓ)) 0
  have hu : ∀ m k z, u B sb m k z = c m * (s k * y z) := by
    intro m k z
    simp only [u, hsb, sold_eq (B m) (hB m), hℓ m, y, hc]; ring
  have hsum : ∀ k z, ∑ m, u B sb m k z = Ct * (s k * y z) := by
    intro k z; simp only [hu, Ct, Finset.sum_mul]
  set D := (∑ k, γ k) * (cA B * (K + 1)) ^ 2
  set W := ∫ z, (‖z‖ + cL B) ^ 2 ∂μ
  refine ⟨1 / 2 * |c i - Ct| * (D * W) / c i, fun t ht => ?_⟩
  set sg := seg sb π' t
  have hsg := seg_mem sb π' hsb' hπ' t ht
  have hupd := update_mem sb hsb' i (sg i) (hsg i)
  -- the squared displacement
  set X : Shock K → ℝ := fun z => ∑ k, γ k * (u B sg i k z - u B sb i k z) ^ 2
  have hXle : ∀ z, X z ≤ t ^ 2 * (D * (‖z‖ + cL B) ^ 2) := by
    intro z
    have hΔ : ∀ k, (u B sg i k z - u B sb i k z) ^ 2 ≤
        t ^ 2 * ((cA B * (K + 1)) ^ 2 * (‖z‖ + cL B) ^ 2) := by
      intro k
      have h := delta_le B hB sb π' hsb' hπ' t ht i k z
      calc (u B sg i k z - u B sb i k z) ^ 2 = |u B sg i k z - u B sb i k z| ^ 2 := (sq_abs _).symm
        _ ≤ (t * (cA B * (K + 1) * (‖z‖ + cL B))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = _ := by ring
    calc X z ≤ ∑ k, γ k * (t ^ 2 * ((cA B * (K + 1)) ^ 2 * (‖z‖ + cL B) ^ 2)) :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hΔ k) (hγ k))
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hX0 : ∀ z, 0 ≤ X z := fun z => Finset.sum_nonneg (fun k _ => mul_nonneg (hγ k) (sq_nonneg _))
  have hXc : Continuous X := by
    have := u_cont B hB sg i; have := u_cont B hB sb i
    simp only [X]; fun_prop
  have hXi : Integrable X μ := int_of_bound μ hM2 X hXc (t ^ 2 * D) (cL B) (cL_nonneg B)
    (fun z => by rw [abs_of_nonneg (hX0 z)]; have := hXle z; linarith)
  have hW := sq_int μ hM2 (cL B) (cL_nonneg B)
  have hXint : ∫ z, X z ∂μ ≤ t ^ 2 * (D * W) := by
    have : ∫ z, X z ∂μ ≤ ∫ z, t ^ 2 * (D * (‖z‖ + cL B) ^ 2) ∂μ :=
      integral_mono hXi ((hW.const_mul D).const_mul _) hXle
    rw [integral_const_mul, integral_const_mul] at this; exact this
  have hXint0 : 0 ≤ ∫ z, X z ∂μ := integral_nonneg hX0
  -- pointwise identity
  have hpt : ∀ z, c i * (Q γ B (Function.update sb i (sg i)) z - Q γ B sb z) =
      1 / 2 * (c i + Ct) * (Sint γ (B i) (sg i) z - Sint γ (B i) s z) +
        1 / 2 * (c i - Ct) * X z := by
    intro z
    rw [Q_upd γ B sb sg i z]
    simp only [Sint, X, hsum]
    have e1 : ∀ k, (sg i k * sold (B i) (portRet (sg i) z)) = u B sg i k z := fun k => rfl
    have e2 : ∀ k, (s k * sold (B i) (portRet s z)) = u B sb i k z := fun k => rfl
    simp only [e1, e2, hu i]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  -- integrate
  have iQ := fun π (h : ∀ j, π j ∈ stdSimplex ℝ (Fin K)) => Q_int μ hM2 γ B hB π h
  have hS1 := Sint_int μ hM2 γ (B i) (hB i) (sg i) (hsg i)
  have hS2 := Sint_int μ hM2 γ (B i) (hB i) s hs
  have hint : c i * (Pot μ B γ (Function.update sb i (sg i)) - Pot μ B γ sb) =
      1 / 2 * (c i + Ct) * (S μ γ (B i) (sg i) - S μ γ (B i) s) +
        1 / 2 * (c i - Ct) * ∫ z, X z ∂μ := by
    rw [Pot_Q μ hM2 γ B hB _ hupd, Pot_Q μ hM2 γ B hB _ hsb', S_eq_Sint, S_eq_Sint,
      ← integral_sub (iQ _ hupd) (iQ _ hsb'), ← integral_sub hS1 hS2, ← integral_const_mul,
      ← integral_const_mul, ← integral_const_mul, ← integral_add]
    · exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    · exact (hS1.sub hS2).const_mul _
    · exact hXi.const_mul _
  have hSge : S μ γ (B i) s ≤ S μ γ (B i) (sg i) := hmin i (hsg i)
  have hci := cpos i
  have hlow : -(1 / 2 * |c i - Ct| * (t ^ 2 * (D * W))) ≤
      c i * (Pot μ B γ (Function.update sb i (sg i)) - Pot μ B γ sb) := by
    rw [hint]
    have hCt : 0 ≤ c i + Ct := by
      have : 0 ≤ Ct := Finset.sum_nonneg (fun m _ => (cpos m).le)
      linarith
    have h1 : 0 ≤ 1 / 2 * (c i + Ct) * (S μ γ (B i) (sg i) - S μ γ (B i) s) := by
      have := sub_nonneg.2 hSge; positivity
    have h2 : -(1 / 2 * |c i - Ct| * ∫ z, X z ∂μ) ≤ 1 / 2 * (c i - Ct) * ∫ z, X z ∂μ := by
      have := neg_abs_le (c i - Ct)
      nlinarith
    have h3 : 1 / 2 * |c i - Ct| * ∫ z, X z ∂μ ≤ 1 / 2 * |c i - Ct| * (t ^ 2 * (D * W)) := by
      have := abs_nonneg (c i - Ct)
      gcongr
    linarith
  have : -(1 / 2 * |c i - Ct| * (D * W) / c i * t ^ 2) =
      (-(1 / 2 * |c i - Ct| * (t ^ 2 * (D * W)))) / c i := by
    field_simp
  rw [this, div_le_iff₀ hci]
  linarith

end SysDivQ


open MeasureTheory

open SystemicDiv.SellOff SysDivAn SysDivQ

theorem solution {N : ℕ} (μ : Measure (Shock 2)) [IsProbabilityMeasure μ]
    (hZ : Assumption33 μ) (hM2 : SecondMoment μ)
    (γ : Fin 2 → ℝ) (hγ : ∀ k, 0 < γ k)
    (B : Fin N → Bank) (hB : ∀ i, (B i).Standing) (ℓ : ℝ) (hℓ : ∀ i, (B i).ell = ℓ)
    (h36 : StrictConvexOn ℝ (Admissible N 2) (Pot μ B γ))
    (piS : Fin 2 → ℝ) (hS : ∀ i, IsBenchmark μ γ (B i) piS) :
    IsNash μ B γ (fun _ => piS) ∧
      ∀ π : Fin N → Fin 2 → ℝ, IsNash μ B γ π → π = fun _ => piS := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine ⟨⟨Set.mem_univ_pi.2 (fun i => i.elim0), fun i => i.elim0⟩, fun π _ => ?_⟩
    funext i; exact i.elim0
  have hs : piS ∈ stdSimplex ℝ (Fin 2) := (hS ⟨0, hN⟩).1
  have hmin : ∀ i, IsMinOn (S μ γ (B i)) (stdSimplex ℝ (Fin 2)) piS := fun i => (hS i).2
  have hγ0 : ∀ k, 0 ≤ γ k := fun k => (hγ k).le
  set sb : Fin N → Fin 2 → ℝ := fun _ => piS with hsb
  have hsb' : ∀ j, sb j ∈ stdSimplex ℝ (Fin 2) := fun _ => hs
  have hsbA : sb ∈ Admissible N 2 := Set.mem_univ_pi.2 hsb'
  have hconv := h36.convexOn
  -- `sb` minimizes the potential on `Π^N`
  have hglob : ∀ π' ∈ Admissible N 2, Pot μ B γ sb ≤ Pot μ B γ π' := by
    intro π' hπ'
    have hπ'' : ∀ j, π' j ∈ stdSimplex ℝ (Fin 2) := fun j => (Set.mem_univ_pi.1 hπ') j
    obtain ⟨C, hC⟩ := approx_add μ hM2 γ hγ0 B hB sb π' hsb' hπ''
    have hE := fun i => same_ell_bound μ hM2 γ hγ0 B hB ℓ hℓ piS hs hmin π' hπ'' i
    choose C0 hC0 using hE
    have := cvx_trick (fun t => Pot μ B γ (seg sb π' t)) (seg_convex μ B γ hconv sb π' hsb' hπ'')
      (C + ∑ i, C0 i) (fun t ht => by
        have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2⟩
        have h1 := hC t ht'
        have h2 : -(∑ i, C0 i * t ^ 2) ≤
            ∑ i, (Pot μ B γ (Function.update sb i (seg sb π' t i)) - Pot μ B γ sb) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_le_sum (fun i _ => hC0 i t ht')
        have h3 : (C + ∑ i, C0 i) * t ^ 2 = C * t ^ 2 + ∑ i, C0 i * t ^ 2 := by
          rw [add_mul, Finset.sum_mul]
        simp only [seg_zero]
        linarith)
    simpa [seg_zero, seg_one] using this
  have hNash : IsNash μ B γ sb := by
    refine ⟨hsbA, fun i p hp => ?_⟩
    have hupd := update_mem sb hsb' i p hp
    have hid := pot_ident μ hM2 B hB γ (Function.update sb i p) sb hupd hsb' i
      (fun j hj => Function.update_of_ne hj _ _)
    have := hglob _ (Set.mem_univ_pi.2 hupd)
    linarith
  refine ⟨hNash, fun π hπ => ?_⟩
  have h1 := nash_min μ hM2 γ hγ0 B hB hconv π hπ sb hsbA
  have h2 := hglob π hπ.1
  by_contra hne
  have h3 := h36.2 hπ.1 hsbA hne (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (0:ℝ) < 1 / 2)
    (by norm_num)
  have h4 := hglob _ (h36.1 hπ.1 hsbA (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num))
  simp only [smul_eq_mul] at h3
  linarith
