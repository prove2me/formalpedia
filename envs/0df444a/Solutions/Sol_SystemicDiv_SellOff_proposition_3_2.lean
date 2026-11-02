-- Prove2me | solution 1 for SystemicDiv.SellOff.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:28:31.105905+00:00
-- url     : https://prove2.me/submissions/c974c13e-51e2-4bc7-ae0a-4dd58cea342a

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotential
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

open SystemicDiv.SellOff SysDivAn

theorem solution {N K : ℕ} (hK : 0 < K) (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (γ : Fin K → ℝ) (hγ : ∀ k, 0 < γ k) :
    MondererShapley.ClosedPath.IsPotential
        (Y := fun _ : Fin N => ↥(stdSimplex ℝ (Fin K)))
        (fun i y => EC μ B γ (fun j => (y j : Fin K → ℝ)) i)
        (fun y => Pot μ B γ (fun j => (y j : Fin K → ℝ))) ∧
      (μ ≪ volume → ∃ π : Fin N → Fin K → ℝ, IsNash μ B γ π) := by
  refine ⟨?_, fun _ => ?_⟩
  · intro i y x z
    apply pot_ident μ hM2 B hB γ
    · intro j; exact (Function.update y i x j).2
    · intro j; exact (Function.update y i z j).2
    · intro j hj; simp [Function.update_of_ne hj]
  · have hc : IsCompact (Admissible N K) :=
      isCompact_univ_pi (fun _ => isCompact_stdSimplex ℝ (Fin K))
    have hne : (Admissible N K).Nonempty :=
      ⟨fun _ => Pi.single ⟨0, hK⟩ 1, Set.mem_univ_pi.2 (fun _ => single_mem_stdSimplex ℝ _)⟩
    obtain ⟨π, hπ, hmin⟩ := hc.exists_isMinOn hne (Pot_contOn μ hM2 B hB γ)
    have hmem : ∀ j, π j ∈ stdSimplex ℝ (Fin K) := fun j => (Set.mem_univ_pi.1 hπ) j
    refine ⟨π, hπ, fun i p hp => ?_⟩
    have hmem' : ∀ j, Function.update π i p j ∈ stdSimplex ℝ (Fin K) := by
      intro j
      by_cases hj : j = i
      · subst hj; simpa using hp
      · rw [Function.update_of_ne hj]; exact hmem j
    have hid := pot_ident μ hM2 B hB γ (Function.update π i p) π hmem' hmem i
      (fun j hj => Function.update_of_ne hj _ _)
    have hle : Pot μ B γ π ≤ Pot μ B γ (Function.update π i p) :=
      hmin (Set.mem_univ_pi.2 hmem')
    linarith
