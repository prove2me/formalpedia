-- Prove2me | solution 1 for WeierstrassCurve.stepCurve_stepSubgroup_two_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0aa7d8bd-4048-5e50-81ff-c2af03d2890c

import Mathlib
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_stepCurve_stepSubgroup_two_eq

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MKcStepTwo

variable {L : Type*} [Field L] [DecidableEq L]

theorem mem_zmultiples_of_nsmul_eq_zero {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    [IsAddCyclic H] [Finite H] {ℓ : ℕ} (hℓ : ℓ.Prime) {Q : G} (hQH : Q ∈ H) (hQ : addOrderOf Q = ℓ)
    {P : G} (hP : P ∈ H) (hP0 : ℓ • P = 0) : P ∈ AddSubgroup.zmultiples Q := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  let Q' : H := ⟨Q, hQH⟩
  have hQ' : addOrderOf Q' = ℓ :=
    (addOrderOf_injective H.subtype Subtype.coe_injective Q').symm.trans hQ
  set T : Finset H := Finset.univ.filter fun a : H => ℓ • a = 0 with hT
  have hTle : T.card ≤ ℓ := IsAddCyclic.card_nsmul_eq_zero_le hℓ.pos
  set Z : Finset H := (AddSubgroup.zmultiples Q' : Set H).toFinset with hZ
  have hZcard : Z.card = ℓ := by
    rw [hZ, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact (Nat.card_zmultiples Q').trans hQ'
  have hZT : Z ⊆ T := by
    intro a ha
    rw [hZ, Set.mem_toFinset] at ha
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 ha
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [smul_comm, addOrderOf_dvd_iff_nsmul_eq_zero.1 (hQ' ▸ dvd_rfl), smul_zero]
  have hZeqT : Z = T := Finset.eq_of_subset_of_card_le hZT (by rw [hZcard]; exact hTle)
  have hPT : (⟨P, hP⟩ : H) ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact hP0)
  rw [← hZeqT, hZ, Set.mem_toFinset] at hPT
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hPT
  exact AddSubgroup.mem_zmultiples_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

section Setup

variable (E : WeierstrassCurve L) (h2 : (2 : L) ≠ 0)
  (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H]
  {x₀ y₀ : L} (hns : E.toAffine.Nonsingular x₀ y₀) (hQH : (.some x₀ y₀ hns : E.toAffine.Point) ∈ H)
  (hgy : E.veluGy x₀ y₀ = 0)

local notation "Q" => (Affine.Point.some x₀ y₀ hns : E.toAffine.Point)

omit [DecidableEq L] in
include hgy in
theorem negY_eq : E.toAffine.negY x₀ y₀ = y₀ := by
  rw [Affine.negY]
  rw [veluGy] at hgy
  linear_combination hgy

include hgy in
theorem two_smul_Q : (2 : ℕ) • Q = 0 := by
  rw [two_nsmul, ← eq_neg_iff_add_eq_zero, Affine.Point.neg_some]
  congr 1
  exact (negY_eq E hgy).symm

include hgy in
theorem addOrderOf_Q : addOrderOf Q = 2 := by
  refine addOrderOf_eq_prime_iff.2 ⟨two_smul_Q E hns hgy, Affine.Point.some_ne_zero hns⟩

include hgy in

theorem mem_zmultiples_Q_iff (P : E.toAffine.Point) :
    P ∈ AddSubgroup.zmultiples Q ↔ P = 0 ∨ P = Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hP
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hP
    have hk : (k % 2) • Q = k • Q := by
      have := mod_addOrderOf_zsmul Q k
      rwa [addOrderOf_Q E hns hgy, Nat.cast_ofNat] at this
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [← hk, h, zero_smul]
    · right; rw [← hk, h, one_smul]
  · rintro (rfl | rfl)
    · exact AddSubgroup.zero_mem _
    · exact AddSubgroup.mem_zmultiples _

include hgy in

theorem some_mem_zmultiples_iff {x y : L} (h : E.toAffine.Nonsingular x y) :
    (Affine.Point.some x y h) ∈ AddSubgroup.zmultiples Q ↔ x = x₀ := by
  rw [mem_zmultiples_Q_iff E hns hgy]
  constructor
  · rintro (h0 | hQ)
    · exact absurd h0 (Affine.Point.some_ne_zero h)
    · exact (Affine.Point.some.inj hQ).1
  · intro hx
    subst hx
    right
    rcases Affine.Y_eq_of_X_eq h.1 hns.1 rfl with hy | hy
    · subst hy; rfl
    · rw [negY_eq E hgy] at hy; subst hy; rfl

include hQH hgy in
theorem kernelXSet_eq : E.kernelXSet H 2 = {x₀} := by
  ext x
  simp only [kernelXSet, Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨P, ⟨hP, hne, hP0⟩, rfl⟩
    have hmem := mem_zmultiples_of_nsmul_eq_zero H Nat.prime_two hQH (addOrderOf_Q E hns hgy) hP hP0
    rcases (mem_zmultiples_Q_iff E hns hgy P).1 hmem with rfl | rfl
    · exact absurd rfl hne
    · rfl
  · intro hx
    rw [hx]
    exact ⟨Q, ⟨hQH, Affine.Point.some_ne_zero hns, two_smul_Q E hns hgy⟩, rfl⟩

omit [DecidableEq L] in
include h2 hgy in
theorem twoTorsionY_eq : E.twoTorsionY x₀ = y₀ := by
  rw [twoTorsionY]
  rw [veluGy] at hgy
  field_simp
  linear_combination hgy

omit [DecidableEq L] in
theorem absSum_singleton (a : L) (g : L → L) : absSum {a} g = g a := by
  rw [absSum_of_finite (Set.finite_singleton a), Set.Finite.toFinset_singleton, Finset.sum_singleton]

include h2 hQH hgy in
theorem stepCurve_eq : E.stepCurve H 2 = E.veluQuotient2 x₀ y₀ := by
  rw [stepCurve_two, kernelXSet_eq E H hns hQH hgy]
  have hG : E.xVeluG x₀ = E.veluGx x₀ y₀ := by rw [xVeluG, twoTorsionY_eq E h2 hgy]
  ext
  · rfl
  · rfl
  · rfl
  · rw [twoVeluCurve_a₄, veluQuotient2_a₄, absSum_singleton, hG]
  · rw [twoVeluCurve_a₆, veluQuotient2_a₆, absSum_singleton, absSum_singleton, hG]

include h2 hQH hgy in
theorem stepX_eq (x : L) : E.stepX H 2 x = E.velu2X x₀ y₀ x := by
  rw [stepX_two, kernelXSet_eq E H hns hQH hgy, twoVeluX, absSum_singleton, xVeluG,
    twoTorsionY_eq E h2 hgy, velu2X]

include hQH hgy in
theorem coKernelXSet_eq :
    E.coKernelXSet H 2 = {x | ∃ (x' y' : L) (h : E.toAffine.Nonsingular x' y'),
      Affine.Point.some x' y' h ∈ H ∧ x' ≠ x₀ ∧ x' = x} := by
  ext x
  simp only [coKernelXSet, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨P, ⟨hP, hP0⟩, rfl⟩
    rcases P with _ | ⟨x', y', h⟩
    · exact absurd (smul_zero _) hP0
    refine ⟨x', y', h, hP, fun hx => hP0 ?_, rfl⟩
    have hmem := (some_mem_zmultiples_iff E hns hgy h).2 hx
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
    rw [← hk, smul_comm, two_smul_Q E hns hgy, smul_zero]
  · rintro ⟨x', y', h, hP, hx, rfl⟩
    refine ⟨.some x' y' h, ⟨hP, fun hP0 => hx ?_⟩, rfl⟩
    have hmem := mem_zmultiples_of_nsmul_eq_zero H Nat.prime_two hQH (addOrderOf_Q E hns hgy) hP hP0
    exact (some_mem_zmultiples_iff E hns hgy h).1 hmem

variable (hΔ : (E.veluQuotient2 x₀ y₀).Δ ≠ 0)
  (φ : E.toAffine.Point →+ (E.veluQuotient2 x₀ y₀).toAffine.Point)
  (hφ : ⇑φ = veluPointMap2 h2 hns.1 hgy hΔ)

include hQH hφ in
theorem subgroupOfX_eq :
    subgroupOfX (E.veluQuotient2 x₀ y₀) (E.velu2X x₀ y₀ '' E.coKernelXSet H 2) = H.map φ := by
  rw [coKernelXSet_eq E H hns hQH hgy, subgroupOfX]
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro P' ⟨hne, ⟨x, ⟨xP, yP, hPns, hP, hxP, rfl⟩, hx⟩⟩
    have hφP : φ (.some xP yP hPns) = .some (E.velu2X x₀ y₀ xP) (E.velu2Y x₀ y₀ xP yP)
        (velu2_map_nonsingular h2 hPns.1 hns.1 hgy hxP hΔ) := by
      rw [hφ, veluPointMap2_some_of_ne _ _ _ _ _ hxP]
    rcases P' with _ | ⟨x', y', hP'⟩
    · exact absurd rfl hne
    change E.velu2X x₀ y₀ xP = x' at hx
    rcases Affine.Y_eq_of_X_eq hP'.1 (velu2_map_nonsingular h2 hPns.1 hns.1 hgy hxP hΔ).1 hx.symm
      with hy | hy
    · have : (Affine.Point.some x' y' hP') = φ (.some xP yP hPns) := by
        rw [hφP]
        cases hx; cases hy; rfl
      rw [this]
      exact AddSubgroup.mem_map_of_mem φ hP
    · have : (Affine.Point.some x' y' hP') = -φ (.some xP yP hPns) := by
        rw [hφP, Affine.Point.neg_some]
        cases hx; cases hy; rfl
      rw [this]
      exact (H.map φ).neg_mem (AddSubgroup.mem_map_of_mem φ hP)
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := AddSubgroup.mem_map.1 hP'
    rcases P with _ | ⟨xP, yP, hPns⟩
    · change φ 0 ∈ _
      rw [map_zero]; exact AddSubgroup.zero_mem _
    by_cases hxP : xP = x₀
    · have : φ (.some xP yP hPns) = 0 := by
        rw [hφ, veluPointMap2_some_of_eq _ _ _ _ _ hxP]; rfl
      rw [this]; exact AddSubgroup.zero_mem _
    · have hφP : φ (.some xP yP hPns) = .some (E.velu2X x₀ y₀ xP) (E.velu2Y x₀ y₀ xP yP)
          (velu2_map_nonsingular h2 hPns.1 hns.1 hgy hxP hΔ) := by
        rw [hφ, veluPointMap2_some_of_ne _ _ _ _ _ hxP]
      refine AddSubgroup.subset_closure ⟨?_, ?_⟩
      · rw [hφP]; exact Affine.Point.some_ne_zero _
      · refine ⟨xP, ⟨xP, yP, hPns, hP, hxP, rfl⟩, ?_⟩
        rw [hφP]; rfl

end Setup

theorem sigma_eq_of_eq {V₁ V₂ : WeierstrassCurve L} (h : V₁ = V₂) {Y₁ Y₂ : Set L} (hY : Y₁ = Y₂) :
    (⟨V₁, subgroupOfX V₁ Y₁⟩ : Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) =
      ⟨V₂, subgroupOfX V₂ Y₂⟩ := by
  subst h hY; rfl

end P2MKcStepTwo

open P2MKcStepTwo in
universe u in
theorem solution
    {L : Type u} [Field L] [DecidableEq L] (E : WeierstrassCurve L) (h2 : (2 : L) ≠ 0)
    (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H]
    {x₀ y₀ : L} (hns : E.toAffine.Nonsingular x₀ y₀) (hQH : (.some x₀ y₀ hns : E.toAffine.Point) ∈ H)
    (hgy : E.veluGy x₀ y₀ = 0) (hΔ : (E.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.veluQuotient2 x₀ y₀).toAffine.Point)
    (hφ : ⇑φ = veluPointMap2 h2 hns.1 hgy hΔ) :
    (⟨E.stepCurve H 2, E.stepSubgroup H 2⟩ : Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) =
      ⟨E.veluQuotient2 x₀ y₀, H.map φ⟩ := by
  rw [← subgroupOfX_eq E h2 H hns hQH hgy hΔ φ hφ, stepSubgroup]
  refine sigma_eq_of_eq (stepCurve_eq E h2 H hns hQH hgy) ?_
  refine Set.image_congr fun x _ => ?_
  exact stepX_eq E h2 H hns hQH hgy x

end S_WeierstrassCurve_stepCurve_stepSubgroup_two_eq
end P2MW
export P2MW.S_WeierstrassCurve_stepCurve_stepSubgroup_two_eq (solution)
