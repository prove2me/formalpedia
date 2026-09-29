-- Prove2me | solution 1 for WeierstrassCurve.stepCurve_stepSubgroup_eq_of_prime_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/06304781-0608-5a77-9714-9eeada4e8176

import Mathlib
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Theorems.Thm_WeierstrassCurve_isOddVeluSet_oddOrderSummingSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MKcStepOdd

variable {L : Type*} [Field L] [DecidableEq L]

omit [DecidableEq L] in

theorem fst_coordsOrZero_neg {W : WeierstrassCurve L} (P : W.toAffine.Point) :
    (-P).coordsOrZero.1 = P.coordsOrZero.1 := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]; rfl

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

theorem nsmul_eq_zero_of_mem_zmultiples {G : Type*} [AddCommGroup G] {ℓ : ℕ} {Q : G}
    (hQ : addOrderOf Q = ℓ) {P : G} (hP : P ∈ AddSubgroup.zmultiples Q) : ℓ • P = 0 := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hP
  rw [smul_comm, addOrderOf_dvd_iff_nsmul_eq_zero.1 (hQ ▸ dvd_rfl), smul_zero]

section Setup

variable (E : WeierstrassCurve L) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
  (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H]
  (Q : E.toAffine.Point) (hQH : Q ∈ H) (hQ : addOrderOf Q = ℓ)

local notation "S" => E.oddOrderSummingSet Q (ℓ / 2)

include hℓ hℓ2 hQ in
theorem isOddVeluSet_S : E.IsOddVeluSet S := by
  refine isOddVeluSet_oddOrderSummingSet hℓ hℓ2 hQ (le_of_eq ?_)
  rcases hℓ.eq_two_or_odd' with h | h
  · exact absurd h hℓ2
  · obtain ⟨m, rfl⟩ := h; omega

include hℓ hQ in

theorem exists_mem_S_of_zsmul (k : ℤ) (hk : (k • Q) ≠ 0) :
    ∃ P ∈ S, P.1 = (k • Q).coordsOrZero.1 := by

  set m : ℕ := (k % ℓ).toNat with hm
  have hmk : (m : ℤ) = k % ℓ := Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hℓ.ne_zero))
  have hmQ : (m : ℤ) • Q = k • Q := by rw [hmk, ← hQ, mod_addOrderOf_zsmul]
  rw [natCast_zsmul] at hmQ
  have hmlt : m < ℓ := by
    have := Int.emod_lt_of_pos k (by exact_mod_cast hℓ.pos : (0 : ℤ) < ℓ)
    omega
  have hm0 : m ≠ 0 := by rintro h; rw [h, zero_smul] at hmQ; exact hk hmQ.symm
  by_cases hle : m ≤ ℓ / 2
  · refine ⟨(m • Q).coordsOrZero, ?_, by rw [hmQ]⟩
    exact (mem_oddOrderSummingSet _).2 ⟨m, Nat.one_le_iff_ne_zero.2 hm0, hle, rfl⟩
  · refine ⟨((ℓ - m) • Q).coordsOrZero, ?_, ?_⟩
    · refine (mem_oddOrderSummingSet _).2 ⟨ℓ - m, ?_, ?_, rfl⟩ <;> omega
    · have : (ℓ - m) • Q = -(m • Q) := by
        rw [eq_neg_iff_add_eq_zero, ← add_smul, Nat.sub_add_cancel hmlt.le]
        exact addOrderOf_dvd_iff_nsmul_eq_zero.1 (hQ ▸ dvd_rfl)
      rw [this, fst_coordsOrZero_neg, hmQ]

include hℓ hQH hQ in
theorem kernelXSet_eq : E.kernelXSet H ℓ = ((S).image Prod.fst : Finset L) := by
  ext x
  simp only [kernelXSet, Set.mem_image, Set.mem_setOf_eq, Finset.coe_image, Finset.mem_coe]
  constructor
  · rintro ⟨P, ⟨hP, hne, hP0⟩, rfl⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1
      (mem_zmultiples_of_nsmul_eq_zero H hℓ hQH hQ hP hP0)
    obtain ⟨P', hP', h⟩ := exists_mem_S_of_zsmul E hℓ Q hQ k hne
    exact ⟨P', hP', h⟩
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨k, hk1, hk2, rfl⟩ := (mem_oddOrderSummingSet _).1 hP
    refine ⟨k • Q, ⟨?_, ?_, ?_⟩, rfl⟩
    · exact H.nsmul_mem hQH k
    · refine nsmul_ne_zero_of_lt_addOrderOf (by omega) ?_
      rw [hQ]
      have := Nat.div_lt_self hℓ.pos one_lt_two
      omega
    · exact nsmul_eq_zero_of_mem_zmultiples hQ (AddSubgroup.mem_zmultiples_iff.2 ⟨k, natCast_zsmul Q k⟩)

include hℓ hℓ2 hQH hQ in

theorem absSum_kernelXSet (g : L → L) :
    absSum (E.kernelXSet H ℓ) g = ∑ P ∈ S, g P.1 := by
  rw [kernelXSet_eq E hℓ H Q hQH hQ, absSum_of_finite (Finset.finite_toSet _),
    Finset.finite_toSet_toFinset, Finset.sum_image]
  intro P hP P' hP' h
  exact (isOddVeluSet_S E hℓ hℓ2 Q hQ).x_injOn P hP P' hP' h

include hℓ hℓ2 hQH hQ in
theorem stepCurve_eq : E.stepCurve H ℓ = E.veluQuotient S := by
  have hS := isOddVeluSet_S E hℓ hℓ2 Q hQ
  rw [stepCurve_of_ne_two _ _ hℓ2]
  ext
  · rfl
  · rfl
  · rfl
  · rw [xVeluCurve_a₄, veluQuotient_a₄, absSum_kernelXSet E hℓ hℓ2 H Q hQH hQ, veluTSum]
    congr 2
    exact Finset.sum_congr rfl fun P _ => E.xVeluT_eq_veluT P.1 P.2
  · rw [xVeluCurve_a₆, veluQuotient_a₆, absSum_kernelXSet E hℓ hℓ2 H Q hQH hQ,
      absSum_kernelXSet E hℓ hℓ2 H Q hQH hQ, veluTSum, veluWSum]
    congr 2
    · congr 1
      exact Finset.sum_congr rfl fun P _ => E.xVeluT_eq_veluT P.1 P.2
    · exact Finset.sum_congr rfl fun P hP => E.xVeluW_eq_veluW (hS.equation P hP)

include hℓ hℓ2 hQH hQ in
theorem stepX_eq (x : L) : E.stepX H ℓ x = E.veluX S x := by
  have hS := isOddVeluSet_S E hℓ hℓ2 Q hQ
  rw [stepX_of_ne_two _ _ hℓ2, xVeluX, veluX, absSum_kernelXSet E hℓ hℓ2 H Q hQH hQ]
  congr 1
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [E.xVeluT_eq_veluT P.1 P.2, E.xVeluU_eq_veluU (hS.equation P hP)]

include hℓ hQH hQ in
theorem coKernelXSet_eq :
    E.coKernelXSet H ℓ = {x | ∃ P ∈ H, P ∉ AddSubgroup.zmultiples Q ∧ P.coordsOrZero.1 = x} := by
  ext x
  simp only [coKernelXSet, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨P, ⟨hP, hP0⟩, rfl⟩
    exact ⟨P, hP, fun h => hP0 (nsmul_eq_zero_of_mem_zmultiples hQ h), rfl⟩
  · rintro ⟨P, hP, hPQ, rfl⟩
    exact ⟨P, ⟨hP, fun h => hPQ (mem_zmultiples_of_nsmul_eq_zero H hℓ hQH hQ hP h)⟩, rfl⟩

variable (φ : E.toAffine.Point →+ (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2))).toAffine.Point)
  (hφker : φ.ker = AddSubgroup.zmultiples Q)
  (hφ : ∀ (x y : L) (h : E.toAffine.Nonsingular x y),
    (.some x y h : E.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
      ∃ h', φ (.some x y h) = .some (E.veluX (E.oddOrderSummingSet Q (ℓ / 2)) x)
        (E.veluY (E.oddOrderSummingSet Q (ℓ / 2)) x y) h')

include hℓ hQH hQ hφker hφ in
theorem subgroupOfX_eq :
    subgroupOfX (E.veluQuotient S) (E.veluX S '' E.coKernelXSet H ℓ) = H.map φ := by
  rw [coKernelXSet_eq E hℓ H Q hQH hQ, subgroupOfX]
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro P' ⟨hne, ⟨x, ⟨P, hP, hPQ, rfl⟩, hx⟩⟩
    rcases P with _ | ⟨xP, yP, hPns⟩
    · exact absurd (AddSubgroup.zero_mem _) hPQ
    obtain ⟨h', hφP⟩ := hφ xP yP hPns hPQ
    rcases P' with _ | ⟨x', y', hP'⟩
    · exact absurd rfl hne
    change E.veluX S xP = x' at hx

    rcases Affine.Y_eq_of_X_eq hP'.1 h'.1 hx.symm with hy | hy
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
    by_cases hPQ : P ∈ AddSubgroup.zmultiples Q
    · have : φ P = 0 := by rw [← AddMonoidHom.mem_ker, hφker]; exact hPQ
      rw [this]; exact AddSubgroup.zero_mem _
    · refine AddSubgroup.subset_closure ⟨?_, ?_⟩
      · intro h0
        apply hPQ
        rw [← hφker, AddMonoidHom.mem_ker]
        exact h0
      · rcases P with _ | ⟨xP, yP, hPns⟩
        · exact absurd (AddSubgroup.zero_mem _) hPQ
        obtain ⟨h', hφP⟩ := hφ xP yP hPns hPQ
        refine ⟨xP, ⟨.some xP yP hPns, hP, hPQ, rfl⟩, ?_⟩
        rw [hφP]; rfl

end Setup

theorem sigma_eq_of_eq {V₁ V₂ : WeierstrassCurve L} (h : V₁ = V₂) {Y₁ Y₂ : Set L} (hY : Y₁ = Y₂) :
    (⟨V₁, subgroupOfX V₁ Y₁⟩ : Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) =
      ⟨V₂, subgroupOfX V₂ Y₂⟩ := by
  subst h hY; rfl

end P2MKcStepOdd

open P2MKcStepOdd in
universe u in
theorem solution
    {L : Type u} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H]
    (Q : E.toAffine.Point) (hQH : Q ∈ H) (hQ : addOrderOf Q = ℓ)
    (φ : E.toAffine.Point →+ (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2))).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ (x y : L) (h : E.toAffine.Nonsingular x y),
      (.some x y h : E.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (E.veluX (E.oddOrderSummingSet Q (ℓ / 2)) x)
          (E.veluY (E.oddOrderSummingSet Q (ℓ / 2)) x y) h') :
    (⟨E.stepCurve H ℓ, E.stepSubgroup H ℓ⟩ : Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) =
      ⟨E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)), H.map φ⟩ := by
  rw [← subgroupOfX_eq E hℓ H Q hQH hQ φ hφker hφ, stepSubgroup]
  refine sigma_eq_of_eq (stepCurve_eq E hℓ hℓ2 H Q hQH hQ) ?_
  refine Set.image_congr fun x _ => ?_
  exact stepX_eq E hℓ hℓ2 H Q hQH hQ x

end S_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two
end P2MW
export P2MW.S_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two (solution)
