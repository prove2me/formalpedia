-- Prove2me | solution 1 for WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/df6df840-7ae3-534f-bf99-a57efcadd7a4

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom

set_option autoImplicit false

open WeierstrassCurve IsLocalRing

namespace VeluIntegralModel

section Velu
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)

theorem map_veluT (x y : R) : φ (W.veluT x y) = (W.map φ).veluT (φ x) (φ y) := by
  simp [WeierstrassCurve.veluT, WeierstrassCurve.veluGx, WeierstrassCurve.veluGy, map_ofNat]

theorem map_veluW (x y : R) : φ (W.veluW x y) = (W.map φ).veluW (φ x) (φ y) := by
  simp [WeierstrassCurve.veluW, WeierstrassCurve.veluU, WeierstrassCurve.veluT,
    WeierstrassCurve.veluGx, WeierstrassCurve.veluGy, map_ofNat]

variable [DecidableEq S]

theorem map_veluTSum (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    φ (W.veluTSum T) = (W.map φ).veluTSum (T.image (Prod.map φ φ)) := by
  rw [WeierstrassCurve.veluTSum, WeierstrassCurve.veluTSum, Finset.sum_image hφ, map_sum]
  exact Finset.sum_congr rfl fun P _ => map_veluT φ W P.1 P.2

theorem map_veluWSum (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    φ (W.veluWSum T) = (W.map φ).veluWSum (T.image (Prod.map φ φ)) := by
  rw [WeierstrassCurve.veluWSum, WeierstrassCurve.veluWSum, Finset.sum_image hφ, map_sum]
  exact Finset.sum_congr rfl fun P _ => map_veluW φ W P.1 P.2

theorem veluQuotient_map (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    (W.veluQuotient T).map φ = (W.map φ).veluQuotient (T.image (Prod.map φ φ)) := by
  ext
  · rfl
  · rfl
  · rfl
  · show φ (W.a₄ - 5 * W.veluTSum T) = _
    rw [WeierstrassCurve.veluQuotient_a₄, map_sub, map_mul, map_ofNat, map_veluTSum φ W T hφ]
    rfl
  · show φ (W.a₆ - W.b₂ * W.veluTSum T - 7 * W.veluWSum T) = _
    rw [WeierstrassCurve.veluQuotient_a₆, map_sub, map_sub, map_mul, map_mul, map_ofNat,
      map_veluTSum φ W T hφ, map_veluWSum φ W T hφ, ← WeierstrassCurve.map_b₂]
    rfl

end Velu

theorem eq_of_coordsOrZero_eq {F : Type*} [Field F] {V : WeierstrassCurve F}
    {P Q : V.toAffine.Point} (hP : P ≠ 0) (hQ : Q ≠ 0) (h : P.coordsOrZero = Q.coordsOrZero) : P = Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd rfl hP
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hQ
  simp only [Affine.Point.coordsOrZero_some, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem nsmul_injOn_of_lt {G : Type*} [AddGroup G] (g : G) {m₁ m₂ : ℕ}
    (h₁ : m₁ < addOrderOf g) (h₂ : m₂ < addOrderOf g) (h : m₁ • g = m₂ • g) : m₁ = m₂ := by
  wlog hle : m₁ ≤ m₂ generalizing m₁ m₂
  · exact (this h₂ h₁ h.symm (le_of_lt (not_le.mp hle))).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hd : d • g = 0 := by
    rw [add_nsmul] at h
    exact (add_eq_left.mp h.symm)
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hd
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · rfl
  · exact absurd (Nat.le_of_dvd hdpos hdvd) (by omega)

section Reduce
variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve A}
variable [DecidableEq L] [DecidableEq (ResidueField A)] (hΔ : (W.map (residue A)).Δ ≠ 0)

theorem reduceHom_injOn {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {P Q : (W.map A.subtype).toAffine.Point} (hP : N • P = 0) (hQ : N • Q = 0)
    (h : reduceHom hΔ P = reduceHom hΔ Q) : P = Q := by
  have h1 : N • (P - Q) = 0 := by rw [nsmul_sub, hP, hQ, sub_zero]
  have h2 : reducePoint hΔ (P - Q) = 0 := by
    show reduceHom hΔ (P - Q) = 0
    rw [map_sub, h, sub_self]
  have key : P - Q = 0 := by
    generalize hR : P - Q = R at h1 h2
    cases R with
    | zero => rfl
    | some x y hxy =>
      exfalso
      have hx : x ∈ A := X_mem_of_nsmul_eq_zero' W hN hxy h1
      rw [reducePoint_some_of_mem hΔ hxy hx] at h2
      exact Affine.Point.some_ne_zero _ h2
  exact sub_eq_zero.mp key

theorem addOrderOf_reduceHom {N : ℕ} (hN : (N : ResidueField A) ≠ 0)
    {P : (W.map A.subtype).toAffine.Point} (hP : addOrderOf P = N) : addOrderOf (reduceHom hΔ P) = N := by
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [← map_nsmul, ← hP, addOrderOf_nsmul_eq_zero, map_zero]
  · rw [← hP]
    apply addOrderOf_dvd_of_nsmul_eq_zero
    refine reduceHom_injOn hΔ hN ?_ (smul_zero _) ?_
    · rw [smul_comm, ← hP, addOrderOf_nsmul_eq_zero, smul_zero]
    · rw [map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]

end Reduce

end VeluIntegralModel

theorem solution
    {L : Type*} [Field L] [DecidableEq L] (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q : (W.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = ℓ) {n : ℕ} (hn : n < ℓ) :
    ∃ V : WeierstrassCurve A,
      V.map A.subtype = (W.map A.subtype).veluQuotient ((W.map A.subtype).oddOrderSummingSet Q n) ∧
      V.map (residue A) =
        (W.map (residue A)).veluQuotient ((W.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) n) := by
  classical
  have hQℓ : ℓ • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
  have hQ₀ord : addOrderOf (reduceHom hΔ Q) = ℓ := VeluIntegralModel.addOrderOf_reduceHom hΔ hℓ hQ

  have hmem : ∀ m : ℕ, 1 ≤ m → m ≤ n → ∃ (x y : L) (h : (W.map A.subtype).toAffine.Nonsingular x y)
      (_ : x ∈ A), m • Q = .some x y h := by
    intro m hm1 hmn
    have hne : m • Q ≠ 0 := by
      intro h0
      have := addOrderOf_dvd_of_nsmul_eq_zero h0
      rw [hQ] at this
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    rcases hP : m • Q with _ | ⟨x, y, h⟩
    · exact absurd hP hne
    · refine ⟨x, y, h, ?_, rfl⟩
      refine WeierstrassCurve.X_mem_of_nsmul_eq_zero' W hℓ h ?_
      rw [← hP, smul_smul, mul_comm, ← smul_smul, hQℓ, smul_zero]

  let sec : L → A := fun z => if hz : z ∈ A then ⟨z, hz⟩ else 0
  have hsec : ∀ {z : L} (hz : z ∈ A), sec z = ⟨z, hz⟩ := fun hz => dif_pos hz
  let TA : Finset (A × A) := (Finset.Icc 1 n).image fun m => Prod.map sec sec (m • Q).coordsOrZero

  have hTsub : TA.image (Prod.map A.subtype A.subtype) = (W.map A.subtype).oddOrderSummingSet Q n := by
    simp only [TA, WeierstrassCurve.oddOrderSummingSet, Finset.image_image]
    refine Finset.image_congr fun m hm => ?_
    rw [Finset.mem_coe, Finset.mem_Icc] at hm
    obtain ⟨x, y, h, hx, hP⟩ := hmem m hm.1 hm.2
    have hy : y ∈ A := WeierstrassCurve.Affine.Y_mem_of_X_mem W h.1 hx
    show Prod.map A.subtype A.subtype (Prod.map sec sec (m • Q).coordsOrZero) = (m • Q).coordsOrZero
    rw [hP, Affine.Point.coordsOrZero_some, Prod.map_apply, Prod.map_apply, hsec hx, hsec hy]
    rfl

  have hr : ∀ {m : ℕ} {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A),
      m • Q = .some x y h →
      Prod.map (residue A) (residue A) (Prod.map sec sec (m • Q).coordsOrZero)
        = (m • reduceHom hΔ Q).coordsOrZero := by
    intro m x y h hx hP
    have hy : y ∈ A := WeierstrassCurve.Affine.Y_mem_of_X_mem W h.1 hx
    rw [← map_nsmul, hP, Affine.Point.coordsOrZero_some, Prod.map_apply, Prod.map_apply, hsec hx, hsec hy]
    show _ = (WeierstrassCurve.reducePoint hΔ (Affine.Point.some x y h)).coordsOrZero
    rw [WeierstrassCurve.reducePoint_some_of_mem hΔ h hx, Affine.Point.coordsOrZero_some]

  have hTres : TA.image (Prod.map (residue A) (residue A)) =
      (W.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) n := by
    simp only [TA, WeierstrassCurve.oddOrderSummingSet, Finset.image_image]
    refine Finset.image_congr fun m hm => ?_
    rw [Finset.mem_coe, Finset.mem_Icc] at hm
    obtain ⟨x, y, h, hx, hP⟩ := hmem m hm.1 hm.2
    exact hr h hx hP

  have hTinj : Set.InjOn (Prod.map (residue A) (residue A)) ↑TA := by
    intro t₁ ht₁ t₂ ht₂ heq
    rw [Finset.mem_coe] at ht₁ ht₂
    simp only [TA, Finset.mem_image, Finset.mem_Icc] at ht₁ ht₂
    obtain ⟨m₁, hm₁, rfl⟩ := ht₁
    obtain ⟨m₂, hm₂, rfl⟩ := ht₂
    obtain ⟨x₁, y₁, h₁, hx₁, hP₁⟩ := hmem m₁ hm₁.1 hm₁.2
    obtain ⟨x₂, y₂, h₂, hx₂, hP₂⟩ := hmem m₂ hm₂.1 hm₂.2
    rw [hr h₁ hx₁ hP₁, hr h₂ hx₂ hP₂] at heq
    have hne : ∀ {m : ℕ}, 1 ≤ m → m ≤ n → m • reduceHom hΔ Q ≠ 0 := by
      intro m hm1 hmn h0
      have := addOrderOf_dvd_of_nsmul_eq_zero h0
      rw [hQ₀ord] at this
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    have hmm : m₁ = m₂ :=
      VeluIntegralModel.nsmul_injOn_of_lt (reduceHom hΔ Q) (by rw [hQ₀ord]; omega) (by rw [hQ₀ord]; omega)
        (VeluIntegralModel.eq_of_coordsOrZero_eq (hne hm₁.1 hm₁.2) (hne hm₂.1 hm₂.2) heq)
    rw [hmm]

  refine ⟨W.veluQuotient TA, ?_, ?_⟩
  · rw [← hTsub]
    exact VeluIntegralModel.veluQuotient_map A.subtype W TA
      ((Function.Injective.prodMap A.subtype_injective A.subtype_injective).injOn)
  · rw [VeluIntegralModel.veluQuotient_map (residue A) W TA hTinj, hTres]

end S_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom
end P2MW
export P2MW.S_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom (solution)
