-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_nonempty_iso_foldr_tensor_tensorPow_of_nonempty_iso_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b74d61d5-5838-57ca-8edf-bc49c88428d8

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_sum_smul_biadditive_mul_eq_sum_smul_biadditive_mul_star
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_nonempty_iso_foldr_tensor_tensorPow_of_nonempty_iso_tensor

set_option autoImplicit false

open scoped Quaternion
p2m_open "QuaternionAlgebra CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

universe u

namespace CasTransport29

section Absorb

variable {G : Type*} [AddCommMonoid G]

def Abs (ε : G) (_h : ε + ε = ε) : Type _ := {g : G // g + ε = g}

variable {ε : G} {hε : ε + ε = ε}

scoped instance : AddCommMonoid (Abs ε hε) where
  add s t := ⟨s.1 + t.1, by rw [add_assoc, t.2]⟩
  zero := ⟨ε, hε⟩
  add_assoc s t r := Subtype.ext (add_assoc _ _ _)
  zero_add s := Subtype.ext (by show ε + s.1 = s.1; rw [add_comm, s.2])
  add_zero s := Subtype.ext s.2
  add_comm s t := Subtype.ext (add_comm _ _)
  nsmul k s := ⟨k • s.1 + ε, by rw [add_assoc, hε]⟩
  nsmul_zero s := Subtype.ext (by show 0 • s.1 + ε = ε; rw [zero_nsmul, zero_add])
  nsmul_succ k s := Subtype.ext (by
    show (k + 1) • s.1 + ε = (k • s.1 + ε) + s.1
    rw [succ_nsmul, add_right_comm])

theorem Abs.val_add (s t : Abs ε hε) : (s + t).1 = s.1 + t.1 := rfl
theorem Abs.val_zero : (0 : Abs ε hε).1 = ε := rfl

theorem Abs.val_sum {ι : Type*} (s : Finset ι) (f : ι → Abs ε hε) :
    (∑ i ∈ s, f i).1 = (∑ i ∈ s, (f i).1) + ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Abs.val_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Abs.val_add, ih, add_assoc]

omit hε in
theorem nsmul_idem_add (h : ε + ε = ε) (k : ℕ) : k • ε + ε = ε := by
  induction k with
  | zero => rw [zero_nsmul, zero_add]
  | succ k ih => rw [succ_nsmul, add_assoc, h, ih]

omit hε in
theorem nsmul_absorb {g : G} (hg : g + ε = g) {k : ℕ} (hk : 0 < k) : k • g + ε = k • g := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [succ_nsmul, add_assoc, hg]

end Absorb

section Transfer

variable {L : Type*} [AddCommGroup L] {G : Type u} [AddCommMonoid G]
  (β : L → L → G)
  (hL : ∀ y y' z : L, β (y + y') z = β y z + β y' z)
  (hR : ∀ y z z' : L, β y (z + z') = β y z + β y z')

include hL hR

theorem eps_idem : β 0 0 + β 0 0 = β 0 0 := by
  have h := hR 0 0 0
  rw [add_zero] at h
  exact h.symm

theorem left_zero (z : L) : β 0 z = β 0 0 := by
  have h1 : β 0 z + β 0 z = β 0 z := by
    have h := hL 0 0 z; rw [add_zero] at h; exact h.symm
  have h2 : β 0 z + β 0 (-z) = β 0 0 := by rw [← hR, add_neg_cancel]
  have h3 : β 0 z + β 0 0 = β 0 z := by
    have h := hR 0 z 0; rw [add_zero] at h; exact h.symm
  calc β 0 z = β 0 z + β 0 0 := h3.symm
    _ = β 0 z + β 0 z + β 0 (-z) := by rw [← h2, add_assoc]
    _ = β 0 0 := by rw [h1, h2]

theorem right_zero (y : L) : β y 0 = β 0 0 := by
  have h1 : β y 0 + β y 0 = β y 0 := by
    have h := hR y 0 0; rw [add_zero] at h; exact h.symm
  have h2 : β y 0 + β (-y) 0 = β 0 0 := by rw [← hL, add_neg_cancel]
  have h3 : β y 0 + β 0 0 = β y 0 := by
    have h := hL y 0 0; rw [add_zero] at h; exact h.symm
  calc β y 0 = β y 0 + β 0 0 := h3.symm
    _ = β y 0 + β y 0 + β (-y) 0 := by rw [← h2, add_assoc]
    _ = β 0 0 := by rw [h1, h2]

theorem absorb (y z : L) : β y z + β 0 0 = β y z := by
  rw [← right_zero β hL hR y, ← hR, add_zero]

theorem transfer {ι : Type*} [Fintype ι] [Nonempty ι] (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (u₁ u₂ v₁ v₂ : ι → L)
    (H : ∀ (T : Type u) [AddCommGroup T] (B : L →+ L →+ T),
      ∑ i, m i • B (u₁ i) (u₂ i) = ∑ i, m i • B (v₁ i) (v₂ i)) :
    ∑ i, m i • β (u₁ i) (u₂ i) = ∑ i, m i • β (v₁ i) (v₂ i) := by
  classical
  set ε : G := β 0 0 with hε_def
  have hε : ε + ε = ε := eps_idem β hL hR
  have habs : ∀ y z, β y z + ε = β y z := absorb β hL hR
  have h0z : ∀ z, β 0 z = ε := left_zero β hL hR

  let βS : L → L → Abs ε hε := fun y z => ⟨β y z, habs y z⟩
  have hSL : ∀ y y' z, βS (y + y') z = βS y z + βS y' z := fun y y' z => Subtype.ext (hL y y' z)
  have hSR : ∀ y z z', βS y (z + z') = βS y z + βS y z' := fun y z z' => Subtype.ext (hR y z z')
  have hS0 : ∀ z, βS 0 z = 0 := fun z => Subtype.ext (h0z z)

  let βu : L → L → AddUnits (Abs ε hε) := fun y z =>
    ⟨βS y z, βS (-y) z, by rw [← hSL, add_neg_cancel, hS0], by rw [← hSL, neg_add_cancel, hS0]⟩
  have hβu : ∀ y z, ((βu y z : AddUnits (Abs ε hε)) : Abs ε hε) = βS y z := fun _ _ => rfl
  let B : L →+ L →+ AddUnits (Abs ε hε) :=
    AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun z => βu y z)
      (by intro z z'; ext; change βS y (z + z') = βS y z + βS y z'; exact hSR y z z'))
      (by intro y y'; ext z; change βS (y + y') z = βS y z + βS y' z; exact hSL y y' z)
  have hB : ∀ y z, ((B y z : AddUnits (Abs ε hε)) : Abs ε hε) = βS y z := fun _ _ => rfl
  have key := congrArg (AddUnits.coeHom (Abs ε hε)) (H (AddUnits (Abs ε hε)) B)
  simp only [map_sum, map_nsmul, AddUnits.coeHom_apply, hB] at key

  have key' := congrArg Subtype.val key
  rw [Abs.val_sum, Abs.val_sum] at key'
  have hval : ∀ (t₁ t₂ : ι → L), (∑ i, (m i • βS (t₁ i) (t₂ i)).1) = (∑ i, m i • β (t₁ i) (t₂ i)) + Fintype.card ι • ε := by
    intro t₁ t₂
    have : ∀ i, (m i • βS (t₁ i) (t₂ i)).1 = m i • β (t₁ i) (t₂ i) + ε := fun i => rfl
    simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
  rw [hval, hval, add_assoc, add_assoc, nsmul_idem_add hε] at key'

  have hsum : ∀ (t₁ t₂ : ι → L), (∑ i, m i • β (t₁ i) (t₂ i)) + ε = ∑ i, m i • β (t₁ i) (t₂ i) := by
    intro t₁ t₂
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), add_right_comm,
      nsmul_absorb (habs _ _) (hm i₀)]
  rw [hsum, hsum] at key'
  exact key'

end Transfer

section Classes

variable {X : Scheme.{u}}

theorem toSkeleton_tensorPow (M : X.Modules) (k : ℕ) :
    toSkeleton (M.tensorPow k) = toSkeleton M ^ k := by
  induction k with
  | zero => rw [Scheme.Modules.tensorPow_zero, pow_zero, Skeleton.one_eq]
  | succ k ih => rw [Scheme.Modules.tensorPow_succ, Skeleton.toSkeleton_tensorObj, ih, pow_succ]

theorem toSkeleton_foldr {n : ℕ} (f : Fin n → X.Modules) :
    toSkeleton (List.foldr (fun M N => M ⊗ N) (𝟙_ X.Modules) (List.ofFn f)) = ∏ i, toSkeleton (f i) := by
  induction n with
  | zero => rw [List.ofFn_zero, List.foldr_nil, Fin.prod_univ_zero, Skeleton.one_eq]
  | succ n ih => rw [List.ofFn_succ, List.foldr_cons, Skeleton.toSkeleton_tensorObj, ih, Fin.prod_univ_succ]

end Classes

end CasTransport29
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_nonempty_iso_foldr_tensor_tensorPow_of_nonempty_iso_tensor.CasTransport29"

open CasTransport29 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {X : Scheme.{u}} (Φ : ↥Λ → ↥Λ → X.Modules)
    (hΦ_left : ∀ y y' z : ↥Λ, Nonempty (Φ (y + y') z ≅ Φ y z ⊗ Φ y' z))
    (hΦ_right : ∀ y z z' : ↥Λ, Nonempty (Φ y (z + z') ≅ Φ y z ⊗ Φ y z')) :
    ∃ (n : ℕ) (w : Fin n → ↥Λ) (m : Fin n → ℕ),
      0 < n ∧ (∀ i, 0 < m i) ∧ (∀ i, (w i : ℍ[ℚ, a, b]) ≠ 0) ∧
      ∀ x : ↥Λ, Nonempty
        (List.foldr (fun M N => M ⊗ N) (𝟙_ X.Modules)
            (List.ofFn fun i : Fin n =>
              (Φ (w i) ⟨(w i : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hΛ.isOrder.mul_mem (w i).2 x.2⟩).tensorPow (m i)) ≅
          List.foldr (fun M N => M ⊗ N) (𝟙_ X.Modules)
            (List.ofFn fun i : Fin n =>
              (Φ ⟨(w i : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]), hΛ.isOrder.mul_mem (w i).2 (star x).2⟩ (w i)).tensorPow (m i))) := by
  classical
  obtain ⟨n, w, m, hn, hm, hw, H⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_sum_smul_biadditive_mul_eq_sum_smul_biadditive_mul_star.{u + 1}
      hqq' hB Λ hΛ μ hμ star hstar
  refine ⟨n, w, m, hn, hm, hw, fun x => ?_⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩

  let β : ↥Λ → ↥Λ → Additive (Skeleton X.Modules) := fun y z => Additive.ofMul (toSkeleton (Φ y z))
  have hL : ∀ y y' z, β (y + y') z = β y z + β y' z := by
    intro y y' z
    obtain ⟨e⟩ := hΦ_left y y' z
    change Additive.ofMul (toSkeleton (Φ (y + y') z)) = Additive.ofMul (toSkeleton (Φ y z) * toSkeleton (Φ y' z))
    rw [← Skeleton.toSkeleton_tensorObj, congr_toSkeleton_of_iso e]
  have hR : ∀ y z z', β y (z + z') = β y z + β y z' := by
    intro y z z'
    obtain ⟨e⟩ := hΦ_right y z z'
    change Additive.ofMul (toSkeleton (Φ y (z + z'))) = Additive.ofMul (toSkeleton (Φ y z) * toSkeleton (Φ y z'))
    rw [← Skeleton.toSkeleton_tensorObj, congr_toSkeleton_of_iso e]
  have key := transfer β hL hR m hm
    (fun i => w i) (fun i => ⟨(w i : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hΛ.isOrder.mul_mem (w i).2 x.2⟩)
    (fun i => ⟨(w i : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]), hΛ.isOrder.mul_mem (w i).2 (star x).2⟩) (fun i => w i)
    (fun T _ B => H T B x)
  have key' := congrArg Additive.toMul key
  simp only [toMul_sum, toMul_nsmul, β, toMul_ofMul] at key'
  refine (toSkeleton_eq_toSkeleton_iff).mp ?_
  rw [toSkeleton_foldr, toSkeleton_foldr]
  simp only [toSkeleton_tensorPow]
  exact key'

end S_QuaternionAlgebra_IsMaximalOrder_exists_nonempty_iso_foldr_tensor_tensorPow_of_nonempty_iso_tensor
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_nonempty_iso_foldr_tensor_tensorPow_of_nonempty_iso_tensor (solution)
