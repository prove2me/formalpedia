-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mem_iff_forall_mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4e8e9df5-03ab-5e2e-95e8-9ecbbc2392c7

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_sum_mul_eq_one_of_forall_mul_mem
import Theorems.Thm_AddSubgroup_exists_forall_mem_iff_single_sub_mul_mem_of_sum_mul_eq_one
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mulVec_mem_iff_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mem_iff_forall_mulVec_mem
p2m_attr_erase "simp" "QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Quaternion
open QuaternionAlgebra

namespace P2mFreeness

section Denominators

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem exists_natCast_smul_mem_of_mem_span (S : Submodule ℤ V) {x : V}
    (hx : x ∈ Submodule.span ℚ (S : Set V)) : ∃ N : ℕ, N ≠ 0 ∧ ((N : ℤ) • x) ∈ S := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [Nat.cast_one, one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact S.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, hN₁, h₁⟩ := hx
    obtain ⟨N₂, hN₂, h₂⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, ?_⟩
    rw [smul_add, Nat.cast_mul]
    refine S.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact S.smul_mem _ h₁
    · rw [mul_smul]; exact S.smul_mem _ h₂
  | smul a x _ hx =>
    obtain ⟨N, hN, h⟩ := hx
    refine ⟨N * a.den, mul_ne_zero hN a.den_ne_zero, ?_⟩
    have : (((N * a.den : ℕ) : ℤ)) • (a • x) = a.num • ((N : ℤ) • x) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ a.num, ← Int.cast_smul_eq_zsmul ℚ (N : ℤ),
        smul_smul, smul_smul]
      congr 1
      push_cast
      rw [mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [this]
    exact S.smul_mem _ h

end Denominators

section Mat

variable {A : Type*} [Ring A]

theorem fin_two_eq {a b c d a' b' c' d' : A} (h₁ : a = a') (h₂ : b = b') (h₃ : c = c') (h₄ : d = d') :
    !![a, b; c, d] = !![a', b'; c', d'] := by
  subst h₁ h₂ h₃ h₄; rfl

theorem upper_mulVec (u : A) (y : Fin 2 → A) :
    (!![1, u; 0, 1] : Matrix (Fin 2) (Fin 2) A).mulVec y = ![y 0 + u * y 1, y 1] := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i <;> simp

theorem upper_mul_upper_neg (u : A) :
    (!![1, u; 0, 1] : Matrix (Fin 2) (Fin 2) A) * !![1, -u; 0, 1] = 1 := by
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  exact fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

theorem upper_neg_mul_upper (u : A) :
    (!![1, -u; 0, 1] : Matrix (Fin 2) (Fin 2) A) * !![1, u; 0, 1] = 1 := by
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  exact fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

theorem diag_mulVec (a b : A) (y : Fin 2 → A) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) A).mulVec y = ![a * y 0, b * y 1] := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i <;> simp

theorem diag_mul_diag (a b a' b' : A) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) A) * !![a', 0; 0, b'] = !![a * a', 0; 0, b * b'] := by
  rw [Matrix.mul_fin_two]
  exact fin_two_eq (by noncomm_ring) (by noncomm_ring) (by noncomm_ring) (by noncomm_ring)

end Mat

end P2mFreeness

open P2mFreeness in
theorem solution
    {c d : ℚ} (q : ℕ) [Fact q.Prime] (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    (M : Submodule ℤ (Fin 2 → ℍ[ℚ, c, d])) (hfg : M.FG)
    (hspan : Submodule.span ℚ (M : Set (Fin 2 → ℍ[ℚ, c, d])) = ⊤)
    (hM : ∀ m ∈ M, ∀ o ∈ O, (fun i => m i * o) ∈ M) :
    ∃ γ γ' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], γ * γ' = 1 ∧ γ' * γ = 1 ∧
      ∀ x : Fin 2 → ℍ[ℚ, c, d], x ∈ M ↔ ∀ i, (γ'.mulVec x) i ∈ O := by
  classical
  have hOo : IsOrder O := hO.isOrder

  let π₀ : (Fin 2 → ℍ[ℚ, c, d]) →ₗ[ℤ] ℍ[ℚ, c, d] := LinearMap.proj 0
  let π₁ : (Fin 2 → ℍ[ℚ, c, d]) →ₗ[ℤ] ℍ[ℚ, c, d] := LinearMap.proj 1
  let J₀ : Submodule ℤ ℍ[ℚ, c, d] := M.map π₀
  let I₂ : Submodule ℤ ℍ[ℚ, c, d] := M.map π₁
  let I₁ : Submodule ℤ ℍ[ℚ, c, d] := M.comap (LinearMap.single ℤ (fun _ : Fin 2 => ℍ[ℚ, c, d]) 0)
  have hI₁ : ∀ a, a ∈ I₁ ↔ Pi.single (0 : Fin 2) a ∈ M := fun a => Iff.rfl
  have hI₂ : ∀ a, a ∈ I₂ ↔ ∃ m ∈ M, m 1 = a := fun a => by
    simp only [I₂, Submodule.mem_map]; rfl
  have hJ₀ : ∀ a, a ∈ J₀ ↔ ∃ m ∈ M, m 0 = a := fun a => by
    simp only [J₀, Submodule.mem_map]; rfl

  have hI₁mul : ∀ z ∈ I₁, ∀ o ∈ O, z * o ∈ I₁ := by
    intro z hz o ho
    rw [hI₁] at hz ⊢
    have := hM _ hz o ho
    convert this using 1
    funext i; fin_cases i <;> simp
  have hI₂mul : ∀ z ∈ I₂, ∀ o ∈ O, z * o ∈ I₂ := by
    intro z hz o ho
    rw [hI₂] at hz ⊢
    obtain ⟨m, hm, rfl⟩ := hz
    exact ⟨_, hM m hm o ho, rfl⟩

  obtain ⟨N, hN0, hNJ, hNI⟩ : ∃ N : ℕ, N ≠ 0 ∧ (∀ a ∈ J₀, ((N : ℤ) • a) ∈ O) ∧ (∀ a ∈ I₂, ((N : ℤ) • a) ∈ O) := by
    obtain ⟨s, hs⟩ := hfg
    have hgen : ∀ m ∈ s, ∃ N : ℕ, N ≠ 0 ∧ ((N : ℤ) • m 0) ∈ O ∧ ((N : ℤ) • m 1) ∈ O := by
      intro m _
      obtain ⟨N₀, hN₀, h₀⟩ := exists_natCast_smul_mem_of_mem_span O (x := m 0)
        (by rw [hOo.spanTop]; exact Submodule.mem_top)
      obtain ⟨N₁, hN₁, h₁⟩ := exists_natCast_smul_mem_of_mem_span O (x := m 1)
        (by rw [hOo.spanTop]; exact Submodule.mem_top)
      refine ⟨N₀ * N₁, mul_ne_zero hN₀ hN₁, ?_, ?_⟩
      · rw [Nat.cast_mul, mul_comm, mul_smul]; exact O.smul_mem _ h₀
      · rw [Nat.cast_mul, mul_smul]; exact O.smul_mem _ h₁
    choose! Nf hNf using hgen
    refine ⟨∏ m ∈ s, Nf m, Finset.prod_ne_zero_iff.mpr fun m hm => (hNf m hm).1, ?_, ?_⟩
    · intro a ha
      rw [hJ₀] at ha
      obtain ⟨m, hm, rfl⟩ := ha
      rw [← hs] at hm
      refine Submodule.span_induction (p := fun m _ => ((∏ m ∈ s, Nf m : ℕ) : ℤ) • m 0 ∈ O) ?_ ?_ ?_ ?_ hm
      · intro m hm
        obtain ⟨k, hk⟩ : Nf m ∣ ∏ m ∈ s, Nf m := Finset.dvd_prod_of_mem _ hm
        rw [hk, Nat.cast_mul, mul_comm, mul_smul]
        exact O.smul_mem _ (hNf m hm).2.1
      · simp
      · intro x y _ _ hx hy
        rw [Pi.add_apply, smul_add]; exact O.add_mem hx hy
      · intro a x _ hx
        rw [Pi.smul_apply, smul_comm]; exact O.smul_mem _ hx
    · intro a ha
      rw [hI₂] at ha
      obtain ⟨m, hm, rfl⟩ := ha
      rw [← hs] at hm
      refine Submodule.span_induction (p := fun m _ => ((∏ m ∈ s, Nf m : ℕ) : ℤ) • m 1 ∈ O) ?_ ?_ ?_ ?_ hm
      · intro m hm
        obtain ⟨k, hk⟩ : Nf m ∣ ∏ m ∈ s, Nf m := Finset.dvd_prod_of_mem _ hm
        rw [hk, Nat.cast_mul, mul_comm, mul_smul]
        exact O.smul_mem _ (hNf m hm).2.2
      · simp
      · intro x y _ _ hx hy
        rw [Pi.add_apply, smul_add]; exact O.add_mem hx hy
      · intro a x _ hx
        rw [Pi.smul_apply, smul_comm]; exact O.smul_mem _ hx

  obtain ⟨N', hN'0, hN'I₁, hN'I₂⟩ : ∃ N' : ℕ, N' ≠ 0 ∧ (∀ o ∈ O, ((N' : ℤ) • o) ∈ I₁) ∧ (∀ o ∈ O, ((N' : ℤ) • o) ∈ I₂) := by
    obtain ⟨N₀, hN₀, h₀⟩ := exists_natCast_smul_mem_of_mem_span M (x := Pi.single (0 : Fin 2) (1 : ℍ[ℚ, c, d]))
      (by rw [hspan]; exact Submodule.mem_top)
    obtain ⟨N₁, hN₁, h₁⟩ := exists_natCast_smul_mem_of_mem_span M (x := Pi.single (1 : Fin 2) (1 : ℍ[ℚ, c, d]))
      (by rw [hspan]; exact Submodule.mem_top)
    have h₀' : ((N₀ * N₁ : ℕ) : ℤ) • Pi.single (0 : Fin 2) (1 : ℍ[ℚ, c, d]) ∈ M := by
      rw [Nat.cast_mul, mul_comm, mul_smul]; exact M.smul_mem _ h₀
    have h₁' : ((N₀ * N₁ : ℕ) : ℤ) • Pi.single (1 : Fin 2) (1 : ℍ[ℚ, c, d]) ∈ M := by
      rw [Nat.cast_mul, mul_smul]; exact M.smul_mem _ h₁
    refine ⟨N₀ * N₁, mul_ne_zero hN₀ hN₁, fun o ho => ?_, fun o ho => ?_⟩
    · rw [hI₁]
      have e : Pi.single (0 : Fin 2) (((N₀ * N₁ : ℕ) : ℤ) • o) =
          fun i => (((N₀ * N₁ : ℕ) : ℤ) • (Pi.single (0 : Fin 2) (1 : ℍ[ℚ, c, d]) : Fin 2 → ℍ[ℚ, c, d])) i * o := by
        funext i
        fin_cases i
        · simp
        · simp
      rw [e]
      exact hM _ h₀' o ho
    · rw [hI₂]
      refine ⟨_, hM _ h₁' o ho, ?_⟩
      simp

  let sc : ℍ[ℚ, c, d] →ₗ[ℤ] ℍ[ℚ, c, d] := (N : ℤ) • LinearMap.id
  have hsc : ∀ (S : Submodule ℤ ℍ[ℚ, c, d]) (a : ℍ[ℚ, c, d]), a ∈ S.map sc ↔ ∃ b ∈ S, ((N : ℤ) • b) = a := by
    intro S a; simp [sc, Submodule.mem_map]
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  have hNinj : ∀ a b : ℍ[ℚ, c, d], ((N : ℤ) • a) = ((N : ℤ) • b) → a = b := by
    intro a b h
    rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ (N : ℤ) b] at h
    have := congrArg (fun z : ℍ[ℚ, c, d] => (((N : ℤ) : ℚ))⁻¹ • z) h
    simp only [smul_smul] at this
    rwa [inv_mul_cancel₀ (by exact_mod_cast hN0), one_smul, one_smul] at this
  have hscmem : ∀ (S : Submodule ℤ ℍ[ℚ, c, d]) (a : ℍ[ℚ, c, d]), ((N : ℤ) • a) ∈ S.map sc ↔ a ∈ S := by
    intro S a
    rw [hsc]
    exact ⟨fun ⟨b, hb, e⟩ => hNinj _ _ e ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩
  have hK₁O : I₁.map sc ≤ O := by
    intro a ha
    rw [hsc] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [hI₁] at hb
    exact hNJ _ ((hJ₀ b).mpr ⟨_, hb, by simp⟩)
  have hK₂O : I₂.map sc ≤ O := by
    intro a ha
    rw [hsc] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact hNI _ hb
  have hK₁mul : ∀ z ∈ I₁.map sc, ∀ o ∈ O, z * o ∈ I₁.map sc := by
    intro z hz o ho
    rw [hsc] at hz ⊢
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨_, hI₁mul b hb o ho, by rw [smul_mul_assoc]⟩
  have hK₂mul : ∀ z ∈ I₂.map sc, ∀ o ∈ O, z * o ∈ I₂.map sc := by
    intro z hz o ho
    rw [hsc] at hz ⊢
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨_, hI₂mul b hb o ho, by rw [smul_mul_assoc]⟩
  have hK₁full : ∃ n : ℤ, n ≠ 0 ∧ ∀ o ∈ O, n • o ∈ I₁.map sc := by
    refine ⟨(N : ℤ) * N', mul_ne_zero (Int.natCast_ne_zero.mpr hN0) (Int.natCast_ne_zero.mpr hN'0), fun o ho => ?_⟩
    rw [mul_smul, hscmem]
    exact hN'I₁ o ho
  have hK₂full : ∃ n : ℤ, n ≠ 0 ∧ ∀ o ∈ O, n • o ∈ I₂.map sc := by
    refine ⟨(N : ℤ) * N', mul_ne_zero (Int.natCast_ne_zero.mpr hN0) (Int.natCast_ne_zero.mpr hN'0), fun o ho => ?_⟩
    rw [mul_smul, hscmem]
    exact hN'I₂ o ho

  obtain ⟨t, y, ht, hy, hsum⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_sum_mul_eq_one_of_forall_mul_mem q hH O hO (I₂.map sc) hK₂O hK₂mul hK₂full

  have hxN : ∀ x ∈ t, ∃ b ∈ I₂, ((N : ℤ) • b) = x := fun x hx => (hsc I₂ x).mp (ht x hx)
  choose! xb hxb using hxN
  obtain ⟨u, hu⟩ := AddSubgroup.exists_forall_mem_iff_single_sub_mul_mem_of_sum_mul_eq_one
    (O : Set ℍ[ℚ, c, d]) M.toAddSubgroup (fun m hm o ho => hM m hm o ho) t xb (fun x => (N : ℤ) • y x)
    (fun k hk => by
      obtain ⟨hb, -⟩ := hxb k hk
      exact (hI₂ _).mp hb)
    (fun k hk m hm => by
      rw [smul_mul_assoc, ← mul_smul_comm]
      exact hy k hk _ ((hscmem I₂ _).mpr ((hI₂ _).mpr ⟨m, hm, rfl⟩)))
    (by
      rw [← hsum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [mul_smul_comm, ← smul_mul_assoc, (hxb k hk).2])

  obtain ⟨γ₁, γ₁', h₁, h₁', hmem⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_matrix_forall_mulVec_mem_iff_of_le q hH O hO (I₁.map sc) (I₂.map sc)
      hK₁O hK₁mul hK₁full hK₂O hK₂mul hK₂full

  set nH : ℍ[ℚ, c, d] := algebraMap ℚ ℍ[ℚ, c, d] (N : ℚ) with hnH
  set nI : ℍ[ℚ, c, d] := algebraMap ℚ ℍ[ℚ, c, d] ((N : ℚ)⁻¹) with hnI
  have hIH : nI * nH = 1 := by rw [hnH, hnI, ← map_mul, inv_mul_cancel₀ hNQ, map_one]
  have hHI : nH * nI = 1 := by rw [hnH, hnI, ← map_mul, mul_inv_cancel₀ hNQ, map_one]
  have hnHmul : ∀ z : ℍ[ℚ, c, d], nH * z = (N : ℤ) • z := by
    intro z
    rw [hnH, map_natCast, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  refine ⟨!![(1 : ℍ[ℚ, c, d]), u; 0, 1] * !![nI, 0; 0, nI] * γ₁,
    γ₁' * !![nH, 0; 0, nH] * !![(1 : ℍ[ℚ, c, d]), -u; 0, 1], ?_, ?_, fun x => ?_⟩
  · calc _ = !![(1 : ℍ[ℚ, c, d]), u; 0, 1] * (!![nI, 0; 0, nI] * (γ₁ * γ₁') * !![nH, 0; 0, nH]) *
          !![(1 : ℍ[ℚ, c, d]), -u; 0, 1] := by noncomm_ring
      _ = 1 := by
        rw [h₁, mul_one, diag_mul_diag, hIH, ← Matrix.one_fin_two, mul_one, upper_mul_upper_neg]
  · calc _ = γ₁' * (!![nH, 0; 0, nH] * (!![(1 : ℍ[ℚ, c, d]), -u; 0, 1] * !![1, u; 0, 1]) * !![nI, 0; 0, nI]) *
          γ₁ := by noncomm_ring
      _ = 1 := by
        rw [upper_neg_mul_upper, mul_one, diag_mul_diag, hHI, ← Matrix.one_fin_two, mul_one, h₁']
  ·
    change x ∈ M.toAddSubgroup ↔ _
    rw [hu x, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmem, upper_mulVec, diag_mulVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hnHmul]
    rw [hscmem, hscmem, hI₁, hI₂, neg_mul, ← sub_eq_add_neg]
    rfl

end S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mem_iff_forall_mulVec_mem
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_matrix_forall_mem_iff_forall_mulVec_mem (solution)
