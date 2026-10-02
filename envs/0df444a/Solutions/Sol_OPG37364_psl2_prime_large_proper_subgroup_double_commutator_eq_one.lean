-- Prove2me | solution 1 for OPG37364.psl2_prime_large_proper_subgroup_double_commutator_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T14:06:22.136083+00:00
-- url     : https://prove2.me/submissions/1b291081-dc9c-4f75-a160-315b56afe416

/-
Stage 13 prime-field adapter, 2026-09-11.
Released under the Apache 2.0 license; see LICENSE.

Classical mathematics: Dickson / Huppert / Davidoff-Sarnak-Valette.
Classification formalization: Qiuzhen-CFSG/CFSG and its source authors,
commit 96b2a02085dc678f3e0a97b334c31ada599c55fd.
This file supplies the prime-field specialization and elementary case adapters.
The external classification sources are preserved unchanged.
-/
import Theorems.Thm_Glauberman_Dickson_huppert_II_8_27_dickson_psl2_subgroup_classification
import Mathlib.GroupTheory.Commutator.Basic

set_option autoImplicit false

open scoped commutatorElement

namespace OPG37364

private lemma double_commutator_of_commutative
    {G : Type*} [Group G] [IsMulCommutative G] (a b c d : G) :
    ⁅⁅a, b⁆, ⁅c, d⁆⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)

private lemma dihedral_commutator_rotation {n : ℕ} (a b : DihedralGroup n) :
    ∃ k, ⁅a, b⁆ = DihedralGroup.r k := by
  cases a <;> cases b <;>
    simp only [commutatorElement_def, DihedralGroup.inv_r, DihedralGroup.inv_sr,
      DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.sr_mul_sr] <;> exact ⟨_, rfl⟩

private lemma dihedral_double_commutator {n : ℕ} (a b c d : DihedralGroup n) :
    ⁅⁅a, b⁆, ⁅c, d⁆⁆ = 1 := by
  obtain ⟨k, hk⟩ := dihedral_commutator_rotation a b
  obtain ⟨l, hl⟩ := dihedral_commutator_rotation c d
  rw [hk, hl, commutatorElement_eq_one_iff_mul_comm]
  simp only [DihedralGroup.r_mul_r, add_comm]

private lemma double_commutator_abelian_by_cyclic
    {G : Type*} [Group G] (N C : Subgroup G)
    [N.Normal] [IsMulCommutative N] [IsCyclic C]
    (hNC : N ⊔ C = ⊤) (a b c d : G) : ⁅⁅a, b⁆, ⁅c, d⁆⁆ = 1 := by
  let f := QuotientGroup.mk' N
  have hC : C.map f = ⊤ := by
    have h := congrArg (Subgroup.map f) hNC
    simpa [f, Subgroup.map_sup,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] using h
  have hsurj : Function.Surjective (f.comp C.subtype) := by
    intro y
    have hy : y ∈ C.map f := hC ▸ Subgroup.mem_top y
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, hxy⟩
  let : IsCyclic (G ⧸ N) := isCyclic_of_surjective (f.comp C.subtype) hsurj
  have hmem (x y : G) : ⁅x, y⁆ ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change f ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  exact congrArg Subtype.val
    (mul_comm' (⟨⁅a, b⁆, hmem a b⟩ : N) (⟨⁅c, d⁆, hmem c d⟩ : N))

private noncomputable def sl2FieldEquiv
    {F K : Type*} [Field F] [Field K] (e : F ≃+* K) :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  { Matrix.SpecialLinearGroup.map e.toRingHom with
    invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
    left_inv := by
      intro x
      ext i j
      change e.symm (e (x i j)) = x i j
      exact e.symm_apply_apply _
    right_inv := by
      intro x
      ext i j
      change e (e.symm (x i j)) = x i j
      exact e.apply_symm_apply _ }

private lemma map_center_equiv {G K : Type*} [Group G] [Group K] (e : G ≃* K) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center K := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    change e w * e x = e x * e w
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hx w)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply Subgroup.mem_center_iff.mpr
    intro z
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using Subgroup.mem_center_iff.mp hy (e z)

private noncomputable def psl2FieldEquiv
    {F K : Type*} [Field F] [Field K] (e : F ≃+* K) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
  QuotientGroup.congr _ _ (sl2FieldEquiv e) (map_center_equiv (sl2FieldEquiv e))

/-- Prime-field consequence of Dickson's subgroup classification (DSV §3.3):
a proper subgroup of PSL₂(F_q) with more than 60 elements is metabelian,
expressed here as the double-commutator identity, without an auxiliary class. -/
theorem _root_.solution
    (q : ℕ) [Fact q.Prime] (_hq5 : 5 ≤ q)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q)))
    (hproper : H ≠ ⊤) (hcard : 60 < Nat.card H) (a b c d : H) :
    ⁅⁅a, b⁆, ⁅c, d⁆⁆ = 1 := by
  have hclass :=
    Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := q) (f := 1) (F := ZMod q) (by simp) H
  rcases hclass with helem | hcyc | hdih | hA4 | hS4 | hA5 | hNC | hPSL | hPGL
  · let := helem
    exact double_commutator_of_commutative a b c d
  · obtain ⟨z, _, _, hz⟩ := hcyc
    let := hz
    exact double_commutator_of_commutative a b c d
  · obtain ⟨z, _, _, ⟨e⟩⟩ := hdih
    apply e.injective
    simpa only [map_commutatorElement, map_one] using
      dihedral_double_commutator (e a) (e b) (e c) (e d)
  · obtain ⟨_, ⟨e⟩⟩ := hA4
    have hc : Nat.card H = 12 := (Nat.card_congr e.toEquiv).trans (by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial])
    omega
  · obtain ⟨_, ⟨e⟩⟩ := hS4
    have hc : Nat.card H = 24 := (Nat.card_congr e.toEquiv).trans (by
      rw [Nat.card_perm]
      norm_num [Nat.factorial])
    omega
  · obtain ⟨_, ⟨e⟩⟩ := hA5
    have hc : Nat.card H = 60 := (Nat.card_congr e.toEquiv).trans (by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial])
    omega
  · obtain ⟨m, t, _, _, N, C, hN, hNabel, _, hC, _, _, hNC⟩ := hNC
    let := hN
    let := hNabel
    let := hC
    exact double_commutator_abelian_by_cyclic N C hNC a b c d
  · obtain ⟨m, _, hm, ⟨e⟩⟩ := hPSL
    have hm1 : m = 1 := Nat.dvd_one.mp hm
    subst m
    let e' := e.trans (psl2FieldEquiv (GaloisField.equivZmodP q).toRingEquiv)
    exact (hproper (H.eq_top_of_card_eq (Nat.card_congr e'.toEquiv))).elim
  · obtain ⟨m, hm, hdvd, _⟩ := hPGL
    have hh := Nat.dvd_one.mp hdvd
    omega

end OPG37364
