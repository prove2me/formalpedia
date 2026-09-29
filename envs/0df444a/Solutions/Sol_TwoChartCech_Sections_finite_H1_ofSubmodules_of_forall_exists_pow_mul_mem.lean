-- Prove2me | solution 1 for TwoChartCech.Sections.finite_H1_ofSubmodules_of_forall_exists_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/044d3525-5023-5fd9-961d-5bbd955a6cb6

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_Sections_finite_H1_ofSubmodules_of_forall_exists_pow_mul_mem

set_option autoImplicit false

universe u v

namespace TwoChartCech
p2m_export "TwoChartCech" "Sections Sections.cechDiff_apply Sections.ofSubmodules"
namespace FinP1
p2m_open "TwoChartCech"

open Submodule

theorem finite_H1
    {R : Type u} [CommRing R] {F : Type v} [CommRing F] [Algebra R F]
    (x y : F) (hxy : x * y = 1)
    (N0 N1 N01 : Submodule R F) (h0 : N0 ≤ N01) (h1 : N1 ≤ N01)
    (hx : ∀ m ∈ N0, x * m ∈ N0) (hy : ∀ m ∈ N1, y * m ∈ N1)
    (hy01 : ∀ m ∈ N01, y * m ∈ N01)
    (G0 : Finset F) (hG0 : (G0 : Set F) ⊆ N0)
    (hspan : (N0 : Set F) ⊆ Submodule.span ↥(Algebra.adjoin R ({x} : Set F)) (G0 : Set F))
    (hloc0 : ∀ z ∈ N01, ∃ k : ℕ, x ^ k * z ∈ N0) (hloc1 : ∀ z ∈ N01, ∃ k : ℕ, y ^ k * z ∈ N1) :
    Module.Finite R (TwoChartCech.Sections.ofSubmodules N0 N1 N01 h0 h1).H1 := by
  classical
  set S := TwoChartCech.Sections.ofSubmodules N0 N1 N01 h0 h1 with hSdef

  have hyx : y * x = 1 := by rw [mul_comm, hxy]
  have hpow : ∀ k : ℕ, y ^ k * x ^ k = 1 := fun k => by rw [← mul_pow, hyx, one_pow]
  have hxN0 : ∀ (j : ℕ) (m : F), m ∈ N0 → x ^ j * m ∈ N0 := by
    intro j m hm
    induction j with
    | zero => simpa
    | succ j ih => rw [pow_succ', mul_assoc]; exact hx _ ih
  have hyN1 : ∀ (j : ℕ) (m : F), m ∈ N1 → y ^ j * m ∈ N1 := by
    intro j m hm
    induction j with
    | zero => simpa
    | succ j ih => rw [pow_succ', mul_assoc]; exact hy _ ih
  have hyN01 : ∀ (j : ℕ) (m : F), m ∈ N01 → y ^ j * m ∈ N01 := by
    intro j m hm
    induction j with
    | zero => simpa
    | succ j ih => rw [pow_succ', mul_assoc]; exact hy01 _ ih

  have hmk0 : ∀ (n : ↥N01), (n : F) ∈ N0 → (Submodule.Quotient.mk n : S.H1) = 0 := by
    intro n hn
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨(-⟨(n : F), hn⟩, 0), ?_⟩
    rw [TwoChartCech.Sections.cechDiff_apply]
    apply Subtype.ext
    change ((0 : ↥N1) : F) - ((-⟨(n : F), hn⟩ : ↥N0) : F) = (n : F)
    simp
  have hmk1 : ∀ (n : ↥N01), (n : F) ∈ N1 → (Submodule.Quotient.mk n : S.H1) = 0 := by
    intro n hn
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨(0, ⟨(n : F), hn⟩), ?_⟩
    rw [TwoChartCech.Sections.cechDiff_apply]
    apply Subtype.ext
    change ((⟨(n : F), hn⟩ : ↥N1) : F) - ((0 : ↥N0) : F) = (n : F)
    simp

  have hG01 : ∀ g : ↥G0, (g : F) ∈ N01 := fun g => h0 (hG0 g.2)
  choose kg hkg using fun g : ↥G0 => hloc1 (g : F) (hG01 g)

  let gen : (Σ g : ↥G0, Fin (kg g)) → S.H1 := fun p =>
    Submodule.Quotient.mk ⟨y ^ (p.2 : ℕ) * (p.1 : F), hyN01 _ _ (hG01 p.1)⟩
  let W : Submodule R S.H1 := Submodule.span R (Set.range gen)

  have hgenW : ∀ (g : ↥G0) (b : ℕ), (Submodule.Quotient.mk ⟨y ^ b * (g : F), hyN01 _ _ (hG01 g)⟩ : S.H1) ∈ W := by
    intro g b
    by_cases hb : b < kg g
    · exact Submodule.subset_span ⟨⟨g, ⟨b, hb⟩⟩, rfl⟩
    · have hle : kg g ≤ b := Nat.le_of_not_lt hb
      have hmem : y ^ b * (g : F) ∈ N1 := by
        have : y ^ b * (g : F) = y ^ (b - kg g) * (y ^ kg g * (g : F)) := by
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
        rw [this]; exact hyN1 _ _ (hkg g)
      rw [hmk1 _ hmem]; exact W.zero_mem

  let T : Set F := {w | ∃ (j : ℕ) (g : ↥G0), w = x ^ j * (g : F)}
  have hT0 : T ⊆ N0 := by
    rintro w ⟨j, g, rfl⟩; exact hxN0 _ _ (hG0 g.2)
  have hstep : ∀ w ∈ Submodule.span R T, ∀ k : ℕ,
      ∃ hw : y ^ k * w ∈ N01, (Submodule.Quotient.mk ⟨y ^ k * w, hw⟩ : S.H1) ∈ W := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hwT =>
      obtain ⟨j, g, rfl⟩ := hwT
      intro k
      by_cases hjk : j ≤ k
      · have heq : y ^ k * (x ^ j * (g : F)) = y ^ (k - j) * (g : F) := by
          rw [← mul_assoc, ← Nat.sub_add_cancel hjk, pow_add, mul_assoc (y ^ (k - j)), hpow, mul_one,
            Nat.sub_add_cancel hjk]
        refine ⟨heq ▸ hyN01 _ _ (hG01 g), ?_⟩
        have : (⟨y ^ k * (x ^ j * (g : F)), heq ▸ hyN01 _ _ (hG01 g)⟩ : ↥N01) =
            ⟨y ^ (k - j) * (g : F), hyN01 _ _ (hG01 g)⟩ := Subtype.ext heq
        rw [this]; exact hgenW g (k - j)
      · have hkj : k ≤ j := Nat.le_of_not_le hjk
        have heq : y ^ k * (x ^ j * (g : F)) = x ^ (j - k) * (g : F) := by
          rw [← mul_assoc, ← Nat.add_sub_cancel' hkj, pow_add, ← mul_assoc, hpow, one_mul, Nat.add_sub_cancel' hkj]
        have hmem : y ^ k * (x ^ j * (g : F)) ∈ N0 := by rw [heq]; exact hxN0 _ _ (hG0 g.2)
        exact ⟨h0 hmem, by rw [hmk0 _ hmem]; exact W.zero_mem⟩
    | zero => intro k; exact ⟨by rw [mul_zero]; exact N01.zero_mem, by
        have : (⟨y ^ k * 0, by rw [mul_zero]; exact N01.zero_mem⟩ : ↥N01) = 0 := Subtype.ext (mul_zero _)
        rw [this, Submodule.Quotient.mk_zero]; exact W.zero_mem⟩
    | add w₁ w₂ _ _ ih₁ ih₂ =>
      intro k
      obtain ⟨hw₁, hW₁⟩ := ih₁ k
      obtain ⟨hw₂, hW₂⟩ := ih₂ k
      have hmem : y ^ k * (w₁ + w₂) ∈ N01 := by rw [mul_add]; exact N01.add_mem hw₁ hw₂
      refine ⟨hmem, ?_⟩
      have : (⟨y ^ k * (w₁ + w₂), hmem⟩ : ↥N01) = ⟨y ^ k * w₁, hw₁⟩ + ⟨y ^ k * w₂, hw₂⟩ :=
        Subtype.ext (mul_add _ _ _)
      rw [this, Submodule.Quotient.mk_add]
      exact W.add_mem hW₁ hW₂
    | smul r w _ ih =>
      intro k
      obtain ⟨hw, hW⟩ := ih k
      have hmem : y ^ k * (r • w) ∈ N01 := by rw [mul_smul_comm]; exact N01.smul_mem r hw
      refine ⟨hmem, ?_⟩
      have : (⟨y ^ k * (r • w), hmem⟩ : ↥N01) = r • ⟨y ^ k * w, hw⟩ := Subtype.ext (mul_smul_comm _ _ _)
      rw [this, Submodule.Quotient.mk_smul]
      exact W.smul_mem r hW

  have hxT : ∀ u ∈ Submodule.span R T, x * u ∈ Submodule.span R T := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem w' hw'T =>
      obtain ⟨j, g, rfl⟩ := hw'T
      exact Submodule.subset_span ⟨j + 1, g, by rw [pow_succ', mul_assoc]⟩
    | zero => rw [mul_zero]; exact (Submodule.span R T).zero_mem
    | add u₁ u₂ _ _ i₁ i₂ => rw [mul_add]; exact (Submodule.span R T).add_mem i₁ i₂
    | smul r u _ i => rw [mul_smul_comm]; exact (Submodule.span R T).smul_mem r i
  have hadjT : ∀ a ∈ Algebra.adjoin R ({x} : Set F), ∀ u ∈ Submodule.span R T, a * u ∈ Submodule.span R T := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a hax =>
      rw [Set.mem_singleton_iff] at hax
      subst hax
      exact hxT
    | algebraMap r =>
      intro u hu
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact (Submodule.span R T).smul_mem r hu
    | add a₁ a₂ _ _ i₁ i₂ => intro u hu; rw [add_mul]; exact (Submodule.span R T).add_mem (i₁ u hu) (i₂ u hu)
    | mul a₁ a₂ _ _ i₁ i₂ => intro u hu; rw [mul_assoc]; exact i₁ _ (i₂ u hu)

  have hspanT : (Submodule.span ↥(Algebra.adjoin R ({x} : Set F)) (G0 : Set F) : Set F) ⊆ Submodule.span R T := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hwG => exact Submodule.subset_span ⟨0, ⟨w, hwG⟩, by rw [pow_zero, one_mul]⟩
    | zero => exact (Submodule.span R T).zero_mem
    | add w₁ w₂ _ _ ih₁ ih₂ => exact (Submodule.span R T).add_mem ih₁ ih₂
    | smul a w _ ih => exact hadjT a.1 a.2 w ih

  have hWtop : ∀ q : S.H1, q ∈ W := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ n =>
      obtain ⟨k, hk⟩ := hloc0 (n : F) n.2
      have hmem : x ^ k * (n : F) ∈ Submodule.span R T := hspanT (hspan hk)
      obtain ⟨hw, hW⟩ := hstep _ hmem k
      have heq : (⟨y ^ k * (x ^ k * (n : F)), hw⟩ : ↥N01) = n :=
        Subtype.ext (show y ^ k * (x ^ k * (n : F)) = (n : F) by rw [← mul_assoc, hpow, one_mul])
      rwa [heq] at hW
  rw [Module.finite_def, Submodule.fg_def]
  exact ⟨Set.range gen, Set.finite_range gen, eq_top_iff.mpr fun q _ => hWtop q⟩

end TwoChartCech.FinP1

theorem solution
    {R : Type u} [CommRing R] {F : Type v} [CommRing F] [Algebra R F]
    (x y : F) (hxy : x * y = 1)
    (N0 N1 N01 : Submodule R F) (h0 : N0 ≤ N01) (h1 : N1 ≤ N01)
    (hx : ∀ m ∈ N0, x * m ∈ N0) (hy : ∀ m ∈ N1, y * m ∈ N1) (hy01 : ∀ m ∈ N01, y * m ∈ N01)
    (G0 : Finset F) (hG0 : (G0 : Set F) ⊆ N0)
    (hspan : (N0 : Set F) ⊆ Submodule.span ↥(Algebra.adjoin R ({x} : Set F)) (G0 : Set F))
    (hloc0 : ∀ z ∈ N01, ∃ k : ℕ, x ^ k * z ∈ N0) (hloc1 : ∀ z ∈ N01, ∃ k : ℕ, y ^ k * z ∈ N1) :
    Module.Finite R (TwoChartCech.Sections.ofSubmodules N0 N1 N01 h0 h1).H1 :=
  TwoChartCech.FinP1.finite_H1 x y hxy N0 N1 N01 h0 h1 hx hy hy01 G0 hG0 hspan hloc0 hloc1

end S_TwoChartCech_Sections_finite_H1_ofSubmodules_of_forall_exists_pow_mul_mem
end P2MW
export P2MW.S_TwoChartCech_Sections_finite_H1_ofSubmodules_of_forall_exists_pow_mul_mem (solution)
