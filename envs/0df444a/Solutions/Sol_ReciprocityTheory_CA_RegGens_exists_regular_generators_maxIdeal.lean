-- Prove2me | solution 1 for ReciprocityTheory.CA.RegGens.exists_regular_generators_maxIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:56.275586+00:00
-- url     : https://prove2.me/submissions/6fe26728-fa81-426f-af7a-e90074926411

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RegGensA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RegGens
import Theorems.Thm_ReciprocityTheory_CA_RegA_IsRegularLocalRing_ringKrullDim_quotient_span_singleton_add_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian IsLocalRing RingTheory.Sequence
universe u v
open ReciprocityTheory ReciprocityTheory.CA ReciprocityTheory.CA.RegGens
open Pointwise
namespace ReciprocityTheory.CA.RegGens
theorem _root_.solution : ∀ (d : ℕ) (P : Type u) [CommRing P] [IsRegularLocalRing P],
    ringKrullDim P = d →
    ∃ rs : List P, rs.length = d ∧ IsRegular P rs ∧ Ideal.ofList rs = maximalIdeal P := by
  intro d
  induction d with
  | zero =>
    intro P _ _ hd
    have hsf : (maximalIdeal P).spanFinrank = 0 := by
      have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := P)
      rw [hd] at h
      exact_mod_cast h
    have hbot : maximalIdeal P = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp hsf
    exact ⟨[], rfl, IsRegular.nil P P, by rw [Ideal.ofList_nil, hbot]⟩
  | succ d IH =>
    intro P _ _ hd
    have hsq : ¬ maximalIdeal P ≤ maximalIdeal P ^ 2 := by
      intro hle
      have hbot := RegA.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq P hle
      have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := P)
      rw [hd, hbot, Submodule.spanFinrank_bot] at h
      have : (0 : ℕ) = d + 1 := by exact_mod_cast h
      omega
    obtain ⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal P ∧ x ∉ maximalIdeal P ^ 2 := by
      by_contra hc
      push Not at hc
      exact hsq fun y hy => hc y hy
    set I : Ideal P := Ideal.span ({x} : Set P) with hI
    have hreg : IsRegularLocalRing (P ⧸ I) :=
      RegA.IsRegularLocalRing.quotient_span_singleton hx hx2
    have hdim : ringKrullDim (P ⧸ I) = d := by
      have h1 := RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hx hx2
      have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := P ⧸ I)
      rw [← h2] at h1 ⊢
      rw [hd] at h1
      have h3 : (maximalIdeal (P ⧸ I)).spanFinrank + 1 = d + 1 := by exact_mod_cast h1
      exact_mod_cast (by omega : (maximalIdeal (P ⧸ I)).spanFinrank = d)
    obtain ⟨rs', hlen, hrs', hgen⟩ := IH (P ⧸ I) hdim
    let lift : P ⧸ I → P := fun y => Quotient.out y
    have hlift : ∀ y, Ideal.Quotient.mk I (lift y) = y := fun y => Ideal.Quotient.mk_out y
    have hmap : (rs'.map lift).map (Ideal.Quotient.mk I) = rs' := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id rs']
      exact List.map_congr_left fun y _ => hlift y
    refine ⟨x :: rs'.map lift, by simp [hlen], ?_, ?_⟩
    · rw [isRegular_cons_iff', hmap]
      refine ⟨?_, ?_⟩
      · have hx0 : x ≠ 0 := by
          rintro rfl
          exact hx2 (zero_mem _)
        exact (IsRegular.of_ne_zero hx0).left
      · have hsm : (x • ⊤ : Submodule P P) = I := by
          rw [hI, ← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
        let e : QuotSMulTop x P ≃ₗ[P] P ⧸ I := Submodule.quotEquivOfEq _ _ hsm
        refine (e.toAddEquiv.isRegular_congr (as := rs') (bs := rs') ?_).mpr hrs'
        refine List.forall₂_same.mpr fun r _ y => ?_
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rfl
    · rw [Ideal.ofList_cons]
      have h1 : Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I)
          (Ideal.ofList (rs'.map lift))) = Ideal.ofList (rs'.map lift) ⊔ I := by
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
          Ideal.mk_ker]
      rw [Ideal.map_ofList, hmap, hgen] at h1
      have h2 : Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (P ⧸ I)) = maximalIdeal P := by
        have : (Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (P ⧸ I))).IsMaximal :=
          Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
        exact IsLocalRing.eq_maximalIdeal this
      rw [← h2, h1, sup_comm]
end ReciprocityTheory.CA.RegGens
