-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isRegularLocalRing_quotient_of_not_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:21.502989+00:00
-- url     : https://prove2.me/submissions/ce89a726-3ea3-4e7e-afaf-dee2e937cce0

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open IsLocalRing
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution [IsRegularLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  classical
  have hreg : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
    obtain ⟨h⟩ := ‹IsRegularLocalRing R›
    exact h
  set n := Submodule.spanFinrank (maximalIdeal R) with hn_def
  have hxle : Ideal.span {x} ≤ maximalIdeal R := (Ideal.span_singleton_le_iff_mem _).mpr hx
  have hxne : Ideal.span {x} ≠ ⊤ := fun htop =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (htop ▸ hxle))
  haveI : Nontrivial (R ⧸ Ideal.span {x}) := by
    refine ⟨⟨0, 1, fun h => hxne ((Ideal.eq_top_iff_one _).mpr ?_)⟩⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]
    exact h.symm
  haveI : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

  have hFG : (maximalIdeal R).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs_card, hs_span⟩ :=
    Submodule.FG.exists_span_set_encard_eq_spanFinrank (p := maximalIdeal R) hFG
  have hs_fin : s.Finite := Set.finite_of_encard_eq_coe hs_card
  have hs_ncard : s.ncard = n := by
    have h := hs_fin.cast_ncard_eq
    rw [hs_card] at h
    exact_mod_cast h
  haveI : Fintype s := hs_fin.fintype
  have hxs : x ∈ Submodule.span R (Set.range ((↑) : s → R)) := by
    rw [Subtype.range_coe, hs_span]
    exact hx
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hxs
  simp only [Finsupp.sum] at hc

  obtain ⟨i0, hi0⟩ : ∃ i, IsUnit (c i) := by
    by_contra hcon
    push_neg at hcon
    apply hx2
    rw [← hc, sq]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [smul_eq_mul]
    refine Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hcon i))) ?_
    rw [← hs_span]
    exact Submodule.subset_span i.2
  have hi0mem : i0 ∈ c.support := Finsupp.mem_support_iff.mpr hi0.ne_zero

  have hrest : ∑ i ∈ c.support.erase i0, c i • (i : R) ∈
      Ideal.span (s \ {(i0 : R)}) ⊔ Ideal.span {x} := by
    refine Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (Submodule.mem_sup_left
      (Ideal.subset_span ⟨i.2, fun h => Finset.ne_of_mem_erase hi (Subtype.ext h)⟩)))
  have hsplit : c i0 • (i0 : R) + ∑ i ∈ c.support.erase i0, c i • (i : R) = x :=
    (Finset.add_sum_erase _ (fun i => c i • (i : R)) hi0mem).trans hc
  have hi0J : (i0 : R) ∈ Ideal.span (s \ {(i0 : R)}) ⊔ Ideal.span {x} := by
    have h1 : c i0 • (i0 : R) = x - ∑ i ∈ c.support.erase i0, c i • (i : R) := by
      rw [← hsplit, add_sub_cancel_right]
    have h2 : c i0 • (i0 : R) ∈ Ideal.span (s \ {(i0 : R)}) ⊔ Ideal.span {x} := by
      rw [h1]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right (Ideal.mem_span_singleton_self x)) hrest
    have h3 : (i0 : R) = ↑hi0.unit⁻¹ * (c i0 • (i0 : R)) := by
      rw [smul_eq_mul, ← mul_assoc, hi0.val_inv_mul, one_mul]
    have h4 := Ideal.mul_mem_left _ (↑hi0.unit⁻¹ : R) h2
    rwa [← h3] at h4
  have hmJ : maximalIdeal R ≤ Ideal.span (s \ {(i0 : R)}) ⊔ Ideal.span {x} := by
    rw [← hs_span]
    refine Submodule.span_le.mpr (fun y hy => ?_)
    by_cases hyi : y = (i0 : R)
    · rw [hyi]
      exact hi0J
    · exact Submodule.mem_sup_left (Ideal.subset_span ⟨hy, hyi⟩)

  have hmap : Ideal.map (Ideal.Quotient.mk (Ideal.span {x}))
      (Ideal.span (s \ {(i0 : R)}) ⊔ Ideal.span {x}) =
      Ideal.span ((Ideal.Quotient.mk (Ideal.span {x})) '' (s \ {(i0 : R)})) := by
    rw [Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq, Ideal.map_span]
  have hmQ : maximalIdeal (R ⧸ Ideal.span {x}) =
      Ideal.span ((Ideal.Quotient.mk (Ideal.span {x})) '' (s \ {(i0 : R)})) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hr : r ∈ maximalIdeal R := by
        by_contra hr
        have hu : IsUnit r := by
          by_contra hu'
          exact hr ((IsLocalRing.mem_maximalIdeal r).mpr (mem_nonunits_iff.mpr hu'))
        exact ((IsLocalRing.mem_maximalIdeal _).mp hy) (hu.map _)
      rw [← hmap]
      exact Ideal.mem_map_of_mem _ (hmJ hr)
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨y, hy, rfl⟩
      have hym : y ∈ maximalIdeal R := by
        rw [← hs_span]
        exact Submodule.subset_span hy.1
      refine (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (fun hu => ?_))
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective v
      have h1 : Ideal.Quotient.mk (Ideal.span {x}) (y * w - 1) = 0 := by
        rw [map_sub, map_mul, hv, map_one, sub_self]
      have h2 : y * w - 1 ∈ maximalIdeal R := hxle (Ideal.Quotient.eq_zero_iff_mem.mp h1)
      have h3 : (1 : R) ∈ maximalIdeal R := by
        have h4 := Ideal.sub_mem _ (Ideal.mul_mem_right w _ hym) h2
        rwa [sub_sub_cancel] at h4
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h3)

  have hk : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span {x})) ≤ n - 1 := by
    have hfin : (s \ {(i0 : R)}).Finite := hs_fin.subset Set.diff_subset
    rw [hmQ]
    calc _ ≤ ((Ideal.Quotient.mk (Ideal.span {x})) '' (s \ {(i0 : R)})).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (hfin.image _)
      _ ≤ (s \ {(i0 : R)}).ncard := Set.ncard_image_le hfin
      _ = s.ncard - 1 := Set.ncard_diff_singleton_of_mem i0.2
      _ = n - 1 := by rw [hs_ncard]
  have hn1 : 1 ≤ n := by
    rw [← hs_ncard]
    exact (Set.ncard_pos hs_fin).mpr ⟨_, i0.2⟩

  have hdimQ := ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ Ideal.span {x})
  have hkrull : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    have hsub : (↑({x} : Finset R) : Set R) ⊆ ↑(Ring.jacobson R) := by
      rw [Finset.coe_singleton, Set.singleton_subset_iff, SetLike.mem_coe, ← Ideal.jacobson_bot,
        IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact hx
    have h := ringKrullDim_le_ringKrullDim_quotient_add_card {x} hsub
    rwa [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one] at h
  generalize hk_def : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span {x})) = k at hk hdimQ
  have hkn : k + 1 ≤ n := by omega
  have hle1 : ((k : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim R := by
    rw [← hreg]
    exact_mod_cast hkn
  have hle2 : ((k : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span {x}) := by
    have h5 := hle1.trans hkrull
    generalize ringKrullDim (R ⧸ Ideal.span {x}) = e at h5 ⊢
    induction e using WithBot.recBotCoe with
    | bot => exact absurd h5 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact le_top
      | coe e =>
        have h6 : k + 1 ≤ e + 1 := by exact_mod_cast h5
        exact_mod_cast (by omega : k ≤ e)
  refine ⟨IsRegularLocalRing.mk ?_, le_antisymm ?_ hkrull⟩
  · rw [hk_def]
    exact le_antisymm hle2 hdimQ
  · exact (add_le_add hdimQ le_rfl).trans hle1
end ReciprocityTheory.AnForm.R
