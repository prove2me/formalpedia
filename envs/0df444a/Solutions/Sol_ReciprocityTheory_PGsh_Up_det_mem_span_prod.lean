-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.det_mem_span_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:56:37.678314+00:00
-- url     : https://prove2.me/submissions/64466b34-8ce2-4ee1-ac74-3424971ce17c

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Theorems.Thm_ReciprocityTheory_PGsh_Up_det_col_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {R : Type*} [CommRing R] [IsLocalRing R] :
    ∀ (m : ℕ) (c : Fin m → R) (n : ℕ) (q : Fin n → ((j : Fin m) → R ⧸ Ideal.span {c j})),
      Submodule.span R (Set.range q) = ⊤ →
      ∀ T : Matrix (Fin n) (Fin n) R, (∀ k, ∑ i, T k i • q i = 0) →
      T.det ∈ Ideal.span {∏ j, c j} := by
  intro m
  induction m with
  | zero => intro c n q _ T _; simp
  | succ m ih =>
    intro c n q hq T hT
    let tl : ((j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) →ₗ[R]
        ((j : Fin m) → R ⧸ Ideal.span {c j.succ}) :=
      LinearMap.pi fun j => LinearMap.proj j.succ
    have htl_surj : Function.Surjective tl := fun y =>
      ⟨Fin.cons (0 : R ⧸ Ideal.span {c 0}) y, funext fun j => rfl⟩
    have hprod : ∏ j, c j = c 0 * ∏ j : Fin m, c j.succ := Fin.prod_univ_succ c

    have hfst : ∀ (r : Fin n → R) (a : Fin n → R),
        (∀ i, Ideal.Quotient.mk (Ideal.span {c 0}) (a i) = q i 0) →
        (∑ i, r i • q i) 0 = Ideal.Quotient.mk (Ideal.span {c 0}) (∑ i, r i * a i) := by
      intro r a ha
      rw [Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, ← ha i, map_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    by_cases hc0 : IsUnit (c 0)
    · have hgen : Submodule.span R (Set.range (tl ∘ q)) = ⊤ := by
        rw [Set.range_comp, ← Submodule.map_span, hq, Submodule.map_top,
          LinearMap.range_eq_top.2 htl_surj]
      have h := ih (fun j => c j.succ) n (tl ∘ q) hgen T (fun k => by
        have := congrArg tl (hT k)
        rw [map_sum, map_zero] at this
        simpa only [map_smul, Function.comp_apply] using this)
      rw [hprod, Ideal.span_singleton_mul_left_unit hc0]
      exact h
    · choose a ha using fun i => Ideal.Quotient.mk_surjective (q i 0)
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
        (hq ▸ Submodule.mem_top : (Pi.single (0 : Fin (m + 1)) (1 : R ⧸ Ideal.span {c 0}) :
          (j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) ∈ Submodule.span R (Set.range q))
      have hc0m : c 0 ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hc0
      have hspan_le : Ideal.span {c 0} ≤ IsLocalRing.maximalIdeal R :=
        (Ideal.span_singleton_le_iff_mem _).2 hc0m
      have h1 : ∑ i, g i * a i - 1 ∈ Ideal.span {c 0} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hfst g a ha, hg]
        simp
      have hu : IsUnit (∑ i, g i * a i) := by
        by_contra hx
        have hx' : ∑ i, g i * a i ∈ IsLocalRing.maximalIdeal R :=
          (IsLocalRing.mem_maximalIdeal _).2 hx
        have := Ideal.sub_mem _ hx' (hspan_le h1)
        rw [sub_sub_cancel] at this
        exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
      obtain ⟨i₀, hi₀⟩ : ∃ i₀, IsUnit (a i₀) := by
        by_contra hne
        push Not at hne
        apply (IsLocalRing.mem_maximalIdeal _).1 _ hu
        exact Ideal.sum_mem _ fun i _ =>
          Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i))
      set ai : R := ↑hi₀.unit⁻¹ with hai
      have haai : a i₀ * ai = 1 := by rw [hai]; exact hi₀.mul_val_inv
      let β : Fin n → R := fun i => a i * ai
      have hβ0 : β i₀ = 1 := haai
      let q'' : Fin n → ((j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) := fun i =>
        if i = i₀ then c 0 • q i₀ else q i - β i • q i₀

      have hcomb : ∀ (r : Fin n → R) (w : R), c 0 * w = ∑ i, r i * β i →
          ∑ i, (if i = i₀ then w else r i) • q'' i = ∑ i, r i • q i := by
        intro r w hw
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
        have hrest : ∑ i ∈ Finset.univ.erase i₀, (if i = i₀ then w else r i) • q'' i =
            ∑ i ∈ Finset.univ.erase i₀, r i • q i -
              (∑ i ∈ Finset.univ.erase i₀, r i * β i) • q i₀ := by
          rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
          simp only [q'', if_neg hne, smul_sub, smul_smul]
        have hw' : c 0 * w = r i₀ + ∑ i ∈ Finset.univ.erase i₀, r i * β i := by
          rw [hw, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hβ0, mul_one]
        rw [hrest]
        simp only [q'', if_pos rfl, smul_smul, ↓reduceIte]
        rw [mul_comm w, hw', add_smul]
        abel

      have hk0 : ∀ k, ∑ i, T k i * a i ∈ Ideal.span {c 0} := fun k => by
        rw [← Ideal.Quotient.eq_zero_iff_mem, ← hfst (T k) a ha, hT k]; rfl
      choose t' ht' using fun k => Ideal.mem_span_singleton'.1 (hk0 k)
      let t : Fin n → R := fun k => t' k * ai
      have ht : ∀ k, c 0 * t k = ∑ i, T k i * β i := fun k => by
        simp only [t, β, ← mul_assoc, ← Finset.sum_mul, ← ht' k]
        ring
      let T'' : Matrix (Fin n) (Fin n) R := Matrix.of fun k i => if i = i₀ then t k else T k i
      have hrel : ∀ k, ∑ i, T'' k i • (tl ∘ q'') i = 0 := fun k => by
        have := hcomb (T k) (t k) (ht k)
        rw [hT k] at this
        have h2 := congrArg tl this
        rw [map_sum, map_zero] at h2
        simpa only [T'', Matrix.of_apply, map_smul, Function.comp_apply] using h2
      have hgen : Submodule.span R (Set.range (tl ∘ q'')) = ⊤ := by
        rw [eq_top_iff]
        intro y _
        obtain ⟨x, rfl⟩ := htl_surj y
        let x0 : (j : Fin (m + 1)) → R ⧸ Ideal.span {c j} := Fin.cons 0 (tl x)
        obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
          (hq ▸ Submodule.mem_top : x0 ∈ Submodule.span R (Set.range q))
        have hr0 : ∑ i, r i * a i ∈ Ideal.span {c 0} := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, ← hfst r a ha, hr]; rfl
        obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1 hr0
        have hw : c 0 * (w' * ai) = ∑ i, r i * β i := by
          simp only [β, ← mul_assoc, ← Finset.sum_mul, ← hw']
          ring
        have hx := hcomb r (w' * ai) hw
        rw [hr] at hx
        have htx : tl x = tl x0 := funext fun j => rfl
        rw [htx, ← hx, map_sum]
        exact Submodule.sum_mem _ fun i _ => by
          rw [map_smul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hdet'' := ih (fun j => c j.succ) n (tl ∘ q'') hgen T'' hrel
      have hTeq : T = T''.updateCol i₀
          (fun k => c 0 * T'' k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * T'' k i) := by
        ext k i
        by_cases hi : i = i₀
        · subst hi
          rw [updateCol_self]
          simp only [T'', Matrix.of_apply, ↓reduceIte]
          rw [ht k, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hβ0, mul_one]
          have : ∑ x ∈ Finset.univ.erase i, β x * (if x = i then t k else T k x) =
              ∑ x ∈ Finset.univ.erase i, T k x * β x :=
            Finset.sum_congr rfl fun x hx => by
              rw [if_neg (Finset.ne_of_mem_erase hx), mul_comm]
          rw [this]; ring
        · rw [updateCol_ne hi]
          simp only [T'', Matrix.of_apply, if_neg hi]
      rw [hTeq, det_col_comb]
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hdet''
      rw [hprod, ← hz]
      exact Ideal.mem_span_singleton'.2 ⟨z, by ring⟩
end ReciprocityTheory.PGsh.Up
