-- Prove2me | solution 1 for ResPCDegreeSize.Main.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:56:54.418141+00:00
-- url     : https://prove2.me/submissions/616c36f6-a5a1-43b7-b8c9-4b99eeaca200

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
open MvPolynomial
namespace ResPCDegreeSize.Main

theorem _root_.solution {p m : ℕ} [Fact p.Prime] {E : Type*} [Field E] [Algebra (ZMod p) E]
    (W : Submodule E (Fin m → E))
    (hW : ∀ u ∈ W, (fun j => u j ^ p) ∈ W) :
    W = Submodule.span E
      {v : Fin m → E | v ∈ W ∧ ∀ j, v j ∈ Set.range (algebraMap (ZMod p) E)} := by
  classical
  set R : Set (Fin m → E) := {v : Fin m → E | v ∈ W ∧ ∀ j, v j ∈ Set.range (algebraMap (ZMod p) E)} with hR
  have hp : p.Prime := Fact.out
  have hfix : ∀ x : E, x ^ p = x → x ∈ Set.range (algebraMap (ZMod p) E) := by
    intro x hx
    set q : Polynomial E := Polynomial.X ^ p - Polynomial.X with hq
    have hq0 : q ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero E hp.one_lt
    have hdeg : q.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq E hp.one_lt
    set T : Finset E := Finset.univ.image (algebraMap (ZMod p) E) with hT
    have hTcard : T.card = p := by
      rw [hT, Finset.card_image_of_injective _ (algebraMap (ZMod p) E).injective, Finset.card_univ, ZMod.card]
    have hTroots : T.val ⊆ q.roots := by
      intro y hy
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hy
      rw [Polynomial.mem_roots hq0]
      simp [hq, Polynomial.IsRoot, ← map_pow, ZMod.pow_card]
    by_contra hxr
    have hxT : x ∉ T := fun h => by
      obtain ⟨a, _, ha⟩ := Finset.mem_image.1 h
      exact hxr ⟨a, ha⟩
    have hsub : (insert x T).val ⊆ q.roots := by
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · rw [Polynomial.mem_roots hq0]; simp [hq, Polynomial.IsRoot, hx]
      · exact hTroots hy
    have := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Finset.card_insert_of_notMem hxT, hTcard, hdeg] at this
    omega
  apply le_antisymm
  swap
  · exact Submodule.span_le.2 fun v hv => hv.1
  suffices H : ∀ n : ℕ, ∀ w ∈ W, (Finset.univ.filter fun j => w j ≠ 0).card = n → w ∈ Submodule.span E R from
    fun w hw => H _ w hw rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw hn
    by_cases hw0 : w = 0
    · subst hw0; exact zero_mem _
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hw0
    simp only [Pi.zero_apply] at hk
    set v : Fin m → E := (w k)⁻¹ • w with hv
    have hvW : v ∈ W := W.smul_mem _ hw
    have hvk : v k = 1 := by simp [hv, hk]
    have hsupp : ∀ j, w j = 0 → v j = 0 := fun j h => by simp [hv, h]
    have smaller : ∀ u ∈ W, (∀ j, w j = 0 → u j = 0) → ∀ i, w i ≠ 0 → u i = 0 → u ∈ Submodule.span E R := by
      intro u hu hus i hi hui
      refine ih _ ?_ u hu rfl
      rw [← hn]
      refine Finset.card_lt_card ⟨fun j hj => ?_, fun hsub => ?_⟩
      · rw [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, fun h => hj.2 (hus j h)⟩
      · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩)
        exact (Finset.mem_filter.1 this).2 hui
    have hvmem : v ∈ Submodule.span E R := by
      set u : Fin m → E := (fun j => v j ^ p) - v with hu
      have huW : u ∈ W := W.sub_mem (hW v hvW) hvW
      have huk : u k = 0 := by simp [hu, hvk]
      have hus : ∀ j, w j = 0 → u j = 0 := fun j h => by simp [hu, hsupp j h, zero_pow hp.ne_zero]
      have huS := smaller u huW hus k hk huk
      by_cases hu0 : u = 0
      · refine Submodule.subset_span ⟨hvW, fun j => hfix _ ?_⟩
        have := congrFun hu0 j
        simpa [hu, sub_eq_zero] using this
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hu0
      simp only [Pi.zero_apply] at hi
      have hwi : w i ≠ 0 := fun h => hi (hus i h)
      set z : Fin m → E := v - (v i / u i) • u with hz
      have hzS : z ∈ Submodule.span E R := by
        refine smaller z (W.sub_mem hvW (W.smul_mem _ huW)) (fun j h => ?_) i hwi ?_
        · simp [hz, hsupp j h, hus j h]
        · simp [hz, hi]
      have : v = z + (v i / u i) • u := by rw [hz]; abel
      rw [this]; exact add_mem hzS (Submodule.smul_mem _ _ huS)
    have : w = w k • v := by rw [hv, smul_smul, mul_inv_cancel₀ hk, one_smul]
    rw [this]; exact Submodule.smul_mem _ _ hvmem


end ResPCDegreeSize.Main

