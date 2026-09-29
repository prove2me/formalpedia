-- Prove2me | solution 1 for ValuationSubring.eq_of_comap_eq_of_forall_sum_mul_not_mem_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/abf8b416-493a-54da-8ff6-cababd950382

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_eq_of_comap_eq_of_forall_sum_mul_not_mem_nonunits

set_option autoImplicit false

namespace Ws23
namespace C5

open scoped BigOperators

variable {K K' : Type*} [Field K] [Field K']

theorem le_one_of_mul_self_le {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {γ : Γ} (h0 : γ ≠ 0)
    (h : γ * γ ≤ γ) : γ ≤ 1 :=
  calc γ = γ * γ * γ⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ h0, mul_one]
    _ ≤ γ * γ⁻¹ := mul_le_mul_left h _
    _ = 1 := mul_inv_cancel₀ h0

section Main

variable (ι : K →+* K') (n : ℕ)
  (W : ValuationSubring K) (U : ValuationSubring K') (hU : U.comap ι = W)
  (u : Fin n → K') (hu : ∀ i, u i ∈ U)
  (hind : ∀ c : Fin n → K, (∀ i, c i ∈ W) → (∃ i, c i ∉ W.nonunits) → ∑ i, ι (c i) * u i ∉ U.nonunits)

include hU hu hind

theorem exists_max_coeff (c : Fin n → K) (hc : c ≠ 0) :
    ∃ i₁ : Fin n, c i₁ ≠ 0 ∧ (∀ i, c i / c i₁ ∈ W) ∧
      ∃ s : K', U.valuation s = 1 ∧ ∑ i, ι (c i) * u i = ι (c i₁) * s := by
  classical
  have hn : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at h
    exact hc (funext fun i => (h.false i).elim)
  obtain ⟨i₁, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => W.valuation (c i)) hn
  have hi₁ : c i₁ ≠ 0 := by
    intro h0
    apply hc
    funext i
    have := hmax i (Finset.mem_univ i)
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact this
  have hdW : ∀ i, c i / c i₁ ∈ W := by
    intro i
    rw [← W.valuation_le_one_iff, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hi₁)]
    exact hmax i (Finset.mem_univ i)

  set s : K' := ∑ i, ι (c i / c i₁) * u i with hs
  have hsU : s ∈ U := by
    refine sum_mem fun i _ => mul_mem ?_ (hu i)
    rw [← ValuationSubring.mem_comap, hU]
    exact hdW i
  have hs1 : U.valuation s = 1 := by
    refine le_antisymm ((U.valuation_le_one_iff s).2 hsU) ?_
    have h := hind (fun i => c i / c i₁) hdW ⟨i₁, by
      show c i₁ / c i₁ ∉ W.nonunits
      rw [div_self hi₁, ValuationSubring.mem_nonunits_iff, map_one]
      exact lt_irrefl 1⟩
    rw [ValuationSubring.mem_nonunits_iff, not_lt] at h
    exact h
  refine ⟨i₁, hi₁, hdW, s, hs1, ?_⟩
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hi₁]

theorem forall_mem_of_sum_mem (c : Fin n → K) (h : ∑ i, ι (c i) * u i ∈ U) : ∀ i, c i ∈ W := by
  by_cases hc : c = 0
  · intro i; rw [hc]; exact W.zero_mem
  obtain ⟨i₁, hi₁, hdW, s, hs1, hsum⟩ := exists_max_coeff ι n W U hU u hu hind c hc
  have hc₁ : c i₁ ∈ W := by
    rw [← hU, ValuationSubring.mem_comap, ← U.valuation_le_one_iff]
    have := (U.valuation_le_one_iff _).2 h
    rw [hsum, map_mul, hs1, mul_one] at this
    exact this
  intro i
  have : c i = c i / c i₁ * c i₁ := by rw [div_mul_cancel₀ _ hi₁]
  rw [this]
  exact mul_mem (hdW i) hc₁

theorem eq_zero_of_sum_eq_zero (c : Fin n → K) (h : ∑ i, ι (c i) * u i = 0) : c = 0 := by
  by_contra hc
  obtain ⟨i₁, hi₁, -, s, hs1, hsum⟩ := exists_max_coeff ι n W U hU u hu hind c hc
  rw [hsum] at h
  rcases mul_eq_zero.1 h with h1 | h1
  · exact hi₁ ((map_eq_zero ι).1 h1)
  · rw [h1, map_zero] at hs1
    exact zero_ne_one hs1

end Main

theorem main (ι : K →+* K') (n : ℕ)
    (b : Fin n → K') (hb : ∀ z : K', ∃ c : Fin n → K, z = ∑ i, ι (c i) * b i)
    (W : ValuationSubring K) (U : ValuationSubring K') (hU : U.comap ι = W)
    (u : Fin n → K') (hu : ∀ i, u i ∈ U)
    (hind : ∀ c : Fin n → K, (∀ i, c i ∈ W) → (∃ i, c i ∉ W.nonunits) → ∑ i, ι (c i) * u i ∉ U.nonunits)
    (V : ValuationSubring K') (hV : V.comap ι = W) :
    V = U := by
  classical

  have hn : n ≠ 0 := by
    rintro rfl
    obtain ⟨c, hc⟩ := hb 1
    simp at hc
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩

  letI alg : Algebra K K' := ι.toAlgebra
  have hsmul : ∀ (a : K) (x : K'), a • x = ι a * x := fun a x => Algebra.smul_def a x
  haveI : Module.Finite K K' := by
    refine ⟨⟨Finset.univ.image b, eq_top_iff.2 fun z _ => ?_⟩⟩
    obtain ⟨c, rfl⟩ := hb z
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hli : LinearIndependent K u := by
    rw [linearIndependent_iff']
    intro s g hg i hi

    let c : Fin n → K := fun j => if j ∈ s then g j else 0
    have hsum : ∑ j, ι (c j) * u j = 0 := by
      rw [← hg, ← Finset.sum_subset (Finset.subset_univ s)]
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [hsmul]; simp [c, hj]
      · intro j _ hj; simp [c, hj]
    have := congrFun (eq_zero_of_sum_eq_zero ι n W U hU u hu hind c hsum) i
    simpa [c, hi] using this
  have hdim : Module.finrank K K' = n := by
    refine le_antisymm ?_ (by simpa using hli.fintype_card_le_finrank)
    have htop : Submodule.span K (Set.range b) = ⊤ := by
      rw [eq_top_iff]
      intro z _
      obtain ⟨c, rfl⟩ := hb z
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← finrank_top, ← htop]
    refine (finrank_span_le_card _).trans ?_
    rw [Set.toFinset_range]
    exact Finset.card_image_le.trans (by simp)
  have hspan : Submodule.span K (Set.range u) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simpa using hdim.symm)
  have hrepr : ∀ z : K', ∃ c : Fin n → K, ∑ i, ι (c i) * u i = z := by
    intro z
    have hz : z ∈ Submodule.span K (Set.range u) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hz
    exact ⟨c, by simpa only [hsmul] using hc⟩

  have huV : ∀ i, u i ∈ V := by
    obtain ⟨j₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => V.valuation (u i)) Finset.univ_nonempty
    have hu0 : u j₀ ≠ 0 := hli.ne_zero j₀
    have hγ : V.valuation (u j₀) * V.valuation (u j₀) ≤ V.valuation (u j₀) := by
      obtain ⟨a, ha⟩ := hrepr (u j₀ * u j₀)
      have haW : ∀ k, a k ∈ W :=
        forall_mem_of_sum_mem ι n W U hU u hu hind a (by rw [ha]; exact mul_mem (hu j₀) (hu j₀))
      rw [← map_mul, ← ha]
      refine Valuation.map_sum_le _ fun k _ => ?_
      rw [map_mul]
      have h1 : V.valuation (ι (a k)) ≤ 1 := by
        rw [V.valuation_le_one_iff, ← ValuationSubring.mem_comap, hV]
        exact haW k
      calc V.valuation (ι (a k)) * V.valuation (u k) ≤ 1 * V.valuation (u j₀) :=
            mul_le_mul' h1 (hmax k (Finset.mem_univ k))
        _ = V.valuation (u j₀) := one_mul _
    have hle : V.valuation (u j₀) ≤ 1 :=
      le_one_of_mul_self_le ((Valuation.ne_zero_iff _).2 hu0) hγ
    intro i
    rw [← V.valuation_le_one_iff]
    exact (hmax i (Finset.mem_univ i)).trans hle

  have hUV : ∀ x : K', x ∈ U → x ∈ V := by
    intro x hx
    obtain ⟨c, rfl⟩ := hrepr x
    have hcW := forall_mem_of_sum_mem ι n W U hU u hu hind c hx
    refine sum_mem fun i _ => mul_mem ?_ (huV i)
    rw [← ValuationSubring.mem_comap, hV]
    exact hcW i

  refine ValuationSubring.ext _ _ fun x => ⟨fun hxV => ?_, hUV x⟩
  by_contra hxU
  obtain ⟨c, rfl⟩ := hrepr x
  have hc : c ≠ 0 := by
    rintro rfl
    apply hxU
    simp
  obtain ⟨i₁, hi₁, hdW, s, hs1, hsum⟩ := exists_max_coeff ι n W U hU u hu hind c hc

  have hc₁ : c i₁ ∉ W := by
    intro h
    apply hxU
    refine sum_mem fun i _ => mul_mem ?_ (hu i)
    rw [← ValuationSubring.mem_comap, hU]
    have : c i = c i / c i₁ * c i₁ := by rw [div_mul_cancel₀ _ hi₁]
    rw [this]
    exact mul_mem (hdW i) h

  have hιV : ι (c i₁) ∉ V := by rwa [← ValuationSubring.mem_comap, hV]
  have hs0 : s ≠ 0 := by
    intro h; rw [h, map_zero] at hs1; exact zero_ne_one hs1
  have hιne : ι (c i₁) ≠ 0 := (map_ne_zero ι).2 hi₁
  have hsval : V.valuation s < 1 := by
    have hs : s = (ι (c i₁))⁻¹ * ∑ i, ι (c i) * u i := by
      rw [hsum, ← mul_assoc, inv_mul_cancel₀ hιne, one_mul]
    rw [hs, map_mul, Valuation.map_inv]
    have h1 : 1 < V.valuation (ι (c i₁)) := by
      rw [← not_le, V.valuation_le_one_iff]
      exact hιV
    have h2 : V.valuation (∑ i, ι (c i) * u i) ≤ 1 := (V.valuation_le_one_iff _).2 hxV
    calc (V.valuation (ι (c i₁)))⁻¹ * V.valuation (∑ i, ι (c i) * u i)
        ≤ (V.valuation (ι (c i₁)))⁻¹ * 1 := mul_le_mul_right h2 _
      _ < 1 := by
          rw [mul_one]
          exact inv_lt_one_of_one_lt₀ h1

  have hsinv : s⁻¹ ∈ V := by
    apply hUV
    rw [← U.valuation_le_one_iff, Valuation.map_inv, hs1, inv_one]
  have : V.valuation s⁻¹ ≤ 1 := (V.valuation_le_one_iff _).2 hsinv
  rw [Valuation.map_inv, inv_le_one₀ ((Valuation.pos_iff _).2 hs0)] at this
  exact absurd hsval (not_lt.2 this)

end Ws23.C5

open scoped BigOperators

theorem solution
    {K K' : Type*} [Field K] [Field K'] (ι : K →+* K') (n : ℕ)
    (b : Fin n → K') (hb : ∀ z : K', ∃ c : Fin n → K, z = ∑ i, ι (c i) * b i)
    (W : ValuationSubring K) (U : ValuationSubring K') (hU : U.comap ι = W)
    (u : Fin n → K') (hu : ∀ i, u i ∈ U)
    (hind : ∀ c : Fin n → K, (∀ i, c i ∈ W) → (∃ i, c i ∉ W.nonunits) → ∑ i, ι (c i) * u i ∉ U.nonunits)
    (V : ValuationSubring K') (hV : V.comap ι = W) :
    V = U :=
  Ws23.C5.main ι n b hb W U hU u hu hind V hV

end S_ValuationSubring_eq_of_comap_eq_of_forall_sum_mul_not_mem_nonunits
end P2MW
export P2MW.S_ValuationSubring_eq_of_comap_eq_of_forall_sum_mul_not_mem_nonunits (solution)
