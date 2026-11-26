-- Prove2me | solution 1 for OCTKernel.Main.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:09:07.015692+00:00
-- url     : https://prove2.me/submissions/7fa374eb-2d6b-48d5-8d9a-6f5477e64288

import Definitions.Def_OCTKernel_Main_Polynomials
import Theorems.Thm_OCTKernel_Main_lemma_3_3

open OCTKernel.Main Polynomial

theorem solution (p n t K : ℕ) [Fact p.Prime]
    (hn : 1 ≤ n) (ht : 1 ≤ t) (hK : 1 ≤ K)
    (hlarge : n * (t + n - 1) < K) (hchar : K + t - 1 < p)
    (α : Fin n → ZMod p) (hα : Function.Injective α)
    (P : Fin n → Polynomial (ZMod p)) (hP : ∀ i, P i ≠ 0)
    (hform : ∀ i, ∃ Q : Polynomial (ZMod p), Q.degree < (t : WithBot ℕ) ∧
      P i = (Polynomial.X - Polynomial.C (α i)) ^ K * Q) :
    LinearIndependent (ZMod p) P := by
  classical
  let W := Submodule.span (ZMod p) (Set.range P)
  let s := Module.finrank (ZMod p) W
  have hmem (i : Fin n) : P i ∈ W := Submodule.subset_span (Set.mem_range_self i)
  have hdeg : W ≤ degreeLE (ZMod p) (K + t - 1 : ℕ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    obtain ⟨Q,hQ,he⟩ := hform i
    have hQ0 : Q ≠ 0 := by intro h; exact hP i (by simp [he,h])
    have hQt := (natDegree_lt_iff_degree_lt hQ0).mpr hQ
    apply mem_degreeLE.mpr
    rw [← natDegree_le_iff_degree_le, he]
    exact natDegree_mul_le.trans (by rw [natDegree_pow,natDegree_X_sub_C]; omega)
  have hpos : 0 < s := by
    let i : Fin n := ⟨0,hn⟩
    haveI : Module.Finite (ZMod p) W := Module.Finite.span_of_finite _ (Set.finite_range P)
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨P i,hmem i⟩, fun h => hP i (congrArg Subtype.val h)⟩
  rw [linearIndependent_iff_card_le_finrank_span, Fintype.card_fin]
  change n ≤ s
  by_contra! hsn
  let f : ZMod p → ℕ := fun a => nu W a - (s-1)
  have hb := OCTKernel.Main.lemma_3_3 p s (K+t-1) hpos hchar W rfl
    (fun q hq => mem_degreeLE.mp (hdeg hq))
  have hKnu (i : Fin n) : K ≤ nu W (α i) := by
    obtain ⟨Q,_,he⟩ := hform i
    apply ((le_rootMultiplicity_iff (hP i)).mpr (show (X - C (α i))^K ∣ P i from ⟨Q,he⟩)).trans
    apply le_csSup (a := (P i).rootMultiplicity (α i))
    · refine ⟨K+t-1, ?_⟩
      rintro _ ⟨q,hq,_,rfl⟩
      calc
        _ = q.roots.count (α i) := (count_roots _).symm
        _ ≤ _ := Multiset.count_le_card _ _
        _ ≤ q.natDegree := card_roots' q
        _ ≤ _ := natDegree_le_iff_degree_le.mpr (mem_degreeLE.mp (hdeg hq))
    · exact ⟨P i,hmem i,hP i,rfl⟩
  have hm : (s+1) * (K - (s-1)) ≤ s * (K+t-1) := by
    calc
      _ ≤ n * (K-(s-1)) := Nat.mul_le_mul_right _ hsn
      _ = ∑ i : Fin n, (K-(s-1)) := by simp
      _ ≤ ∑ i : Fin n, f (α i) := Finset.sum_le_sum fun i _ => Nat.sub_le_sub_right (hKnu i) _
      _ = ∑ x ∈ Finset.univ.image α, f x := (Finset.sum_image (fun x _ y _ h => hα h)).symm
      _ ≤ ∑ x : ZMod p, f x := Finset.sum_le_univ_sum_of_nonneg (by simp)
      _ ≤ _ := hb
  have hnb : n ≤ n*(t+n-1) := by
    conv_lhs => rw [← Nat.mul_one n]
    exact Nat.mul_le_mul_left _ (by omega)
  have hB : s * (t+s-1) ≤ n * (t+n-1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e₁ : K-(s-1)+s = K+1 := by omega
  have e₂ : (K+t-1)+1 = K+t := by omega
  have e₃ : (t+s-1)+1 = t+s := by omega
  nlinarith [congrArg (fun a => s*a) e₁,congrArg (fun a => s*a) e₂,
    congrArg (fun a => s*a) e₃]
