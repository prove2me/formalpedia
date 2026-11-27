-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.isSS_coeff_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:50.659108+00:00
-- url     : https://prove2.me/submissions/96404a32-b99c-4c79-add3-abc3282cbd30

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFacB
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_isSS_coeff
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_eq_zero_of_eval_algebraMap
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_IsSS_adjoin
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_IsSS_smul
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_IsSS_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
variable {A : Type} [Ring A] [Algebra ℂ A]
set_option linter.deprecated false
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
theorem _root_.solution (m : Multiset ℂ) (hm : m.Nodup) (r s : ℕ) (_hrs : Multiset.card m = r + s) (c₁ c₂ : ℂ)
    (a b : ℕ → A) (ha : a r = 1) (hb : b s = 1)
    (hcomm : ∀ i j, Commute (a i) (a j) ∧ Commute (a i) (b j) ∧ Commute (b i) (b j))
    (hrel : ∀ u : ℂ, (∑ k ∈ Finset.range (r + 1), (u + c₁) ^ k • a k) *
      (∑ k ∈ Finset.range (s + 1), (u + c₂) ^ k • b k) = algebraMap ℂ A (m.map (u + ·)).prod) (k : ℕ) :
    (k ≤ r → IsSS (a k)) ∧ (k ≤ s → IsSS (b k)) := by
  classical
  let S : Set A := Set.range a ∪ Set.range b
  have hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩) y (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact (hcomm i j).1.eq
    · exact (hcomm i j).2.1.eq
    · exact ((hcomm j i).2.1.eq).symm
    · exact (hcomm i j).2.2.eq
  letI : CommRing (Algebra.adjoin ℂ S) := Algebra.adjoinCommRingOfComm ℂ hS
  let a' : ℕ → Algebra.adjoin ℂ S := fun i => ⟨a i, Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)⟩
  let b' : ℕ → Algebra.adjoin ℂ S := fun i => ⟨b i, Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)⟩

  have key : ∀ (n : ℕ) (a' : ℕ → Algebra.adjoin ℂ S), a' n = 1 →
      ∃ P : (Algebra.adjoin ℂ S)[X], P.Monic ∧ (∀ k ≤ n, P.coeff k = a' k) ∧
        ∀ y : ℂ, P.eval (algebraMap ℂ _ y) = ∑ k ∈ Finset.range (n + 1), y ^ k • a' k := by
    intro n a' hn
    refine ⟨X ^ n + ∑ i ∈ Finset.range n, C (a' i) * X ^ i, monic_X_pow_add ?_, fun k hk => ?_, fun y => ?_⟩
    · refine mem_degreeLT.1 (Submodule.sum_mem _ fun i hi => mem_degreeLT.2 ?_)
      exact (degree_C_mul_X_pow_le i (a' i)).trans_lt (by exact_mod_cast Finset.mem_range.1 hi)
    · simp only [coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]
      rcases hk.lt_or_eq with hk | rfl
      · rw [if_neg hk.ne, zero_add, Finset.sum_ite_eq]
        simp [Finset.mem_range.2 hk]
      · rw [if_pos rfl, Finset.sum_ite_eq]
        simp [hn]
    · simp only [eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
      rw [Finset.sum_range_succ, hn, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← map_pow, mul_comm, ← Algebra.smul_def]
      · rw [← map_pow, Algebra.algebraMap_eq_smul_one]
  obtain ⟨P, hPm, hPc, hPe⟩ := key r a' (Subtype.ext ha)
  obtain ⟨Q, hQm, hQc, hQe⟩ := key s b' (Subtype.ext hb)
  let p : ℂ[X] := (m.map fun x => X + C x).prod
  have hpe : p = ∏ x ∈ m.toFinset, (X - C (-x)) := by
    simp only [p]
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hm]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    rw [map_neg, sub_neg_eq_add]
  have hps : p.Separable := by
    rw [hpe]
    exact separable_prod_X_sub_C_iff'.2 fun x _ y _ h => neg_inj.1 h
  have hval : ∀ u : ℂ, p.eval u = (m.map (u + ·)).prod := by
    intro u
    simp only [p, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_X, eval_C]

  have hrelP : P.comp (X + C (algebraMap ℂ _ c₁)) * Q.comp (X + C (algebraMap ℂ _ c₂)) =
      p.map (algebraMap ℂ (Algebra.adjoin ℂ S)) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eval_algebraMap _ fun u => ?_
    rw [eval_sub, eval_mul, eval_comp, eval_comp, eval_map, eval₂_at_apply, hval]
    simp only [eval_add, eval_X, eval_C, ← map_add]
    rw [hPe, hQe, sub_eq_zero]
    apply Subtype.ext
    have hv : ∀ x y : Algebra.adjoin ℂ S, ((x * y : Algebra.adjoin ℂ S) : A) = (x : A) * y := fun x y => rfl
    have hsm : ∀ (c : ℂ) (x : Algebra.adjoin ℂ S), ((c • x : Algebra.adjoin ℂ S) : A) = c • (x : A) :=
      fun c x => rfl
    have halg : ∀ c : ℂ, ((algebraMap ℂ (Algebra.adjoin ℂ S) c : Algebra.adjoin ℂ S) : A) = algebraMap ℂ A c :=
      fun c => rfl
    have hsum : ∀ (t : Finset ℕ) (g : ℕ → Algebra.adjoin ℂ S),
        ((∑ i ∈ t, g i : Algebra.adjoin ℂ S) : A) = ∑ i ∈ t, (g i : A) := by
      intro t g
      induction t using Finset.induction_on with
      | empty => rfl
      | insert j t hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
        rfl
    rw [hv, hsum, hsum, halg]
    simp only [hsm]
    exact hrel u

  let P₁ := P.comp (X + C (algebraMap ℂ (Algebra.adjoin ℂ S) c₁))
  let Q₁ := Q.comp (X + C (algebraMap ℂ (Algebra.adjoin ℂ S) c₂))
  have hP₁ : P₁.Monic := hPm.comp_X_add_C _
  have hQ₁ : Q₁.Monic := hQm.comp_X_add_C _
  have hss₁ : ∀ j, IsSS (P₁.coeff j) := isSS_coeff p hps P₁ Q₁ hP₁ hQ₁ hrelP
  have hss₂ : ∀ j, IsSS (Q₁.coeff j) := isSS_coeff p hps Q₁ P₁ hQ₁ hP₁ (by rw [mul_comm]; exact hrelP)

  have unshift : ∀ (P₁ : (Algebra.adjoin ℂ S)[X]) (c : ℂ), (∀ j, IsSS (P₁.coeff j)) →
      ∀ k, IsSS ((P₁.comp (X - C (algebraMap ℂ _ c))).coeff k) := by
    intro P₁ c h k
    rw [comp_eq_sum_left, Polynomial.sum, finsetSum_coeff]
    refine IsSS.sum _ _ (fun j _ => ?_) fun i _ j _ => Commute.all _ _
    rw [coeff_C_mul]
    have hmap : (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c)) ^ j = ((X - C c) ^ j).map (algebraMap ℂ _) := by
      simp [Polynomial.map_pow]
    rw [hmap, coeff_map, mul_comm, ← Algebra.smul_def]
    exact (h j).smul _
  have hPP : P = P₁.comp (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c₁)) := by
    simp only [P₁, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]
  have hQQ : Q = Q₁.comp (X - C (algebraMap ℂ (Algebra.adjoin ℂ S) c₂)) := by
    simp only [Q₁, comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]
  have toA : ∀ x : Algebra.adjoin ℂ S, IsSS x → IsSS (x : A) := by
    rintro x ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have := aeval_algHom_apply (Algebra.adjoin ℂ S).val x (∏ v ∈ t, (X - C v))
    rw [Subalgebra.coe_val] at this
    rw [this, ht]
    rfl
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · have h1 := unshift P₁ c₁ hss₁ k
    rw [← hPP, hPc k hk] at h1
    exact toA _ h1
  · have h1 := unshift Q₁ c₂ hss₂ k
    rw [← hQQ, hQc k hk] at h1
    exact toA _ h1
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
