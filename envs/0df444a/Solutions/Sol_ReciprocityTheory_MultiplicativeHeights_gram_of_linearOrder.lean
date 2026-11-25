-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gram_of_linearOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:45:30.807512+00:00
-- url     : https://prove2.me/submissions/76b9e046-9efc-4f00-9b58-41dac10db98d

import Definitions.Def_ReciprocityTheory_SemistableReduction_DetGramEqProdGramSchmidt
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex
import Definitions.Def_ReciprocityTheory_SemistableReduction_GramOfLinearOrder
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_lex_enum
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exp_torus_mean_le_l2_of_lex
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_norm_coeffVec
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_polyInner_eq_inner
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_prod_le_re_det_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights
open Finset Pointwise
private lemma support_subset_of_mem_span_of_support_subset {ι : Type} (s : Set (ι →₀ ℕ))
    (G : Set (MvPolynomial ι ℂ)) (hG : ∀ g ∈ G, (g.support : Set (ι →₀ ℕ)) ⊆ s)
    {p : MvPolynomial ι ℂ} (hp : p ∈ Submodule.span ℂ G) : (p.support : Set (ι →₀ ℕ)) ⊆ s := by
  classical
  induction hp using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero => simp
  | add x y _ _ hx hy =>
    intro t ht
    rcases Finset.mem_union.mp (MvPolynomial.support_add ht) with h | h
    exacts [hx h, hy h]
  | smul a x _ hx => exact fun t ht => hx (MvPolynomial.support_smul ht)
end ReciprocityTheory.MultiplicativeHeights
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset Pointwise
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι : Type} [Fintype ι] [LinearOrder ι]
    (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) (F : MvPolynomial ι ℂ) (S : Finset (ι →₀ ℕ)) (hF : F ≠ 0) :
    Real.exp (2 * S.card * torusMean F) ≤
      (Matrix.det (Matrix.of fun m m' : S =>
        polyInner (F * MvPolynomial.monomial (m : ι →₀ ℕ) 1)
          (F * MvPolynomial.monomial (m' : ι →₀ ℕ) 1))).re := by
  obtain ⟨m, hmS, hminj, hmlex⟩ := exists_lex_enum S
  let T : Finset (ι →₀ ℕ) := S.biUnion fun s => (F * MvPolynomial.monomial s (1 : ℂ)).support
  have hPT : ∀ s ∈ S, (F * MvPolynomial.monomial s (1 : ℂ)).support ⊆ T := fun s hs =>
    Finset.subset_biUnion_of_mem (fun s => (F * MvPolynomial.monomial s (1 : ℂ)).support) hs
  let v : Fin S.card → EuclideanSpace ℂ T := fun k => coeffVec T (F * MvPolynomial.monomial (m k) 1)

  have hbij : Function.Bijective (fun k : Fin S.card => (⟨m k, hmS k⟩ : S)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fun a b h => hminj (congrArg Subtype.val h), by simp⟩
  let e : Fin S.card ≃ S := Equiv.ofBijective _ hbij
  have hdet : Matrix.det (Matrix.of fun a b : S =>
        polyInner (F * MvPolynomial.monomial (a : ι →₀ ℕ) 1)
          (F * MvPolynomial.monomial (b : ι →₀ ℕ) 1)) = (Matrix.gram ℂ v).det := by
    rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose (Matrix.gram ℂ v)]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.gram_apply,
      e, Equiv.ofBijective_apply]
    exact polyInner_eq_inner T _ _ (hPT _ (hmS i))
  have hT : ∀ j, ((F * MvPolynomial.monomial (m j) (1 : ℂ)).support : Set (ι →₀ ℕ)) ⊆ T :=
    fun j => by exact_mod_cast hPT _ (hmS j)

  have hδ : ∀ k : Fin S.card, ∀ x ∈ Submodule.span ℂ (v '' Set.Iio k),
      Real.exp (2 * torusMean F) ≤ ‖v k - x‖ ^ 2 := by
    intro k x hx
    have hspan : Submodule.span ℂ (v '' Set.Iio k) =
        (Submodule.span ℂ ((fun j => MvPolynomial.monomial (m j) (1 : ℂ)) '' Set.Iio k)).map
          ((coeffVec T).comp (LinearMap.mulLeft ℂ F)) := by
      rw [Submodule.map_span, ← Set.image_comp]
      rfl
    rw [hspan] at hx
    obtain ⟨Q, hQ, rfl⟩ := hx
    have hQsupp : ∀ t ∈ Q.support, toLex (m k) < toLex t := by
      have hs := support_subset_of_mem_span_of_support_subset {t | toLex (m k) < toLex t} _ (by
        rintro _ ⟨j, hj, rfl⟩ t ht
        have ht' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
        subst ht'
        exact hmlex j k hj) hQ
      intro t ht
      exact hs ht
    have hmain := exp_torus_mean_le_l2_of_lex hBasic hLex hL2 F hF (m k) Q hQsupp
    have hFQ : ((F * Q).support : Set (ι →₀ ℕ)) ⊆ T := by
      have hmemFQ : F * Q ∈ Submodule.span ℂ
          ((LinearMap.mulLeft ℂ F) '' ((fun j => MvPolynomial.monomial (m j) (1 : ℂ)) '' Set.Iio k)) := by
        rw [← Submodule.map_span]
        exact Submodule.mem_map.mpr ⟨Q, hQ, rfl⟩
      refine support_subset_of_mem_span_of_support_subset _ _ ?_ hmemFQ
      rintro _ ⟨_, ⟨j, _, rfl⟩, rfl⟩
      exact hT j
    have hsupp : (F * (MvPolynomial.monomial (m k) 1 - Q)).support ⊆ T := by
      rw [mul_sub]
      intro t ht
      rcases Finset.mem_union.mp (MvPolynomial.support_sub _ _ _ ht) with h | h
      · exact_mod_cast hT k h
      · exact_mod_cast hFQ h
    have hsub : v k - ((coeffVec T).comp (LinearMap.mulLeft ℂ F)) Q =
        coeffVec T (F * (MvPolynomial.monomial (m k) 1 - Q)) := by
      rw [mul_sub, map_sub] <;> rfl
    rw [hsub, norm_coeffVec T _ hsupp]
    calc Real.exp (2 * torusMean F) = Real.exp (torusMean F) ^ 2 := by
          rw [sq, ← Real.exp_add, two_mul]
      _ ≤ _ := by gcongr
  have hprod := prod_le_re_det_gram S.card v (fun _ => Real.exp (2 * torusMean F))
    (fun _ => (Real.exp_pos _).le) hδ
  rw [hdet]
  refine le_trans (le_of_eq ?_) hprod
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  congr 1
  ring
end ReciprocityTheory.MultiplicativeHeights
