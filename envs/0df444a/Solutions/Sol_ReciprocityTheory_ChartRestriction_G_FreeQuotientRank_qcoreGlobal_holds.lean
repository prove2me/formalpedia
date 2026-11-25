-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.qcoreGlobal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:17:46.924051+00:00
-- url     : https://prove2.me/submissions/61b38daf-8bf6-4da0-bd42-f46727377428

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreGlobPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_sum_places_restrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_finsum_regroup
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_finite_ordAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_globalQuot_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_one_lt_absNorm_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution : QCoreGlobalStatement := by
  intro K K₁ V _ _ _ _ _ _ _ _ M ρ θ c hD s hs supN a Bθ Carch Bdeg hconj hmean harch hdeg
  classical
  set D := detCT c θ with hDdef
  let F : HeightOneSpectrum (𝓞 K₁) → ℝ := fun w => (ordAt w D : ℝ) + ∑ i, s i w
  have hordfin : (Function.support fun w : HeightOneSpectrum (𝓞 K₁) => (ordAt w D : ℝ)).Finite := by
    refine (finite_ordAt hD).subset fun w hw => ?_
    have hpos : (0 : ℝ) < logN w := Real.log_pos (one_lt_absNorm_real w)
    simp only [Function.mem_support] at hw ⊢
    exact mul_ne_zero hw hpos.ne'
  have hFfin : (Function.support F).Finite := by
    refine (hordfin.union (Set.finite_iUnion fun i => hs i)).subset fun w hw => ?_
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, Function.mem_support, not_or, not_exists,
      not_not] at hnot
    apply hw
    simp [F, hnot.1, hnot.2]
  obtain ⟨hfinsupp, hregroup⟩ := finsum_regroup (K := K) F hFfin
  have hnn : ∀ la, nnFun (K := K) D s la =
      (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) /
        (Module.finrank K K₁ : ℝ) := fun la => rfl
  have hK₁K : (0 : ℝ) < Module.finrank K K₁ := by
    have : Module.Finite K K₁ := Module.Finite.of_restrictScalars_finite ℚ K K₁
    exact_mod_cast Module.finrank_pos
  have hKQ : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have htower : (Module.finrank ℚ K₁ : ℝ) = Module.finrank ℚ K * Module.finrank K K₁ := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ K K₁).symm
  refine ⟨hfinsupp.subset fun la hla => by
    rw [Function.mem_support, hnn] at hla
    intro h; apply hla; simp [h], ?_⟩

  have hsum : (∑ᶠ la : HeightOneSpectrum (𝓞 K), nnFun (K := K) D s la * logN la) =
      (∑ᶠ w, F w * logN w) / (Module.finrank K K₁ : ℝ) := by
    have hfin2 : (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
        (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) * logN la).Finite :=
      hfinsupp.subset fun la hla => by
        rw [Function.mem_support] at hla ⊢
        intro h; apply hla; rw [h, zero_mul]
    rw [← hregroup, div_eq_mul_inv, finsum_mul]
    refine finsum_congr fun la => ?_
    rw [hnn]; ring

  let m : Matrix (Fin ρ) (Fin ρ) K₁ := Matrix.of fun i j => c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V))
  have hmD : m.det = D := rfl
  let b : Fin ρ → InfinitePlace K₁ → ℝ := fun j σ =>
    Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) + Carch
  have hG := globalQuot_holds K₁ ρ m (by rw [hmD]; exact hD) s (fun _ => 0) a b (fun _ => Bdeg) 0 hs
    (by simp) (fun σ i j hij => harch σ i j hij) hdeg (by simp)
  have hLHS : (∑ᶠ w, ((ordAt w m.det : ℝ) + ∑ i, s i w + (ρ : ℝ) * (fun _ => (0 : ℝ)) w) * logN w) =
      ∑ᶠ w, F w * logN w := finsum_congr fun w => by simp [F, hmD]
  rw [hLHS] at hG
  have hKQc : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast Embeddings.card K ℂ
  have hbj : ∀ j, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) / (Module.finrank ℚ K₁ : ℝ) ≤
      Bθ + Carch := by
    intro j
    have e0 : ∀ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ =
        (σ.mult : ℝ) * Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) +
          Carch * (σ.mult : ℝ) := fun σ => by simp only [b]; ring
    have e2 := sum_places_restrict (K := K) (K₁ := K₁)
      (fun τ => Real.log (supN τ ((θ j : M) : V))) (fun τ => by rw [hconj])
    have e3 : (∑ σ : InfinitePlace K₁, (σ.mult : ℝ)) = Module.finrank ℚ K₁ := by
      exact_mod_cast InfinitePlace.sum_mult_eq
    rw [Finset.sum_congr rfl (fun σ _ => e0 σ), Finset.sum_add_distrib, ← Finset.mul_sum, e2, e3]
    have hm := hmean j
    rw [hKQc] at hm
    have hsplit : ((Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V)) +
        Carch * (Module.finrank ℚ K₁ : ℝ)) / (Module.finrank ℚ K₁ : ℝ) =
        (∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V))) / (Module.finrank ℚ K : ℝ) + Carch := by
      rw [htower]; field_simp
    rw [hsplit]; linarith
  have hsumj : ∑ j : Fin ρ, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) /
      (Module.finrank ℚ K₁ : ℝ) ≤ (ρ : ℝ) * (Bθ + Carch) := by
    calc _ ≤ ∑ _j : Fin ρ, (Bθ + Carch) := Finset.sum_le_sum fun j _ => hbj j
      _ = (ρ : ℝ) * (Bθ + Carch) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hBdeg : ∑ _i : Fin ρ, Bdeg = (ρ : ℝ) * Bdeg := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hBdeg] at hG
  rw [hsum, div_div, mul_comm (Module.finrank K K₁ : ℝ), ← htower]
  nlinarith [hG, hsumj]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
