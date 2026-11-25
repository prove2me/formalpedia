-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage.lenW_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:30:34.30153+00:00
-- url     : https://prove2.me/submissions/f866180b-fda7-4db4-bf77-04550ebd5ab8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalQuotientRank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalLengthFraction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalLengthAverage
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_LocalLengthAverage_algebraMap_mem_Rv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_LocalLengthFraction_local_len
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_LocalQuotientRank_detCT_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_LocalQuotientRank_quot_finrank
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_LocalQuotientRank_span_tmul_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_LocalQuotientRank_tmul_mem_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
  ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
open scoped TensorProduct
variable {K K₁ V : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage
theorem _root_.solution (hL : QuotLocalStatement) (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hspan : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V)
    (θ : Fin (finrank (𝓞 K) (QuotMW M W)) → M)
    (hθ : Submodule.span K (Set.range fun j => ((θ j : M) : V)) ⊔ W = ⊤)
    (c : Fin (finrank (𝓞 K) (QuotMW M W)) → Module.Dual K₁ (K₁ ⊗[K] V))
    (hc : ∀ x : K₁ ⊗[K] V, (∀ i, c i x = 0) ↔
      x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)))
    (w : HeightOneSpectrum (𝓞 K₁)) (s : Fin (finrank (𝓞 K) (QuotMW M W)) → ℝ) (β : ℝ)
    (hint : ∀ i, ∀ m ∈ M, c i ((1 : K₁) ⊗ₜ[K] m) ≠ 0 →
      -β ≤ (ordAt w (c i ((1 : K₁) ⊗ₜ[K] m)) : ℝ) + s i) :
    ∃ n : ℕ, lenW w M W θ = n ∧
      (n : ℝ) ≤ (ordAt w (detCT c θ) : ℝ) + ∑ i, s i +
        (finrank (𝓞 K) (QuotMW M W) : ℝ) * β := by
  classical
  let inst : Module (Rv K₁ w) (K₁ ⊗[K] V) := Module.compHom _ (Rv K₁ w).subtype
  have hst : IsScalarTower (Rv K₁ w) K₁ (K₁ ⊗[K] V) :=
    ⟨fun r a x => mul_smul (r : K₁) a x⟩
  have hsmul : ∀ (r : Rv K₁ w) (x : K₁ ⊗[K] V), r • x = (r : K₁) • x := fun r x => rfl
  set Mw : Submodule (Rv K₁ w) (K₁ ⊗[K] V) := Submodule.span (Rv K₁ w)
    ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (M.restrictScalars ℤ : Set V)) with hMwdef
  have hgen : ∀ m ∈ M, (1 : K₁) ⊗ₜ[K] m ∈ Mw := fun m hm => Submodule.subset_span ⟨m, hm, rfl⟩
  have hsc : ∀ (a : 𝓞 K) (m : V), (1 : K₁) ⊗ₜ[K] (a • m) =
      (⟨algebraMap K K₁ (algebraMap (𝓞 K) K a), algebraMap_mem_Rv w a⟩ : Rv K₁ w) •
        ((1 : K₁) ⊗ₜ[K] m) := by
    intro a m
    rw [hsmul, ← algebraMap_smul K a m, TensorProduct.tmul_smul,
      ← algebraMap_smul K₁ (algebraMap (𝓞 K) K a)]
  have hMwFG : Mw.FG := by
    obtain ⟨G, hG⟩ := hM
    refine ⟨G.image (fun a : V => (1 : K₁) ⊗ₜ[K] a), ?_⟩
    rw [Finset.coe_image]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact hgen g (hG ▸ Submodule.subset_span hg)
    · rw [hMwdef, Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      have hm' : m ∈ Submodule.span (𝓞 K) (G : Set V) := by rw [hG]; exact hm
      clear hm
      show (1 : K₁) ⊗ₜ[K] m ∈ _
      induction hm' using Submodule.span_induction with
      | mem g hg => exact Submodule.subset_span ⟨g, hg, rfl⟩
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb
      | smul a b _ hb => rw [hsc]; exact Submodule.smul_mem _ _ hb
  have hMspan : Submodule.span K₁ (Mw : Set (K₁ ⊗[K] V)) = ⊤ := by
    rw [eq_top_iff, ← span_tmul_one (K := K) (K₁ := K₁) (V := V), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hr : (Set.range fun m : M => (m : V)) = (M : Set V) := Subtype.range_coe
    have hv : v ∈ Submodule.span K (Set.range fun m : M => (m : V)) := by
      rw [hr, hspan]; trivial
    have h1 := tmul_mem_span (K₁ := K₁) (fun m : M => (m : V)) hv
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨m, rfl⟩
    exact Submodule.subset_span (hgen m m.2)
  have hint' : ∀ i, ∀ y ∈ Mw, c i y ≠ 0 → -β ≤ (ordAt w (c i y) : ℝ) + s i := by
    intro i y hy hne
    have hball : w.valuation K₁ (c i y) ≤ WithZero.exp (-⌈-β - s i⌉) := by
      clear hne
      rw [hMwdef] at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨m, hm, rfl⟩ := hz
        by_cases h0 : c i ((1 : K₁) ⊗ₜ[K] m) = 0
        · rw [h0, map_zero]; exact zero_le
        · have h1 := hint i m hm h0
          rw [val_eq_exp w h0, WithZero.exp_le_exp, neg_le_neg_iff, Int.ceil_le]
          linarith
      | zero => rw [map_zero, map_zero]; exact zero_le
      | add a b _ _ ha hb =>
        rw [map_add]
        exact le_trans (Valuation.map_add _ _ _) (max_le ha hb)
      | smul r a _ ha =>
        show w.valuation K₁ (c i ((r : K₁) • a)) ≤ _
        rw [map_smul, smul_eq_mul, map_mul]
        exact le_trans (mul_le_of_le_one_left' ((mem_Rv_iff w _).mp r.2)) ha
    rw [val_eq_exp w hne, WithZero.exp_le_exp, neg_le_neg_iff, Int.ceil_le] at hball
    linarith
  have hcP : ∀ i, ∀ x ∈ Submodule.span K₁ ((fun a : V => (1 : K₁) ⊗ₜ[K] a) '' (W : Set V)),
      c i x = 0 := fun i x hx => (hc x).mpr hx i
  obtain ⟨n, hn1, hn2⟩ := @local_len K₁ _ _ w (K₁ ⊗[K] V) _ _ _ inst hst hL _ Mw hMwFG hMspan _ (quot_finrank M hM hspan W θ hθ)
    (fun j => (1 : K₁) ⊗ₜ[K] ((θ j : M) : V)) (fun j => hgen _ (θ j).2) (fun i => c i) hcP s β
    hint' (detCT_ne_zero M hM hspan W θ hθ c hc)
  exact ⟨n, hn1, hn2⟩
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthAverage
