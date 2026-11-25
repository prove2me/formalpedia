-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.pf_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:47:00.71386+00:00
-- url     : https://prove2.me/submissions/ca78d6b9-4627-44a4-b160-444c4edbfa89

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_exists_unif
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HeightMultiplicativity_log_gauss_ratio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_algK_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_at_la
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (y : OmS (Ω c) d.D d.N) (hy : y ≠ 0)
    (PA PB : KTp K d.D d.N) (hA : PA ≠ 0) (hB : PB ≠ 0)
    (hAB : letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) y * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) PB =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) PA)
    (la : HeightOneSpectrum (𝓞 K)) :
    Real.log (gaussAbs (FinitePlace.mk la) PA) - Real.log (gaussAbs (FinitePlace.mk la) PB) =
      -((d.nLa h c la y : ℝ) * logNorm la) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨ϖ, hϖ1, hϖ2, hϖ⟩ := exists_unif la
  obtain ⟨u, hu, hN⟩ := d.norm_at_la hd h c la ϖ hϖ1 hϖ2 y hy
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (laT d.D d.N la).primeCompl u
  dsimp only at hu hN
  have hx : x ∈ (laT d.D d.N la).primeCompl :=
    (IsLocalization.AtPrime.isUnit_mk'_iff (Op d.D d.N la) (laT d.D d.N la) x s).1 hu
  set g := (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)).comp (OTtoKT K d.D d.N)
  have hspec : g x = g s * OpToKT d.D d.N la (IsLocalization.mk' (Op d.D d.N la) x s) :=
    (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
  set n : ℤ := ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℤ) * WithTop.untopD 0 (w y) with hn
  have hn' : d.nLa h c la y = n := rfl
  set X' : KTp K d.D d.N := OTtoKT K d.D d.N x
  set S' : KTp K d.D d.N := OTtoKT K d.D d.N (s : OT K d.D d.N)
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)

  have hmain : algebraMap _ (KTf K d.D d.N) PA * algebraMap _ (KTf K d.D d.N) S' =
      (algebraMap K (KTf K d.D d.N) (ϖ : K)) ^ n * algebraMap _ (KTf K d.D d.N) X' *
        algebraMap _ (KTf K d.D d.N) PB := by
    rw [← hAB, hN]
    have : algebraMap _ (KTf K d.D d.N) X' = g x := rfl
    have h2 : algebraMap _ (KTf K d.D d.N) S' = g s := rfl
    rw [this, h2, hspec]; ring
  have hlogN : logNorm la = Real.log ((Ideal.absNorm la.asIdeal : ℕ) : ℝ) := rfl
  have hxm : x ∉ Ideal.map (C : 𝓞 K →+* OT K d.D d.N) la.asIdeal := hx
  have hsm : (s : OT K d.D d.N) ∉ Ideal.map (C : 𝓞 K →+* OT K d.D d.N) la.asIdeal := s.2
  rw [hn', hlogN]
  have hϖ0 : algebraMap K (KTf K d.D d.N) (ϖ : K) ≠ 0 := by
    rw [map_ne_zero]; intro h0'; rw [h0', map_zero] at hϖ
    have := NumberField.HeightOneSpectrum.one_lt_absNorm la
    have hN0 : (0 : ℝ) < ((Ideal.absNorm la.asIdeal : ℕ) : ℝ) := by
      exact_mod_cast (zero_lt_one.trans this)
    exact (inv_pos.2 hN0).ne' hϖ.symm
  rcases le_or_gt 0 n with h0 | h0
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h0
    rw [hm] at hmain ⊢
    have hp : PA * S' = C ((ϖ : K) ^ m) * X' * PB := by
      apply hinj
      rw [map_mul, map_mul, map_mul, ← d.algK_eq, map_pow, hmain, zpow_natCast]
    have := log_gauss_ratio la ϖ hϖ PA PB hA hB x s hxm hsm m hp
    rw [this]; push_cast; ring
  · obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat h0.le
    have hp : PB * X' = C ((ϖ : K) ^ m) * S' * PA := by
      apply hinj
      rw [map_mul, map_mul, map_mul, ← d.algK_eq, map_pow]
      rw [hm, zpow_neg, zpow_natCast] at hmain
      have hpow : (algebraMap K (KTf K d.D d.N) (ϖ : K)) ^ m ≠ 0 := pow_ne_zero _ hϖ0
      field_simp at hmain
      first
      | linear_combination hmain
      | linear_combination -hmain
    have := log_gauss_ratio la ϖ hϖ PB PA hB hA s x hsm hxm m hp
    rw [hm]; push_cast; linarith
end ReciprocityTheory.ChartRestriction.G.T0.Data
